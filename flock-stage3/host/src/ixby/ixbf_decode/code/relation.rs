use super::super::{
  grammar::Phase,
  synthesis::{Bits, Builder},
};
use super::{CodeGate, CodeKind, CodeOp};
use crate::{
  boolean::BooleanR1csPlan,
  ixby::bits::{add, subtract},
  sizing::CountedGate,
};
use flock_prover::field::F128;

fn word(i: usize) -> Bits {
  (128 * i..128 * (i + 1)).collect()
}
fn value(w: F128) -> u128 {
  w.lo as u128 | ((w.hi as u128) << 64)
}
fn mask(b: &mut Builder, on: usize, x: &[usize]) -> Bits {
  x.iter().map(|&v| b.b.and(on, v)).collect()
}
fn choose(b: &mut Builder, on: usize, a: &[usize], c: &[usize]) -> Bits {
  a.iter()
    .zip(c)
    .map(|(&a, &c)| {
      let p = b.b.product_of_parities(&[on], &[a, c]);
      b.sum(&[c, p])
    })
    .collect()
}
fn plus(b: &mut Builder, on: usize, a: &[usize], c: &[usize]) -> Bits {
  let (v, carry) = add(&mut b.b, b.one, b.zero, a, c);
  b.require_zero(on, &[carry]);
  v
}
fn multiply(b: &mut Builder, on: usize, x: &[usize], constant: u64) -> Bits {
  let mut out = b.constant(128, 0);
  for shift in 0..64 {
    if constant & (1u64 << shift) == 0 {
      continue;
    }
    b.require_zero(on, &x[128 - shift..]);
    let term = [vec![b.zero; shift], x[..128 - shift].to_vec()].concat();
    out = plus(b, on, &out, &term);
  }
  out
}
pub(super) fn build(g: &CodeGate) -> BooleanR1csPlan {
  let scratch = match g.op {
    CodeOp::Request => {
      16_384
        + 1500
          * g.layout.address(g.kind)[1..]
            .iter()
            .map(|v| v.count_ones() as usize)
            .sum::<usize>()
    },
    CodeOp::Record => 8192 + 512 * g.layout.window_words(),
  };
  let mut b = Builder::new(
    g.input_count(),
    g.output_count(),
    128 * (g.input_count() + g.output_count()) + scratch,
  );
  let enabled = word(0)[0];
  b.require_zero(b.one, &word(0)[1..]);
  let disabled = b.not(enabled);
  match g.op {
    CodeOp::Request => {
      let address = g.layout.address(g.kind);
      let bounds = g.layout.bounds(g.kind);
      let mut offset = b.constant(128, address[0]);
      for i in 0..3 {
        let x = word(i + 1);
        b.require_zero(disabled, &x);
        if address[i + 1] == 0 {
          b.require_zero(b.one, &x);
        } else {
          let bound = b.constant(128, bounds[i]);
          let (_, less) = subtract(&mut b.b, b.one, b.zero, &x, &bound);
          b.require(enabled, less);
        }
        let term = multiply(&mut b, enabled, &x, address[i + 1]);
        offset = plus(&mut b, enabled, &offset, &term);
      }
      let width = (g.layout.record_words(g.kind) * 16) as u64;
      let length = b.constant(128, g.layout.bytes());
      let amount = b.constant(128, width);
      let end = plus(&mut b, enabled, &offset, &amount);
      let (_, outside) = subtract(&mut b.b, b.one, b.zero, &length, &end);
      b.require_zero(enabled, &[outside]);
      b.require_zero(enabled, &offset[64..]);
      let offset = mask(&mut b, enabled, &offset[..64]);
      let cursor = [offset.clone(), b.constant(64, g.layout.bytes())].concat();
      b.write(4, &cursor);
      let take = mask(&mut b, enabled, &amount);
      b.write(5, &take);
      let last = (g.layout.bytes() - 1) / 1024;
      let index = [offset[10..].to_vec(), vec![b.zero; 10]].concat();
      let bound = b.constant(64, last);
      let (_, outside) = subtract(&mut b.b, b.one, b.zero, &bound, &index);
      let first = choose(&mut b, outside, &bound, &index);
      let one = b.constant(64, 1);
      let successor = plus(&mut b, enabled, &first, &one);
      let (_, outside) = subtract(&mut b.b, b.one, b.zero, &bound, &successor);
      let next = choose(&mut b, outside, &bound, &successor);
      b.write(6, &[first, vec![b.zero; 64]].concat());
      b.write(7, &[next, vec![b.zero; 64]].concat());
    },
    CodeOp::Record => {
      let n = g.layout.record_words(g.kind);
      for i in 0..g.layout.window_words() {
        b.require_zero(if i < n { disabled } else { b.one }, &word(1 + i));
      }
      if g.kind == CodeKind::Program {
        let phase = b.eq_const(&word(4)[..8], Phase::Done as u64);
        b.require(enabled, phase);
      } else {
        let one = b.constant(128, 1);
        let present = b.equal(&word(1), &one);
        b.require(enabled, present);
      }
      for i in 0..n {
        let result = mask(&mut b, enabled, &word(1 + i));
        b.write(g.input_count() + i, &result);
      }
    },
  }
  b.finish(g.input_count() + g.output_count() - 1)
}

pub(super) fn evaluate(g: &CodeGate, input: &[F128]) -> Vec<F128> {
  let enabled = input[0].lo & 1 != 0;
  let mut bad = value(input[0]) > 1;
  let mut out = match g.op {
    CodeOp::Request => {
      let address = g.layout.address(g.kind);
      let bounds = g.layout.bounds(g.kind);
      let mut offset = address[0] as u128;
      for i in 0..3 {
        let x = value(input[i + 1]);
        bad |= (!enabled && x != 0)
          || (address[i + 1] == 0 && x != 0)
          || (enabled && address[i + 1] != 0 && x >= bounds[i] as u128);
        let (term, overflow) = x.overflowing_mul(address[i + 1] as u128);
        bad |= enabled && overflow;
        let (sum, overflow) = offset.overflowing_add(term);
        bad |= enabled && overflow;
        offset = sum;
      }
      let width = (g.layout.record_words(g.kind) * 16) as u64;
      let (end, overflow) = offset.overflowing_add(width as u128);
      bad |= enabled
        && (overflow
          || end > g.layout.bytes() as u128
          || offset > u64::MAX as u128);
      let offset = if enabled { offset as u64 } else { 0 };
      let first = (offset / 1024).min((g.layout.bytes() - 1) / 1024);
      let next = (first + 1).min((g.layout.bytes() - 1) / 1024);
      vec![
        F128::new(offset, g.layout.bytes()),
        F128::new(if enabled { width } else { 0 }, 0),
        F128::new(first, 0),
        F128::new(next, 0),
      ]
    },
    CodeOp::Record => {
      let n = g.layout.record_words(g.kind);
      bad |= input[1..]
        .iter()
        .enumerate()
        .any(|(i, w)| (i >= n || !enabled) && *w != F128::ZERO);
      bad |= enabled
        && if g.kind == CodeKind::Program {
          input[4].lo as u8 != Phase::Done as u8
        } else {
          input[1] != F128::ONE
        };
      if enabled { input[1..1 + n].to_vec() } else { vec![F128::ZERO; n] }
    },
  };
  out.push(F128::new(u64::from(bad), 0));
  out
}
