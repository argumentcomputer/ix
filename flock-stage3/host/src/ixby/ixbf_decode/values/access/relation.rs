use super::super::super::{
  grammar::Phase,
  synthesis::{Bits, Builder},
};
use super::{ValueAccessGate, ValueAccessOp, ValueKind};
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
fn used(kind: ValueKind) -> [bool; 3] {
  match kind {
    ValueKind::Manifest => [false; 3],
    ValueKind::Node => [true, false, false],
    ValueKind::Child => [true; 3],
    ValueKind::Root => [false, true, true],
  }
}
fn selected(kind: ValueKind) -> Option<usize> {
  match kind {
    ValueKind::Manifest => None,
    ValueKind::Node => Some(1),
    ValueKind::Child | ValueKind::Root => Some(3),
  }
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
pub(super) fn build(g: &ValueAccessGate) -> BooleanR1csPlan {
  let scratch = match g.op {
    ValueAccessOp::Request => {
      16_384 + 1500 * g.layout.address(g.kind)[1].count_ones() as usize
    },
    ValueAccessOp::Record => 8192 + 512 * g.layout.window_words(),
  };
  let mut b = Builder::new(
    g.input_count(),
    g.output_count(),
    128 * (g.input_count() + g.output_count()) + scratch,
  );
  let enabled = word(0)[0];
  b.require_zero(b.one, &word(0)[1..]);
  let disabled = b.not(enabled);
  for (i, used) in used(g.kind).into_iter().enumerate() {
    let x = word(i + 1);
    b.require_zero(if used { disabled } else { b.one }, &x);
    if used {
      let bound = b.constant(128, g.layout.nodes());
      let (_, less) = subtract(&mut b.b, b.one, b.zero, &x, &bound);
      b.require(enabled, less);
    }
  }
  let index = selected(g.kind).map(word).unwrap_or_else(|| b.constant(128, 0));
  match g.op {
    ValueAccessOp::Request => {
      let [base, stride] = g.layout.address(g.kind);
      let mut offset = b.constant(128, base);
      for shift in 0..64 {
        if stride & (1u64 << shift) != 0 {
          b.require_zero(enabled, &index[128 - shift..]);
          let term =
            [vec![b.zero; shift], index[..128 - shift].to_vec()].concat();
          offset = plus(&mut b, enabled, &offset, &term);
        }
      }
      let length = b.constant(128, g.layout.bytes());
      let amount = b.constant(128, (16 * g.layout.record_words(g.kind)) as u64);
      let end = plus(&mut b, enabled, &offset, &amount);
      let (_, outside) = subtract(&mut b.b, b.one, b.zero, &length, &end);
      b.require_zero(enabled, &[outside]);
      b.require_zero(enabled, &offset[64..]);
      let offset = mask(&mut b, enabled, &offset[..64]);
      b.write(4, &[offset.clone(), b.constant(64, g.layout.bytes())].concat());
      let take = mask(&mut b, enabled, &amount);
      b.write(5, &take);
      let first = [offset[10..].to_vec(), vec![b.zero; 10]].concat();
      let one = b.constant(64, 1);
      let next = plus(&mut b, enabled, &first, &one);
      let last = b.constant(64, (g.layout.bytes() - 1) / 1024);
      let (_, outside) = subtract(&mut b.b, b.one, b.zero, &last, &next);
      let next = choose(&mut b, outside, &last, &next);
      b.write(6, &[first, vec![b.zero; 64]].concat());
      b.write(7, &[next, vec![b.zero; 64]].concat());
    },
    ValueAccessOp::Record => {
      let n = g.layout.record_words(g.kind);
      for i in 0..g.layout.window_words() {
        b.require_zero(if i < n { disabled } else { b.one }, &word(4 + i));
      }
      if g.kind == ValueKind::Manifest {
        let phase = b.eq_const(&word(4 + 4 + 1)[..8], Phase::Done as u64);
        b.require(enabled, phase);
      } else {
        let one = b.constant(128, 1);
        let present = b.equal(&word(4), &one);
        b.require(enabled, present);
        if matches!(g.kind, ValueKind::Child | ValueKind::Root) {
          let parent = if g.kind == ValueKind::Root {
            b.constant(128, 0)
          } else {
            plus(&mut b, enabled, &word(1), &one)
          };
          let at = 4 + g.layout.tree_start();
          let same_parent = b.equal(&word(at), &parent);
          let same_ordinal = b.equal(&word(at + 1), &word(2));
          b.require(enabled, same_parent);
          b.require(enabled, same_ordinal);
        }
      }
      let index = mask(&mut b, enabled, &index);
      b.write(g.input_count(), &index);
      for i in 0..n {
        let result = mask(&mut b, enabled, &word(4 + i));
        b.write(g.input_count() + 1 + i, &result);
      }
    },
  }
  b.finish(g.input_count() + g.output_count() - 1)
}
pub(super) fn evaluate(g: &ValueAccessGate, input: &[F128]) -> Vec<F128> {
  let enabled = input[0].lo & 1 != 0;
  let mut bad = value(input[0]) > 1;
  for (i, used) in used(g.kind).into_iter().enumerate() {
    let x = value(input[i + 1]);
    bad |=
      if !used || !enabled { x != 0 } else { x >= g.layout.nodes() as u128 };
  }
  let index = selected(g.kind).map(|i| value(input[i])).unwrap_or(0);
  let mut out = match g.op {
    ValueAccessOp::Request => {
      let [base, stride] = g.layout.address(g.kind);
      let (offset, overflow) = index.overflowing_mul(stride as u128);
      bad |= enabled && overflow;
      let (offset, overflow) = offset.overflowing_add(base as u128);
      bad |= enabled && overflow;
      let width = (16 * g.layout.record_words(g.kind)) as u64;
      let (end, overflow) = offset.overflowing_add(width as u128);
      bad |= enabled
        && (overflow
          || end > g.layout.bytes() as u128
          || offset > u64::MAX as u128);
      let offset = if enabled { offset as u64 } else { 0 };
      let first = offset / 1024;
      let next = (first + 1).min((g.layout.bytes() - 1) / 1024);
      vec![
        F128::new(offset, g.layout.bytes()),
        F128::new(if enabled { width } else { 0 }, 0),
        F128::new(first, 0),
        F128::new(next, 0),
      ]
    },
    ValueAccessOp::Record => {
      let n = g.layout.record_words(g.kind);
      bad |= input[4..]
        .iter()
        .enumerate()
        .any(|(i, w)| (i >= n || !enabled) && *w != F128::ZERO);
      if enabled {
        bad |= if g.kind == ValueKind::Manifest {
          input[9].lo as u8 != Phase::Done as u8
        } else {
          input[4] != F128::ONE
        };
        if matches!(g.kind, ValueKind::Child | ValueKind::Root) {
          let (parent, overflow) = if g.kind == ValueKind::Root {
            (0, false)
          } else {
            value(input[1]).overflowing_add(1)
          };
          let at = 4 + g.layout.tree_start();
          bad |=
            overflow || value(input[at]) != parent || input[at + 1] != input[2];
        }
      }
      let mut out = vec![if enabled {
        F128::new(index as u64, (index >> 64) as u64)
      } else {
        F128::ZERO
      }];
      out.extend(if enabled {
        input[4..4 + n].to_vec()
      } else {
        vec![F128::ZERO; n]
      });
      out
    },
  };
  out.push(F128::new(u64::from(bad), 0));
  out
}
