use super::{BLOCKS, CONSTRUCTORS, CodeGate, CodeGateKind, FUNCTIONS};
use crate::{
  boolean::{BooleanR1csBuilder, BooleanR1csPlan},
  ixby::{
    bits::{
      add, any, equal, equal_constant, not, require, require_zero, subtract,
    },
    ixbf::Primitive,
    paged_frame::LOCALS,
    paged_value,
  },
  sizing::CountedGate,
};
type Bits = Vec<usize>;
struct S {
  b: BooleanR1csBuilder,
  one: usize,
  zero: usize,
  bad: Vec<usize>,
}
impl S {
  fn new(gate: &CodeGate) -> Self {
    let k = match gate.kind() {
      CodeGateKind::Operand => 16,
      CodeGateKind::Block => 14,
      _ => 13,
    };
    let mut b = BooleanR1csBuilder::new(
      k,
      128 * (gate.input_count() + gate.output_count()),
    );
    for bit in 0..gate.input_count() * 128 {
      b.free_boolean_at(bit);
    }
    let one = b.alloc_constant_one();
    let zero = b.xor(&[one, one], one);
    Self { b, one, zero, bad: Vec::new() }
  }
  fn c(&self, n: usize, v: u64) -> Bits {
    (0..n)
      .map(|i| if i < 64 && v & (1 << i) != 0 { self.one } else { self.zero })
      .collect()
  }
  fn eqc(&mut self, a: &[usize], v: u64) -> usize {
    equal_constant(&mut self.b, self.one, a, v)
  }
  fn eq(&mut self, a: &[usize], b: &[usize]) -> usize {
    equal(&mut self.b, self.one, a, b)
  }
  fn sum(&mut self, a: &[usize]) -> usize {
    self.b.xor(a, self.one)
  }
  fn and(&mut self, a: usize, b: usize) -> usize {
    self.b.and(a, b)
  }
  fn inv(&mut self, a: usize) -> usize {
    not(&mut self.b, self.one, a)
  }
  fn need(&mut self, f: usize, good: usize) {
    require(&mut self.b, self.one, &mut self.bad, f, good);
  }
  fn zeros(&mut self, f: usize, bits: &[usize]) {
    require_zero(&mut self.b, self.one, &mut self.bad, f, bits);
  }
  fn unused(&mut self, used: usize, bits: &[usize]) {
    let f = self.inv(used);
    self.zeros(f, bits);
  }
  fn mask(&mut self, f: usize, bits: &[usize]) -> Bits {
    bits.iter().map(|&bit| self.and(f, bit)).collect()
  }
  fn add(&mut self, a: &[usize], b: &[usize]) -> Bits {
    add(&mut self.b, self.one, self.zero, a, b).0
  }
  fn lt(&mut self, a: &[usize], b: &[usize]) -> usize {
    subtract(&mut self.b, self.one, self.zero, a, b).1
  }
  fn bound(&mut self, f: usize, a: &[usize], max: u64) {
    let mut a = a.to_vec();
    a.resize(64, self.zero);
    let good = self.lt(&a, &self.c(64, max + 1));
    self.need(f, good);
  }
  fn frame(&mut self, enabled: usize) {
    self.zeros(enabled, &bits(128, 8));
    self.bound(enabled, &bits(136, 16), 1023);
    self.bound(enabled, &bits(160, 8), 128);
    self.zeros(enabled, &bits(168, 8));
    self.bound(enabled, &bits(176, 16), 1024);
    self.zeros(enabled, &bits(192, 64));
  }
  fn code_address(&self, offset: &[usize]) -> Bits {
    let mut out = self.c(128, BLOCKS);
    out[..8].copy_from_slice(offset);
    out[8..16].copy_from_slice(&bits(152, 8));
    out[16..32].copy_from_slice(&bits(136, 16));
    out
  }
  fn read(
    &mut self,
    out: &mut Bits,
    enabled: usize,
    address: &[usize],
    value: &[usize],
  ) {
    out.extend(self.mask(enabled, address));
    out.extend(self.c(128, 0));
    out.extend(value);
  }
}
fn bits(at: usize, n: usize) -> Bits {
  (at..at + n).collect()
}

fn header(s: &mut S, enabled: usize) {
  let h = 256;
  s.unused(enabled, &bits(h, 256));
  s.zeros(enabled, &bits(h + 56, 8));
  s.zeros(enabled, &bits(h + 112, 144));
  let locals = bits(h, 8);
  let inst = bits(h + 8, 8);
  let op = bits(h + 16, 8);
  let primitive = bits(h + 24, 8);
  let operands = bits(h + 32, 8);
  let args = bits(h + 40, 8);
  let alternatives = bits(h + 48, 8);
  let reference = bits(h + 64, 16);
  let target = bits(h + 80, 8);
  let other = bits(h + 88, 8);
  let projection = bits(h + 96, 16);
  let matches = (0..8).map(|i| s.eqc(&inst, i)).collect::<Vec<_>>();
  let valid = s.sum(&matches);
  s.need(enabled, valid);
  let i =
    matches.into_iter().map(|flag| s.and(enabled, flag)).collect::<Vec<_>>();
  let matches = (0..8).map(|i| s.eqc(&op, i)).collect::<Vec<_>>();
  let valid = s.sum(&matches);
  s.need(i[0], valid);
  s.unused(i[0], &op);
  let o = matches.into_iter().map(|flag| s.and(i[0], flag)).collect::<Vec<_>>();
  let equal_locals = s.eq(&locals, &bits(160, 8));
  s.need(enabled, equal_locals);
  let vector = s.sum(&[o[1], o[2], o[4], o[5], o[6], o[7], i[2], i[3], i[4]]);
  s.unused(vector, &args);
  s.bound(vector, &args, 64);
  let main = s.sum(&[o[0], o[3], o[7], i[1], i[4], i[5], i[6], i[7]]);
  let mut extra = s.c(8, 0);
  extra[0] = main;
  let total = s.add(&args, &extra);
  let total_ok = s.eq(&operands, &total);
  s.need(enabled, total_ok);
  s.unused(o[1], &primitive);
  let prim_matches = Primitive::ALL
    .iter()
    .map(|p| s.eqc(&primitive, u64::from(p.opcode())))
    .collect::<Vec<_>>();
  let prim_valid = s.sum(&prim_matches);
  s.need(o[1], prim_valid);
  let mut arity = s.c(8, 0);
  for (p, &flag) in Primitive::ALL.iter().zip(&prim_matches) {
    for (bit, output) in arity.iter_mut().enumerate() {
      if p.arity() & (1 << bit) != 0 {
        *output = s.sum(&[*output, flag]);
      }
    }
  }
  let right_arity = s.eq(&args, &arity);
  s.need(o[1], right_arity);
  s.unused(i[5], &alternatives);
  s.bound(i[5], &alternatives, 128);
  let function_ref = s.sum(&[o[4], o[5], i[2]]);
  let ref_used = s.sum(&[function_ref, o[2]]);
  s.unused(ref_used, &reference);
  s.bound(function_ref, &reference, 1023);
  s.bound(o[2], &reference, 255);
  let target_used = s.sum(&[i[0], i[6], i[7]]);
  s.unused(target_used, &target);
  let other_used = s.sum(&[i[6], i[7]]);
  s.unused(other_used, &other);
  s.unused(o[3], &projection);
}

pub(super) fn build(gate: &CodeGate) -> BooleanR1csPlan {
  let mut s = S::new(gate);
  let one = s.one;
  let enabled = 0;
  s.zeros(one, &bits(1, 127));
  let mut out = Vec::new();
  match gate.kind() {
    CodeGateKind::Block => {
      s.frame(enabled);
      header(&mut s, enabled);
      let address = s.code_address(&s.c(8, 0));
      s.read(&mut out, enabled, &address, &bits(256, 256));
    },
    CodeGateKind::Function | CodeGateKind::Constructor => {
      let constructor = gate.kind() == CodeGateKind::Constructor;
      s.unused(enabled, &bits(128, 384));
      s.zeros(enabled, &bits(138, 118));
      s.bound(enabled, &bits(128, 10), if constructor { 255 } else { 1023 });
      let address = if constructor {
        let index = bits(128, 10);
        let mut twice = vec![s.zero];
        twice.extend_from_slice(&index[..9]);
        let triple = s.add(&index, &twice);
        let offset = s.add(&triple, &s.c(10, 2));
        let mut address = s.c(128, CONSTRUCTORS);
        address[..10].copy_from_slice(&offset);
        address
      } else {
        let mut address = s.c(128, FUNCTIONS);
        address[..10].copy_from_slice(&bits(128, 10));
        address
      };
      s.bound(enabled, &bits(256, 8), 64);
      if constructor {
        s.zeros(enabled, &bits(264, 248));
      } else {
        s.zeros(enabled, &bits(288, 224));
        let blocks = bits(272, 16);
        s.bound(enabled, &blocks, 256);
        let mut entry = bits(264, 8);
        entry.resize(16, s.zero);
        let valid_entry = s.lt(&entry, &blocks);
        s.need(enabled, valid_entry);
      }
      s.read(&mut out, enabled, &address, &bits(256, 256));
    },
    CodeGateKind::Operand | CodeGateKind::Alternative => {
      let operand = gate.kind() == CodeGateKind::Operand;
      s.frame(enabled);
      s.unused(enabled, &bits(256, (gate.input_count() - 2) * 128));
      s.zeros(enabled, &bits(264, 120));
      s.zeros(enabled, &bits(392, 120));
      let index = bits(256, 8);
      let count = bits(384, 8);
      s.bound(enabled, &count, if operand { 65 } else { 128 });
      let in_range = s.lt(&index, &count);
      s.need(enabled, in_range);
      let offset = s.add(&index, &s.c(8, if operand { 1 } else { 128 }));
      let code_address = s.code_address(&offset);
      s.read(&mut out, enabled, &code_address, &bits(512, 256));
      if operand {
        let local_tag = s.eqc(&bits(512, 64), 0);
        let local = s.and(enabled, local_tag);
        let literal = s.sum(&[enabled, local]);
        s.zeros(local, &bits(576, 64));
        s.zeros(local, &bits(647, 121));
        let slot = bits(640, 8);
        let valid_slot = s.lt(&slot, &bits(160, 8));
        s.need(local, valid_slot);
        let literal_bits = s.mask(literal, &bits(512, 256));
        paged_value::cell(
          &mut s.b,
          s.one,
          &mut s.bad,
          literal,
          &literal_bits,
          true,
        );
        s.unused(local, &bits(768, 256));
        let mut local_address = s.c(128, LOCALS);
        local_address[..7].copy_from_slice(&slot[..7]);
        local_address[7..23].copy_from_slice(&bits(176, 16));
        s.read(&mut out, local, &local_address, &bits(768, 256));
        let local_bits = s.mask(local, &bits(768, 256));
        let value = literal_bits
          .iter()
          .zip(local_bits)
          .map(|(&a, b)| s.sum(&[a, b]))
          .collect::<Vec<_>>();
        paged_value::cell(&mut s.b, s.one, &mut s.bad, enabled, &value, false);
        out.extend(value);
      } else {
        s.zeros(enabled, &bits(528, 240));
      }
    },
  }
  let violation = any(&mut s.b, s.one, &s.bad);
  let mut residual = s.c(128, 0);
  residual[0] = violation;
  out.extend(residual);
  assert_eq!(out.len(), gate.output_count() * 128);
  for (i, bit) in out.into_iter().enumerate() {
    s.b.write_xor(gate.input_count() * 128 + i, &[bit], s.one);
  }
  s.b.finish()
}
