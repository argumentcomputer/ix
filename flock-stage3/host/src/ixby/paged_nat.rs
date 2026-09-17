//! Exact immediate Nat128 arithmetic for paged execution. Division uses
//! Boolean quotient/remainder advice constrained by a full 256-bit integer
//! identity, a strict remainder bound, and the reference zero-divisor rule.
//! No binary-field product is treated as an integer product.
use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness_into,
    write_f128,
  },
  ixby::bits::{
    add, any, equal, equal_constant, fill_words, not, read_words, require,
    require_zero, subtract,
  },
  multiplication::sum_bit_columns,
  sizing::{CircuitEmitter, CountedGate},
};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{GateType, SlotId, SlotWitness, Wire},
  field::F128,
  r1cs::BlockR1cs,
  schedule::{IoWord, TableType},
  union::SlotWitnessDest,
};
use std::sync::{Arc, OnceLock};

const INPUTS: usize = 5;
const OUTPUTS: usize = 3;
const QUOTIENT: usize = 8 * 128;
const REMAINDER: usize = 9 * 128;
#[derive(Clone, Debug)]
pub struct Nat128Gate {
  nu: usize,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct Nat128Row {
  input: [F128; INPUTS],
  quotient: F128,
  remainder: F128,
}
fn integer(v: F128) -> u128 {
  u128::from(v.lo) | u128::from(v.hi) << 64
}
fn word(v: u128) -> F128 {
  F128::new(v as u64, (v >> 64) as u64)
}
fn fill(row: &Nat128Row, bits: &mut [bool]) {
  fill_words(&row.input, bits);
  write_f128(bits, QUOTIENT, row.quotient);
  write_f128(bits, REMAINDER, row.remainder);
}
impl Nat128Gate {
  pub fn new(nu: usize) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "Nat128 row domain");
    Ok(Self { nu, plan: Arc::new(OnceLock::new()) })
  }
  fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(build)
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[Nat128Row],
    dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    generate_boolean_witness_into(self.plan(), rows, self.nu, dst, fill)
  }
}
impl CountedGate for Nat128Gate {
  fn input_count(&self) -> usize {
    INPUTS
  }
  fn output_count(&self) -> usize {
    OUTPUTS
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}
impl GateType for Nat128Gate {
  type Row = Nat128Row;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..INPUTS)
        .map(IoWord::input)
        .chain((INPUTS..INPUTS + OUTPUTS).map(IoWord::output))
        .collect(),
    )
  }
  fn eval(&self, input: &[F128], _: &(), outputs: &mut Vec<F128>) -> Nat128Row {
    let input: [F128; INPUTS] = input.try_into().unwrap();
    let a = integer(input[2]);
    let b =
      if input[0].lo == 11 { 0xffff_ffff_0000_0001 } else { integer(input[4]) };
    let division = matches!(input[0].lo, 4 | 5 | 11);
    let (q, r) = if division {
      (a.checked_div(b).unwrap_or(0), a.checked_rem(b).unwrap_or(a))
    } else {
      (0, 0)
    };
    let row = Nat128Row { input, quotient: word(q), remainder: word(r) };
    if let Some(out) = native(&row) {
      outputs.extend(out);
    } else {
      let mut bits = vec![false; self.plan().k()];
      self.plan().fill_row(&mut bits, |bits| fill(&row, bits));
      outputs.extend(read_words(&bits, INPUTS, OUTPUTS));
    }
    row
  }
  fn witness(&self, _: &[Nat128Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
/// Control zero is canonical inactive padding; 1..7 mean functional Nat
/// Add/Sub/Mul/Div/Mod/Eq/Lt. The caller must derive it from actual code wires.
/// Revision one also admits 8 = NatToWord32 and 9 = Word32ToNat.
pub struct Nat128Slot {
  slot: SlotId,
  gate: Nat128Gate,
  zero: Wire,
}
impl Nat128Slot {
  pub fn declare(b: &mut impl CircuitEmitter, nu: usize) -> Result<Self> {
    let gate = Nat128Gate::new(nu)?;
    Ok(Self {
      slot: b.slot(gate.clone()),
      gate,
      zero: b.fixed_public_input(F128::ZERO),
    })
  }
  pub fn gate(&self) -> (SlotId, &Nat128Gate) {
    (self.slot, &self.gate)
  }
  pub fn evaluate(
    &self,
    b: &mut impl CircuitEmitter,
    control: Wire,
    a: [Wire; 2],
    c: [Wire; 2],
  ) -> [Wire; 2] {
    let out = b.gate(self.slot, &[control, a[0], a[1], c[0], c[1]]);
    b.connect(out[2], self.zero);
    [out[0], out[1]]
  }
}
fn native(row: &Nat128Row) -> Option<[F128; 3]> {
  let input = row.input;
  let control = input[0].lo;
  if input[0].hi != 0 || control > 11 {
    return None;
  }
  if control == 0 {
    return (input[1..] == [F128::ZERO; 4]).then_some([F128::ZERO; 3]);
  }
  if control >= 8 {
    let tag = match control {
      8 | 11 => 8,
      9 => 2,
      10 => 3,
      _ => unreachable!(),
    };
    let a = integer(input[2]);
    if input[1] != F128::new(tag, 0)
      || input[3..] != [F128::ZERO; 2]
      || (control == 9 && a > u128::from(u32::MAX))
      || (control == 10 && a >= 0xffff_ffff_0000_0001)
    {
      return None;
    }
    let (tag, result) = match control {
      8 => (2, a & u128::from(u32::MAX)),
      9 | 10 => (8, a),
      11 => (3, a % 0xffff_ffff_0000_0001),
      _ => unreachable!(),
    };
    return Some([F128::new(tag, 0), word(result), F128::ZERO]);
  }
  if input[1] != F128::new(8, 0) || input[3] != F128::new(8, 0) {
    return None;
  }
  let a = integer(input[2]);
  let b = integer(input[4]);
  let (result, overflow) = match control {
    1 => a.overflowing_add(b),
    2 => (a.saturating_sub(b), false),
    3 => a.overflowing_mul(b),
    4 => (integer(row.quotient), false),
    5 => (integer(row.remainder), false),
    6 => (u128::from(a == b), false),
    7 => (u128::from(a < b), false),
    _ => unreachable!(),
  };
  Some([
    F128::new(if control >= 6 { 1 } else { 8 }, 0),
    word(result),
    F128::new(u64::from(overflow), 0),
  ])
}
fn range(at: usize, len: usize) -> Vec<usize> {
  (at..at + len).collect()
}
fn build() -> BooleanR1csPlan {
  let mut b = BooleanR1csBuilder::new(17, 10 * 128);
  for bit in 0..INPUTS * 128 {
    b.free_boolean_at(bit);
  }
  for bit in QUOTIENT..REMAINDER + 128 {
    b.free_boolean_at(bit);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let control_bits = 4;
  let flags = (0..=11)
    .map(|i| equal_constant(&mut b, one, &range(0, control_bits), i))
    .collect::<Vec<_>>();
  let mut bad = range(control_bits, 128 - control_bits);
  let valid = b.xor(&flags, one);
  require(&mut b, one, &mut bad, one, valid);
  require_zero(&mut b, one, &mut bad, flags[0], &range(128, 512));
  let binary = b.xor(&flags[1..=7], one);
  for at in [128, 384] {
    let tag = equal_constant(&mut b, one, &range(at, 64), 8);
    require(&mut b, one, &mut bad, binary, tag);
    require_zero(&mut b, one, &mut bad, binary, &range(at + 64, 64));
  }
  for (flag, tag) in
    [(flags[8], 8), (flags[9], 2), (flags[10], 3), (flags[11], 8)]
  {
    let typed = equal_constant(&mut b, one, &range(128, 64), tag);
    require(&mut b, one, &mut bad, flag, typed);
    require_zero(&mut b, one, &mut bad, flag, &range(192, 64));
    require_zero(&mut b, one, &mut bad, flag, &range(384, 256));
  }
  require_zero(&mut b, one, &mut bad, flags[9], &range(288, 96));
  let a = range(256, 128);
  let p = (0..128)
    .map(|i| {
      if i < 64 && 0xffff_ffff_0000_0001u64 & (1 << i) != 0 {
        one
      } else {
        zero
      }
    })
    .collect::<Vec<_>>();
  require_zero(&mut b, one, &mut bad, flags[10], &a[64..]);
  let canonical = subtract(&mut b, one, zero, &a, &p).1;
  require(&mut b, one, &mut bad, flags[10], canonical);
  let rhs = range(512, 128)
    .iter()
    .zip(&p)
    .map(|(&v, &p)| {
      let constant = b.and(flags[11], p);
      b.xor(&[v, constant], one)
    })
    .collect::<Vec<_>>();
  let q = range(QUOTIENT, 128);
  let r = range(REMAINDER, 128);
  let dividing = b.xor(&[flags[4], flags[5], flags[11]], one);
  let not_dividing = not(&mut b, one, dividing);
  require_zero(&mut b, one, &mut bad, not_dividing, &range(QUOTIENT, 256));
  let (sum, carry) = add(&mut b, one, zero, &a, &rhs);
  bad.push(b.and(flags[1], carry));
  let (difference, borrow) = subtract(&mut b, one, zero, &a, &rhs);
  let positive = not(&mut b, one, borrow);
  let difference =
    difference.iter().map(|&bit| b.and(positive, bit)).collect::<Vec<_>>();

  // One carry-save product serves both full multiplication and the exact
  // q*b+r=a certificate. Its upper half cannot be dropped or reduced modulo p.
  let product_enabled = b.xor(&[flags[3], dividing], one);
  let x = a
    .iter()
    .zip(&q)
    .map(|(&a, &q)| {
      let a = b.and(flags[3], a);
      let q = b.and(dividing, q);
      b.xor(&[a, q], one)
    })
    .collect::<Vec<_>>();
  let y =
    rhs.iter().map(|&bit| b.and(product_enabled, bit)).collect::<Vec<_>>();
  let mut columns = vec![Vec::new(); 257];
  for (i, &x) in x.iter().enumerate() {
    for (j, &y) in y.iter().enumerate() {
      columns[i + j].push(b.and(x, y));
    }
  }
  for (i, &r) in r.iter().enumerate() {
    columns[i].push(r);
  }
  let product = sum_bit_columns(&mut b, columns, one, 256)
    .into_iter()
    .map(|bit| bit.unwrap_or(zero))
    .collect::<Vec<_>>();
  require_zero(&mut b, one, &mut bad, flags[3], &product[128..]);
  let mut expected = a.clone();
  expected.resize(256, zero);
  let exact = equal(&mut b, one, &product, &expected);
  require(&mut b, one, &mut bad, dividing, exact);
  let nonzero = any(&mut b, one, &rhs);
  let divisor_zero = not(&mut b, one, nonzero);
  let zero_case = b.and(dividing, divisor_zero);
  require_zero(&mut b, one, &mut bad, zero_case, &q);
  let normal = b.and(dividing, nonzero);
  let remainder_bound = subtract(&mut b, one, zero, &r, &rhs).1;
  require(&mut b, one, &mut bad, normal, remainder_bound);
  let same = equal(&mut b, one, &a, &rhs);
  let comparison_equal = b.and(flags[6], same);
  let comparison_less = b.and(flags[7], borrow);
  let comparison = b.xor(&[comparison_equal, comparison_less], one);
  let mut integer_flags = flags[1..=5].to_vec();
  integer_flags.extend_from_slice(&flags[9..=10]);
  let integer_result = b.xor(&integer_flags, one);
  let boolean_result = b.xor(&flags[6..=7], one);
  b.write_xor(INPUTS * 128, &[boolean_result, flags[11]], one);
  b.write_xor(INPUTS * 128 + 1, &[flags[8], flags[11]], one);
  b.write_xor(INPUTS * 128 + 3, &[integer_result], one);
  for bit in 0..128 {
    let mut terms =
      [(&sum, 1), (&difference, 2), (&product, 3), (&q, 4), (&r, 5)]
        .into_iter()
        .map(|(value, at)| b.and(flags[at], value[bit]))
        .collect::<Vec<_>>();
    if bit == 0 {
      terms.push(comparison);
    }
    if bit < 32 {
      terms.push(b.and(flags[8], a[bit]));
      terms.push(b.and(flags[9], a[bit]));
    }
    if bit < 64 {
      terms.push(b.and(flags[10], a[bit]));
    }
    terms.push(b.and(flags[11], r[bit]));
    b.write_xor((INPUTS + 1) * 128 + bit, &terms, one);
  }
  let violation = any(&mut b, one, &bad);
  b.write_xor((INPUTS + 2) * 128, &[violation], one);
  b.finish()
}

#[cfg(test)]
mod tests {
  use super::*;
  #[test]
  fn conversions_preserve_low_bits_and_constrain_types_padding_and_outputs() {
    let gate = Nat128Gate::new(3).unwrap();
    let table = gate.r1cs();
    for control in [8, 9] {
      let tag = if control == 8 { 8 } else { 2 };
      let values = if control == 8 {
        vec![0, 1, (1 << 32) - 1, 1 << 32, (1 << 65) + 37, u128::MAX]
      } else {
        vec![0, 1, 1 << 31, (1 << 32) - 1]
      };
      for a in values {
        let input = [
          F128::new(control, 0),
          F128::new(tag, 0),
          word(a),
          F128::ZERO,
          F128::ZERO,
        ];
        let mut output = Vec::new();
        let row = gate.eval(&input, &(), &mut output);
        assert_eq!(checked(&gate, &row), output);
        assert_eq!(
          output,
          [
            F128::new(if control == 8 { 2 } else { 8 }, 0),
            word(a & u128::from(u32::MAX)),
            F128::ZERO
          ]
        );
      }
      let row = gate.eval(
        &[
          F128::new(control, 0),
          F128::new(tag, 0),
          word(37),
          F128::ZERO,
          F128::ZERO,
        ],
        &(),
        &mut Vec::new(),
      );
      // A dishonest prover cannot change any tag, payload, or residual bit.
      let mut bits = vec![false; gate.plan().k()];
      gate.plan().fill_row(&mut bits, |bits| fill(&row, bits));
      bits.resize(table.n(), false);
      for bit in INPUTS * 128..(INPUTS + OUTPUTS) * 128 {
        bits[bit] = !bits[bit];
        assert!(!table.satisfies(&bits), "unconstrained output bit {bit}");
        bits[bit] = !bits[bit];
      }
      for at in [1, 3, 4] {
        for bit in 0..128 {
          let mut changed = row.clone();
          changed.input[at] += word(1 << bit);
          assert_eq!(checked(&gate, &changed)[2], F128::ONE);
        }
      }
      for bit in 0..128 {
        let mut changed = row.clone();
        changed.input[2] += word(1 << bit);
        let out = checked(&gate, &changed);
        assert_eq!(
          out[2],
          if control == 9 && bit >= 32 { F128::ONE } else { F128::ZERO }
        );
        if out[2] == F128::ZERO {
          assert_eq!(
            out[1],
            word(integer(changed.input[2]) & u128::from(u32::MAX))
          );
        }
        for quotient in [true, false] {
          let mut changed = row.clone();
          if quotient {
            changed.quotient = word(1 << bit);
          } else {
            changed.remainder = word(1 << bit);
          }
          assert_eq!(checked(&gate, &changed)[2], F128::ONE);
        }
      }
    }
    for control in 12..16 {
      let row = gate.eval(
        &[
          F128::new(control, 0),
          F128::ZERO,
          F128::ZERO,
          F128::ZERO,
          F128::ZERO,
        ],
        &(),
        &mut Vec::new(),
      );
      assert_eq!(checked(&gate, &row)[2], F128::ONE);
    }
  }
  fn checked(gate: &Nat128Gate, row: &Nat128Row) -> Vec<F128> {
    let mut bits = vec![false; gate.plan().k()];
    gate.plan().fill_row(&mut bits, |bits| fill(row, bits));
    let out = read_words(&bits, INPUTS, OUTPUTS);
    let table = gate.r1cs();
    bits.resize(table.n(), false);
    assert!(table.satisfies(&bits));
    out
  }
  #[test]
  fn field_conversions_bind_canonical_values_and_modular_certificates() {
    let gate = Nat128Gate::new(3).unwrap();
    let table = gate.r1cs();
    let p = 0xffff_ffff_0000_0001u128;
    for control in [10, 11] {
      for a in [0, 1, (1 << 32) - 1, p - 1, p, p + 1, 1 << 65, u128::MAX] {
        let input = [
          word(control),
          word(if control == 10 { 3 } else { 8 }),
          word(a),
          F128::ZERO,
          F128::ZERO,
        ];
        let mut out = Vec::new();
        let row = gate.eval(&input, &(), &mut out);
        let constrained = checked(&gate, &row);
        if control == 10 && a >= p {
          assert_eq!(constrained[2], F128::ONE);
          continue;
        }
        assert_eq!(constrained, out);
        assert_eq!(
          out,
          [word(if control == 10 { 8 } else { 3 }), word(a % p), F128::ZERO]
        );
        let mut bits = vec![false; table.n()];
        gate.plan().fill_row(&mut bits[..gate.plan().k()], |b| fill(&row, b));
        for bit in INPUTS * 128..(INPUTS + OUTPUTS) * 128 {
          bits[bit] ^= true;
          assert!(
            !table.satisfies(&bits),
            "control {control}, output bit {bit}"
          );
          bits[bit] ^= true;
        }
        for bit in 0..128 {
          for at in [1, 3, 4] {
            let mut bad = row.clone();
            bad.input[at] += word(1 << bit);
            assert_eq!(checked(&gate, &bad)[2], F128::ONE);
          }
          for quotient in [true, false] {
            let mut bad = row.clone();
            if quotient {
              bad.quotient += word(1 << bit);
            } else {
              bad.remainder += word(1 << bit);
            }
            assert_eq!(checked(&gate, &bad)[2], F128::ONE);
          }
        }
      }
    }
  }
  #[test]
  fn nat128_matches_exact_integer_semantics_including_zero_divisors_and_overflow()
   {
    let gate = Nat128Gate::new(3).unwrap();
    let values = [
      0,
      1,
      2,
      u32::MAX as u128,
      u64::MAX as u128,
      1 << 64,
      (1 << 65) - 1,
      1 << 127,
      u128::MAX,
    ];
    for control in 1..=7 {
      for &a in &values {
        for &b in &values {
          let input = [
            F128::new(control, 0),
            F128::new(8, 0),
            word(a),
            F128::new(8, 0),
            word(b),
          ];
          let mut native = Vec::new();
          let row = gate.eval(&input, &(), &mut native);
          assert_eq!(
            checked(&gate, &row),
            native,
            "control={control}, a={a}, b={b}"
          );
        }
      }
    }
    let mut native = Vec::new();
    let row = gate.eval(&[F128::ZERO; INPUTS], &(), &mut native);
    assert_eq!(checked(&gate, &row), [F128::ZERO; OUTPUTS]);
    eprintln!("Nat128: {} useful Boolean columns", gate.plan().useful_bits());
  }
  #[test]
  fn quotient_remainder_and_high_product_bits_are_constrained() {
    let gate = Nat128Gate::new(3).unwrap();
    for (a, b) in [
      (u128::MAX, 0),
      (u128::MAX, 1),
      (u128::MAX, 1 << 64),
      ((1 << 65) - 1, 37),
    ] {
      let mut out = Vec::new();
      let row = gate.eval(
        &[F128::new(4, 0), F128::new(8, 0), word(a), F128::new(8, 0), word(b)],
        &(),
        &mut out,
      );
      assert_eq!(checked(&gate, &row)[2], F128::ZERO);
      for quotient in [true, false] {
        for bit in 0..128 {
          let mut changed = row.clone();
          let value = if quotient {
            &mut changed.quotient
          } else {
            &mut changed.remainder
          };
          *value += word(1 << bit);
          assert_eq!(checked(&gate, &changed)[2], F128::ONE);
        }
      }
    }
    // q*b+r matches a modulo 2^128 but has a nonzero high half.
    let row = Nat128Row {
      input: [
        F128::new(4, 0),
        F128::new(8, 0),
        F128::ZERO,
        F128::new(8, 0),
        word(1 << 127),
      ],
      quotient: word(2),
      remainder: F128::ZERO,
    };
    assert_eq!(checked(&gate, &row)[2], F128::ONE);
  }

  #[test]
  fn nat128_advice_and_padding_match_the_complete_matrices() {
    let gate = Nat128Gate::new(3).unwrap();
    let rows = [0, 1, 4, 5, 7]
      .into_iter()
      .map(|control| {
        let input = if control == 0 {
          [F128::ZERO; INPUTS]
        } else {
          [
            F128::new(control, 0),
            F128::new(8, 0),
            word((1 << 65) - 1),
            F128::new(8, 0),
            word(37),
          ]
        };
        gate.eval(&input, &(), &mut Vec::new())
      })
      .collect::<Vec<_>>();
    crate::ixby::test_support::padding(gate.plan(), &rows, fill, |dst| {
      gate.generate_witness_into(&rows, dst)
    });
  }
}
