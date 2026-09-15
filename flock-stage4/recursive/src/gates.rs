//! Fixed native tables. Every live row is checked by Flock's element PIOP;
//! unused rows satisfy the required all-zero padding convention.
use flock_prover::{
  circuit::builder::{GateType, SlotWitness},
  element_r1cs::{ElementTableBuilder, ElementTableType},
  field::F128,
  schedule::{IoWord, TableType},
};
use ixby_flock::sizing::CountedGate;
use std::sync::Arc;

pub(crate) const MACS_PER_ROW: usize = 64;
pub(crate) struct MacGate;
pub(crate) struct PackGate;

fn mac_table() -> Arc<ElementTableType> {
  let mut b = ElementTableBuilder::new(9);
  for i in 0..MACS_PER_ROW {
    let at = 4 * i;
    let tmp = 4 * MACS_PER_ROW + i;
    b.free_wire(at)
      .free_wire(at + 1)
      .free_wire(at + 2)
      .mult(tmp, at, at + 1)
      .linear(at + 3, &[(tmp, F128::ONE), (at + 2, F128::ONE)]);
  }
  Arc::new(b.build().unwrap())
}
fn pack_table() -> Arc<ElementTableType> {
  let mut b = ElementTableBuilder::new(8);
  let mut terms = Vec::with_capacity(128);
  for i in 0..128 {
    b.mult(i, i, i); // b^2=b in a field iff b is zero or one.
    let basis =
      if i < 64 { F128::new(1 << i, 0) } else { F128::new(0, 1 << (i - 64)) };
    terms.push((i, basis));
  }
  b.linear(128, &terms);
  Arc::new(b.build().unwrap())
}
fn witness(rows: &[Vec<F128>], nu: usize, width: usize) -> SlotWitness {
  let mut z = vec![F128::ZERO; width << nu];
  for (j, row) in rows.iter().enumerate() {
    for (i, &v) in row.iter().enumerate() {
      z[(i << nu) + j] = v;
    }
  }
  SlotWitness::Element(z)
}
impl GateType for MacGate {
  type Row = Vec<F128>;
  type Hint = ();
  fn table(&self) -> TableType {
    TableType::element(mac_table())
      .with_io_schema((0..4 * MACS_PER_ROW).map(IoWord::input).collect())
  }
  fn eval(&self, input: &[F128], _: &(), _: &mut Vec<F128>) -> Vec<F128> {
    let mut row = input.to_vec();
    row.extend(input.as_chunks::<4>().0.iter().map(|v| v[0] * v[1]));
    row
  }
  fn witness(&self, rows: &[Vec<F128>], nu: usize) -> SlotWitness {
    witness(rows, nu, 512)
  }
}
impl CountedGate for MacGate {
  fn input_count(&self) -> usize {
    4 * MACS_PER_ROW
  }
  fn output_count(&self) -> usize {
    0
  }
  fn table_at(&self, _: usize) -> TableType {
    self.table()
  }
}
impl GateType for PackGate {
  type Row = Vec<F128>;
  type Hint = ();
  fn table(&self) -> TableType {
    TableType::element(pack_table())
      .with_io_schema((0..129).map(IoWord::input).collect())
  }
  fn eval(&self, input: &[F128], _: &(), _: &mut Vec<F128>) -> Vec<F128> {
    input.to_vec()
  }
  fn witness(&self, rows: &[Vec<F128>], nu: usize) -> SlotWitness {
    witness(rows, nu, 256)
  }
}
impl CountedGate for PackGate {
  fn input_count(&self) -> usize {
    129
  }
  fn output_count(&self) -> usize {
    0
  }
  fn table_at(&self, _: usize) -> TableType {
    self.table()
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  #[test]
  fn native_tables_constrain_results_bits_packing_and_padding() {
    let mut inputs = Vec::new();
    for i in 0..MACS_PER_ROW {
      let a = F128::new(0x1234567812345678 + i as u64, 0x8989898912121212);
      let b = F128::new(0xaaaa000088884444, 0x9876543212345678 + i as u64);
      let c = F128::new(i as u64, i as u64 + 1);
      inputs.extend([a, b, c, a * b + c]);
    }
    let row = MacGate.eval(&inputs, &(), &mut vec![]);
    let SlotWitness::Element(mut witness) = MacGate.witness(&[row], 1) else {
      panic!()
    };
    assert!(mac_table().satisfies(&witness, 1, 1));
    witness[3 << 1] += F128::ONE;
    assert!(!mac_table().satisfies(&witness, 1, 1));
    witness[3 << 1] += F128::ONE;
    witness[1] = F128::ONE;
    assert!(!mac_table().satisfies(&witness, 1, 1));

    let value = F128::new(0x1234567887654321, 0xfedcba9801234567);
    let mut row = (0..128)
      .map(|i| {
        F128::new(
          if i < 64 { value.lo >> i & 1 } else { value.hi >> (i - 64) & 1 },
          0,
        )
      })
      .collect::<Vec<_>>();
    row.push(value);
    let SlotWitness::Element(mut witness) = PackGate.witness(&[row], 1) else {
      panic!()
    };
    assert!(pack_table().satisfies(&witness, 1, 1));
    witness[128 << 1] += F128::ONE;
    assert!(!pack_table().satisfies(&witness, 1, 1));
    witness[128 << 1] += F128::ONE;
    witness[0] = F128::new(2, 0);
    assert!(!pack_table().satisfies(&witness, 1, 1));
  }
}
