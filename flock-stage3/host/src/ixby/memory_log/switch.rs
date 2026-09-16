use crate::sizing::CountedGate;
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{GateType, SlotWitness},
  element_r1cs::{ElementTableBuilder, ElementTableType},
  field::F128,
  schedule::{IoWord, TableType},
};
use std::sync::{Arc, OnceLock};

/// Sixteen independent whole-record switches share one element row. Every
/// selector satisfies s*s=s, which permits exactly zero or one in F128.
pub(super) const SWITCHES_PER_ROW: usize = 16;

#[derive(Clone)]
pub struct SwitchGate {
  words: usize,
  table: Arc<OnceLock<Arc<ElementTableType>>>,
}
#[derive(Clone, Debug)]
pub struct SwitchRow(pub(super) Vec<F128>);

impl SwitchGate {
  pub fn new(words: usize) -> Result<Self> {
    ensure!((1..=16).contains(&words), "memory record word capacity");
    Ok(Self { words, table: Arc::new(OnceLock::new()) })
  }
  pub fn record_words(&self) -> usize {
    self.words
  }
  pub fn element_table(&self) -> &Arc<ElementTableType> {
    self.table.get_or_init(|| {
      let input = self.input_count();
      let output = self.output_count();
      let columns = input + output + SWITCHES_PER_ROW * self.words;
      let mut b =
        ElementTableBuilder::new(columns.next_power_of_two().ilog2() as usize);
      for lane in 0..SWITCHES_PER_ROW {
        let at = lane * (1 + 2 * self.words);
        b.mult(at, at, at);
        for word in 0..self.words {
          let left = at + 1 + word;
          let right = left + self.words;
          let delta = input + output + lane * self.words + word;
          let out = input + 2 * lane * self.words + word;
          b.free_wire(left)
            .free_wire(right)
            .mult_lin(
              delta,
              &[(at, F128::ONE)],
              &[(left, F128::ONE), (right, F128::ONE)],
            )
            .linear(out, &[(left, F128::ONE), (delta, F128::ONE)])
            .linear(
              out + self.words,
              &[(right, F128::ONE), (delta, F128::ONE)],
            );
        }
      }
      Arc::new(b.build().unwrap())
    })
  }
  pub fn fill_witness(&self, rows: &[SwitchRow], nu: usize, dst: &mut [F128]) {
    assert!(rows.len() <= 1usize << nu);
    assert_eq!(dst.len(), self.element_table().width() << nu);
    // Required even for a recycled destination: all unused rows and columns
    // belong to the committed polynomial and must use canonical zero padding.
    dst.fill(F128::ZERO);
    for (row, values) in rows.iter().enumerate() {
      for (column, &value) in values.0.iter().enumerate() {
        dst[(column << nu) + row] = value;
      }
    }
  }
}
impl CountedGate for SwitchGate {
  fn input_count(&self) -> usize {
    SWITCHES_PER_ROW * (1 + 2 * self.words)
  }
  fn output_count(&self) -> usize {
    SWITCHES_PER_ROW * 2 * self.words
  }
  fn table_at(&self, _: usize) -> TableType {
    self.table()
  }
}
impl GateType for SwitchGate {
  type Row = SwitchRow;
  type Hint = ();
  fn table(&self) -> TableType {
    TableType::element(self.element_table().clone()).with_io_schema(
      (0..self.input_count())
        .map(IoWord::input)
        .chain(
          (self.input_count()..self.input_count() + self.output_count())
            .map(IoWord::output),
        )
        .collect(),
    )
  }
  fn eval(&self, input: &[F128], _: &(), outputs: &mut Vec<F128>) -> SwitchRow {
    assert_eq!(input.len(), self.input_count());
    let mut row = input.to_vec();
    let mut deltas = Vec::with_capacity(SWITCHES_PER_ROW * self.words);
    for lane in input.chunks_exact(1 + 2 * self.words) {
      let (left, right) = lane[1..].split_at(self.words);
      let delta = left
        .iter()
        .zip(right)
        .map(|(&x, &y)| lane[0] * (x + y))
        .collect::<Vec<_>>();
      row.extend(left.iter().zip(&delta).map(|(&x, &d)| x + d));
      row.extend(right.iter().zip(&delta).map(|(&y, &d)| y + d));
      deltas.extend(delta);
    }
    outputs.extend_from_slice(&row[self.input_count()..]);
    row.extend(deltas);
    SwitchRow(row)
  }
  fn witness(&self, rows: &[SwitchRow], nu: usize) -> SlotWitness {
    let mut z = vec![F128::ZERO; self.element_table().width() << nu];
    self.fill_witness(rows, nu, &mut z);
    SlotWitness::Element(z)
  }
}
