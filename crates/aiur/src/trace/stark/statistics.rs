//! Raw execution feedback for the Lean statistics and benchmark layer.
//! Circuit widths and counts belong to the backend; cost models do not.
use super::{Backend, CircuitStatistics, WitnessField};
use crate::Execution;
use multi_stark::{
  p3_field::BasedVectorSpace,
  types::{ExtVal, Val},
};
use serde::Serialize;

#[derive(Serialize)]
pub struct CircuitMeasurements {
  #[serde(flatten)]
  pub shape: CircuitStatistics,
  pub rows: usize,
  pub cache_hits: u64,
}

#[derive(Serialize)]
pub struct ExecutionStatistics {
  pub log_blowup: usize,
  pub extension_degree: usize,
  pub circuits: Vec<CircuitMeasurements>,
}

impl<B: WitnessField> Backend<'_, '_, B> {
  /// Raw unpadded heights and memoization counts in canonical circuit order.
  /// Fixed tables always use their full height and have no cache savings.
  /// No witness matrices or proofs are allocated.
  pub fn execution_statistics(
    &self,
    record: &Execution<B>,
  ) -> ExecutionStatistics {
    let mut hits = Vec::with_capacity(self.system.circuits.len());
    for members in &self.members {
      hits.push(
        members
          .iter()
          .map(|&f| {
            let table = &record.queries.tables[f];
            (0..table.len())
              .map(|r| table.count(r).saturating_sub(1))
              .sum::<u64>()
          })
          .sum(),
      );
    }
    hits.extend(std::iter::repeat_n(0, self.tables.len()));
    for &width in &self.rom.widths {
      hits.push(
        record
          .memory
          .indices_for_width(width)
          .iter()
          .map(|&i| {
            record
              .memory
              .get(i)
              .expect("ROM row")
              .multiplicity
              .saturating_sub(1)
          })
          .sum(),
      );
    }
    ExecutionStatistics {
      log_blowup: self.parameters.log_blowup,
      extension_degree: <ExtVal as BasedVectorSpace<Val>>::DIMENSION,
      circuits: self
        .statistics()
        .into_iter()
        .zip(self.execution_rows(record))
        .zip(hits)
        .map(|((shape, rows), cache_hits)| CircuitMeasurements {
          shape,
          rows,
          cache_hits,
        })
        .collect(),
    }
  }
}
