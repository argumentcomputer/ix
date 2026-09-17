//! Exact marginals of Flock's eight-plane circuit-structure table.
//!
//! The pinned table has three live-cell planes, two row-independent element
//! constant planes, one Boolean-pin prefix plane, and two zero planes. Walk
//! live cells once and sum the constant/prefix planes analytically instead of
//! evaluating every entry of its padded rectangle. This changes no table,
//! transcript, circuit, or verifier claim.
use flock_prover::{
  circuit::{Circuit, SigmaAssertion},
  field::F128,
  matrix_fold::FoldMatrix,
};
use rayon::prelude::*;

pub(crate) struct StructureMatrix<'a> {
  circuit: &'a Circuit,
  rows: usize,
  columns: usize,
  counts: Vec<usize>,
  affine: Vec<(usize, F128, F128)>,
  pins: Vec<(usize, usize)>,
}
impl<'a> StructureMatrix<'a> {
  pub(crate) fn new(circuit: &'a Circuit) -> Self {
    let reference = SigmaAssertion::matrix(circuit);
    let rows = reference.n_rows();
    let columns = reference.n_cols() / 8;
    let registry = circuit.registry();
    let nb = registry.num_boolean();
    let base = registry.element_base() >> 7;
    let mut affine = Vec::new();
    for (ty, slot) in registry.types()[nb..].iter().zip(&registry.slots()[nb..])
    {
      let element = ty.element_type().expect("element registry suffix");
      let offset = ((slot.offset >> 7) - base) >> registry.nu();
      for (i, (&a, &b)) in
        element.a_const().iter().zip(element.b_const()).enumerate()
      {
        if a != F128::ZERO || b != F128::ZERO {
          affine.push((offset + i, a, b));
        }
      }
    }
    let pins = registry
      .boolean_types()
      .iter()
      .enumerate()
      .filter_map(|(i, ty)| ty.const_pin.map(|_| (i, circuit.counts()[i])))
      .collect();
    Self {
      circuit,
      rows,
      columns,
      counts: circuit.live_mask().counts,
      affine,
      pins,
    }
  }
}
impl FoldMatrix for StructureMatrix<'_> {
  fn row_marginal(&self, weights: &[F128], rows: usize) -> Vec<F128> {
    assert_eq!(rows, self.n_rows());
    assert_eq!(weights.len(), self.n_cols());
    let k = self.columns;
    let affine = self.affine.iter().fold(F128::ZERO, |sum, &(i, a, b)| {
      sum + weights[3 * k + i] * a + weights[4 * k + i] * b
    });
    let mut out = vec![affine; rows];
    out.par_chunks_mut(256).enumerate().for_each(|(chunk, values)| {
      let first = chunk * 256;
      for (slot, &count) in self.counts.iter().enumerate() {
        let active = count.saturating_sub(first).min(values.len());
        if active == 0 {
          continue;
        }
        let id = weights[slot];
        let live = weights[k + slot];
        let sigma = weights[2 * k + slot];
        if id == F128::ZERO && live == F128::ZERO && sigma == F128::ZERO {
          continue;
        }
        let base = slot * rows;
        let constant = live + id * F128::new(base as u64, 0);
        for (i, value) in values[..active].iter_mut().enumerate() {
          let row = first + i;
          *value += constant
            + id * F128::new(row as u64, 0)
            + sigma * F128::new(self.circuit.sigma()[base + row] as u64, 0);
        }
      }
      for &(slot, count) in &self.pins {
        let active = count.saturating_sub(first).min(values.len());
        let weight = weights[5 * k + slot];
        if weight != F128::ZERO {
          for value in &mut values[..active] {
            *value += weight;
          }
        }
      }
    });
    out
  }

  fn col_marginal(&self, weights: &[F128], columns: usize) -> Vec<F128> {
    assert_eq!(weights.len(), self.n_rows());
    assert_eq!(columns, self.n_cols());
    let mut prefix = Vec::with_capacity(weights.len() + 1);
    let mut id_prefix = Vec::with_capacity(weights.len() + 1);
    prefix.push(F128::ZERO);
    id_prefix.push(F128::ZERO);
    for (row, &weight) in weights.iter().enumerate() {
      prefix.push(prefix[row] + weight);
      id_prefix.push(id_prefix[row] + weight * F128::new(row as u64, 0));
    }
    let cells = self
      .counts
      .par_iter()
      .enumerate()
      .map(|(slot, &count)| {
        let base = slot * self.rows;
        let sigma = weights[..count]
          .iter()
          .zip(&self.circuit.sigma()[base..base + count])
          .fold(F128::ZERO, |sum, (&weight, &target)| {
            sum + weight * F128::new(target as u64, 0)
          });
        [
          F128::new(base as u64, 0) * prefix[count] + id_prefix[count],
          prefix[count],
          sigma,
        ]
      })
      .collect::<Vec<_>>();
    let k = self.columns;
    let mut out = vec![F128::ZERO; columns];
    for (slot, [id, live, sigma]) in cells.into_iter().enumerate() {
      out[slot] = id;
      out[k + slot] = live;
      out[2 * k + slot] = sigma;
    }
    for &(slot, a, b) in &self.affine {
      out[3 * k + slot] = a * prefix[self.rows];
      out[4 * k + slot] = b * prefix[self.rows];
    }
    for &(slot, count) in &self.pins {
      out[5 * k + slot] = prefix[count];
    }
    out
  }

  fn n_rows(&self) -> usize {
    self.rows
  }
  fn n_cols(&self) -> usize {
    8 * self.columns
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::gates::MacGate;
  use flock_prover::{
    circuit::builder::{GateType, ShapeBuilder, SlotWitness},
    element_r1cs::{ElementTableType, SparseF128Matrix},
    matrix_fold::{MatrixClaim, Weight},
    schedule::{IoWord, TableType},
  };
  use ixby_flock::hash::Blake3Gate;
  use std::sync::Arc;

  struct AffineGate;
  impl GateType for AffineGate {
    type Row = ();
    type Hint = ();
    fn table(&self) -> TableType {
      let a = SparseF128Matrix::from_rows(
        "a",
        4,
        vec![vec![(0, F128::ONE)], vec![(1, F128::ONE)], vec![], vec![]],
      )
      .unwrap();
      let b = SparseF128Matrix::from_rows(
        "b",
        4,
        vec![vec![(1, F128::ONE)], vec![], vec![], vec![]],
      )
      .unwrap();
      let ty = ElementTableType::new(
        2,
        3,
        a,
        b,
        vec![F128::new(0, 0x12345678), F128::ZERO, F128::ZERO, F128::ZERO],
        vec![F128::ZERO, F128::new(0x98765432, 7), F128::ZERO, F128::ZERO],
      )
      .unwrap();
      TableType::element(Arc::new(ty))
        .with_io_schema((0..3).map(IoWord::input).collect())
    }
    fn eval(&self, _: &[F128], _: &(), _: &mut Vec<F128>) {}
    fn witness(&self, _: &[()], _: usize) -> SlotWitness {
      unreachable!("shape-only differential fixture")
    }
  }

  fn shape(
    nu: usize,
    boolean: bool,
    element: bool,
    counts: [usize; 3],
    publics: usize,
  ) -> flock_prover::circuit::builder::CircuitShape {
    let mut b = ShapeBuilder::new(nu);
    let mut slots = Vec::new();
    if boolean {
      slots.push((b.slot(Blake3Gate { nu }), counts[0]));
    }
    if element {
      slots.push((b.slot(MacGate), counts[1]));
      slots.push((b.slot(AffineGate), counts[2]));
    }
    let mut wires = (0..publics).map(|_| b.public_input()).collect::<Vec<_>>();
    wires.extend((0..7).map(|_| b.input()));
    for (slot, count) in slots {
      for row in 0..count {
        let inputs = (0..b.slot_inputs(slot))
          .map(|i| wires[(i * 3 + row) % wires.len()])
          .collect::<Vec<_>>();
        for output in b.gate(slot, &inputs) {
          let sink = b.public_input();
          b.connect(sink, output);
        }
      }
    }
    b.finish().unwrap()
  }

  fn weights(n: usize, salt: u64) -> Vec<F128> {
    (0..n)
      .map(|i| {
        let x = (i as u64).wrapping_mul(0x9e3779b97f4a7c15).wrapping_add(salt);
        F128::new(x.rotate_left(13), x.rotate_right(11) ^ 0xa5a5a5a5a5a5a5a5)
      })
      .collect()
  }

  #[test]
  fn marginals_match_pinned_table_for_all_planes_and_partial_rows() {
    for (nu, boolean, element, counts, publics) in [
      (3, true, false, [0, 0, 0], 0),
      (3, true, false, [7, 0, 0], 9),
      (3, false, true, [0, 8, 1], 0),
      (4, true, true, [3, 7, 16], 3),
      (4, true, true, [16, 0, 1], 19),
      (2, false, true, [0, 0, 0], 5),
      (9, true, true, [257, 511, 19], 519),
    ] {
      let shape = shape(nu, boolean, element, counts, publics);
      let fast = StructureMatrix::new(&shape.circuit);
      let reference = SigmaAssertion::matrix(&shape.circuit);
      assert_eq!(
        (fast.n_rows(), fast.n_cols()),
        (reference.n_rows(), reference.n_cols())
      );
      let row = weights(fast.n_rows(), 3);
      let column = weights(fast.n_cols(), 9);
      assert_eq!(
        fast.col_marginal(&row, fast.n_cols()),
        reference.col_marginal(&row, fast.n_cols())
      );
      assert_eq!(
        fast.row_marginal(&column, fast.n_rows()),
        reference.row_marginal(&column, fast.n_rows())
      );
      for plane in 0..8 {
        let mut one_plane = vec![F128::ZERO; fast.n_cols()];
        let range = plane * fast.columns..(plane + 1) * fast.columns;
        one_plane[range.clone()].copy_from_slice(&column[range]);
        assert_eq!(
          fast.row_marginal(&one_plane, fast.n_rows()),
          reference.row_marginal(&one_plane, fast.n_rows()),
          "plane {plane}"
        );
      }
      for at in [0, fast.n_rows() / 2, fast.n_rows() - 1] {
        let mut unit = vec![F128::ZERO; fast.n_rows()];
        unit[at] = F128::ONE;
        assert_eq!(
          fast.col_marginal(&unit, fast.n_cols()),
          reference.col_marginal(&unit, fast.n_cols())
        );
      }
      let mut claim = MatrixClaim::honest(
        Weight::low_eq(row, vec![]),
        Weight::low_eq(column, vec![]),
        &reference,
      );
      assert!(claim.check_direct(&fast));
      claim.value += F128::ONE;
      assert!(!claim.check_direct(&fast));
    }
  }
}
