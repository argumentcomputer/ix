//! Scalar quotient evaluation with precomputed coset selectors and reusable
//! per-thread row scratch (no nested Rayon or per-block heap allocations).
use p3_matrix::dense::RowMajorMatrix;
use p3_maybe_rayon::prelude::*;

use super::KzgConfig;
use super::Radix2Coset;
use super::Scalar;
use multi_stark::config::QuotientCommitInput;
use multi_stark::eval::VarValues;
use multi_stark::traits::Algebra;
use multi_stark::traits::EvaluationDomain;
use multi_stark::traits::Field;

const INV_SUB_BLOCK: usize = 1 << 12;

/// Serial Montgomery batch inversion into `out` scaled by `scale`:
/// `out[i] = scale * values[i]^{-1}`.
///
/// # Panics
/// Panics if any input is zero or if `values.len() != out.len()`.
pub(super) fn batch_inverse_serial_scaled(
  values: &[Scalar],
  scale: Scalar,
  out: &mut [Scalar],
) {
  assert_eq!(values.len(), out.len());
  if values.is_empty() {
    return;
  }
  let mut acc = Scalar::ONE;
  for (slot, &v) in out.iter_mut().zip(values) {
    *slot = acc;
    acc *= v;
  }
  assert!(acc != Scalar::ZERO, "batch_inverse: zero input");
  let mut inv = acc.inverse() * scale;
  for i in (0..values.len()).rev() {
    out[i] *= inv;
    inv *= values[i];
  }
}

/// Serial Montgomery batch inversion into `out`: `out[i] = values[i]^{-1}`.
pub(super) fn batch_inverse_serial(values: &[Scalar], out: &mut [Scalar]) {
  assert_eq!(values.len(), out.len());
  if values.is_empty() {
    return;
  }
  let mut acc = Scalar::ONE;
  for (slot, &v) in out.iter_mut().zip(values) {
    *slot = acc;
    acc *= v;
  }
  assert!(acc != Scalar::ZERO, "batch_inverse: zero input");
  let mut inv = acc.inverse();
  for i in (0..values.len()).rev() {
    out[i] *= inv;
    inv *= values[i];
  }
}

/// Lagrange selectors precomputed once per trace-sized quotient coset and
/// reused across every fixed-column constraint pass.
///
/// Because `domain.generator() == trace_domain.generator() == g` with `g^n = 1`
/// and `last = g^{-1}`, we have:
///   `x_r - g^{-1} = g^{-1} · (x_{(r+1) mod n} - 1)`
/// so `is_last_row(r) = g · is_first_row((r + 1) mod n)`, halving both batch
/// inversions and selector memory.
pub(super) struct CosetSelectors {
  g: Scalar,
  last: Scalar,
  inv_vanishing: Scalar,
  first_sel: Vec<Scalar>,
}

impl CosetSelectors {
  pub(super) fn new(trace_domain: Radix2Coset, domain: Radix2Coset) -> Self {
    let n = trace_domain.size();
    assert_eq!(trace_domain.shift, Scalar::ONE);
    assert_eq!(domain.size(), n);
    let g = domain.generator();
    debug_assert_eq!(g, trace_domain.generator());
    let last = g.inverse();
    let vanishing =
      domain.shift.exp_power_of_2(trace_domain.log_size) - Scalar::ONE;
    let inv_vanishing = vanishing.inverse();

    let mut first_sel = super::pcs::generate_buffer(n, |_| Scalar::ZERO);
    let chunk_rows =
      n.div_ceil(current_num_threads().max(1) * 4).max(INV_SUB_BLOCK);
    first_sel.par_chunks_mut(chunk_rows).enumerate().for_each_init(
      || Vec::with_capacity(INV_SUB_BLOCK),
      |denoms, (chunk_idx, out)| {
        let chunk_start = chunk_idx * chunk_rows;
        let mut x =
          domain.shift * g.exp_u64(u64::try_from(chunk_start).unwrap());
        for sub_out in out.chunks_mut(INV_SUB_BLOCK) {
          denoms.clear();
          for _ in 0..sub_out.len() {
            denoms.push(x - Scalar::ONE);
            x *= g;
          }
          batch_inverse_serial_scaled(denoms, vanishing, sub_out);
        }
      },
    );

    Self { g, last, inv_vanishing, first_sel }
  }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn evaluate_coset(
  input: &QuotientCommitInput<'_, KzgConfig>,
  pass: &super::quotient_plan::Pass,
  domain: Radix2Coset,
  selectors: &CosetSelectors,
  powers: &[Scalar],
  fixed: Option<&RowMajorMatrix<Scalar>>,
  main: &RowMajorMatrix<Scalar>,
  stage2: &RowMajorMatrix<Scalar>,
  coset: usize,
  ratio: usize,
  block_size: Option<usize>,
  output: &mut [Scalar],
) {
  if let Some(b) = block_size {
    assert!(b > 0);
  }
  let n = input.trace_domain.size();
  assert_eq!(input.trace_domain.shift, Scalar::ONE);
  assert_eq!(domain.size(), n);
  assert_eq!(selectors.first_sel.len(), n);
  assert_eq!(output.len(), n * ratio);
  assert!(coset < ratio);

  let g = selectors.g;
  let last = selectors.last;
  let inv_vanishing = selectors.inv_vanishing;
  let delta = (input.lookup_publics[3] - input.lookup_publics[2])
    * (Scalar::from_usize(n) * input.trace_domain.generator()).inverse();
  let circuit = input.circuit;
  let ext = multi_stark::system::extension_params::<KzgConfig>();
  let chunk_rows = block_size.unwrap_or_else(|| {
    n.div_ceil(current_num_threads().max(1) * 4).max(INV_SUB_BLOCK)
  });
  output.par_chunks_mut(chunk_rows * ratio).enumerate().for_each_init(
    || {
      (
        Vec::with_capacity(pass.graph.nodes.len()),
        Vec::with_capacity(input.constraint_count),
      )
    },
    |(graph, constraints), (block, out)| {
      let start = block * chunk_rows;
      let rows = out.len() / ratio;
      let mut x = domain.shift * g.exp_u64(u64::try_from(start).unwrap());
      let main_w = main.width;
      let stage2_w = stage2.width;
      for local in 0..rows {
        let row = start + local;
        let next = if row + 1 == n { 0 } else { row + 1 };
        let main_at = row * main_w;
        let main_next = next * main_w;
        let stage2_at = row * stage2_w;
        let stage2_next = next * stage2_w;
        let preprocessed = fixed.map_or([&[][..], &[][..]], |m| {
          [
            &m.values[row * m.width..(row + 1) * m.width],
            &m.values[next * m.width..(next + 1) * m.width],
          ]
        });
        let is_first_row = selectors.first_sel[row];
        let is_last_row = g * selectors.first_sel[next];
        let is_transition = x - last;
        x *= g;
        let view = VarValues {
          preprocessed,
          main: [
            &main.values[main_at..main_at + main_w],
            &main.values[main_next..main_next + main_w],
          ],
          stage2: [
            &stage2.values[stage2_at..stage2_at + stage2_w],
            &stage2.values[stage2_next..stage2_next + stage2_w],
          ],
          publics: &input.lookup_publics,
          is_first_row,
          is_last_row,
          is_transition,
        };
        pass.graph.sweep(&view, graph);
        let mut value = pass
          .graph
          .zeros
          .iter()
          .zip(&pass.weights)
          .fold(Scalar::ZERO, |acc, (id, &weight)| {
            acc + graph[id.index()] * powers[weight]
          });
        for (group, lookups) in &pass.groups {
          let is_last_group = *group + 1 == stage2_w;
          let target = if is_last_group {
            view.stage2[1][0]
          } else {
            view.stage2[0][group + 1]
          };
          constraints.clear();
          multi_stark::lookup::logup_constraint_values(
            lookups,
            graph,
            &[view.stage2[0][*group]],
            &[target],
            &input.lookup_publics,
            &[if is_last_group { delta } else { Scalar::ZERO }],
            is_last_row,
            ext.w,
            ext.degree,
            circuit.lookup_group_size.max(1),
            constraints,
          );
          debug_assert_eq!(constraints.len(), 1);
          value += constraints[0] * powers[circuit.graph.zeros.len() + group];
        }
        out[local * ratio + coset] += value * inv_vanishing;
      }
    },
  );
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn coset_selectors_match_pointwise_formulas() {
    for log_size in [0usize, 1, 4, 13] {
      let trace = Radix2Coset { log_size, shift: Scalar::ONE };
      let big = trace.create_disjoint_domain(1 << (log_size + 1));
      let generator = big.generator();
      for coset in 0..2 {
        let domain = Radix2Coset {
          log_size,
          shift: big.shift * generator.exp_u64(u64::try_from(coset).unwrap()),
        };
        let sel = CosetSelectors::new(trace, domain);
        let n = trace.size();
        let mut x = domain.shift;
        for row in 0..n {
          let expected = trace.selectors_at_point(x);
          let next = if row + 1 == n { 0 } else { row + 1 };
          assert_eq!(sel.first_sel[row], expected.is_first_row);
          assert_eq!(sel.g * sel.first_sel[next], expected.is_last_row);
          assert_eq!(x - sel.last, expected.is_transition);
          assert_eq!(sel.inv_vanishing, expected.inv_vanishing);
          x *= sel.g;
        }
      }
    }
  }
}
