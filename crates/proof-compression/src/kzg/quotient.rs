//! Scalar quotient evaluation with bounded selectors and reusable row scratch.
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
use multi_stark::traits::batch_inverse;

#[allow(clippy::too_many_arguments)]
pub(super) fn evaluate_coset(
  input: &QuotientCommitInput<'_, KzgConfig>,
  pass: &super::quotient_plan::Pass,
  domain: Radix2Coset,
  fixed: Option<&RowMajorMatrix<Scalar>>,
  main: &RowMajorMatrix<Scalar>,
  stage2: &RowMajorMatrix<Scalar>,
  alpha: Scalar,
  coset: usize,
  ratio: usize,
  output: &mut [Scalar],
) {
  let n = input.trace_domain.size();
  assert_eq!(input.trace_domain.shift, Scalar::ONE);
  assert_eq!(domain.size(), n);
  assert_eq!(output.len(), n * ratio);
  assert!(coset < ratio);
  let g = domain.generator();
  let last = input.trace_domain.generator().inverse();
  let vanishing =
    domain.shift.exp_power_of_2(input.trace_domain.log_size) - Scalar::ONE;
  let inv_vanishing = vanishing.inverse();
  let delta = (input.lookup_publics[3] - input.lookup_publics[2])
    * (Scalar::from_usize(n) * input.trace_domain.generator()).inverse();
  let mut powers: Vec<_> =
    alpha.powers().take(input.constraint_count).collect();
  powers.reverse();
  let circuit = input.circuit;
  let ext = multi_stark::system::extension_params::<KzgConfig>();
  const BLOCK: usize = 1 << 12;
  output.par_chunks_mut(BLOCK * ratio).enumerate().for_each(|(block, out)| {
    let start = block * BLOCK;
    let rows = out.len() / ratio;
    let x0 = domain.shift * g.exp_u64(start as u64);
    let first_denoms: Vec<_> =
      g.powers().take(rows).map(|p| x0 * p - Scalar::ONE).collect();
    let first_inv = batch_inverse(&first_denoms);
    drop(first_denoms);
    let transition: Vec<_> =
      g.powers().take(rows).map(|p| x0 * p - last).collect();
    let last_inv = batch_inverse(&transition);
    let mut graph = Vec::with_capacity(pass.graph.nodes.len());
    let mut constraints = Vec::with_capacity(input.constraint_count);
    for local in 0..rows {
      let row = start + local;
      let next = (row + 1) % n;
      let row_values = |matrix: &RowMajorMatrix<Scalar>, r| r * matrix.width;
      let main_at = row_values(main, row);
      let main_next = row_values(main, next);
      let stage2_at = row_values(stage2, row);
      let stage2_next = row_values(stage2, next);
      let preprocessed = fixed.map_or([&[][..], &[][..]], |m| {
        [
          &m.values[row * m.width..(row + 1) * m.width],
          &m.values[next * m.width..(next + 1) * m.width],
        ]
      });
      let is_last_row = vanishing * last_inv[local];
      let view = VarValues {
        preprocessed,
        main: [
          &main.values[main_at..main_at + main.width],
          &main.values[main_next..main_next + main.width],
        ],
        stage2: [
          &stage2.values[stage2_at..stage2_at + stage2.width],
          &stage2.values[stage2_next..stage2_next + stage2.width],
        ],
        publics: &input.lookup_publics,
        is_first_row: vanishing * first_inv[local],
        is_last_row,
        is_transition: transition[local],
      };
      pass.graph.sweep(&view, &mut graph);
      constraints.clear();
      let mut value = pass
        .graph
        .zeros
        .iter()
        .zip(&pass.weights)
        .fold(Scalar::ZERO, |acc, (id, &weight)| {
          acc + graph[id.index()] * powers[weight]
        });
      for (group, lookups) in &pass.groups {
        let last = *group + 1 == stage2.width;
        let target =
          if last { view.stage2[1][0] } else { view.stage2[0][group + 1] };
        constraints.clear();
        multi_stark::lookup::logup_constraint_values(
          lookups,
          &graph,
          &[view.stage2[0][*group]],
          &[target],
          &input.lookup_publics,
          &[if last { delta } else { Scalar::ZERO }],
          is_last_row,
          ext.w,
          ext.degree,
          circuit.lookup_group_size.max(1),
          &mut constraints,
        );
        debug_assert_eq!(constraints.len(), 1);
        value += constraints[0] * powers[circuit.graph.zeros.len() + group];
      }
      out[local * ratio + coset] += value * inv_vanishing;
    }
  });
}
