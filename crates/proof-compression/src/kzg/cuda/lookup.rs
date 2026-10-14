//! Device lookup construction with grouped rational sums and stock prefix
//! scans.

use super::quotient::{self, Column, Instruction, Lookup, Program, allocation};
use super::*;
use crate::kzg::{config::KzgConfig, field::Scalar, pcs::CommittedMatrix};
use multi_stark::config::LookupCommitInput;
use multi_stark::traits::Algebra;

#[repr(C, align(32))]
pub(super) struct Parameters {
  pub(super) beta: [u64; 4],
  pub(super) gamma: [u64; 4],
  pub(super) trace_log: u32,
  pub(super) slots: u32,
  pub(super) group_size: u32,
  pub(super) blocks: u32,
}

unsafe extern "C" {
  fn ix_kzg_lookup(
    device: i32,
    parameters: *const Parameters,
    columns: *const Column,
    column_count: usize,
    evaluation_columns: usize,
    nodes: *const Instruction,
    node_count: usize,
    lookups: *const Lookup,
    lookup_count: usize,
    args: *const u32,
    arg_count: usize,
    outputs: *const *mut [u64; 4],
    total: *mut [u64; 4],
  ) -> i32;
}

fn memory_bound(
  program: &Program,
  n: usize,
  groups: usize,
  columns: usize,
  evaluated: usize,
) -> Option<usize> {
  let blocks = n.div_ceil(quotient::TILE).min(quotient::MAX_BLOCKS);
  let elements = n
    .checked_mul(evaluated)?
    .checked_add(n.checked_mul(groups)?.checked_mul(4)?)?
    .checked_add(
      blocks.checked_mul(quotient::TILE)?.checked_mul(program.slots.max(1))?,
    )?;
  [
    allocation::<Fr>(elements)?,
    allocation::<Instruction>(program.nodes.len())?,
    allocation::<Lookup>(program.lookups.len())?,
    allocation::<u32>(program.args.len())?,
    allocation::<Column>(columns)?,
    allocation::<Fr>(1)?,
    quotient::HEADROOM,
  ]
  .into_iter()
  .try_fold(0usize, usize::checked_add)
}

pub(in crate::kzg) fn coefficients(
  input: &LookupCommitInput<'_, KzgConfig>,
  beta: Scalar,
  gamma: Scalar,
) -> Option<(Vec<Vec<Fr>>, Scalar)> {
  let main = quotient::matrix(input.stage_1)?;
  let fixed = match input.preprocessed {
    Some(data) => Some(quotient::matrix(data)?),
    None => None,
  };
  let trace = main.domain();
  if trace.shift != Scalar::ONE || !(10..=27).contains(&trace.log_size) {
    return None;
  }
  let n = 1usize.checked_shl(u32::try_from(trace.log_size).ok()?)?;
  let circuit = input.circuit;
  let group_size = circuit.lookup_group_size.max(1);
  let groups = circuit.graph.lookups.len().div_ceil(group_size).max(1);
  let widths = [fixed.map_or(0, CommittedMatrix::width), main.width(), 0];
  if group_size > multi_stark::lookup::MAX_LOOKUP_GROUP
    || groups != circuit.stage_2_width
    || widths[..2] != [circuit.preprocessed_width, circuit.main_width]
    || fixed.is_some_and(|matrix| matrix.domain() != trace)
  {
    return None;
  }
  let program = quotient::encode_lookup(&circuit.graph, widths)?;
  if program.lookups.is_empty() {
    return Some((vec![vec![Fr::ZERO; n]], Scalar::ZERO));
  }
  let all_columns = quotient::views([fixed, Some(main)].into_iter().flatten())?;
  if all_columns
    .iter()
    .any(|(column, _, _)| column.is_empty() || column.len() > n)
  {
    return None;
  }
  let evaluated =
    all_columns.iter().filter(|(_, _, constant)| !constant).count();
  let bytes = memory_bound(&program, n, groups, all_columns.len(), evaluated)?;
  let eligible = quotient::eligible_devices(&all_columns, bytes);
  let parameters = Parameters {
    beta: beta.0.0.0,
    gamma: gamma.0.0.0,
    trace_log: u32::try_from(trace.log_size).ok()?,
    slots: u32::try_from(program.slots.max(1)).ok()?,
    group_size: u32::try_from(group_size).ok()?,
    blocks: u32::try_from(n.div_ceil(quotient::TILE).min(quotient::MAX_BLOCKS))
      .ok()?,
  };
  if passes::enabled(eligible.is_empty())
    && let Some(output) =
      passes::lookup_coefficients(input, &parameters, &all_columns, widths)
  {
    return Some(output);
  }
  assert!(
    !eligible.is_empty(),
    "KZG lookup of {n} rows needs {bytes} bytes and no selected device admits it (budgets {:?}); lower IX_KZG_CUDA_RESIDENT_GIB or the chunk size",
    quotient::device_budgets()
  );
  let mut outputs: Vec<_> = (0..groups).map(|_| vec![Fr::ZERO; n]).collect();
  let output_pointers: Vec<*mut [u64; 4]> =
    outputs.iter_mut().map(|values| values.as_mut_ptr().cast()).collect();
  let mut columns = quotient::column_descriptors(&all_columns);
  let mut total = [0; 4];
  let device =
    quotient::acquire_columns(&eligible, &mut columns, &all_columns, bytes)
      .expect("KZG lookup admission failed after eviction");
  let started = std::time::Instant::now();
  // The native job synchronizes every transfer before borrowed buffers expire.
  check(
    unsafe {
      ix_kzg_lookup(
        device.id(),
        &parameters,
        columns.as_ptr(),
        columns.len(),
        evaluated,
        program.nodes.as_ptr(),
        program.nodes.len(),
        program.lookups.as_ptr(),
        program.lookups.len(),
        program.args.as_ptr(),
        program.args.len(),
        output_pointers.as_ptr(),
        &mut total,
      )
    },
    "resident lookup",
  );
  tracing::info!(
    device = device.id(),
    rows = n,
    groups,
    evaluated,
    bytes,
    seconds = started.elapsed().as_secs_f64(),
    "KZG lookup constructed on device"
  );
  Some((outputs, Scalar(Fr::new_unchecked(BigInt(total)))))
}
