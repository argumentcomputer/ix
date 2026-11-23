//! Device lookup construction with grouped rational sums and stock prefix
//! scans.

use super::quotient::{self, Column, Instruction, Lookup, Program, allocation};
use super::*;
use crate::kzg::{
  field::CurveScalar,
  pcs::{CoefficientConfig, CommittedMatrix},
};
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

const _: () = {
  assert!(size_of::<Parameters>() == 96 && align_of::<Parameters>() == 32);
  assert!(std::mem::offset_of!(Parameters, gamma) == 32);
  assert!(std::mem::offset_of!(Parameters, trace_log) == 64);
  assert!(std::mem::offset_of!(Parameters, blocks) == 76);
};

fn memory_bound<C: KzgCurve>(
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
    allocation::<C::Fr>(elements)?,
    allocation::<Instruction>(program.nodes.len())?,
    allocation::<Lookup>(program.lookups.len())?,
    allocation::<u32>(program.args.len())?,
    allocation::<Column>(columns)?,
    allocation::<C::Fr>(1)?,
    quotient::HEADROOM,
  ]
  .into_iter()
  .try_fold(0usize, usize::checked_add)
}

pub(in crate::kzg) fn coefficients<
  C: KzgCurve,
  SC: CoefficientConfig<C>,
>(
  input: &LookupCommitInput<'_, SC>,
  beta: CurveScalar<C>,
  gamma: CurveScalar<C>,
) -> Option<(Vec<Vec<C::Fr>>, CurveScalar<C>)> {
  coefficients_with_mode::<C, SC>(input, beta, gamma, settings().passes)
}

pub(super) fn coefficients_with_mode<
  C: KzgCurve,
  SC: CoefficientConfig<C>,
>(
  input: &LookupCommitInput<'_, SC>,
  beta: CurveScalar<C>,
  gamma: CurveScalar<C>,
  mode: PassMode,
) -> Option<(Vec<Vec<C::Fr>>, CurveScalar<C>)> {
  let main = quotient::matrix(input.stage_1)?;
  let fixed = match input.preprocessed {
    Some(data) => Some(quotient::matrix(data)?),
    None => None,
  };
  let trace = main.domain();
  if trace.shift != CurveScalar::<C>::ONE
    || !(10..=27).contains(&trace.log_size)
  {
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
  let program = quotient::encode_lookup::<C>(&circuit.graph, widths)?;
  if program.lookups.is_empty() {
    return Some((vec![vec![C::FR_ZERO; n]], CurveScalar::<C>::ZERO));
  }
  let all_columns =
    quotient::views::<C>([fixed, Some(main)].into_iter().flatten())?;
  if all_columns
    .iter()
    .any(|(column, _, _)| column.is_empty() || column.len() > n)
  {
    return None;
  }
  let evaluated =
    all_columns.iter().filter(|(_, _, constant)| !constant).count();
  let bytes =
    memory_bound::<C>(&program, n, groups, all_columns.len(), evaluated)?;
  let parameters = Parameters {
    beta: C::fr_mont_limbs(beta.0),
    gamma: C::fr_mont_limbs(gamma.0),
    trace_log: u32::try_from(trace.log_size).ok()?,
    slots: u32::try_from(program.slots.max(1)).ok()?,
    group_size: u32::try_from(group_size).ok()?,
    blocks: u32::try_from(n.div_ceil(quotient::TILE).min(quotient::MAX_BLOCKS))
      .ok()?,
  };
  let run_passes = || {
    passes::lookup_coefficients::<C, SC>(input, &parameters, &all_columns, widths)
  };
  if mode == PassMode::Force {
    return Some(run_passes().expect(
      "forced KZG lookup passes are unsupported or no selected device admits them",
    ));
  }
  let mut columns = quotient::column_descriptors::<C>(&all_columns);
  let device =
    quotient::acquire_columns::<C>(&mut columns, &all_columns, bytes);
  if device.is_none()
    && mode == PassMode::Fallback
    && let Some(output) = run_passes()
  {
    return Some(output);
  }
  let device = device.unwrap_or_else(|| {
    panic!(
      "KZG lookup of {n} rows needs {bytes} bytes and no selected device admits it (budgets {:?}); lower IX_KZG_CUDA_RESIDENT_GIB or the chunk size",
      quotient::device_budgets::<C>()
    )
  });
  let mut outputs: Vec<_> = (0..groups).map(|_| vec![C::FR_ZERO; n]).collect();
  let output_pointers: Vec<*mut [u64; 4]> =
    outputs.iter_mut().map(|values| values.as_mut_ptr().cast()).collect();
  let mut total = [0; 4];
  let started = std::time::Instant::now();
  // The native job synchronizes every transfer before borrowed buffers expire.
  check(
    unsafe {
      C::ffi_lookup(
        device.id(),
        std::ptr::from_ref(&parameters).cast(),
        columns.as_ptr().cast(),
        columns.len(),
        evaluated,
        program.nodes.as_ptr().cast(),
        program.nodes.len(),
        program.lookups.as_ptr().cast(),
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
    curve = C::NAME,
    device = device.id(),
    rows = n,
    groups,
    evaluated,
    bytes,
    seconds = started.elapsed().as_secs_f64(),
    "KZG lookup constructed on device"
  );
  Some((outputs, CurveScalar(C::fr_from_mont_limbs_unchecked(total))))
}
