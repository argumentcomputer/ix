//! Constraint-specific device working sets for traces that exceed dense
//! admission.

use super::quotient::{
  Column, Instruction, Lookup, PolynomialView, Program, allocation,
};
use super::*;
use crate::kzg::{Scalar, config::KzgConfig};
use multi_stark::config::{LookupCommitInput, QuotientCommitInput};
use multi_stark::traits::EvaluationDomain;

#[repr(C, align(32))]
struct NativePass {
  weight: [u64; 4],
  columns: *const Column,
  column_count: usize,
  evaluated: usize,
  nodes: *const Instruction,
  node_count: usize,
  roots: *const u32,
  root_count: usize,
  lookups: *const Lookup,
  lookup_count: usize,
  args: *const u32,
  arg_count: usize,
  slots: usize,
  group: usize,
}

struct Pass {
  program: Program,
  columns: Vec<Column>,
  evaluated: usize,
  group: usize,
  weight: Fr,
}

impl Pass {
  fn new(
    program: Program,
    all: &[PolynomialView<'_>],
    extra: &[usize],
    group: usize,
    weight: Fr,
  ) -> Option<Self> {
    let (columns, evaluated) = quotient::pass_columns(all, &program, extra)?;
    Some(Self { program, columns, evaluated, group, weight })
  }

  fn native(&self) -> NativePass {
    NativePass {
      weight: self.weight.0.0,
      columns: self.columns.as_ptr(),
      column_count: self.columns.len(),
      evaluated: self.evaluated,
      nodes: self.program.nodes.as_ptr(),
      node_count: self.program.nodes.len(),
      roots: self.program.roots.as_ptr(),
      root_count: self.program.roots.len(),
      lookups: self.program.lookups.as_ptr(),
      lookup_count: self.program.lookups.len(),
      args: self.program.args.as_ptr(),
      arg_count: self.program.args.len(),
      slots: self.program.slots.max(1),
      group: self.group,
    }
  }
}

unsafe extern "C" {
  fn ix_kzg_lookup_passes(
    device: i32,
    parameters: *const lookup::Parameters,
    passes: *const NativePass,
    pass_count: usize,
    outputs: *const *mut [u64; 4],
    total: *mut [u64; 4],
  ) -> i32;
  fn ix_kzg_quotient_passes(
    device: i32,
    parameters: *const quotient::Parameters,
    passes: *const NativePass,
    pass_count: usize,
    publics: *const [u64; 4],
    public_count: usize,
    shifts: *const [u64; 4],
    inverse_vanishing: *const [u64; 4],
    outputs: *const *mut [u64; 4],
  ) -> i32;
}

pub(super) fn enabled(dense_rejected: bool) -> bool {
  match settings().passes {
    PassMode::Off => false,
    PassMode::Fallback => dense_rejected,
    PassMode::Force => true,
  }
}

fn memory_bound(
  passes: &[Pass],
  rows: usize,
  blocks: usize,
  extra_columns: usize,
  publics: usize,
) -> Option<usize> {
  let max = |f: fn(&Pass) -> usize| passes.iter().map(f).max().unwrap_or(0);
  let evaluated = max(|p| p.evaluated);
  let slots = max(|p| p.program.slots.max(1));
  let elements = rows
    .checked_mul(evaluated.checked_add(extra_columns)?)?
    .checked_add(blocks.checked_mul(quotient::TILE)?.checked_mul(slots)?)?;
  [
    allocation::<Fr>(elements)?,
    allocation::<Column>(max(|p| p.columns.len()))?,
    allocation::<Instruction>(max(|p| p.program.nodes.len()))?,
    allocation::<u32>(max(|p| p.program.roots.len()))?,
    allocation::<Lookup>(max(|p| p.program.lookups.len()))?,
    allocation::<u32>(max(|p| p.program.args.len()))?,
    allocation::<Fr>(publics.checked_add(1)?)?,
    quotient::HEADROOM,
  ]
  .into_iter()
  .try_fold(0usize, usize::checked_add)
}

fn admit(bytes: usize) -> Option<Device<'static>> {
  let devices = Devices::get();
  if devices.ids.len() != 1 || bytes > devices.potential_budget(0) {
    tracing::info!(
      bytes,
      devices = devices.ids.len(),
      budget = devices.potential_budget(0),
      "KZG constraint passes not admitted"
    );
    return None;
  }
  let device = devices.acquire_at(0);
  device.prepare_budget(bytes).then_some(device)
}

pub(super) fn lookup_coefficients(
  input: &LookupCommitInput<'_, KzgConfig>,
  parameters: &lookup::Parameters,
  all: &[PolynomialView<'_>],
  widths: [usize; 3],
) -> Option<(Vec<Vec<Fr>>, Scalar)> {
  if Devices::get().ids.len() != 1 {
    return None;
  }
  let rows = 1usize.checked_shl(parameters.trace_log)?;
  let group_size = parameters.group_size as usize;
  let graph = &input.circuit.graph;
  let groups = graph.lookups.len().div_ceil(group_size);
  if groups == 0 {
    return None;
  }
  let passes: Vec<_> = (0..groups)
    .map(|group| {
      let start = group * group_size;
      let program = quotient::encode_pass(
        graph,
        widths,
        0,
        &[],
        start..(start + group_size).min(graph.lookups.len()),
      )?;
      Pass::new(program, all, &[], group, Fr::ONE)
    })
    .collect::<Option<_>>()?;
  let bytes = memory_bound(
    &passes,
    rows,
    parameters.blocks as usize,
    groups.checked_add(3)?,
    0,
  )?;
  let device = admit(bytes)?;
  let native: Vec<_> = passes.iter().map(Pass::native).collect();
  let mut outputs = vec![vec![Fr::ZERO; rows]; groups];
  let pointers: Vec<*mut [u64; 4]> =
    outputs.iter_mut().map(|v| v.as_mut_ptr().cast()).collect();
  let mut total = [0; 4];
  let started = std::time::Instant::now();
  // Every descriptor and output remains borrowed until the native stream
  // drains.
  check(
    unsafe {
      ix_kzg_lookup_passes(
        device.id(),
        parameters,
        native.as_ptr(),
        native.len(),
        pointers.as_ptr(),
        &mut total,
      )
    },
    "lookup constraint passes",
  );
  tracing::info!(
    device = device.id(),
    rows,
    groups,
    passes = passes.len(),
    evaluated = passes.iter().map(|p| p.evaluated).max().unwrap_or(0),
    bytes,
    seconds = started.elapsed().as_secs_f64(),
    "KZG lookup constructed in GPU passes"
  );
  Some((outputs, Scalar(Fr::new_unchecked(BigInt(total)))))
}

pub(super) fn quotient_coefficients(
  input: &QuotientCommitInput<'_, KzgConfig>,
  parameters: &quotient::Parameters,
  all: &[PolynomialView<'_>],
  widths: [usize; 3],
  shifts: &[Fr],
  inverse_vanishing: &[Fr],
) -> Option<Vec<Vec<Fr>>> {
  if Devices::get().ids.len() != 1 {
    return None;
  }
  if !(10..=27).contains(&input.trace_domain.log_size) {
    return None;
  }
  let rows = input.trace_domain.size();
  let ratio = input.quotient_domain.size() / rows;
  let graph = &input.circuit.graph;
  let groups = widths[2];
  let stage2 = widths[0].checked_add(widths[1])?;
  let count = graph.zeros.len().checked_add(groups)?;
  let mut weight = Fr::ONE;
  let mut weights: Vec<_> = (0..count)
    .map(|_| {
      let value = weight;
      weight *= Fr::new_unchecked(BigInt(parameters.alpha));
      value
    })
    .collect();
  weights.reverse();
  let mut passes = Vec::with_capacity(count);
  for (i, root) in graph.zeros.iter().enumerate() {
    let program = quotient::encode_pass(
      graph,
      widths,
      input.lookup_publics.len(),
      core::slice::from_ref(root),
      0..0,
    )?;
    passes.push(Pass::new(program, all, &[], usize::MAX, weights[i])?);
  }
  for group in 0..groups {
    let start = group * parameters.group_size as usize;
    let end = (start + parameters.group_size as usize).min(graph.lookups.len());
    let program = quotient::encode_pass(
      graph,
      widths,
      input.lookup_publics.len(),
      &[],
      start..end,
    )?;
    let next = if group + 1 == groups { 0 } else { group + 1 };
    passes.push(Pass::new(
      program,
      all,
      &[stage2 + group, stage2 + next],
      group,
      weights[graph.zeros.len() + group],
    )?);
  }
  let bytes = memory_bound(
    &passes,
    rows,
    parameters.blocks as usize,
    ratio.checked_add(1)?,
    input.lookup_publics.len(),
  )?;
  let device = admit(bytes)?;
  let native: Vec<_> = passes.iter().map(Pass::native).collect();
  let mut outputs = vec![vec![Fr::ZERO; rows]; ratio];
  let pointers: Vec<*mut [u64; 4]> =
    outputs.iter_mut().map(|v| v.as_mut_ptr().cast()).collect();
  let started = std::time::Instant::now();
  // Native failures are errors; only preflight admission can select the host
  // fallback.
  check(
    unsafe {
      ix_kzg_quotient_passes(
        device.id(),
        parameters,
        native.as_ptr(),
        native.len(),
        input.lookup_publics.as_ptr().cast(),
        input.lookup_publics.len(),
        shifts.as_ptr().cast(),
        inverse_vanishing.as_ptr().cast(),
        pointers.as_ptr(),
      )
    },
    "quotient constraint passes",
  );
  tracing::info!(
    device = device.id(),
    rows,
    ratio,
    passes = passes.len(),
    evaluated = passes.iter().map(|p| p.evaluated).max().unwrap_or(0),
    bytes,
    seconds = started.elapsed().as_secs_f64(),
    "KZG quotient evaluated in GPU passes"
  );
  Some(outputs)
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::traits::Algebra;

  #[test]
  fn pass_abi_and_memory_arithmetic() {
    assert_eq!(size_of::<NativePass>(), 160);
    assert_eq!(std::mem::offset_of!(NativePass, group), 128);
    assert!(memory_bound(&[], usize::MAX, 256, 4, 0).is_none());
  }

  #[test]
  fn pruned_pass_contains_only_transitive_dependencies() {
    use multi_stark::expr::{ColRef, RowOffset, Source};
    use multi_stark::graph::{ConstraintGraph, Node, NodeId};
    let graph = ConstraintGraph {
      nodes: vec![
        Node::Var(ColRef {
          source: Source::Preprocessed,
          offset: RowOffset::Current,
          index: 0,
        }),
        Node::Var(ColRef {
          source: Source::Preprocessed,
          offset: RowOffset::Next,
          index: 1,
        }),
        Node::Var(ColRef {
          source: Source::Main,
          offset: RowOffset::Current,
          index: 0,
        }),
        Node::Mul(NodeId(0), NodeId(2)),
        Node::Add(NodeId(3), NodeId(1)),
        Node::Const(Scalar::ONE),
      ],
      degrees: vec![1; 6],
      zeros: vec![NodeId(3), NodeId(4)],
      lookups: vec![multi_stark::lookup::Lookup {
        multiplicity: NodeId(5),
        args: vec![NodeId(1)],
      }],
      lookup_prefix_len: 6,
      max_constraint_degree: 2,
    };
    let values = [Fr::ONE];
    let all: Vec<PolynomialView<'_>> =
      (0..4).map(|_| (&values[..], None, false)).collect();
    let root =
      quotient::encode_pass(&graph, [2, 1, 1], 0, &[NodeId(3)], 0..0).unwrap();
    let root = Pass::new(root, &all, &[], usize::MAX, Fr::ONE).unwrap();
    assert_eq!(root.program.nodes.len(), 3);
    assert_eq!(root.evaluated, 2);
    let lookup =
      quotient::encode_pass(&graph, [2, 1, 1], 0, &[], 0..1).unwrap();
    let lookup = Pass::new(lookup, &all, &[3], 0, Fr::ONE).unwrap();
    assert_eq!(lookup.program.nodes.len(), 2);
    assert_eq!(lookup.evaluated, 2);
    assert!(
      quotient::encode_pass(&graph, [2, 1, 1], 0, &[NodeId(9)], 0..0).is_none()
    );
    assert!(quotient::encode_pass(&graph, [2, 1, 1], 0, &[], 0..2).is_none());
    assert!(memory_bound(&[root], 1 << 27, 256, 3, 4).unwrap() < 22usize << 30);
  }
}
