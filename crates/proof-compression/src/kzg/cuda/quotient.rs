//! Quotient construction on trace-sized device cosets, with coefficient-only
//! output.

use super::*;
use crate::kzg::{config::KzgConfig, field::Scalar, pcs::CommittedMatrix};
use multi_stark::config::QuotientCommitInput;
use multi_stark::expr::{RowOffset, Source};
use multi_stark::graph::{ConstraintGraph, Node, NodeId};
use multi_stark::traits::Algebra;

pub(super) const TILE: usize = 128;
pub(super) const MAX_BLOCKS: usize = 256;
pub(super) const HEADROOM: usize = 1 << 30;

#[derive(Clone, Copy, Default)]
#[repr(C, align(32))]
pub(super) struct Instruction {
  value: [u64; 4],
  a: u32,
  b: u32,
  op: u32,
  out: u32,
}

#[repr(C)]
pub(super) struct Lookup {
  multiplicity: u32,
  arg_start: u32,
  arg_count: u32,
}

#[repr(C, align(32))]
pub(super) struct Column {
  input: *const [u64; 4],
  pub(super) resident: *const c_void,
  count: usize,
  padding: u64,
  constant: [u64; 4],
  slot: u32,
  reserved: u32,
}

#[repr(C, align(32))]
pub(super) struct Parameters {
  pub(super) alpha: [u64; 4],
  pub(super) generator: [u64; 4],
  pub(super) generator_inverse: [u64; 4],
  pub(super) delta: [u64; 4],
  pub(super) quotient_shift_inverse: [u64; 4],
  pub(super) trace_log: u32,
  pub(super) quotient_log: u32,
  pub(super) slots: u32,
  pub(super) stage2_start: u32,
  pub(super) group_size: u32,
  pub(super) blocks: u32,
}

unsafe extern "C" {
  fn ix_kzg_quotient(
    device: i32,
    parameters: *const Parameters,
    columns: *const Column,
    column_count: usize,
    evaluation_columns: usize,
    nodes: *const Instruction,
    node_count: usize,
    roots: *const u32,
    root_count: usize,
    lookups: *const Lookup,
    lookup_count: usize,
    args: *const u32,
    arg_count: usize,
    publics: *const [u64; 4],
    public_count: usize,
    coset_shifts: *const [u64; 4],
    inverse_vanishing: *const [u64; 4],
    outputs: *const *mut [u64; 4],
  ) -> i32;
}

pub(super) struct Program {
  pub(super) nodes: Vec<Instruction>,
  pub(super) roots: Vec<u32>,
  pub(super) lookups: Vec<Lookup>,
  pub(super) args: Vec<u32>,
  pub(super) slots: usize,
}

fn encode(
  graph: &ConstraintGraph<Scalar>,
  widths: [usize; 3],
  publics: usize,
) -> Option<Program> {
  encode_range(graph, widths, publics, graph.nodes.len(), &graph.zeros, None)
}

pub(super) fn encode_lookup(
  graph: &ConstraintGraph<Scalar>,
  widths: [usize; 3],
) -> Option<Program> {
  encode_range(graph, widths, 0, graph.lookup_prefix_len, &[], None)
}

fn encode_range(
  graph: &ConstraintGraph<Scalar>,
  widths: [usize; 3],
  publics: usize,
  n: usize,
  roots: &[NodeId],
  selection: Option<&core::ops::Range<usize>>,
) -> Option<Program> {
  let selected =
    graph.lookups.get(selection.cloned().unwrap_or(0..graph.lookups.len()))?;
  let mut live = vec![selection.is_none(); n];
  if selection.is_some() {
    let mut pending: Vec<_> = roots
      .iter()
      .chain(
        selected
          .iter()
          .flat_map(|l| core::iter::once(&l.multiplicity).chain(l.args.iter())),
      )
      .copied()
      .collect();
    while let Some(id) = pending.pop() {
      let used = live.get_mut(id.index())?;
      if *used {
        continue;
      }
      *used = true;
      match *graph.nodes.get(id.index())? {
        Node::Add(a, b) | Node::Sub(a, b) | Node::Mul(a, b) => {
          if a.index() >= id.index() || b.index() >= id.index() {
            return None;
          }
          pending.extend([a, b]);
        },
        Node::Neg(a) => {
          if a.index() >= id.index() {
            return None;
          }
          pending.push(a);
        },
        _ => {},
      }
    }
  }
  let node_range = graph.nodes.get(..n)?;
  let mut last: Vec<_> = (0..n).collect();
  for (i, node) in node_range.iter().enumerate() {
    if !live[i] {
      continue;
    }
    let mut consume = |id: NodeId| {
      if id.index() >= i {
        return None;
      }
      last[id.index()] = i;
      Some(())
    };
    match *node {
      Node::Add(a, b) | Node::Sub(a, b) | Node::Mul(a, b) => {
        consume(a)?;
        consume(b)?;
      },
      Node::Neg(a) => consume(a)?,
      _ => {},
    }
  }
  for id in roots.iter().chain(selected.iter().flat_map(|lookup| {
    core::iter::once(&lookup.multiplicity).chain(lookup.args.iter())
  })) {
    *last.get_mut(id.index())? = n;
  }
  let mut mapping = vec![0u32; n];
  let mut free = Vec::new();
  let mut retire = vec![Vec::new(); n + 1];
  let mut slots = 0u32;
  let mut nodes = Vec::with_capacity(n);
  for (i, node) in node_range.iter().enumerate() {
    free.append(&mut retire[i]);
    if !live[i] {
      continue;
    }
    let out = free.pop().unwrap_or_else(|| {
      let slot = slots;
      slots += 1;
      slot
    });
    mapping[i] = out;
    if last[i] < n {
      retire[last[i] + 1].push(out);
    }
    let mut encoded = Instruction { out, ..Default::default() };
    match *node {
      Node::Const(value) => encoded.value = value.0.0.0,
      Node::Var(column) => {
        let source = match column.source {
          Source::Preprocessed => 0,
          Source::Main => 1,
          Source::Stage2 => 2,
        };
        if column.index as usize >= widths[source] {
          return None;
        }
        encoded.op = 1;
        encoded.a = u32::try_from(widths[..source].iter().sum::<usize>())
          .ok()?
          .checked_add(column.index)?;
        encoded.b = u32::from(column.offset == RowOffset::Next);
      },
      Node::Public(index) => {
        if index as usize >= publics {
          return None;
        }
        encoded.op = 2;
        encoded.a = index;
      },
      Node::IsFirstRow => encoded.op = 3,
      Node::IsLastRow => encoded.op = 4,
      Node::IsTransition => encoded.op = 5,
      Node::Add(a, b) | Node::Sub(a, b) | Node::Mul(a, b) => {
        encoded.op = match node {
          Node::Add(..) => 6,
          Node::Sub(..) => 7,
          _ => 8,
        };
        encoded.a = mapping[a.index()];
        encoded.b = mapping[b.index()];
      },
      Node::Neg(a) => {
        encoded.op = 9;
        encoded.a = mapping[a.index()];
      },
    }
    nodes.push(encoded);
  }
  let roots = roots.iter().map(|id| mapping[id.index()]).collect();
  let mut lookups = Vec::with_capacity(selected.len());
  let mut args = Vec::new();
  for lookup in selected {
    lookups.push(Lookup {
      multiplicity: mapping[lookup.multiplicity.index()],
      arg_start: u32::try_from(args.len()).ok()?,
      arg_count: u32::try_from(lookup.args.len()).ok()?,
    });
    args.extend(lookup.args.iter().map(|id| mapping[id.index()]));
  }
  Some(Program { nodes, roots, lookups, args, slots: slots as usize })
}

pub(super) fn encode_pass(
  graph: &ConstraintGraph<Scalar>,
  widths: [usize; 3],
  publics: usize,
  roots: &[NodeId],
  lookups: core::ops::Range<usize>,
) -> Option<Program> {
  encode_range(graph, widths, publics, graph.nodes.len(), roots, Some(&lookups))
}

pub(super) fn pass_columns(
  all: &[PolynomialView<'_>],
  program: &Program,
  extra: &[usize],
) -> Option<(Vec<Column>, usize)> {
  let mut used = vec![false; all.len()];
  for node in &program.nodes {
    if node.op == 1 {
      *used.get_mut(node.a as usize)? = true;
    }
  }
  for &column in extra {
    *used.get_mut(column)? = true;
  }
  let mut columns = column_descriptors(all);
  let mut count = 0;
  for ((descriptor, (_, _, constant)), needed) in
    columns.iter_mut().zip(all).zip(used)
  {
    descriptor.slot = if needed && !constant {
      let slot = u32::try_from(count).ok()?;
      count += 1;
      slot
    } else {
      u32::MAX
    };
  }
  Some((columns, count))
}

pub(super) fn matrix(
  data: (&crate::kzg::pcs::KzgProverData, usize),
) -> Option<&CommittedMatrix> {
  data.0.matrices.get(data.1)
}

pub(super) fn allocation<T>(count: usize) -> Option<usize> {
  count
    .checked_add(31)?
    .checked_div(32)?
    .checked_mul(32)?
    .checked_mul(size_of::<T>())
}

fn memory_bound(
  program: &Program,
  n: usize,
  ratio: usize,
  columns: usize,
  evaluated: usize,
  publics: usize,
) -> Option<usize> {
  let blocks = n.div_ceil(TILE).min(MAX_BLOCKS);
  let elements = evaluated
    .checked_mul(n)?
    .checked_add(n)?
    .checked_add(n.checked_mul(ratio)?)?
    .checked_add(
      blocks.checked_mul(TILE)?.checked_mul(program.slots.max(1))?,
    )?;
  // Base_dev_ptr is in-place. Both static twiddle tables fit in 21 MiB; the
  // remaining headroom covers allocator granularity and runtime state. The
  // memory query excludes live allocations and credits reusable pool pages.
  [
    allocation::<Fr>(elements)?,
    allocation::<Instruction>(program.nodes.len())?,
    allocation::<u32>(program.roots.len())?,
    allocation::<Lookup>(program.lookups.len())?,
    allocation::<u32>(program.args.len())?,
    allocation::<Column>(columns)?,
    allocation::<Fr>(publics)?,
    HEADROOM,
  ]
  .into_iter()
  .try_fold(0usize, usize::checked_add)
}

/// Every column of the input matrices as a host slice with its device
/// residency and constant flag. Disk-backed columns are not admitted.
pub(super) fn views<'a>(
  matrices: impl IntoIterator<Item = &'a CommittedMatrix>,
) -> Option<Vec<PolynomialView<'a>>> {
  let mut all = Vec::new();
  for matrix in matrices {
    all.extend(matrix.cuda_columns()?);
  }
  Some(all)
}

pub(in crate::kzg) fn coefficients(
  input: &QuotientCommitInput<'_, KzgConfig>,
  alpha: Scalar,
) -> Option<Vec<Vec<Fr>>> {
  let trace = input.trace_domain;
  let quotient = input.quotient_domain;
  if trace.log_size < 10
    || quotient.log_size > 28
    || trace.log_size > quotient.log_size
    || trace.shift != Scalar::ONE
    || quotient.shift == Scalar::ZERO
  {
    return None;
  }
  let n = 1usize.checked_shl(u32::try_from(trace.log_size).ok()?)?;
  let ratio = 1usize
    .checked_shl(u32::try_from(quotient.log_size - trace.log_size).ok()?)?;
  let circuit = input.circuit;
  let group_size = circuit.lookup_group_size.max(1);
  let groups = circuit.graph.lookups.len().div_ceil(group_size).max(1);
  if input.lookup_publics.len() < 4
    || group_size > multi_stark::lookup::MAX_LOOKUP_GROUP
    || groups != circuit.stage_2_width
    || input.constraint_count
      != circuit.graph.zeros.len().checked_add(groups)?
  {
    return None;
  }
  let fixed = match input.preprocessed {
    Some(data) => Some(matrix(data)?),
    None => None,
  };
  let main = matrix(input.stage_1)?;
  let stage2 = matrix(input.stage_2)?;
  let widths =
    [fixed.map_or(0, CommittedMatrix::width), main.width(), stage2.width()];
  if widths
    != [circuit.preprocessed_width, circuit.main_width, circuit.stage_2_width]
    || [fixed, Some(main), Some(stage2)]
      .into_iter()
      .flatten()
      .any(|m| m.domain() != trace)
  {
    return None;
  }
  let program = encode(&circuit.graph, widths, input.lookup_publics.len())?;
  let generator = trace.generator().0;
  let generator_inverse = generator.inverse()?;
  let mut shift = quotient.shift.0;
  let mut shifts = Vec::with_capacity(ratio);
  let mut inverse_vanishing = Vec::with_capacity(ratio);
  for _ in 0..ratio {
    shifts.push(shift);
    inverse_vanishing.push((shift.pow([n as u64]) - Fr::ONE).inverse()?);
    shift *= quotient.generator().0;
  }
  let all_columns =
    views([fixed, Some(main), Some(stage2)].into_iter().flatten())?;
  if all_columns
    .iter()
    .any(|(column, _, _)| column.is_empty() || column.len() > n)
  {
    return None;
  }
  let evaluated =
    all_columns.iter().filter(|(_, _, constant)| !constant).count();
  let bytes = memory_bound(
    &program,
    n,
    ratio,
    all_columns.len(),
    evaluated,
    input.lookup_publics.len(),
  )?;
  let parameters = Parameters {
    alpha: alpha.0.0.0,
    generator: generator.0.0,
    generator_inverse: generator_inverse.0.0,
    delta: ((input.lookup_publics[3].0 - input.lookup_publics[2].0)
      * (Fr::from(n as u64) * generator).inverse()?)
    .0
    .0,
    quotient_shift_inverse: quotient.shift.0.inverse()?.0.0,
    trace_log: u32::try_from(trace.log_size).ok()?,
    quotient_log: u32::try_from(quotient.log_size).ok()?,
    slots: u32::try_from(program.slots.max(1)).ok()?,
    stage2_start: u32::try_from(widths[0].checked_add(widths[1])?).ok()?,
    group_size: u32::try_from(group_size).ok()?,
    blocks: u32::try_from(n.div_ceil(TILE).min(MAX_BLOCKS)).ok()?,
  };
  let eligible = eligible_devices(&all_columns, bytes);
  if passes::enabled(eligible.is_empty())
    && let Some(output) = passes::quotient_coefficients(
      input,
      &parameters,
      &all_columns,
      widths,
      &shifts,
      &inverse_vanishing,
    )
  {
    return Some(output);
  }
  assert!(
    !eligible.is_empty(),
    "KZG quotient of {n} rows needs {bytes} bytes and no selected device admits it (budgets {:?}); lower IX_KZG_CUDA_RESIDENT_GIB or the chunk size",
    device_budgets()
  );
  let mut outputs: Vec<_> = (0..ratio).map(|_| vec![Fr::ZERO; n]).collect();
  let output_pointers: Vec<*mut [u64; 4]> =
    outputs.iter_mut().map(|values| values.as_mut_ptr().cast()).collect();
  let mut columns = column_descriptors(&all_columns);
  let device = acquire_columns(&eligible, &mut columns, &all_columns, bytes)
    .expect("KZG quotient admission failed after eviction");
  let started = std::time::Instant::now();
  // Every borrowed coefficient and output buffer outlives the synchronous call.
  check(
    unsafe {
      ix_kzg_quotient(
        device.id(),
        &parameters,
        columns.as_ptr(),
        columns.len(),
        evaluated,
        program.nodes.as_ptr(),
        program.nodes.len(),
        program.roots.as_ptr(),
        program.roots.len(),
        program.lookups.as_ptr(),
        program.lookups.len(),
        program.args.as_ptr(),
        program.args.len(),
        input.lookup_publics.as_ptr().cast(),
        input.lookup_publics.len(),
        shifts.as_ptr().cast(),
        inverse_vanishing.as_ptr().cast(),
        output_pointers.as_ptr(),
      )
    },
    "resident quotient",
  );
  tracing::info!(
    device = device.id(),
    rows = n,
    ratio,
    evaluated,
    bytes,
    seconds = started.elapsed().as_secs_f64(),
    "KZG quotient evaluated on device"
  );
  Some(outputs)
}

/// Current admission budget of every selected device, for diagnostics.
pub(super) fn device_budgets() -> Vec<usize> {
  let devices = Devices::get();
  (0..devices.ids.len()).map(|index| devices.potential_budget(index)).collect()
}

pub(super) type PolynomialView<'a> =
  (&'a [Fr], Option<&'a ResidentPolynomial>, bool);

pub(super) fn eligible_devices(
  all_columns: &[PolynomialView<'_>],
  bytes: usize,
) -> Vec<(usize, usize)> {
  let devices = Devices::get();
  let mut eligible = Vec::new();
  for index in 0..devices.ids.len() {
    if bytes <= devices.potential_budget(index) {
      let local = all_columns
        .iter()
        .filter(|(_, resident, _)| {
          resident.is_some_and(|r| r.reservation.index == index)
        })
        .count();
      eligible.push((index, local));
    }
  }
  eligible.sort_by_key(|(_, local)| std::cmp::Reverse(*local));
  eligible
}

pub(super) fn column_descriptors(
  all_columns: &[PolynomialView<'_>],
) -> Vec<Column> {
  let mut next_slot = 0;
  all_columns
    .iter()
    .map(|(column, _, constant)| {
      let slot = if *constant {
        u32::MAX
      } else {
        let slot = next_slot;
        next_slot += 1;
        slot
      };
      Column {
        input: column.as_ptr().cast(),
        resident: std::ptr::null(),
        count: column.len(),
        padding: 0,
        constant: column[0].0.0,
        slot,
        reserved: 0,
      }
    })
    .collect()
}

/// Lease the first free device among `eligible`, in its order of preference,
/// with `bytes` of budget prepared on it.
pub(super) fn acquire_device(
  eligible: &[(usize, usize)],
  bytes: usize,
) -> Option<Device<'static>> {
  Device::assert_unleased();
  if eligible.is_empty() {
    return None;
  }
  let devices = Devices::get();
  let device = {
    let mut busy = devices.busy.lock().unwrap();
    loop {
      if let Some(&(index, _)) =
        eligible.iter().find(|&&(index, _)| !busy[index])
      {
        busy[index] = true;
        break Device::new(devices, index);
      }
      busy = devices.available.wait(busy).unwrap();
    }
  };
  device.prepare_budget(bytes).then_some(device)
}

/// Point descriptors at the resident copies that live on `device`. The
/// kernels reject a resident pointer from another device and upload every
/// unbound column from its host slice instead.
pub(super) fn bind_resident(
  columns: &mut [Column],
  all_columns: &[PolynomialView<'_>],
  device: &Device<'_>,
) {
  for (column, (_, resident, _)) in columns.iter_mut().zip(all_columns) {
    column.resident = resident
      .filter(|r| r.reservation.index == device.index)
      .map_or(std::ptr::null(), |r| r.context as *const c_void);
  }
}

pub(super) fn acquire_columns(
  eligible: &[(usize, usize)],
  columns: &mut [Column],
  all_columns: &[PolynomialView<'_>],
  bytes: usize,
) -> Option<Device<'static>> {
  let device = acquire_device(eligible, bytes)?;
  bind_resident(columns, all_columns, &device);
  Some(device)
}
