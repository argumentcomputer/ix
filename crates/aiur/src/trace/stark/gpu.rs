//! Stage-one population on the GPU (`AIUR_GPU_TRACE=generated`).
//!
//! Function circuits whose population plans need no host-only state are
//! filled on the device by `cuda/population.cu`, which interprets the same
//! compiled plans as the host writer ([`crate::trace::plan`]) and applies the
//! same placement. They reach multi-stark as generated traces: the host
//! neither builds nor uploads their rows, and graph lookups regenerate tiles
//! on the device. The record tables those rows read are uploaded once per
//! proof, so the execution record can be dropped before proving. Other
//! circuits (memory, fixed tables, plans with stores, loads or stream hints)
//! keep host rows. Proof bytes are identical to host population.
//!
//! Depth circuits (the depth pass, [`crate::trace::depth`]) are filled on the
//! device too: each plan carries a depth section, and the record upload holds
//! the recorded query heights. Their gap limbs' range-table uses are counted
//! once at upload, by a pass over every real row, because the fixed range
//! tables are committed before any tile is generated and tiles can be
//! generated more than once.
//!
//! `AIUR_GPU_TRACE_CIRCUITS=a,b` restricts device population to the listed
//! circuits, named by circuit or by member function; the record upload then
//! holds only what those circuits read.
//!
//! Multi-stark asks a generated source to release its device state only
//! under device memory pressure, when admitting a commitment, lookup or
//! quotient phase that is short of memory. The uploaded record is then
//! copied to host memory once, freed, and uploaded again from that copy on
//! the next tile. Because admission can reclaim it, device planning does not
//! reserve the record beside the proving peak. `AIUR_GPU_TRACE_RELEASE=0`
//! pins the record instead, saving the host copy; device planning then
//! charges it.
use super::{planning::HostCause, *};
use crate::{
  Execution,
  trace::{
    Action,
    depth::{DepthPlan, Kind as DepthKind},
    plan::device::{Constants, Encoded, Target},
  },
};
use multi_stark::{cuda::DeviceTraceView, witness::TraceGenerator};
use std::{
  ffi::c_void,
  sync::{Arc, Mutex, RwLock, RwLockReadGuard},
};

const POLY_CONST: u32 = 0;
const POLY_VAR: u32 = 1;
const POLY_ADD: u32 = 2;
const POLY_SUB: u32 = 3;
const POLY_MUL: u32 = 4;

/// The depth column word of a circuit without one.
const NO_COLUMN: u32 = u32::MAX;
/// Depth slot kinds in a plan's depth section.
const DEPTH_EXACT: u32 = 0;
const DEPTH_GAP: u32 = 1;
const DEPTH_EXTERNAL: u32 = 2;

#[repr(C)]
#[derive(Clone, Copy)]
struct AiurFunction {
  code: *const u32,
  constants: *const u64,
  rows: *const u64,
  multiplicities: *const u64,
  /// Each query's recorded height, or null when the table tracks none.
  depths: *const u64,
  count: u64,
  first: u64,
  code_len: u32,
  scratch: u32,
  inputs: u32,
  outputs: u32,
  stride: u32,
  pad: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct AiurCallee {
  rows: *const u64,
  index: *const u32,
  multiplicities: *const u64,
  /// Each query's recorded height, or null when the table tracks none.
  depths: *const u64,
  count: u64,
  mask: u32,
  inputs: u32,
  outputs: u32,
  stride: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct AiurCircuit {
  members: *const AiurFunction,
  callees: *const AiurCallee,
  real: u64,
  member_count: u32,
  width: u32,
  scratch: u32,
  pad: u32,
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct AiurPopulationError {
  code: i32,
  op: u32,
  row: u64,
}

unsafe extern "C" {
  fn aiur_gpu_memory_info(
    device: i32,
    free_bytes: *mut usize,
    total_bytes: *mut usize,
  ) -> i32;
  fn aiur_gpu_population_threads() -> u64;
  fn aiur_gpu_malloc(
    device: i32,
    bytes: usize,
    output: *mut *mut c_void,
  ) -> i32;
  fn aiur_gpu_free(device: i32, pointer: *mut c_void) -> i32;
  fn aiur_gpu_host_alloc(bytes: usize, output: *mut *mut c_void) -> i32;
  fn aiur_gpu_host_free(pointer: *mut c_void) -> i32;
  fn aiur_gpu_upload(
    device: i32,
    destination: *mut c_void,
    source: *const c_void,
    bytes: usize,
  ) -> i32;
  fn aiur_gpu_download(
    device: i32,
    destination: *mut c_void,
    source: *const c_void,
    bytes: usize,
  ) -> i32;
  fn aiur_gpu_canonicalize(device: i32, words: *mut u64, count: u64) -> i32;
  fn aiur_gpu_build_index(
    device: i32,
    rows: *const u64,
    count: u64,
    inputs: u32,
    row_stride: u32,
    index: *mut u32,
    mask: u32,
  ) -> i32;
  fn aiur_gpu_populate(
    device: i32,
    circuit: *const AiurCircuit,
    output: *mut u64,
    base: u64,
    first: u64,
    rows: u64,
    height: u64,
    scratch: *mut u64,
    error: *mut AiurPopulationError,
    status: *mut AiurPopulationError,
  ) -> i32;
  fn aiur_gpu_count_ranges(
    device: i32,
    circuit: *const AiurCircuit,
    threads: u64,
    rows: *mut u64,
    scratch: *mut u64,
    ranges: *mut u64,
    error: *mut AiurPopulationError,
    status: *mut AiurPopulationError,
  ) -> i32;
  fn aiur_gpu_error_string(status: i32) -> *const std::ffi::c_char;
}

fn check(status: i32, what: &str) -> Result<(), String> {
  if status == 0 {
    return Ok(());
  }
  // SAFETY: the CUDA runtime returns a static NUL-terminated string.
  let message =
    unsafe { std::ffi::CStr::from_ptr(aiur_gpu_error_string(status)) };
  Err(format!("{what}: CUDA error {status} ({})", message.to_string_lossy()))
}

pub(super) fn memory_budget(device: i32) -> Result<u64, String> {
  let (mut free, mut total) = (0usize, 0usize);
  // SAFETY: both output pointers refer to initialized, writable values.
  check(
    unsafe { aiur_gpu_memory_info(device, &mut free, &mut total) },
    "GPU memory information",
  )?;
  Ok((total as u64) / 100 * 85)
}

/// A device allocation, freed on drop.
struct Buffer {
  device: i32,
  pointer: *mut c_void,
}
// SAFETY: the allocation is plain device memory owned by this value.
unsafe impl Send for Buffer {}
unsafe impl Sync for Buffer {}
impl Buffer {
  fn new(device: i32, bytes: usize) -> Result<Self, String> {
    let mut pointer = std::ptr::null_mut();
    // SAFETY: the out-pointer is valid for writing.
    check(
      unsafe { aiur_gpu_malloc(device, bytes, &raw mut pointer) },
      "GPU population allocation",
    )?;
    Ok(Self { device, pointer })
  }
  fn upload<T: Copy>(device: i32, data: &[T]) -> Result<Self, String> {
    let buffer = Self::new(device, std::mem::size_of_val(data))?;
    buffer.write(0, data)?;
    Ok(buffer)
  }
  /// Copies `data` to byte offset `offset`.
  fn write<T: Copy>(&self, offset: usize, data: &[T]) -> Result<(), String> {
    // SAFETY: callers stay within the allocation; `data` is host memory.
    check(
      unsafe {
        aiur_gpu_upload(
          self.device,
          self.pointer.cast::<u8>().add(offset).cast(),
          data.as_ptr().cast(),
          std::mem::size_of_val(data),
        )
      },
      "GPU population upload",
    )
  }
  /// Copies the allocation's first `words` words to the host.
  fn read(&self, words: usize) -> Result<Vec<u64>, String> {
    let mut values = vec![0u64; words];
    // SAFETY: callers stay within the allocation; `values` holds `words`.
    check(
      unsafe {
        aiur_gpu_download(
          self.device,
          values.as_mut_ptr().cast(),
          self.pointer,
          words * 8,
        )
      },
      "GPU population download",
    )?;
    Ok(values)
  }
  fn as_ptr<T>(&self) -> *mut T {
    self.pointer.cast()
  }
}
impl Drop for Buffer {
  fn drop(&mut self) {
    // SAFETY: allocated by `aiur_gpu_malloc` on this device, freed once.
    unsafe { aiur_gpu_free(self.device, self.pointer) };
  }
}

/// Words in one page-locked staging buffer.
const STAGING_WORDS: usize = 8 << 20;

/// A page-locked host buffer of [`STAGING_WORDS`] words.
struct Staging(*mut u64);
// SAFETY: the allocation is plain host memory owned by this value.
unsafe impl Send for Staging {}
impl Drop for Staging {
  fn drop(&mut self) {
    // SAFETY: allocated by `aiur_gpu_host_alloc`, freed once.
    unsafe { aiur_gpu_host_free(self.0.cast()) };
  }
}

/// Staging buffers kept between uploads: page-locking memory stalls every
/// other CUDA call in the process while it runs. At most
/// [`STAGING_POOL`] are kept; concurrent uploads beyond that allocate their
/// own and free them afterwards.
static STAGING: Mutex<Vec<Staging>> = Mutex::new(Vec::new());
const STAGING_POOL: usize = 4;

impl Buffer {
  /// Copies `pieces`, concatenated, to this buffer from word `offset` on.
  /// The driver stages pageable copies one at a time, at about the same
  /// rate however many threads issue them; packing into page-locked memory
  /// in parallel and copying from there runs at host memory and link speed.
  ///
  /// `parallel` packs on the current Rayon pool. Callers holding a lock
  /// that pool workers can wait on must pass `false`: a worker blocked in
  /// a parallel loop may run any queued job, including one that waits on
  /// that same lock.
  fn write_staged(
    &self,
    offset: usize,
    pieces: &[&[u64]],
    parallel: bool,
  ) -> Result<(), String> {
    let total: usize = pieces.iter().map(|p| p.len()).sum();
    if total == 0 {
      return Ok(());
    }
    let staging =
      STAGING.lock().unwrap_or_else(std::sync::PoisonError::into_inner).pop();
    let staging = match staging {
      Some(staging) => staging,
      None => {
        let mut pointer = std::ptr::null_mut();
        // SAFETY: the out-pointer is valid for writing.
        check(
          unsafe { aiur_gpu_host_alloc(STAGING_WORDS * 8, &raw mut pointer) },
          "GPU population staging allocation",
        )?;
        Staging(pointer.cast())
      },
    };
    // Pieces split at batch boundaries and into parallel-sized parts.
    const PART: usize = 1 << 17;
    let mut parts = Vec::new();
    let mut batch_start = offset;
    let mut used = 0;
    let mut result = Ok(());
    let flush = |parts: &mut Vec<(usize, &[u64])>,
                 used: &mut usize,
                 batch_start: &mut usize|
     -> Result<(), String> {
      let base = staging.0 as usize;
      let copy = |&(at, piece): &(usize, &[u64])| {
        // SAFETY: each part has its own range within the staging buffer.
        unsafe {
          std::ptr::copy_nonoverlapping(
            piece.as_ptr(),
            (base as *mut u64).add(at),
            piece.len(),
          );
        }
      };
      #[cfg(feature = "parallel")]
      if parallel {
        parts.par_iter().for_each(copy);
      } else {
        parts.iter().for_each(copy);
      }
      #[cfg(not(feature = "parallel"))]
      {
        let _ = parallel;
        parts.iter().for_each(copy);
      }
      // SAFETY: the destination range lies within this buffer.
      check(
        unsafe {
          aiur_gpu_upload(
            self.device,
            self.pointer.cast::<u64>().add(*batch_start).cast(),
            staging.0.cast(),
            *used * 8,
          )
        },
        "GPU population upload",
      )?;
      *batch_start += *used;
      *used = 0;
      parts.clear();
      Ok(())
    };
    'pieces: for piece in pieces {
      let mut rest = *piece;
      while !rest.is_empty() {
        let take = rest.len().min(PART).min(STAGING_WORDS - used);
        parts.push((used, &rest[..take]));
        used += take;
        rest = &rest[take..];
        if used == STAGING_WORDS {
          result = flush(&mut parts, &mut used, &mut batch_start);
          if result.is_err() {
            break 'pieces;
          }
        }
      }
    }
    if result.is_ok() && used > 0 {
      result = flush(&mut parts, &mut used, &mut batch_start);
    }
    let mut pool =
      STAGING.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    if pool.len() < STAGING_POOL {
      pool.push(staging);
    }
    drop(pool);
    result
  }
}

/// Device bytes of one launch workspace for `words` scratch words per
/// thread, as [`Workspace::new`] allocates it.
fn workspace_bytes(words: u64) -> u64 {
  // SAFETY: the launch bound has no arguments or side effects.
  unsafe { aiur_gpu_population_threads() }
    .saturating_mul(words.max(1))
    .saturating_mul(8)
    .saturating_add(std::mem::size_of::<AiurPopulationError>() as u64)
}

/// A launch's scratch and failure report, reused across tiles.
struct Workspace {
  scratch: Buffer,
  /// Words `scratch` holds.
  capacity: u64,
  error: Buffer,
  /// Page-locked host copy of `error`, written by each launch.
  status: *mut AiurPopulationError,
}
// SAFETY: the buffers are owned by this value and used by one launch at a time.
unsafe impl Send for Workspace {}
impl Workspace {
  fn new(device: i32, capacity: u64) -> Result<Self, String> {
    let bytes = usize::try_from(capacity.saturating_mul(8))
      .map_err(|_| "population scratch size overflow")?;
    let scratch = Buffer::new(device, bytes)?;
    let error =
      Buffer::new(device, std::mem::size_of::<AiurPopulationError>())?;
    let mut status = std::ptr::null_mut();
    // SAFETY: the out-pointer is valid for writing.
    check(
      unsafe {
        aiur_gpu_host_alloc(
          std::mem::size_of::<AiurPopulationError>(),
          &raw mut status,
        )
      },
      "GPU population status allocation",
    )?;
    Ok(Self { scratch, capacity, error, status: status.cast() })
  }
}
impl Drop for Workspace {
  fn drop(&mut self) {
    // SAFETY: allocated by `aiur_gpu_host_alloc`, freed once.
    unsafe { aiur_gpu_host_free(self.status.cast()) };
  }
}

/// A function's encoded plan with its placement, ready to upload.
struct Program {
  code: Vec<u32>,
  scratch: u32,
  inputs: u32,
  outputs: u32,
}

/// Device encodings of a backend's population plans, built once. Only the
/// members of selected device circuits are encoded; a circuit is filled on
/// the device only when all of its members can be.
pub(super) struct DevicePlans {
  programs: Vec<Option<Program>>,
  constants: Vec<u64>,
  /// Call targets: callee slot to function index.
  callees: Vec<usize>,
  pub(super) circuits: Vec<bool>,
  /// Per function: why its plan cannot be encoded, with details such as the
  /// hint channel or map name; empty when it can.
  causes: Vec<Vec<(HostCause, String)>>,
  /// Per function circuit: whether `AIUR_GPU_TRACE_CIRCUITS` admits it.
  selected: Vec<bool>,
  /// Compiled writers bound by `AIUR_GPU_TRACE=compiled`.
  compiled: Option<Arc<super::compiled::Selection>>,
}

fn map_kind(name: &str) -> Option<u32> {
  Some(match name {
    "UInt8::from_field" => 0,
    "UInt8::raw_bit_decomposition" => 1,
    "UInt8::range_pair" => 2,
    "UInt8::raw_xor" => 3,
    "UInt8::raw_and" => 4,
    "UInt8::raw_or" => 5,
    "UInt8::raw_lt" => 6,
    "UInt8::raw_add" => 7,
    "UInt8::raw_sub" => 8,
    "UInt8::raw_mul" => 9,
    "UInt8::raw_xor_split4" => 10,
    "UInt8::raw_xor_split7" => 11,
    "UInt8::raw_sum_byte" => 12,
    _ => return None,
  })
}

fn hint_kind(channel: &str) -> Option<u32> {
  Some(match channel {
    "u32.bytes" => 0,
    "u32.sub" => 1,
    "u32.add" => 2,
    "u32.add3" => 3,
    "u32.lt" => 4,
    "bytes_le" => 5,
    _ => return None,
  })
}

/// Postfix tokens of `p`, reading physical column `column(c)` for each of
/// its columns `c`.
fn polynomial(
  p: &Polynomial,
  constants: &mut Constants,
  out: &mut Vec<u32>,
  column: &impl Fn(usize) -> usize,
) -> Option<()> {
  match p {
    Polynomial::Const(value) => {
      out.extend([POLY_CONST, constants.word(*value)? & 0x7fff_ffff]);
    },
    Polynomial::Var(c) => {
      out.extend([POLY_VAR, u32::try_from(column(*c)).ok()?]);
    },
    Polynomial::Add(xs) | Polynomial::Sub(xs) | Polynomial::Mul(xs) => {
      polynomial(&xs[0], constants, out, column)?;
      polynomial(&xs[1], constants, out, column)?;
      out.extend([
        match p {
          Polynomial::Add(_) => POLY_ADD,
          Polynomial::Sub(_) => POLY_SUB,
          _ => POLY_MUL,
        },
        0,
      ]);
    },
  }
  Some(())
}

/// Encodes the plans of the functions `include` admits, with their own
/// constant pool and callee slots.
fn encode<B: WitnessField>(
  backend: &Backend<'_, '_, B>,
  include: impl Fn(usize) -> bool,
) -> (Vec<Option<Program>>, Constants, Vec<usize>) {
  let plan = &*backend.plan;
  let program = plan.program.program();
  let functions = program.functions.len();
  let mut constants = Constants::default();
  let mut callees = Vec::new();
  let mut slots = FxHashMap::default();
  let programs = plan
    .fills
    .iter()
    .enumerate()
    .map(|(f, fill)| {
      if !include(f) {
        return None;
      }
      let chip = plan.members[f];
      let placement = &backend.placements[chip];
      let steps = &plan.artifact.functions[f].steps;
      let mut call = |callable: usize| {
        if callable >= functions {
          map_kind(&program.maps.get(callable - functions)?.name)
            .map(Target::Map)
        } else {
          let next = u32::try_from(callees.len()).ok()?;
          let slot = *slots.entry(callable).or_insert_with(|| {
            callees.push(callable);
            next
          });
          Some(Target::Call(slot))
        }
      };
      let mut hint = |instruction: usize| {
        steps.iter().find_map(|step| match &step.action {
          Action::Hint { instruction: i, channel, .. } if *i == instruction => {
            hint_kind(channel)
          },
          _ => None,
        })
      };
      let column = |c: usize| placement.columns[c];
      let Encoded { mut code, scratch, inputs, outputs } =
        fill.encode(&mut call, &mut hint, &column, &mut constants)?;
      // The selector comes first: depth slot enables read it.
      code.push(u32::try_from(placement.selector).ok()?);
      encode_depth(
        &plan.depth,
        chip,
        &column,
        &mut call,
        &mut constants,
        &mut code,
      )?;
      code.push(u32::try_from(placement.writes.len()).ok()?);
      for write in &placement.writes {
        let mut tokens = vec![];
        polynomial(&write.value, &mut constants, &mut tokens, &|c| c)?;
        code.push(u32::try_from(write.column).ok()?);
        code.push(u32::try_from(tokens.len() / 2).ok()?);
        code.extend(tokens);
      }
      Some(Program { code, scratch, inputs, outputs })
    })
    .collect();
  (programs, constants, callees)
}

/// Each depth range table's first word in the flat device count buffer, and
/// the buffer's length in words.
fn range_offsets(depth: &DepthPlan) -> (Vec<usize>, usize) {
  let mut offsets = vec![];
  let mut words = 0usize;
  for table in &depth.tables {
    offsets.push(words);
    words += 1 << table.width;
  }
  (offsets, words)
}

/// Appends circuit `chip`'s depth section, over physical columns `column`:
/// the depth column (or [`NO_COLUMN`]) and the slot count, then per exact,
/// gap or external slot its kind, its new columns as (column, limb width,
/// range-table offset) triples, its callee slots, its enable, and the count
/// and each of its callee query's arguments, each polynomial as a token
/// count and tokens.
fn encode_depth(
  depth: &DepthPlan,
  chip: usize,
  column: &impl Fn(usize) -> usize,
  call: &mut impl FnMut(usize) -> Option<Target>,
  constants: &mut Constants,
  code: &mut Vec<u32>,
) -> Option<()> {
  let (offsets, _) = range_offsets(depth);
  let fill = &depth.fills[chip];
  code.push(match fill.column {
    Some(c) => u32::try_from(column(c)).ok().filter(|&c| c != NO_COLUMN)?,
    None => NO_COLUMN,
  });
  let exact = fill
    .exact
    .iter()
    .map(|e| (DEPTH_EXACT, vec![], &e.enable, &e.args, &e.callees));
  let slots = fill.slots.iter().map(|slot| {
    let (kind, columns) = match slot.kind {
      DepthKind::Gap(first) => (
        DEPTH_GAP,
        depth
          .limbs
          .iter()
          .enumerate()
          .map(|(i, &(width, table))| {
            [column(first + i), width as usize, offsets[table]]
          })
          .collect(),
      ),
      DepthKind::External(c) => (DEPTH_EXTERNAL, vec![[column(c), 0, 0]]),
    };
    (kind, columns, &slot.enable, &slot.args, &slot.callees)
  });
  code.push(u32::try_from(fill.exact.len() + fill.slots.len()).ok()?);
  for (kind, columns, enable, args, callees) in exact.chain(slots) {
    code.push(kind);
    code.push(u32::try_from(columns.len()).ok()?);
    for word in columns.into_iter().flatten() {
      code.push(u32::try_from(word).ok()?);
    }
    code.push(u32::try_from(callees.len()).ok()?);
    for &callee in callees {
      match call(callee)? {
        Target::Call(slot) => code.push(slot),
        Target::Map(_) => return None,
      }
    }
    let mut push = |p: &Polynomial, code: &mut Vec<u32>| {
      let mut tokens = vec![];
      polynomial(p, constants, &mut tokens, column)?;
      code.push(u32::try_from(tokens.len() / 2).ok()?);
      code.extend(tokens);
      Some(())
    };
    push(enable, code)?;
    code.push(u32::try_from(args.len()).ok()?);
    for arg in args {
      push(arg, code)?;
    }
  }
  Some(())
}

/// Whether a member of function circuit `ci` has a depth column or depth
/// slots, which compiled writers do not fill.
pub(super) fn circuit_has_depth<B: WitnessField>(
  backend: &Backend<'_, '_, B>,
  ci: usize,
) -> bool {
  backend.members[ci]
    .iter()
    .any(|&f| !backend.plan.depth.fills[backend.plan.members[f]].is_empty())
}

/// The host-only operations in function `f`'s population steps.
fn host_steps<B: WitnessField>(
  backend: &Backend<'_, '_, B>,
  f: usize,
) -> Vec<(HostCause, String)> {
  let maps = &backend.plan.program.program().maps;
  let mut causes = vec![];
  for step in &backend.plan.artifact.functions[f].steps {
    let cause = match &step.action {
      Action::Store { .. } => (HostCause::Store, "store".to_owned()),
      Action::Load { .. } => (HostCause::Load, "load".to_owned()),
      Action::Hint { channel, .. } if hint_kind(channel).is_none() => {
        (HostCause::UnsupportedHint, format!("hint {channel}"))
      },
      Action::Call { name, .. }
        if map_kind(name).is_none() && maps.iter().any(|m| m.name == *name) =>
      {
        (HostCause::UnsupportedMap, format!("map {name}"))
      },
      _ => continue,
    };
    if !causes.contains(&cause) {
      causes.push(cause);
    }
  }
  causes.sort();
  causes
}

/// The circuits named in `AIUR_GPU_TRACE_CIRCUITS`, if it is set.
fn allowlist() -> Result<Option<Vec<String>>, String> {
  match std::env::var("AIUR_GPU_TRACE_CIRCUITS") {
    Ok(value) => {
      let names: Vec<_> = value
        .split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(str::to_owned)
        .collect();
      Ok((!names.is_empty()).then_some(names))
    },
    Err(std::env::VarError::NotPresent) => Ok(None),
    Err(error) => Err(format!("AIUR_GPU_TRACE_CIRCUITS: {error}")),
  }
}

impl DevicePlans {
  /// Scratch words per launch thread for device circuit `ci`: its widest
  /// member plan when interpreted, none with a compiled writer. `members`
  /// lists each circuit's functions.
  fn scratch_words(&self, ci: usize, members: &[Vec<usize>]) -> u64 {
    if self.compiled.as_ref().is_some_and(|c| c.covers(ci)) {
      return 0;
    }
    members
      .get(ci)
      .into_iter()
      .flatten()
      .filter_map(|&f| self.programs[f].as_ref())
      .map(|p| u64::from(p.scratch))
      .max()
      .unwrap_or(0)
  }

  /// Device scratch the population launches can hold at once. Multi-stark
  /// fills up to `MAX_CONCURRENT_LDES` generated traces concurrently, at most
  /// one per device circuit, and each call takes a pooled workspace. The pool
  /// replaces a workspace too small for a call with a larger one, so every
  /// workspace held can grow to the widest circuit's size. None without
  /// device circuits.
  pub(super) fn scratch_bytes(&self, members: &[Vec<usize>]) -> u64 {
    let circuits: Vec<usize> =
      (0..self.circuits.len()).filter(|&ci| self.circuits[ci]).collect();
    let widest = circuits
      .iter()
      .map(|&ci| workspace_bytes(self.scratch_words(ci, members)))
      .max()
      .unwrap_or(0);
    let concurrent = circuits.len().min(multi_stark::cuda::MAX_CONCURRENT_LDES);
    widest.saturating_mul(concurrent as u64)
  }

  pub(super) fn record_bytes<B: WitnessField>(
    &self,
    backend: &Backend<'_, '_, B>,
    record: &Execution<B>,
  ) -> Result<u64, String> {
    Image::new(backend, self, record)?.bytes()
  }

  /// Categories and text for why function circuit `ci` stays on the host.
  pub(super) fn host_cause<B: WitnessField>(
    &self,
    backend: &Backend<'_, '_, B>,
    ci: usize,
  ) -> (Vec<HostCause>, String) {
    if self.circuits[ci] {
      return (vec![], "generated on device".to_owned());
    }
    let members = &backend.members[ci];
    let blocked: Vec<_> =
      members.iter().filter(|&&f| !self.causes[f].is_empty()).collect();
    if blocked.is_empty() {
      return if self.selected[ci]
        && self.compiled.is_some()
        && circuit_has_depth(backend, ci)
      {
        (
          vec![HostCause::CompiledDepth],
          "compiled writers do not fill depth columns".to_owned(),
        )
      } else if self.selected[ci] && self.compiled.is_some() {
        (
          vec![HostCause::NotCompiled],
          "no writer in the compiled bundle".to_owned(),
        )
      } else if self.selected[ci] {
        (vec![HostCause::EncodingLimit], "no device plan".to_owned())
      } else {
        (
          vec![HostCause::NotSelected],
          "not in AIUR_GPU_TRACE_CIRCUITS".to_owned(),
        )
      };
    }
    let mut causes: Vec<_> = blocked
      .iter()
      .flat_map(|&&f| self.causes[f].iter().map(|(c, _)| *c))
      .collect();
    if blocked.len() < members.len() {
      causes.push(HostCause::IneligibleGroup);
    }
    causes.sort();
    causes.dedup();
    let names: Vec<_> = blocked
      .iter()
      .map(|&&f| {
        let details: Vec<_> =
          self.causes[f].iter().map(|(_, d)| d.as_str()).collect();
        format!(
          "{} ({})",
          backend.plan.artifact.functions[f].name,
          details.join(", ")
        )
      })
      .collect();
    (causes, format!("unsupported population plans: {}", names.join(", ")))
  }

  /// The device population `AIUR_GPU_TRACE` selects. Unset, it is
  /// `compiled` when a compiled bundle is registered and lookups run on the
  /// device, and host population otherwise.
  pub(super) fn from_env<B: WitnessField>(
    backend: &Backend<'_, '_, B>,
  ) -> Result<Option<Self>, String> {
    let mode = match std::env::var("AIUR_GPU_TRACE") {
      Err(std::env::VarError::NotPresent)
        if backend.gpu_lookup_only && super::compiled::registered() =>
      {
        Ok("compiled".to_owned())
      },
      mode => mode,
    };
    match mode.as_deref() {
      Ok("generated") => {
        if !backend.gpu_lookup_only {
          return Err(
            "AIUR_GPU_TRACE=generated requires device lookups (unset AIUR_TRACE_ONLY_LOOKUPS=0)"
              .into(),
          );
        }
        Self::select(backend, allowlist()?.as_deref()).map(Some)
      },
      Ok(mode @ ("compiled" | "compiled+generated")) => {
        if !backend.gpu_lookup_only {
          return Err(format!(
            "AIUR_GPU_TRACE={mode} requires device lookups (unset AIUR_TRACE_ONLY_LOOKUPS=0)"
          ));
        }
        let mut plans = Self::select(backend, allowlist()?.as_deref())?;
        let selection = super::compiled::select(
          backend,
          &mut plans.circuits,
          &mut plans.callees,
          mode == "compiled+generated",
        )?;
        plans.compiled = Some(Arc::new(selection));
        Ok(Some(plans))
      },
      Ok("cpu") | Ok("") | Err(_) => Ok(None),
      Ok(other) => Err(format!(
        "AIUR_GPU_TRACE must be cpu, generated, compiled or compiled+generated, not {other:?}"
      )),
    }
  }

  /// Plans for every eligible circuit.
  #[cfg(test)]
  pub(super) fn new<B: WitnessField>(backend: &Backend<'_, '_, B>) -> Self {
    Self::select(backend, None).expect("no allowlist to reject")
  }

  /// Plans for the eligible circuits named in `allowlist` by circuit or
  /// member function name, or for every eligible circuit without one.
  pub(super) fn select<B: WitnessField>(
    backend: &Backend<'_, '_, B>,
    allowlist: Option<&[String]>,
  ) -> Result<Self, String> {
    let functions = &backend.plan.artifact.functions;
    let selected: Vec<bool> = backend
      .members
      .iter()
      .enumerate()
      .map(|(ci, members)| {
        allowlist.is_none_or(|names| {
          names.iter().any(|n| {
            *n == backend.names[ci]
              || members.iter().any(|&f| functions[f].name == *n)
          })
        })
      })
      .collect();
    if let Some(names) = allowlist {
      let unknown: Vec<_> = names
        .iter()
        .filter(|n| {
          !backend.names[..backend.members.len()].contains(n)
            && !functions.iter().any(|f| f.name == **n)
        })
        .map(String::as_str)
        .collect();
      if !unknown.is_empty() {
        return Err(format!(
          "AIUR_GPU_TRACE_CIRCUITS names no circuit or function: {}",
          unknown.join(", ")
        ));
      }
    }
    let (all, _, _) = encode(backend, |_| true);
    let causes: Vec<_> = all
      .iter()
      .enumerate()
      .map(|(f, program)| {
        if program.is_some() {
          return vec![];
        }
        let causes = host_steps(backend, f);
        if causes.is_empty() {
          vec![(HostCause::EncodingLimit, "encoding limit".to_owned())]
        } else {
          causes
        }
      })
      .collect();
    let circuits: Vec<bool> = backend
      .members
      .iter()
      .zip(&selected)
      .map(|(members, &selected)| {
        selected
          && !members.is_empty()
          && members.iter().all(|&f| all[f].is_some())
      })
      .collect();
    let mut include = vec![false; all.len()];
    for (ci, &on) in circuits.iter().enumerate() {
      if on {
        for &f in &backend.members[ci] {
          include[f] = true;
        }
      }
    }
    let (programs, constants, callees) = encode(backend, |f| include[f]);
    Ok(Self {
      programs,
      constants: constants.values,
      callees,
      circuits,
      causes,
      selected,
      compiled: None,
    })
  }

  pub(super) fn compiled(&self) -> Option<&super::compiled::Selection> {
    self.compiled.as_deref()
  }
}

/// A device circuit's member in an [`Image`].
struct MemberImage {
  /// Index into [`Image::tables`].
  table: usize,
  code_offset: usize,
  code_len: u32,
  scratch: u32,
  inputs: u32,
  outputs: u32,
  first: u64,
}

struct CircuitImage {
  members: Vec<MemberImage>,
  real: u64,
  width: u32,
  scratch: u32,
  /// Whether a member has gap slots, whose limbs use the range tables.
  gaps: bool,
}

/// An uploaded query table.
#[derive(Clone, Copy)]
struct TableImage {
  function: usize,
  count: usize,
  /// Words per row: inputs, then outputs.
  stride: usize,
  /// Whether the table's recorded heights are uploaded with it.
  depths: bool,
}

/// Everything a device record holds except the query table contents, kept
/// on the host to rebuild the record after a release.
struct Image {
  code: Vec<u32>,
  constants: Vec<u64>,
  tables: Vec<TableImage>,
  /// Callee slots in order: table index, inputs, outputs.
  callees: Vec<(usize, u32, u32)>,
  circuits: Vec<Option<CircuitImage>>,
  heights: Vec<usize>,
}

impl Image {
  fn new<B: WitnessField>(
    backend: &Backend<'_, '_, B>,
    plans: &DevicePlans,
    record: &Execution<B>,
  ) -> Result<Self, String> {
    let tables = &record.queries.tables;
    let mut code: Vec<u32> = vec![];
    let mut offsets = vec![0; plans.programs.len()];
    for (f, program) in plans.programs.iter().enumerate() {
      if let Some(program) = program {
        offsets[f] = code.len();
        code.extend(&program.code);
      }
    }
    let mut needed: Vec<usize> = plans.callees.clone();
    for (ci, &on) in plans.circuits.iter().enumerate() {
      if on {
        needed.extend(&backend.members[ci]);
      }
    }
    needed.sort_unstable();
    needed.dedup();
    let table_of: FxHashMap<usize, usize> =
      needed.iter().enumerate().map(|(i, &f)| (f, i)).collect();
    let uploaded = needed
      .iter()
      .map(|&f| {
        let (inputs, outputs) = tables[f].widths();
        let count = tables[f].len();
        let depths = tables[f].depths_len() != 0;
        if depths && tables[f].depths_len() < count {
          return Err("query record is missing depth heights".to_owned());
        }
        Ok(TableImage { function: f, count, stride: inputs + outputs, depths })
      })
      .collect::<Result<_, String>>()?;
    let callees = plans
      .callees
      .iter()
      .map(|&f| {
        let (inputs, outputs) = tables[f].widths();
        Ok((
          table_of[&f],
          u32::try_from(inputs).map_err(|_| "callee width overflow")?,
          u32::try_from(outputs).map_err(|_| "callee width overflow")?,
        ))
      })
      .collect::<Result<_, String>>()?;
    let count = backend.system.circuits.len();
    let mut circuits: Vec<Option<CircuitImage>> =
      (0..count).map(|_| None).collect();
    let mut heights = vec![0; count];
    for (ci, &on) in plans.circuits.iter().enumerate() {
      if !on {
        continue;
      }
      let mut members = vec![];
      let mut first = 0u64;
      let mut scratch = 0;
      for &f in &backend.members[ci] {
        let program = plans.programs[f].as_ref().expect("encoded member");
        members.push(MemberImage {
          table: table_of[&f],
          code_offset: offsets[f],
          code_len: u32::try_from(program.code.len())
            .map_err(|_| "device plan too long")?,
          scratch: program.scratch,
          inputs: program.inputs,
          outputs: program.outputs,
          first,
        });
        first += tables[f].len() as u64;
        scratch = scratch.max(program.scratch);
      }
      let real = usize::try_from(first).map_err(|_| "row count overflow")?;
      heights[ci] = if real == 0 {
        0
      } else {
        real.checked_next_power_of_two().ok_or("trace height overflow")?
      };
      circuits[ci] = Some(CircuitImage {
        members,
        real: first,
        width: u32::try_from(backend.system.circuits[ci].main_width)
          .map_err(|_| "circuit width overflow")?,
        scratch,
        gaps: backend.members[ci].iter().any(|&f| {
          backend.plan.depth.fills[backend.plan.members[f]]
            .slots
            .iter()
            .any(|slot| matches!(slot.kind, DepthKind::Gap(_)))
        }),
      });
    }
    Ok(Self {
      code,
      constants: plans.constants.clone(),
      tables: uploaded,
      callees,
      circuits,
      heights,
    })
  }

  fn index_slots(count: usize) -> Result<usize, String> {
    count
      .max(1)
      .checked_mul(2)
      .and_then(usize::checked_next_power_of_two)
      .ok_or_else(|| "device index size overflow".into())
  }

  /// Device bytes [`Self::upload`] allocates.
  fn bytes(&self) -> Result<u64, String> {
    let mut bytes = (self.code.len() as u128 * 4).max(8)
      + (self.constants.len() as u128 * 8).max(8);
    for table in &self.tables {
      bytes += (table.count as u128 * table.stride as u128).max(1) * 8;
      bytes += table.count.max(1) as u128 * 8;
      if table.depths {
        bytes += table.count.max(1) as u128 * 8;
      }
    }
    for &(table, _, _) in &self.callees {
      bytes += Self::index_slots(self.tables[table].count)? as u128 * 4;
    }
    bytes += (self.callees.len() as u128
      * std::mem::size_of::<AiurCallee>() as u128)
      .max(8);
    for circuit in self.circuits.iter().flatten() {
      bytes +=
        (circuit.members.len() * std::mem::size_of::<AiurFunction>()) as u128;
    }
    u64::try_from(bytes).map_err(|_| "device record size overflow".into())
  }

  /// Allocates the record on `device`, filling each query table's rows,
  /// multiplicities and heights with `fill`.
  fn upload(
    &self,
    device: i32,
    mut fill: impl FnMut(usize, &TableBuffers) -> Result<(), String>,
  ) -> Result<Resident, String> {
    let code = Buffer::upload(device, &self.code)?;
    let constants = Buffer::upload(device, &self.constants)?;
    let mut tables = vec![];
    for (i, table) in self.tables.iter().enumerate() {
      let words =
        table.count.checked_mul(table.stride).ok_or("table size overflow")?;
      let buffers = TableBuffers {
        rows: Buffer::new(device, words.max(1) * 8)?,
        multiplicities: Buffer::new(device, table.count.max(1) * 8)?,
        depths: table
          .depths
          .then(|| Buffer::new(device, table.count.max(1) * 8))
          .transpose()?,
      };
      fill(i, &buffers)?;
      tables.push(buffers);
    }
    let mut indexes = vec![];
    let mut callees = vec![];
    for &(table, inputs, outputs) in &self.callees {
      let TableImage { count, stride, .. } = self.tables[table];
      let size = Self::index_slots(count)?;
      let mask =
        u32::try_from(size - 1).map_err(|_| "callee index overflow")?;
      let index = Buffer::new(device, size * 4)?;
      let buffers = &tables[table];
      // SAFETY: `index` holds `size` words; `rows` holds the table rows.
      check(
        unsafe {
          aiur_gpu_build_index(
            device,
            buffers.rows.as_ptr(),
            count as u64,
            inputs,
            stride as u32,
            index.as_ptr(),
            mask,
          )
        },
        "GPU population callee index",
      )?;
      callees.push(AiurCallee {
        rows: buffers.rows.as_ptr(),
        index: index.as_ptr(),
        multiplicities: buffers.multiplicities.as_ptr(),
        depths: buffers.depths_ptr(),
        count: count as u64,
        mask,
        inputs,
        outputs,
        stride: stride as u32,
      });
      indexes.push(index);
    }
    let callee_buffer = Buffer::upload(device, &callees)?;
    let mut descriptors = vec![];
    let circuits = self
      .circuits
      .iter()
      .map(|circuit| {
        let Some(circuit) = circuit else { return Ok(None) };
        let members: Vec<_> = circuit
          .members
          .iter()
          .map(|m| {
            let TableImage { count, stride, .. } = self.tables[m.table];
            let buffers = &tables[m.table];
            AiurFunction {
              // SAFETY: offsets index the uploaded code.
              code: unsafe { code.as_ptr::<u32>().add(m.code_offset) },
              constants: constants.as_ptr(),
              rows: buffers.rows.as_ptr(),
              multiplicities: buffers.multiplicities.as_ptr(),
              depths: buffers.depths_ptr(),
              count: count as u64,
              first: m.first,
              code_len: m.code_len,
              scratch: m.scratch,
              inputs: m.inputs,
              outputs: m.outputs,
              stride: stride as u32,
              pad: 0,
            }
          })
          .collect();
        let buffer = Buffer::upload(device, &members)?;
        let descriptor = AiurCircuit {
          members: buffer.as_ptr(),
          callees: callee_buffer.as_ptr(),
          real: circuit.real,
          member_count: members.len() as u32,
          width: circuit.width,
          scratch: circuit.scratch,
          pad: 0,
        };
        descriptors.push(buffer);
        Ok(Some(descriptor))
      })
      .collect::<Result<_, String>>()?;
    let mut buffers = vec![code, constants, callee_buffer];
    buffers.extend(indexes);
    buffers.extend(descriptors);
    Ok(Resident { circuits, tables, _buffers: buffers })
  }
}

/// One uploaded query table: its rows, multiplicities and, when tracked,
/// recorded heights.
struct TableBuffers {
  rows: Buffer,
  multiplicities: Buffer,
  depths: Option<Buffer>,
}

impl TableBuffers {
  fn depths_ptr(&self) -> *const u64 {
    self.depths.as_ref().map_or(std::ptr::null(), |d| d.as_ptr())
  }
}

/// A record's device allocations.
struct Resident {
  circuits: Vec<Option<AiurCircuit>>,
  /// Each [`Image::tables`] entry's buffers.
  tables: Vec<TableBuffers>,
  _buffers: Vec<Buffer>,
}

/// Host copy of an uploaded table's canonical rows, multiplicities and
/// heights (empty when untracked).
struct Spilled {
  rows: Vec<u64>,
  multiplicities: Vec<u64>,
  depths: Vec<u64>,
}

#[derive(Default)]
struct State {
  resident: Option<Resident>,
  /// Host copy of each uploaded table, taken by the first release.
  spilled: Option<Vec<Spilled>>,
}

/// One proof's device-resident record tables and circuit descriptors.
pub(super) struct DeviceRecord {
  device: i32,
  image: Image,
  state: RwLock<State>,
  /// Launch workspaces, reused by tiles and freed with the record.
  workspaces: Mutex<Vec<Workspace>>,
  /// Whether multi-stark's release requests free the record.
  releasable: bool,
  /// Device bytes of the uploaded record.
  bytes: u64,
  compiled: Option<Arc<super::compiled::Selection>>,
  /// Depth range-table uses of every real row of the device circuits,
  /// counted at upload.
  ranges: RangeCounts,
}
// SAFETY: the raw pointers address device memory owned by `state`, and
// launch workspaces are used by one tile at a time.
unsafe impl Send for DeviceRecord {}
unsafe impl Sync for DeviceRecord {}

fn poisoned<T>(_: T) -> String {
  "GPU population state poisoned".into()
}

impl DeviceRecord {
  /// Uploads what the device circuits read from `record`: their member
  /// queries and every callee's queries with an input index, with the
  /// recorded heights of tables that track them. Then counts the device
  /// circuits' depth range-table uses.
  pub(super) fn upload<B: WitnessField>(
    backend: &Backend<'_, '_, B>,
    plans: &DevicePlans,
    record: &Execution<B>,
    device: i32,
  ) -> Result<Self, String> {
    let image = Image::new(backend, plans, record)?;
    let tables = &record.queries.tables;
    let resident = image.upload(device, |i, buffers| {
      let TableImage { function, count, stride, .. } = image.tables[i];
      let table = &tables[function];
      if table.static_map.is_some() {
        return Err("GPU population cannot read a map's table".into());
      }
      let (chunks, chunk_stride, per_chunk) = table.row_chunks();
      if chunk_stride != stride {
        return Err("query table stride changed".into());
      }
      let mut done = 0;
      let mut words = Vec::new();
      for chunk in chunks {
        let take = per_chunk.min(count - done);
        if take == 0 {
          break;
        }
        words.push(B::words(&chunk[..take * stride]));
        done += take;
      }
      if done != count {
        return Err("query table storage ended early".into());
      }
      let pieces: Vec<&[u64]> = words.iter().map(|w| &w[..]).collect();
      buffers.rows.write_staged(0, &pieces, true)?;
      // SAFETY: the buffer holds `count * stride` words.
      check(
        unsafe {
          aiur_gpu_canonicalize(
            device,
            buffers.rows.as_ptr(),
            (count * stride) as u64,
          )
        },
        "GPU population canonicalization",
      )?;
      let counts = &table.counts()[..count];
      if counts.iter().any(|&c| c >= Val::ORDER_U64) {
        return Err("function count reaches field characteristic".into());
      }
      buffers.multiplicities.write_staged(0, &[counts], true)?;
      if let Some(depths) = &buffers.depths {
        let heights = &table.depths()[..count];
        if heights.iter().any(|&d| d >= Val::ORDER_U64) {
          return Err("query record depth reaches field characteristic".into());
        }
        depths.write_staged(0, &[heights], true)?;
      }
      Ok(())
    })?;
    let bytes = image.bytes()?;
    let mut record = Self {
      device,
      image,
      state: RwLock::new(State { resident: Some(resident), spilled: None }),
      workspaces: Mutex::new(vec![]),
      releasable: release_enabled(),
      bytes,
      compiled: plans.compiled.clone(),
      ranges: RangeCounts::default(),
    };
    record.ranges = record.count_ranges(&backend.plan.depth)?;
    Ok(record)
  }

  /// Uses of the depth range tables by every real row of the device
  /// circuits with gap slots: one counting launch per such circuit, which
  /// fills each row into a per-thread buffer and tallies its gap limbs.
  fn count_ranges(&self, depth: &DepthPlan) -> Result<RangeCounts, String> {
    let (_, words) = range_offsets(depth);
    let counted: Vec<usize> = (0..self.image.circuits.len())
      .filter(|&ci| {
        self.image.circuits[ci].as_ref().is_some_and(|c| c.gaps && c.real > 0)
      })
      .collect();
    if counted.is_empty() || words == 0 {
      return Ok(RangeCounts::default());
    }
    let ranges = Buffer::upload(self.device, &vec![0u64; words])?;
    let state = self.resident()?;
    let resident = state.resident.as_ref().expect("resident record");
    // SAFETY: plain query of the launch configuration.
    let launch = unsafe { aiur_gpu_population_threads() };
    for ci in counted {
      let circuit = resident.circuits[ci].ok_or("not a device circuit")?;
      let width = u64::from(circuit.width).max(1);
      // At most 2^24 words of per-thread rows, in whole blocks.
      let threads = ((1u64 << 24) / width / 128 * 128).clamp(128, launch);
      let rows = Buffer::new(
        self.device,
        usize::try_from(threads * width * 8)
          .map_err(|e| format!("range counting buffer: {e}"))?,
      )?;
      let workspace = Workspace::new(
        self.device,
        threads.saturating_mul(u64::from(circuit.scratch).max(1)),
      )?;
      // SAFETY: device pointers come from this record's resident buffers,
      // which the read guard keeps alive, and from buffers sized above for
      // `threads` threads.
      check(
        unsafe {
          aiur_gpu_count_ranges(
            self.device,
            &circuit,
            threads,
            rows.as_ptr(),
            workspace.scratch.as_ptr(),
            ranges.as_ptr(),
            workspace.error.as_ptr(),
            workspace.status,
          )
        },
        "GPU depth range counting",
      )?;
      // SAFETY: the launch completed, so the page-locked copy is current.
      population_status(ci, unsafe { workspace.status.read_volatile() })?;
    }
    drop(state);
    let flat = ranges.read(words)?;
    Ok(RangeCounts::from_flat(depth.tables.iter().map(|t| t.width), &flat))
  }

  /// Depth range-table uses of every real row of the device circuits.
  pub(super) fn ranges(&self) -> &RangeCounts {
    &self.ranges
  }

  /// The padded height of a device circuit, if `ci` is one.
  pub(super) fn height(&self, ci: usize) -> Option<usize> {
    self.image.circuits[ci].as_ref().map(|_| self.image.heights[ci])
  }

  fn width(&self, ci: usize) -> usize {
    self.image.circuits[ci].as_ref().map_or(0, |c| c.width as usize)
  }

  /// The record on the device, uploaded again from its host copy if it was
  /// released.
  fn resident(&self) -> Result<RwLockReadGuard<'_, State>, String> {
    loop {
      let state = self.state.read().map_err(poisoned)?;
      if state.resident.is_some() {
        return Ok(state);
      }
      drop(state);
      let mut state = self.state.write().map_err(poisoned)?;
      if state.resident.is_none() {
        let spilled =
          state.spilled.as_ref().ok_or("released record has no host copy")?;
        // Sequential packing: a parallel loop here could run a queued
        // tile job on this thread, which would wait on the write lock it
        // holds.
        state.resident =
          Some(self.image.upload(self.device, |i, buffers| {
            let copy = &spilled[i];
            buffers.rows.write_staged(0, &[&copy.rows], false)?;
            buffers.multiplicities.write_staged(
              0,
              &[&copy.multiplicities],
              false,
            )?;
            match &buffers.depths {
              Some(depths) => depths.write_staged(0, &[&copy.depths], false),
              None => Ok(()),
            }
          })?);
      }
    }
  }

  /// Frees the record and launch workspaces on `device`, first copying the
  /// tables to the host if no copy exists. Tiles requested later upload the
  /// record again. If the copy fails the record stays resident.
  pub(super) fn release(&self, device: i32) {
    if device != self.device {
      return;
    }
    let mut state =
      self.state.write().unwrap_or_else(std::sync::PoisonError::into_inner);
    let Some(resident) = &state.resident else { return };
    if state.spilled.is_none() {
      let copy = self
        .image
        .tables
        .iter()
        .zip(&resident.tables)
        .map(|(table, buffers)| {
          Ok(Spilled {
            rows: buffers.rows.read(table.count * table.stride)?,
            multiplicities: buffers.multiplicities.read(table.count)?,
            depths: match &buffers.depths {
              Some(depths) => depths.read(table.count)?,
              None => vec![],
            },
          })
        })
        .collect::<Result<Vec<_>, String>>();
      match copy {
        Ok(copy) => state.spilled = Some(copy),
        Err(error) => {
          eprintln!("[aiur/gpu] keeping device record resident: {error}");
          return;
        },
      }
    }
    state.resident = None;
    self
      .workspaces
      .lock()
      .unwrap_or_else(std::sync::PoisonError::into_inner)
      .clear();
  }

  /// A workspace for at least `words` scratch words per launch thread.
  fn workspace(&self, words: u64) -> Result<Workspace, String> {
    // SAFETY: plain query of the launch configuration.
    let capacity =
      unsafe { aiur_gpu_population_threads() }.saturating_mul(words.max(1));
    let pooled = self.workspaces.lock().map_err(poisoned)?.pop();
    match pooled {
      Some(workspace) if workspace.capacity >= capacity => Ok(workspace),
      _ => Workspace::new(self.device, capacity),
    }
  }

  /// Fills `rows` rows of circuit `ci`'s shard (`base`, `height`) from shard
  /// row `first` into device memory at `output`.
  #[allow(clippy::too_many_arguments)]
  pub(super) fn populate(
    &self,
    ci: usize,
    output: *mut u64,
    base: usize,
    first: usize,
    rows: usize,
    height: usize,
    real_rows: usize,
  ) -> Result<(), String> {
    let state = self.resident()?;
    let resident = state.resident.as_ref().expect("resident record");
    let mut circuit = resident.circuits[ci].ok_or("not a device circuit")?;
    circuit.real = circuit
      .real
      .min(base.checked_add(real_rows).ok_or("device slice overflow")? as u64);
    if let Some(selection) = &self.compiled
      && selection.covers(ci)
    {
      // Compiled writers keep their slots in registers: the smallest
      // pooled workspace serves for its error and status words.
      let workspace = self.workspace(0)?;
      let launched = selection.populate(
        ci,
        self.device,
        (&raw const circuit).cast(),
        output,
        base,
        first,
        rows,
        height,
        workspace.error.as_ptr(),
        workspace.status.cast(),
      );
      // A failed launch may leave work queued on the workspace, so it is
      // freed rather than reused.
      launched?;
      // SAFETY: the launch completed, so the page-locked copy is current.
      let status = unsafe { workspace.status.read_volatile() };
      self.workspaces.lock().map_err(poisoned)?.push(workspace);
      return population_status(ci, status);
    }
    let workspace = self.workspace(u64::from(circuit.scratch))?;
    // SAFETY: device pointers come from this record's resident buffers,
    // which the read guard keeps alive; the caller owns `rows * width`
    // words at `output` on this device; the workspace is exclusively ours.
    let launched = check(
      unsafe {
        aiur_gpu_populate(
          self.device,
          &circuit,
          output,
          base as u64,
          first as u64,
          rows as u64,
          height as u64,
          workspace.scratch.as_ptr(),
          workspace.error.as_ptr(),
          workspace.status,
        )
      },
      "GPU population",
    );
    // A failed launch may leave work queued on the workspace, so it is
    // freed rather than reused.
    launched?;
    // SAFETY: the launch completed, so the page-locked copy is current.
    let status = unsafe { workspace.status.read_volatile() };
    self.workspaces.lock().map_err(poisoned)?.push(workspace);
    population_status(ci, status)
  }

  #[cfg(test)]
  pub(super) fn is_resident(&self) -> bool {
    self.state.read().unwrap().resident.is_some()
  }

  #[cfg(test)]
  pub(super) fn pooled_workspaces(&self) -> usize {
    self.workspaces.lock().unwrap().len()
  }

  /// Populates rows into a device tile prefilled with `fill` and returns
  /// the raw words the device wrote.
  #[cfg(test)]
  #[allow(clippy::too_many_arguments)]
  pub(super) fn tile_words(
    &self,
    ci: usize,
    base: usize,
    first: usize,
    rows: usize,
    height: usize,
    real_rows: usize,
    fill: u64,
  ) -> Result<Vec<u64>, String> {
    let words = rows * self.width(ci);
    let tile = Buffer::upload(self.device, &vec![fill; words.max(1)])?;
    self.populate(ci, tile.as_ptr(), base, first, rows, height, real_rows)?;
    tile.read(words)
  }
}

/// The error a population launch recorded, if any.
fn population_status(
  ci: usize,
  status: AiurPopulationError,
) -> Result<(), String> {
  if status.code == 0 {
    return Ok(());
  }
  Err(format!(
    "GPU population of circuit {ci} failed at row {} (kernel {}): {}",
    status.row,
    status.op,
    match status.code {
      1 => "active zero denominator",
      2 => "no matching trace arm",
      3 => "rejected pattern actually matches",
      4 => "no table entry for map input",
      5 => "missing recorded callee",
      6 => "invalid hint input",
      8 => "device polynomial stack overflow",
      9 => "callee is not below its caller, or its depth gap is too wide",
      10 => "exact depth slot callee is not one below its caller",
      11 => "pending recorded callee",
      12 => "missing recorded callee height",
      _ => "invalid device plan encoding",
    }
  ))
}

/// Rows `base..base + height` of a device circuit: one batch shard.
pub(super) struct DeviceTrace {
  pub(super) record: Arc<DeviceRecord>,
  pub(super) circuit: usize,
  pub(super) base: usize,
  pub(super) height: usize,
  pub(super) real_rows: usize,
}

impl TraceGenerator<Val> for DeviceTrace {
  fn height(&self) -> usize {
    self.height
  }
  fn width(&self) -> usize {
    self.record.width(self.circuit)
  }
  fn write_rows(&self, first: usize, output: &mut [Val]) {
    let width = self.width();
    assert_eq!(output.len() % width, 0, "partial generated row");
    let rows = output.len() / width;
    let mut run = || -> Result<(), String> {
      let tile = Buffer::new(self.record.device, output.len().max(1) * 8)?;
      self.record.populate(
        self.circuit,
        tile.as_ptr(),
        self.base,
        first % self.height,
        rows,
        self.height,
        self.real_rows,
      )?;
      // SAFETY: `Goldilocks` is `#[repr(transparent)]` over `u64`; the tile
      // holds `output.len()` canonical words.
      check(
        unsafe {
          aiur_gpu_download(
            self.record.device,
            output.as_mut_ptr().cast(),
            tile.as_ptr(),
            output.len() * 8,
          )
        },
        "GPU population download",
      )
    };
    run().unwrap_or_else(|error| panic!("{error}"));
  }
  fn write_device_rows(&self, view: DeviceTraceView<'_>) -> Result<(), String> {
    if view.width() != self.width() || view.device_id() != self.record.device {
      return Err("generated trace tile mismatch".into());
    }
    self.record.populate(
      self.circuit,
      view.as_mut_ptr(),
      self.base,
      view.first_row() % self.height,
      view.rows(),
      self.height,
      self.real_rows,
    )
  }
  fn device_state_bytes(&self) -> usize {
    if self.record.releasable {
      usize::try_from(self.record.bytes).unwrap_or(usize::MAX)
    } else {
      0
    }
  }
  fn device_state_resident(&self) -> bool {
    self
      .record
      .state
      .read()
      .unwrap_or_else(std::sync::PoisonError::into_inner)
      .resident
      .is_some()
  }
  fn device_workspace_bytes(&self) -> usize {
    let words = if self
      .record
      .compiled
      .as_ref()
      .is_some_and(|c| c.covers(self.circuit))
    {
      0
    } else {
      self.record.image.circuits[self.circuit]
        .as_ref()
        .map_or(0, |c| u64::from(c.scratch))
    };
    usize::try_from(workspace_bytes(words)).unwrap_or(usize::MAX)
  }
  fn release_device(&self, device_id: i32) {
    if self.record.releasable {
      self.record.release(device_id);
    }
  }
}

/// Whether a release request frees the device record, keeping a host copy
/// for re-upload. On unless `AIUR_GPU_TRACE_RELEASE=0`: multi-stark asks only
/// when a phase's admission is short of memory, so the record then never
/// pins device memory a later phase needs. The copy lives as long as the
/// record, so host planning charges it whenever this is on.
pub(super) fn release_enabled() -> bool {
  std::env::var("AIUR_GPU_TRACE_RELEASE").as_deref() != Ok("0")
}
