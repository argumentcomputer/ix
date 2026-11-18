//! Stage-one population on the GPU (`AIUR_GPU_TRACE=generated`).
//!
//! Function circuits whose population plans need no host-only state are
//! filled on the device by `cuda/population.cu`, which interprets the same
//! compiled plans as the host writer ([`crate::trace::plan`]) and applies the
//! same placement. They reach multi-stark as generated traces: the host
//! neither builds nor uploads their rows, and graph lookups regenerate tiles
//! on the device. Other circuits (memory, fixed tables, plans with hints
//! that have no device data or maps outside the U8 library) keep host rows.
//! Proof bytes are identical to host population.
//!
//! A hint keyed by two fields with field outputs is read on the device when
//! the record binds its channel to [`DeviceArenas`] (stream advice reads,
//! such as IxVM's input bytes): the arenas are uploaded once per device
//! record, beside the tables, and kept across its shard images. A record
//! whose sites carry no such data, or data from more than one source, keeps
//! those circuits on the host.
//!
//! The device reads the record tables those rows read: query tables, and the
//! ROM cells of each width that stores and loads access, through a hash index
//! of each table's keys. When execution recorded every device circuit
//! member's row references ([`crate::refs`]) and the planner found the whole
//! record does not fit beside a shard's proving, the record is uploaded one
//! shard at a time ([`DeviceRecord::
//! upload_sharded`]): a shard image ([`ShardRows`]) holds only the shard's
//! own rows and the callee rows and ROM cells their references name,
//! gathered on the host while the previous shard proves and uploaded by the
//! shard's first tile, with indexes over just those rows. A lookup that finds
//! its key there finds the row a whole-table lookup would, since keys are
//! unique in a table; one that does not fails loudly. Otherwise (no
//! references, or no layout) the whole record is uploaded once per proof,
//! so the execution record can be dropped before proving.
//!
//! Depth circuits (the depth pass, [`crate::trace::depth`]) are filled on the
//! device too: each plan carries a depth section, and the record upload holds
//! the recorded query heights. Their gap limbs' range-table uses are counted
//! at upload, by a pass over every real row (shard by shard, for a per-shard
//! record), because the fixed range tables are committed before any tile is
//! generated and tiles can be generated more than once.
//!
//! `AIUR_GPU_TRACE_CIRCUITS=a,b` restricts device population to the listed
//! circuits, named by circuit or by member function; the record upload then
//! holds only what those circuits read.
//!
//! Multi-stark asks a generated source to release its device state only
//! under device memory pressure, when admitting a commitment, lookup or
//! quotient phase that is short of memory. The uploaded record is then
//! freed and uploaded again on the next tile: from the execution record
//! itself while a proof lends it ([`DeviceRecord::attach`]), as streamed
//! proofs do, so the host holds no second copy; otherwise from a host copy
//! taken once at the first release. A shard image is only ever uploaded
//! from a lent record. Because admission can reclaim it,
//! device planning does not reserve the record beside the proving peak.
//! `AIUR_GPU_TRACE_RELEASE=0` pins the record instead; device planning then
//! charges it.
use super::{
  planning::HostCause,
  streaming::{BatchLayout, ShardLayout},
  *,
};
use crate::{
  Execution,
  bytecode::Type,
  hints::{ArenaData, DeviceArenas},
  query::Stored,
  trace::{
    Action,
    depth::{DepthPlan, Kind as DepthKind},
    plan::device::{Constants, Encoded, Source, Target},
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

/// The hint kind of a read of a record's advice arenas, after the word
/// hints of [`crate::trace::DEVICE_HINTS`] (`HINT_ARENA_READ` in
/// `cuda/population.cu`).
const HINT_ARENA_READ: u32 = 6;

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
  /// Query `q` is row `q - offset` of `rows`, `multiplicities` and `depths`.
  offset: u64,
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
  /// Each row's query or ROM address, ascending, or null when the rows are
  /// the whole table.
  ids: *const u64,
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

/// One advice arena on the device: bytes, or canonical words when `words`
/// is set; both null when empty.
#[repr(C)]
#[derive(Clone, Copy)]
struct AiurArena {
  bytes: *const u8,
  words: *const u64,
  len: u64,
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
    arenas: *const AiurArena,
    arena_count: u64,
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
    arenas: *const AiurArena,
    arena_count: u64,
    begin: u64,
    end: u64,
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

/// The device bytes a shard may plan to hold: the device's memory minus the
/// reserve multi-stark keeps free when it admits a phase
/// (`MULTI_STARK_CUDA_MIN_FREE_BYTES`, by default none).
/// Planning against the same bound multi-stark admits against keeps a
/// planned shard from spilling.
pub(super) fn memory_budget(device: i32) -> Result<u64, String> {
  let (mut free, mut total) = (0usize, 0usize);
  // SAFETY: both output pointers refer to initialized, writable values.
  check(
    unsafe { aiur_gpu_memory_info(device, &mut free, &mut total) },
    "GPU memory information",
  )?;
  let total = total as u64;
  let reserve = match std::env::var("MULTI_STARK_CUDA_MIN_FREE_BYTES") {
    Ok(value) => value.parse::<u64>().map_err(|_| {
      format!(
        "MULTI_STARK_CUDA_MIN_FREE_BYTES must be a byte count, not {value:?}"
      )
    })?,
    Err(_) => 0,
  };
  Ok(total.saturating_sub(reserve))
}

/// Free bytes on `device`, or zero if the query fails.
fn device_free(device: i32) -> u64 {
  let (mut free, mut total) = (0usize, 0usize);
  // SAFETY: both output pointers refer to initialized, writable values.
  let status = unsafe { aiur_gpu_memory_info(device, &mut free, &mut total) };
  if status == 0 { free as u64 } else { 0 }
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
  fn write_staged<T: Copy + Into<u64> + Sync>(
    &self,
    offset: usize,
    pieces: &[&[T]],
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
    let flush = |parts: &mut Vec<(usize, &[T])>,
                 used: &mut usize,
                 batch_start: &mut usize|
     -> Result<(), String> {
      let base = staging.0 as usize;
      let copy = |&(at, piece): &(usize, &[T])| {
        // SAFETY: each part has its own range within the staging buffer.
        let words = unsafe {
          std::slice::from_raw_parts_mut(
            (base as *mut u64).add(at),
            piece.len(),
          )
        };
        for (word, &value) in words.iter_mut().zip(piece) {
          *word = value.into();
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

impl Buffer {
  /// Writes `rows` rows of `stride` words from word zero on, row `i` filled
  /// by `fill(i, row)`, packed into page-locked staging a buffer at a time,
  /// on scoped threads when `parallel`. Not on the Rayon pool: callers may
  /// hold the device record's state lock, and a Rayon worker waiting in a
  /// parallel loop can run a queued tile job that waits on that lock.
  fn write_gathered(
    &self,
    rows: usize,
    stride: usize,
    parallel: bool,
    fill: impl Fn(usize, &mut [u64]) + Sync,
  ) -> Result<(), String> {
    if rows == 0 || stride == 0 {
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
    let batch = (STAGING_WORDS / stride).max(1);
    let mut result = Ok(());
    let mut first = 0;
    while first < rows && result.is_ok() {
      let count = batch.min(rows - first);
      // SAFETY: the staging buffer holds `STAGING_WORDS >= count * stride`
      // words, and only this call uses it.
      let words = unsafe {
        std::slice::from_raw_parts_mut(staging.0, count * stride)
      };
      let threads = if parallel {
        std::thread::available_parallelism().map_or(1, usize::from)
      } else {
        1
      };
      let per_thread = count.div_ceil(threads).max(4096) * stride;
      let fill = &fill;
      std::thread::scope(|scope| {
        for (part, words) in words.chunks_mut(per_thread).enumerate() {
          let start = first + part * (per_thread / stride);
          let mut pack = move || {
            for (i, row) in words.chunks_mut(stride).enumerate() {
              fill(start + i, row);
            }
          };
          if threads == 1 {
            pack();
          } else {
            scope.spawn(pack);
          }
        }
      });
      // SAFETY: the destination range lies within this buffer.
      result = check(
        unsafe {
          aiur_gpu_upload(
            self.device,
            self.pointer.cast::<u64>().add(first * stride).cast(),
            staging.0.cast(),
            count * stride * 8,
          )
        },
        "GPU population upload",
      );
      first += count;
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
pub(super) fn workspace_bytes(words: u64) -> u64 {
  // SAFETY: the launch bound has no arguments or side effects.
  let scratch = unsafe { aiur_gpu_population_threads() }
    .saturating_mul(words.max(1))
    .saturating_mul(8);
  let bytes = allocated(u128::from(scratch))
    + allocated(std::mem::size_of::<AiurPopulationError>() as u128);
  u64::try_from(bytes).unwrap_or(u64::MAX)
}

/// Device memory a `cudaMalloc` of `bytes` takes from the free pool.
/// Measured on an RTX PRO 6000 (CUDA 13, driver 595) with 2000 equal
/// requests each: a request above 1 MiB takes whole 2 MiB pages; smaller
/// ones are packed into shared 2 MiB pages at 1 KiB granularity, with
/// packing loss of up to a third (8 bytes took 1.0 KiB, 16385 took 17.4 KiB,
/// 512 KiB + 1 took 683 KiB of a page shared three ways), which twice the
/// rounded size, at most a page, bounds. A request of zero bytes allocates
/// eight.
fn allocated(bytes: u128) -> u128 {
  const PAGE: u128 = 2 << 20;
  const GRAIN: u128 = 1 << 10;
  let bytes = bytes.max(8);
  if bytes > PAGE / 2 {
    bytes.div_ceil(PAGE) * PAGE
  } else {
    (2 * bytes.div_ceil(GRAIN) * GRAIN).min(PAGE)
  }
}

/// Device bytes [`ArenaBuffers::upload`] allocates for `arenas`.
fn arena_bytes(arenas: &[ArenaData<'_>]) -> u128 {
  allocated(arenas.len().max(1) as u128 * size_of::<AiurArena>() as u128)
    + arenas
      .iter()
      .filter(|a| !a.is_empty())
      .map(|a| allocated(a.bytes() as u128))
      .sum::<u128>()
}

/// Device bytes the workspace pool can hold for concurrent calls needing
/// `workspaces` bytes each (see [`DevicePlans::scratch_bytes`]).
fn pooled_scratch(workspaces: &[u64]) -> u64 {
  let minimal = workspace_bytes(0);
  let limit = multi_stark::cuda::MAX_CONCURRENT_LDES;
  let scratch: Vec<u64> =
    workspaces.iter().copied().filter(|&bytes| bytes > minimal).collect();
  let widest = scratch.iter().copied().max().unwrap_or(0);
  widest
    .saturating_mul(scratch.len().min(limit) as u64)
    .saturating_add(minimal.saturating_mul(workspaces.len().min(limit) as u64))
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
  /// Lookup slots its plan and depth section read.
  slots: Vec<u32>,
}

/// Device encodings of a backend's population plans, built once. Only the
/// members of selected device circuits are encoded; a circuit is filled on
/// the device only when all of its members can be.
pub(super) struct DevicePlans {
  programs: Vec<Option<Program>>,
  constants: Vec<u64>,
  /// Lookup slots in order: callee functions and ROM widths.
  callees: Vec<Source>,
  pub(super) circuits: Vec<bool>,
  /// Per function: why its plan cannot be encoded, with details such as the
  /// hint channel or map name; empty when it can.
  causes: Vec<Vec<(HostCause, String)>>,
  /// Per function circuit: whether `AIUR_GPU_TRACE_CIRCUITS` admits it.
  selected: Vec<bool>,
  /// Compiled writers bound by `AIUR_GPU_TRACE=compiled`.
  compiled: Option<Arc<super::compiled::Selection>>,
  /// Per function circuit: its members' arena-read sites, as (function,
  /// instruction).
  arena_sites: Vec<Vec<(usize, usize)>>,
}

fn map_kind(name: &str) -> Option<u32> {
  crate::trace::DEVICE_MAPS.iter().position(|&m| m == name).map(|i| i as u32)
}

fn hint_kind(channel: &str) -> Option<u32> {
  crate::trace::DEVICE_HINTS.iter().position(|&h| h == channel).map(|i| i as u32)
}

/// The device kind of a hint step: a word hint, or an arena read for a
/// channel keyed by two fields with field outputs, which a record can bind
/// to [`DeviceArenas`].
fn step_hint_kind(action: &Action) -> Option<u32> {
  let Action::Hint { channel, key_type, r#type, .. } = action else {
    return None;
  };
  hint_kind(channel).or_else(|| {
    let fields = |ty: &Type, n: Option<usize>| match ty {
      Type::Tuple { items } => {
        n.is_none_or(|n| items.len() == n)
          && items.iter().all(|t| *t == Type::Field)
      },
      _ => false,
    };
    (fields(key_type, Some(2))
      && (*r#type == Type::Field || fields(r#type, None)))
    .then_some(HINT_ARENA_READ)
  })
}

/// The instructions of function `f`'s arena-read hint sites.
fn arena_sites<B: WitnessField>(
  backend: &Backend<'_, '_, B>,
  f: usize,
) -> Vec<usize> {
  let mut sites: Vec<usize> = backend.plan.artifact.functions[f]
    .steps
    .iter()
    .filter_map(|step| match &step.action {
      Action::Hint { instruction, .. }
        if step_hint_kind(&step.action) == Some(HINT_ARENA_READ) =>
      {
        Some(*instruction)
      },
      _ => None,
    })
    .collect();
  sites.sort_unstable();
  sites.dedup();
  sites
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
) -> (Vec<Option<Program>>, Constants, Vec<Source>) {
  let plan = &*backend.plan;
  let program = plan.program.program();
  let functions = program.functions.len();
  let mut constants = Constants::default();
  let table = std::cell::RefCell::new((Vec::new(), FxHashMap::default()));
  let used = std::cell::RefCell::new(Vec::new());
  let slot = |source: Source| {
    let (callees, slots) = &mut *table.borrow_mut();
    let next = u32::try_from(callees.len()).ok()?;
    let slot = *slots.entry(source).or_insert_with(|| {
      callees.push(source);
      next
    });
    used.borrow_mut().push(slot);
    Some(slot)
  };
  let programs = plan
    .fills
    .iter()
    .enumerate()
    .map(|(f, fill)| {
      if !include(f) {
        return None;
      }
      used.borrow_mut().clear();
      let chip = plan.members[f];
      let placement = &backend.placements[chip];
      let steps = &plan.artifact.functions[f].steps;
      let mut call = |callable: usize| {
        if callable >= functions {
          map_kind(&program.maps.get(callable - functions)?.name)
            .map(Target::Map)
        } else {
          slot(Source::Function(callable)).map(Target::Call)
        }
      };
      let mut hint = |instruction: usize| {
        steps.iter().find_map(|step| match &step.action {
          Action::Hint { instruction: i, .. } if *i == instruction => {
            step_hint_kind(&step.action)
          },
          _ => None,
        })
      };
      let mut rom = |width: usize| slot(Source::Rom(width));
      let column = |c: usize| placement.columns[c];
      let Encoded { mut code, scratch, inputs, outputs } =
        fill.encode(&mut call, &mut hint, &mut rom, &column, &mut constants)?;
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
      let mut slots = used.borrow().clone();
      slots.sort_unstable();
      slots.dedup();
      Some(Program { code, scratch, inputs, outputs, slots })
    })
    .collect();
  (programs, constants, table.into_inner().0)
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
/// slots.
#[cfg(test)]
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
      Action::Hint { channel, .. }
        if step_hint_kind(&step.action).is_none() =>
      {
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
  /// gives compiled writers (which need no scratch) only minimal workspaces,
  /// and gives an interpreted call the smallest pooled workspace that holds
  /// its scratch, superseding a smaller one it cannot use
  /// ([`DeviceRecord::workspace`]). So at most one minimal workspace per
  /// concurrent call and one scratch workspace, of at most the widest
  /// interpreted circuit's size, per concurrent interpreted call exist.
  /// Only the `enabled` circuits are counted.
  pub(super) fn scratch_bytes(
    &self,
    members: &[Vec<usize>],
    enabled: &[bool],
  ) -> u64 {
    let workspaces: Vec<u64> = (0..enabled.len())
      .filter(|&ci| enabled[ci])
      .map(|ci| workspace_bytes(self.scratch_words(ci, members)))
      .collect();
    pooled_scratch(&workspaces)
  }

  /// The function circuits the device populates for `record`: the device
  /// circuits its planner admitted.
  pub(super) fn enabled<B: WitnessField>(
    &self,
    record: &Execution<B>,
  ) -> Vec<bool> {
    let arenas = self.record_arenas(record);
    (0..self.circuits.len())
      .map(|ci| {
        self.circuits[ci]
          && record.host_population.admits(ci)
          && self.reads_arenas(record, arenas.as_ref(), ci)
      })
      .collect()
  }

  /// The advice arenas `record` binds to its arena-read sites: those of the
  /// first site that has any.
  pub(super) fn record_arenas<B: WitnessField>(
    &self,
    record: &Execution<B>,
  ) -> Option<Arc<dyn DeviceArenas>> {
    self.arena_sites.iter().flatten().find_map(|&(f, i)| {
      record.hints.sites.get(f)?.get(i)?.as_ref()?.arenas.clone()
    })
  }

  /// Whether every arena-read site of circuit `ci` reads `arenas` in
  /// `record` ([`Self::record_arenas`]).
  fn reads_arenas<B: WitnessField>(
    &self,
    record: &Execution<B>,
    arenas: Option<&Arc<dyn DeviceArenas>>,
    ci: usize,
  ) -> bool {
    self.arena_sites.get(ci).is_none_or(|sites| {
      sites.iter().all(|&(f, i)| {
        let site = record.hints.sites.get(f).and_then(|s| s.get(i)?.as_ref());
        match (site.and_then(|s| s.arenas.as_ref()), arenas) {
          (Some(site), Some(arenas)) => site.identity() == arenas.identity(),
          _ => false,
        }
      })
    })
  }

  /// Whether the device can populate circuit `ci` for `record`: it is a
  /// device circuit and `record` binds its arena reads to device data.
  pub(super) fn supports<B: WitnessField>(
    &self,
    record: &Execution<B>,
    ci: usize,
  ) -> bool {
    self.circuits.get(ci).copied().unwrap_or(false)
      && self.reads_arenas(record, self.record_arenas(record).as_ref(), ci)
  }

  /// Whether circuit `ci` reads advice arenas.
  fn uses_arenas(&self, ci: usize) -> bool {
    self.arena_sites.get(ci).is_some_and(|sites| !sites.is_empty())
  }

  /// The advice arenas the `enabled` circuits read, if any do.
  fn arenas_for<B: WitnessField>(
    &self,
    record: &Execution<B>,
    enabled: &[bool],
  ) -> Option<Arc<dyn DeviceArenas>> {
    (0..enabled.len())
      .any(|ci| enabled[ci] && self.uses_arenas(ci))
      .then(|| self.record_arenas(record))
      .flatten()
  }

  /// The lookup slots function circuit `ci` reads: its compiled writer's,
  /// or its members' encoded plans'.
  fn slots_of(&self, ci: usize, members: &[Vec<usize>]) -> Vec<u32> {
    if let Some(slots) = self.compiled.as_ref().and_then(|c| c.slots(ci)) {
      return slots.to_vec();
    }
    members[ci]
      .iter()
      .filter_map(|&f| self.programs[f].as_ref())
      .flat_map(|p| p.slots.iter().copied())
      .collect()
  }

  /// Every table the `enabled` circuits read: their members' queries and
  /// their lookup slots' tables.
  fn sources_read<B: WitnessField>(
    &self,
    backend: &Backend<'_, '_, B>,
    enabled: &[bool],
  ) -> rustc_hash::FxHashSet<Source> {
    let mut read = rustc_hash::FxHashSet::default();
    for ci in (0..enabled.len()).filter(|&ci| enabled[ci]) {
      read.extend(backend.members[ci].iter().map(|&f| Source::Function(f)));
      read.extend(
        self
          .slots_of(ci, &backend.members)
          .into_iter()
          .map(|slot| self.callees[slot as usize]),
      );
    }
    read
  }

  /// The device bytes of `record`'s population as a function of the
  /// admitted circuits, as [`Self::record_bytes`] computes them.
  pub(super) fn record_model<B: WitnessField>(
    &self,
    backend: &Backend<'_, '_, B>,
    record: &Execution<B>,
  ) -> Result<RecordModel, String> {
    let tables = &record.queries.tables;
    let code: u128 =
      self.programs.iter().flatten().map(|p| p.code.len() as u128).sum();
    let mut fixed = allocated(code * 4)
      + allocated(self.constants.len() as u128 * 8)
      + allocated(
        self.callees.len() as u128 * std::mem::size_of::<AiurCallee>() as u128,
      );
    let mut sources: Vec<Source> = self.callees.clone();
    for (ci, &on) in self.circuits.iter().enumerate() {
      if on {
        sources
          .extend(backend.members[ci].iter().map(|&f| Source::Function(f)));
      }
    }
    sources.sort_unstable_by_key(|&source| match source {
      Source::Function(f) => (0, f),
      Source::Rom(width) => (1, width),
    });
    sources.dedup();
    let index: FxHashMap<Source, usize> =
      sources.iter().enumerate().map(|(i, &s)| (s, i)).collect();
    let mut empty = vec![0u128; sources.len()];
    let mut full = vec![0u128; sources.len()];
    let mut always = vec![false; sources.len()];
    for (i, &source) in sources.iter().enumerate() {
      let (count, stride, depths) = match source {
        Source::Function(f) => {
          let (inputs, outputs) = tables[f].widths();
          (tables[f].len(), inputs + outputs, tables[f].depths_len() != 0)
        },
        Source::Rom(width) => {
          (record.memory.width_cells(width).len(), width, false)
        },
      };
      let table = |count: usize| {
        allocated((count as u128 * stride as u128).max(1) * 8)
          + allocated(count.max(1) as u128 * 8) * (1 + u128::from(depths))
      };
      empty[i] = table(0);
      full[i] = table(count);
      let lookups = self.callees.iter().filter(|&&c| c == source).count();
      empty[i] +=
        lookups as u128 * allocated(Image::index_slots(0)? as u128 * 4);
      full[i] +=
        lookups as u128 * allocated(Image::index_slots(count)? as u128 * 4);
      always[i] = lookups != 0;
    }
    for i in (0..sources.len()).filter(|&i| always[i]) {
      fixed += empty[i];
      full[i] -= empty[i];
    }
    let circuits = (0..self.circuits.len())
      .map(|ci| {
        if !self.circuits[ci] {
          return CircuitModel {
            read: vec![],
            members: 0,
            workspace: 0,
            arenas: false,
          };
        }
        let mut read: Vec<usize> = backend.members[ci]
          .iter()
          .map(|&f| index[&Source::Function(f)])
          .chain(
            self
              .slots_of(ci, &backend.members)
              .into_iter()
              .map(|slot| index[&self.callees[slot as usize]]),
          )
          .collect();
        read.sort_unstable();
        read.dedup();
        CircuitModel {
          read,
          members: allocated(
            (backend.members[ci].len() * std::mem::size_of::<AiurFunction>())
              as u128,
          ),
          workspace: workspace_bytes(self.scratch_words(ci, &backend.members)),
          arenas: self.uses_arenas(ci),
        }
      })
      .collect();
    let arenas = self
      .record_arenas(record)
      .map_or(0, |arenas| arena_bytes(&arenas.arenas()));
    Ok(RecordModel { fixed, full, circuits, shards: None, arenas })
  }

  /// [`Self::record_model`] for proving `record` with `layout`: when its
  /// device record is uploaded one shard image at a time
  /// ([`DeviceRecord::upload_sharded`]), the largest image's bound.
  pub(super) fn record_model_for<B: WitnessField>(
    &self,
    backend: &Backend<'_, '_, B>,
    record: &Execution<B>,
    layout: &BatchLayout,
  ) -> Result<RecordModel, String> {
    let mut model = self.record_model(backend, record)?;
    let image = Image::of(backend, self, record, &self.circuits)?;
    let Ok(sharding) = Sharding::new(&image, backend, record) else {
      return Ok(model);
    };
    let tables = &record.queries.tables;
    let count = |shard: &ShardLayout, ci: usize| -> Vec<(usize, usize)> {
      let (Some(circuit), Some(slice)) =
        (&image.circuits[ci], shard.circuits.get(ci))
      else {
        return vec![];
      };
      let mut rows: FxHashMap<usize, usize> = FxHashMap::default();
      for m in &circuit.members {
        let Source::Function(f) = image.tables[m.table].source else {
          continue;
        };
        let first = m.first as usize;
        let lo = slice.first.max(first);
        let hi = (slice.first + slice.rows).min(first + tables[f].len());
        if lo >= hi {
          continue;
        }
        *rows.entry(m.table).or_default() += hi - lo;
        let Some(refs) = tables[f].refs.as_ref() else { continue };
        let (lo, hi) = (lo - first, hi - first);
        let blocks =
          lo >> crate::refs::BLOCK_SHIFT..((hi - 1) >> crate::refs::BLOCK_SHIFT) + 1;
        sharding.each_ref(refs, f, blocks, |site, _| {
          if let Some(Some(table)) = sharding.targets[f].get(site) {
            *rows.entry(*table).or_default() += 1;
          }
          // Each alias holds at most one row of a key.
          if let Some(Some((_, aliases))) = sharding.aliases[f].get(site) {
            for &(_, table) in aliases {
              *rows.entry(table).or_default() += 1;
            }
          }
        });
      }
      let mut rows: Vec<(usize, usize)> = rows.into_iter().collect();
      rows.sort_unstable();
      rows
    };
    let circuits = image.circuits.len();
    let per_shard = |shard: &ShardLayout| -> Vec<Vec<(usize, usize)>> {
      (0..circuits).map(|ci| count(shard, ci)).collect()
    };
    #[cfg(feature = "parallel")]
    let rows = layout.shards.par_iter().map(per_shard).collect();
    #[cfg(not(feature = "parallel"))]
    let rows = layout.shards.iter().map(per_shard).collect();
    model.shards = Some(ShardModel { image, rows });
    Ok(model)
  }

  /// Per shard of `layout`, with every device circuit admitted: the image
  /// bound planning charges ([`Self::record_model_for`]), the image the
  /// gather builds, and the gather's seconds; and the whole record's
  /// device bytes. `None` when the record has no usable references.
  pub(super) fn shard_image_sizes<B: WitnessField>(
    &self,
    backend: &Backend<'_, '_, B>,
    record: &Execution<B>,
    layout: &BatchLayout,
  ) -> Result<Option<(Vec<(u64, u64, f64)>, u64)>, String> {
    let model = self.record_model_for(backend, record, layout)?;
    let Some(shards) = &model.shards else { return Ok(None) };
    let image = &shards.image;
    let sharding = Sharding::new(image, backend, record)?;
    let sizes = layout
      .shards
      .iter()
      .enumerate()
      .map(|(s, shard)| {
        let rows = image.shard_rows(&sharding, record, shard, |_| true)?;
        let bound = u64::try_from(shards.shard_bytes(s, &self.circuits))
          .unwrap_or(u64::MAX);
        Ok((bound, rows.bytes, rows.seconds))
      })
      .collect::<Result<_, String>>()?;
    Ok(Some((sizes, image.bytes()?)))
  }

  /// [`Self::record_bytes`] for proving `record` with `layout`, as
  /// [`Self::record_model_for`] bounds it.
  pub(super) fn record_bytes_for<B: WitnessField>(
    &self,
    backend: &Backend<'_, '_, B>,
    record: &Execution<B>,
    layout: &BatchLayout,
  ) -> Result<u64, String> {
    let model = self.record_model_for(backend, record, layout)?;
    if model.shards.is_none() {
      return self.record_bytes(backend, record);
    }
    Ok(model.bytes(&self.enabled(record)))
  }

  /// Device bytes population holds for `record`: the uploaded record and
  /// the launch workspaces of the circuits its planner admitted.
  pub(super) fn record_bytes<B: WitnessField>(
    &self,
    backend: &Backend<'_, '_, B>,
    record: &Execution<B>,
  ) -> Result<u64, String> {
    let enabled = self.enabled(record);
    let scratch = self.scratch_bytes(&backend.members, &enabled);
    let upload = Image::new(backend, self, record)?.bytes()?;
    let arenas = u64::try_from(
      self.arenas_for(record, &enabled).map_or(0, |a| arena_bytes(&a.arenas())),
    )
    .unwrap_or(u64::MAX);
    Ok(upload.saturating_add(scratch).saturating_add(arenas))
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
      return if self.selected[ci] && self.compiled.is_some() {
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
  /// `compiled+generated` when a compiled bundle is registered and lookups
  /// run on the device, and host population otherwise: the interpreter
  /// fills the circuits a bundle skips instead of the host.
  pub(super) fn from_env<B: WitnessField>(
    backend: &Backend<'_, '_, B>,
  ) -> Result<Option<Self>, String> {
    let mode = match std::env::var("AIUR_GPU_TRACE") {
      Err(std::env::VarError::NotPresent)
        if backend.gpu_lookup_only && super::compiled::registered() =>
      {
        Ok("compiled+generated".to_owned())
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
    let arena_sites = backend
      .members
      .iter()
      .map(|members| {
        members
          .iter()
          .flat_map(|&f| arena_sites(backend, f).into_iter().map(move |i| (f, i)))
          .collect()
      })
      .collect();
    Ok(Self {
      programs,
      constants: constants.values,
      callees,
      circuits,
      causes,
      selected,
      compiled: None,
      arena_sites,
    })
  }

  pub(super) fn compiled(&self) -> Option<&super::compiled::Selection> {
    self.compiled.as_deref()
  }

  /// One line naming how many function circuits population fills on the
  /// device, how many of those by compiled writers, and why the others stay
  /// on the host: circuits per combination of causes, most common first.
  pub(super) fn summary<B: WitnessField>(
    &self,
    backend: &Backend<'_, '_, B>,
  ) -> String {
    let device = self.circuits.iter().filter(|&&on| on).count();
    let compiled = self.compiled.as_deref().map_or_else(
      || "no compiled bundle".to_owned(),
      |selection| {
        format!(
          "{} by compiled writers (bundle {})",
          selection.bound(),
          selection.tag()
        )
      },
    );
    let mut reasons: std::collections::BTreeMap<String, usize> =
      std::collections::BTreeMap::new();
    for ci in (0..self.circuits.len()).filter(|&ci| !self.circuits[ci]) {
      let (causes, _) = self.host_cause(backend, ci);
      let causes: Vec<String> =
        causes.iter().map(|c| format!("{c:?}")).collect();
      *reasons.entry(causes.join("+")).or_default() += 1;
    }
    let mut reasons: Vec<_> = reasons.into_iter().collect();
    reasons.sort_by(|a, b| b.1.cmp(&a.1));
    let reasons: Vec<String> = reasons
      .iter()
      .map(|(causes, count)| format!("{count} {causes}"))
      .collect();
    format!(
      "{device} of {} function circuits populated on the device, {compiled}; on the host: {}",
      self.circuits.len(),
      if reasons.is_empty() { "none".to_owned() } else { reasons.join("; ") }
    )
  }
}

/// [`DevicePlans::record_model`]: the bytes an upload holds whatever is
/// admitted, and what each table and circuit adds.
pub(super) struct RecordModel {
  fixed: u128,
  /// Per table: its bytes when some admitted circuit reads it, beyond what
  /// `fixed` already holds for it.
  full: Vec<u128>,
  circuits: Vec<CircuitModel>,
  /// For a record uploaded one shard image at a time, the images' bounds,
  /// which replace the whole record's tables.
  shards: Option<ShardModel>,
  /// The record's advice arenas, held once whenever an admitted circuit
  /// reads them.
  arenas: u128,
}

/// Bounds on the shard images of one layout ([`ShardRows`]).
struct ShardModel {
  image: Image,
  /// Per shard, per device circuit: the rows of each table its rows read,
  /// counted once per member row and reference (so at least the rows its
  /// image holds).
  rows: Vec<Vec<Vec<(usize, usize)>>>,
}

impl ShardModel {
  /// The device bytes of the two largest shard images when the `admitted`
  /// circuits are populated: the next shard's image is uploaded while the
  /// current one proves ([`DeviceRecord::prefetch`]).
  fn bytes(&self, admitted: &[bool]) -> u128 {
    let mut largest = [0u128; 2];
    for shard in 0..self.rows.len() {
      let bytes = self.shard_bytes(shard, admitted);
      if bytes > largest[0] {
        largest = [bytes, largest[0]];
      } else if bytes > largest[1] {
        largest[1] = bytes;
      }
    }
    largest[0] + largest[1]
  }

  /// The bound on shard `shard`'s image when the `admitted` circuits are
  /// populated.
  fn shard_bytes(&self, shard: usize, admitted: &[bool]) -> u128 {
    let mut counts = vec![0usize; self.image.tables.len()];
    for (ci, rows) in self.rows[shard].iter().enumerate() {
      if admitted.get(ci).copied().unwrap_or(false) {
        for &(table, n) in rows {
          counts[table] += n;
        }
      }
    }
    u128::from(self.image.bytes_with(&counts, true).unwrap_or(u64::MAX))
  }
}

struct CircuitModel {
  /// Indices into [`RecordModel::full`].
  read: Vec<usize>,
  /// Its member descriptors.
  members: u128,
  /// One launch workspace.
  workspace: u64,
  /// Whether it reads the record's advice arenas.
  arenas: bool,
}

impl RecordModel {
  /// [`DevicePlans::record_bytes`] when exactly the `admitted` device
  /// circuits are populated.
  pub(super) fn bytes(&self, admitted: &[bool]) -> u64 {
    let arenas = if self
      .circuits
      .iter()
      .zip(admitted)
      .any(|(c, on)| *on && c.arenas)
    {
      self.arenas
    } else {
      0
    };
    if let Some(shards) = &self.shards {
      let workspaces: Vec<u64> = self
        .circuits
        .iter()
        .zip(admitted)
        .filter(|(_, on)| **on)
        .map(|(c, _)| c.workspace)
        .collect();
      return u64::try_from(shards.bytes(admitted) + arenas)
        .unwrap_or(u64::MAX)
        .saturating_add(pooled_scratch(&workspaces));
    }
    let mut read = vec![false; self.full.len()];
    let mut upload = self.fixed + arenas;
    let mut workspaces = vec![];
    for (circuit, _) in
      self.circuits.iter().zip(admitted).filter(|(_, on)| **on)
    {
      for &table in &circuit.read {
        if !std::mem::replace(&mut read[table], true) {
          upload += self.full[table];
        }
      }
      upload += circuit.members;
      workspaces.push(circuit.workspace);
    }
    u64::try_from(upload)
      .unwrap_or(u64::MAX)
      .saturating_add(pooled_scratch(&workspaces))
  }

  /// The bytes admitting circuit `ci` alone adds to an empty upload.
  pub(super) fn alone(&self, ci: usize) -> u64 {
    let circuit = &self.circuits[ci];
    let arenas = if circuit.arenas { self.arenas } else { 0 };
    if let Some(shards) = &self.shards {
      let mut admitted = vec![false; self.circuits.len()];
      admitted[ci] = true;
      return u64::try_from(shards.bytes(&admitted) + arenas)
        .unwrap_or(u64::MAX)
        .saturating_add(pooled_scratch(&[circuit.workspace]));
    }
    let tables: u128 = circuit.read.iter().map(|&t| self.full[t]).sum();
    u64::try_from(tables + circuit.members + arenas)
      .unwrap_or(u64::MAX)
      .saturating_add(pooled_scratch(&[circuit.workspace]))
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

/// An uploaded lookup table: a function's recorded queries, or the ROM
/// cells of one width in address order.
#[derive(Clone, Copy)]
struct TableImage {
  source: Source,
  count: usize,
  /// Words per row: inputs, then outputs (a ROM cell's words).
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
  /// Lookup slots in order: table index, inputs, outputs.
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
    Self::of(backend, plans, record, &plans.enabled(record))
  }

  /// The image of the `enabled` device circuits.
  fn of<B: WitnessField>(
    backend: &Backend<'_, '_, B>,
    plans: &DevicePlans,
    record: &Execution<B>,
    enabled: &[bool],
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
    let read = plans.sources_read(backend, enabled);
    let mut needed: Vec<Source> = plans.callees.clone();
    needed.extend(read.iter().copied());
    needed.sort_unstable_by_key(|&source| match source {
      Source::Function(f) => (0, f),
      Source::Rom(width) => (1, width),
    });
    needed.dedup();
    let table_of: FxHashMap<Source, usize> =
      needed.iter().enumerate().map(|(i, &s)| (s, i)).collect();
    // Slots no enabled circuit reads keep their position with no rows.
    let uploaded = needed
      .iter()
      .map(|&source| match source {
        Source::Function(f) => {
          let (inputs, outputs) = tables[f].widths();
          let count = if read.contains(&source) { tables[f].len() } else { 0 };
          let depths = tables[f].depths_len() != 0;
          if depths && tables[f].depths_len() < count {
            return Err("query record is missing depth heights".to_owned());
          }
          Ok(TableImage { source, count, stride: inputs + outputs, depths })
        },
        Source::Rom(width) => Ok(TableImage {
          source,
          count: if read.contains(&source) {
            record.memory.width_cells(width).len()
          } else {
            0
          },
          stride: width,
          depths: false,
        }),
      })
      .collect::<Result<_, String>>()?;
    let callees = plans
      .callees
      .iter()
      .map(|&source| {
        let (inputs, outputs) = match source {
          Source::Function(f) => tables[f].widths(),
          Source::Rom(width) => (width, 0),
        };
        Ok((
          table_of[&source],
          u32::try_from(inputs).map_err(|_| "callee width overflow")?,
          u32::try_from(outputs).map_err(|_| "callee width overflow")?,
        ))
      })
      .collect::<Result<_, String>>()?;
    let count = backend.system.circuits.len();
    let mut circuits: Vec<Option<CircuitImage>> =
      (0..count).map(|_| None).collect();
    let mut heights = vec![0; count];
    for (ci, &on) in enabled.iter().enumerate() {
      if !on {
        continue;
      }
      let mut members = vec![];
      let mut first = 0u64;
      let mut scratch = 0;
      for &f in &backend.members[ci] {
        let program = plans.programs[f].as_ref().expect("encoded member");
        members.push(MemberImage {
          table: table_of[&Source::Function(f)],
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
    let counts: Vec<usize> = self.tables.iter().map(|t| t.count).collect();
    self.bytes_with(&counts, false)
  }

  /// Device bytes [`Self::upload_rows`] allocates for tables of `counts`
  /// rows, with ROM ids for a shard image.
  fn bytes_with(&self, counts: &[usize], shard: bool) -> Result<u64, String> {
    let mut bytes = allocated(self.code.len() as u128 * 4)
      + allocated(self.constants.len() as u128 * 8);
    for (table, &count) in self.tables.iter().zip(counts) {
      bytes += allocated((count as u128 * table.stride as u128).max(1) * 8);
      bytes += allocated(count.max(1) as u128 * 8);
      if table.depths {
        bytes += allocated(count.max(1) as u128 * 8);
      }
      if shard && matches!(table.source, Source::Rom(_)) {
        bytes += allocated(count.max(1) as u128 * 8);
      }
    }
    for &(table, _, _) in &self.callees {
      bytes += allocated(Self::index_slots(counts[table])? as u128 * 4);
    }
    bytes += allocated(
      self.callees.len() as u128 * std::mem::size_of::<AiurCallee>() as u128,
    );
    for circuit in self.circuits.iter().flatten() {
      bytes += allocated(
        (circuit.members.len() * std::mem::size_of::<AiurFunction>()) as u128,
      );
    }
    u64::try_from(bytes).map_err(|_| "device record size overflow".into())
  }

  /// Allocates the record on `device`, filling each query table's rows,
  /// multiplicities and heights with `fill`.
  fn upload(
    &self,
    device: i32,
    fill: impl FnMut(usize, &TableBuffers) -> Result<(), String>,
  ) -> Result<Resident, String> {
    let counts: Vec<usize> = self.tables.iter().map(|t| t.count).collect();
    self.upload_rows(device, &counts, None, fill)
  }

  /// Allocates `counts[i]` rows of each table `i` on `device`, filled by
  /// `fill`. With `shard`, those are the rows its ids list, and members
  /// index them through its offsets; without, every row of the table.
  fn upload_rows(
    &self,
    device: i32,
    counts: &[usize],
    shard: Option<&ShardRows>,
    mut fill: impl FnMut(usize, &TableBuffers) -> Result<(), String>,
  ) -> Result<Resident, String> {
    let code = Buffer::upload(device, &self.code)?;
    let constants = Buffer::upload(device, &self.constants)?;
    let mut tables = vec![];
    for (i, table) in self.tables.iter().enumerate() {
      let count = counts[i];
      let words = count.checked_mul(table.stride).ok_or("table size overflow")?;
      let buffers = TableBuffers {
        rows: Buffer::new(device, words.max(1) * 8)?,
        multiplicities: Buffer::new(device, count.max(1) * 8)?,
        depths: table
          .depths
          .then(|| Buffer::new(device, count.max(1) * 8))
          .transpose()?,
        ids: match (shard, table.source) {
          (Some(shard), Source::Rom(_)) => {
            let ids: Vec<u64> =
              shard.ids[i].iter().map(|&id| u64::from(id)).collect();
            Some(Buffer::upload(device, &ids)?)
          },
          _ => None,
        },
      };
      fill(i, &buffers)?;
      tables.push(buffers);
    }
    let mut indexes = vec![];
    let mut callees = vec![];
    for &(table, inputs, outputs) in &self.callees {
      let TableImage { stride, .. } = self.tables[table];
      let count = counts[table];
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
        ids: buffers.ids.as_ref().map_or(std::ptr::null(), |b| b.as_ptr()),
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
      .enumerate()
      .map(|(ci, circuit)| {
        let Some(circuit) = circuit else { return Ok(None) };
        let members: Vec<_> = circuit
          .members
          .iter()
          .enumerate()
          .map(|(member, m)| {
            let TableImage { stride, .. } = self.tables[m.table];
            let count = counts[m.table];
            let offset = shard
              .and_then(|s| s.offsets.get(ci)?.get(member).copied())
              .unwrap_or(0);
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
              offset,
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

/// The rows of each record table that one trace shard's device rows read:
/// their own queries, and the callee rows and ROM cells their recorded
/// references ([`crate::refs`]) name. A shard image uploads only these,
/// and the device looks callees up among them.
pub(super) struct ShardRows {
  /// Per [`Image::tables`] entry: its query rows or ROM addresses,
  /// ascending.
  ids: Vec<Vec<u32>>,
  /// Per circuit, per member: the offset from a query to its row among its
  /// table's ids.
  offsets: Vec<Vec<u64>>,
  /// Device bytes of the image.
  bytes: u64,
  /// Host seconds the gather took.
  pub(super) seconds: f64,
}

impl ShardRows {
  fn counts(&self) -> Vec<usize> {
    self.ids.iter().map(Vec::len).collect()
  }
}

/// What gathering shard images needs beyond the [`Image`].
struct Sharding {
  /// Per function: the [`Image::tables`] entry of each of its reference
  /// targets, if the image holds it.
  targets: Vec<Vec<Option<usize>>>,
  /// Per function: the bits of its references that hold the row.
  row_bits: Vec<u32>,
  /// Per function, per reference target: when it is a function `g` with
  /// aliases ([`crate::refs::FunctionRefs::aliases`]), `g` and each alias
  /// with its table, whose rows with the key of a referenced row of `g` a
  /// depth slot may read instead.
  aliases: Vec<Vec<Option<(usize, Vec<(usize, usize)>)>>>,
}

impl Sharding {
  /// How `image`'s shard images are gathered from `record`'s references, or
  /// why they cannot be: a device circuit member's references are missing.
  fn new<B: WitnessField>(
    image: &Image,
    backend: &Backend<'_, '_, B>,
    record: &Execution<B>,
  ) -> Result<Self, String> {
    let plan = backend
      .plan
      .program
      .ref_plan()
      .ok_or("execution recorded no row references")?;
    let tables = &record.queries.tables;
    let name = |f: usize| &backend.plan.artifact.functions[f].name;
    for circuit in image.circuits.iter().flatten() {
      for m in &circuit.members {
        let Source::Function(f) = image.tables[m.table].source else {
          return Err("a device circuit member is not a function".into());
        };
        if plan.functions.get(f).is_none_or(Option::is_none) {
          return Err(format!("{} records no references", name(f)));
        }
        match &tables[f].refs {
          Some(refs) if refs.overflowed() => {
            return Err(format!("{}'s references overflowed", name(f)));
          },
          Some(refs) if refs.is_compact() => {},
          _ => return Err(format!("{} has no compact references", name(f))),
        }
      }
    }
    let table_of: FxHashMap<Source, usize> =
      image.tables.iter().enumerate().map(|(i, t)| (t.source, i)).collect();
    let mut targets = vec![];
    let mut row_bits = vec![];
    let mut aliases = vec![];
    for function in &plan.functions {
      let Some(refs) = function else {
        targets.push(vec![]);
        row_bits.push(0);
        aliases.push(vec![]);
        continue;
      };
      aliases.push(
        refs
          .aliases
          .iter()
          .zip(&refs.targets)
          .map(|(functions, &target)| {
            let crate::refs::Target::Function(g) = target else { return None };
            let tables: Vec<(usize, usize)> = functions
              .iter()
              .filter_map(|&a| Some((a, *table_of.get(&Source::Function(a))?)))
              .collect();
            (!tables.is_empty()).then_some((g, tables))
          })
          .collect(),
      );
      targets.push(
        refs
          .targets
          .iter()
          .map(|&target| {
            let source = match target {
              crate::refs::Target::Function(g) => Source::Function(g),
              crate::refs::Target::Rom(width) => Source::Rom(width),
            };
            table_of.get(&source).copied()
          })
          .collect(),
      );
      row_bits.push(refs.row_bits);
    }
    Ok(Self { targets, row_bits, aliases })
  }
}

impl Sharding {
  /// Visits each reference, as (target index, row or address), that
  /// function `f`'s rows of blocks `blocks` recorded in `refs`.
  fn each_ref(
    &self,
    refs: &crate::refs::TableRefs,
    f: usize,
    blocks: std::ops::Range<usize>,
    mut visit: impl FnMut(usize, usize),
  ) {
    let bits = self.row_bits[f];
    let mask = ((1u64 << bits) - 1) as u32;
    let rows = blocks.start << crate::refs::BLOCK_SHIFT
      ..blocks.end << crate::refs::BLOCK_SHIFT;
    for &reference in refs.block_refs(blocks) {
      visit((reference >> bits) as usize, (reference & mask) as usize);
    }
    for (site, value) in refs.wide_refs(rows) {
      visit(site, value);
    }
  }
}

/// A bitmap of a table's rows that threads mark concurrently.
struct Marks(Vec<std::sync::atomic::AtomicU64>);

impl Marks {
  fn new(rows: usize) -> Self {
    Self(
      (0..rows.div_ceil(64))
        .map(|_| std::sync::atomic::AtomicU64::new(0))
        .collect(),
    )
  }
  #[inline]
  fn set(&self, row: usize) {
    if let Some(word) = self.0.get(row / 64) {
      word.fetch_or(1 << (row % 64), std::sync::atomic::Ordering::Relaxed);
    }
  }
  fn set_range(&self, rows: std::ops::Range<usize>) {
    let mut row = rows.start;
    while row < rows.end {
      let bit = row % 64;
      let take = (64 - bit).min(rows.end - row);
      let mask = if take == 64 { u64::MAX } else { ((1u64 << take) - 1) << bit };
      if let Some(word) = self.0.get(row / 64) {
        word.fetch_or(mask, std::sync::atomic::Ordering::Relaxed);
      }
      row += take;
    }
  }
  fn ids(&self) -> Vec<u32> {
    let mut ids = vec![];
    for (w, word) in self.0.iter().enumerate() {
      let mut bits = word.load(std::sync::atomic::Ordering::Relaxed);
      while bits != 0 {
        ids.push((w * 64) as u32 + bits.trailing_zeros());
        bits &= bits - 1;
      }
    }
    ids
  }
}

impl Image {
  /// The shard image of the rows `shard` gives the circuits `include`
  /// admits, from `record`'s compacted references.
  fn shard_rows<B: WitnessField>(
    &self,
    sharding: &Sharding,
    record: &Execution<B>,
    shard: &ShardLayout,
    include: impl Fn(usize) -> bool + Sync,
  ) -> Result<ShardRows, String> {
    let start = std::time::Instant::now();
    let tables = &record.queries.tables;
    let marks: Vec<Marks> = self
      .tables
      .iter()
      .map(|t| match t.source {
        Source::Function(f) => Marks::new(tables[f].len()),
        Source::Rom(width) => {
          Marks::new(record.memory.width_cells(width).len())
        },
      })
      .collect();
    // Work items: a member's own rows, and runs of blocks of its references.
    const RUN: usize = 64;
    let mut work = vec![];
    for (ci, circuit) in self.circuits.iter().enumerate() {
      let (Some(circuit), Some(slice)) = (circuit, shard.circuits.get(ci))
      else {
        continue;
      };
      if slice.rows == 0 || !include(ci) {
        continue;
      }
      for m in &circuit.members {
        let Source::Function(f) = self.tables[m.table].source else {
          return Err("device circuit member is not a function".into());
        };
        let first = m.first as usize;
        let end = first + tables[f].len();
        let lo = slice.first.max(first);
        let hi = (slice.first + slice.rows).min(end);
        if lo >= hi {
          continue;
        }
        let (lo, hi) = (lo - first, hi - first);
        marks[m.table].set_range(lo..hi);
        let blocks = lo >> crate::refs::BLOCK_SHIFT
          ..((hi - 1) >> crate::refs::BLOCK_SHIFT) + 1;
        let mut b = blocks.start;
        while b < blocks.end {
          work.push((f, b..(b + RUN).min(blocks.end)));
          b += RUN;
        }
      }
    }
    let mark = |(f, blocks): &(usize, std::ops::Range<usize>)| {
      let Some(refs) = tables[*f].refs.as_ref().filter(|r| r.is_compact())
      else {
        return Err(format!("function {f} has no row references"));
      };
      let targets = &sharding.targets[*f];
      let aliases = &sharding.aliases[*f];
      let mut buffer = vec![];
      sharding.each_ref(refs, *f, blocks.clone(), |site, row| {
        if let Some(Some(table)) = targets.get(site) {
          marks[*table].set(row);
        }
        if let Some(Some((g, aliases))) = aliases.get(site) {
          let key = tables[*g].input_in(row, &mut buffer);
          for &(alias, table) in aliases {
            if let Some(found) = tables[alias].lookup(key).1 {
              marks[table].set(found);
            }
          }
        }
      });
      Ok(())
    };
    #[cfg(feature = "parallel")]
    work.par_iter().try_for_each(mark)?;
    #[cfg(not(feature = "parallel"))]
    work.iter().try_for_each(mark)?;
    #[cfg(feature = "parallel")]
    let ids: Vec<Vec<u32>> = marks.par_iter().map(Marks::ids).collect();
    #[cfg(not(feature = "parallel"))]
    let ids: Vec<Vec<u32>> = marks.iter().map(Marks::ids).collect();
    drop(marks);
    let offsets = self
      .circuits
      .iter()
      .enumerate()
      .map(|(ci, circuit)| {
        let (Some(circuit), Some(slice)) = (circuit, shard.circuits.get(ci))
        else {
          return vec![];
        };
        circuit
          .members
          .iter()
          .map(|m| {
            let lo = slice.first.saturating_sub(m.first as usize) as u32;
            let position = ids[m.table].partition_point(|&id| id < lo) as u32;
            u64::from(lo - position.min(lo))
          })
          .collect()
      })
      .collect();
    let counts: Vec<usize> = ids.iter().map(Vec::len).collect();
    let bytes = self.bytes_with(&counts, true)?;
    Ok(ShardRows {
      ids,
      offsets,
      bytes,
      seconds: start.elapsed().as_secs_f64(),
    })
  }
}

/// Fills a shard image's table `table` from `record`: the rows, counts,
/// heights of the queries or ROM cells `ids` lists, staged a buffer at a time.
fn fill_rows<B: WitnessField>(
  device: i32,
  record: &Execution<B>,
  table: TableImage,
  ids: &[u32],
  buffers: &TableBuffers,
  parallel: bool,
) -> Result<(), String> {
  let stride = table.stride;
  match table.source {
    Source::Function(f) => {
      let table = &record.queries.tables[f];
      if table.static_map.is_some() {
        return Err("GPU population cannot read a map's table".into());
      }
      if ids.iter().any(|&id| id as usize >= table.len()) {
        return Err("missing query row".into());
      }
      if table.widths().0 + table.widths().1 != stride {
        return Err("query table stride changed".into());
      }
      buffers.rows.write_gathered(ids.len(), stride, parallel, |i, out| {
        let row = ids[i] as usize;
        match table.stored(row) {
          Stored::Narrow(values) => {
            for (out, &value) in out.iter_mut().zip(values) {
              *out = u64::from(value);
            }
          },
          Stored::Wide(values) => out.copy_from_slice(&B::words(values)),
          Stored::Mixed => table.row_words(row, out),
        }
      })?;
      buffers.multiplicities.write_gathered(ids.len(), 1, parallel, |i, out| {
        out[0] = table.count(ids[i] as usize);
      })?;
      if let Some(depths) = &buffers.depths {
        if table.depths_len() < table.len() {
          return Err("query record is missing depth heights".into());
        }
        depths.write_gathered(ids.len(), 1, parallel, |i, out| {
          out[0] = table.depth(ids[i] as usize);
        })?;
      }
    },
    Source::Rom(width) => {
      let cells = record.memory.width_cells(width);
      if ids.iter().any(|&id| id as usize >= cells.len()) {
        return Err("missing ROM cell".into());
      }
      buffers.rows.write_gathered(ids.len(), stride, parallel, |i, out| {
        if let Some(entry) = cells.get(ids[i] as usize) {
          out.copy_from_slice(&B::words(entry.cell.value));
        }
      })?;
      buffers.multiplicities.write_gathered(ids.len(), 1, parallel, |i, out| {
        out[0] = cells.get(ids[i] as usize).map_or(0, |entry| entry.multiplicity);
      })?;
    },
  }
  // SAFETY: the buffer holds `ids.len() * stride` words.
  check(
    unsafe {
      aiur_gpu_canonicalize(
        device,
        buffers.rows.as_ptr(),
        (ids.len() * stride) as u64,
      )
    },
    "GPU population canonicalization",
  )
}

/// One uploaded query table: its rows, multiplicities and, when tracked,
/// recorded heights; in a shard image, a ROM table's addresses too.
struct TableBuffers {
  rows: Buffer,
  multiplicities: Buffer,
  depths: Option<Buffer>,
  ids: Option<Buffer>,
}

impl TableBuffers {
  fn depths_ptr(&self) -> *const u64 {
    self.depths.as_ref().map_or(std::ptr::null(), |d| d.as_ptr())
  }
}

/// A record's advice arenas on the device.
struct ArenaBuffers {
  /// One [`AiurArena`] per arena.
  descriptors: Buffer,
  count: u64,
  _data: Vec<Buffer>,
}

impl ArenaBuffers {
  fn upload(device: i32, arenas: &[ArenaData<'_>]) -> Result<Self, String> {
    let mut data = vec![];
    let mut descriptors = Vec::with_capacity(arenas.len());
    for arena in arenas {
      let mut descriptor = AiurArena {
        bytes: std::ptr::null(),
        words: std::ptr::null(),
        len: arena.len() as u64,
      };
      match arena {
        _ if arena.is_empty() => {},
        ArenaData::Bytes(bytes) => {
          let buffer = Buffer::upload(device, bytes)?;
          descriptor.bytes = buffer.as_ptr::<u8>();
          data.push(buffer);
        },
        ArenaData::Words(words) => {
          let buffer = Buffer::upload(device, words.as_ref())?;
          descriptor.words = buffer.as_ptr::<u64>();
          data.push(buffer);
        },
      }
      descriptors.push(descriptor);
    }
    Ok(Self {
      descriptors: Buffer::upload(device, &descriptors)?,
      count: descriptors.len() as u64,
      _data: data,
    })
  }

  /// The arguments of a launch reading `arenas`.
  fn launch(arenas: Option<&Self>) -> (*const AiurArena, u64) {
    arenas.map_or((std::ptr::null(), 0), |a| {
      (a.descriptors.as_ptr::<AiurArena>().cast_const(), a.count)
    })
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
  /// The shard image `resident` holds, for a per-shard record.
  shard: Option<Arc<ShardRows>>,
  /// The next shard's image, uploaded while the current one proves
  /// ([`DeviceRecord::prefetch`]).
  next: Option<(Arc<ShardRows>, Resident)>,
  /// The advice arenas, kept across shard images.
  arenas: Option<ArenaBuffers>,
}

/// One proof's device-resident record tables and circuit descriptors.
pub(super) struct DeviceRecord {
  device: i32,
  image: Image,
  state: RwLock<State>,
  /// Address of the execution record this was uploaded from.
  origin: *const (),
  /// That record while an [`Attached`] guard lends it: a release then
  /// keeps no host copy, and the next tile uploads from the record again.
  restore: RwLock<Option<RecordOrigin>>,
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
  /// Set when the record is uploaded one shard image at a time.
  sharding: Option<Sharding>,
  /// Held while a shard image is prefetched ([`Self::prefetch`]).
  prefetching: Mutex<()>,
  /// The advice arenas the device circuits read, uploaded again after a
  /// release.
  advice: Option<Arc<dyn DeviceArenas>>,
}
// SAFETY: the raw pointers address device memory owned by `state`, and
// launch workspaces are used by one tile at a time.
unsafe impl Send for DeviceRecord {}
unsafe impl Sync for DeviceRecord {}

fn poisoned<T>(_: T) -> String {
  "GPU population state poisoned".into()
}

/// A lent execution record and the [`fill_table`] that reads its type.
#[derive(Clone, Copy)]
struct RecordOrigin {
  record: *const (),
  fill:
    unsafe fn(i32, *const (), TableImage, &TableBuffers) -> Result<(), String>,
  fill_rows: unsafe fn(
    i32,
    *const (),
    TableImage,
    &[u32],
    &TableBuffers,
  ) -> Result<(), String>,
}

/// # Safety
/// `record` points to a live `Execution<B>`.
unsafe fn fill_rows_from<B: WitnessField>(
  device: i32,
  record: *const (),
  table: TableImage,
  ids: &[u32],
  buffers: &TableBuffers,
) -> Result<(), String> {
  // SAFETY: the caller's contract.
  let record = unsafe { &*record.cast::<Execution<B>>() };
  fill_rows(device, record, table, ids, buffers, true)
}

/// # Safety
/// `record` points to a live `Execution<B>`.
unsafe fn fill_from<B: WitnessField>(
  device: i32,
  record: *const (),
  table: TableImage,
  buffers: &TableBuffers,
) -> Result<(), String> {
  // SAFETY: the caller's contract.
  let record = unsafe { &*record.cast::<Execution<B>>() };
  fill_table(device, record, table, buffers, false)
}

/// Lends a [`DeviceRecord`] its execution record until dropped
/// ([`DeviceRecord::attach`]).
pub(super) struct Attached<'a> {
  record: &'a DeviceRecord,
}

impl Drop for Attached<'_> {
  fn drop(&mut self) {
    *self
      .record
      .restore
      .write()
      .unwrap_or_else(std::sync::PoisonError::into_inner) = None;
  }
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
    let advice = plans.arenas_for(record, &plans.enabled(record));
    let report = std::env::var_os("AIUR_POPULATION_REPORT").is_some();
    let free_before = if report { device_free(device) } else { 0 };
    let resident = image.upload(device, |i, buffers| {
      fill_table(device, record, image.tables[i], buffers, true)
    })?;
    let mut bytes = image.bytes()?;
    let arenas = match &advice {
      Some(advice) => {
        let data = advice.arenas();
        let arena_bytes = arena_bytes(&data);
        if report {
          eprintln!(
            "[aiur/gpu] advice arenas: {arena_bytes} B in {} arenas",
            data.len()
          );
        }
        bytes = bytes
          .saturating_add(u64::try_from(arena_bytes).unwrap_or(u64::MAX));
        Some(ArenaBuffers::upload(device, &data)?)
      },
      None => None,
    };
    if report {
      // Other work on the device can move free memory meanwhile, so this
      // measures the record's footprint only on an otherwise idle device.
      let used = free_before.saturating_sub(device_free(device));
      eprintln!(
        "[aiur/gpu] record upload: {bytes} B modelled, {used} B taken from \
         device free memory ({} tables, {} callee indexes)",
        image.tables.len(),
        image.callees.len()
      );
    }
    let mut record = Self {
      device,
      image,
      state: RwLock::new(State {
        resident: Some(resident),
        spilled: None,
        shard: None,
        next: None,
        arenas,
      }),
      origin: std::ptr::from_ref(record).cast(),
      restore: RwLock::new(None),
      workspaces: Mutex::new(vec![]),
      releasable: release_enabled(),
      bytes,
      compiled: plans.compiled.clone(),
      ranges: RangeCounts::default(),
      sharding: None,
      prefetching: Mutex::new(()),
      advice,
    };
    record.ranges = record.count_ranges(&backend.plan.depth)?;
    Ok(record)
  }

  /// A record uploaded one shard image of `layout` at a time
  /// ([`ShardRows`]), when every device circuit's members recorded their
  /// references; otherwise the whole record ([`Self::upload`]). Each shard
  /// image is gathered when the shard's witness is built and uploaded by its
  /// first tile, which needs the execution record attached
  /// ([`Self::attach`]). The depth range uses are counted here, shard by
  /// shard.
  pub(super) fn upload_sharded<B: WitnessField>(
    backend: &Backend<'_, '_, B>,
    plans: &DevicePlans,
    record: &Execution<B>,
    device: i32,
    layout: &BatchLayout,
  ) -> Result<Self, String> {
    let image = Image::new(backend, plans, record)?;
    let sharding = match Sharding::new(&image, backend, record) {
      Ok(sharding) => sharding,
      Err(reason) => {
        if std::env::var_os("AIUR_POPULATION_REPORT").is_some() {
          eprintln!("[aiur/gpu] uploading the whole device record: {reason}");
        }
        return Self::upload(backend, plans, record, device);
      },
    };
    let mut record_state = Self {
      device,
      image,
      state: RwLock::new(State::default()),
      origin: std::ptr::from_ref(record).cast(),
      restore: RwLock::new(None),
      workspaces: Mutex::new(vec![]),
      releasable: release_enabled(),
      bytes: 0,
      compiled: plans.compiled.clone(),
      ranges: RangeCounts::default(),
      sharding: Some(sharding),
      prefetching: Mutex::new(()),
      advice: plans.arenas_for(record, &plans.enabled(record)),
    };
    record_state.ranges =
      record_state.count_shard_ranges(&backend.plan.depth, record, layout)?;
    Ok(record_state)
  }

  /// The image of `shard`'s device rows, for a per-shard record.
  pub(super) fn shard_rows<B: WitnessField>(
    &self,
    record: &Execution<B>,
    shard: &ShardLayout,
  ) -> Result<Option<Arc<ShardRows>>, String> {
    let Some(sharding) = &self.sharding else { return Ok(None) };
    if !std::ptr::eq(std::ptr::from_ref(record).cast(), self.origin) {
      return Err("shard image of another execution".into());
    }
    let rows = self.image.shard_rows(sharding, record, shard, |_| true)?;
    Ok(Some(Arc::new(rows)))
  }

  /// Depth range-table uses of the device circuits with gap slots, counted
  /// shard by shard: each shard's image of those circuits is uploaded and
  /// its rows of them are filled once, as [`Self::count_ranges`] does.
  fn count_shard_ranges<B: WitnessField>(
    &self,
    depth: &DepthPlan,
    record: &Execution<B>,
    layout: &BatchLayout,
  ) -> Result<RangeCounts, String> {
    let (_, words) = range_offsets(depth);
    let gapped = |ci: usize| {
      self.image.circuits[ci].as_ref().is_some_and(|c| c.gaps && c.real > 0)
    };
    let sharding = self.sharding.as_ref().ok_or("not a per-shard record")?;
    if words == 0 || !(0..self.image.circuits.len()).any(gapped) {
      return Ok(RangeCounts::default());
    }
    let ranges = Buffer::upload(self.device, &vec![0u64; words])?;
    let start = std::time::Instant::now();
    let mut uploaded = 0u64;
    self.upload_arenas(&mut *self.state.write().map_err(poisoned)?)?;
    let state = self.state.read().map_err(poisoned)?;
    for shard in &layout.shards {
      let counted: Vec<usize> = (0..self.image.circuits.len())
        .filter(|&ci| gapped(ci) && shard.circuits.get(ci).is_some_and(|s| s.rows > 0))
        .collect();
      if counted.is_empty() {
        continue;
      }
      let rows = self.image.shard_rows(sharding, record, shard, gapped)?;
      uploaded += rows.bytes;
      let resident = self.image.upload_rows(
        self.device,
        &rows.counts(),
        Some(&rows),
        |i, buffers| {
          fill_rows(
            self.device,
            record,
            self.image.tables[i],
            &rows.ids[i],
            buffers,
            true,
          )
        },
      )?;
      for &ci in &counted {
        let slice = shard.circuits[ci];
        self.count_circuit(
          &resident,
          state.arenas.as_ref(),
          ci,
          slice.first as u64,
          (slice.first + slice.rows) as u64,
          &ranges,
        )?;
      }
    }
    drop(state);
    if std::env::var_os("AIUR_POPULATION_REPORT").is_some() {
      eprintln!(
        "[aiur/gpu] depth range counts: {} shard images of gap circuits, {uploaded} B, in {:.2}s",
        layout.shards.len(),
        start.elapsed().as_secs_f64()
      );
    }
    let flat = ranges.read(words)?;
    Ok(RangeCounts::from_flat(depth.tables.iter().map(|t| t.width), &flat))
  }

  /// Lends this record the execution record it was uploaded from, until
  /// the guard drops. A release then frees the device record without
  /// copying it to the host, since a re-upload reads `record` again, so a
  /// proof that holds its execution record anyway holds no second copy.
  ///
  /// # Safety
  /// The guard must be dropped, not leaked, while `record` is still
  /// borrowed: a re-upload after `record` is gone would read freed memory.
  pub(super) unsafe fn attach<'a, B: WitnessField>(
    &'a self,
    record: &'a Execution<B>,
  ) -> Result<Attached<'a>, String> {
    if !std::ptr::eq(std::ptr::from_ref(record).cast(), self.origin) {
      return Err("device record attached to another execution".into());
    }
    *self.restore.write().map_err(poisoned)? =
      Some(RecordOrigin {
        record: self.origin,
        fill: fill_from::<B>,
        fill_rows: fill_rows_from::<B>,
      });
    Ok(Attached { record: self })
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
    let state = self.resident(None)?;
    let resident = state.resident.as_ref().expect("resident record");
    for ci in counted {
      let real = self.image.circuits[ci].as_ref().map_or(0, |c| c.real);
      self.count_circuit(
        resident,
        state.arenas.as_ref(),
        ci,
        0,
        real,
        &ranges,
      )?;
    }
    drop(state);
    let flat = ranges.read(words)?;
    Ok(RangeCounts::from_flat(depth.tables.iter().map(|t| t.width), &flat))
  }

  /// Adds the depth range-table uses of circuit `ci`'s real rows
  /// `begin..end`, filled from `resident`, to `ranges`.
  fn count_circuit(
    &self,
    resident: &Resident,
    arenas: Option<&ArenaBuffers>,
    ci: usize,
    begin: u64,
    end: u64,
    ranges: &Buffer,
  ) -> Result<(), String> {
    // SAFETY: plain query of the launch configuration.
    let launch = unsafe { aiur_gpu_population_threads() };
    {
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
      let (arena_descriptors, arena_count) = ArenaBuffers::launch(arenas);
      // SAFETY: device pointers come from this record's resident buffers,
      // which the read guard keeps alive, and from buffers sized above for
      // `threads` threads.
      check(
        unsafe {
          aiur_gpu_count_ranges(
            self.device,
            &circuit,
            arena_descriptors,
            arena_count,
            begin,
            end,
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
    Ok(())
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

  /// Whether `state` holds what a tile of `shard` reads: the whole record,
  /// or for a per-shard record that shard's image.
  fn holds(&self, state: &State, shard: Option<&Arc<ShardRows>>) -> bool {
    state.resident.is_some()
      && (self.advice.is_none() || state.arenas.is_some())
      && (self.sharding.is_none()
        || matches!((&state.shard, shard), (Some(a), Some(b)) if Arc::ptr_eq(a, b)))
  }

  /// The record on the device, uploaded again from its host copy if it was
  /// released; for a per-shard record, `shard`'s image, replacing any other
  /// shard's.
  fn resident(
    &self,
    shard: Option<&Arc<ShardRows>>,
  ) -> Result<RwLockReadGuard<'_, State>, String> {
    if self.sharding.is_some() && shard.is_none() {
      return Err("per-shard device record used without a shard image".into());
    }
    loop {
      let state = self.state.read().map_err(poisoned)?;
      if self.holds(&state, shard) {
        return Ok(state);
      }
      drop(state);
      // A shard image being prefetched may be this one: wait for it rather
      // than upload it twice.
      drop(self.prefetching.lock().map_err(poisoned)?);
      let mut state = self.state.write().map_err(poisoned)?;
      self.upload_arenas(&mut state)?;
      if !self.holds(&state, shard) {
        // Held across the upload, so the lent record outlives its reads.
        let restore = self.restore.read().map_err(poisoned)?;
        if let Some(rows) = shard {
          // The other shard's image is freed before this one is allocated.
          state.resident = None;
          state.shard = None;
          let resident = match state.next.take() {
            Some((next, resident)) if Arc::ptr_eq(&next, rows) => resident,
            _ => {
              let origin = (*restore).ok_or(
                "a per-shard device record needs its execution record attached",
              )?;
              // SAFETY: the read guard keeps the attachment.
              unsafe { self.upload_shard(origin, rows, "uploaded by its tile") }?
            },
          };
          drop(restore);
          state.resident = Some(resident);
          state.shard = Some(rows.clone());
          continue;
        }
        // Sequential packing: a parallel loop here could run a queued
        // tile job on this thread, which would wait on the write lock it
        // holds.
        let resident = match (&state.spilled, *restore) {
          (Some(spilled), _) => {
            self.image.upload(self.device, |i, buffers| {
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
            })?
          },
          (None, Some(origin)) => {
            self.image.upload(self.device, |i, buffers| {
              // SAFETY: the read guard keeps the attachment, whose record
              // outlives it.
              unsafe {
                (origin.fill)(
                  self.device,
                  origin.record,
                  self.image.tables[i],
                  buffers,
                )
              }
            })?
          },
          (None, None) => {
            return Err("released record has no host copy".into());
          },
        };
        drop(restore);
        state.resident = Some(resident);
      }
    }
  }

  /// Uploads the advice arenas into `state` if they are read and missing.
  fn upload_arenas(&self, state: &mut State) -> Result<(), String> {
    if let Some(advice) = &self.advice
      && state.arenas.is_none()
    {
      let start = std::time::Instant::now();
      let arenas = advice.arenas();
      state.arenas = Some(ArenaBuffers::upload(self.device, &arenas)?);
      if std::env::var_os("AIUR_POPULATION_REPORT").is_some() {
        eprintln!(
          "[aiur/gpu] advice arenas: {} B in {} arenas uploaded in {:.3}s",
          arena_bytes(&arenas),
          arenas.len(),
          start.elapsed().as_secs_f64()
        );
      }
    }
    Ok(())
  }

  /// Uploads `rows`' image from the record `origin` lends.
  ///
  /// # Safety
  /// `origin`'s record must outlive the call.
  unsafe fn upload_shard(
    &self,
    origin: RecordOrigin,
    rows: &ShardRows,
    how: &str,
  ) -> Result<Resident, String> {
    let start = std::time::Instant::now();
    let resident = self.image.upload_rows(
      self.device,
      &rows.counts(),
      Some(rows),
      |i, buffers| {
        // SAFETY: the caller's contract.
        unsafe {
          (origin.fill_rows)(
            self.device,
            origin.record,
            self.image.tables[i],
            &rows.ids[i],
            buffers,
          )
        }
      },
    )?;
    if std::env::var_os("AIUR_POPULATION_REPORT").is_some() {
      eprintln!(
        "[aiur/gpu] shard image: {} B {how} in {:.3}s, gathered in {:.3}s",
        rows.bytes,
        start.elapsed().as_secs_f64(),
        rows.seconds
      );
    }
    Ok(resident)
  }

  /// Uploads `rows`' image beside the current shard's on another thread,
  /// for a per-shard record whose execution record is attached, so that
  /// the shard's first tile need not wait for it and neither does the
  /// witness that called this. Called when the next shard's witness is
  /// built, while the current shard proves. A failed upload (the device
  /// short of memory, say) leaves the tile to upload it.
  pub(super) fn prefetch(self: &Arc<Self>, rows: &Arc<ShardRows>) {
    if self.sharding.is_none() {
      return;
    }
    let (record, rows) = (Arc::clone(self), Arc::clone(rows));
    let spawned = std::thread::Builder::new()
      .name("aiur-prefetch".into())
      .spawn(move || record.prefetch_now(&rows));
    if let Err(error) = spawned {
      eprintln!("[aiur/gpu] shard image not prefetched: {error}");
    }
  }

  fn prefetch_now(&self, rows: &Arc<ShardRows>) {
    let Ok(_prefetching) = self.prefetching.lock() else { return };
    {
      let Ok(state) = self.state.read() else { return };
      let pending = state.next.as_ref().is_some_and(|(n, _)| Arc::ptr_eq(n, rows));
      if pending || self.holds(&state, Some(rows)) {
        return;
      }
    }
    let Ok(restore) = self.restore.read() else { return };
    let Some(origin) = *restore else { return };
    // SAFETY: the read guard keeps the attachment.
    let Ok(resident) = (unsafe { self.upload_shard(origin, rows, "prefetched") })
    else {
      return;
    };
    drop(restore);
    let Ok(mut state) = self.state.write() else { return };
    if !self.holds(&state, Some(rows)) {
      state.next = Some((rows.clone(), resident));
    }
  }

  /// Frees the record and launch workspaces on `device`, first copying the
  /// tables to the host if no copy exists and no execution record is
  /// attached. Tiles requested later upload the record again. If the copy
  /// fails the record stays resident.
  pub(super) fn release(&self, device: i32) {
    if device != self.device {
      return;
    }
    let mut state =
      self.state.write().unwrap_or_else(std::sync::PoisonError::into_inner);
    if self.sharding.is_some() && state.resident.is_none() {
      if self.restore.read().is_ok_and(|r| r.is_some()) {
        state.next = None;
        state.arenas = None;
      }
      return;
    }
    let Some(resident) = &state.resident else { return };
    if self.sharding.is_some() {
      // A shard image is gathered again from the attached record; without
      // one it stays.
      if self.restore.read().map_or(true, |r| r.is_none()) {
        return;
      }
      state.next = None;
      state.resident = None;
      state.shard = None;
      state.arenas = None;
      self
        .workspaces
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .clear();
      return;
    }
    let attached = self
      .restore
      .read()
      .unwrap_or_else(std::sync::PoisonError::into_inner)
      .is_some();
    if state.spilled.is_none() && !attached {
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
    state.arenas = None;
    self
      .workspaces
      .lock()
      .unwrap_or_else(std::sync::PoisonError::into_inner)
      .clear();
  }

  /// A workspace for at least `words` scratch words per launch thread.
  fn workspace(&self, words: u64) -> Result<Workspace, String> {
    // SAFETY: plain query of the launch configuration.
    let minimal = unsafe { aiur_gpu_population_threads() };
    let capacity = minimal.saturating_mul(words.max(1));
    let mut pool = self.workspaces.lock().map_err(poisoned)?;
    // A minimal call never holds a scratch workspace, which would make an
    // interpreted call allocate another: `DevicePlans::scratch_bytes`
    // bounds the pool by that.
    let fitting = pool
      .iter()
      .enumerate()
      .filter(|(_, w)| {
        w.capacity >= capacity && (capacity > minimal || w.capacity == minimal)
      })
      .min_by_key(|(_, w)| w.capacity)
      .map(|(i, _)| i);
    if let Some(i) = fitting {
      return Ok(pool.swap_remove(i));
    }
    if capacity > minimal
      && let Some(i) = pool
        .iter()
        .enumerate()
        .filter(|(_, w)| w.capacity > minimal)
        .max_by_key(|(_, w)| w.capacity)
        .map(|(i, _)| i)
    {
      // Too small for this call, so superseded by the one it allocates.
      drop(pool.swap_remove(i));
    }
    drop(pool);
    Workspace::new(self.device, capacity)
  }

  /// Fills `rows` rows of circuit `ci`'s shard (`base`, `height`) from shard
  /// row `first` into device memory at `output`.
  #[allow(clippy::too_many_arguments)]
  pub(super) fn populate(
    &self,
    ci: usize,
    shard: Option<&Arc<ShardRows>>,
    output: *mut u64,
    base: usize,
    first: usize,
    rows: usize,
    height: usize,
    real_rows: usize,
  ) -> Result<(), String> {
    let state = self.resident(shard)?;
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
    let (arenas, arena_count) = ArenaBuffers::launch(state.arenas.as_ref());
    // SAFETY: device pointers come from this record's resident buffers,
    // which the read guard keeps alive; the caller owns `rows * width`
    // words at `output` on this device; the workspace is exclusively ours.
    let launched = check(
      unsafe {
        aiur_gpu_populate(
          self.device,
          &circuit,
          arenas,
          arena_count,
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
  pub(super) fn has_host_copy(&self) -> bool {
    self.state.read().unwrap().spilled.is_some()
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
    shard: Option<&Arc<ShardRows>>,
    base: usize,
    first: usize,
    rows: usize,
    height: usize,
    real_rows: usize,
    fill: u64,
  ) -> Result<Vec<u64>, String> {
    let words = rows * self.width(ci);
    let tile = Buffer::upload(self.device, &vec![fill; words.max(1)])?;
    self.populate(ci, shard, tile.as_ptr(), base, first, rows, height, real_rows)?;
    tile.read(words)
  }
}

/// Fills one uploaded table's rows, multiplicities and recorded heights
/// from `record`. With `parallel` off, no rayon job runs on this thread, so
/// a caller holding a lock that queued tile jobs wait on cannot run one.
fn fill_table<B: WitnessField>(
  device: i32,
  record: &Execution<B>,
  table: TableImage,
  buffers: &TableBuffers,
  parallel: bool,
) -> Result<(), String> {
  let TableImage { source, count, stride, .. } = table;
  let function = match source {
    Source::Function(f) => f,
    Source::Rom(width) => {
      return upload_rom::<B>(device, record, width, count, buffers, parallel);
    },
  };
  let table = &record.queries.tables[function];
  if table.static_map.is_some() {
    return Err("GPU population cannot read a map's table".into());
  }
  let (chunks, chunk_stride, per_chunk) = table.row_chunks();
  if chunk_stride != stride {
    return Err("query table stride changed".into());
  }
  // The first `count` rows of `chunks`, chunk by chunk.
  fn take<T>(
    chunks: &[Vec<T>],
    count: usize,
    stride: usize,
    per_chunk: usize,
  ) -> Result<Vec<&[T]>, String> {
    let mut done = 0;
    let mut pieces = Vec::new();
    for chunk in chunks {
      let take = per_chunk.min(count - done);
      if take == 0 {
        break;
      }
      pieces.push(&chunk[..take * stride]);
      done += take;
    }
    if done != count {
      return Err("query table storage ended early".into());
    }
    Ok(pieces)
  }
  match chunks {
    // Rows of `u32` columns only hold canonical values, widened while staged.
    Stored::Narrow(chunks) => {
      let pieces = take(chunks, count, stride, per_chunk)?;
      buffers.rows.write_staged(0, &pieces, parallel)?;
    },
    Stored::Wide(chunks) => {
      let words: Vec<_> = take(chunks, count, stride, per_chunk)?
        .into_iter()
        .map(B::words)
        .collect();
      let pieces: Vec<&[u64]> = words.iter().map(|w| &w[..]).collect();
      buffers.rows.write_staged(0, &pieces, parallel)?;
    },
    // Packed rows with field-element columns are unpacked row by row.
    Stored::Mixed => {
      if table.len() < count {
        return Err("query table storage ended early".into());
      }
      buffers.rows.write_gathered(count, stride, parallel, |i, out| {
        table.row_words(i, out);
      })?;
    },
  }
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
  // Counts and heights are `u32`s, below the field characteristic.
  if table.len() < count {
    return Err("query table storage ended early".into());
  }
  buffers.multiplicities.write_gathered(count, 1, parallel, |i, out| {
    out[0] = table.count(i);
  })?;
  if let Some(depths) = &buffers.depths {
    if table.depths_len() < count {
      return Err("query record is missing depth heights".into());
    }
    depths.write_gathered(count, 1, parallel, |i, out| {
      out[0] = table.depth(i);
    })?;
  }
  Ok(())
}

/// Uploads the `count` ROM cells of `width` in address order as table rows
/// (`width` words each), with their multiplicities. A cell's row index is
/// its width-local address. Cells are gathered a staging buffer's worth at
/// a time, so the host holds no copy of the whole table.
fn upload_rom<B: WitnessField>(
  device: i32,
  record: &Execution<B>,
  width: usize,
  count: usize,
  buffers: &TableBuffers,
  parallel: bool,
) -> Result<(), String> {
  let memory = &record.memory;
  if count == 0 {
    return Ok(());
  }
  let bucket = memory.width_cells(width);
  if bucket.len() != count {
    return Err("ROM cell count changed".into());
  }
  let block = (STAGING_WORDS / width.max(1)).max(1);
  let mut words = vec![0u64; block.min(count) * width];
  let mut multiplicities = vec![0u64; block.min(count)];
  for start in (0..count).step_by(block) {
    let cells = block.min(count - start);
    let words = &mut words[..cells * width];
    let multiplicities = &mut multiplicities[..cells];
    type Cell<'a> = (usize, (&'a mut [u64], &'a mut u64));
    let fill = |(offset, (row, multiplicity)): Cell<'_>| -> Result<(), String> {
      let address = start + offset;
      let entry = bucket.get(address).ok_or("missing ROM cell")?;
      if entry.address != address {
        return Err("ROM addresses are not consecutive from zero".into());
      }
      if entry.multiplicity >= Val::ORDER_U64 {
        return Err("ROM multiplicity reaches field characteristic".into());
      }
      row.copy_from_slice(&B::words(entry.cell.value));
      *multiplicity = entry.multiplicity;
      Ok(())
    };
    // Zero-width cells have empty rows; `chunks_mut` needs a positive size.
    let mut empty: Vec<&mut [u64]> = vec![];
    let rows: Vec<&mut [u64]> = if width == 0 {
      empty.resize_with(cells, || &mut []);
      empty
    } else {
      words.chunks_mut(width).collect()
    };
    #[cfg(feature = "parallel")]
    if parallel {
      rows
        .into_par_iter()
        .zip(multiplicities.par_iter_mut())
        .enumerate()
        .try_for_each(fill)?;
    } else {
      rows
        .into_iter()
        .zip(multiplicities.iter_mut())
        .enumerate()
        .try_for_each(fill)?;
    }
    #[cfg(not(feature = "parallel"))]
    rows
      .into_iter()
      .zip(multiplicities.iter_mut())
      .enumerate()
      .try_for_each(fill)?;
    buffers.rows.write_staged(start * width, &[words], parallel)?;
    buffers.multiplicities.write_staged(start, &[multiplicities], parallel)?;
  }
  // SAFETY: the buffer holds `count * width` words.
  check(
    unsafe {
      aiur_gpu_canonicalize(
        device,
        buffers.rows.as_ptr(),
        (count * width) as u64,
      )
    },
    "GPU population canonicalization",
  )
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
      13 => "missing recorded store",
      14 => "missing recorded load",
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
  /// The shard's image, for a per-shard record.
  pub(super) rows: Option<Arc<ShardRows>>,
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
        self.rows.as_ref(),
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
      self.rows.as_ref(),
      view.as_mut_ptr(),
      self.base,
      view.first_row() % self.height,
      view.rows(),
      self.height,
      self.real_rows,
    )
  }
  fn device_state_bytes(&self) -> usize {
    if !self.record.releasable {
      return 0;
    }
    let bytes = self.rows.as_ref().map_or(self.record.bytes, |rows| rows.bytes);
    usize::try_from(bytes).unwrap_or(usize::MAX)
  }
  fn device_state_resident(&self) -> bool {
    let state = self
      .record
      .state
      .read()
      .unwrap_or_else(std::sync::PoisonError::into_inner);
    self.record.holds(&state, self.rows.as_ref())
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

/// Whether a release request frees the device record, to be uploaded again
/// on the next tile. On unless `AIUR_GPU_TRACE_RELEASE=0`: multi-stark asks
/// only when a phase's admission is short of memory, so the record then
/// never pins device memory a later phase needs.
pub(super) fn release_enabled() -> bool {
  std::env::var("AIUR_GPU_TRACE_RELEASE").as_deref() != Ok("0")
}
