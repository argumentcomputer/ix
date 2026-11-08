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
use super::*;
use crate::{
  Execution,
  trace::{
    Action,
    plan::device::{Constants, Encoded, Target},
  },
};
use multi_stark::{cuda::DeviceTraceView, witness::TraceGenerator};
use std::{ffi::c_void, sync::Arc};

const POLY_CONST: u32 = 0;
const POLY_VAR: u32 = 1;
const POLY_ADD: u32 = 2;
const POLY_SUB: u32 = 3;
const POLY_MUL: u32 = 4;

#[repr(C)]
#[derive(Clone, Copy)]
struct AiurFunction {
  code: *const u32,
  constants: *const u64,
  rows: *const u64,
  multiplicities: *const u64,
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
  fn aiur_gpu_population_threads() -> u64;
  fn aiur_gpu_malloc(
    device: i32,
    bytes: usize,
    output: *mut *mut c_void,
  ) -> i32;
  fn aiur_gpu_free(device: i32, pointer: *mut c_void) -> i32;
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
    let buffer = Self::new(device, size_of_val(data))?;
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
          size_of_val(data),
        )
      },
      "GPU population upload",
    )
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

/// A function's encoded plan with its placement, ready to upload.
struct Program {
  code: Vec<u32>,
  scratch: u32,
  inputs: u32,
  outputs: u32,
}

/// Device encodings of a backend's population plans, built once. Functions
/// the device cannot fill are `None`; a circuit is filled on the device only
/// when all of its members are encoded.
pub(super) struct DevicePlans {
  programs: Vec<Option<Program>>,
  constants: Vec<u64>,
  /// Call targets: callee slot to function index.
  callees: Vec<usize>,
  pub(super) circuits: Vec<bool>,
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

fn polynomial(
  p: &Polynomial,
  constants: &mut Constants,
  out: &mut Vec<u32>,
) -> Option<()> {
  match p {
    Polynomial::Const(value) => {
      out.extend([POLY_CONST, constants.word(*value)? & 0x7fff_ffff]);
    },
    Polynomial::Var(column) => {
      out.extend([POLY_VAR, u32::try_from(*column).ok()?]);
    },
    Polynomial::Add(xs) | Polynomial::Sub(xs) | Polynomial::Mul(xs) => {
      polynomial(&xs[0], constants, out)?;
      polynomial(&xs[1], constants, out)?;
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

impl DevicePlans {
  /// `None` unless `AIUR_GPU_TRACE=generated`, which requires device lookups.
  pub(super) fn from_env<B: WitnessField>(
    backend: &Backend<'_, '_, B>,
  ) -> Result<Option<Self>, String> {
    match std::env::var("AIUR_GPU_TRACE").as_deref() {
      Ok("generated") => {
        if !backend.gpu_lookup_only {
          return Err(
            "AIUR_GPU_TRACE=generated requires device lookups (unset AIUR_TRACE_ONLY_LOOKUPS=0)"
              .into(),
          );
        }
        Ok(Some(Self::new(backend)))
      },
      Ok("cpu") | Ok("") | Err(_) => Ok(None),
      Ok(other) => {
        Err(format!("AIUR_GPU_TRACE must be cpu or generated, not {other:?}"))
      },
    }
  }

  pub(super) fn new<B: WitnessField>(backend: &Backend<'_, '_, B>) -> Self {
    let plan = backend.plan;
    let program = plan.program.program();
    let functions = program.functions.len();
    let mut constants = Constants::default();
    let mut callees = Vec::new();
    let mut slots = FxHashMap::default();
    let programs: Vec<_> = plan
      .fills
      .iter()
      .enumerate()
      .map(|(f, fill)| {
        let placement = &backend.placements[plan.members[f]];
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
            Action::Hint { instruction: i, channel, .. }
              if *i == instruction =>
            {
              hint_kind(channel)
            },
            _ => None,
          })
        };
        let column = |c: usize| placement.columns[c];
        let Encoded { mut code, scratch, inputs, outputs } =
          fill.encode(&mut call, &mut hint, &column, &mut constants)?;
        code.push(u32::try_from(placement.selector).ok()?);
        code.push(u32::try_from(placement.writes.len()).ok()?);
        for write in &placement.writes {
          let mut tokens = vec![];
          polynomial(&write.value, &mut constants, &mut tokens)?;
          code.push(u32::try_from(write.column).ok()?);
          code.push(u32::try_from(tokens.len() / 2).ok()?);
          code.extend(tokens);
        }
        Some(Program { code, scratch, inputs, outputs })
      })
      .collect();
    let circuits: Vec<bool> = backend
      .members
      .iter()
      .map(|members| {
        !members.is_empty() && members.iter().all(|&f| programs[f].is_some())
      })
      .collect();
    Self { programs, constants: constants.values, callees, circuits }
  }
}

/// One proof's device-resident record tables and circuit descriptors.
pub(super) struct DeviceRecord {
  device: i32,
  circuits: Vec<Option<AiurCircuit>>,
  heights: Vec<usize>,
  widths: Vec<usize>,
  _buffers: Vec<Buffer>,
}
// SAFETY: the raw pointers address device memory owned by `_buffers`.
unsafe impl Send for DeviceRecord {}
unsafe impl Sync for DeviceRecord {}

impl DeviceRecord {
  /// Uploads what the device circuits read from `record`: their member
  /// queries and every callee's queries with an input index.
  pub(super) fn upload<B: WitnessField>(
    backend: &Backend<'_, '_, B>,
    plans: &DevicePlans,
    record: &Execution<B>,
    device: i32,
  ) -> Result<Self, String> {
    let tables = &record.queries.tables;
    let mut buffers = vec![];
    // Programs: every encoded plan back to back, and the constant pool.
    let mut code: Vec<u32> = vec![];
    let mut offsets = vec![0; plans.programs.len()];
    for (f, program) in plans.programs.iter().enumerate() {
      if let Some(program) = program {
        offsets[f] = code.len();
        code.extend(&program.code);
      }
    }
    let code_buffer = Buffer::upload(device, &code)?;
    let constants = Buffer::upload(device, &plans.constants)?;
    // Query tables, uploaded once per function from their storage chunks.
    let mut rows = FxHashMap::default();
    let mut needed: Vec<usize> = plans.callees.clone();
    for (ci, &on) in plans.circuits.iter().enumerate() {
      if on {
        needed.extend(&backend.members[ci]);
      }
    }
    needed.sort_unstable();
    needed.dedup();
    for &f in &needed {
      let table = &tables[f];
      if table.static_map.is_some() {
        return Err("GPU population cannot read a map's table".into());
      }
      let (chunks, stride, per_chunk) = table.row_chunks();
      let count = table.len();
      let words = count.checked_mul(stride).ok_or("table size overflow")?;
      let buffer = Buffer::new(device, words.max(1) * 8)?;
      let mut done = 0;
      for chunk in chunks {
        let take = per_chunk.min(count - done);
        if take == 0 {
          break;
        }
        let values = B::words(&chunk[..take * stride]);
        buffer.write(done * stride * 8, &values)?;
        done += take;
      }
      if done != count {
        return Err("query table storage ended early".into());
      }
      // SAFETY: the buffer holds `words` words.
      check(
        unsafe { aiur_gpu_canonicalize(device, buffer.as_ptr(), words as u64) },
        "GPU population canonicalization",
      )?;
      let counts = &table.counts()[..count];
      if counts.iter().any(|&c| c >= Val::ORDER_U64) {
        return Err("function count reaches field characteristic".into());
      }
      let multiplicities = Buffer::upload(device, counts)?;
      rows.insert(f, (buffer, multiplicities, stride));
    }
    // Callee input indexes.
    let mut callees = vec![];
    let mut indexes = vec![];
    for &f in &plans.callees {
      let (inputs, outputs) = tables[f].widths();
      let (buffer, _, stride) = &rows[&f];
      let count = tables[f].len();
      let size = (count.max(1) * 2).next_power_of_two();
      let mask =
        u32::try_from(size - 1).map_err(|_| "callee index overflow")?;
      let index = Buffer::new(device, size * 4)?;
      // SAFETY: `index` holds `size` words; `buffer` holds the table rows.
      check(
        unsafe {
          aiur_gpu_build_index(
            device,
            buffer.as_ptr(),
            count as u64,
            inputs as u32,
            *stride as u32,
            index.as_ptr(),
            mask,
          )
        },
        "GPU population callee index",
      )?;
      callees.push(AiurCallee {
        rows: buffer.as_ptr(),
        index: index.as_ptr(),
        count: count as u64,
        mask,
        inputs: inputs as u32,
        outputs: outputs as u32,
        stride: *stride as u32,
      });
      indexes.push(index);
    }
    let callee_buffer = Buffer::upload(device, &callees)?;
    // Circuit descriptors.
    let mut circuits = vec![None; backend.system.circuits.len()];
    let mut heights = vec![0; backend.system.circuits.len()];
    let mut widths = vec![0; backend.system.circuits.len()];
    let mut descriptors = vec![];
    for (ci, &on) in plans.circuits.iter().enumerate() {
      if !on {
        continue;
      }
      let mut members = vec![];
      let mut first = 0u64;
      let mut circuit_scratch = 0;
      for &f in &backend.members[ci] {
        let program = plans.programs[f].as_ref().expect("encoded member");
        let (buffer, multiplicities, stride) = &rows[&f];
        let count = tables[f].len() as u64;
        members.push(AiurFunction {
          // SAFETY: offsets index the uploaded code.
          code: unsafe { code_buffer.as_ptr::<u32>().add(offsets[f]) },
          constants: constants.as_ptr(),
          rows: buffer.as_ptr(),
          multiplicities: multiplicities.as_ptr(),
          count,
          first,
          code_len: program.code.len() as u32,
          scratch: program.scratch,
          inputs: program.inputs,
          outputs: program.outputs,
          stride: *stride as u32,
          pad: 0,
        });
        first += count;
        circuit_scratch = circuit_scratch.max(program.scratch);
      }
      let real = usize::try_from(first).map_err(|_| "row count overflow")?;
      let height = if real == 0 {
        0
      } else {
        real.checked_next_power_of_two().ok_or("trace height overflow")?
      };
      let width = backend.system.circuits[ci].main_width;
      let member_buffer = Buffer::upload(device, &members)?;
      circuits[ci] = Some(AiurCircuit {
        members: member_buffer.as_ptr(),
        callees: callee_buffer.as_ptr(),
        real: first,
        member_count: members.len() as u32,
        width: width as u32,
        scratch: circuit_scratch,
        pad: 0,
      });
      heights[ci] = height;
      widths[ci] = width;
      descriptors.push(member_buffer);
    }
    buffers.push(code_buffer);
    buffers.push(constants);
    for (_, (rows, multiplicities, _)) in rows {
      buffers.push(rows);
      buffers.push(multiplicities);
    }
    buffers.extend(indexes);
    buffers.push(callee_buffer);
    buffers.extend(descriptors);
    Ok(Self { device, circuits, heights, widths, _buffers: buffers })
  }

  /// The padded height of a device circuit, if `ci` is one.
  pub(super) fn height(&self, ci: usize) -> Option<usize> {
    self.circuits[ci].map(|_| self.heights[ci])
  }

  /// Fills `rows` rows of circuit `ci`'s shard (`base`, `height`) from shard
  /// row `first` into device memory at `output`.
  fn populate(
    &self,
    ci: usize,
    output: *mut u64,
    base: usize,
    first: usize,
    rows: usize,
    height: usize,
  ) -> Result<(), String> {
    let circuit = self.circuits[ci].as_ref().ok_or("not a device circuit")?;
    // SAFETY: plain query of the launch configuration.
    let threads = unsafe { aiur_gpu_population_threads() };
    let scratch = Buffer::new(
      self.device,
      (threads * u64::from(circuit.scratch).max(1) * 8) as usize,
    )?;
    let error = Buffer::upload(self.device, &[AiurPopulationError::default()])?;
    // SAFETY: device pointers come from this record's live buffers; the
    // caller owns `rows * width` words at `output` on this device.
    check(
      unsafe {
        aiur_gpu_populate(
          self.device,
          circuit,
          output,
          base as u64,
          first as u64,
          rows as u64,
          height as u64,
          scratch.as_ptr(),
          error.as_ptr(),
        )
      },
      "GPU population",
    )?;
    let mut status = [AiurPopulationError::default()];
    // SAFETY: `error` holds one value.
    check(
      unsafe {
        aiur_gpu_download(
          self.device,
          status.as_mut_ptr().cast(),
          error.as_ptr(),
          size_of::<AiurPopulationError>(),
        )
      },
      "GPU population status",
    )?;
    let status = status[0];
    if status.code != 0 {
      return Err(format!(
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
          _ => "invalid device plan encoding",
        }
      ));
    }
    Ok(())
  }
}

/// Rows `base..base + height` of a device circuit: one batch shard.
pub(super) struct DeviceTrace {
  pub(super) record: Arc<DeviceRecord>,
  pub(super) circuit: usize,
  pub(super) base: usize,
  pub(super) height: usize,
}

impl TraceGenerator<Val> for DeviceTrace {
  fn height(&self) -> usize {
    self.height
  }
  fn width(&self) -> usize {
    self.record.widths[self.circuit]
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
    )
  }
}
