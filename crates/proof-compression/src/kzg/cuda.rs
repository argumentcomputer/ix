//! Bounded, synchronous BLS12-381 operations on the visible sppark devices.
//!
//! With this feature compiled, every proving operation above the size
//! thresholds in the prover runs on the devices; only tiny shapes and
//! disk-backed columns use the host implementation. Memory admission is
//! checked before each operation and a rejected admission is an error, as is
//! any failure after a native operation has started. Every native call holds
//! a device lease; leases are per thread and refuse reentrant acquisition so
//! Rayon work stealing cannot deadlock a worker on its own device.

use ark_bls12_381::{Fq, Fr, G1Affine, G1Projective};
use ark_ff::{AdditiveGroup, BigInt, Field, Zero};
use blst as _;
use rayon::prelude::*;
use std::cell::Cell;
use std::collections::HashMap;
use std::ffi::c_void;
use std::sync::{Arc, Condvar, Mutex, OnceLock};

pub(super) mod lookup;
mod passes;
pub(super) mod quotient;
pub(super) mod srs_cache;
#[cfg(test)]
mod tests;

/// When the constraint-pass layout replaces dense device admission.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PassMode {
  Off,
  /// Only when the dense working set does not fit the device.
  Fallback,
  Force,
}

/// Runtime selection for the CUDA backend. Install it once with
/// [`configure`] before the first proving operation; afterwards the defaults
/// apply. Environment parsing belongs to the command line, not here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Settings {
  /// CUDA ordinals to use, in preference order; `None` uses every supported
  /// device.
  pub devices: Option<Vec<i32>>,
  /// Points per MSM chunk, in `1..=2^28`.
  pub msm_chunk_points: usize,
  /// Device bytes retained for resident coefficients per device; `None`
  /// uses half of each device's memory. The default keeps 8 GiB so that the
  /// lookup and quotient working sets of large partitions are always
  /// admitted beside the retained columns on one device.
  pub resident_limit_bytes: Option<usize>,
  /// Keep uploaded SRS ranges resident across operations.
  pub srs_cache: bool,
  pub passes: PassMode,
}

impl Default for Settings {
  fn default() -> Self {
    Self {
      devices: None,
      msm_chunk_points: 1 << 24,
      resident_limit_bytes: Some(8 << 30),
      srs_cache: false,
      passes: PassMode::Fallback,
    }
  }
}

static SETTINGS: OnceLock<Settings> = OnceLock::new();

/// Install the backend settings. Returns `false` if settings were already
/// installed or implicitly fixed by an earlier operation.
pub fn configure(settings: Settings) -> bool {
  assert!(
    (1..=1 << 28).contains(&settings.msm_chunk_points),
    "MSM chunk size must be in 1..=2^28"
  );
  SETTINGS.set(settings).is_ok()
}

pub fn settings() -> &'static Settings {
  SETTINGS.get_or_init(Settings::default)
}

#[repr(C)]
struct FftJob {
  input: *const [u64; 4],
  resident_input: *const c_void,
  output: *mut [u64; 4],
  input_count: usize,
  resident_output: *mut *mut c_void,
}

#[repr(C)]
#[derive(Default)]
struct NativeIdleMemory {
  driver_free_bytes: u64,
  total_bytes: u64,
  current_pool_reserved_bytes: u64,
  current_pool_used_bytes: u64,
  default_pool_reserved_bytes: u64,
  default_pool_used_bytes: u64,
  current_pool_is_default: u64,
}

unsafe extern "C" {
  fn ix_kzg_range_push(name: *const std::ffi::c_char);
  fn ix_kzg_range_pop();
  fn ix_kzg_fft_batch(
    device: i32,
    jobs: *const FftJob,
    job_count: usize,
    lg: u32,
    inverse: bool,
    shift: *const [u64; 4],
    slots: usize,
  ) -> i32;
  fn ix_kzg_polynomial_upload(
    device: i32,
    input: *const [u64; 4],
    count: usize,
    output: *mut *mut c_void,
  ) -> i32;
  fn ix_kzg_polynomial_destroy(device: i32, pointer: *mut c_void) -> i32;

  fn ix_kzg_devices(count: *mut i32) -> i32;
  fn ix_kzg_device_ordinal(index: i32, ordinal: *mut i32) -> i32;
  fn ix_kzg_memory(device: i32, free: *mut usize, total: *mut usize) -> i32;
  fn ix_kzg_idle_memory(
    device: i32,
    trim: bool,
    report: *mut NativeIdleMemory,
  ) -> i32;
  fn ix_kzg_msm_create(
    device: i32,
    out: *mut *mut c_void,
    points: *const c_void,
    count: usize,
  ) -> i32;
  fn ix_kzg_msm_invoke(
    device: i32,
    context: *mut c_void,
    out: *mut [[u64; 6]; 3],
    scalars: *const [u64; 4],
    count: usize,
    normalization: *const [u64; 4],
  ) -> i32;
  fn ix_kzg_msm_invoke_resident(
    device: i32,
    context: *mut c_void,
    out: *mut [[u64; 6]; 3],
    polynomial: *const c_void,
    offset: usize,
    count: usize,
    normalization: *const [u64; 4],
  ) -> i32;
  fn ix_kzg_msm_destroy(device: i32, context: *mut c_void) -> i32;
  #[cfg(test)]
  fn ix_kzg_fft(
    device: i32,
    values: *mut [u64; 4],
    lg: u32,
    inverse: bool,
    shift: *const [u64; 4],
  ) -> i32;
  #[cfg(test)]
  fn ix_kzg_fft_from(
    device: i32,
    input: *const [u64; 4],
    input_count: usize,
    output: *mut [u64; 4],
    lg: u32,
    inverse: bool,
    shift: *const [u64; 4],
  ) -> i32;
  fn ix_kzg_evaluate_resident(
    device: i32,
    coefficients: *const [u64; 4],
    resident: *const c_void,
    count: usize,
    points: *const [u64; 4],
    point_count: usize,
    results: *mut [u64; 4],
  ) -> i32;
  fn ix_kzg_divide(
    device: i32,
    input: *const [u64; 4],
    output: *mut [u64; 4],
    count: usize,
    z: *const [u64; 4],
  ) -> i32;
  fn ix_kzg_divide_resident(
    device: i32,
    input: *const [u64; 4],
    count: usize,
    z: *const [u64; 4],
    output: *mut *mut c_void,
  ) -> i32;
  fn ix_kzg_polynomial_sample(
    device: i32,
    polynomial: *const c_void,
    offset: usize,
    count: usize,
    samples: *mut [u64; 4],
  ) -> i32;
}

/// An NVTX range on the calling host thread, closed when dropped.
pub(super) struct ProfileRange(std::marker::PhantomData<std::rc::Rc<()>>);

impl ProfileRange {
  pub(super) fn new(name: &std::ffi::CStr) -> Self {
    unsafe { ix_kzg_range_push(name.as_ptr()) };
    Self(std::marker::PhantomData)
  }
}

impl Drop for ProfileRange {
  fn drop(&mut self) {
    unsafe { ix_kzg_range_pop() };
  }
}

// The FFI names explicit limb arrays. These checks reject an arkworks layout
// change before its field storage can be borrowed without a packing copy.
const _: () = {
  assert!(size_of::<Fr>() == size_of::<[u64; 4]>());
  assert!(align_of::<Fr>() == align_of::<[u64; 4]>());
  assert!(std::mem::offset_of!(Fr, 0) == 0);
  assert!(std::mem::offset_of!(BigInt<4>, 0) == 0);
  assert!(size_of::<G1Affine>() == 104);
  assert!(std::mem::offset_of!(G1Affine, x) == 0);
  assert!(std::mem::offset_of!(G1Affine, y) == 48);
  assert!(std::mem::offset_of!(G1Affine, infinity) == 96);
  assert!(size_of::<Fq>() == size_of::<[u64; 6]>());
  assert!(std::mem::offset_of!(Fq, 0) == 0);
  assert!(std::mem::offset_of!(BigInt<6>, 0) == 0);
};

fn check(code: i32, operation: &str) {
  assert_eq!(code, 0, "KZG CUDA {operation} failed (CUDA status {code})");
}

struct Devices {
  ids: Vec<i32>,
  busy: Mutex<Vec<bool>>,
  available: Condvar,
  chunk_points: usize,
  resident_bytes: Mutex<Vec<usize>>,
  resident_limits: Vec<usize>,
}

static DEVICES: OnceLock<Devices> = OnceLock::new();

thread_local! {
  static DEVICE_LEASES: Cell<usize> = const { Cell::new(0) };
}

impl Devices {
  fn potential_budget(&self, index: usize) -> usize {
    let (mut free, mut total) = (0, 0);
    check(
      unsafe { ix_kzg_memory(self.ids[index], &mut free, &mut total) },
      "memory query",
    );
    free.saturating_add(srs_cache::reclaimable(index)).saturating_sub(total / 4)
  }

  fn get() -> &'static Self {
    DEVICES.get_or_init(|| {
      let settings = settings();
      let mut count = 0;
      // The FFI writes one integer and initializes sppark's device registry.
      check(unsafe { ix_kzg_devices(&mut count) }, "device discovery");
      assert!(
        count > 0,
        "the KZG CUDA backend requires a visible CUDA GPU; build without the cuda feature for host execution"
      );
      let supported: Vec<i32> = (0..count)
        .map(|index| {
          let mut ordinal = -1;
          // Logical sppark indices need not match CUDA ordinals on mixed hosts.
          check(
            unsafe { ix_kzg_device_ordinal(index, &mut ordinal) },
            "device ordinal",
          );
          ordinal
        })
        .collect();
      let ids: Vec<i32> =
        settings.devices.clone().unwrap_or_else(|| supported.clone());
      assert!(!ids.is_empty(), "at least one KZG CUDA device is required");
      for (i, &id) in ids.iter().enumerate() {
        assert!(
          supported.contains(&id) && !ids[..i].contains(&id),
          "invalid or duplicate KZG CUDA ordinal {id}"
        );
      }
      let chunk_points = settings.msm_chunk_points;
      let resident_limits: Vec<_> = ids
        .iter()
        .map(|&id| {
          let (mut free, mut total) = (0, 0);
          check(unsafe { ix_kzg_memory(id, &mut free, &mut total) }, "memory query");
          settings
            .resident_limit_bytes
            .unwrap_or(total / 2)
            .min(total / 2)
            .min(free.saturating_sub(total / 4))
        })
        .collect();
      tracing::info!(?ids, chunk_points, ?resident_limits, "KZG sppark CUDA backend");
      Devices {
        busy: Mutex::new(vec![false; ids.len()]),
        resident_bytes: Mutex::new(vec![0; ids.len()]),
        resident_limits,
        ids,
        available: Condvar::new(),
        chunk_points,
      }
    })
  }

  fn acquire(&self) -> Device<'_> {
    Device::assert_unleased();
    let mut busy = self.busy.lock().unwrap();
    loop {
      if let Some(index) = busy.iter().position(|&v| !v) {
        busy[index] = true;
        return Device::new(self, index);
      }
      busy = self.available.wait(busy).unwrap();
    }
  }

  fn acquire_at(&self, index: usize) -> Device<'_> {
    Device::assert_unleased();
    let mut busy = self.busy.lock().unwrap();
    while busy[index] {
      busy = self.available.wait(busy).unwrap();
    }
    busy[index] = true;
    Device::new(self, index)
  }

  fn acquire_group(&self, indices: &[usize]) -> Vec<Device<'_>> {
    Device::assert_unleased();
    assert!(indices.iter().enumerate().all(|(i, &index)| {
      index < self.ids.len() && !indices[..i].contains(&index)
    }));
    let mut busy = self.busy.lock().unwrap();
    while indices.iter().any(|&index| busy[index]) {
      busy = self.available.wait(busy).unwrap();
    }
    for &index in indices {
      busy[index] = true;
    }
    indices.iter().map(|&index| Device::new(self, index)).collect()
  }

  fn reserve(&self, bytes: usize) -> Option<Reservation> {
    let mut retained = self.resident_bytes.lock().unwrap();
    let index = (0..self.ids.len())
      .filter(|&i| bytes <= self.resident_limits[i].saturating_sub(retained[i]))
      .min_by_key(|&i| retained[i])?;
    retained[index] += bytes;
    Some(Reservation { index, bytes })
  }
}

struct Device<'a> {
  devices: &'a Devices,
  index: usize,
  // Thread-local accounting requires release on the acquiring thread.
  _thread: std::marker::PhantomData<std::rc::Rc<()>>,
}

impl<'a> Device<'a> {
  fn new(devices: &'a Devices, index: usize) -> Self {
    DEVICE_LEASES.set(DEVICE_LEASES.get() + 1);
    Self { devices, index, _thread: std::marker::PhantomData }
  }

  fn assert_unleased() {
    // Nested Rayon work can steal a job that waits for its own thread's lease.
    assert_eq!(DEVICE_LEASES.get(), 0, "reentrant KZG device lease");
  }

  fn prepare_budget(&self, required: usize) -> bool {
    srs_cache::prepare_budget(self, required)
  }

  fn id(&self) -> i32 {
    self.devices.ids[self.index]
  }

  fn budget(&self) -> usize {
    let (mut free, mut total) = (0, 0);
    // The lease excludes other KZG operations on these sppark streams.
    check(
      unsafe { ix_kzg_memory(self.id(), &mut free, &mut total) },
      "memory query",
    );
    free.saturating_sub(total / 4)
  }

  fn idle_memory(&self, trim: bool) -> super::pcs::KzgDeviceMemorySnapshot {
    let mut memory = NativeIdleMemory::default();
    check(
      unsafe { ix_kzg_idle_memory(self.id(), trim, &mut memory) },
      "idle memory release",
    );
    let (srs_point_bytes, msm_workspace_bytes) =
      srs_cache::resident_bytes(self.index);
    super::pcs::KzgDeviceMemorySnapshot {
      driver_free_bytes: memory.driver_free_bytes,
      total_bytes: memory.total_bytes,
      current_pool_reserved_bytes: memory.current_pool_reserved_bytes,
      current_pool_used_bytes: memory.current_pool_used_bytes,
      default_pool_reserved_bytes: memory.default_pool_reserved_bytes,
      default_pool_used_bytes: memory.default_pool_used_bytes,
      current_pool_is_default: memory.current_pool_is_default != 0,
      resident_coefficient_bytes: self.devices.resident_bytes.lock().unwrap()
        [self.index],
      srs_point_bytes,
      msm_workspace_bytes,
    }
  }
}

pub(super) fn release_idle_device_memory() -> super::pcs::KzgIdleMemoryRelease {
  let mut report = super::pcs::KzgIdleMemoryRelease {
    cuda_enabled: true,
    ..Default::default()
  };
  let Some(devices) = DEVICES.get() else {
    return report;
  };
  let indices: Vec<_> = (0..devices.ids.len()).collect();
  let leases = devices.acquire_group(&indices);
  report.initialized = true;
  for device in &leases {
    let before = device.idle_memory(false);
    let (released_srs_point_bytes, released_msm_workspace_bytes) =
      srs_cache::release_all(device);
    let after = device.idle_memory(true);
    report.devices.push(super::pcs::KzgDeviceMemoryRelease {
      device: device.id(),
      before,
      after,
      released_srs_point_bytes,
      released_msm_workspace_bytes,
    });
  }
  report.quiesced = true;
  report
}

impl Drop for Device<'_> {
  fn drop(&mut self) {
    self.devices.busy.lock().unwrap()[self.index] = false;
    DEVICE_LEASES.set(DEVICE_LEASES.get() - 1);
    self.devices.available.notify_all();
  }
}

struct Reservation {
  index: usize,
  bytes: usize,
}

impl Drop for Reservation {
  fn drop(&mut self) {
    Devices::get().resident_bytes.lock().unwrap()[self.index] -= self.bytes;
  }
}

/// Immutable device coefficients; every native use holds this device's lease.
/// Host coefficients remain the recovery source when the residency budget is
/// full.
pub(super) struct ResidentPolynomial {
  reservation: Reservation,
  context: usize,
}

impl Drop for ResidentPolynomial {
  fn drop(&mut self) {
    let device = Devices::get().acquire_at(self.reservation.index);
    // Native destruction waits for all streams before the budget is returned.
    let code = unsafe {
      ix_kzg_polynomial_destroy(device.id(), self.context as *mut c_void)
    };
    if code != 0 {
      tracing::error!(code, "KZG resident polynomial destruction failed");
    }
  }
}

pub(super) fn retain(coefficients: &[Fr]) -> Option<Arc<ResidentPolynomial>> {
  if coefficients.len() < 1 << 16 {
    return None;
  }
  let devices = Devices::get();
  let reservation =
    devices.reserve(coefficients.len().checked_mul(32).unwrap())?;
  let device = devices.acquire_at(reservation.index);
  if !device.prepare_budget(reservation.bytes + (1 << 30)) {
    return None;
  }
  let mut context = std::ptr::null_mut();
  // The native handle owns immutable storage and synchronizes its upload.
  check(
    unsafe {
      ix_kzg_polynomial_upload(
        device.id(),
        coefficients.as_ptr().cast(),
        coefficients.len(),
        &mut context,
      )
    },
    "retain polynomial",
  );
  Some(Arc::new(ResidentPolynomial { reservation, context: context as usize }))
}

/// Assign resident inputs to their owning device, balancing host inputs
/// across the remaining queues. Each queue has at most two full-size working
/// buffers.
pub(super) fn fft_columns(
  inputs: &[(&[Fr], Option<&ResidentPolynomial>)],
  lg: usize,
  inverse: bool,
  shift: Fr,
) -> Vec<Vec<Fr>> {
  assert!(lg <= 31 && !shift.is_zero());
  let count = 1usize << lg;
  assert!(inputs.iter().all(|(input, _)| input.len() <= count));
  if inputs.is_empty() {
    return vec![];
  }
  let devices = Devices::get();
  let mut groups = vec![Vec::new(); devices.ids.len()];
  for (column, (_, resident)) in inputs.iter().enumerate() {
    if let Some(resident) = resident {
      groups[resident.reservation.index].push(column);
    }
  }
  for (column, (_, resident)) in inputs.iter().enumerate() {
    if resident.is_none() {
      let index = (0..groups.len()).min_by_key(|&i| groups[i].len()).unwrap();
      groups[index].push(column);
    }
  }
  let shift = if inverse { shift.inverse().unwrap() } else { shift };
  let groups: Vec<_> = groups
    .into_par_iter()
    .enumerate()
    .filter(|(_, g)| !g.is_empty())
    .map(|(index, group)| {
      let started = std::time::Instant::now();
      let device = devices.acquire_at(index);
      let wait_seconds = started.elapsed().as_secs_f64();
      device.prepare_budget(count * 32 * group.len().min(2) + (1 << 30));
      let workspace = device.budget().saturating_sub(1 << 30);
      let slots = (workspace / (count * 32)).min(2).min(group.len());
      assert!(slots > 0, "insufficient free VRAM for KZG FFT queue");
      let mut outputs: Vec<_> =
        group.iter().map(|_| Vec::<Fr>::with_capacity(count)).collect();
      let jobs: Vec<_> = group
        .iter()
        .zip(&mut outputs)
        .map(|(&column, output)| {
          let (input, resident) = inputs[column];
          FftJob {
            input: input.as_ptr().cast(),
            resident_input: resident
              .map_or(std::ptr::null(), |r| r.context as *const c_void),
            output: output.spare_capacity_mut().as_mut_ptr().cast(),
            input_count: input.len(),
            resident_output: std::ptr::null_mut(),
          }
        })
        .collect();
      let started = std::time::Instant::now();
      // Native queues drain both streams on success and failure. Only a
      // successful call initializes every field in each output allocation.
      check(
        unsafe {
          ix_kzg_fft_batch(
            device.id(),
            jobs.as_ptr(),
            jobs.len(),
            u32::try_from(lg).expect("domain log size"),
            inverse,
            &shift.0.0,
            slots,
          )
        },
        "FFT queue",
      );
      for output in &mut outputs {
        unsafe { output.set_len(count) };
      }
      tracing::debug!(
        device = device.id(),
        columns = jobs.len(),
        elements = count,
        slots,
        wait_seconds,
        cuda_seconds = started.elapsed().as_secs_f64(),
        "KZG FFT queue"
      );
      group.into_iter().zip(outputs).collect::<Vec<_>>()
    })
    .collect();
  let mut outputs = vec![Vec::new(); inputs.len()];
  for (index, output) in groups.into_iter().flatten() {
    outputs[index] = output;
  }
  outputs
}

/// Interpolate owned columns in place on the host while retaining admitted
/// device outputs. A native queue owns unfinished outputs until it drains.
pub(super) fn interpolate_columns(
  columns: Vec<Vec<Fr>>,
  lg: usize,
  shift: Fr,
) -> (Vec<Vec<Fr>>, Vec<Option<Arc<ResidentPolynomial>>>) {
  assert!(lg <= 31 && !shift.is_zero());
  let count = 1usize << lg;
  let devices = Devices::get();
  let mut groups: Vec<Vec<_>> =
    (0..devices.ids.len()).map(|_| Vec::new()).collect();
  let width = columns.len();
  for (column, values) in columns.into_iter().enumerate() {
    assert_eq!(values.len(), count);
    let reservation =
      if count >= 1 << 16 { devices.reserve(count * 32) } else { None };
    let index = reservation.as_ref().map_or_else(
      || (0..groups.len()).min_by_key(|&i| groups[i].len()).unwrap(),
      |r| r.index,
    );
    groups[index].push((column, values, reservation));
  }
  let shift = shift.inverse().unwrap();
  let parts: Vec<_> = groups
    .into_par_iter()
    .enumerate()
    .filter(|(_, group)| !group.is_empty())
    .map(|(index, mut group)| {
      let device = devices.acquire_at(index);
      let bytes = count * 32;
      // All retained outputs survive the queue. Count them in addition to
      // the two transient slots, even though their lifetimes overlap.
      let retained =
        group.iter().filter(|(_, _, r)| r.is_some()).count() * bytes;
      device.prepare_budget(retained + bytes * group.len().min(2) + (1 << 30));
      let budget = device.budget().saturating_sub(1 << 30);
      if retained + bytes > budget {
        for (_, _, reservation) in &mut group {
          *reservation = None;
        }
      }
      let retained =
        group.iter().filter(|(_, _, r)| r.is_some()).count() * bytes;
      let slots = ((budget - retained) / bytes).min(2).min(group.len());
      assert!(slots > 0, "insufficient free VRAM for KZG interpolation queue");
      let mut handles = vec![std::ptr::null_mut(); group.len()];
      let jobs: Vec<_> = group
        .iter_mut()
        .zip(&mut handles)
        .map(|((_, values, reservation), handle)| FftJob {
          input: values.as_ptr().cast(),
          resident_input: std::ptr::null(),
          output: values.as_mut_ptr().cast(),
          input_count: count,
          resident_output: if reservation.is_some() {
            handle
          } else {
            std::ptr::null_mut()
          },
        })
        .collect();
      let started = std::time::Instant::now();
      let code = unsafe {
        ix_kzg_fft_batch(
          device.id(),
          jobs.as_ptr(),
          jobs.len(),
          u32::try_from(lg).expect("domain log size"),
          true,
          &shift.0.0,
          slots,
        )
      };
      // A later job can fail after an earlier retained output completed.
      // Reclaim those handles while the lease still excludes native users.
      if code != 0 {
        for handle in handles.into_iter().filter(|p| !p.is_null()) {
          unsafe { ix_kzg_polynomial_destroy(device.id(), handle) };
        }
        check(code, "interpolation queue");
        unreachable!();
      }
      tracing::debug!(
        device = device.id(),
        columns = group.len(),
        elements = count,
        slots,
        resident_bytes = retained,
        cuda_seconds = started.elapsed().as_secs_f64(),
        "KZG interpolation queue"
      );
      drop(device);
      group
        .into_iter()
        .zip(handles)
        .map(|((column, values, reservation), context)| {
          let resident = reservation.map(|reservation| {
            assert!(!context.is_null());
            Arc::new(ResidentPolynomial {
              reservation,
              context: context as usize,
            })
          });
          (column, values, resident)
        })
        .collect::<Vec<_>>()
    })
    .collect();
  let mut outputs = vec![Vec::new(); width];
  let mut residents = vec![None; width];
  for (column, values, resident) in parts.into_iter().flatten() {
    outputs[column] = values;
    residents[column] = resident;
  }
  (outputs, residents)
}

pub(super) fn msm(points: &[G1Affine], scalars: &[Fr]) -> G1Projective {
  msm_chunked(points, scalars, Devices::get().chunk_points)
}

fn msm_chunked(
  points: &[G1Affine],
  scalars: &[Fr],
  chunk_limit: usize,
) -> G1Projective {
  msm_columns_chunked(points, &[scalars], chunk_limit).remove(0)
}

pub(super) fn msm_columns(
  points: &[G1Affine],
  columns: &[&[Fr]],
) -> Vec<G1Projective> {
  msm_columns_chunked(points, columns, Devices::get().chunk_points)
}

pub(super) fn msm_columns_resident(
  points: &[G1Affine],
  columns: &[(&[Fr], Option<&ResidentPolynomial>)],
) -> Vec<G1Projective> {
  assert!(columns.iter().all(|(c, _)| c.len() == points.len()));
  if points.is_empty() {
    return vec![G1Projective::zero(); columns.len()];
  }
  let devices = Devices::get();
  let mut groups = vec![Vec::new(); devices.ids.len()];
  let mut host = Vec::new();
  for (i, (_, resident)) in columns.iter().enumerate() {
    if let Some(resident) = resident {
      groups[resident.reservation.index].push(i);
    } else {
      host.push(i);
    }
  }
  let parts: Vec<_> = groups
    .into_par_iter()
    .enumerate()
    .filter(|(_, g)| !g.is_empty())
    .map(|(index, group)| {
      let device = devices.acquire_at(index);
      device.prepare_budget(
        devices.chunk_points.min(points.len()) * 384 + (1 << 30),
      );
      let chunk =
        devices.chunk_points.min(device.budget().saturating_sub(1 << 30) / 384);
      assert!(chunk > 0, "insufficient free VRAM for KZG MSM");
      let mut sums = vec![G1Projective::zero(); group.len()];
      for (part, points) in points.chunks(chunk).enumerate() {
        let resident_points = upload_msm_points(&device, points);
        let start = part * chunk;
        for (sum, &column) in sums.iter_mut().zip(&group) {
          let (coefficients, resident) = columns[column];
          let input = &coefficients[start..start + points.len()];
          let normalization = msm_normalization(input);
          let mut out = [[0; 6]; 3];
          // Resident coefficients are read-only. Normalization uses a
          // bounded temporary on the same device as this SRS chunk.
          check(
            unsafe {
              ix_kzg_msm_invoke_resident(
                device.id(),
                resident_points.context,
                &mut out,
                resident.unwrap().context as *const c_void,
                start,
                points.len(),
                normalization
                  .as_ref()
                  .map_or(std::ptr::null(), |(_, inverse)| &inverse.0.0),
              )
            },
            "resident scalar MSM",
          );
          let point = projective(out);
          *sum += normalization.map_or(point, |(scale, _)| point * scale);
        }
      }
      group.into_iter().zip(sums).collect::<Vec<_>>()
    })
    .collect();
  let mut sums = vec![G1Projective::zero(); columns.len()];
  for (i, point) in parts.into_iter().flatten() {
    sums[i] = point;
  }
  if !host.is_empty() {
    let inputs: Vec<_> = host.iter().map(|&i| columns[i].0).collect();
    for (i, point) in host.into_iter().zip(msm_columns(points, &inputs)) {
      sums[i] = point;
    }
  }
  sums
}

fn projective(limbs: [[u64; 6]; 3]) -> G1Projective {
  G1Projective::new_unchecked(
    Fq::new_unchecked(BigInt(limbs[0])),
    Fq::new_unchecked(BigInt(limbs[1])),
    Fq::new_unchecked(BigInt(limbs[2])),
  )
}

fn upload_msm_points<'lease, 'devices>(
  device: &'lease Device<'devices>,
  points: &[G1Affine],
) -> ResidentMsm<'lease, 'devices> {
  let mut context = std::ptr::null_mut();
  // The layout-checked arkworks storage stays borrowed through the upload.
  // Native conversion preserves infinity without a polynomial-sized host copy.
  check(
    unsafe {
      ix_kzg_msm_create(
        device.id(),
        &mut context,
        points.as_ptr().cast(),
        points.len(),
      )
    },
    "MSM point upload",
  );
  assert!(!context.is_null());
  ResidentMsm { device, context }
}

struct ResidentMsm<'lease, 'devices> {
  device: &'lease Device<'devices>,
  context: *mut c_void,
}

impl Drop for ResidentMsm<'_, '_> {
  fn drop(&mut self) {
    // The borrowed lease outlives the native points and bucket workspace.
    unsafe { ix_kzg_msm_destroy(self.device.id(), self.context) };
  }
}

fn msm_normalization(scalars: &[Fr]) -> Option<(Fr, Fr)> {
  if scalars.len() < 4096 {
    return None;
  }
  sample_normalization(
    (0usize..128)
      .map(|i| scalars[i.wrapping_mul(0x9e37_79b9_7f4a_7c15) % scalars.len()]),
  )
}

fn sample_normalization(samples: impl Iterator<Item = Fr>) -> Option<(Fr, Fr)> {
  let mut counts = HashMap::new();
  for value in samples {
    if !value.is_zero() {
      *counts.entry(value.min(-value)).or_insert(0usize) += 1;
    }
  }
  let (scale, count) =
    counts.into_iter().max_by_key(|&(scale, count)| (count, scale))?;
  if count < 16 || scale == Fr::ONE || scale == -Fr::ONE {
    return None;
  }
  // Equal nonunit scalars overload one serial Pippenger bucket per window.
  // Scaling them to +/-1 uses sppark's parallel addition path; multiplying
  // the resulting point by `scale` restores the original MSM exactly.
  Some((scale, scale.inverse().unwrap()))
}

fn msm_columns_chunked(
  points: &[G1Affine],
  columns: &[&[Fr]],
  chunk_limit: usize,
) -> Vec<G1Projective> {
  assert!(columns.iter().all(|column| column.len() == points.len()));
  if points.is_empty() || columns.is_empty() {
    return vec![G1Projective::zero(); columns.len()];
  }
  assert!(chunk_limit > 0);
  let devices = Devices::get();
  let chunk = points.len().div_ceil(devices.ids.len()).min(chunk_limit).max(1);
  points
    .par_chunks(chunk)
    .enumerate()
    .map(|(chunk_index, points)| {
      let device = devices.acquire();
      device.prepare_budget(points.len() * 384 + (1 << 30));
      // The largest window uses < 1 GiB of buckets. Resident affine points,
      // scalars, signed digits and sorting scratch fit in 384 B/point.
      let admitted = device.budget().saturating_sub(1 << 30) / 384;
      assert!(admitted > 0, "insufficient free VRAM for KZG MSM");
      let mut sums = vec![G1Projective::zero(); columns.len()];
      for (part, points) in points.chunks(admitted).enumerate() {
        let start = chunk_index * chunk + part * admitted;
        let count = points.len();
        let resident = upload_msm_points(&device, points);
        for (sum, column) in sums.iter_mut().zip(columns) {
          let input = &column[start..start + count];
          let normalization = msm_normalization(input);
          let mut out = [[0; 6]; 3];
          // The resident point chunk is immutable across all column calls.
          check(
            unsafe {
              ix_kzg_msm_invoke(
                device.id(),
                resident.context,
                &mut out,
                input.as_ptr().cast(),
                count,
                normalization
                  .as_ref()
                  .map_or(std::ptr::null(), |(_, inverse)| &inverse.0.0),
              )
            },
            "MSM",
          );
          let point = projective(out);
          *sum += match normalization {
            Some((scale, _)) => point * scale,
            None => point,
          };
        }
      }
      sums
    })
    .reduce(
      || vec![G1Projective::zero(); columns.len()],
      |mut sums, parts| {
        for (sum, part) in sums.iter_mut().zip(parts) {
          *sum += part;
        }
        sums
      },
    )
}

#[cfg(test)]
pub(super) fn fft(values: &mut [Fr], inverse: bool, shift: Fr) {
  // sppark's 32-bit domain stride cannot represent 2^32.
  assert!(values.len().is_power_of_two() && values.len().ilog2() <= 31);
  assert!(!shift.is_zero());
  if values.len() == 1 {
    return;
  }
  let started = std::time::Instant::now();
  let device = Devices::get().acquire();
  let wait_seconds = started.elapsed().as_secs_f64();
  assert!(
    device.prepare_budget(values.len().checked_mul(32).unwrap() + (1 << 30)),
    "insufficient free VRAM for KZG FFT"
  );
  let shift = if inverse { shift.inverse().unwrap() } else { shift };
  let started = std::time::Instant::now();
  // sppark normalizes inverse NTTs. Coset powers act on coefficients, before
  // the forward transform or after the inverse transform in natural order.
  check(
    // The asserted layout covers every byte of each field. The exclusive
    // slice remains borrowed until all native transfers have completed.
    unsafe {
      ix_kzg_fft(
        device.id(),
        values.as_mut_ptr().cast(),
        values.len().ilog2(),
        inverse,
        &shift.0.0,
      )
    },
    "FFT",
  );
  let cuda_seconds = started.elapsed().as_secs_f64();
  tracing::debug!(
    device = device.id(),
    elements = values.len(),
    wait_seconds,
    cuda_seconds,
    "KZG FFT transfer profile"
  );
}

#[cfg(test)]
pub(super) fn fft_from(coefficients: &[Fr], lg: usize, shift: Fr) -> Vec<Fr> {
  assert!(lg <= 31 && !shift.is_zero());
  let count = 1usize << lg;
  assert!(coefficients.len() <= count);
  let device = Devices::get().acquire();
  assert!(
    device.prepare_budget(count * 32 + (1 << 30)),
    "insufficient free VRAM for KZG FFT"
  );
  let mut values = Vec::<Fr>::with_capacity(count);
  // Input limbs have the checked layout above. CUDA initializes the entire
  // output before its length is set; failure leaves an empty, droppable Vec.
  check(
    unsafe {
      ix_kzg_fft_from(
        device.id(),
        coefficients.as_ptr().cast(),
        coefficients.len(),
        values.spare_capacity_mut().as_mut_ptr().cast(),
        u32::try_from(lg).expect("domain log size"),
        false,
        &shift.0.0,
      )
    },
    "out-of-place FFT",
  );
  unsafe { values.set_len(count) };
  values
}

#[cfg(test)]
pub(super) fn evaluate_many(coefficients: &[Fr], points: &[Fr]) -> Vec<Fr> {
  evaluate_resident(coefficients, None, points)
}

pub(super) fn evaluate_resident(
  coefficients: &[Fr],
  resident: Option<&ResidentPolynomial>,
  points: &[Fr],
) -> Vec<Fr> {
  if points.is_empty() {
    return vec![];
  }
  if coefficients.len() < 2 {
    return vec![
      coefficients.first().copied().unwrap_or(Fr::ZERO);
      points.len()
    ];
  }
  let devices = Devices::get();
  let device = resident.map_or_else(
    || devices.acquire(),
    |r| devices.acquire_at(r.reservation.index),
  );
  let bytes = points
    .len()
    .checked_mul(64)
    .and_then(|bytes| {
      bytes.checked_add(if resident.is_some() {
        0
      } else {
        coefficients.len().checked_mul(32)?
      })
    })
    .and_then(|bytes| bytes.checked_add(1 << 30))
    .expect("KZG evaluation size overflow");
  assert!(
    device.prepare_budget(bytes),
    "insufficient free VRAM for KZG evaluation"
  );
  let mut results = Vec::<Fr>::with_capacity(points.len());
  // Coefficients are immutable for the entire call. The resident handle is
  // tied to its owning device and results keep point order, with repeats.
  check(
    unsafe {
      ix_kzg_evaluate_resident(
        device.id(),
        coefficients.as_ptr().cast(),
        resident.map_or(std::ptr::null(), |r| r.context as *const c_void),
        coefficients.len(),
        points.as_ptr().cast(),
        points.len(),
        results.spare_capacity_mut().as_mut_ptr().cast(),
      )
    },
    "polynomial evaluation",
  );
  unsafe { results.set_len(points.len()) };
  results
}

pub(super) fn divide(coefficients: &[Fr], z: Fr) -> Vec<Fr> {
  if coefficients.len() < 2 {
    return vec![];
  }
  // Parallel first-touch keeps page faults out of the pinned-ring download.
  let mut values =
    super::buffer::generate(coefficients.len() - 1, |_| Fr::ZERO);
  let device = Devices::get().acquire();
  assert!(
    device
      .prepare_budget(coefficients.len().checked_mul(32).unwrap() + (1 << 30)),
    "insufficient free VRAM for KZG division"
  );
  // The call synchronizes its copies and kernels before releasing buffers.
  check(
    unsafe {
      ix_kzg_divide(
        device.id(),
        coefficients.as_ptr().cast(),
        values.as_mut_ptr().cast(),
        coefficients.len(),
        &z.0.0,
      )
    },
    "polynomial division",
  );
  values
}

pub(super) fn single_device_opening(
  points: &[G1Affine],
  coefficients: &[Fr],
  z: Fr,
) -> Option<G1Projective> {
  // A quotient on one card loses the multi-device MSM partitioning benefit.
  if Devices::get().ids.len() != 1 {
    return None;
  }
  divide_and_msm(points, coefficients, z)
}

/// Divide and commit without a polynomial-sized download or scalar re-upload.
/// The quotient and its MSM scratch must fit together under one device lease.
fn divide_and_msm(
  points: &[G1Affine],
  coefficients: &[Fr],
  z: Fr,
) -> Option<G1Projective> {
  divide_and_msm_chunked(points, coefficients, z, Devices::get().chunk_points)
}

fn divide_and_msm_chunked(
  points: &[G1Affine],
  coefficients: &[Fr],
  z: Fr,
  chunk_limit: usize,
) -> Option<G1Projective> {
  assert_eq!(points.len(), coefficients.len().saturating_sub(1));
  if points.is_empty() {
    return Some(G1Projective::zero());
  }
  let devices = Devices::get();
  let device = devices.acquire();
  device.prepare_budget(
    coefficients
      .len()
      .checked_mul(32)?
      .checked_add(1 << 30)?
      .checked_add(chunk_limit.min(points.len()).checked_mul(384)?)?,
  );
  let chunk = opening_chunk(coefficients.len(), chunk_limit, device.budget())?;
  let mut context = std::ptr::null_mut();
  check(
    unsafe {
      ix_kzg_divide_resident(
        device.id(),
        coefficients.as_ptr().cast(),
        coefficients.len(),
        &z.0.0,
        &mut context,
      )
    },
    "resident polynomial division",
  );
  let quotient = LeasedPolynomial { device: &device, context };
  Some(commit_leased_quotient(&quotient, points, chunk))
}

fn opening_chunk(
  count: usize,
  chunk_limit: usize,
  budget: usize,
) -> Option<usize> {
  let fixed = count.checked_mul(32)?.checked_add(1 << 30)?;
  let chunk = chunk_limit.min(budget.checked_sub(fixed)? / 384);
  (chunk > 0).then_some(chunk)
}

fn commit_leased_quotient(
  quotient: &LeasedPolynomial<'_, '_>,
  points: &[G1Affine],
  chunk: usize,
) -> G1Projective {
  let device = quotient.device;
  let mut result = G1Projective::zero();
  for (part, points) in points.chunks(chunk).enumerate() {
    let offset = part * chunk;
    let mut samples = [Fr::ZERO; 128];
    let normalization = if points.len() >= 4096 {
      check(
        unsafe {
          ix_kzg_polynomial_sample(
            device.id(),
            quotient.context,
            offset,
            points.len(),
            samples.as_mut_ptr().cast(),
          )
        },
        "resident scalar sample",
      );
      sample_normalization(samples.into_iter())
    } else {
      None
    };
    let resident_points = upload_msm_points(device, points);
    let mut out = [[0; 6]; 3];
    check(
      unsafe {
        ix_kzg_msm_invoke_resident(
          device.id(),
          resident_points.context,
          &mut out,
          quotient.context,
          offset,
          points.len(),
          normalization
            .as_ref()
            .map_or(std::ptr::null(), |(_, inverse)| &inverse.0.0),
        )
      },
      "opening witness MSM",
    );
    let point = projective(out);
    result += normalization.map_or(point, |(scale, _)| point * scale);
  }
  result
}

struct LeasedPolynomial<'lease, 'devices> {
  device: &'lease Device<'devices>,
  context: *mut c_void,
}

impl Drop for LeasedPolynomial<'_, '_> {
  fn drop(&mut self) {
    // The existing lease covers destruction; reacquiring it would deadlock.
    let code =
      unsafe { ix_kzg_polynomial_destroy(self.device.id(), self.context) };
    if code != 0 {
      tracing::error!(code, "KZG temporary polynomial destruction failed");
    }
  }
}
