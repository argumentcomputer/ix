//! Bounded, synchronous KZG operations on the visible sppark devices for both
//! BN254 (`libix_bn254_cuda.so`) and BLS12-381 (`libix_bls12_381_cuda.so`).
//!
//! With this feature compiled, every proving operation above the size
//! thresholds in the prover runs on the devices; only tiny shapes and
//! disk-backed columns use the host implementation. Memory admission is
//! checked before each operation and a rejected admission is an error, as is
//! any failure after a native operation has started. Every native call holds
//! a device lease; leases are per thread and refuse reentrant acquisition so
//! Rayon work stealing cannot deadlock a worker on its own device.

use super::curve::{G1AffineOf, G1ProjectiveOf, KzgCurve};
use ark_ff::{Field, Zero};
use blst as _;
use rayon::prelude::*;
use std::cell::Cell;
use std::collections::HashMap;
use std::ffi::c_void;
use std::marker::PhantomData;
use std::sync::{Arc, Condvar, Mutex, OnceLock};

mod abi;
pub(super) mod lookup;
mod passes;
pub(super) mod quotient;
pub(super) mod srs_residency;
#[cfg(test)]
mod tests;

#[doc(hidden)]
pub use abi::CudaCurve;
#[doc(hidden)]
pub use srs_residency::Cache as SrsCache;

// Conservative bound for point storage, upload staging, scalars, signed
// digits and sorting scratch. Buckets use separate headroom; Fq coordinate
// widths do not determine scalar and sorting allocation sizes.
const MSM_BYTES_PER_POINT: usize = 384;

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
  /// adapts to each device's VRAM (`total / 3`, capped by `total / 2` and
  /// free memory minus the standing reserve) so lookup and quotient working
  /// sets stay admitted beside retained columns on both 24 GiB and 80+ GiB GPUs.
  pub resident_limit_bytes: Option<usize>,
  /// Keep uploaded SRS ranges resident across operations (evictable under
  /// memory pressure).
  pub srs_cache: bool,
  pub passes: PassMode,
}

impl Default for Settings {
  fn default() -> Self {
    Self {
      devices: None,
      msm_chunk_points: 1 << 24,
      resident_limit_bytes: None,
      srs_cache: true,
      passes: PassMode::Fallback,
    }
  }
}

/// Standing VRAM reserve kept free for the CUDA driver and runtime:
/// bounded by `min(total / 10, 4 GiB)` instead of a fixed 25% share.
const fn vram_reserve(total: usize) -> usize {
  let tenth = total / 10;
  let cap = 4 << 30;
  if tenth < cap { tenth } else { cap }
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
#[doc(hidden)]
pub struct FftJob {
  input: *const [u64; 4],
  resident_input: *const c_void,
  output: *mut [u64; 4],
  input_count: usize,
  resident_output: *mut *mut c_void,
}

/// An NVTX range on the calling host thread, closed when dropped.
pub(super) struct ProfileRange<C: KzgCurve>(PhantomData<(std::rc::Rc<()>, C)>);

impl<C: KzgCurve> ProfileRange<C> {
  pub(super) fn new(name: &std::ffi::CStr) -> Self {
    unsafe { C::ffi_range_push(name.as_ptr()) };
    Self(PhantomData)
  }
}

impl<C: KzgCurve> Drop for ProfileRange<C> {
  fn drop(&mut self) {
    unsafe { C::ffi_range_pop() };
  }
}

fn check(code: i32, operation: &str) {
  assert_eq!(code, 0, "KZG CUDA {operation} failed (CUDA status {code})");
}

#[doc(hidden)]
pub struct Devices {
  ids: Vec<i32>,
  busy: Mutex<Vec<bool>>,
  available: Condvar,
  chunk_points: usize,
  resident_bytes: Mutex<Vec<usize>>,
  resident_limits: Vec<usize>,
}

thread_local! {
  static DEVICE_LEASES: Cell<usize> = const { Cell::new(0) };
}

impl Devices {
  fn potential_budget<C: KzgCurve>(&self, index: usize) -> usize {
    let (mut free, mut total) = (0, 0);
    check(
      unsafe { C::ffi_memory(self.ids[index], &mut free, &mut total) },
      "memory query",
    );
    free
      .saturating_add(srs_residency::reclaimable::<C>(index))
      .saturating_sub(vram_reserve(total))
  }

  fn get<C: KzgCurve>() -> &'static Self {
    C::devices_slot().get_or_init(|| {
      abi::validate::<C>();
      let settings = settings();
      let mut count = 0;
      // The FFI writes one integer and initializes sppark's device registry.
      check(unsafe { C::ffi_devices(&mut count) }, "device discovery");
      assert!(
        count > 0,
        "the KZG CUDA backend requires a visible compatible CUDA GPU (compiled SM architectures: {}); build without the cuda feature for host execution",
        env!("IX_KZG_CUDA_COMPILED_ARCHS")
      );
      let supported: Vec<i32> = (0..count)
        .map(|index| {
          let mut ordinal = -1;
          // Logical sppark indices need not match CUDA ordinals on mixed hosts.
          check(
            unsafe { C::ffi_device_ordinal(index, &mut ordinal) },
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
          supported.contains(&id),
          "unsupported KZG CUDA ordinal {id}; compiled SM architectures: {}",
          env!("IX_KZG_CUDA_COMPILED_ARCHS")
        );
        assert!(!ids[..i].contains(&id), "duplicate KZG CUDA ordinal {id}");
      }
      let chunk_points = settings.msm_chunk_points;
      let resident_limits: Vec<_> = ids
        .iter()
        .map(|&id| {
          let (mut free, mut total) = (0, 0);
          check(
            unsafe { C::ffi_memory(id, &mut free, &mut total) },
            "memory query",
          );
          let reserve = vram_reserve(total);
          settings
            .resident_limit_bytes
            .unwrap_or(total / 3)
            .min(total / 2)
            .min(free.saturating_sub(reserve))
        })
        .collect();
      tracing::info!(
        curve = C::NAME,
        ?ids,
        chunk_points,
        ?resident_limits,
        "KZG sppark CUDA backend"
      );
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

  fn acquire_admitted(
    &self,
    preferred: &[usize],
    mut admit: impl FnMut(&Device<'_>) -> bool,
  ) -> Option<Device<'_>> {
    Device::assert_unleased();
    let mut pending = preferred.to_vec();
    while !pending.is_empty() {
      let device = {
        let mut busy = self.busy.lock().unwrap();
        loop {
          if let Some(position) = pending.iter().position(|&i| !busy[i]) {
            let index = pending.remove(position);
            busy[index] = true;
            break Device::new(self, index);
          }
          busy = self.available.wait(busy).unwrap();
        }
      };
      // A busy operation's scratch is temporary. Only its released device
      // can report the capacity available for the next operation.
      if admit(&device) {
        return Some(device);
      }
    }
    None
  }

  fn reserve<C: KzgCurve>(&self, bytes: usize) -> Option<Reservation<C>> {
    let mut retained = self.resident_bytes.lock().unwrap();
    let index = (0..self.ids.len())
      .filter(|&i| bytes <= self.resident_limits[i].saturating_sub(retained[i]))
      .min_by_key(|&i| retained[i])?;
    retained[index] += bytes;
    Some(Reservation { index, bytes, _curve: PhantomData })
  }
}

struct Device<'a> {
  devices: &'a Devices,
  index: usize,
  // Thread-local accounting requires release on the acquiring thread.
  _thread: PhantomData<std::rc::Rc<()>>,
}

impl<'a> Device<'a> {
  fn new(devices: &'a Devices, index: usize) -> Self {
    DEVICE_LEASES.set(DEVICE_LEASES.get() + 1);
    Self { devices, index, _thread: PhantomData }
  }

  fn assert_unleased() {
    // Nested Rayon work can steal a job that waits for its own thread's lease.
    assert_eq!(DEVICE_LEASES.get(), 0, "reentrant KZG device lease");
  }

  fn prepare_budget<C: KzgCurve>(&self, required: usize) -> bool {
    srs_residency::prepare_budget::<C>(self, required)
  }

  fn id(&self) -> i32 {
    self.devices.ids[self.index]
  }

  fn budget<C: KzgCurve>(&self) -> usize {
    let (mut free, mut total) = (0, 0);
    // The lease excludes other KZG operations on these sppark streams.
    check(
      unsafe { C::ffi_memory(self.id(), &mut free, &mut total) },
      "memory query",
    );
    free.saturating_sub(vram_reserve(total))
  }
}

impl Drop for Device<'_> {
  fn drop(&mut self) {
    self.devices.busy.lock().unwrap()[self.index] = false;
    DEVICE_LEASES.set(DEVICE_LEASES.get() - 1);
    self.devices.available.notify_all();
  }
}

struct Reservation<C: KzgCurve> {
  index: usize,
  bytes: usize,
  _curve: PhantomData<C>,
}

impl<C: KzgCurve> Drop for Reservation<C> {
  fn drop(&mut self) {
    Devices::get::<C>().resident_bytes.lock().unwrap()[self.index] -=
      self.bytes;
  }
}

/// Immutable device coefficients; every native use holds this device's lease.
/// Host coefficients remain the recovery source when the residency budget is
/// full.
pub(super) struct ResidentPolynomial<C: KzgCurve> {
  reservation: Reservation<C>,
  context: usize,
}

impl<C: KzgCurve> Drop for ResidentPolynomial<C> {
  fn drop(&mut self) {
    let device = Devices::get::<C>().acquire_at(self.reservation.index);
    // Native destruction waits for all streams before the budget is returned.
    let code = unsafe {
      C::ffi_polynomial_destroy(device.id(), self.context as *mut c_void)
    };
    if code != 0 {
      tracing::error!(
        curve = C::NAME,
        code,
        "KZG resident polynomial destruction failed"
      );
    }
  }
}

pub(super) fn retain<C: KzgCurve>(
  coefficients: &[C::Fr],
) -> Option<Arc<ResidentPolynomial<C>>> {
  if coefficients.len() < 1 << 16 {
    return None;
  }
  let devices = Devices::get::<C>();
  let reservation =
    devices.reserve::<C>(coefficients.len().checked_mul(32).unwrap())?;
  let device = devices.acquire_at(reservation.index);
  if !device.prepare_budget::<C>(reservation.bytes + (1 << 30)) {
    return None;
  }
  let mut context = std::ptr::null_mut();
  // The native handle owns immutable storage and synchronizes its upload.
  check(
    unsafe {
      C::ffi_polynomial_upload(
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
pub(super) fn fft_columns<C: KzgCurve>(
  inputs: &[(&[C::Fr], Option<&ResidentPolynomial<C>>)],
  lg: usize,
  inverse: bool,
  shift: C::Fr,
) -> Vec<Vec<C::Fr>> {
  assert!(lg <= C::MAX_FFT_LOG, "unsupported KZG CUDA FFT domain");
  assert!(!shift.is_zero());
  let count = 1usize << lg;
  assert!(inputs.iter().all(|(input, _)| input.len() <= count));
  if inputs.is_empty() {
    return vec![];
  }
  let devices = Devices::get::<C>();
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
      device.prepare_budget::<C>(count * 32 * group.len().min(2) + (1 << 30));
      let workspace = device.budget::<C>().saturating_sub(1 << 30);
      let slots = (workspace / (count * 32)).min(2).min(group.len());
      assert!(slots > 0, "insufficient free VRAM for KZG FFT queue");
      let mut outputs: Vec<_> =
        group.iter().map(|_| Vec::<C::Fr>::with_capacity(count)).collect();
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
          C::ffi_fft_batch(
            device.id(),
            jobs.as_ptr().cast(),
            jobs.len(),
            u32::try_from(lg).expect("domain log size"),
            inverse,
            C::fr_mont_limbs_ref(&shift),
            slots,
          )
        },
        "FFT queue",
      );
      for output in &mut outputs {
        unsafe { output.set_len(count) };
      }
      tracing::debug!(
        curve = C::NAME,
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
pub(super) fn interpolate_columns<C: KzgCurve>(
  columns: Vec<Vec<C::Fr>>,
  lg: usize,
  shift: C::Fr,
) -> (Vec<Vec<C::Fr>>, Vec<Option<Arc<ResidentPolynomial<C>>>>) {
  assert!(lg <= C::MAX_FFT_LOG, "unsupported KZG CUDA FFT domain");
  assert!(!shift.is_zero());
  let count = 1usize << lg;
  let devices = Devices::get::<C>();
  let mut groups: Vec<Vec<_>> =
    (0..devices.ids.len()).map(|_| Vec::new()).collect();
  let width = columns.len();
  for (column, values) in columns.into_iter().enumerate() {
    assert_eq!(values.len(), count);
    let reservation =
      if count >= 1 << 16 { devices.reserve::<C>(count * 32) } else { None };
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
      device
        .prepare_budget::<C>(retained + bytes * group.len().min(2) + (1 << 30));
      let budget = device.budget::<C>().saturating_sub(1 << 30);
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
        C::ffi_fft_batch(
          device.id(),
          jobs.as_ptr().cast(),
          jobs.len(),
          u32::try_from(lg).expect("domain log size"),
          true,
          C::fr_mont_limbs_ref(&shift),
          slots,
        )
      };
      check(code, "interpolation queue");
      tracing::debug!(
        curve = C::NAME,
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

pub(super) fn msm<C: KzgCurve>(
  points: &[G1AffineOf<C>],
  scalars: &[C::Fr],
) -> G1ProjectiveOf<C> {
  msm_chunked::<C>(points, scalars, Devices::get::<C>().chunk_points)
}

fn msm_chunked<C: KzgCurve>(
  points: &[G1AffineOf<C>],
  scalars: &[C::Fr],
  chunk_limit: usize,
) -> G1ProjectiveOf<C> {
  msm_columns_chunked::<C>(points, &[scalars], chunk_limit).remove(0)
}

pub(super) fn msm_columns<C: KzgCurve>(
  points: &[G1AffineOf<C>],
  columns: &[&[C::Fr]],
) -> Vec<G1ProjectiveOf<C>> {
  msm_columns_chunked::<C>(points, columns, Devices::get::<C>().chunk_points)
}

pub(super) fn msm_columns_resident<C: KzgCurve>(
  points: &[G1AffineOf<C>],
  columns: &[(&[C::Fr], Option<&ResidentPolynomial<C>>)],
) -> Vec<G1ProjectiveOf<C>> {
  assert!(columns.iter().all(|(c, _)| c.len() == points.len()));
  if points.is_empty() {
    return vec![G1ProjectiveOf::<C>::zero(); columns.len()];
  }
  let devices = Devices::get::<C>();
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
      device.prepare_budget::<C>(
        devices.chunk_points.min(points.len()) * MSM_BYTES_PER_POINT
          + (1 << 30),
      );
      let chunk = devices.chunk_points.min(
        device.budget::<C>().saturating_sub(1 << 30) / MSM_BYTES_PER_POINT,
      );
      assert!(chunk > 0, "insufficient free VRAM for KZG MSM");
      let mut sums = vec![G1ProjectiveOf::<C>::zero(); group.len()];
      for (part, points) in points.chunks(chunk).enumerate() {
        let resident_points = upload_msm_points::<C>(&device, points);
        let start = part * chunk;
        for (sum, &column) in sums.iter_mut().zip(&group) {
          let (coefficients, resident) = columns[column];
          let input = &coefficients[start..start + points.len()];
          let normalization = msm_normalization::<C>(input);
          let mut out = [C::FqLimbs::default(); 3];
          // Resident coefficients are read-only. Normalization uses a
          // bounded temporary on the same device as this SRS chunk.
          check(
            unsafe {
              C::ffi_msm_invoke_resident(
                device.id(),
                resident_points.context,
                &mut out,
                resident.unwrap().context as *const c_void,
                start,
                points.len(),
                normalization
                  .as_ref()
                  .map_or(std::ptr::null(), |(_, inverse)| {
                    C::fr_mont_limbs_ref(inverse)
                  }),
              )
            },
            "resident scalar MSM",
          );
          let point = projective::<C>(out);
          *sum += normalization.map_or(point, |(scale, _)| point * scale);
        }
      }
      group.into_iter().zip(sums).collect::<Vec<_>>()
    })
    .collect();
  let mut sums = vec![G1ProjectiveOf::<C>::zero(); columns.len()];
  for (i, point) in parts.into_iter().flatten() {
    sums[i] = point;
  }
  if !host.is_empty() {
    let inputs: Vec<_> = host.iter().map(|&i| columns[i].0).collect();
    for (i, point) in host.into_iter().zip(msm_columns::<C>(points, &inputs)) {
      sums[i] = point;
    }
  }
  sums
}

fn projective<C: KzgCurve>(limbs: [C::FqLimbs; 3]) -> G1ProjectiveOf<C> {
  G1ProjectiveOf::<C>::new_unchecked(
    C::fq_from_mont_limbs_unchecked(limbs[0]),
    C::fq_from_mont_limbs_unchecked(limbs[1]),
    C::fq_from_mont_limbs_unchecked(limbs[2]),
  )
}

fn upload_msm_points<'lease, 'devices, C: KzgCurve>(
  device: &'lease Device<'devices>,
  points: &[G1AffineOf<C>],
) -> ResidentMsm<'lease, 'devices, C> {
  let mut context = std::ptr::null_mut();
  // The layout-checked arkworks storage stays borrowed through the upload.
  // Native conversion preserves infinity without a polynomial-sized host copy.
  check(
    unsafe {
      C::ffi_msm_create(
        device.id(),
        &mut context,
        points.as_ptr().cast(),
        points.len(),
      )
    },
    "MSM point upload",
  );
  assert!(!context.is_null());
  ResidentMsm { device, context, _curve: PhantomData }
}

struct ResidentMsm<'lease, 'devices, C: KzgCurve> {
  device: &'lease Device<'devices>,
  context: *mut c_void,
  _curve: PhantomData<C>,
}

impl<C: KzgCurve> Drop for ResidentMsm<'_, '_, C> {
  fn drop(&mut self) {
    // The borrowed lease outlives the native points and bucket workspace.
    unsafe { C::ffi_msm_destroy(self.device.id(), self.context) };
  }
}

fn msm_normalization<C: KzgCurve>(scalars: &[C::Fr]) -> Option<(C::Fr, C::Fr)> {
  if scalars.len() < 4096 {
    return None;
  }
  sample_normalization::<C>(
    (0usize..128)
      .map(|i| scalars[i.wrapping_mul(0x9e37_79b9_7f4a_7c15) % scalars.len()]),
  )
}

fn sample_normalization<C: KzgCurve>(
  samples: impl Iterator<Item = C::Fr>,
) -> Option<(C::Fr, C::Fr)> {
  let mut counts = HashMap::new();
  for value in samples {
    if !value.is_zero() {
      *counts.entry(value.min(-value)).or_insert(0usize) += 1;
    }
  }
  let (scale, count) =
    counts.into_iter().max_by_key(|&(scale, count)| (count, scale))?;
  if count < 16 || scale == C::FR_ONE || scale == -C::FR_ONE {
    return None;
  }
  // Equal nonunit scalars overload one serial Pippenger bucket per window.
  // Scaling them to +/-1 uses sppark's parallel addition path; multiplying
  // the resulting point by `scale` restores the original MSM exactly.
  Some((scale, scale.inverse().unwrap()))
}

fn msm_columns_chunked<C: KzgCurve>(
  points: &[G1AffineOf<C>],
  columns: &[&[C::Fr]],
  chunk_limit: usize,
) -> Vec<G1ProjectiveOf<C>> {
  assert!(columns.iter().all(|column| column.len() == points.len()));
  if points.is_empty() || columns.is_empty() {
    return vec![G1ProjectiveOf::<C>::zero(); columns.len()];
  }
  assert!(chunk_limit > 0);
  let devices = Devices::get::<C>();
  let chunk = points.len().div_ceil(devices.ids.len()).min(chunk_limit).max(1);
  points
    .par_chunks(chunk)
    .enumerate()
    .map(|(chunk_index, points)| {
      let device = devices.acquire();
      device
        .prepare_budget::<C>(points.len() * MSM_BYTES_PER_POINT + (1 << 30));
      // The largest window uses < 1 GiB of buckets. Resident affine points,
      // scalars, signed digits and sorting scratch fit in 384 B/point.
      let admitted =
        device.budget::<C>().saturating_sub(1 << 30) / MSM_BYTES_PER_POINT;
      assert!(admitted > 0, "insufficient free VRAM for KZG MSM");
      let mut sums = vec![G1ProjectiveOf::<C>::zero(); columns.len()];
      for (part, points) in points.chunks(admitted).enumerate() {
        let start = chunk_index * chunk + part * admitted;
        let count = points.len();
        let resident = upload_msm_points::<C>(&device, points);
        for (sum, column) in sums.iter_mut().zip(columns) {
          let input = &column[start..start + count];
          let normalization = msm_normalization::<C>(input);
          let mut out = [C::FqLimbs::default(); 3];
          // The resident point chunk is immutable across all column calls.
          check(
            unsafe {
              C::ffi_msm_invoke(
                device.id(),
                resident.context,
                &mut out,
                input.as_ptr().cast(),
                count,
                normalization
                  .as_ref()
                  .map_or(std::ptr::null(), |(_, inverse)| {
                    C::fr_mont_limbs_ref(inverse)
                  }),
              )
            },
            "MSM",
          );
          let point = projective::<C>(out);
          *sum += match normalization {
            Some((scale, _)) => point * scale,
            None => point,
          };
        }
      }
      sums
    })
    .reduce(
      || vec![G1ProjectiveOf::<C>::zero(); columns.len()],
      |mut sums, parts| {
        for (sum, part) in sums.iter_mut().zip(parts) {
          *sum += part;
        }
        sums
      },
    )
}

#[cfg(test)]
pub(super) fn fft<C: KzgCurve>(
  values: &mut [C::Fr],
  inverse: bool,
  shift: C::Fr,
) {
  assert!(values.len().is_power_of_two());
  assert!(
    values.len().ilog2() as usize <= C::MAX_FFT_LOG,
    "unsupported KZG CUDA FFT domain"
  );
  assert!(!shift.is_zero());
  if values.len() == 1 {
    return;
  }
  let started = std::time::Instant::now();
  let device = Devices::get::<C>().acquire();
  let wait_seconds = started.elapsed().as_secs_f64();
  assert!(
    device
      .prepare_budget::<C>(values.len().checked_mul(32).unwrap() + (1 << 30)),
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
      C::ffi_fft(
        device.id(),
        values.as_mut_ptr().cast(),
        values.len().ilog2(),
        inverse,
        C::fr_mont_limbs_ref(&shift),
      )
    },
    "FFT",
  );
  let cuda_seconds = started.elapsed().as_secs_f64();
  tracing::debug!(
    curve = C::NAME,
    device = device.id(),
    elements = values.len(),
    wait_seconds,
    cuda_seconds,
    "KZG FFT transfer profile"
  );
}

#[cfg(test)]
pub(super) fn fft_from<C: KzgCurve>(
  coefficients: &[C::Fr],
  lg: usize,
  shift: C::Fr,
) -> Vec<C::Fr> {
  assert!(lg <= C::MAX_FFT_LOG, "unsupported KZG CUDA FFT domain");
  assert!(!shift.is_zero());
  let count = 1usize << lg;
  assert!(coefficients.len() <= count);
  let device = Devices::get::<C>().acquire();
  assert!(
    device.prepare_budget::<C>(count * 32 + (1 << 30)),
    "insufficient free VRAM for KZG FFT"
  );
  let mut values = Vec::<C::Fr>::with_capacity(count);
  // Input limbs have the checked layout above. CUDA initializes the entire
  // output before its length is set; failure leaves an empty, droppable Vec.
  check(
    unsafe {
      C::ffi_fft_from(
        device.id(),
        coefficients.as_ptr().cast(),
        coefficients.len(),
        values.spare_capacity_mut().as_mut_ptr().cast(),
        u32::try_from(lg).expect("domain log size"),
        false,
        C::fr_mont_limbs_ref(&shift),
      )
    },
    "out-of-place FFT",
  );
  unsafe { values.set_len(count) };
  values
}

#[cfg(test)]
pub(super) fn evaluate_many<C: KzgCurve>(
  coefficients: &[C::Fr],
  points: &[C::Fr],
) -> Vec<C::Fr> {
  evaluate_resident::<C>(coefficients, None, points)
}

pub(super) fn evaluate_resident<C: KzgCurve>(
  coefficients: &[C::Fr],
  resident: Option<&ResidentPolynomial<C>>,
  points: &[C::Fr],
) -> Vec<C::Fr> {
  if points.is_empty() {
    return vec![];
  }
  if coefficients.len() < 2 {
    return vec![
      coefficients.first().copied().unwrap_or(C::FR_ZERO);
      points.len()
    ];
  }
  let devices = Devices::get::<C>();
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
    device.prepare_budget::<C>(bytes),
    "insufficient free VRAM for KZG evaluation"
  );
  let mut results = Vec::<C::Fr>::with_capacity(points.len());
  // Coefficients are immutable for the entire call. The resident handle is
  // tied to its owning device and results keep point order, with repeats.
  check(
    unsafe {
      C::ffi_evaluate_resident(
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

pub(super) fn divide<C: KzgCurve>(
  coefficients: &[C::Fr],
  z: C::Fr,
) -> Vec<C::Fr> {
  if coefficients.len() < 2 {
    return vec![];
  }
  // Parallel first-touch keeps page faults out of the pinned-ring download.
  let mut values =
    super::pcs::generate_buffer(coefficients.len() - 1, |_| C::FR_ZERO);
  let device = Devices::get::<C>().acquire();
  assert!(
    device.prepare_budget::<C>(
      coefficients.len().checked_mul(32).unwrap() + (1 << 30)
    ),
    "insufficient free VRAM for KZG division"
  );
  // The call synchronizes its copies and kernels before releasing buffers.
  check(
    unsafe {
      C::ffi_divide(
        device.id(),
        coefficients.as_ptr().cast(),
        values.as_mut_ptr().cast(),
        coefficients.len(),
        C::fr_mont_limbs_ref(&z),
      )
    },
    "polynomial division",
  );
  values
}

pub(super) fn single_device_opening<C: KzgCurve>(
  points: &[G1AffineOf<C>],
  coefficients: &[C::Fr],
  z: C::Fr,
) -> Option<G1ProjectiveOf<C>> {
  // A quotient on one card loses the multi-device MSM partitioning benefit.
  if Devices::get::<C>().ids.len() != 1 {
    return None;
  }
  divide_and_msm::<C>(points, coefficients, z)
}

/// Divide and commit without a polynomial-sized download or scalar re-upload.
/// The quotient and its MSM scratch must fit together under one device lease.
fn divide_and_msm<C: KzgCurve>(
  points: &[G1AffineOf<C>],
  coefficients: &[C::Fr],
  z: C::Fr,
) -> Option<G1ProjectiveOf<C>> {
  divide_and_msm_chunked::<C>(
    points,
    coefficients,
    z,
    Devices::get::<C>().chunk_points,
  )
}

fn divide_and_msm_chunked<C: KzgCurve>(
  points: &[G1AffineOf<C>],
  coefficients: &[C::Fr],
  z: C::Fr,
  chunk_limit: usize,
) -> Option<G1ProjectiveOf<C>> {
  assert_eq!(points.len(), coefficients.len().saturating_sub(1));
  if points.is_empty() {
    return Some(G1ProjectiveOf::<C>::zero());
  }
  let devices = Devices::get::<C>();
  let device = devices.acquire();
  device.prepare_budget::<C>(
    coefficients.len().checked_mul(32)?.checked_add(1 << 30)?.checked_add(
      chunk_limit.min(points.len()).checked_mul(MSM_BYTES_PER_POINT)?,
    )?,
  );
  let chunk =
    opening_chunk(coefficients.len(), chunk_limit, device.budget::<C>())?;
  let mut context = std::ptr::null_mut();
  check(
    unsafe {
      C::ffi_divide_resident(
        device.id(),
        coefficients.as_ptr().cast(),
        coefficients.len(),
        C::fr_mont_limbs_ref(&z),
        &mut context,
      )
    },
    "resident polynomial division",
  );
  let quotient =
    LeasedPolynomial::<C> { device: &device, context, _curve: PhantomData };
  Some(commit_leased_quotient::<C>(&quotient, points, chunk))
}

fn opening_chunk(
  count: usize,
  chunk_limit: usize,
  budget: usize,
) -> Option<usize> {
  let fixed = count.checked_mul(32)?.checked_add(1 << 30)?;
  let chunk = chunk_limit.min(budget.checked_sub(fixed)? / MSM_BYTES_PER_POINT);
  (chunk > 0).then_some(chunk)
}

fn commit_leased_quotient<C: KzgCurve>(
  quotient: &LeasedPolynomial<'_, '_, C>,
  points: &[G1AffineOf<C>],
  chunk: usize,
) -> G1ProjectiveOf<C> {
  let device = quotient.device;
  let mut result = G1ProjectiveOf::<C>::zero();
  for (part, points) in points.chunks(chunk).enumerate() {
    let offset = part * chunk;
    let mut samples = [C::FR_ZERO; 128];
    let normalization = if points.len() >= 4096 {
      check(
        unsafe {
          C::ffi_polynomial_sample(
            device.id(),
            quotient.context,
            offset,
            points.len(),
            samples.as_mut_ptr().cast(),
          )
        },
        "resident scalar sample",
      );
      sample_normalization::<C>(samples.into_iter())
    } else {
      None
    };
    let resident_points = upload_msm_points::<C>(device, points);
    let mut out = [C::FqLimbs::default(); 3];
    check(
      unsafe {
        C::ffi_msm_invoke_resident(
          device.id(),
          resident_points.context,
          &mut out,
          quotient.context,
          offset,
          points.len(),
          normalization.as_ref().map_or(std::ptr::null(), |(_, inverse)| {
            C::fr_mont_limbs_ref(inverse)
          }),
        )
      },
      "opening witness MSM",
    );
    let point = projective::<C>(out);
    result += normalization.map_or(point, |(scale, _)| point * scale);
  }
  result
}

struct LeasedPolynomial<'lease, 'devices, C: KzgCurve> {
  device: &'lease Device<'devices>,
  context: *mut c_void,
  _curve: PhantomData<C>,
}

impl<C: KzgCurve> Drop for LeasedPolynomial<'_, '_, C> {
  fn drop(&mut self) {
    // The existing lease covers destruction; reacquiring it would deadlock.
    let code =
      unsafe { C::ffi_polynomial_destroy(self.device.id(), self.context) };
    if code != 0 {
      tracing::error!(
        curve = C::NAME,
        code,
        "KZG temporary polynomial destruction failed"
      );
    }
  }
}
