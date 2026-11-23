//! Evictable immutable SRS ranges, independent of mutable sppark MSM scratch.

use super::*;
use crate::kzg::srs::Srs;
use std::sync::{
  Weak,
  atomic::{AtomicU64, Ordering},
};

const LIMIT: usize = 12 << 30;
const HEADROOM: usize = 1 << 30;
const MAX_CHUNK: usize = 1 << 24;
const UPLOAD_POINTS: usize = 1 << 18;

#[cfg(test)]
mod tests;

pub(in crate::kzg) struct Owner<C: KzgCurve> {
  id: u64,
  token: Arc<()>,
  srs: Arc<Srs<C>>,
}

impl<C: KzgCurve> Owner<C> {
  pub(in crate::kzg) fn new(srs: Arc<Srs<C>>) -> Arc<Self> {
    static NEXT: AtomicU64 = AtomicU64::new(1);
    let id = NEXT
      .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| {
        id.checked_add(1)
      })
      .expect("SRS cache identity exhausted");
    Arc::new(Self { id, token: Arc::new(()), srs })
  }
}

pub(in crate::kzg) fn enabled() -> bool {
  settings().srs_cache
}

struct Entry {
  owner: Weak<()>,
  id: u64,
  start: usize,
  count: usize,
  pointer: usize,
  bytes: usize,
  used: u64,
}

impl Entry {
  fn contains<C: KzgCurve>(
    &self,
    owner: &Owner<C>,
    start: usize,
    count: usize,
  ) -> bool {
    self.id == owner.id
      && start >= self.start
      && start - self.start <= self.count
      && count <= self.count - (start - self.start)
  }

  fn overlaps<C: KzgCurve>(
    &self,
    owner: &Owner<C>,
    start: usize,
    count: usize,
  ) -> bool {
    self.id == owner.id
      && self.start < start + count
      && start < self.start + self.count
  }
}

struct Workspace {
  pointer: usize,
  window: u32,
  bytes: usize,
}

#[derive(Default)]
#[doc(hidden)]
pub struct Cache {
  entries: Vec<Entry>,
  workspace: Option<Workspace>,
  clock: u64,
  hits: u64,
  uploads: u64,
  upload_bytes: u64,
  evictions: u64,
}

impl Cache {
  fn point_bytes(&self) -> usize {
    self.entries.iter().map(|entry| entry.bytes).sum()
  }
  fn bytes(&self) -> usize {
    self.point_bytes() + self.workspace.as_ref().map_or(0, |w| w.bytes)
  }

  fn evict<C: KzgCurve>(&mut self, device: &Device<'_>, index: usize) {
    let entry = self.entries.swap_remove(index);
    check(
      unsafe { C::ffi_srs_destroy(device.id(), entry.pointer as *mut c_void) },
      "SRS eviction",
    );
    self.evictions += 1;
    tracing::debug!(
      curve = C::NAME,
      device = device.id(),
      owner = entry.id,
      start = entry.start,
      bytes = entry.bytes,
      "KZG SRS cache evicted"
    );
  }

  fn drop_workspace<C: KzgCurve>(&mut self, device: &Device<'_>) {
    if let Some(workspace) = self.workspace.take() {
      check(
        unsafe {
          C::ffi_srs_workspace_destroy(
            device.id(),
            workspace.pointer as *mut c_void,
          )
        },
        "MSM workspace eviction",
      );
    }
  }

  fn purge<C: KzgCurve>(&mut self, device: &Device<'_>) {
    while let Some(index) =
      self.entries.iter().position(|entry| entry.owner.strong_count() == 0)
    {
      self.evict::<C>(device, index);
    }
  }

  fn oldest(&self) -> Option<usize> {
    self
      .entries
      .iter()
      .enumerate()
      .min_by_key(|(_, entry)| entry.used)
      .map(|(i, _)| i)
  }
}

fn caches<C: KzgCurve>() -> &'static [Mutex<Cache>] {
  C::srs_caches_slot().get_or_init(|| {
    Devices::get::<C>()
      .ids
      .iter()
      .map(|_| Mutex::new(Cache::default()))
      .collect()
  })
}

pub(super) fn reclaimable<C: KzgCurve>(index: usize) -> usize {
  caches::<C>()[index].lock().unwrap().bytes()
}

/// The caller owns the only operation lease; no cached native handle can be
/// in use.
pub(super) fn prepare_budget<C: KzgCurve>(
  device: &Device<'_>,
  required: usize,
) -> bool {
  let mut cache = caches::<C>()[device.index].lock().unwrap();
  cache.purge::<C>(device);
  while device.budget::<C>() < required {
    if let Some(index) = cache.oldest() {
      cache.evict::<C>(device, index);
    } else if cache.workspace.is_some() {
      cache.drop_workspace::<C>(device);
    } else {
      return false;
    }
  }
  true
}

struct Handles {
  points: usize,
  point_offset: usize,
  workspace: usize,
}

fn prepare<C: KzgCurve>(
  device: &Device<'_>,
  owner: &Arc<Owner<C>>,
  start: usize,
  count: usize,
) -> Handles {
  assert!(count > 0 && count <= MAX_CHUNK);
  assert!(start <= owner.srs.g1.len() && count <= owner.srs.g1.len() - start);
  let (mut window, mut persistent, mut temporary) = (0, 0, 0);
  check(
    unsafe {
      C::ffi_srs_plan(
        device.id(),
        count,
        &mut window,
        &mut persistent,
        &mut temporary,
      )
    },
    "MSM memory plan",
  );
  let point_bytes =
    count.div_ceil(32).checked_mul(32 * C::DEVICE_AFFINE_BYTES).unwrap();
  let staging_bytes =
    count.min(UPLOAD_POINTS).div_ceil(32) * 32 * size_of::<G1AffineOf<C>>();
  let mut cache = caches::<C>()[device.index].lock().unwrap();
  cache.purge::<C>(device);
  if cache
    .workspace
    .as_ref()
    .is_some_and(|workspace| workspace.window != window)
  {
    cache.drop_workspace::<C>(device);
  }
  loop {
    let hit = cache
      .entries
      .iter()
      .position(|entry| entry.contains(owner, start, count));
    if hit.is_none()
      && let Some(index) = cache
        .entries
        .iter()
        .position(|entry| entry.overlaps(owner, start, count))
    {
      cache.evict::<C>(device, index);
      continue;
    }
    if hit.is_none() && cache.point_bytes() + point_bytes > LIMIT {
      let index = cache.oldest().expect("SRS chunk exceeds cache limit");
      cache.evict::<C>(device, index);
      continue;
    }
    let needed = temporary
      + HEADROOM
      + if hit.is_none() { point_bytes + staging_bytes } else { 0 }
      + if cache.workspace.is_none() { persistent } else { 0 };
    if device.budget::<C>() < needed {
      if let Some(index) = cache.oldest() {
        cache.evict::<C>(device, index);
        continue;
      }
      panic!("insufficient free VRAM for admitted cached MSM");
    }
    if cache.workspace.is_none() {
      let mut pointer = std::ptr::null_mut();
      check(
        unsafe {
          C::ffi_srs_workspace_create(device.id(), count, &mut pointer)
        },
        "MSM workspace creation",
      );
      cache.workspace = Some(Workspace {
        pointer: pointer as usize,
        window,
        bytes: persistent,
      });
    }
    cache.clock =
      cache.clock.checked_add(1).expect("SRS cache clock exhausted");
    let used = cache.clock;
    let index = if let Some(index) = hit {
      cache.hits += 1;
      cache.entries[index].used = used;
      index
    } else {
      let mut pointer = std::ptr::null_mut();
      check(
        unsafe {
          C::ffi_srs_upload(
            device.id(),
            owner.srs.g1[start..].as_ptr().cast(),
            count,
            &mut pointer,
          )
        },
        "SRS cache upload",
      );
      cache.uploads += 1;
      cache.upload_bytes += (count * size_of::<G1AffineOf<C>>()) as u64;
      cache.entries.push(Entry {
        owner: Arc::downgrade(&owner.token),
        id: owner.id,
        start,
        count,
        pointer: pointer as usize,
        bytes: point_bytes,
        used,
      });
      cache.entries.len() - 1
    };
    assert!(
      device.budget::<C>() >= temporary + HEADROOM,
      "cached MSM free-memory recheck failed"
    );
    let entry = &cache.entries[index];
    tracing::debug!(
      curve = C::NAME,
      device = device.id(),
      owner = owner.id,
      start,
      count,
      hit = hit.is_some(),
      point_bytes = cache.point_bytes(),
      workspace_bytes = persistent,
      hits = cache.hits,
      uploads = cache.uploads,
      upload_bytes = cache.upload_bytes,
      evictions = cache.evictions,
      "KZG SRS cache access"
    );
    return Handles {
      points: entry.pointer,
      point_offset: start - entry.start,
      workspace: cache.workspace.as_ref().unwrap().pointer,
    };
  }
}

#[derive(Clone, Copy)]
enum Scalars<'a, C: KzgCurve> {
  Host(&'a [C::Fr]),
  Resident { pointer: usize, offset: usize, count: usize },
}

fn invoke<C: KzgCurve>(
  device: &Device<'_>,
  handles: &Handles,
  scalars: Scalars<'_, C>,
  normalization: Option<(C::Fr, C::Fr)>,
) -> G1ProjectiveOf<C> {
  let (host, resident, scalar_offset, count) = match scalars {
    Scalars::Host(values) => {
      (values.as_ptr().cast(), std::ptr::null(), 0, values.len())
    },
    Scalars::Resident { pointer, offset, count } => {
      (std::ptr::null(), pointer as *const c_void, offset, count)
    },
  };
  let mut output = [C::FqLimbs::default(); 3];
  check(
    unsafe {
      C::ffi_srs_msm(
        device.id(),
        handles.workspace as *mut c_void,
        handles.points as *const c_void,
        handles.point_offset,
        &mut output,
        host,
        resident,
        scalar_offset,
        count,
        normalization.as_ref().map_or(std::ptr::null(), |(_, inverse)| {
          C::fr_mont_limbs_ref(inverse)
        }),
      )
    },
    "cached SRS MSM",
  );
  let result = projective::<C>(output);
  normalization.map_or(result, |(scale, _)| result * scale)
}

pub(in crate::kzg) fn msm_columns<C: KzgCurve>(
  owner: &Arc<Owner<C>>,
  start: usize,
  columns: &[(&[C::Fr], Option<&ResidentPolynomial<C>>)],
) -> Vec<G1ProjectiveOf<C>> {
  let count = columns.first().map_or(0, |(column, _)| column.len());
  assert!(columns.iter().all(|(column, _)| column.len() == count));
  assert!(start <= owner.srs.g1.len() && count <= owner.srs.g1.len() - start);
  if count == 0 {
    return vec![G1ProjectiveOf::<C>::zero(); columns.len()];
  }
  let devices = Devices::get::<C>();
  let limit = devices.chunk_points.min(MAX_CHUNK);
  let mut groups = vec![Vec::new(); devices.ids.len()];
  let mut host = Vec::new();
  for (column, (_, resident)) in columns.iter().enumerate() {
    if let Some(resident) = resident {
      groups[resident.reservation.index].push(column);
    } else {
      host.push(column);
    }
  }
  let mut work = Vec::new();
  for (index, group) in groups.into_iter().enumerate() {
    if !group.is_empty() {
      work.push((index, 0, count, group));
    }
  }
  if !host.is_empty() {
    let chunk = count.div_ceil(devices.ids.len()).min(limit).max(1);
    for (index, offset) in (0..count).step_by(chunk).enumerate() {
      work.push((
        index % devices.ids.len(),
        offset,
        (count - offset).min(chunk),
        host.clone(),
      ));
    }
  }
  let parts: Vec<_> = work
    .into_par_iter()
    .map(|(index, offset, length, group)| {
      let device = devices.acquire_at(index);
      let chunk = limit.min(
        devices.potential_budget::<C>(index).saturating_sub(HEADROOM)
          / MSM_BYTES_PER_POINT,
      );
      assert!(chunk > 0, "insufficient free VRAM for KZG MSM");
      let mut sums = vec![G1ProjectiveOf::<C>::zero(); group.len()];
      for part in (offset..offset + length).step_by(chunk) {
        let length = (offset + length - part).min(chunk);
        let handles = prepare::<C>(&device, owner, start + part, length);
        for (&column, sum) in group.iter().zip(&mut sums) {
          let (coefficients, resident) = columns[column];
          let input = &coefficients[part..part + length];
          let scalars = resident.map_or(Scalars::Host(input), |resident| {
            Scalars::Resident {
              pointer: resident.context,
              offset: part,
              count: length,
            }
          });
          *sum += invoke::<C>(
            &device,
            &handles,
            scalars,
            msm_normalization::<C>(input),
          );
        }
      }
      group.into_iter().zip(sums).collect::<Vec<_>>()
    })
    .collect();
  let mut result = vec![G1ProjectiveOf::<C>::zero(); columns.len()];
  for (column, point) in parts.into_iter().flatten() {
    result[column] += point;
  }
  result
}

pub(in crate::kzg) fn single_device_opening<C: KzgCurve>(
  owner: &Arc<Owner<C>>,
  coefficients: &[C::Fr],
  z: C::Fr,
) -> Option<G1ProjectiveOf<C>> {
  let devices = Devices::get::<C>();
  if devices.ids.len() != 1 || coefficients.len() < 2 {
    return None;
  }
  let count = coefficients.len() - 1;
  assert!(count <= owner.srs.g1.len());
  let device = devices.acquire_at(0);
  let chunk = opening_chunk(
    coefficients.len(),
    devices.chunk_points.min(MAX_CHUNK),
    devices.potential_budget::<C>(0),
  )?;
  let required = coefficients
    .len()
    .checked_mul(32)?
    .checked_add(HEADROOM)?
    .checked_add(chunk.checked_mul(MSM_BYTES_PER_POINT)?)?;
  if !device.prepare_budget::<C>(required) {
    return None;
  }
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
    "cached SRS opening division",
  );
  let quotient =
    LeasedPolynomial::<C> { device: &device, context, _curve: PhantomData };
  let mut result = G1ProjectiveOf::<C>::zero();
  for offset in (0..count).step_by(chunk) {
    let count = (count - offset).min(chunk);
    let mut samples = [C::FR_ZERO; 128];
    let normalization = if count >= 4096 {
      check(
        unsafe {
          C::ffi_polynomial_sample(
            device.id(),
            quotient.context,
            offset,
            count,
            samples.as_mut_ptr().cast(),
          )
        },
        "cached SRS opening sample",
      );
      sample_normalization::<C>(samples.into_iter())
    } else {
      None
    };
    let handles = prepare::<C>(&device, owner, offset, count);
    result += invoke::<C>(
      &device,
      &handles,
      Scalars::Resident { pointer: quotient.context as usize, offset, count },
      normalization,
    );
  }
  Some(result)
}
