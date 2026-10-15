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

pub(in crate::kzg) struct Owner {
  id: u64,
  srs: Arc<Srs>,
}

impl Owner {
  pub(in crate::kzg) fn new(srs: Arc<Srs>) -> Arc<Self> {
    static NEXT: AtomicU64 = AtomicU64::new(1);
    let id = NEXT
      .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| {
        id.checked_add(1)
      })
      .expect("SRS cache identity exhausted");
    Arc::new(Self { id, srs })
  }
}

pub(in crate::kzg) fn enabled() -> bool {
  settings().srs_cache
}

unsafe extern "C" {
  fn ix_kzg_srs_plan(
    device: i32,
    count: usize,
    window: *mut u32,
    persistent: *mut usize,
    temporary: *mut usize,
  ) -> i32;
  fn ix_kzg_srs_upload(
    device: i32,
    input: *const c_void,
    count: usize,
    output: *mut *mut c_void,
  ) -> i32;
  fn ix_kzg_srs_destroy(device: i32, points: *mut c_void) -> i32;
  fn ix_kzg_srs_workspace_create(
    device: i32,
    count: usize,
    output: *mut *mut c_void,
  ) -> i32;
  fn ix_kzg_srs_workspace_destroy(device: i32, workspace: *mut c_void) -> i32;
  fn ix_kzg_srs_msm(
    device: i32,
    workspace: *mut c_void,
    points: *const c_void,
    point_offset: usize,
    output: *mut [[u64; 6]; 3],
    host: *const [u64; 4],
    polynomial: *const c_void,
    scalar_offset: usize,
    count: usize,
    normalization: *const [u64; 4],
  ) -> i32;
}

struct Entry {
  owner: Weak<Owner>,
  id: u64,
  start: usize,
  count: usize,
  pointer: usize,
  bytes: usize,
  used: u64,
}

impl Entry {
  fn contains(&self, owner: &Owner, start: usize, count: usize) -> bool {
    self.id == owner.id
      && start >= self.start
      && start - self.start <= self.count
      && count <= self.count - (start - self.start)
  }

  fn overlaps(&self, owner: &Owner, start: usize, count: usize) -> bool {
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
struct Cache {
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

  fn evict(&mut self, device: &Device<'_>, index: usize) {
    let entry = self.entries.swap_remove(index);
    check(
      unsafe { ix_kzg_srs_destroy(device.id(), entry.pointer as *mut c_void) },
      "SRS eviction",
    );
    self.evictions += 1;
    tracing::debug!(
      device = device.id(),
      owner = entry.id,
      start = entry.start,
      bytes = entry.bytes,
      "KZG SRS cache evicted"
    );
  }

  fn drop_workspace(&mut self, device: &Device<'_>) {
    if let Some(workspace) = self.workspace.take() {
      check(
        unsafe {
          ix_kzg_srs_workspace_destroy(
            device.id(),
            workspace.pointer as *mut c_void,
          )
        },
        "MSM workspace eviction",
      );
    }
  }

  fn purge(&mut self, device: &Device<'_>) {
    while let Some(index) =
      self.entries.iter().position(|entry| entry.owner.strong_count() == 0)
    {
      self.evict(device, index);
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

fn caches() -> &'static [Mutex<Cache>] {
  static CACHES: OnceLock<Vec<Mutex<Cache>>> = OnceLock::new();
  CACHES.get_or_init(|| {
    Devices::get().ids.iter().map(|_| Mutex::new(Cache::default())).collect()
  })
}

pub(super) fn reclaimable(index: usize) -> usize {
  caches()[index].lock().unwrap().bytes()
}

/// The caller owns the only operation lease; no cached native handle can be
/// in use.
pub(super) fn prepare_budget(device: &Device<'_>, required: usize) -> bool {
  let mut cache = caches()[device.index].lock().unwrap();
  cache.purge(device);
  while device.budget() < required {
    if let Some(index) = cache.oldest() {
      cache.evict(device, index);
    } else if cache.workspace.is_some() {
      cache.drop_workspace(device);
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

fn prepare(
  device: &Device<'_>,
  owner: &Arc<Owner>,
  start: usize,
  count: usize,
) -> Handles {
  assert!(count > 0 && count <= MAX_CHUNK);
  assert!(start <= owner.srs.g1.len() && count <= owner.srs.g1.len() - start);
  let (mut window, mut persistent, mut temporary) = (0, 0, 0);
  check(
    unsafe {
      ix_kzg_srs_plan(
        device.id(),
        count,
        &mut window,
        &mut persistent,
        &mut temporary,
      )
    },
    "MSM memory plan",
  );
  let point_bytes = count.div_ceil(32).checked_mul(32 * 96).unwrap();
  let staging_bytes = count.min(UPLOAD_POINTS).div_ceil(32) * 32 * 104;
  let mut cache = caches()[device.index].lock().unwrap();
  cache.purge(device);
  if cache
    .workspace
    .as_ref()
    .is_some_and(|workspace| workspace.window != window)
  {
    cache.drop_workspace(device);
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
      cache.evict(device, index);
      continue;
    }
    if hit.is_none() && cache.point_bytes() + point_bytes > LIMIT {
      let index = cache.oldest().expect("SRS chunk exceeds cache limit");
      cache.evict(device, index);
      continue;
    }
    let needed = temporary
      + HEADROOM
      + if hit.is_none() { point_bytes + staging_bytes } else { 0 }
      + if cache.workspace.is_none() { persistent } else { 0 };
    if device.budget() < needed {
      if let Some(index) = cache.oldest() {
        cache.evict(device, index);
        continue;
      }
      panic!("insufficient free VRAM for admitted cached MSM");
    }
    if cache.workspace.is_none() {
      let mut pointer = std::ptr::null_mut();
      check(
        unsafe {
          ix_kzg_srs_workspace_create(device.id(), count, &mut pointer)
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
          ix_kzg_srs_upload(
            device.id(),
            owner.srs.g1[start..].as_ptr().cast(),
            count,
            &mut pointer,
          )
        },
        "SRS cache upload",
      );
      cache.uploads += 1;
      cache.upload_bytes += (count * size_of::<G1Affine>()) as u64;
      cache.entries.push(Entry {
        owner: Arc::downgrade(owner),
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
      device.budget() >= temporary + HEADROOM,
      "cached MSM free-memory recheck failed"
    );
    let entry = &cache.entries[index];
    tracing::debug!(
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
enum Scalars<'a> {
  Host(&'a [Fr]),
  Resident { pointer: usize, offset: usize, count: usize },
}

fn invoke(
  device: &Device<'_>,
  handles: &Handles,
  scalars: Scalars<'_>,
  normalization: Option<(Fr, Fr)>,
) -> G1Projective {
  let (host, resident, scalar_offset, count) = match scalars {
    Scalars::Host(values) => {
      (values.as_ptr().cast(), std::ptr::null(), 0, values.len())
    },
    Scalars::Resident { pointer, offset, count } => {
      (std::ptr::null(), pointer as *const c_void, offset, count)
    },
  };
  let mut output = [[0; 6]; 3];
  check(
    unsafe {
      ix_kzg_srs_msm(
        device.id(),
        handles.workspace as *mut c_void,
        handles.points as *const c_void,
        handles.point_offset,
        &mut output,
        host,
        resident,
        scalar_offset,
        count,
        normalization
          .as_ref()
          .map_or(std::ptr::null(), |(_, inverse)| &inverse.0.0),
      )
    },
    "cached SRS MSM",
  );
  let result = projective(output);
  normalization.map_or(result, |(scale, _)| result * scale)
}

pub(in crate::kzg) fn msm_columns(
  owner: &Arc<Owner>,
  start: usize,
  columns: &[(&[Fr], Option<&ResidentPolynomial>)],
) -> Vec<G1Projective> {
  let count = columns.first().map_or(0, |(column, _)| column.len());
  assert!(columns.iter().all(|(column, _)| column.len() == count));
  assert!(start <= owner.srs.g1.len() && count <= owner.srs.g1.len() - start);
  if count == 0 {
    return vec![G1Projective::zero(); columns.len()];
  }
  let devices = Devices::get();
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
      let chunk = limit
        .min(devices.potential_budget(index).saturating_sub(HEADROOM) / 384);
      assert!(chunk > 0, "insufficient free VRAM for KZG MSM");
      let mut sums = vec![G1Projective::zero(); group.len()];
      for part in (offset..offset + length).step_by(chunk) {
        let length = (offset + length - part).min(chunk);
        let handles = prepare(&device, owner, start + part, length);
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
          *sum += invoke(&device, &handles, scalars, msm_normalization(input));
        }
      }
      group.into_iter().zip(sums).collect::<Vec<_>>()
    })
    .collect();
  let mut result = vec![G1Projective::zero(); columns.len()];
  for (column, point) in parts.into_iter().flatten() {
    result[column] += point;
  }
  result
}

pub(in crate::kzg) fn single_device_opening(
  owner: &Arc<Owner>,
  coefficients: &[Fr],
  z: Fr,
) -> Option<G1Projective> {
  let devices = Devices::get();
  if devices.ids.len() != 1 || coefficients.len() < 2 {
    return None;
  }
  let count = coefficients.len() - 1;
  assert!(count <= owner.srs.g1.len());
  let device = devices.acquire_at(0);
  let chunk = opening_chunk(
    coefficients.len(),
    devices.chunk_points.min(MAX_CHUNK),
    devices.potential_budget(0),
  )?;
  let required = coefficients
    .len()
    .checked_mul(32)?
    .checked_add(HEADROOM)?
    .checked_add(chunk.checked_mul(384)?)?;
  if !device.prepare_budget(required) {
    return None;
  }
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
    "cached SRS opening division",
  );
  let quotient = LeasedPolynomial { device: &device, context };
  let mut result = G1Projective::zero();
  for offset in (0..count).step_by(chunk) {
    let count = (count - offset).min(chunk);
    let mut samples = [Fr::ZERO; 128];
    let normalization = if count >= 4096 {
      check(
        unsafe {
          ix_kzg_polynomial_sample(
            device.id(),
            quotient.context,
            offset,
            count,
            samples.as_mut_ptr().cast(),
          )
        },
        "cached SRS opening sample",
      );
      sample_normalization(samples.into_iter())
    } else {
      None
    };
    let handles = prepare(&device, owner, offset, count);
    result += invoke(
      &device,
      &handles,
      Scalars::Resident { pointer: quotient.context as usize, offset, count },
      normalization,
    );
  }
  Some(result)
}
