//! Opt-in dense primitive measurements for the 2^24 PLONK domain.

use super::*;
use crate::pipeline::SetupConfig;
use ark_serialize::CanonicalSerialize;
use serde_json::{Value, json};
use std::{
  fs::{File, OpenOptions},
  io::{Seek, Write},
  path::PathBuf,
  time::{Instant, SystemTime, UNIX_EPOCH},
};

const N: usize = 1 << 24;
const SEED: &[u8] = b"ix/bn254/plonk-scale/dense-primitives/v1";

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
    output: *mut ProjectiveLimbs,
    host: *const [u64; 4],
    polynomial: *const c_void,
    scalar_offset: usize,
    count: usize,
    normalization: *const [u64; 4],
  ) -> i32;
}

struct Report {
  file: File,
  value: Value,
}

impl Report {
  fn new(operation: &str, repeats: usize, ordinal: i32) -> Self {
    let path = PathBuf::from(
      std::env::var_os("IX_PLONK_PRIMITIVE_REPORT")
        .expect("set IX_PLONK_PRIMITIVE_REPORT to a new report path"),
    );
    let file = OpenOptions::new()
      .write(true)
      .create_new(true)
      .open(path)
      .expect("create a new primitive benchmark report");
    let mut report = Self {
      file,
      value: json!({
        "format": "ix-bn254-plonk-scale-primitives/v1",
        "operation": operation,
        "completed": false,
        "all_comparisons_passed": false,
        "started_unix_seconds": SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs(),
        "device_ordinal": ordinal,
        "cuda_visible_devices": std::env::var("CUDA_VISIBLE_DEVICES").ok(),
        "compiled_cuda_architectures": env!("IX_KZG_CUDA_COMPILED_ARCHS"),
        "rayon_threads": rayon::current_num_threads(),
        "warm_repeats": repeats,
        "seed": String::from_utf8_lossy(SEED),
        "field_vector_hash_encoding": "BLAKE3 of little-endian Montgomery Fr limbs; native ABI checked",
        "scope": "Existing ix BN254 CUDA primitives, not a gnark CUDA prover. Native calls include host transfers. Only the first case is process-cold; OS page-cache state is uncontrolled.",
        "warm_definition": "Repeated identical operation within one case; uncached MSM still uploads its bases on every call",
        "records": [],
      }),
    };
    report.save();
    report
  }

  fn save(&mut self) {
    self.file.set_len(0).unwrap();
    self.file.rewind().unwrap();
    serde_json::to_writer_pretty(&mut self.file, &self.value).unwrap();
    self.file.write_all(b"\n").unwrap();
    self.file.flush().unwrap();
  }

  fn record(&mut self, record: Value) {
    eprintln!("plonk-scale {}", serde_json::to_string(&record).unwrap());
    self.value["records"].as_array_mut().unwrap().push(record);
    self.save();
  }
}

fn timed<T>(operation: impl FnOnce() -> T) -> (T, f64) {
  let start = Instant::now();
  let result = operation();
  (result, start.elapsed().as_secs_f64())
}

fn dense(count: usize) -> Vec<Fr> {
  (0..count)
    .into_par_iter()
    .map(|index| {
      let mut wide = [0; 64];
      blake3::Hasher::new()
        .update(SEED)
        .update(&(index as u64).to_le_bytes())
        .finalize_xof()
        .fill(&mut wide);
      let value = Fr::from_le_bytes_mod_order(&wide);
      if value.is_zero() { Fr::ONE } else { value }
    })
    .collect()
}

fn field_hash(values: &[Fr]) -> String {
  // The ABI asserts a padding-free four-limb Fr representation.
  let bytes = unsafe {
    std::slice::from_raw_parts(
      values.as_ptr().cast::<u8>(),
      size_of_val(values),
    )
  };
  let mut hash = blake3::Hasher::new();
  hash.update_rayon(bytes);
  hash.finalize().to_hex().to_string()
}

fn point_hex(point: G1Projective) -> String {
  let mut bytes = Vec::new();
  point.into_affine().serialize_compressed(&mut bytes).unwrap();
  bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn memory(device: i32) -> Value {
  // libix_bn254_cuda.so keeps its CUDA runtime private; these queries read
  // driver-wide state through a separate static runtime.
  #[link(name = "cudart_static", kind = "static")]
  unsafe extern "C" {
    fn cudaMemGetInfo(free: *mut usize, total: *mut usize) -> i32;
    fn cudaDeviceGetDefaultMemPool(pool: *mut *mut c_void, device: i32) -> i32;
    fn cudaDeviceGetMemPool(pool: *mut *mut c_void, device: i32) -> i32;
    fn cudaMemPoolGetAttribute(
      pool: *mut c_void,
      attribute: i32,
      value: *mut c_void,
    ) -> i32;
  }

  let (mut free, mut total) = (0, 0);
  check(
    unsafe { ix_kzg_memory(device, &mut free, &mut total) },
    "benchmark memory query",
  );
  // ix_kzg_memory selects this device before querying its allocation pool.
  let (mut driver_free, mut driver_total) = (0, 0);
  check(
    unsafe { cudaMemGetInfo(&mut driver_free, &mut driver_total) },
    "benchmark driver memory query",
  );
  let mut default_pool = std::ptr::null_mut();
  check(
    unsafe { cudaDeviceGetDefaultMemPool(&mut default_pool, device) },
    "benchmark default allocation pool",
  );
  let mut active_pool = std::ptr::null_mut();
  check(
    unsafe { cudaDeviceGetMemPool(&mut active_pool, device) },
    "benchmark active allocation pool",
  );
  let statistics = |pool| {
    // cudaMemPoolAttr 5..=8 each returns a uint64_t byte count.
    let mut values = [0u64; 4];
    for (value, attribute) in values.iter_mut().zip(5..=8) {
      check(
        unsafe {
          cudaMemPoolGetAttribute(
            pool,
            attribute,
            std::ptr::from_mut(value).cast(),
          )
        },
        "benchmark allocation pool statistics",
      );
    }
    json!({
      "reserved_current_bytes": values[0],
      "reserved_high_bytes": values[1],
      "used_current_bytes": values[2],
      "used_high_bytes": values[3],
    })
  };
  json!({
    "total_bytes": total,
    "available_including_reusable_pool_bytes": free,
    "driver_total_bytes": driver_total,
    "driver_free_bytes": driver_free,
    "driver_used_bytes": driver_total.saturating_sub(driver_free),
    "default_pool": statistics(default_pool),
    "active_pool_is_default": active_pool == default_pool,
    "different_active_pool": if active_pool == default_pool {
      None
    } else {
      Some(statistics(active_pool))
    },
    "pool_high_water_scope": "Cumulative since pool creation or last external reset; this benchmark does not reset it",
    "pool_peak_is_total_vram_peak": false,
    "pool_peak_exclusions": "Driver/context/module overhead and allocations outside this pool; driver_used_bytes is only an instantaneous snapshot",
  })
}

struct CachedMsm<'a, 'b> {
  device: &'a Device<'b>,
  points: *mut c_void,
  workspace: *mut c_void,
}

impl<'a, 'b> CachedMsm<'a, 'b> {
  fn new(device: &'a Device<'b>, points: &[G1Affine]) -> (Self, Value) {
    let mut handle = Self {
      device,
      points: std::ptr::null_mut(),
      workspace: std::ptr::null_mut(),
    };
    let (mut window, mut persistent, mut temporary) = (0, 0, 0);
    check(
      unsafe {
        ix_kzg_srs_plan(
          device.id(),
          points.len(),
          &mut window,
          &mut persistent,
          &mut temporary,
        )
      },
      "benchmark cached MSM plan",
    );
    let (_, workspace_seconds) = timed(|| {
      check(
        unsafe {
          ix_kzg_srs_workspace_create(
            device.id(),
            points.len(),
            &mut handle.workspace,
          )
        },
        "benchmark cached MSM workspace",
      )
    });
    let (_, upload_seconds) = timed(|| {
      check(
        unsafe {
          ix_kzg_srs_upload(
            device.id(),
            points.as_ptr().cast(),
            points.len(),
            &mut handle.points,
          )
        },
        "benchmark cached MSM points",
      )
    });
    (
      handle,
      json!({
        "native_count": points.len(), "window": window,
        "planned_persistent_workspace_bytes": persistent,
        "planned_temporary_workspace_bytes": temporary,
        "device_point_bytes": points.len() * 64,
        "workspace_seconds": workspace_seconds, "point_upload_seconds": upload_seconds,
        "initialization_seconds": workspace_seconds + upload_seconds,
      }),
    )
  }

  fn invoke(&self, scalars: &[Fr]) -> G1Projective {
    let mut output = [[0; FQ_LIMBS]; 3];
    check(
      unsafe {
        ix_kzg_srs_msm(
          self.device.id(),
          self.workspace,
          self.points,
          0,
          &mut output,
          scalars.as_ptr().cast(),
          std::ptr::null(),
          0,
          scalars.len(),
          std::ptr::null(),
        )
      },
      "benchmark cached MSM",
    );
    projective(output)
  }

  fn close(mut self) {
    let points = std::mem::replace(&mut self.points, std::ptr::null_mut());
    check(
      unsafe { ix_kzg_srs_destroy(self.device.id(), points) },
      "benchmark cached points destruction",
    );
    let workspace =
      std::mem::replace(&mut self.workspace, std::ptr::null_mut());
    check(
      unsafe { ix_kzg_srs_workspace_destroy(self.device.id(), workspace) },
      "benchmark cached workspace destruction",
    );
  }
}

impl Drop for CachedMsm<'_, '_> {
  fn drop(&mut self) {
    if !self.points.is_null() {
      unsafe { ix_kzg_srs_destroy(self.device.id(), self.points) };
    }
    if !self.workspace.is_null() {
      unsafe { ix_kzg_srs_workspace_destroy(self.device.id(), self.workspace) };
    }
  }
}

fn uncached_msm(
  device: &Device<'_>,
  points: &[G1Affine],
  scalars: &[Fr],
) -> (G1Projective, Value) {
  let (resident, upload_seconds) = timed(|| upload_msm_points(device, points));
  let mut output = [[0; FQ_LIMBS]; 3];
  let (_, invoke_seconds) = timed(|| {
    check(
      unsafe {
        ix_kzg_msm_invoke(
          device.id(),
          resident.context,
          &mut output,
          scalars.as_ptr().cast(),
          scalars.len(),
          std::ptr::null(),
        )
      },
      "benchmark uncached MSM",
    )
  });
  let (_, destroy_seconds) = timed(|| {
    let status = unsafe { ix_kzg_msm_destroy(device.id(), resident.context) };
    std::mem::forget(resident);
    check(status, "benchmark uncached MSM destruction");
  });
  (
    projective(output),
    json!({
      "point_upload_and_workspace_seconds": upload_seconds,
      "invoke_seconds": invoke_seconds, "destroy_seconds": destroy_seconds,
    }),
  )
}

fn msm_benchmark(report: &mut Report, cached: bool, repeats: usize) {
  let (srs, load_seconds) = timed(|| {
    SetupConfig::from_env(false)
      .unwrap()
      .for_stage(SEED, 2 * N)
      .unwrap()
      .srs(2 * N, false)
      .unwrap()
  });
  report.record(json!({
    "phase": "srs_load", "seconds": load_seconds,
    "loaded_prefix_points": srs.g1.len(), "largest_used_point_end": N+10,
    "public_max_degree": srs.public_setup.max_degree,
    "setup_id": blake3::Hash::from(srs.public_setup.id).to_hex().to_string(),
  }));
  let (values, generate_seconds) = timed(|| dense(N + 3));
  let (input_hash, hash_seconds) = timed(|| field_hash(&values));
  report.record(json!({
    "phase": "dense_scalar_generation", "elements": values.len(),
    "seconds": generate_seconds, "hash_seconds": hash_seconds,
    "input_montgomery_blake3": input_hash, "zero_scalars": 0,
  }));
  for (offset, count) in [(0, N), (7, N + 3)] {
    let points = &srs.g1[offset..offset + count];
    let scalars = &values[..count];
    eprintln!("plonk-scale phase=cpu_msm offset={offset} count={count}");
    let (expected, cpu_seconds) =
      timed(|| G1Projective::msm(points, scalars).unwrap());
    assert!(
      !expected.is_zero(),
      "dense reference unexpectedly equals infinity"
    );
    report.record(json!({
      "phase": "cpu_msm_reference", "offset": offset, "count": count,
      "seconds": cpu_seconds, "compressed_result": point_hex(expected),
    }));
    let device = Devices::get().acquire_at(0);
    assert!(
      device.prepare_budget(N * MSM_BYTES_PER_POINT + (1 << 30)),
      "full N-point MSM cannot be admitted"
    );
    let (resident, initialization) = if cached {
      let (resident, initialization) = CachedMsm::new(&device, &points[..N]);
      (Some(resident), initialization)
    } else {
      (None, json!({"initialization_seconds": 0.0}))
    };
    report.record(json!({
      "phase": "msm_initialization", "offset": offset, "count": count,
      "cached": cached, "details": initialization,
      "memory": memory(device.id()),
    }));
    for trial in 0..=repeats {
      let (point, gpu_seconds, details) = if let Some(resident) = &resident {
        let (point, seconds) = timed(|| resident.invoke(&scalars[..N]));
        (point, seconds, json!({}))
      } else {
        let ((point, details), seconds) =
          timed(|| uncached_msm(&device, &points[..N], &scalars[..N]));
        (point, seconds, details)
      };
      let (actual, tail_seconds) = timed(|| {
        if count == N {
          point
        } else {
          point + G1Projective::msm(&points[N..], &scalars[N..]).unwrap()
        }
      });
      let matches = actual == expected;
      report.record(json!({
        "phase": "gpu_msm", "trial": trial,
        "warm": trial != 0, "cached": cached, "offset": offset,
        "process_first_msm": offset == 0 && trial == 0,
        "basis_first_use": trial == 0,
        "resident_basis_reused": cached && trial != 0,
        "host_point_end": offset+count, "count": count,
        "native_gpu_count": N, "native_gpu_calls": 1, "native_point_offset": 0,
        "cpu_tail_points": count-N,
        "gpu_call_seconds": gpu_seconds, "cpu_tail_and_add_seconds": tail_seconds,
        "operation_seconds": gpu_seconds+tail_seconds,
        "first_use_with_initialization_seconds": if trial == 0 {
          Some(gpu_seconds+tail_seconds+initialization["initialization_seconds"].as_f64().unwrap())
        } else { None },
        "compressed_result": point_hex(actual), "matches_full_cpu_reference": matches,
        "native_details": details, "memory": memory(device.id()),
      }));
      assert!(matches, "large MSM differs from full CPU reference");
    }
    if let Some(resident) = resident {
      let (_, seconds) = timed(|| resident.close());
      report.record(json!({"phase": "cached_msm_cleanup", "seconds": seconds}));
    }
  }
}

fn fft_benchmark(report: &mut Report, log_size: usize, repeats: usize) {
  let inverse = match std::env::var("IX_PLONK_PRIMITIVE_DIRECTION")
    .as_deref()
    .unwrap_or("forward")
  {
    "forward" => false,
    "inverse" => true,
    _ => panic!("IX_PLONK_PRIMITIVE_DIRECTION must be forward or inverse"),
  };
  let shift: u64 = std::env::var("IX_PLONK_PRIMITIVE_SHIFT")
    .unwrap_or_else(|_| "5".into())
    .parse()
    .unwrap();
  assert!(shift != 0, "FFT coset shift must be nonzero");
  let shift = Fr::from(shift);
  let count = 1usize << log_size;
  let (input, generate_seconds) = timed(|| dense(count));
  let (input_hash, input_hash_seconds) = timed(|| field_hash(&input));
  report.record(json!({
    "phase": "dense_fft_input", "log_size": log_size, "elements": count,
    "bytes_per_vector": count*32, "inverse": inverse,
    "shift": shift.into_bigint().to_string(), "generation_seconds": generate_seconds,
    "hash_seconds": input_hash_seconds, "input_montgomery_blake3": input_hash,
  }));
  let (domain, domain_seconds) = timed(|| {
    Radix2EvaluationDomain::<Fr>::new(count).unwrap().get_coset(shift).unwrap()
  });
  let (mut expected, cpu_copy_seconds) = timed(|| input.clone());
  eprintln!("plonk-scale phase=cpu_fft log_size={log_size} inverse={inverse}");
  let (_, cpu_seconds) = timed(|| {
    if inverse {
      domain.ifft_in_place(&mut expected)
    } else {
      domain.fft_in_place(&mut expected)
    }
  });
  let (expected_hash, hash_seconds) = timed(|| field_hash(&expected));
  report.record(json!({
    "phase": "cpu_fft_reference", "domain_seconds": domain_seconds,
    "input_copy_seconds": cpu_copy_seconds, "seconds": cpu_seconds,
    "hash_seconds": hash_seconds, "output_montgomery_blake3": expected_hash,
  }));
  for trial in 0..=repeats {
    let (mut actual, copy_seconds) = timed(|| input.clone());
    let (_, gpu_seconds) = timed(|| fft(&mut actual, inverse, shift));
    let (mismatch, compare_seconds) = timed(|| {
      actual
        .par_iter()
        .zip(&expected)
        .enumerate()
        .find_any(|(_, (a, b))| a != b)
        .map(|(index, _)| index)
    });
    let (actual_hash, hash_seconds) = timed(|| field_hash(&actual));
    report.record(json!({
      "phase": "gpu_fft", "trial": trial, "warm": trial != 0,
      "native_gpu_count": count, "native_gpu_log_size": log_size,
      "native_gpu_calls": 1, "inverse": inverse,
      "input_copy_seconds": copy_seconds, "gpu_call_seconds": gpu_seconds,
      "compare_seconds": compare_seconds, "hash_seconds": hash_seconds,
      "output_montgomery_blake3": actual_hash, "mismatch_index": mismatch,
      "matches_full_cpu_reference": mismatch.is_none(),
      "memory": memory(Devices::get().ids[0]),
    }));
    assert!(mismatch.is_none(), "large FFT differs from full CPU reference");
  }
}

// The CPU references are only representative with the `parallel` feature.
#[cfg(feature = "parallel")]
#[test]
#[ignore = "full-scale CUDA benchmark; set IX_PLONK_PRIMITIVE_OP and IX_PLONK_PRIMITIVE_REPORT and run this test alone"]
fn bn254_plonk_scale_primitives() {
  let operation = std::env::var("IX_PLONK_PRIMITIVE_OP")
    .expect("explicit primitive operation required");
  assert!(matches!(
    operation.as_str(),
    "msm-cached" | "msm-uncached" | "fft-n" | "fft-m"
  ));
  let repeats: usize = std::env::var("IX_PLONK_PRIMITIVE_REPEATS")
    .unwrap_or_else(|_| "3".into())
    .parse()
    .unwrap();
  assert!((1..=10).contains(&repeats));
  let device: i32 = std::env::var("IX_PLONK_PRIMITIVE_DEVICE")
    .unwrap_or_else(|_| "0".into())
    .parse()
    .unwrap();
  assert!(
    configure(Settings {
      devices: Some(vec![device]),
      msm_chunk_points: N,
      srs_cache: true,
      ..Settings::default()
    }),
    "run the benchmark alone in a fresh process"
  );
  let mut report = Report::new(&operation, repeats, device);
  let start = Instant::now();
  let (_, initialization_seconds) = timed(Devices::get);
  report.record(json!({
    "phase": "device_initialization", "seconds": initialization_seconds,
    "memory": memory(device),
  }));
  match operation.as_str() {
    "msm-cached" => msm_benchmark(&mut report, true, repeats),
    "msm-uncached" => msm_benchmark(&mut report, false, repeats),
    "fft-n" => fft_benchmark(&mut report, 24, repeats),
    "fft-m" => fft_benchmark(&mut report, 26, repeats),
    _ => unreachable!(),
  }
  report.value["total_seconds"] = json!(start.elapsed().as_secs_f64());
  report.value["completed"] = json!(true);
  report.value["all_comparisons_passed"] = json!(true);
  report.save();
}
