use super::*;
use multi_stark::{cuda::CudaDft, witness::TraceSource};

pub(super) fn parity(program: &Toplevel, record: &QueryRecord, io: &IOBuffer) {
  let bound = generated_cuda::CUDA.bind(&generated::PROGRAM, program).unwrap();
  let dft = CudaDft::new(0);
  for (index, circuit) in program.circuits.iter().enumerate() {
    let mut expected = Vec::new();
    for &member in &circuit.members {
      for query in 0..record.function_queries[member].len() {
        if record.function_queries[member]
          .get_index(query)
          .unwrap()
          .1
          .multiplicity
          == G::ZERO
        {
          continue;
        }
        expected.extend(
          program
            .main_row_for_test(index, member, query, record, io)
            .into_iter()
            .map(|g| g.as_canonical_u64()),
        );
      }
    }
    if expected.is_empty() {
      continue;
    }
    let rows = expected.len() / circuit.layout.width();
    let last = circuit.members.len() - 1;
    let end = (last, record.function_queries[circuit.members[last]].len());
    let (source, _) =
      bound.prepare(index, record, io, &[], (0, 0), end, rows, true).unwrap();
    let TraceSource::Generated(source) = source else { unreachable!() };
    let height = rows.next_power_of_two();
    let width = circuit.layout.width();
    expected.resize(height * width, 0);
    let mut host = vec![G::ZERO; expected.len()];
    source.write_rows(0, &mut host);
    assert_eq!(
      host.iter().map(|g| g.as_canonical_u64()).collect::<Vec<_>>(),
      expected
    );
    for (first, rows) in [(0, height), (height - 1, height + 1)] {
      let actual = dft.generated_trace_rows(source.clone(), first, rows);
      // Goldilocks is repr(transparent) over u64. Reading raw words catches
      // noncanonical device output that field equality would otherwise hide.
      let raw = unsafe {
        std::slice::from_raw_parts(
          actual.values.as_ptr().cast::<u64>(),
          actual.values.len(),
        )
      };
      for (i, &word) in raw.iter().enumerate() {
        let row = (first + i / width) % height;
        assert_eq!(
          word,
          expected[row * width + i % width],
          "circuit {index}, row {row}, column {}",
          i % width
        );
        assert!(word < G::ORDER_U64);
      }
    }
  }
}

#[test]
fn regrouping_and_frozen_seeds() {
  let mut program = (generated::PROGRAM.expected)();
  program.circuits[0].members.swap(0, 1);
  let mut record = QueryRecord::new(&program);
  let mut io = io();
  for (function, args) in [
    (0, vec![G::ZERO, -G::ONE]),
    (3, vec![G::ONE, G::from_u8(255)]),
    (12, vec![]),
  ] {
    program.execute_in(function, args, &mut io, &mut record).unwrap();
  }
  parity(&program, &record, &io);
  let bound = generated_cuda::CUDA.bind(&generated::PROGRAM, &program).unwrap();
  let (source, _) =
    bound.prepare(0, &record, &io, &[], (0, 0), (3, 0), 3, true).unwrap();
  drop(record);
  drop(io);
  let TraceSource::Generated(source) = source else { unreachable!() };
  let expected = TraceSource::Generated(source.clone()).materialize();
  let actual = CudaDft::new(0).generated_trace_rows(source, 0, 4);
  assert_eq!(actual.values, expected.values);
}

unsafe extern "C" {
  fn cudaSetDevice(device: i32) -> i32;
  fn cudaMalloc(output: *mut *mut std::ffi::c_void, bytes: usize) -> i32;
  fn cudaFree(output: *mut std::ffi::c_void) -> i32;

}

struct DeviceBuffer(*mut std::ffi::c_void);
impl DeviceBuffer {
  fn new(bytes: usize) -> Self {
    let mut pointer = std::ptr::null_mut();
    assert_eq!(unsafe { cudaSetDevice(0) }, 0);
    assert_eq!(unsafe { cudaMalloc(&mut pointer, bytes) }, 0);
    Self(pointer)
  }
}
impl Drop for DeviceBuffer {
  fn drop(&mut self) {
    assert_eq!(unsafe { cudaFree(self.0) }, 0);
  }
}

fn synthetic_blake3(rows: usize) -> (Toplevel, QueryRecord, IOBuffer) {
  let program = (blake3::PROGRAM.expected)();
  let mut record = QueryRecord::new(&program);
  for i in 0..rows {
    let mut input = [G::ZERO; 129];
    input[0] = G::from_usize(i % 8);
    for (j, value) in input[1..].iter_mut().enumerate() {
      *value = G::from_usize((i * 37 + j * 19) % 256);
    }
    input[1] = G::from_usize(i & 255);
    input[2] = G::from_usize((i >> 8) & 255);
    input[3] = G::from_usize((i >> 16) & 255);
    let output = [G::from_u8(42); 32];
    record.function_queries[0]
      .insert(
        &input,
        &output,
        if i % 2 == 0 { -G::ONE } else { G::from_u64(1 << 40) },
      )
      .unwrap();
  }
  (program, record, io())
}

#[test]
#[ignore = "opt-in optimized same-input comparison with the handwritten CUDA writer"]
fn blake3_performance_gate() {
  assert!(!cfg!(debug_assertions), "run this benchmark with --release");
  use std::{hint::black_box, time::Instant};
  const ROWS: usize = 65536;
  let (program, record, io) = synthetic_blake3(ROWS);
  let compiled = blake3_cuda::CUDA.bind(&blake3::PROGRAM, &program).unwrap();
  let scalar = blake3::PROGRAM.bind(&program).unwrap();
  let writer = scalar.function(0).unwrap();
  let mut seed = vec![0; writer.seed_words()];
  let mut packed = vec![0; ROWS * 176];
  for (query, dst) in packed.chunks_exact_mut(176).enumerate() {
    writer.pack_row(&record, &io, query, false, &mut seed).unwrap();
    SeedEncoding::U8Payload.encode(&seed, dst).unwrap();
  }
  let output = DeviceBuffer::new(ROWS * 533 * 8);
  let generated = || {
    assert_eq!(
      unsafe {
        blake3_cuda::aiur_trace_blake3_0(
          0,
          packed.as_ptr(),
          1,
          ROWS,
          ROWS,
          533,
          129,
          131,
          output.0.cast(),
        )
      },
      0
    )
  };
  let handwritten = || {
    assert_eq!(
      unsafe {
        crate::gpu_trace::aiur_blake3_trace(
          0,
          packed.as_ptr().cast(),
          ROWS,
          ROWS,
          output.0.cast(),
        )
      },
      0
    )
  };
  let prepare_generated = || {
    black_box(
      compiled
        .prepare(0, &record, &io, &[], (0, 0), (0, ROWS), ROWS, false)
        .unwrap(),
    );
  };
  let prepare_handwritten = || {
    black_box(
      crate::gpu_trace::prepare(
        &program,
        0,
        &record,
        &[],
        (0, 0),
        (0, ROWS),
        ROWS,
      )
      .unwrap(),
    );
  };
  for _ in 0..3 {
    handwritten();
    generated();
  }
  prepare_handwritten();
  prepare_generated();
  let mut samples = [Vec::new(), Vec::new(), Vec::new(), Vec::new()];
  let cases: [&dyn Fn(); 4] =
    [&handwritten, &generated, &prepare_handwritten, &prepare_generated];
  for sample in 0..9 {
    let order = if sample % 2 == 0 { [0, 1, 2, 3] } else { [1, 0, 3, 2] };
    for index in order {
      let start = Instant::now();
      cases[index]();
      samples[index].push(start.elapsed().as_secs_f64() * 1000.0);
    }
  }
  for (name, sample) in [
    "upload_handwritten",
    "upload_generated",
    "prepare_handwritten",
    "prepare_generated",
  ]
  .iter()
  .zip(&mut samples)
  {
    sample.sort_by(f64::total_cmp);
    println!(
      "{name}: rows={ROWS}, median_ms={:.4}, samples_ms={sample:?}",
      sample[4]
    );
  }
  println!(
    "upload_ratio={:.4}, preparation_ratio={:.4}",
    samples[1][4] / samples[0][4],
    samples[3][4] / samples[2][4]
  );
}

#[test]
fn maximum_tile_and_wrapped_halo() {
  let (program, record, io) = synthetic_blake3(65537);
  let compiled = blake3_cuda::CUDA.bind(&blake3::PROGRAM, &program).unwrap();
  let (source, _) = compiled
    .prepare(0, &record, &io, &[], (0, 0), (0, 65537), 65537, false)
    .unwrap();
  let TraceSource::Generated(source) = source else { unreachable!() };
  let dft = CudaDft::new(0);
  for first in [0, 65536, 131070] {
    let actual = dft.generated_trace_rows(source.clone(), first, 65537);
    let mut expected = vec![G::ZERO; actual.values.len()];
    source.write_rows(first, &mut expected);
    for (i, (actual, expected)) in
      actual.values.iter().zip(&expected).enumerate()
    {
      assert_eq!(actual, expected, "row {}, column {}", i / 533, i % 533);
    }
  }
}

#[test]
fn concurrent_uploads_keep_frozen_seeds() {
  let devices: Vec<i32> = std::env::var("AIUR_TEST_GPU_DEVICES")
    .unwrap_or_else(|_| "0".into())
    .split(',')
    .map(|x| x.parse().unwrap())
    .collect();
  let (program, record, io) = synthetic_blake3(33);
  let bound = blake3_cuda::CUDA.bind(&blake3::PROGRAM, &program).unwrap();
  let (source, _) =
    bound.prepare(0, &record, &io, &[], (0, 0), (0, 33), 33, false).unwrap();
  let TraceSource::Generated(source) = source else { unreachable!() };
  let barrier = std::sync::Barrier::new(8);
  std::thread::scope(|scope| {
    for worker in 0..8 {
      let source = source.clone();
      let barrier = &barrier;
      let device = devices[worker % devices.len()];
      scope.spawn(move || {
        let dft = CudaDft::new(device);
        barrier.wait();
        for first in [0, 32, 63] {
          let actual = dft.generated_trace_rows(source.clone(), first, 65);
          let mut expected = vec![G::ZERO; actual.values.len()];
          source.write_rows(first, &mut expected);
          assert_eq!(actual.values, expected);
        }
      });
    }
  });
}

#[test]
fn device_errors_release_the_staging_lease() {
  let output = DeviceBuffer::new(24);
  let mut seed = [0u8; 16];
  seed[0] = 1;
  seed[8] = 7;
  let write = |seed: &[u8; 16], encoding| unsafe {
    generated_cuda::aiur_trace_fixtures_19(
      0,
      seed.as_ptr(),
      encoding,
      1,
      1,
      3,
      1,
      2,
      output.0.cast(),
    )
  };
  // More failures than staging slots detects leases stranded by an error.
  for _ in 0..8 {
    assert_eq!(write(&seed, 1), 10002);
  }
  assert_ne!(write(&seed, 2), 0);
  seed[8] = 0;
  assert_eq!(write(&seed, 1), 0);
}

#[test]
fn cuda_binding_rejects_changed_seed_width() {
  let program = (blake3::PROGRAM.expected)();
  let mut functions = blake3::PROGRAM.functions.to_vec();
  functions[0].as_mut().unwrap().seed_words = 1;
  let changed = Box::leak(Box::new(GeneratedProgram {
    fingerprint: blake3::PROGRAM.fingerprint,
    complete: true,
    expected: blake3::PROGRAM.expected,
    functions: Box::leak(functions.into_boxed_slice()),
  }));
  assert!(blake3_cuda::CUDA.bind(changed, &program).is_err());
}

#[test]
fn mixed_codecs_bound_unused_seed_capacity() {
  let program = (generated::PROGRAM.expected)();
  let mut record = QueryRecord::new(&program);
  for i in 0..1024_u64 {
    let high = if i % 2 == 0 { 0 } else { 1 << 32 };
    record.function_queries[0]
      .insert(&[G::from_u64(high + i / 256), G::from_u64(i % 256)], &[], G::ONE)
      .unwrap();
  }
  let bound = generated_cuda::CUDA.bind(&generated::PROGRAM, &program).unwrap();
  let (source, _) = bound
    .prepare(0, &record, &io(), &[], (0, 0), (0, 1024), 1024, false)
    .unwrap();
  let TraceSource::Generated(source) = source else { unreachable!() };
  assert!(
    source.host_bytes() < 512 * 1024,
    "mixed codecs retained unused tile reservations: {}",
    source.host_bytes()
  );
}
