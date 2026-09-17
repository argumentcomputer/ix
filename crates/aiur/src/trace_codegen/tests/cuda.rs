use super::*;
use std::sync::Arc;

use multi_stark::{
  cuda::CudaDft,
  p3_field::Field,
  p3_matrix::Matrix,
  witness::{TraceGenerator, TraceSource},
};

use crate::trace_codegen::cuda::prepare_memory;

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
    let height = rows.next_power_of_two();
    let width = circuit.layout.width();
    expected.resize(height * width, 0);
    // Alias checking forces the canonical codec; without it the typed codec
    // is used wherever the guards pass. Both must reproduce the oracle.
    for check_aliases in [true, false] {
      let (source, _) = bound
        .prepare(index, record, io, &[], (0, 0), end, rows, check_aliases)
        .unwrap();
      let TraceSource::Generated(source) = source else { unreachable!() };
      let mut host = vec![G::ZERO; expected.len()];
      source.write_rows(0, &mut host);
      assert_eq!(
        host.iter().map(|g| g.as_canonical_u64()).collect::<Vec<_>>(),
        expected,
        "circuit {index}, check_aliases {check_aliases}: CPU mirror"
      );
      for (first, rows) in [(0, height), (height - 1, height + 1)] {
        let actual = dft.generated_trace_rows(source.clone(), first, rows);
        // Goldilocks is repr(transparent) over u64. Reading raw words
        // catches noncanonical device output that field equality would
        // otherwise hide.
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
            "circuit {index}, check_aliases {check_aliases}, row {row}, column {}",
            i % width
          );
          assert!(word < G::ORDER_U64);
        }
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

/// Timings of the generated BLAKE3 provider on one tile: typed against
/// canonical upload plus generation, and seed preparation against
/// materializing the same rows on the host. The retired handwritten kernel
/// measured 2.30 ms upload and 7.45 to 7.84 ms preparation on this tile.
#[test]
#[ignore = "opt-in timing of the generated BLAKE3 provider on one GPU"]
fn blake3_generated_timing() {
  assert!(!cfg!(debug_assertions), "run this benchmark with --release");
  use std::{hint::black_box, time::Instant};
  const ROWS: usize = 65536;
  let (program, record, io) = synthetic_blake3(ROWS);
  let compiled = blake3_cuda::CUDA.bind(&blake3::PROGRAM, &program).unwrap();
  let scalar = blake3::PROGRAM.bind(&program).unwrap();
  let writer = scalar.function(0).unwrap();
  let schema = writer.schema();
  // Multiplicity, then the stage as a full word, then 160 bytes.
  assert_eq!(schema.bytes, 176);
  assert_eq!(schema.offsets[1], 8);
  assert!(schema.offsets[2..].iter().enumerate().all(|(i, &o)| o == 16 + i));
  let canonical_stride = SeedEncoding::Canonical.stride(schema);
  let mut seed = vec![0; writer.seed_words()];
  let mut typed = vec![0; ROWS * schema.bytes];
  let mut canonical = vec![0; ROWS * canonical_stride];
  for query in 0..ROWS {
    writer.pack_row(&record, &io, query, false, &mut seed).unwrap();
    SeedEncoding::Typed
      .encode(
        schema,
        &seed,
        &mut typed[query * schema.bytes..(query + 1) * schema.bytes],
      )
      .unwrap();
    SeedEncoding::Canonical
      .encode(
        schema,
        &seed,
        &mut canonical
          [query * canonical_stride..(query + 1) * canonical_stride],
      )
      .unwrap();
  }
  let output = DeviceBuffer::new(ROWS * 533 * 8);
  // Canonical seeds for a whole tile exceed the staging lease, so both
  // encodings are uploaded in the chunks the runtime would use for the
  // wider one, keeping the launch count equal.
  let chunk = (16 * 1024 * 1024 - 8) / canonical_stride;
  let upload = |seeds: &[u8], stride: usize, encoding: u32, chunk: usize| {
    for first in (0..ROWS).step_by(chunk) {
      let rows = chunk.min(ROWS - first);
      assert_eq!(
        unsafe {
          blake3_cuda::aiur_trace_blake3_0(
            0,
            seeds[first * stride..].as_ptr(),
            encoding,
            rows,
            rows,
            533,
            129,
            131,
            output.0.cast::<u64>().add(first * 533),
          )
        },
        0
      )
    }
  };
  let prepare = || {
    compiled
      .prepare(0, &record, &io, &[], (0, 0), (0, ROWS), ROWS, false)
      .unwrap()
  };
  let (source, _) = prepare();
  let TraceSource::Generated(source) = source else { unreachable!() };
  let mut host = vec![G::ZERO; ROWS * 533];
  // Production uploads a span as one call, so the typed tile also runs in
  // the spans `prepare` would cut, as the runtime's pipeline sees them.
  let span = (16 * 1024 * 1024 - 8) / schema.bytes;
  println!(
    "strides: canonical={canonical_stride}, typed={}, typed_span_rows={span}",
    schema.bytes
  );
  let mut cases: [(&str, Box<dyn FnMut()>); 5] = [
    (
      "upload_canonical",
      Box::new(|| upload(&canonical, canonical_stride, 0, chunk)),
    ),
    ("upload_typed", Box::new(|| upload(&typed, schema.bytes, 1, chunk))),
    (
      "upload_typed_span",
      Box::new(|| upload(&typed, schema.bytes, 1, span)),
    ),
    ("cpu_rows", Box::new(|| source.write_rows(0, &mut host))),
    (
      "prepare_generated",
      Box::new(|| {
        black_box(prepare());
      }),
    ),
  ];
  for (_, case) in &mut cases {
    for _ in 0..2 {
      case();
    }
  }
  let mut samples = [const { Vec::new() }; 5];
  for sample in 0..9 {
    let order =
      if sample % 2 == 0 { [0, 1, 2, 3, 4] } else { [2, 1, 0, 4, 3] };
    for index in order {
      let start = Instant::now();
      (cases[index].1)();
      samples[index].push(start.elapsed().as_secs_f64() * 1000.0);
    }
  }
  for ((name, _), sample) in cases.iter().zip(&mut samples) {
    sample.sort_by(f64::total_cmp);
    println!(
      "{name}: rows={ROWS}, median_ms={:.4}, samples_ms={sample:?}",
      sample[4]
    );
  }
  println!(
    "typed_over_canonical_upload={:.4}, prepare_over_cpu_rows={:.4}",
    samples[1][4] / samples[0][4],
    samples[4][4] / samples[3][4]
  );
}

#[test]
fn failed_device_writer_releases_its_source() {
  struct Failing;
  impl TraceGenerator<G> for Failing {
    fn height(&self) -> usize {
      8
    }
    fn width(&self) -> usize {
      3
    }
    fn host_bytes(&self) -> usize {
      0
    }
    fn write_rows(&self, _: usize, _: &mut [G]) {
      unreachable!()
    }
    fn write_device_rows(
      &self,
      _: multi_stark::cuda::DeviceTraceView<'_>,
    ) -> Result<(), String> {
      Err("fixture failure".into())
    }
  }
  let source: Arc<dyn TraceGenerator<G>> = Arc::new(Failing);
  let weak = Arc::downgrade(&source);
  let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
    CudaDft::new(0).generate_coset_lde(source, 2, G::GENERATOR)
  }));
  assert!(result.is_err());
  assert!(weak.upgrade().is_none(), "failed generation leaked its source");
}

#[test]
fn generated_sources_and_commitments_stay_on_their_device() {
  use multi_stark::{
    config::StarkGenericConfig,
    types::{CommitmentParameters, FriParameters, GoldilocksBlake3Config},
  };
  let cp = CommitmentParameters { log_blowup: 2, cap_height: 0 };
  let fp = FriParameters {
    log_final_poly_len: 0,
    max_log_arity: 1,
    num_queries: 64,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 0,
  };
  let program = (blake3::PROGRAM.expected)();
  let mut io = io();
  let mut input = vec![G::ZERO];
  input.extend((0..128).map(G::from_usize));
  let (record, _) = program.execute(0, input, &mut io).unwrap();
  let count = record.function_queries[0].len();
  assert_eq!(count, 8, "one query per BLAKE3 stage");
  let compiled = blake3_cuda::CUDA.bind(&blake3::PROGRAM, &program).unwrap();
  let (source, _) = compiled
    .prepare(0, &record, &io, &[], (0, 0), (0, count), count, false)
    .unwrap();
  let devices: Vec<i32> = std::env::var("AIUR_TEST_GPU_DEVICES")
    .unwrap_or_else(|_| "0".into())
    .split(',')
    .map(|s| s.parse().unwrap())
    .collect();
  let roots = std::thread::scope(|scope| {
    let handles: Vec<_> = devices
      .into_iter()
      .map(|device| {
        let source = source.clone();
        scope.spawn(move || {
          let config =
            GoldilocksBlake3Config::with_device(cp, fp, Some(device));
          let domain =
            multi_stark::config::Domain::<GoldilocksBlake3Config>::new(
              G::ONE,
              3,
            )
            .unwrap();
          let (root, data) = config.commit_main(vec![(domain, source.clone())]);
          drop(data);
          let (regenerated, data) = config.commit_main(vec![(domain, source)]);
          assert_eq!(root, regenerated);
          drop(data);
          root
        })
      })
      .collect();
    handles.into_iter().map(|h| h.join().unwrap()).collect::<Vec<_>>()
  });
  assert!(roots.windows(2).all(|pair| pair[0] == pair[1]));
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
fn cuda_binding_rejects_changed_seed_layout_of_the_same_size() {
  // Swap the stage word and the first message byte: same words, same 176
  // bytes, consistent offsets, different layout. The kernel would read the
  // packer's bytes in the wrong places, so the schema contract must reject it.
  let program = (blake3::PROGRAM.expected)();
  let mut functions = blake3::PROGRAM.functions.to_vec();
  let writer = functions[0].as_mut().unwrap();
  let mut widths = writer.schema.widths.to_vec();
  widths.swap(1, 2);
  let mut offsets = vec![0; widths.len()];
  let mut cursor = 0;
  for width in [SeedWidth::Full, SeedWidth::U32, SeedWidth::U16, SeedWidth::U8]
  {
    for (i, &w) in widths.iter().enumerate() {
      if w == width {
        offsets[i] = cursor;
        cursor += width.bytes();
      }
    }
  }
  let schema: &'static SeedSchema = Box::leak(Box::new(SeedSchema {
    widths: Box::leak(widths.into_boxed_slice()),
    offsets: Box::leak(offsets.into_boxed_slice()),
    bytes: writer.schema.bytes,
  }));
  assert!(schema.is_consistent());
  writer.schema = schema;
  let changed = Box::leak(Box::new(GeneratedProgram {
    fingerprint: blake3::PROGRAM.fingerprint,
    complete: true,
    expected: blake3::PROGRAM.expected,
    functions: Box::leak(functions.into_boxed_slice()),
  }));
  assert!(changed.bind(&program).is_ok(), "the layout alone is well formed");
  assert_eq!(
    blake3_cuda::CUDA.bind(changed, &program).err(),
    Some("CUDA unit was compiled for different seed layouts")
  );
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
fn wide_rows_widen_the_member_span_once() {
  // Function 3's value input is speculatively a byte. Alternating byte rows
  // through the default arm and wide rows through the multiply arm must
  // produce one full-width span for the whole run, matching CPU rows,
  // without retaining typed reservations.
  let program = (generated::PROGRAM.expected)();
  let mut record = QueryRecord::new(&program);
  let mut io = io();
  for i in 0..1024_u64 {
    let (tag, value) =
      if i % 2 == 0 { (2 + i / 256, i % 256) } else { (0, (1 << 32) + i) };
    program
      .execute_in(
        3,
        vec![G::from_u64(tag), G::from_u64(value)],
        &mut io,
        &mut record,
      )
      .unwrap();
  }
  assert_eq!(record.function_queries[3].len(), 1024);
  let circuit = circuit_of(&program, 3);
  let member =
    program.circuits[circuit].members.iter().position(|&f| f == 3).unwrap();
  let bound = generated_cuda::CUDA.bind(&generated::PROGRAM, &program).unwrap();
  let (source, _) = bound
    .prepare(
      circuit,
      &record,
      &io,
      &[],
      (member, 0),
      (member, 1024),
      1024,
      false,
    )
    .unwrap();
  let TraceSource::Generated(source) = source else { unreachable!() };
  let words = bound_words(&generated::PROGRAM, 3);
  assert!(source.host_bytes() >= 1024 * 8 * words);
  assert!(
    source.host_bytes() < 2 * 1024 * 8 * words + 1024,
    "widened span retained unused reservations: {}",
    source.host_bytes()
  );
  let width = program.circuits[circuit].layout.width();
  let mut expected = vec![G::ZERO; 1024 * width];
  source.write_rows(0, &mut expected);
  let actual = CudaDft::new(0).generated_trace_rows(source, 0, 1024);
  assert_eq!(actual.values, expected);
}

fn bound_words(program: &GeneratedProgram, function: usize) -> usize {
  program.functions[function].as_ref().unwrap().seed_words
}

#[test]
fn wide_row_in_a_later_chunk_widens_earlier_chunks() {
  // Three packing chunks of function 3 rows, all bytes except one wide value
  // in the third chunk, with zero-multiplicity queries scattered through the
  // run. Every chunk must end up full width, rows must keep query order with
  // the dead queries skipped, and the device rows must match the oracle.
  const ROWS: u64 = 3 * 4096 + 300;
  let program = (generated::PROGRAM.expected)();
  let mut record = QueryRecord::new(&program);
  let mut io = io();
  for i in 0..ROWS {
    let (tag, value) = if i == 2 * 4096 + 777 {
      (0, (1 << 32) + i)
    } else {
      (2 + i / 256, i % 256)
    };
    program
      .execute_in(
        3,
        vec![G::from_u64(tag), G::from_u64(value)],
        &mut io,
        &mut record,
      )
      .unwrap();
  }
  assert_eq!(record.function_queries[3].len(), ROWS as usize);
  for dead in [0usize, 5, 4095, 4096, 9000, ROWS as usize - 1] {
    *record.function_queries[3].get_index_mut(dead).unwrap().1 = G::ZERO;
  }
  let live: Vec<usize> = (0..ROWS as usize)
    .filter(|&q| {
      record.function_queries[3].get_index(q).unwrap().1.multiplicity != G::ZERO
    })
    .collect();
  let circuit = circuit_of(&program, 3);
  let member =
    program.circuits[circuit].members.iter().position(|&f| f == 3).unwrap();
  let bound = generated_cuda::CUDA.bind(&generated::PROGRAM, &program).unwrap();
  let (source, _) = bound
    .prepare(
      circuit,
      &record,
      &io,
      &[],
      (member, 0),
      (member, ROWS as usize),
      live.len(),
      false,
    )
    .unwrap();
  let TraceSource::Generated(source) = source else { unreachable!() };
  let words = bound_words(&generated::PROGRAM, 3);
  assert!(
    source.host_bytes() >= live.len() * 8 * words,
    "the whole run is full width: {}",
    source.host_bytes()
  );
  let width = program.circuits[circuit].layout.width();
  let height = live.len().next_power_of_two();
  let mut expected: Vec<u64> = live
    .iter()
    .flat_map(|&q| program.main_row_for_test(circuit, 3, q, &record, &io))
    .map(|g| g.as_canonical_u64())
    .collect();
  expected.resize(height * width, 0);
  let mut host = vec![G::ZERO; height * width];
  source.write_rows(0, &mut host);
  assert_eq!(
    host.iter().map(|g| g.as_canonical_u64()).collect::<Vec<_>>(),
    expected,
    "CPU mirror"
  );
  let actual = CudaDft::new(0).generated_trace_rows(source, 0, height);
  assert_eq!(
    actual.values.iter().map(|g| g.as_canonical_u64()).collect::<Vec<_>>(),
    expected,
    "device rows"
  );
}

#[test]
fn memory_tables_match_the_cpu_builder() {
  use crate::memory::Memory;
  // Two widths, a nonzero pointer namespace, zero and negative
  // multiplicities, and ranges that start past the table's first entry.
  let program = (generated::PROGRAM.expected)();
  let mut record = QueryRecord::with_pointer_base(&program, 1 << 30);
  for (width, entries) in [(2usize, 300usize), (10, 4097)] {
    let table = record.memory_queries.get_mut(&width).unwrap();
    for i in 0..entries {
      let values: Vec<G> = (0..width)
        .map(|j| G::from_u64(((i * 977 + j * 131) as u64) << 40 | i as u64))
        .collect();
      let multiplicity = match i % 3 {
        0 => G::ZERO,
        1 => -G::from_usize(i),
        _ => G::from_usize(i),
      };
      table
        .insert(
          &values,
          &[G::from_usize(record.pointer_base + i)],
          multiplicity,
        )
        .unwrap();
    }
  }
  let dft = CudaDft::new(0);
  for (width, ranges) in [
    (2usize, vec![0..300, 5..300, 299..300]),
    (10, vec![0..4097, 4096..4097, 13..2000]),
  ] {
    for range in ranges {
      let (expected, _) =
        Memory::witness_data_range(width, &record, &[], range.clone());
      let (source, _) =
        prepare_memory(&record, width, &[], range.clone()).unwrap();
      let TraceSource::Generated(source) = source else { unreachable!() };
      assert_eq!(source.height(), expected.height());
      let mut host = vec![G::ZERO; expected.values.len()];
      source.write_rows(0, &mut host);
      assert_eq!(
        host, expected.values,
        "width {width}, range {range:?}: CPU mirror"
      );
      let height = expected.height();
      for (first, rows) in [(0, height), (height - 1, height + 1)] {
        let actual = dft.generated_trace_rows(source.clone(), first, rows);
        let w = width + 3;
        for (i, cell) in actual.values.iter().enumerate() {
          let row = (first + i / w) % height;
          assert_eq!(
            *cell,
            expected.values[row * w + i % w],
            "width {width}, range {range:?}, row {row}, column {}",
            i % w
          );
        }
      }
    }
  }
  assert!(prepare_memory(&record, 2, &[], 0..0).is_err());
  assert!(prepare_memory(&record, 2, &[], 0..301).is_err());
}
