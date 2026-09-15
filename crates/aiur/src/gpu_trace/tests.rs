use super::*;
use crate::{
  bytecode::{Circuit, Function},
  execute::IOBuffer,
};
use multi_stark::p3_matrix::Matrix;

pub(crate) fn toplevel() -> Toplevel {
  Toplevel {
    functions: vec![Function {
      body: blake3_body::body(0),
      layout: LAYOUT,
      entry: true,
      constrained: true,
    }],
    circuits: vec![Circuit { members: vec![0], layout: LAYOUT }],
    memory_sizes: vec![],
  }
}

fn io() -> IOBuffer {
  IOBuffer { data: Default::default(), map: Default::default() }
}

#[test]
fn compiled_signature_rejects_changed_body() {
  let mut top = toplevel();
  assert!(supported(&top, 0));
  top.functions[0].body.ops.push(crate::bytecode::Op::Const(G::ONE));
  assert!(!supported(&top, 0));
}

#[test]
fn seeds_reject_values_that_would_be_truncated() {
  let top = toplevel();
  for (index, value, output_value, output_len) in [
    (0, G::from_u8(8), G::ZERO, 32),
    (1, G::from_u16(256), G::ZERO, 32),
    (128, G::NEG_ONE, G::ZERO, 32),
    (0, G::ZERO, G::from_u16(256), 32),
    (0, G::ZERO, G::NEG_ONE, 32),
    (0, G::ZERO, G::ZERO, 31),
  ] {
    let mut input = vec![G::ZERO; 129];
    input[index] = value;
    let output = vec![output_value; output_len];
    let mut record = QueryRecord::new(&top);
    record.function_queries[0].insert(&input, &output, G::ONE);
    assert!(prepare(&top, 0, &record, &[], (0, 0), (0, 1), 1).is_none());
  }
}

#[test]
fn failed_device_writer_releases_its_source() {
  struct Failing;
  impl TraceGenerator<G> for Failing {
    fn height(&self) -> usize {
      8
    }
    fn width(&self) -> usize {
      WIDTH
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
    multi_stark::cuda::CudaDft::new(0).generate_coset_lde(
      source,
      2,
      G::GENERATOR,
    )
  }));
  assert!(result.is_err());
  assert!(weak.upgrade().is_none(), "failed generation leaked its source");
}

#[test]
fn blake3_cells_match_bytecode_and_cuda() {
  let top = toplevel();
  let slots: Vec<_> =
    top.build_constraints(0).1.iter().map(|l| l.args.len()).collect();
  let mut io = io();
  let mut record = QueryRecord::new(&top);
  for stage in 0..8 {
    for pattern in 0..3 {
      let mut input = vec![G::from_usize(stage)];
      input.extend((0..128).map(|i| {
        G::from_usize(match pattern {
          0 => 0,
          1 => 255,
          _ => (i * 37 + stage * 19) % 256,
        })
      }));
      top.execute_in(0, input.clone(), &mut io, &mut record).unwrap();
      top.execute_in(0, input, &mut io, &mut record).unwrap();
    }
  }
  *record.function_queries[0].get_index_mut(2).unwrap().1 = G::ZERO;
  *record.function_queries[0].get_index_mut(5).unwrap().1 = G::NEG_ONE;
  let len = record.function_queries[0].len();
  for (lo, hi) in [(0, len), (0, 1), (1, 4), (2, 7), (3, 20)] {
    let rows = record.function_queries[0]
      .iter()
      .skip(lo)
      .take(hi - lo)
      .filter(|(_, result)| !result.multiplicity.is_zero())
      .count();
    let (reference, _) =
      top.witness_data_range(0, &record, &io, &slots, (0, lo), (0, hi), rows);
    let (generated, _) =
      prepare(&top, 0, &record, &slots, (0, lo), (0, hi), rows).unwrap();
    let TraceSource::Generated(source) = generated else {
      panic!("expected GPU source")
    };
    let mut scalar = vec![G::ZERO; reference.values.len()];
    source.write_rows(0, &mut scalar);
    assert_eq!(
      scalar, reference.values,
      "scalar specialized writer differs at span {lo}..{hi}"
    );
    let dft = multi_stark::cuda::CudaDft::new(0);
    let device =
      dft.generated_trace_rows(Arc::clone(&source), 0, reference.height());
    assert_eq!(
      device.values, reference.values,
      "CUDA writer differs at span {lo}..{hi}"
    );
    for value in &device.values {
      let raw = unsafe { *(value as *const G).cast::<u64>() };
      assert_eq!(
        raw,
        value.as_canonical_u64(),
        "noncanonical device field encoding"
      );
    }
    let halo =
      dft.generated_trace_rows(Arc::clone(&source), reference.height() - 1, 2);
    let mut expected =
      reference.values[(reference.height() - 1) * WIDTH..].to_vec();
    expected.extend_from_slice(&reference.values[..WIDTH]);
    assert_eq!(halo.values, expected, "wrapped lookup halo differs");
  }
  assert!(prepare(&top, 0, &record, &slots, (0, 0), (0, 0), 0).is_none());
}

fn patterned_source(rows: usize, salt: usize) -> Arc<dyn TraceGenerator<G>> {
  Arc::new(Blake3Trace {
    seeds: (0..rows)
      .map(|r| Blake3Seed {
        multiplicity: (G::NEG_ONE - G::from_usize(r + salt)).as_canonical_u64(),
        stage: ((r + salt) % 8) as u8,
        input: std::array::from_fn(|i| ((r * 37 + i + salt) % 256) as u8),
        output: std::array::from_fn(|i| ((r + i * 19 + salt) % 256) as u8),
        padding: [0; 7],
      })
      .collect(),
    height: rows.next_power_of_two(),
  })
}

#[test]
fn maximum_seed_tile_and_padding_match_scalar() {
  let source = patterned_source(65537, 0);
  let dft = multi_stark::cuda::CudaDft::new(0);
  for (first, rows) in [(0, 65537), (65536, 3), (131071, 2)] {
    let actual = dft.generated_trace_rows(Arc::clone(&source), first, rows);
    let mut expected = vec![G::ZERO; rows * WIDTH];
    source.write_rows(first, &mut expected);
    assert_eq!(actual.values, expected, "tile starting at {first}");
  }
}

#[test]
fn concurrent_seed_uploads_keep_distinct_contents() {
  let devices: Vec<i32> = std::env::var("AIUR_TEST_GPU_DEVICES")
    .unwrap_or_else(|_| "0".into())
    .split(',')
    .map(|s| s.parse().unwrap())
    .collect();
  let ready = std::sync::Barrier::new(8);
  std::thread::scope(|scope| {
    for worker in 0..8 {
      let ready = &ready;
      let device = devices[worker % devices.len()];
      scope.spawn(move || {
        let source = patterned_source(4095, worker * 13);
        let dft = multi_stark::cuda::CudaDft::new(device);
        ready.wait();
        for first in [0, 1, 4095, 23] {
          let mut expected = vec![G::ZERO; 4096 * WIDTH];
          source.write_rows(first, &mut expected);
          let actual =
            dft.generated_trace_rows(Arc::clone(&source), first, 4096);
          assert_eq!(actual.values, expected, "worker {worker}, first {first}");
        }
      });
    }
  });
}

#[test]
fn blake3_sources_and_trees_stay_on_their_device() {
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
  let top = toplevel();
  let mut input = vec![G::ZERO];
  input.extend((0..128).map(|i| G::from_usize(i)));
  let (record, _) = top.execute(0, input, &mut io()).unwrap();
  let slots =
    top.build_constraints(0).1.iter().map(|l| l.args.len()).collect::<Vec<_>>();
  let (source, _) =
    prepare(&top, 0, &record, &slots, (0, 0), (1, 0), 8).unwrap();
  let devices: Vec<i32> = std::env::var("AIUR_TEST_GPU_DEVICES")
    .unwrap_or_else(|_| "0".into())
    .split(',')
    .map(|s| s.parse().unwrap())
    .collect();
  let results = std::thread::scope(|scope| {
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
          let (root, data) =
            config.commit_main(vec![(domain, source.clone())], None);
          let tree = config.checkpoint_main(data, 1 << 20).unwrap();
          let (restored, data) =
            config.commit_main(vec![(domain, source)], Some(tree));
          assert_eq!(root, restored);
          drop(data);
          root
        })
      })
      .collect();
    handles.into_iter().map(|h| h.join().unwrap()).collect::<Vec<_>>()
  });
  assert!(results.windows(2).all(|pair| pair[0] == pair[1]));
}
