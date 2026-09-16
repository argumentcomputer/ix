use super::*;
use crate::{
  hash::pack_bytes,
  ixby::{
    ixbf::DecodeLimits,
    paged_frame::{HEAP, LOCALS, Phase},
    paged_value::INPUT_BYTES,
  },
};
use flock_prover::circuit::builder::ShapeBuilder;

// Independently encoded format-1, semantics-0 identity: arity 1, return local 0.
const IDENTITY: &[u8] = &[
  b'I', b'X', b'B', b'F', 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 8, 0x80,
  0x20, 64, 64, 24, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0,
];
fn input(value: &[u8]) -> Vec<u8> {
  b"IXFI\x01\0\0\0\0\0\0\0\x01".iter().chain(value).copied().collect()
}
fn natural(mut n: u128) -> Vec<u8> {
  let mut out = Vec::new();
  loop {
    let low = n as u8 & 127;
    n >>= 7;
    out.push(low | if n == 0 { 0 } else { 128 });
    if n == 0 {
      return out;
    }
  }
}

#[test]
fn production_execution_setups_validate_every_driver_and_complete_boundaries() {
  let source = input(&[0, 3, 1, 2, 3, 4]);
  for class in [
    BatchClass::Small,
    BatchClass::Objects,
    BatchClass::Compact,
    BatchClass::Bytes,
    BatchClass::SharedCompact,
  ] {
    let compiled = CompiledPagedExecution::compile(class).unwrap();
    let mut image =
      NativeImage::load(IDENTITY, &source, DecodeLimits::default()).unwrap();
    let initial_root = image.memory.root();
    let mut machine = image.machine().unwrap();
    let advice = machine.batch(class, &mut image.memory).unwrap().unwrap();
    compiled.check_advice(&advice).unwrap();
    let statement = ExecutionStatement::from_words(&advice.expected).unwrap();
    assert_eq!(statement.parameters(), &image.parameters);
    assert_eq!(statement.initial()[0], F128::ZERO);
    assert_eq!(statement.initial()[1..25], image.state);
    assert_eq!(statement.initial()[25..], initial_root);
    assert_eq!(statement.final_state()[0], F128::new(4, 0));
    assert_eq!(statement.final_state()[1..25], machine.state);
    assert_eq!(statement.final_state()[25..], image.memory.root());
    assert!(machine.next_chip().unwrap().is_none());
    for (at, value) in [
      (3, F128::new(4, 0)),
      (30, F128::ZERO),
      (30, F128::new(1 << 59, 0)),
      (30, F128::new(4, 1)),
    ] {
      let mut bad = advice.expected.clone();
      bad[at] = value;
      assert!(ExecutionStatement::from_words(&bad).is_err());
    }
    assert_eq!(compiled.public_template().outputs(), PUBLIC_WORDS);
  }
}

#[test]
fn original_scalar_payloads_and_byte_ranges_survive_native_loading() {
  let wide = (1u128 << 65) + 7;
  let mut nat = vec![0, 0];
  nat.extend(natural(wide));
  let cases = [
    (nat, [F128::new(8, 0), F128::new(7, 2)]),
    (vec![0, 2, 1], [F128::ONE, F128::ONE]),
    (vec![0, 3, 1, 2, 3, 4], [F128::new(2, 0), F128::new(0x04030201, 0)]),
    (vec![0, 4, 17, 0, 0, 0, 0, 0, 0, 0], [F128::new(3, 0), F128::new(17, 0)]),
    (
      vec![0, 5, 17, 0, 0, 0, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0],
      [F128::new(4, 0), F128::new(17, 19)],
    ),
    (vec![3], [F128::new(5, 0), F128::ZERO]),
    (vec![0, 6, 0], [F128::new(6, 0), F128::ZERO]),
    (vec![0, 1, 0], [F128::new(10, 0), F128::ZERO]),
    (
      vec![0, 6, 3, 0x03, 0xfe, 0x11],
      [F128::new(6, 0), F128::new((INPUT_BYTES << 5) + 16, 3)],
    ),
    (
      vec![0, 1, 2, 0xc3, 0xa9],
      [F128::new(10, 0), F128::new((INPUT_BYTES << 5) + 16, 2)],
    ),
  ];
  for (value, expected) in cases {
    let source = input(&value);
    let image =
      NativeImage::load(IDENTITY, &source, DecodeLimits::default()).unwrap();
    assert_eq!(image.memory.value(LOCALS).unwrap(), expected);
    assert_eq!(
      image.parameters,
      [F128::new(1, 0), F128::new(24, 0), F128::new(4096, 64)]
    );
    assert_eq!(image.state[HEAP_COUNT], F128::ZERO);
    assert_eq!(image.state[BYTE_COUNT], F128::ZERO);
    let mut bytes = [0; 32];
    bytes[..source.len()].copy_from_slice(&source);
    assert_eq!(
      image.memory.value(INPUT_BYTES).unwrap(),
      [pack_bytes(&bytes[..16]), pack_bytes(&bytes[16..])]
    );
  }
}

#[test]
fn nested_constructor_and_partial_application_input_runs_in_actual_batch() {
  let id = [vec![0xa5; 32], vec![1, 2]].concat();
  let mut program = IDENTITY[..12].to_vec();
  // Limits, budget, entry and the complete one-constructor declaration.
  program.extend([2, 1, 1, 3, 3, 0, 8, 0x80, 0x20, 64, 64, 24, 0, 1]);
  program.extend(&id);
  program.extend([2, 2]); // two fields, two functions
  program.extend([1, 0, 1, 1, 1, 0, 0]); // identity, arity 1
  program.extend([3, 0, 1, 3, 1, 0, 2]); // arity 3, return local 2
  let mut value = vec![1];
  value.extend(&id);
  value.extend([2, 0, 3, 1, 2, 3, 4, 2, 1, 2, 0, 0]);
  value.extend(natural((1u128 << 65) + 7));
  value.push(3);
  let source = input(&value);
  let mut image =
    NativeImage::load(&program, &source, DecodeLimits::default()).unwrap();
  let root = [F128::new(7, 0), F128::new(HEAP, 2)];
  assert_eq!(image.state[HEAP_COUNT], F128::new(4, 0));
  assert_eq!(image.memory.value(LOCALS).unwrap(), root);
  for (i, expected) in [
    [F128::new(2, 0), F128::new(0x04030201, 0)],
    [F128::new(9, 1), F128::new(HEAP + 2, 2)],
    [F128::new(8, 0), F128::new(7, 2)],
    [F128::new(5, 0), F128::ZERO],
  ]
  .into_iter()
  .enumerate()
  {
    assert_eq!(image.memory.value(HEAP + i as u64).unwrap(), expected);
  }
  let mut machine = image.machine().unwrap();
  let advice =
    machine.batch(BatchClass::Compact, &mut image.memory).unwrap().unwrap();
  assert_eq!(machine.clock, 4);
  assert_eq!(machine.state[0].lo, Phase::Halted as u64);
  assert_eq!(machine.state[2..4], root);
  assert_eq!(machine.state[FUEL], F128::new(22, 2));
  let mut builder = ShapeBuilder::new(BatchClass::Compact.nu());
  let emission = emit_batch(&mut builder, BatchClass::Compact).unwrap();
  let shape = builder.finish().unwrap();
  let witness =
    shape.run(&emission.inputs.assign(&advice.private).unwrap(), &[]);
  assert_eq!(
    witness.public,
    emission.public.instantiate(&advice.expected).unwrap()
  );
}

#[test]
fn native_loading_rejects_truncation_and_unrepresentable_functional_values() {
  let source = input(&[0, 6, 3, 1, 2, 3]);
  for end in 0..source.len() {
    assert!(
      NativeImage::load(IDENTITY, &source[..end], DecodeLimits::default())
        .is_err()
    );
  }
  let mut program = IDENTITY.to_vec();
  program.splice(19..21, [127]);
  assert!(
    NativeImage::load(&program, &source, DecodeLimits::default()).is_err()
  );
  let mut program = IDENTITY.to_vec();
  program.splice(23..24, natural(1u128 << 65));
  assert!(
    NativeImage::load(&program, &source, DecodeLimits::default()).is_err()
  );
  let mut wide = vec![0, 0];
  wide.extend([128; 18]);
  wide.push(4); // 2^128, canonical natural but outside the Nat128 component
  assert!(
    NativeImage::load(IDENTITY, &input(&wide), DecodeLimits::default())
      .is_err()
  );
}

#[test]
#[ignore = "requires explicit original IXBF/IXFI files; native prefix and actual circuit batches"]
fn original_program_input_prefix_exercises_paged_execution() {
  let program = std::fs::read(
    std::env::var_os("IXBY_PAGED_PROGRAM").expect("IXBY_PAGED_PROGRAM"),
  )
  .unwrap();
  let input = std::fs::read(
    std::env::var_os("IXBY_PAGED_INPUT").expect("IXBY_PAGED_INPUT"),
  )
  .unwrap();
  let batches = std::env::var("IXBY_PAGED_BATCHES")
    .unwrap_or_else(|_| "100".into())
    .parse::<usize>()
    .unwrap();
  assert!((1..=10_000).contains(&batches));
  let started = std::time::Instant::now();
  let mut image =
    NativeImage::load(&program, &input, DecodeLimits::default()).unwrap();
  let initial_root = image.memory.root();
  eprintln!(
    "original native image: program={} input={} cells={} root={initial_root:?} load={:?}",
    program.len(),
    input.len(),
    image.cell_count,
    started.elapsed()
  );
  let mut machine = image.machine().unwrap();
  let mut builder = ShapeBuilder::new(BatchClass::Compact.nu());
  let emission = emit_batch(&mut builder, BatchClass::Compact).unwrap();
  let shape = builder.finish().unwrap();
  let started = std::time::Instant::now();
  let mut before = None::<Vec<F128>>;
  let mut completed = 0;
  for _ in 0..batches {
    let Some(advice) = machine
      .batch(BatchClass::Compact, &mut image.memory)
      .unwrap_or_else(|error| {
        panic!("clock={} state={:?}: {error:#}", machine.clock, machine.state)
      })
    else {
      break;
    };
    if let Some(previous) = &before {
      assert_eq!(previous[..3], advice.expected[..3]);
      assert_eq!(previous[30..57], advice.expected[3..30]);
    }
    let witness =
      shape.run(&emission.inputs.assign(&advice.private).unwrap(), &[]);
    assert_eq!(
      witness.public,
      emission.public.instantiate(&advice.expected).unwrap()
    );
    before = Some(advice.expected);
    completed += 1;
  }
  assert!(machine.clock > 0);
  eprintln!(
    "original prefix: batches={completed} microsteps={} logical_steps={} heap_fields={} byte_cells={} elapsed={:?}; source admission and complete execution remain unproved",
    machine.clock,
    machine.state[FUEL].hi,
    machine.state[HEAP_COUNT].lo,
    machine.state[BYTE_COUNT].lo,
    started.elapsed()
  );
}

#[test]
#[ignore = "requires original IXBF/IXFI; proves one conditional execution segment with a fresh receiver"]
fn original_execution_segment_proves_with_fresh_memory_root_binding() {
  proof_tests::original_proof_test(
    BatchClass::Compact,
    "ixby::paged_exec::image_tests::original_execution_segment_proves_with_fresh_memory_root_binding",
    || {
      let program = std::fs::read(
        std::env::var_os("IXBY_PAGED_PROGRAM").expect("IXBY_PAGED_PROGRAM"),
      )
      .unwrap();
      let input = std::fs::read(
        std::env::var_os("IXBY_PAGED_INPUT").expect("IXBY_PAGED_INPUT"),
      )
      .unwrap();
      let index = std::env::var("IXBY_PAGED_PROOF_BATCH")
        .unwrap_or_else(|_| "99".into())
        .parse::<usize>()
        .unwrap();
      assert!(index < 10_000);
      let mut image =
        NativeImage::load(&program, &input, DecodeLimits::default()).unwrap();
      let mut machine = image.machine().unwrap();
      for _ in 0..index {
        machine
          .batch(BatchClass::Compact, &mut image.memory)
          .unwrap()
          .expect("execution prefix");
      }
      let before = machine.clock;
      let fuel = machine.state[FUEL].hi;
      let advice = machine
        .batch(BatchClass::Compact, &mut image.memory)
        .unwrap()
        .expect("execution segment");
      eprintln!(
        "original segment: batch={index} clocks={before}..{} logical_steps={fuel}..{}; expected memory root is conditional, source admission remains unproved",
        machine.clock, machine.state[FUEL].hi
      );
      (advice, Vec::new())
    },
  );
}

#[test]
#[ignore = "requires original IXBF/IXFI; execution proof using shared tree authentication and a fresh receiver"]
fn original_execution_segment_with_shared_tree_proves_fresh() {
  proof_tests::original_proof_test(
    BatchClass::SharedCompact,
    "ixby::paged_exec::image_tests::original_execution_segment_with_shared_tree_proves_fresh",
    || {
      let program = std::fs::read(
        std::env::var_os("IXBY_PAGED_PROGRAM").expect("IXBY_PAGED_PROGRAM"),
      )
      .unwrap();
      let input = std::fs::read(
        std::env::var_os("IXBY_PAGED_INPUT").expect("IXBY_PAGED_INPUT"),
      )
      .unwrap();
      let mut image =
        NativeImage::load(&program, &input, DecodeLimits::default()).unwrap();
      let mut machine = image.machine().unwrap();
      for _ in 0..99 {
        machine
          .batch(BatchClass::SharedCompact, &mut image.memory)
          .unwrap()
          .expect("execution prefix");
      }
      let before = machine.clock;
      let fuel = machine.state[FUEL].hi;
      let advice = machine
        .batch(BatchClass::SharedCompact, &mut image.memory)
        .unwrap()
        .expect("execution segment");
      eprintln!(
        "original shared-tree segment: batch=99 clocks={before}..{} logical_steps={fuel}..{}; expected initial memory remains conditional on source admission",
        machine.clock, machine.state[FUEL].hi
      );
      (advice, Vec::new())
    },
  );
}

#[test]
#[ignore = "original artifacts; native advice-generation throughput only, no proof claim"]
fn original_native_advice_generation_prefix() {
  let program =
    std::fs::read(std::env::var_os("IXBY_PAGED_PROGRAM").unwrap()).unwrap();
  let input =
    std::fs::read(std::env::var_os("IXBY_PAGED_INPUT").unwrap()).unwrap();
  let batches = std::env::var("IXBY_PAGED_BATCHES")
    .unwrap_or_else(|_| "10000".into())
    .parse::<usize>()
    .unwrap();
  assert!((1..=100_000).contains(&batches));
  let started = std::time::Instant::now();
  let mut image =
    NativeImage::load(&program, &input, DecodeLimits::default()).unwrap();
  eprintln!(
    "native throughput image: program={} input={} cells={} load={:?}",
    program.len(),
    input.len(),
    image.cell_count,
    started.elapsed()
  );
  let mut machine = image.machine().unwrap();
  machine.compare_native_advice =
    std::env::var_os("IXBY_COMPARE_NATIVE_ADVICE").is_some();
  eprintln!(
    "differential comparison against actual Boolean plans: {}",
    machine.compare_native_advice
  );
  let started = std::time::Instant::now();
  let mut completed = 0;
  for _ in 0..batches {
    let Some(_advice) =
      machine.batch(BatchClass::SharedCompact, &mut image.memory).unwrap()
    else {
      break;
    };
    completed += 1;
    if completed % 1000 == 0 {
      eprintln!(
        "native advice prefix: batches={completed} microsteps={} logical_steps={} elapsed={:?}",
        machine.clock,
        machine.state[FUEL].hi,
        started.elapsed()
      );
    }
  }
  assert!(machine.clock > 0);
  eprintln!(
    "native advice generation ONLY: batches={completed} microsteps={} logical_steps={} heap_fields={} byte_cells={} elapsed={:?}; no complete batch-table checks or proofs in this throughput loop",
    machine.clock,
    machine.state[FUEL].hi,
    machine.state[HEAP_COUNT].lo,
    machine.state[BYTE_COUNT].lo,
    started.elapsed()
  );
}
