use super::super::{
  COMMITTED, DEPTH as STACK_DEPTH, ENTRY, FIELDS, HEAP, INPUTS,
  InputCaptureGate, NATURAL, NEXT, OUTPUTS, RANGE, REPLIES, RESOLVED, SCALAR,
  SPAN, STACK, STATE, STATE_WORDS, TAG,
};
use super::*;
use crate::{
  hash::pack_bytes,
  ixby::{
    auth_memory::{MemoryDepth, SparseMemory},
    ixbf::{self, DecodeLimits},
    ixbf_decode::{
      dispatch::{DISPATCH_CONTEXT_INDICES, test_parse_program},
      paged::input_capture::batch::{
        CompiledInputCapture, InputCaptureAdvice, InputCaptureStatement,
        InputCaptureWitness,
      },
    },
    paged_code::PackedProgram,
    paged_exec::NativeImage,
    paged_value::INPUT_BYTES,
  },
};
use flock_prover::{circuit::builder::GateType, field::F128};
pub(super) fn nat(out: &mut Vec<u8>, mut v: u128) {
  loop {
    let byte = (v & 127) as u8;
    v >>= 7;
    out.push(byte | if v == 0 { 0 } else { 128 });
    if v == 0 {
      break;
    }
  }
}
pub(super) fn id(out: &mut Vec<u8>, i: usize) {
  out.extend([0xa0 + i as u8; 32]);
  nat(out, (1 << 100) + i as u128);
  nat(out, (1 << 127) + i as u128);
}
pub(super) fn program(arity: usize) -> Vec<u8> {
  let mut out = b"IXBF\x01\0\0\0\0\0\0\0".to_vec();
  for n in [
    1024, 256, 256, 128, 64, 1024, 65536, 4096, 16777216, 16777216, 100000, 0,
    4,
  ] {
    nat(&mut out, n);
  }
  for (i, fields) in [0, 1, 2, 64].into_iter().enumerate() {
    id(&mut out, i);
    nat(&mut out, fields);
  }
  nat(&mut out, 2);
  for n in [arity as u128, 0, 1, arity as u128] {
    nat(&mut out, n);
  }
  out.extend([1, 2]);
  out.extend([64, 0, 1, 64, 1, 0, 63]);
  out
}
#[derive(Clone)]
pub(super) enum Value {
  Scalar(Vec<u8>),
  Constructor(usize, Vec<Value>),
  Pap(Vec<Value>),
  Erased,
}
impl Value {
  fn encode(&self, out: &mut Vec<u8>) {
    match self {
      Self::Scalar(s) => {
        out.push(0);
        out.extend(s);
      },
      Self::Erased => out.push(3),
      Self::Constructor(i, children) => {
        out.push(1);
        id(out, *i);
        nat(out, children.len() as u128);
        for child in children {
          child.encode(out);
        }
      },
      Self::Pap(children) => {
        out.extend([2, 1]);
        nat(out, children.len() as u128);
        for child in children {
          child.encode(out);
        }
      },
    }
  }
}
pub(super) fn input(values: &[Value]) -> Vec<u8> {
  let mut out = b"IXFI\x01\0\0\0\0\0\0\0".to_vec();
  nat(&mut out, values.len() as u128);
  for v in values {
    v.encode(&mut out);
  }
  out
}
pub(super) fn sample() -> (Vec<u8>, Vec<u8>) {
  let mut n = vec![0];
  nat(&mut n, u128::MAX);
  let mut bytes = vec![6];
  nat(&mut bytes, 2051);
  bytes.extend((0..2051).map(|i| (i * 197) as u8));
  let mut string = vec![1];
  let text = "𐀀".repeat(27);
  nat(&mut string, text.len() as u128);
  string.extend(text.as_bytes());
  let values = vec![
    Value::Constructor(
      2,
      vec![
        Value::Constructor(
          2,
          vec![
            Value::Scalar(n),
            Value::Pap(vec![Value::Scalar(bytes), Value::Scalar(string)]),
          ],
        ),
        Value::Constructor(0, vec![]),
      ],
    ),
    Value::Scalar(vec![2, 1]),
  ];
  (program(values.len()), input(&values))
}
pub(super) fn context(program: &[u8]) -> [F128; 15] {
  let p = test_parse_program(program, 100000).unwrap();
  DISPATCH_CONTEXT_INDICES.map(|i| p[i])
}
pub(super) fn initial(program: &[u8], input: &[u8]) -> SparseMemory {
  let a = ixbf::decode_program(program, DecodeLimits::default()).unwrap();
  let mut cells = PackedProgram::from_artifact(&a).unwrap().cells;
  for (i, bytes) in input.chunks(32).enumerate() {
    let mut cell = [0; 32];
    cell[..bytes.len()].copy_from_slice(bytes);
    cells.push((
      INPUT_BYTES + i as u64,
      [pack_bytes(&cell[..16]), pack_bytes(&cell[16..])],
    ));
  }
  SparseMemory::from_cells(MemoryDepth::new(40).unwrap(), cells).unwrap()
}
pub(super) fn batches(
  program: &[u8],
  input: &[u8],
  setup: &CompiledInputCapture,
) -> Vec<InputCaptureAdvice> {
  let context = context(program);
  let mut memory = initial(program, input);
  let root = memory.root();
  let mut walk = InputCaptureWitness::new(input, context).unwrap();
  let mut batches: Vec<InputCaptureAdvice> = Vec::new();
  while let Some(a) = walk.next_batch(&mut memory).unwrap() {
    setup.check_advice(&a).unwrap();
    if let Some(prev) = batches.last() {
      assert_eq!(prev.statement.final_state(), a.statement.initial());
    }
    batches.push(a);
    assert!(batches.len() < 100000);
  }
  assert!(walk.done());
  let mut whole = *batches[0].statement.words();
  whole[40..].copy_from_slice(batches.last().unwrap().statement.final_state());
  InputCaptureStatement::from_words(&whole)
    .unwrap()
    .check_complete(&context, root)
    .unwrap();
  let native =
    NativeImage::load(program, input, DecodeLimits::default()).unwrap();
  assert_eq!(memory.root(), native.memory.root());
  assert_eq!(
    walk.state()[1],
    native.state[crate::ixby::paged_exec::HEAP_COUNT]
  );
  for i in 0..64 {
    assert_eq!(memory.value(STACK + i).unwrap(), [F128::ZERO; 2]);
  }
  let initialize =
    crate::ixby::ixbf_decode::paged::initialize::InitializeGate::new(3)
      .unwrap();
  let mut initial = Vec::new();
  initialize.eval(
    &context.into_iter().chain(*walk.state()).collect::<Vec<_>>(),
    &(),
    &mut initial,
  );
  assert_eq!(initial[27], F128::ZERO);
  assert_eq!(initial[..3], native.parameters);
  assert_eq!(initial[3..27], native.state);

  batches
}
pub(super) fn eval(g: &InputCaptureGate, input: &[F128]) -> Vec<F128> {
  let mut out = Vec::new();
  g.eval(input, &(), &mut out);
  out
}
#[test]
fn complete_input_materialization_matches_native_preorder_values_and_clears_frontier()
 {
  let setup = CompiledInputCapture::compile().unwrap();
  let (p, i) = sample();
  let a = batches(&p, &i, &setup);
  let union = flock_prover::union::UnionInstance::new(
    &setup.shape.registry,
    setup.shape.counts.clone(),
  );
  eprintln!(
    "input capture sample batches={} M={} dense={}",
    a.len(),
    union.dense_m(),
    union.dense_words()
  );
  let tail = 40 + 2 + 3 * (64 + 2 * DEPTH) + 9 * STEPS;
  for at in [
    0,
    1,
    3,
    5,
    6,
    27,
    28,
    33,
    34,
    35,
    36,
    37,
    38,
    40,
    41,
    42,
    318,
    319,
    tail,
    tail + 2,
    tail + 2 + 3,
    tail + 2 + 5 * CELLS + 2,
  ] {
    let mut bad = a[0].clone();
    bad.private[at] += F128::ONE;
    assert!(setup.check_advice(&bad).is_err(), "private word {at}");
  }

  let mut wide = vec![0];
  nat(&mut wide, (1 << 65) + 7);
  let mut word = vec![3];
  word.extend(u32::MAX.to_le_bytes());
  let mut gold = vec![4];
  gold.extend(0xffffffff00000000u64.to_le_bytes());
  let mut ext = vec![5];
  ext.extend(17u64.to_le_bytes());
  ext.extend(19u64.to_le_bytes());
  let scalars = vec![
    Value::Scalar(wide),
    Value::Scalar(word),
    Value::Scalar(gold),
    Value::Scalar(ext),
    Value::Scalar(vec![6, 0]),
    Value::Scalar(vec![1, 0]),
    Value::Erased,
    Value::Pap(vec![]),
    Value::Constructor(0, vec![]),
  ];
  batches(&program(scalars.len()), &input(&scalars), &setup);
  batches(&program(0), &input(&[]), &setup);
  let mut nested = Value::Erased;
  for _ in 0..17 {
    nested = Value::Constructor(2, vec![nested, Value::Erased]);
  }
  batches(&program(2), &input(&[nested, Value::Erased]), &setup);
  batches(
    &program(1),
    &input(&[Value::Constructor(3, vec![Value::Erased; 64])]),
    &setup,
  );
}
#[test]
fn input_capture_padding_references_frontier_and_all_output_words_are_bound() {
  use crate::ixby::bits::{fill_words, read_words};
  let setup = CompiledInputCapture::compile().unwrap();
  let (p, i) = sample();
  let batches = batches(&p, &i, &setup);
  let (slot, g) = setup.emission.capture.capture_gate();
  let mut rows = Vec::new();
  for a in &batches {
    rows.extend_from_slice(
      setup.witness(a).unwrap().rows::<InputCaptureGate>(slot),
    );
  }
  for r in &rows {
    let mut pad = r.0.clone();
    pad[TAG] = F128::new(17, 0);
    pad[COMMITTED] = F128::ZERO;
    pad[FIELDS..STATE].fill(F128::ZERO);
    pad[RESOLVED..].fill(F128::ZERO);
    let out = eval(g, &pad);
    assert_eq!(&out[..STATE_WORDS], &r.0[STATE..STATE + STATE_WORDS]);
    assert_eq!(out[STATE_WORDS..], [F128::ZERO; OUTPUTS - STATE_WORDS]);
    for at in [TAG, COMMITTED, SCALAR, SPAN, HEAP, STACK_DEPTH, ENTRY, RESOLVED]
    {
      let mut bad = r.0.clone();
      bad[at].hi |= 1 << 63;
      assert_eq!(eval(g, &bad).last(), Some(&F128::ONE), "alias at={at}");
    }
  }
  let ctor = rows
    .iter()
    .find(|r| r.0[TAG] == F128::new(9, 0) && r.0[FIELDS] == F128::ONE)
    .unwrap();
  for at in [
    FIELDS + 1,
    FIELDS + 2,
    FIELDS + 3,
    FIELDS + 4,
    FIELDS + 5,
    REPLIES,
    REPLIES + 1,
    REPLIES + 2,
    REPLIES + 3,
    REPLIES + 4,
  ] {
    let mut bad = ctor.0.clone();
    bad[at] += F128::ONE;
    assert_eq!(eval(g, &bad).last(), Some(&F128::ONE), "constructor at={at}");
  }
  let pop = rows.iter().find(|r| r.0[REPLIES + 6] != F128::ZERO).unwrap();
  let mut bad = pop.0.clone();
  bad[REPLIES + 6] = F128::ZERO;
  assert_eq!(eval(g, &bad).last(), Some(&F128::ONE));
  let gate = InputCaptureGate::new(3).unwrap();
  let table = gate.r1cs();
  for r in [ctor, pop] {
    let mut bits = vec![false; table.n()];
    gate.plan().fill_row(&mut bits[..gate.plan().k()], |b| fill_words(&r.0, b));
    assert!(table.satisfies(&bits));
    assert_eq!(read_words(&bits, INPUTS, OUTPUTS), eval(&gate, &r.0));
    for at in INPUTS..INPUTS + OUTPUTS {
      for bit in [0, 63, 64, 127] {
        bits[at * 128 + bit] ^= true;
        assert!(!table.satisfies(&bits));
        bits[at * 128 + bit] ^= true;
      }
    }
  }
  rows.truncate(7);
  crate::ixby::test_support::padding(
    gate.plan(),
    &rows,
    |r, b| fill_words(&r.0, b),
    |dst| gate.generate_witness_into(&rows, dst),
  );
}

#[test]
#[ignore = "joint Input grammar/value/memory proofs with fresh receivers and recomputed substitutions"]
fn input_capture_proves_fresh_and_rejects_recomputed_values() {
  use flock_prover::prover::UnionSlotProverInput;
  use std::{io::Read, time::Instant};
  const CHILD: &str = "IXBY_INPUT_CAPTURE_VERIFY_CHILD";
  let start = Instant::now();
  let setup = CompiledInputCapture::compile().unwrap();
  let setup_time = start.elapsed();
  if std::env::var_os(CHILD).is_some() {
    let mut bytes = Vec::new();
    std::io::stdin()
      .take(8 * 1024 * 1024 + 16 * PUBLIC_WORDS as u64 + 1)
      .read_to_end(&mut bytes)
      .unwrap();
    assert!(bytes.len() >= 16 * PUBLIC_WORDS);
    let expected = bytes[..16 * PUBLIC_WORDS]
      .as_chunks::<16>()
      .0
      .iter()
      .map(|v| pack_bytes(v))
      .collect::<Vec<_>>();
    setup
      .verify(
        &InputCaptureStatement::from_words(&expected).unwrap(),
        &bytes[16 * PUBLIC_WORDS..],
      )
      .unwrap();
    return;
  }
  let (program, input) = sample();
  let batches = batches(&program, &input, &setup);
  let (slot, g) = setup.emission.capture.capture_gate();
  let mut attacked = [false; 7];
  for (index, advice) in batches.iter().enumerate() {
    let witness = setup.witness(advice).unwrap();
    let start = Instant::now();
    let proof = setup.prove(advice).unwrap();
    let elapsed = start.elapsed();
    setup.verify(&advice.statement, &proof).unwrap();
    fresh_verify(advice, &proof);
    eprintln!(
      "joint input capture {index}: proof={} setup={setup_time:?} witness+prove={elapsed:?}",
      proof.len()
    );
    for at in 0..PUBLIC_WORDS {
      let mut words = *advice.statement.words();
      words[at] += F128::ONE;
      if let Ok(bad) = InputCaptureStatement::from_words(&words) {
        assert!(
          setup.verify(&bad, &proof).is_err(),
          "accepted expected word {at}"
        );
      }
    }
    assert!(
      setup.verify(&advice.statement, &proof[..proof.len() - 1]).is_err()
    );
    let mut extra = proof.clone();
    extra.push(0);
    assert!(setup.verify(&advice.statement, &extra).is_err());
    for (attack, done) in attacked.iter_mut().enumerate() {
      if *done {
        continue;
      }
      let mut rows = witness.rows::<InputCaptureGate>(slot).to_vec();
      let Some(row) = rows.iter_mut().find(|r| {
        if r.0[COMMITTED] != F128::ONE {
          return false;
        }
        let phase = r.0[1].lo as u8;
        match attack {
          0 => phase == 0,
          1 | 2 | 6 => {
            phase == 19 && r.0[FIELDS] == F128::ONE && r.0[RESOLVED].lo < 3
          },
          3 => r.0[REPLIES + 6].lo >> 36 == 4,
          4 => phase == 14,
          5 => phase == 18,
          _ => false,
        }
      }) else {
        continue;
      };
      match attack {
        0 => {
          row.0[7] += F128::ONE;
          row.0[FIELDS] += F128::ONE;
          row.0[REPLIES].lo += 1;
        },
        1 => {
          row.0[FIELDS + 1] += F128::ONE;
          row.0[REPLIES] += F128::ONE;
        },
        2 => row.0[HEAP] += F128::ONE,
        3 => row.0[REPLIES + 6].lo += 1,
        4 => row.0[NATURAL] += F128::new(0, 1 << 63),
        5 => {
          row.0[RANGE].lo += 1;
          row.0[0].lo += 1;
          row.0[NEXT].lo += 1;
        },
        _ => row.0[RESOLVED] += F128::ONE,
      }
      *done = true;
      let mut output = Vec::new();
      g.eval(&row.0, &(), &mut output);
      assert_eq!(output.last(), Some(&F128::ZERO));
      let table = g.r1cs();
      let boolean = setup
        .drivers
        .iter()
        .map(|d| {
          if d.slot() == slot {
            let rows = rows.clone();
            UnionSlotProverInput::in_place(
              move |dst| g.generate_witness_into(&rows, dst),
              table.csc_lincheck_circuit(),
            )
          } else {
            d.prover(&witness)
          }
        })
        .collect();
      let bad = setup.prove_rows(&witness, boolean).unwrap();
      let error = setup.verify(&advice.statement, &bad).unwrap_err();
      eprintln!("recomputed input attack {attack} rejected: {error}");
      assert!(format!("{error}").contains("Wiring"));
    }
  }
  assert!(attacked.into_iter().all(|v| v));
}

#[test]
#[ignore = "complete original input materialization and exact initialization; set IXBY_PAGED_PROGRAM and IXBY_PAGED_INPUT"]
fn original_input_materializes_the_exact_initial_execution_image() {
  let program = std::fs::read(
    std::env::var_os("IXBY_PAGED_PROGRAM").expect("IXBY_PAGED_PROGRAM"),
  )
  .unwrap();
  let input = std::fs::read(
    std::env::var_os("IXBY_PAGED_INPUT").expect("IXBY_PAGED_INPUT"),
  )
  .unwrap();
  let setup = CompiledInputCapture::compile().unwrap();
  let start = std::time::Instant::now();
  let advice = batches(&program, &input, &setup);
  for a in &advice {
    let proof = setup.prove(a).unwrap();
    setup.verify(&a.statement, &proof).unwrap();
    fresh_verify(a, &proof);
    eprintln!(
      "original input proof={} bytes, fresh verifier passed",
      proof.len()
    );
  }
  eprintln!(
    "original input bytes={} batches={} events={} exact native root/initial state/parameters matched elapsed={:?}",
    input.len(),
    advice.len(),
    advice.iter().map(|a| a.steps).sum::<usize>(),
    start.elapsed()
  );
}

fn fresh_verify(advice: &InputCaptureAdvice, proof: &[u8]) {
  use std::{
    io::Write,
    process::{Command, Stdio},
  };
  let mut child = Command::new(std::env::current_exe().unwrap())
      .args(["--ignored", "--exact", "ixby::ixbf_decode::paged::input_capture::batch::tests::input_capture_proves_fresh_and_rejects_recomputed_values", "--test-threads=1", "--nocapture"])
      .current_dir(std::env::temp_dir())
      .env_clear()
      .env("IXBY_INPUT_CAPTURE_VERIFY_CHILD", "1")
      .env("RAYON_NUM_THREADS", "4")
      .stdin(Stdio::piped())
      .stdout(Stdio::piped())
      .stderr(Stdio::piped())
      .spawn()
      .unwrap();
  let mut stdin = child.stdin.take().unwrap();
  for word in advice.statement.words() {
    stdin.write_all(&word.lo.to_le_bytes()).unwrap();
    stdin.write_all(&word.hi.to_le_bytes()).unwrap();
  }
  stdin.write_all(proof).unwrap();
  drop(stdin);
  let output = child.wait_with_output().unwrap();
  assert!(
    output.status.success(),
    "{} {}",
    String::from_utf8_lossy(&output.stdout),
    String::from_utf8_lossy(&output.stderr)
  );
}
