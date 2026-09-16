use super::*;
use crate::{
  hash::pack_bytes,
  ixby::{
    bits::{fill_words, read_words},
    ixbf::{self, DecodeLimits, Primitive},
    ixbf_decode::{
      GrammarKind, NaturalCapacity,
      dispatch::{DispatchConfig, DispatchEvaluator, EvaluatedStep},
    },
    paged_code::{CodeGate, CodeGateKind, PackedProgram},
    paged_value::PROGRAM_BYTES,
  },
};
use flock_prover::{circuit::builder::GateType, field::F128};
use std::collections::BTreeMap;

fn eval<G: GateType<Hint = ()>>(gate: &G, input: &[F128]) -> Vec<F128> {
  let mut output = Vec::new();
  gate.eval(input, &(), &mut output);
  output
}
fn nat(bytes: &mut Vec<u8>, mut n: u128) {
  loop {
    let digit = (n & 127) as u8;
    n >>= 7;
    bytes.push(digit | if n == 0 { 0 } else { 128 });
    if n == 0 {
      break;
    }
  }
}
pub(super) fn sample() -> Vec<u8> {
  let mut functions: Vec<Vec<(u128, Vec<u8>)>> = vec![vec![(1, vec![1, 0, 0])]];
  for op in [
    vec![0, 0, 0],
    vec![1, Primitive::NatAdd.opcode(), 2, 0, 0, 2],
    vec![2, 1, 1, 0, 0],
    vec![3, 0, 0, 0],
    vec![4, 0, 0],
    vec![5, 0, 1, 0, 0],
    vec![6, 1, 0, 0],
    vec![7, 0, 0, 1, 2],
  ] {
    let mut instruction = vec![0];
    instruction.extend(op);
    instruction.push(1);
    functions.push(vec![(1, instruction), (2, vec![1, 0, 1])]);
  }
  for instruction in
    [vec![2, 0, 1, 0, 0], vec![3, 1, 0, 0], vec![4, 0, 0, 1, 2]]
  {
    functions.push(vec![(1, instruction)]);
  }
  functions.push(vec![
    (1, vec![5, 0, 0, 2, 0, 1, 1, 2]),
    (1, vec![1, 2]),
    (2, vec![1, 0, 1]),
  ]);
  functions.push(vec![
    (1, vec![6, 0, 0, 1, 2]),
    (1, vec![1, 2]),
    (2, vec![1, 0, 1]),
  ]);
  functions.push(vec![
    (1, vec![7, 0, 0, 1, 2]),
    (1, vec![1, 2]),
    (1, vec![1, 0, 0]),
  ]);
  functions.push(vec![(1, vec![5, 0, 0, 0])]);
  let mut wide = vec![0];
  nat(&mut wide, u128::MAX);
  let mut word = vec![3];
  word.extend(u32::MAX.to_le_bytes());
  let mut gold = vec![4];
  gold.extend(0xffffffff00000000u64.to_le_bytes());
  let mut ext = vec![5];
  ext.extend(0xfffffffeffffffffu64.to_le_bytes());
  ext.extend(7u64.to_le_bytes());
  let mut string = vec![1];
  let chars = "𐀀".repeat(27);
  nat(&mut string, chars.len() as u128);
  string.extend(chars.as_bytes());
  let mut bytes = vec![6];
  nat(&mut bytes, 2051);
  bytes.extend((0..2051).map(|i| (i * 197) as u8));
  for scalar in
    [wide, string, vec![1, 0], vec![2, 1], word, gold, ext, bytes, vec![6, 0]]
  {
    let mut ret = vec![1, 1];
    ret.extend(scalar);
    functions.push(vec![(1, ret)]);
  }
  let mut source = b"IXBF\x01\0\0\0\0\0\0\0".to_vec();
  for n in [
    1024, 256, 256, 128, 64, 1024, 65536, 4096, 16777216, 16777216, 100000, 0,
    2,
  ] {
    nat(&mut source, n);
  }
  for index in 0..2 {
    source.extend([0x91; 32]);
    nat(&mut source, u128::MAX);
    nat(&mut source, (1u128 << 100) + index);
    nat(&mut source, index);
  }
  nat(&mut source, functions.len() as u128);
  for blocks in functions {
    nat(&mut source, 1);
    nat(&mut source, 0);
    nat(&mut source, blocks.len() as u128);
    for (locals, instruction) in blocks {
      nat(&mut source, locals);
      source.extend(instruction);
    }
  }
  source
}
fn input(
  old: &[F128; 30],
  event: &EvaluatedStep,
  state: &[F128; 7],
) -> Vec<F128> {
  let mut input = GRAMMAR_INDICES.map(|i| old[i]).to_vec();
  input.extend([
    event.next,
    event.state[1],
    F128::new(event.tag as u64, 0),
    F128::new(u64::from(event.committed), 0),
  ]);
  input.extend(event.fields);
  assert_eq!(event.natural_magnitude.len(), 1);
  input.extend([event.natural_magnitude[0], event.payload_range]);
  input.extend(state);
  input
}
struct Trace {
  inputs: Vec<Vec<F128>>,
  final_parser: [F128; 30],
  cells: BTreeMap<u64, [F128; 2]>,
}
fn capture(source: &[u8]) -> Trace {
  let config = DispatchConfig {
    kind: GrammarKind::Program,
    natural: NaturalCapacity::new(128).unwrap(),
  };
  let decoder = DispatchEvaluator::new(config).unwrap();
  let gate = CodeCaptureGate::new(3).unwrap();
  let header = CodeGate::new(3, CodeGateKind::Block).unwrap();
  let mut parser =
    decoder.initialize(source.len() as u64, [F128::ZERO; 15]).unwrap();
  let mut state = [F128::ZERO; 7];
  let mut inputs = Vec::new();
  let mut cells = BTreeMap::new();
  while parser[1].lo as u8 != 20 {
    let req = decoder.request(&parser).unwrap();
    let at = req[4].lo as usize;
    let take = (req[5].lo as usize).min(source.len() - at);
    let mut bytes = vec![0; config.window_bytes()];
    bytes[..take].copy_from_slice(&source[at..at + take]);
    let words = bytes
      .as_chunks::<16>()
      .0
      .iter()
      .map(|b| pack_bytes(b))
      .collect::<Vec<_>>();
    let event = decoder.step(&parser, &words).unwrap();
    let row = input(&parser, &event, &state);
    let out = eval(&gate, &row);
    assert_eq!(
      out.last(),
      Some(&F128::ZERO),
      "capture at offset {} phase {} tag {}",
      parser[0].lo,
      parser[1].lo as u8,
      event.tag
    );
    assert_eq!(
      eval(&header, &[out[19], out[20], out[21], F128::ZERO]).last(),
      Some(&F128::ZERO),
      "completed header at {}",
      parser[0].lo
    );
    for record in out[7..19].as_chunks::<4>().0 {
      if record[1] == F128::ONE {
        assert!(
          cells.insert(record[0].lo, [record[2], record[3]]).is_none(),
          "duplicate capture address"
        );
      } else {
        assert_eq!(record, &[F128::ZERO; 4]);
      }
    }
    inputs.push(row);
    state = out[..7].try_into().unwrap();
    parser = event.state;
    assert!(inputs.len() < 1_000_000);
  }
  assert_eq!(state, [F128::ZERO; 7]);
  assert_eq!(parser[0], F128::new(source.len() as u64, source.len() as u64));
  Trace { inputs, final_parser: parser, cells }
}
#[test]
fn actual_parser_events_capture_every_instruction_scalar_and_full_identifier() {
  let bytes = sample();
  let artifact = ixbf::decode_program(&bytes, DecodeLimits::default()).unwrap();
  let expected = PackedProgram::from_artifact(&artifact)
    .unwrap()
    .cells
    .into_iter()
    .filter(|(a, _)| *a < PROGRAM_BYTES)
    .collect::<BTreeMap<_, _>>();
  let trace = capture(&bytes);
  assert_eq!(trace.cells, expected);
  assert_eq!(trace.final_parser[3].lo, artifact.functions().len() as u64);
  let g = CodeCaptureGate::new(3).unwrap();
  for row in &trace.inputs {
    // Stream batch padding may interrupt every phase, including UTF-8 and
    // a literal with pending Nat/byte payload. It cannot materialize writes.
    let mut pad = row.clone();
    pad[TAG] = F128::new(17, 0);
    pad[COMMITTED] = F128::ZERO;
    pad[NEXT_CONTROL] = pad[1];
    pad[FIELDS..STATE].fill(F128::ZERO);
    let out = eval(&g, &pad);
    assert_eq!(&out[..7], &row[STATE..]);
    assert_eq!(out[7..], [F128::ZERO; OUTPUTS - 7]);
  }
}
#[test]
fn capture_rejects_aliases_duplicate_cases_and_invalid_pending_state() {
  let trace = capture(&sample());
  let g = CodeCaptureGate::new(3).unwrap();
  for phase in [1, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] {
    let row = trace.inputs.iter().find(|r| r[1].lo as u8 == phase).unwrap();
    for at in [TAG, COMMITTED, CURRENT, OPEN, OPERANDS, SCALAR] {
      let mut bad = row.clone();
      bad[at].hi ^= 1 << 63;
      assert_eq!(
        eval(&g, &bad).last(),
        Some(&F128::ONE),
        "alias phase={phase} at={at}"
      );
    }
    let mut bad = row.clone();
    bad[TAG] = F128::new((row[TAG].lo + 1) % 17, 0);
    assert_eq!(eval(&g, &bad).last(), Some(&F128::ONE));
    let mut bad = row.clone();
    bad[COMMITTED] = F128::new(2, 0);
    assert_eq!(eval(&g, &bad).last(), Some(&F128::ONE));
  }
  let mut duplicate = trace
    .inputs
    .iter()
    .find(|r| r[1].lo as u8 == 12 && r[SEEN] != F128::ZERO)
    .unwrap()
    .clone();
  duplicate[FIELDS] = F128::ZERO;
  assert_eq!(eval(&g, &duplicate).last(), Some(&F128::ONE));
  for phase in [3, 4, 6, 7, 8, 9, 10, 11, 12] {
    let mut bad =
      trace.inputs.iter().find(|r| r[1].lo as u8 == phase).unwrap().clone();
    let at = FIELDS + usize::from(phase == 6);
    bad[at].hi |= 1 << 63;
    assert_eq!(eval(&g, &bad).last(), Some(&F128::ONE));
  }
  let mut bad =
    trace.inputs.iter().find(|r| r[1].lo as u8 == 18).unwrap().clone();
  bad[RANGE].lo += 1;
  assert_eq!(eval(&g, &bad).last(), Some(&F128::ONE));
}
#[test]
fn capture_r1cs_outputs_and_recycled_padding_are_constrained() {
  let trace = capture(&sample());
  let gate = CodeCaptureGate::new(3).unwrap();
  let r1cs = gate.r1cs();
  for phase in [1, 12, 14, 16, 18] {
    let input = trace.inputs.iter().find(|r| r[1].lo as u8 == phase).unwrap();
    let output = eval(&gate, input);
    let mut row = vec![false; r1cs.n()];
    gate
      .plan()
      .fill_row(&mut row[..gate.plan().k()], |bits| fill_words(input, bits));
    assert!(r1cs.satisfies(&row));
    assert_eq!(read_words(&row, INPUTS, OUTPUTS), output);
    for at in INPUTS..INPUTS + OUTPUTS {
      for bit in [0, 63, 64, 127] {
        row[at * 128 + bit] ^= true;
        assert!(!r1cs.satisfies(&row));
        row[at * 128 + bit] ^= true;
      }
    }
  }
  let rows = trace
    .inputs
    .iter()
    .take(7)
    .cloned()
    .map(CodeCaptureRow)
    .collect::<Vec<_>>();
  crate::ixby::test_support::padding(
    gate.plan(),
    &rows,
    |r, bits| fill_words(&r.0, bits),
    |dst| gate.generate_witness_into(&rows, dst),
  );
}
#[test]
#[ignore = "full original program parser-to-code differential; set IXBY_PAGED_PROGRAM"]
fn original_program_capture_matches_all_packed_code_cells() {
  let path =
    std::env::var_os("IXBY_PAGED_PROGRAM").expect("IXBY_PAGED_PROGRAM");
  let bytes = std::fs::read(path).unwrap();
  let artifact = ixbf::decode_program(&bytes, DecodeLimits::default()).unwrap();
  let expected = PackedProgram::from_artifact(&artifact)
    .unwrap()
    .cells
    .into_iter()
    .filter(|(a, _)| *a < PROGRAM_BYTES)
    .collect::<BTreeMap<_, _>>();
  let started = std::time::Instant::now();
  let trace = capture(&bytes);
  assert_eq!(trace.cells, expected);
  eprintln!(
    "complete original capture: bytes={} events={} cells={} elapsed={:?}",
    bytes.len(),
    trace.inputs.len(),
    trace.cells.len(),
    started.elapsed()
  );
}
