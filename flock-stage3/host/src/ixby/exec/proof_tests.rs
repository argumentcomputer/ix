//! Real, direct scalar IxBy execution proofs. No Aiur proof, Stage 2 native
//! decoder/verifier, or host-resolved action is part of the accepted relation.

use super::{
  tests::{CAPACITY, cases, setup},
  *,
};
use crate::ixby::decode::{
  InputDecodeGate, ProgramDecodeGate,
  test_support::{
    FunctionImage as F, Instruction as I, Operand as O, Value as V, input,
    program,
  },
};
use flock_prover::{
  circuit::builder::GateType, field::F128, prover::UnionSlotProverInput,
};
use std::{
  io::{Read, Write},
  process::{Command, Stdio},
  time::Instant,
};

const CHILD: &str = "IXBY_FLOCK_EXEC_VERIFY_CHILD";
const TEST: &str = "ixby::exec::proof_tests::direct_scalar_exec_proofs_share_setup_and_verify_without_advice";

fn isolated(expected: ExecStatementDigest, bytes: &[u8]) -> bool {
  let mut child = Command::new(std::env::current_exe().unwrap())
    .args(["--ignored", "--exact", TEST, "--test-threads=1", "--nocapture"])
    .current_dir(std::env::temp_dir())
    .env_clear()
    .env(CHILD, "1")
    .env("RAYON_NUM_THREADS", "4")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .spawn()
    .unwrap();
  let mut stdin = child.stdin.take().unwrap();
  stdin.write_all(&expected.0).unwrap();
  stdin.write_all(bytes).unwrap();
  drop(stdin);
  let result = child.wait_with_output().unwrap();
  if !result.status.success() {
    eprintln!(
      "isolated Exec verifier rejected: {}",
      String::from_utf8_lossy(&result.stderr)
    );
  }
  result.status.success()
}

#[test]
#[ignore = "direct byte-authenticated IxBy executions, all scalar opcodes, isolated verifier and malicious wiring"]
fn direct_scalar_exec_proofs_share_setup_and_verify_without_advice() {
  if std::env::var_os(CHILD).is_some() {
    let mut bytes = Vec::new();
    std::io::stdin()
      .take(proof::MAX_BYTES + 33)
      .read_to_end(&mut bytes)
      .unwrap();
    assert!((32..=proof::MAX_BYTES as usize + 32).contains(&bytes.len()));
    let expected = ExecStatementDigest(bytes[..32].try_into().unwrap());
    // No private data, reference program construction/execution, expected
    // output hashing, witness run, or prover call occurs in this branch.
    setup().verify(expected, &bytes[32..]).unwrap();
    return;
  }
  let compiled = setup();
  let identity = compiled.identities();
  eprintln!(
    "Exec approved setup {}: nu={}, m={}",
    blake3::Hash::from_bytes(identity.digest()).to_hex(),
    compiled.nu,
    compiled.params.m
  );
  let cases = cases();
  for (index, (code, args, result)) in cases.iter().enumerate() {
    let expected = expected_statement(compiled.profile(), code, args, result);
    let start = Instant::now();
    let bytes = compiled.prove(expected, code, args).unwrap();
    let proving = start.elapsed();
    let start = Instant::now();
    assert!(isolated(expected, &bytes));
    eprintln!(
      "Exec case {index}/{}: {} complete proof bytes; code/input/output {}/{}/{} bytes; prove {:.3}s; fresh verify {:.3}s",
      cases.len(),
      bytes.len(),
      code.len(),
      args.len(),
      result.len(),
      proving.as_secs_f64(),
      start.elapsed().as_secs_f64()
    );
    assert_eq!(compiled.identities(), identity);
    if index == 0 {
      negatives(&compiled, code, args, result, expected, &bytes);
    }
  }

  // Replace a single table's row with independently recomputed, locally valid
  // advice for DIFFERENT bytes. Acceptance must fail at constrained wiring,
  // not at a host decoder or stale local R1CS output.
  let (code, args, result) = &cases[0];
  let expected = expected_statement(compiled.profile(), code, args, result);
  for splice in [false, true] {
    let bytes = spliced_proof(&compiled, expected, code, args, splice);
    assert!(!isolated(expected, &bytes));
  }
}

fn negatives(
  compiled: &CompiledExec,
  code: &[u8],
  args: &[u8],
  result: &[u8],
  expected: ExecStatementDigest,
  bytes: &[u8],
) {
  let mut parameters = compiled.profile().parameters();
  parameters[13] += 1;
  let changed = SemanticProfile::new(parameters).unwrap();
  let mut other_code = code.to_vec();
  *other_code.last_mut().unwrap() ^= 1;
  let other_input = input(&[V::Bool(1)]);
  let mut other_result = result.to_vec();
  *other_result.last_mut().unwrap() ^= 1;
  for wrong in [
    expected_statement(changed, code, args, result),
    expected_statement(compiled.profile(), &other_code, args, result),
    expected_statement(compiled.profile(), code, &other_input, result),
    expected_statement(compiled.profile(), code, args, &other_result),
  ] {
    assert!(compiled.verify(wrong, bytes).is_err());
  }
  for at in [0, 7, 8, 39, 40, bytes.len() / 2, bytes.len() - 1] {
    let mut wrong = bytes.to_vec();
    wrong[at] ^= 1;
    assert!(compiled.verify(expected, &wrong).is_err());
  }
  assert!(compiled.verify(expected, &bytes[..bytes.len() - 1]).is_err());
  let mut trailing = bytes.to_vec();
  trailing.push(0);
  assert!(compiled.verify(expected, &trailing).is_err());
  for domain in [*b"IXFLK301", *b"IXFLK302", *b"IXBP\0\0\0\0"] {
    let mut wrong = bytes.to_vec();
    wrong[..8].copy_from_slice(&domain);
    assert!(compiled.verify(expected, &wrong).is_err());
  }
  let reduced = PrimitiveSet::new(
    &PrimitiveSet::scalar()
      .opcodes()
      .filter(|op| *op != 24)
      .collect::<Vec<_>>(),
  )
  .unwrap();
  let other =
    compile_exec_profile(compiled.profile(), CAPACITY, reduced).unwrap();
  assert_ne!(other.identities(), compiled.identities());
  assert!(other.verify(expected, bytes).is_err());
  let mut changed_header = bytes.to_vec();
  changed_header[8..40].copy_from_slice(&other.identities().digest());
  assert!(other.verify(expected, &changed_header).is_err());
}

fn spliced_proof(
  compiled: &CompiledExec,
  expected: ExecStatementDigest,
  code: &[u8],
  args: &[u8],
  program_splice: bool,
) -> Vec<u8> {
  let private = [
    proof::buffer(CAPACITY.program.bytes, code).unwrap(),
    proof::buffer(CAPACITY.input.bytes, args).unwrap(),
  ]
  .concat();
  let witness =
    compiled.shape.run(&compiled.input.assign(&private).unwrap(), &[]);
  let public = compiled.public.instantiate(&expected.limbs()).unwrap();
  assert_eq!(witness.public, public);
  let mut drivers = witness::drivers(compiled, &witness);
  if program_splice {
    let different = program(
      0,
      &[F {
        arity: 1,
        entry: 0,
        blocks: vec![(1, I::Ret(O::Literal(V::Bool(1))))],
      }],
    );
    let gate = &compiled.machine.program_gate;
    let mut output = Vec::new();
    let row = gate.eval(
      &proof::buffer(CAPACITY.program.bytes, &different).unwrap(),
      &(),
      &mut output,
    );
    assert_eq!(
      output.last(),
      Some(&F128::ZERO),
      "locally valid substituted program"
    );
    let slot = compiled.machine.program_slot.slot();
    let index = compiled.shape.registry_slot(slot);
    assert_eq!(witness.rows::<ProgramDecodeGate>(slot).len(), 1);
    drivers[index] = UnionSlotProverInput::in_place(
      move |dst| gate.generate_witness_into(&[row], dst),
      compiled.tables[index].csc_lincheck_circuit(),
    );
  } else {
    let different = input(&[V::Bool(1)]);
    let gate = &compiled.machine.input_gate;
    let mut output = Vec::new();
    let row = gate.eval(
      &proof::buffer(CAPACITY.input.bytes, &different).unwrap(),
      &(),
      &mut output,
    );
    assert_eq!(
      output.last(),
      Some(&F128::ZERO),
      "locally valid substituted input"
    );
    let slot = compiled.machine.input_slot.slot();
    let index = compiled.shape.registry_slot(slot);
    assert_eq!(witness.rows::<InputDecodeGate>(slot).len(), 1);
    drivers[index] = UnionSlotProverInput::in_place(
      move |dst| gate.generate_witness_into(&[row], dst),
      compiled.tables[index].csc_lincheck_circuit(),
    );
  }
  compiled.prove_rows(&public, drivers).unwrap()
}
