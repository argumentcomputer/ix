use super::object_fixtures::{CAPACITY, cases, setup};
use super::*;

#[test]
fn constructor_inputs_operations_cases_and_outputs_execute_in_one_setup() {
  let compiled = setup();
  eprintln!(
    "Object Exec census nu={}, m={}, tables={}, largest_log_k={}, setup={}",
    compiled.nu,
    compiled.params.m,
    compiled.tables.len(),
    compiled.tables.iter().map(|t| t.k_log).max().unwrap(),
    blake3::Hash::from_bytes(compiled.identities().digest()).to_hex()
  );
  assert_eq!(
    compiled.object_capacity().unwrap(),
    ObjectCapacity::new(2, 3, 7).unwrap()
  );
  for (index, (code, args, result)) in cases().into_iter().enumerate() {
    let expected =
      expected_statement(compiled.profile(), &code, &args, &result);
    let private = [
      proof::buffer(CAPACITY.program.bytes, &code).unwrap(),
      proof::buffer(CAPACITY.input.bytes, &args).unwrap(),
    ]
    .concat();
    let witness =
      compiled.shape.run(&compiled.input.assign(&private).unwrap(), &[]);
    assert_eq!(
      witness.public,
      compiled.public.instantiate(&expected.limbs()).unwrap(),
      "object case {index}"
    );
    assert_eq!(
      witness::drivers(&compiled, &witness).len(),
      compiled.tables.len()
    );
    eprintln!(
      "Object execution {index}: program/input/output {}/{}/{}",
      code.len(),
      args.len(),
      result.len()
    );
    if let Some(golden) = match index {
      14 => Some([
        13973111836034229465,
        15659412292072259085,
        17218498890851642343,
        10094572489215979567,
      ]),
      20 => Some([
        6894069929495142598,
        13159459254287799980,
        12762327979321263514,
        8108651417668358157,
      ]),
      _ => None,
    } {
      let words: Vec<_> = expected
        .0
        .as_chunks::<8>()
        .0
        .iter()
        .map(|word| u64::from_le_bytes(*word))
        .collect();
      assert_eq!(words, golden, "shared pure Lean statement golden {index}");
    }
  }
}

const CHILD: &str = "IXBY_FLOCK_OBJECT_EXEC_VERIFY_CHILD";
const TEST: &str = "ixby::exec::object_tests::constructor_exec_proofs_verify_in_isolation_and_reject_recomputed_object_rows";

fn isolated(expected: ExecStatementDigest, proof: &[u8]) -> bool {
  use std::{
    io::Write,
    process::{Command, Stdio},
  };
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
  stdin.write_all(proof).unwrap();
  drop(stdin);
  let result = child.wait_with_output().unwrap();
  if !result.status.success() {
    eprintln!(
      "isolated object Exec verifier rejected: {}",
      String::from_utf8_lossy(&result.stderr)
    );
  }
  result.status.success()
}

#[test]
#[ignore = "bounded immutable constructor execution, isolated verifiers and recomputed malicious object rows"]
fn constructor_exec_proofs_verify_in_isolation_and_reject_recomputed_object_rows()
 {
  use std::{io::Read, time::Instant};
  if std::env::var_os(CHILD).is_some() {
    let mut bytes = Vec::new();
    std::io::stdin()
      .take(proof::MAX_BYTES + 33)
      .read_to_end(&mut bytes)
      .unwrap();
    assert!((32..=proof::MAX_BYTES as usize + 32).contains(&bytes.len()));
    // Only verifier-owned setup and S+proof, never private image/input/output,
    // a reference/native evaluator, decoded objects or a heap/hash oracle.
    setup()
      .verify(
        ExecStatementDigest(bytes[..32].try_into().unwrap()),
        &bytes[32..],
      )
      .unwrap();
    return;
  }
  let compiled = setup();
  let identity = compiled.identities();
  let cases = cases();
  for (index, (code, args, result)) in cases.iter().enumerate() {
    let expected = expected_statement(compiled.profile(), code, args, result);
    let start = Instant::now();
    let bytes = compiled.prove(expected, code, args).unwrap();
    let proving = start.elapsed();
    let start = Instant::now();
    assert!(isolated(expected, &bytes), "constructor case {index}");
    eprintln!(
      "Object Exec {index}/{}: {} proof bytes, prove {:.3}s, fresh verify {:.3}s",
      cases.len(),
      bytes.len(),
      proving.as_secs_f64(),
      start.elapsed().as_secs_f64()
    );
    assert_eq!(identity, compiled.identities());
    if index == 0 {
      for at in [0, 8, 39, bytes.len() / 2, bytes.len() - 1] {
        let mut bad = bytes.clone();
        bad[at] ^= 1;
        assert!(compiled.verify(expected, &bad).is_err());
      }
      let mut wrong = result.clone();
      *wrong.last_mut().unwrap() ^= 1;
      assert!(
        compiled
          .verify(
            expected_statement(compiled.profile(), code, args, &wrong),
            &bytes
          )
          .is_err()
      );
      let smaller = ObjectCapacity::new(2, 3, 6).unwrap();
      let byte_capacity = compiled.byte_capacity().unwrap();
      let other = compile_exec_object_profile(
        SemanticProfile::objects(CAPACITY, byte_capacity, smaller).unwrap(),
        CAPACITY,
        byte_capacity,
        smaller,
        PrimitiveSet::crypto(),
        Blake3Backend::PackedWordsV0,
      )
      .unwrap();
      assert_ne!(other.identities(), identity);
      assert!(other.verify(expected, &bytes).is_err());
      let mut renamed = bytes.clone();
      renamed[8..40].copy_from_slice(&other.identities().digest());
      assert!(other.verify(expected, &renamed).is_err());
      let byte_only = compile_exec_byte_profile(
        SemanticProfile::bytes(CAPACITY, byte_capacity).unwrap(),
        CAPACITY,
        byte_capacity,
        PrimitiveSet::crypto(),
        Blake3Backend::PackedWordsV0,
      )
      .unwrap();
      assert!(byte_only.verify(expected, &bytes).is_err());
      renamed[8..40].copy_from_slice(&byte_only.identities().digest());
      assert!(byte_only.verify(expected, &renamed).is_err());
    }
  }
  for (index, forge_identity) in [(1, false), (6, true)] {
    let (code, args, result) = &cases[index];
    let expected = expected_statement(compiled.profile(), code, args, result);
    let bytes =
      spliced_object_proof(&compiled, expected, code, args, forge_identity);
    assert!(
      !isolated(expected, &bytes),
      "fully recomputed object splice must reject"
    );
  }
}

fn spliced_object_proof(
  compiled: &CompiledExec,
  expected: ExecStatementDigest,
  code: &[u8],
  args: &[u8],
  forge_identity: bool,
) -> Vec<u8> {
  use crate::ixby::object_value::ObjectDispatchGate;
  use flock_prover::{
    circuit::builder::GateType, field::F128, prover::UnionSlotProverInput,
  };
  let private = [
    proof::buffer(CAPACITY.program.bytes, code).unwrap(),
    proof::buffer(CAPACITY.input.bytes, args).unwrap(),
  ]
  .concat();
  let witness =
    compiled.shape.run(&compiled.input.assign(&private).unwrap(), &[]);
  let public = compiled.public.instantiate(&expected.limbs()).unwrap();
  assert_eq!(witness.public, public);
  let objects = compiled.machine.objects.as_ref().unwrap();
  let gate = &objects.gate;
  let index = compiled.shape.registry_slot(objects.slot);
  let mut rows = witness.rows::<ObjectDispatchGate>(objects.slot).to_vec();
  let mut forged = rows[0].inputs().to_vec();
  if forge_identity {
    // Replace the selected pair by the distinct nullary declaration. The
    // numeric member/tag is the same, but the full declaration ID differs.
    let arena = 1 + gate.normalized_words() + objects.layout.program_words();
    forged[arena].lo = 0; // declaration 0, no fields; presence stays set.
    forged[arena + 1..arena + objects.layout.record_words()].fill(F128::ZERO);
  } else {
    let args = 1 + CAPACITY.control.frame_words() + 5;
    forged[args + 3].lo ^= 1; // canonical Word32 field 17 -> 16
  }
  let mut output = Vec::new();
  rows[0] = gate.eval(&forged, &(), &mut output);
  assert_eq!(output.last(), Some(&F128::ZERO));
  let mut drivers = witness::drivers(compiled, &witness);
  drivers[index] = UnionSlotProverInput::in_place(
    move |dst| gate.generate_witness_into(&rows, dst),
    compiled.tables[index].csc_lincheck_circuit(),
  );
  compiled.prove_rows(&public, drivers).unwrap()
}
