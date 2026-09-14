use super::application_fixtures::{CAPACITY, cases, setup};
use super::*;
use crate::ixby::{
  application::PapDispatchGate, bits::fill_words, control::ControlStepGate,
};
use flock_prover::{
  circuit::builder::GateType, field::F128, prover::UnionSlotProverInput,
};

const CHILD: &str = "IXBY_FLOCK_APPLICATION_VERIFY_CHILD";
const TEST: &str = "ixby::exec::application_proof_tests::application_proofs_verify_in_isolation_and_reject_recomputed_capture_rest_and_return_rows";

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
      "isolated application verifier rejected: {}",
      String::from_utf8_lossy(&result.stderr)
    );
  }
  result.status.success()
}

#[test]
#[ignore = "bounded application proofs, isolated digest-only verifiers and recomputed capture/rest/return forgeries"]
fn application_proofs_verify_in_isolation_and_reject_recomputed_capture_rest_and_return_rows()
 {
  use std::{io::Read, time::Instant};
  if std::env::var_os(CHILD).is_some() {
    let mut bytes = Vec::new();
    std::io::stdin()
      .take(proof::MAX_BYTES + 33)
      .read_to_end(&mut bytes)
      .unwrap();
    assert!((32..=proof::MAX_BYTES as usize + 32).contains(&bytes.len()));
    // The verifier receives only approved setup, expected digest and proof.
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
  for (index, (code, input, output)) in cases.iter().enumerate() {
    let expected = expected_statement(compiled.profile(), code, input, output);
    let start = Instant::now();
    let bytes = compiled.prove(expected, code, input).unwrap();
    let proving = start.elapsed();
    let start = Instant::now();
    assert!(isolated(expected, &bytes), "application proof {index}");
    eprintln!(
      "Application Exec {index}/{}: {} proof bytes, prove {:.3}s, fresh verify {:.3}s",
      cases.len(),
      bytes.len(),
      proving.as_secs_f64(),
      start.elapsed().as_secs_f64()
    );
    assert_eq!(compiled.identities(), identity);
    if index == 0 {
      for at in [0, 8, 39, bytes.len() / 2, bytes.len() - 1] {
        let mut bad = bytes.clone();
        bad[at] ^= 1;
        assert!(compiled.verify(expected, &bad).is_err());
      }
      let mut wrong = output.clone();
      *wrong.last_mut().unwrap() ^= 1;
      assert!(
        compiled
          .verify(
            expected_statement(compiled.profile(), code, input, &wrong),
            &bytes
          )
          .is_err()
      );
      let old = compile_exec_object_profile(
        compiled.profile(),
        CAPACITY,
        ByteCapacity::new(33).unwrap(),
        ObjectCapacity::new(2, 3, 7).unwrap(),
        PrimitiveSet::crypto(),
        Blake3Backend::PackedWordsV0,
      )
      .unwrap();
      assert_ne!(old.identities(), identity);
      assert!(old.verify(expected, &bytes).is_err());
      let mut renamed = bytes.clone();
      renamed[8..40].copy_from_slice(&old.identities().digest());
      assert!(old.verify(expected, &renamed).is_err());
    }
  }
  for (index, forgery) in [(0, 0), (14, 1), (14, 2)] {
    let (code, input, output) = &cases[index];
    let expected = expected_statement(compiled.profile(), code, input, output);
    let forged = spliced_proof(&compiled, expected, code, input, forgery);
    assert!(
      !isolated(expected, &forged),
      "locally valid application forgery {forgery}"
    );
    eprintln!("Application recomputed forgery {forgery} rejected");
  }
}

fn spliced_proof(
  compiled: &CompiledExec,
  expected: ExecStatementDigest,
  code: &[u8],
  input: &[u8],
  forgery: usize,
) -> Vec<u8> {
  let private = [
    proof::buffer(CAPACITY.program.bytes, code).unwrap(),
    proof::buffer(CAPACITY.input.bytes, input).unwrap(),
  ]
  .concat();
  let witness =
    compiled.shape.run(&compiled.input.assign(&private).unwrap(), &[]);
  let public = compiled.public.instantiate(&expected.limbs()).unwrap();
  assert_eq!(witness.public, public);
  let mut drivers = witness::drivers(compiled, &witness);
  if forgery == 2 {
    let gate = &compiled.machine.control_gate;
    let slot = compiled.machine.control_slot.slot();
    let registry = compiled.shape.registry_slot(slot);
    let mut rows = witness.rows::<ControlStepGate>(slot).to_vec();
    // Ret must resume the top apply-rest continuation, before the older let.
    let row = rows
      .iter()
      .position(|row| {
        let state = row.inputs();
        state[0].lo as u32 == 1 && state[0].hi as u32 == 2
      })
      .unwrap();
    let mut forged = rows[row].inputs().to_vec();
    let top = 3 + 2 * CAPACITY.control.frame_words();
    assert_eq!(forged[top].hi >> 32, 1);
    assert_eq!(forged[top + 2].lo, 22);
    forged[top + 2].lo = 23;
    let mut output = Vec::new();
    rows[row] = gate.eval(&forged, &(), &mut output);
    assert_eq!(output.last(), Some(&F128::ZERO));
    let r1cs = gate.r1cs();
    let mut bits = vec![false; r1cs.n()];
    gate
      .plan()
      .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&forged, bits));
    assert!(r1cs.satisfies(&bits));
    drivers[registry] = UnionSlotProverInput::in_place(
      move |dst| gate.generate_witness_into(&rows, dst),
      compiled.tables[registry].csc_lincheck_circuit(),
    );
    compiled.prove_rows(&public, drivers).unwrap()
  } else {
    let apps = compiled.machine.applications.as_ref().unwrap();
    let gate = &apps.gate;
    let registry = compiled.shape.registry_slot(apps.slot);
    let mut rows = witness.rows::<PapDispatchGate>(apps.slot).to_vec();
    let row = if forgery == 0 { 0 } else { 1 };
    let mut forged = rows[row].0.clone();
    if forgery == 0 {
      let first_capture = 1 + CAPACITY.control.state_words() + 6;
      assert_eq!(forged[first_capture].lo, 11);
      forged[first_capture].lo = 12;
    } else {
      assert_eq!(forged[1].lo as u32, 3);
      assert_eq!(forged[6].lo, 22);
      forged[6].lo = 23;
    }
    let mut output = Vec::new();
    rows[row] = gate.eval(&forged, &(), &mut output);
    assert_eq!(output.last(), Some(&F128::ZERO));
    let r1cs = gate.r1cs();
    let mut bits = vec![false; r1cs.n()];
    gate
      .plan()
      .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&forged, bits));
    assert!(r1cs.satisfies(&bits));
    drivers[registry] = UnionSlotProverInput::in_place(
      move |dst| gate.generate_witness_into(&rows, dst),
      compiled.tables[registry].csc_lincheck_circuit(),
    );
    compiled.prove_rows(&public, drivers).unwrap()
  }
}
