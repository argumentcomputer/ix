//! Explicit implementation upgrade conformance; generic scalar execution,
//! not a certified Stage 2 guest or terminal FFLONK proof.

use super::{
  tests::{CAPACITY, cases},
  *,
};
use crate::{
  blake3_backend::Blake3CompressionSlots,
  packed_blake3::{PackedGateKind, PackedWordGate},
};
use flock_prover::{
  circuit::builder::GateType, field::F128, prover::UnionSlotProverInput,
};
use std::{
  io::{Read, Write},
  process::{Command, Stdio},
};

fn setup(backend: Blake3Backend) -> CompiledExec {
  compile_exec_profile_with_backend(
    SemanticProfile::scalar(CAPACITY).unwrap(),
    CAPACITY,
    PrimitiveSet::scalar(),
    backend,
  )
  .unwrap()
}

#[test]
fn backend_choice_binds_new_keys_but_preserves_generic_execution_and_legacy_identity()
 {
  let legacy = setup(Blake3Backend::LegacyOptionF);
  let packed = setup(Blake3Backend::PackedWordsV0);
  assert_eq!(legacy.identities(), tests::setup().identities());
  assert_eq!(
    packed.identities(),
    setup(Blake3Backend::PackedWordsV0).identities()
  );
  assert_eq!(packed.blake3_backend(), Blake3Backend::PackedWordsV0);
  assert_eq!(legacy.blake3_backend(), Blake3Backend::LegacyOptionF);
  let (a, b) = (legacy.identities(), packed.identities());
  assert_eq!(a.profile, b.profile);
  assert_eq!(a.capacity, b.capacity);
  assert_eq!(a.primitives, b.primitives);
  assert_ne!(a.implementation, b.implementation);
  assert_ne!(a.registry, b.registry);
  assert_ne!(a.circuit, b.circuit);
  assert_ne!(a.digest(), b.digest());
  assert_ne!(legacy.transcript_domain(), packed.transcript_domain());
  assert_eq!(legacy.shape.counts.len(), 23);
  assert_eq!(packed.shape.counts.len(), 32);
  assert_eq!(packed.public.outputs(), 2);
  assert_eq!(legacy.input.private_words(), packed.input.private_words());
  let Blake3CompressionSlots::PackedWordsV0(first) =
    packed.commitments.hashes()[0].compression()
  else {
    panic!("explicit packed backend");
  };
  for hash in packed.commitments.hashes() {
    let Blake3CompressionSlots::PackedWordsV0(current) = hash.compression()
    else {
      panic!("all domains must share the backend")
    };
    assert_eq!(current.gates().len(), 10);
    for ((a, left), (b, right)) in first.gates().iter().zip(current.gates()) {
      assert_eq!(a.kind(), b.kind());
      assert_eq!(left, right);
    }
  }
  // The entire existing scalar/control corpus, including changed images,
  // branch outcomes, call/recursion depths and all enabled scalar opcodes.
  for (code, args, result) in cases() {
    let expected = expected_statement(packed.profile(), &code, &args, &result);
    let private = [
      proof::buffer(CAPACITY.program.bytes, &code).unwrap(),
      proof::buffer(CAPACITY.input.bytes, &args).unwrap(),
    ]
    .concat();
    let witness =
      packed.shape.run(&packed.input.assign(&private).unwrap(), &[]);
    assert_eq!(
      witness.public,
      packed.public.instantiate(&expected.limbs()).unwrap()
    );
    assert_eq!(witness::drivers(&packed, &witness).len(), 32);
  }
  let union =
    UnionInstance::new(&packed.shape.registry, packed.shape.counts.clone());
  let config = packed.params.ligerito_verifier_config().unwrap();
  eprintln!(
    "packed scalar Exec: setup {:?}, nu={}, virtual_m={}, dense_m={}, dense_words={}, live_lanes={}, queries={:?}, grinding={:?}",
    b.digest(),
    packed.nu,
    union.m_total(),
    packed.params.m,
    union.dense_words(),
    packed.params.num_ntts(),
    config.queries,
    config.grinding_bits
  );
}

const CHILD: &str = "IXBY_PACKED_EXEC_VERIFY_CHILD";
const TEST: &str = "ixby::exec::backend_tests::packed_exec_proofs_verify_in_isolation_and_reject_backend_and_wiring_substitution";

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
      "isolated packed Exec rejection: {}",
      String::from_utf8_lossy(&result.stderr)
    );
  }
  result.status.success()
}

#[test]
#[ignore = "all scalar corpus real packed Exec proofs, fresh verification, cross-backend and valid-row wiring negatives"]
fn packed_exec_proofs_verify_in_isolation_and_reject_backend_and_wiring_substitution()
 {
  if std::env::var_os(CHILD).is_some() {
    let mut bytes = Vec::new();
    std::io::stdin()
      .take(proof::MAX_BYTES + 33)
      .read_to_end(&mut bytes)
      .unwrap();
    assert!((32..=proof::MAX_BYTES as usize + 32).contains(&bytes.len()));
    let expected = ExecStatementDigest(bytes[..32].try_into().unwrap());
    // Approved backend is fixed here, never selected by proof metadata.
    // No guest, byte input, trace, gate evaluation or native hash is needed.
    setup(Blake3Backend::PackedWordsV0).verify(expected, &bytes[32..]).unwrap();
    return;
  }
  let packed = setup(Blake3Backend::PackedWordsV0);
  let identity = packed.identities();
  for (index, (code, args, result)) in cases().into_iter().enumerate() {
    let expected = expected_statement(packed.profile(), &code, &args, &result);
    let bytes = packed.prove(expected, &code, &args).unwrap();
    assert!(isolated(expected, &bytes));
    assert_eq!(packed.identities(), identity);
    eprintln!("packed Exec corpus case {index}: {} bundle bytes", bytes.len());
    if index != 0 {
      continue;
    }
    let legacy = setup(Blake3Backend::LegacyOptionF);
    let old = legacy.prove(expected, &code, &args).unwrap();
    for (receiver, foreign) in [(&legacy, &bytes), (&packed, &old)] {
      assert!(receiver.verify(expected, foreign).is_err());
      let mut forged_header = foreign.clone();
      forged_header[8..40].copy_from_slice(&receiver.identities().digest());
      assert!(receiver.verify(expected, &forged_header).is_err());
    }
    let mut wrong = expected;
    wrong.0[0] ^= 1;
    assert!(!isolated(wrong, &bytes));
    for i in [0, 8, 39, 40, bytes.len() - 1] {
      let mut wrong = bytes.clone();
      wrong[i] ^= 1;
      assert!(packed.verify(expected, &wrong).is_err());
    }
    assert!(packed.verify(expected, &bytes[..bytes.len() - 1]).is_err());
    let mut wrong = bytes.clone();
    wrong.push(0);
    assert!(packed.verify(expected, &wrong).is_err());
    let bad = miswired_compression(&packed, expected, &code, &args);
    assert!(!isolated(expected, &bad));
  }
}

fn miswired_compression(
  compiled: &CompiledExec,
  expected: ExecStatementDigest,
  code: &[u8],
  args: &[u8],
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
  let Blake3CompressionSlots::PackedWordsV0(packed) =
    compiled.commitments.hashes()[0].compression()
  else {
    panic!("packed backend")
  };
  let (gate, slot) = packed
    .gates()
    .iter()
    .find(|(g, _)| g.kind() == PackedGateKind::Add)
    .unwrap();
  let mut rows = witness.rows::<PackedWordGate>(*slot).to_vec();
  // Replace the initial IV addition with a valid zero+zero row. The driver
  // computes a satisfying local witness; only global wiring is invalid.
  rows[0] = gate.eval(&[F128::ZERO; 2], &(), &mut Vec::new());
  let index = compiled.shape.registry_slot(*slot);
  drivers[index] = UnionSlotProverInput::in_place(
    move |dst| gate.generate_witness_into(&rows, dst),
    compiled.tables[index].csc_lincheck_circuit(),
  );
  compiled.prove_rows(&public, drivers).unwrap()
}
