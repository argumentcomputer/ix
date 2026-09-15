use super::nat_fixtures::{CAPACITY, cases, setup};
use super::*;

#[test]
fn native_nat_operations_control_objects_and_bytes_execute_in_one_setup() {
  let compiled = setup();
  eprintln!(
    "Nat Exec census nu={}, m={}, tables={}, largest_log_k={}, setup={}",
    compiled.nu,
    compiled.params.m,
    compiled.tables.len(),
    compiled.tables.iter().map(|t| t.k_log).max().unwrap(),
    blake3::Hash::from_bytes(compiled.identities().digest()).to_hex()
  );
  assert_eq!(compiled.nat_capacity().unwrap().bits(), 192);
  assert_eq!(
    blake3::Hash::from_bytes(compiled.identities().digest()).to_hex().as_str(),
    "b82c5886b0e40c74c45aa0f7939a3470d2791e275465e3851170857d6e218376"
  );
  for (index, (code, input, output)) in cases().into_iter().enumerate() {
    let expected =
      expected_statement(compiled.profile(), &code, &input, &output);
    // Independently encoded and evaluated in Tests/Ixby/Flock/Nats.lean.
    let golden = match index {
      0 => Some([
        10543937101595496891,
        13067204517167037398,
        14111677314597180777,
        11101863275982993741,
      ]),
      25 => Some([
        6431930672498536397,
        8633735064928880919,
        14192929670046353702,
        520228631706350942,
      ]),
      29 => Some([
        12256219420089308533,
        2944215410467354441,
        4031868974126339541,
        9999387711666983146,
      ]),
      _ => None,
    };
    if let Some(golden) = golden {
      assert_eq!(
        expected
          .limbs()
          .iter()
          .flat_map(|word| [word.lo, word.hi])
          .collect::<Vec<_>>(),
        golden,
        "Lean Nat statement golden {index}"
      );
    }
    let private = [
      proof::buffer(CAPACITY.program.bytes, &code).unwrap(),
      proof::buffer(CAPACITY.input.bytes, &input).unwrap(),
    ]
    .concat();
    let witness =
      compiled.shape.run(&compiled.input.assign(&private).unwrap(), &[]);
    assert_eq!(
      witness.public,
      compiled.public.instantiate(&expected.limbs()).unwrap(),
      "Nat case {index}"
    );
    assert_eq!(
      witness::drivers(&compiled, &witness).len(),
      compiled.tables.len()
    );
    eprintln!(
      "Nat execution {index}: program/input/output {}/{}/{}",
      code.len(),
      input.len(),
      output.len()
    );
  }
}

#[test]
fn nat_setup_requires_explicit_revision_bounds_and_primitive_admission() {
  let bytes = ByteCapacity::new(33).unwrap();
  let objects = ObjectCapacity::new(2, 3, 7).unwrap();
  let nats = NatCapacity::new(192).unwrap();
  let values = (bytes, Some(objects), nats);
  let profile =
    SemanticProfile::nat(CAPACITY, bytes, Some(objects), nats).unwrap();
  let backend = Blake3Backend::PackedWordsV0;
  let primitives = PrimitiveSet::crypto_nat();
  assert_eq!(profile.revision(), 1);
  assert_eq!(
    SemanticProfile::from_bytes(&profile.to_bytes()).unwrap(),
    profile
  );
  assert_eq!(
    primitives.opcodes().collect::<Vec<_>>(),
    (0..42).collect::<Vec<_>>()
  );
  assert_eq!(primitives.crypto_subset(), PrimitiveSet::crypto());
  assert!(PrimitiveSet::new(&[35]).is_err());
  assert!(PrimitiveSet::with_bytes(&[35]).is_err());
  assert!(PrimitiveSet::with_crypto(&[35]).is_err());
  assert!(PrimitiveSet::with_nat(&[42]).is_err());
  assert!(PrimitiveSet::with_nat(&[35, 35]).is_err());
  assert_eq!(NatCapacity::new(0).unwrap().bytes(), 0);
  assert_eq!(NatCapacity::new(1024).unwrap().bytes(), 128);
  assert!(NatCapacity::new(1025).is_err());
  for index in 0..14 {
    let mut parameters = profile.parameters();
    parameters[index] += 1;
    if let Ok(changed) = SemanticProfile::new_nat(parameters) {
      assert!(
        compile_exec_nat_profile(
          changed, CAPACITY, values, primitives, backend
        )
        .is_err(),
        "changed Nat semantic capacity {index}"
      );
    }
  }
  assert!(
    compile_exec_nat_profile(
      profile,
      CAPACITY,
      (bytes, Some(objects), NatCapacity::new(191).unwrap()),
      primitives,
      backend
    )
    .is_err()
  );
  assert!(
    SemanticProfile::nat(
      CAPACITY,
      ByteCapacity::new(23).unwrap(),
      Some(objects),
      nats
    )
    .is_err()
  );
  let old = SemanticProfile::objects(CAPACITY, bytes, objects).unwrap();
  assert!(
    compile_exec_nat_profile(old, CAPACITY, values, primitives, backend)
      .is_err()
  );
  assert!(
    compile_exec_object_profile(
      profile,
      CAPACITY,
      bytes,
      objects,
      PrimitiveSet::crypto(),
      backend
    )
    .is_err()
  );
  assert!(
    compile_exec_object_profile(
      old, CAPACITY, bytes, objects, primitives, backend
    )
    .is_err()
  );
  let old_bytes = SemanticProfile::bytes(CAPACITY, bytes).unwrap();
  assert!(
    compile_exec_byte_profile(old_bytes, CAPACITY, bytes, primitives, backend)
      .is_err()
  );
  let old_scalar = SemanticProfile::scalar(CAPACITY).unwrap();
  assert!(compile_exec_profile(old_scalar, CAPACITY, primitives).is_err());
}

#[test]
fn nat_without_objects_handles_zero_and_partial_byte_bounds_and_rejects_invalid_execution()
 {
  use super::nat_fixtures::{nat, operation, revision};
  use crate::ixby::decode::test_support::{
    FunctionImage as F, Instruction as I, Operand as O, Value as V, input,
    output, program,
  };
  let mut capacity = CAPACITY;
  capacity.program.functions = 1;
  capacity.control.continuations = 1;
  capacity.input.bytes = 64;
  capacity.output_bytes = 64;
  capacity.steps = 4;
  for bits in [0, 9] {
    let bytes = ByteCapacity::new(2).unwrap();
    let nats = NatCapacity::new(bits).unwrap();
    let compiled = compile_exec_nat_profile(
      SemanticProfile::nat(capacity, bytes, None, nats).unwrap(),
      capacity,
      (bytes, None, nats),
      PrimitiveSet::with_nat(&[35, 36, 37, 38, 39, 40, 41]).unwrap(),
      Blake3Backend::PackedWordsV0,
    )
    .unwrap();
    assert!(compiled.object_capacity().is_none());
    assert_eq!(compiled.nat_capacity(), Some(nats));
    let run = |(code, input, output): (Vec<u8>, Vec<u8>, Vec<u8>),
               valid: bool| {
      let expected =
        expected_statement(compiled.profile(), &code, &input, &output);
      let private = [
        proof::buffer(capacity.program.bytes, &code).unwrap(),
        proof::buffer(capacity.input.bytes, &input).unwrap(),
      ]
      .concat();
      // The ordinary prover also catches inconsistent fixed-zero wiring.
      // This checks execution admission, not cryptographic verification.
      let witness =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
          compiled.shape.run(&compiled.input.assign(&private).unwrap(), &[])
        }));
      assert_eq!(
        witness.is_ok_and(|witness| witness.public
          == compiled.public.instantiate(&expected.limbs()).unwrap()),
        valid,
        "Nat bits={bits}, code={code:?}, input={input:?}"
      );
    };
    let (a, b) = if bits == 0 { (0u32, 0u32) } else { (510, 1) };
    let results = [
      nat(a + b),
      nat(a.saturating_sub(b)),
      nat(a * b),
      nat(a.checked_div(b).unwrap_or(0)),
      nat(a.checked_rem(b).unwrap_or(a)),
      V::Bool(u8::from(a == b)),
      V::Bool(u8::from(a < b)),
    ];
    for (opcode, result) in (35..42).zip(results) {
      run(operation(opcode, &[nat(a), nat(b)], &result), true);
    }
    let case = revision(program(
      0,
      &[F {
        arity: 1,
        entry: 0,
        blocks: vec![
          (1, I::CaseNat(O::Local(0), 1, 2)),
          (1, I::Ret(O::Local(0))),
          (2, I::Ret(O::Local(1))),
        ],
      }],
    ));
    for value in if bits == 0 { vec![0u32] } else { vec![0, 1, 511] } {
      run(
        (
          case.clone(),
          revision(input(&[nat(value)])),
          revision(output(&nat(value.saturating_sub(1)))),
        ),
        true,
      );
    }
    run(
      (case, revision(input(&[V::Word(0)])), revision(output(&nat(0u32)))),
      false,
    );
    run(operation(35, &[V::Word(0), nat(0u32)], &nat(0u32)), false);
    run(operation(35, &[V::Bytes(vec![]), nat(0u32)], &nat(0u32)), false);
    run(operation(35, &[V::Nat(vec![0]), nat(0u32)], &nat(0u32)), false);
    let maximum = (1u32 << bits) - 1;
    run(operation(35, &[nat(maximum + 1), nat(0u32)], &nat(0u32)), false);
    if bits != 0 {
      run(operation(35, &[nat(maximum), nat(1u32)], &nat(0u32)), false);
      run(operation(37, &[nat(256u32), nat(2u32)], &nat(0u32)), false);
      run(operation(35, &[V::Nat(vec![1, 0]), nat(0u32)], &nat(1u32)), false);
    }
    let mut old_revision = operation(35, &[nat(0u32), nat(0u32)], &nat(0u32));
    old_revision.0[4..8].fill(0);
    run(old_revision, false);
  }
}

const CHILD: &str = "IXBY_FLOCK_NAT_EXEC_VERIFY_CHILD";
const TEST: &str = "ixby::exec::nat_tests::nat_exec_proofs_verify_in_isolation_and_reject_recomputed_arithmetic_and_case_rows";

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
      "isolated Nat verifier rejected: {}",
      String::from_utf8_lossy(&result.stderr)
    );
  }
  result.status.success()
}

#[test]
#[ignore = "exact-Nat execution proofs, isolated verifiers and recomputed malicious arithmetic/case rows"]
fn nat_exec_proofs_verify_in_isolation_and_reject_recomputed_arithmetic_and_case_rows()
 {
  use std::{io::Read, time::Instant};
  if std::env::var_os(CHILD).is_some() {
    let mut bytes = Vec::new();
    std::io::stdin()
      .take(proof::MAX_BYTES + 33)
      .read_to_end(&mut bytes)
      .unwrap();
    assert!((32..=proof::MAX_BYTES as usize + 32).contains(&bytes.len()));
    // No private program, input, output, trace, decoded magnitude, or evaluator.
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
    assert!(isolated(expected, &bytes), "Nat proof case {index}");
    eprintln!(
      "Nat Exec {index}/{}: {} proof bytes, prove {:.3}s, fresh verify {:.3}s",
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
      let smaller = nat_fixtures::setup_with_bits(191);
      assert_ne!(identity, smaller.identities());
      assert!(smaller.verify(expected, &bytes).is_err());
      let mut renamed = bytes.clone();
      renamed[8..40].copy_from_slice(&smaller.identities().digest());
      assert!(smaller.verify(expected, &renamed).is_err());
      let old = object_fixtures::setup();
      assert!(old.verify(expected, &bytes).is_err());
      renamed[8..40].copy_from_slice(&old.identities().digest());
      assert!(old.verify(expected, &renamed).is_err());
    }
  }
  for index in [0, 21] {
    let (code, input, output) = &cases[index];
    let expected = expected_statement(compiled.profile(), code, input, output);
    let forged = spliced_proof(&compiled, expected, code, input, index == 21);
    assert!(
      !isolated(expected, &forged),
      "fully recomputed Nat row splice must reject"
    );
  }
}

fn spliced_proof(
  compiled: &CompiledExec,
  expected: ExecStatementDigest,
  code: &[u8],
  input: &[u8],
  case: bool,
) -> Vec<u8> {
  use crate::ixby::{bits::fill_words, nat_value::NatDispatchGate};
  use flock_prover::{
    circuit::builder::GateType, field::F128, prover::UnionSlotProverInput,
  };
  let private = [
    proof::buffer(CAPACITY.program.bytes, code).unwrap(),
    proof::buffer(CAPACITY.input.bytes, input).unwrap(),
  ]
  .concat();
  let witness =
    compiled.shape.run(&compiled.input.assign(&private).unwrap(), &[]);
  let public = compiled.public.instantiate(&expected.limbs()).unwrap();
  assert_eq!(witness.public, public);
  let nats = compiled.machine.nats.as_ref().unwrap();
  let gate = &nats.gate;
  let index = compiled.shape.registry_slot(nats.slot);
  let mut rows = witness.rows::<NatDispatchGate>(nats.slot).to_vec();
  let mut forged = rows[0].0.clone();
  let first_data =
    CAPACITY.control.frame_words() + 4 + 2 * CAPACITY.program.operands;
  if case {
    forged[first_data].lo = 2;
  } else {
    forged[first_data].lo ^= 1;
  }
  let mut output = Vec::new();
  rows[0] = gate.eval(&forged, &(), &mut output);
  assert_eq!(output.last(), Some(&F128::ZERO));
  let r1cs = gate.r1cs();
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&forged, bits));
  assert!(r1cs.satisfies(&bits), "changed row remains locally valid");
  let mut drivers = witness::drivers(compiled, &witness);
  drivers[index] = UnionSlotProverInput::in_place(
    move |dst| gate.generate_witness_into(&rows, dst),
    compiled.tables[index].csc_lincheck_circuit(),
  );
  compiled.prove_rows(&public, drivers).unwrap()
}
