use super::*;
use crate::ixby::{
  control::ControlCapacities,
  decode::{
    InputCapacities, ProgramCapacities,
    test_support::{
      FunctionImage as F, Instruction as I, Operand as O, Value as V, input,
      output, program,
    },
  },
};

pub(super) const CAPACITY: MachineCapacities = MachineCapacities {
  program: ProgramCapacities {
    bytes: 192,
    functions: 1,
    blocks: 2,
    operands: 3,
  },
  control: ControlCapacities { locals: 4, continuations: 1, arguments: 3 },
  input: InputCapacities { bytes: 192, values: 3 },
  output_bytes: 192,
  steps: 3,
};

pub(super) fn setup() -> CompiledExec {
  let bytes = ByteCapacity::new(65).unwrap();
  compile_exec_byte_profile(
    SemanticProfile::bytes(CAPACITY, bytes).unwrap(),
    CAPACITY,
    bytes,
    PrimitiveSet::crypto_bytes(),
    Blake3Backend::PackedWordsV0,
  )
  .unwrap()
}

pub(super) fn operation(
  opcode: u8,
  args: &[V],
  result: &V,
) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
  let arity = args.len() as u32;
  (
    program(
      0,
      &[F {
        arity,
        entry: 0,
        blocks: vec![
          (arity, I::Primitive(opcode, (0..arity).map(O::Local).collect(), 1)),
          (arity + 1, I::Ret(O::Local(arity))),
        ],
      }],
    ),
    input(args),
    output(result),
  )
}

pub(super) fn cases() -> Vec<(Vec<u8>, Vec<u8>, Vec<u8>)> {
  let data: Vec<_> = (0..65).map(|i| (i * 73 + 19) as u8).collect();
  let bytes = V::Bytes(data.clone());
  let mut cases = vec![
    operation(
      11,
      &[V::Word(0x89ab_cdef)],
      &V::Bytes(0x89ab_cdefu32.to_le_bytes().to_vec()),
    ),
    operation(
      12,
      &[V::Bytes(0x89ab_cdefu32.to_le_bytes().to_vec())],
      &V::Word(0x89ab_cdef),
    ),
    operation(
      19,
      &[V::Field(0xffff_ffff_0000_0000)],
      &V::Bytes(0xffff_ffff_0000_0000u64.to_le_bytes().to_vec()),
    ),
    operation(
      20,
      &[V::Bytes(0xffff_ffff_0000_0000u64.to_le_bytes().to_vec())],
      &V::Field(0xffff_ffff_0000_0000),
    ),
    operation(29, std::slice::from_ref(&bytes), &V::Word(65)),
    operation(30, &[bytes.clone(), V::Word(64)], &V::Word(data[64].into())),
    operation(
      31,
      &[V::Bytes(data[..31].to_vec()), V::Bytes(data[31..].to_vec())],
      &bytes,
    ),
    operation(
      32,
      &[bytes.clone(), V::Word(15), V::Word(18)],
      &V::Bytes(data[15..33].to_vec()),
    ),
    operation(32, &[bytes.clone(), V::Word(65), V::Word(0)], &V::Bytes(vec![])),
    operation(33, &[bytes.clone(), bytes.clone()], &V::Bool(1)),
    operation(33, &[V::Bytes(vec![0]), V::Bytes(vec![])], &V::Bool(0)),
    operation(
      34,
      std::slice::from_ref(&bytes),
      &V::Bytes(blake3::hash(&data).as_bytes().to_vec()),
    ),
    operation(
      34,
      &[V::Bytes(vec![])],
      &V::Bytes(blake3::hash(&[]).as_bytes().to_vec()),
    ),
    operation(0, &[V::Word(u32::MAX), V::Word(2)], &V::Word(1)),
  ];
  // Proposed success ABI: exact canonical CheckEnv(root, none) bytes. This
  // checks result representation only, not certification of a Stage 2 guest.
  let claim = [vec![0xe5], vec![0x2a; 32], vec![0]].concat();
  for data in [vec![], vec![0], data, claim] {
    let value = V::Bytes(data);
    cases.push((
      program(
        0,
        &[F { arity: 1, entry: 0, blocks: vec![(1, I::Ret(O::Local(0)))] }],
      ),
      input(std::slice::from_ref(&value)),
      output(&value),
    ));
    cases.push((
      program(
        0,
        &[F {
          arity: 0,
          entry: 0,
          blocks: vec![(0, I::Ret(O::Literal(value.clone())))],
        }],
      ),
      input(&[]),
      output(&value),
    ));
  }
  cases.push((
    program(
      0,
      &[F {
        arity: 0,
        entry: 0,
        blocks: vec![(0, I::Ret(O::Literal(V::Erased)))],
      }],
    ),
    input(&[]),
    output(&V::Erased),
  ));
  cases
}

#[test]
fn byte_profile_executes_existing_opcodes_and_commits_every_output_byte() {
  let compiled = setup();
  eprintln!(
    "Byte Exec census: nu={}, m={}, tables={}, setup={}",
    compiled.nu,
    compiled.params.m,
    compiled.tables.len(),
    blake3::Hash::from_bytes(compiled.identities().digest()).to_hex()
  );
  assert_eq!(compiled.byte_capacity().unwrap().bytes(), 65);
  assert_eq!(compiled.tables.len(), 36);
  assert_eq!(
    blake3::Hash::from_bytes(compiled.identities().digest()).to_hex().as_str(),
    "5d2443a7f909e97fd1414963e8a4c4c5e534c43c8c477419763b84d2381b8092"
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
      "byte case {index}"
    );
    assert_eq!(
      witness::drivers(&compiled, &witness).len(),
      compiled.tables.len()
    );
  }
}

#[test]
fn byte_profile_is_an_explicit_setup_upgrade() {
  let bytes = ByteCapacity::new(65).unwrap();
  let scalar = SemanticProfile::scalar(CAPACITY).unwrap();
  let profile = SemanticProfile::bytes(CAPACITY, bytes).unwrap();
  assert_eq!(
    SemanticProfile::from_bytes(&profile.to_bytes()).unwrap(),
    profile
  );
  assert_ne!(profile, scalar);
  assert!(
    compile_exec_profile(profile, CAPACITY, PrimitiveSet::scalar()).is_err()
  );
  assert!(
    compile_exec_profile(scalar, CAPACITY, PrimitiveSet::crypto_bytes())
      .is_err()
  );
  assert!(
    compile_exec_byte_profile(
      scalar,
      CAPACITY,
      bytes,
      PrimitiveSet::crypto_bytes(),
      Blake3Backend::PackedWordsV0
    )
    .is_err()
  );
  assert!(
    compile_exec_byte_profile(
      profile,
      CAPACITY,
      ByteCapacity::new(64).unwrap(),
      PrimitiveSet::crypto_bytes(),
      Blake3Backend::PackedWordsV0
    )
    .is_err()
  );
  assert!(ByteCapacity::new(0).is_err());
  assert!(ByteCapacity::new(4097).is_err());
  assert!(
    crate::ixby::primitive::PrimitivePrepareGate::new(
      3,
      3,
      PrimitiveSet::crypto_bytes()
    )
    .is_err()
  );
}

#[test]
fn byte_hash_statement_matches_the_pure_lean_reference_vector() {
  let bytes = ByteCapacity::new(65).unwrap();
  let profile = SemanticProfile::bytes(CAPACITY, bytes).unwrap();
  let data: Vec<_> = (0..65).map(|i| (i * 73 + 19) as u8).collect();
  let (code, input, output) = operation(
    34,
    &[V::Bytes(data.clone())],
    &V::Bytes(blake3::hash(&data).as_bytes().to_vec()),
  );
  let expected = expected_statement(profile, &code, &input, &output);
  // Independently recomputed by Tests.Ixby.Flock.Bytes using the pure Lean
  // codec, interpreter, BLAKE3 and commitment chain.
  assert_eq!(
    expected
      .limbs()
      .iter()
      .flat_map(|word| [word.lo, word.hi])
      .collect::<Vec<_>>(),
    [
      15935915575136097193,
      10006034811852012573,
      15504166987277840427,
      12112749443985250975
    ]
  );
}

const CHILD: &str = "IXBY_FLOCK_BYTE_EXEC_VERIFY_CHILD";
const PROOF_TEST: &str = "ixby::exec::byte_tests::byte_exec_proofs_verify_in_isolation_and_reject_recomputed_forged_rows";

fn isolated(expected: ExecStatementDigest, proof: &[u8]) -> bool {
  use std::{
    io::Write,
    process::{Command, Stdio},
  };
  let mut child = Command::new(std::env::current_exe().unwrap())
    .args([
      "--ignored",
      "--exact",
      PROOF_TEST,
      "--test-threads=1",
      "--nocapture",
    ])
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
      "isolated byte Exec verifier rejected: {}",
      String::from_utf8_lossy(&result.stderr)
    );
  }
  result.status.success()
}

#[test]
#[ignore = "real byte Exec proofs, fresh verifier processes and locally valid malicious byte rows"]
fn byte_exec_proofs_verify_in_isolation_and_reject_recomputed_forged_rows() {
  use std::{io::Read, time::Instant};
  if std::env::var_os(CHILD).is_some() {
    let mut bytes = Vec::new();
    std::io::stdin()
      .take(proof::MAX_BYTES + 33)
      .read_to_end(&mut bytes)
      .unwrap();
    assert!((32..=proof::MAX_BYTES as usize + 32).contains(&bytes.len()));
    // Only verifier-owned setup and externally supplied S: no program,
    // inputs, output, hash oracle, trace or native execution in this process.
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
  for (index, (code, args, result)) in cases().into_iter().enumerate() {
    let expected =
      expected_statement(compiled.profile(), &code, &args, &result);
    let start = Instant::now();
    let bytes = compiled.prove(expected, &code, &args).unwrap();
    let proving = start.elapsed();
    let start = Instant::now();
    assert!(isolated(expected, &bytes), "byte case {index}");
    eprintln!(
      "Byte Exec case {index}: {} proof bytes, prove {:.3}s, fresh verify {:.3}s",
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
      assert!(compiled.verify(expected, &bytes[..bytes.len() - 1]).is_err());
      let mut wrong_output = result.clone();
      *wrong_output.last_mut().unwrap() ^= 1;
      let wrong =
        expected_statement(compiled.profile(), &code, &args, &wrong_output);
      assert!(compiled.verify(wrong, &bytes).is_err());
      let reduced = PrimitiveSet::with_bytes(
        &PrimitiveSet::crypto_bytes()
          .opcodes()
          .filter(|op| *op != 34)
          .collect::<Vec<_>>(),
      )
      .unwrap();
      let other = compile_exec_byte_profile(
        compiled.profile(),
        CAPACITY,
        compiled.byte_capacity().unwrap(),
        reduced,
        Blake3Backend::PackedWordsV0,
      )
      .unwrap();
      assert_ne!(other.identities(), identity);
      assert!(other.verify(expected, &bytes).is_err());
      let mut renamed = bytes.clone();
      renamed[8..40].copy_from_slice(&other.identities().digest());
      assert!(other.verify(expected, &renamed).is_err());
    }
  }
  let (code, args, result) = operation(
    34,
    &[V::Bytes(vec![1, 2, 3])],
    &V::Bytes(blake3::hash(&[1, 2, 3]).as_bytes().to_vec()),
  );
  let expected = expected_statement(compiled.profile(), &code, &args, &result);
  for forged_hash in [false, true] {
    let proof =
      spliced_byte_proof(&compiled, expected, &code, &args, forged_hash);
    assert!(
      !isolated(expected, &proof),
      "locally valid byte splice must fail wiring"
    );
  }
}

fn spliced_byte_proof(
  compiled: &CompiledExec,
  expected: ExecStatementDigest,
  code: &[u8],
  args: &[u8],
  forged_hash: bool,
) -> Vec<u8> {
  use crate::ixby::byte_value::{BytePrimitiveGate, ByteReadGate};
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
  let mut drivers = witness::drivers(compiled, &witness);
  let bytes = compiled.machine.bytes.as_ref().unwrap();
  if forged_hash {
    let gate = &bytes.primitive_gate;
    let slot = bytes.primitive_slot;
    let index = compiled.shape.registry_slot(slot);
    let mut rows = witness.rows::<BytePrimitiveGate>(slot).to_vec();
    let mut forged = rows[0].inputs().to_vec();
    let digest = forged.len() - 2;
    forged[digest].lo ^= 1;
    let mut output = Vec::new();
    rows[0] = gate.eval(&forged, &(), &mut output);
    assert_eq!(output.last(), Some(&F128::ZERO));
    drivers[index] = UnionSlotProverInput::in_place(
      move |dst| gate.generate_witness_into(&rows, dst),
      compiled.tables[index].csc_lincheck_circuit(),
    );
  } else {
    let gate = &bytes.read_gate;
    let slot = bytes.read_slot.slot();
    let index = compiled.shape.registry_slot(slot);
    let mut rows = witness.rows::<ByteReadGate>(slot).to_vec();
    let mut forged = rows[0].inputs().to_vec();
    let allocation = CAPACITY.program.functions
      * CAPACITY.program.blocks
      * CAPACITY.program.operands;
    forged[2 + allocation * bytes.capacity.record_words() + 1].lo ^= 1;
    let mut output = Vec::new();
    rows[0] = gate.eval(&forged, &(), &mut output);
    assert_eq!(output.last(), Some(&F128::ZERO));
    drivers[index] = UnionSlotProverInput::in_place(
      move |dst| gate.generate_witness_into(&rows, dst),
      compiled.tables[index].csc_lincheck_circuit(),
    );
  }
  compiled.prove_rows(&public, drivers).unwrap()
}

const CONTROL_CAPACITY: MachineCapacities = MachineCapacities {
  program: ProgramCapacities {
    bytes: 256,
    functions: 2,
    blocks: 5,
    operands: 2,
  },
  control: ControlCapacities { locals: 4, continuations: 2, arguments: 2 },
  input: InputCapacities { bytes: 128, values: 2 },
  output_bytes: 128,
  steps: 10,
};

fn control_setup() -> CompiledExec {
  let bytes = ByteCapacity::new(33).unwrap();
  compile_exec_byte_profile(
    SemanticProfile::bytes(CONTROL_CAPACITY, bytes).unwrap(),
    CONTROL_CAPACITY,
    bytes,
    PrimitiveSet::crypto_bytes(),
    Blake3Backend::PackedWordsV0,
  )
  .unwrap()
}

fn control_cases() -> Vec<(Vec<u8>, Vec<u8>, Vec<u8>)> {
  let data: Vec<_> = (0..32).map(|i| (i * 73 + 19) as u8).collect();
  let suffix: Vec<_> = (32..33).map(|i| (i * 73 + 19) as u8).collect();
  let bytes = V::Bytes(data.clone());
  let callee = F {
    arity: 1,
    entry: 0,
    blocks: vec![
      (
        1,
        I::Primitive(
          31,
          vec![O::Local(0), O::Literal(V::Bytes(suffix.clone()))],
          1,
        ),
      ),
      (2, I::Primitive(34, vec![O::Local(1)], 2)),
      (3, I::Ret(O::Local(2))),
    ],
  };
  let mut cases = Vec::new();
  for (condition, returned) in [(1, 3), (1, 2), (0, 3)] {
    let caller = F {
      arity: 2,
      entry: 0,
      blocks: vec![
        (2, I::Copy(O::Local(0), 1)),
        (3, I::Branch(O::Local(1), 2, 3)),
        (3, I::Call(Some(1), vec![O::Local(2)], 4)),
        (3, I::Tail(Some(1), vec![O::Literal(V::Bytes(vec![]))])),
        (4, I::Ret(O::Local(returned))),
      ],
    };
    let expected = if returned == 2 {
      bytes.clone()
    } else {
      let message = if condition == 1 {
        [data.clone(), suffix.clone()].concat()
      } else {
        suffix.clone()
      };
      V::Bytes(blake3::hash(&message).as_bytes().to_vec())
    };
    cases.push((
      program(0, &[caller, callee.clone()]),
      input(&[bytes.clone(), V::Bool(condition)]),
      output(&expected),
    ));
  }
  for tail in [false, true] {
    let call = if tail {
      I::Tail(None, vec![O::Local(0), O::Literal(V::Bool(0))])
    } else {
      I::Call(None, vec![O::Local(0), O::Literal(V::Bool(0))], 3)
    };
    let function = F {
      arity: 2,
      entry: 0,
      blocks: vec![
        (2, I::Branch(O::Local(1), 1, 2)),
        (2, call),
        (2, I::Ret(O::Local(0))),
        (3, I::Ret(O::Local(2))),
      ],
    };
    cases.push((
      program(0, &[function]),
      input(&[bytes.clone(), V::Bool(1)]),
      output(&bytes),
    ));
  }
  for same in [false, true] {
    let function = F {
      arity: 1,
      entry: 0,
      blocks: vec![
        (1, I::Primitive(33, vec![O::Local(0), O::Literal(bytes.clone())], 1)),
        (2, I::Branch(O::Local(1), 2, 3)),
        (2, I::Ret(O::Local(0))),
        (2, I::Ret(O::Literal(V::Bytes(vec![])))),
      ],
    };
    let arg = if same { bytes.clone() } else { V::Bytes(vec![1, 2, 3]) };
    cases.push((
      program(0, &[function]),
      input(&[arg]),
      output(&if same { bytes.clone() } else { V::Bytes(vec![]) }),
    ));
  }
  cases
}

#[test]
fn byte_handles_survive_copy_call_tail_self_call_branch_and_return_wiring() {
  let compiled = control_setup();
  for (index, (code, args, result)) in control_cases().into_iter().enumerate() {
    let expected =
      expected_statement(compiled.profile(), &code, &args, &result);
    let private = [
      proof::buffer(CONTROL_CAPACITY.program.bytes, &code).unwrap(),
      proof::buffer(CONTROL_CAPACITY.input.bytes, &args).unwrap(),
    ]
    .concat();
    let witness =
      compiled.shape.run(&compiled.input.assign(&private).unwrap(), &[]);
    assert_eq!(
      witness.public,
      compiled.public.instantiate(&expected.limbs()).unwrap(),
      "byte control case {index}"
    );
  }
}

#[test]
#[ignore = "real byte allocation/call/branch/return proofs under one larger control setup"]
fn byte_control_proofs_preserve_old_allocations_and_use_constrained_hash_results()
 {
  let compiled = control_setup();
  let identity = compiled.identities();
  eprintln!(
    "Byte control census: nu={}, m={}, largest k={}",
    compiled.nu,
    compiled.params.m,
    compiled.shape.registry.types().iter().map(|t| t.k_log).max().unwrap()
  );
  for (index, (code, args, result)) in control_cases().into_iter().enumerate() {
    let expected =
      expected_statement(compiled.profile(), &code, &args, &result);
    let start = std::time::Instant::now();
    let proof = compiled.prove(expected, &code, &args).unwrap();
    compiled.verify(expected, &proof).unwrap();
    eprintln!(
      "Byte control case {index}: {} proof bytes, prove+verify {:.3}s",
      proof.len(),
      start.elapsed().as_secs_f64()
    );
    assert_eq!(identity, compiled.identities());
  }
}

#[test]
#[ignore = "real legacy-compression byte Exec proofs and cross-backend setup substitution"]
fn byte_exec_legacy_compression_proofs_preserve_semantics_not_setup_identity() {
  let bytes = ByteCapacity::new(65).unwrap();
  let legacy = compile_exec_byte_profile(
    SemanticProfile::bytes(CAPACITY, bytes).unwrap(),
    CAPACITY,
    bytes,
    PrimitiveSet::crypto_bytes(),
    Blake3Backend::LegacyOptionF,
  )
  .unwrap();
  let packed = setup();
  assert_eq!(legacy.profile(), packed.profile());
  assert_ne!(legacy.identities(), packed.identities());
  let cases = cases();
  for index in [6, 11] {
    let (code, args, result) = &cases[index];
    let expected = expected_statement(legacy.profile(), code, args, result);
    let proof = legacy.prove(expected, code, args).unwrap();
    legacy.verify(expected, &proof).unwrap();
    assert!(packed.verify(expected, &proof).is_err());
    let mut renamed = proof.clone();
    renamed[8..40].copy_from_slice(&packed.identities().digest());
    assert!(packed.verify(expected, &renamed).is_err());
    eprintln!(
      "Legacy-compression byte Exec case {index}: {} proof bytes",
      proof.len()
    );
  }
}
