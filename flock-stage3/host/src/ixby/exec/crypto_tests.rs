//! Complete existing crypto-v0 primitive dispatch under one approved setup.
use super::{
  byte_tests::{CAPACITY, operation},
  *,
};
use crate::ixby::{
  control::ControlCapacities,
  decode::{
    InputCapacities, ProgramCapacities,
    test_support::{
      FunctionImage as F, Instruction as I, Operand as O, Value as V, input,
      output, program,
    },
  },
  primitive::PrimitivePrepareGate,
};
use flock_prover::{
  circuit::builder::GateType, field::F128, prover::UnionSlotProverInput,
};

fn setup() -> CompiledExec {
  compile(CAPACITY, 65, Blake3Backend::PackedWordsV0)
}

fn compile(
  capacity: MachineCapacities,
  bytes: usize,
  backend: Blake3Backend,
) -> CompiledExec {
  let bytes = ByteCapacity::new(bytes).unwrap();
  compile_exec_byte_profile(
    SemanticProfile::bytes(capacity, bytes).unwrap(),
    capacity,
    bytes,
    PrimitiveSet::crypto(),
    backend,
  )
  .unwrap()
}

fn cases() -> Vec<(Vec<u8>, Vec<u8>, Vec<u8>)> {
  // One case per byte opcode from the independently tested byte corpus.
  let mut cases: Vec<_> = byte_tests::cases()
    .into_iter()
    .enumerate()
    .filter(|(index, _)| [0, 1, 2, 3, 4, 5, 6, 7, 9, 11].contains(index))
    .map(|(_, case)| case)
    .collect();
  let value = |words: [F128; 2]| match words[0].lo {
    1 => V::Bool(words[1].lo as u8),
    2 => V::Word(words[1].lo as u32),
    3 => V::Field(words[1].lo),
    4 => V::Ext(words[1].lo, words[1].hi),
    _ => unreachable!(),
  };
  for opcode in PrimitiveSet::scalar().opcodes() {
    let (args, result) = crate::ixby::primitive::tests::oracle(
      opcode,
      u32::MAX,
      1,
      0xffff_ffff_0000_0000,
      1,
    );
    cases.push(operation(
      opcode,
      &args.into_iter().map(value).collect::<Vec<_>>(),
      &value(result),
    ));
  }
  for (opcode, a, b) in [
    (1, 0u32, 1u32),
    (1, u32::MAX, u32::MAX),
    (2, u32::MAX, u32::MAX),
    (2, 0x10000, 0x10000),
    (2, 0x89ab_cdef, 17),
    (6, 0x89ab_cdef, 0),
    (6, 0x89ab_cdef, 31),
    (6, 0x89ab_cdef, 32),
    (6, 0x89ab_cdef, 33),
    (6, 0x89ab_cdef, u32::MAX),
    (7, 0x89ab_cdef, 0),
    (7, 0x89ab_cdef, 31),
    (7, 0x89ab_cdef, 32),
    (7, 0x89ab_cdef, 1 << 31),
    (8, 0x89ab_cdef, 0),
    (8, 0x89ab_cdef, 31),
    (8, 0x89ab_cdef, 32),
    (8, 0x89ab_cdef, 33),
    (8, 0x89ab_cdef, u32::MAX),
  ] {
    let result = match opcode {
      1 => a.wrapping_sub(b),
      2 => a.wrapping_mul(b),
      6 => a.checked_shl(b).unwrap_or(0),
      7 => a.checked_shr(b).unwrap_or(0),
      8 => a.rotate_right(b),
      _ => unreachable!(),
    };
    cases.push(operation(opcode, &[V::Word(a), V::Word(b)], &V::Word(result)));
  }
  assert_eq!(cases.len(), 49);
  cases
}

fn check_execution(
  compiled: &CompiledExec,
  code: &[u8],
  args: &[u8],
  result: &[u8],
) {
  let expected = expected_statement(compiled.profile(), code, args, result);
  let c = compiled.capacity();
  let private = [
    proof::buffer(c.program.bytes, code).unwrap(),
    proof::buffer(c.input.bytes, args).unwrap(),
  ]
  .concat();
  let witness =
    compiled.shape.run(&compiled.input.assign(&private).unwrap(), &[]);
  assert_eq!(
    witness.public,
    compiled.public.instantiate(&expected.limbs()).unwrap()
  );
  assert_eq!(witness::drivers(compiled, &witness).len(), compiled.tables.len());
}

#[test]
fn full_crypto_setup_executes_all_35_opcodes_and_preserves_old_setup_identities()
 {
  let compiled = setup();
  assert_eq!(compiled.tables.len(), 36);
  eprintln!(
    "Crypto Exec census: nu={}, m={}, tables={}, setup={}",
    compiled.nu,
    compiled.params.m,
    compiled.tables.len(),
    blake3::Hash::from_bytes(compiled.identities().digest()).to_hex()
  );
  assert_eq!(
    blake3::Hash::from_bytes(compiled.identities().digest()).to_hex().as_str(),
    "5cc6dd8434d9ca4a7ba350267467c4c5183eb0a3e8ae44cc562f1bc8c43a0707"
  );
  for (code, args, result) in cases() {
    check_execution(&compiled, &code, &args, &result);
  }
  let old = byte_tests::setup();
  assert_eq!(old.profile(), compiled.profile());
  assert_eq!(
    blake3::Hash::from_bytes(old.identities().digest()).to_hex().as_str(),
    "5d2443a7f909e97fd1414963e8a4c4c5e534c43c8c477419763b84d2381b8092"
  );
  assert_ne!(old.identities(), compiled.identities());
  assert_ne!(old.transcript_domain(), compiled.transcript_domain());
  assert!(
    compile_exec_profile(
      SemanticProfile::scalar(CAPACITY).unwrap(),
      CAPACITY,
      PrimitiveSet::crypto().crypto_scalar_subset()
    )
    .is_err()
  );
}

const PIPELINE: MachineCapacities = MachineCapacities {
  program: ProgramCapacities {
    bytes: 256,
    functions: 1,
    blocks: 6,
    operands: 2,
  },
  control: ControlCapacities { locals: 7, continuations: 1, arguments: 2 },
  input: InputCapacities { bytes: 128, values: 2 },
  output_bytes: 128,
  steps: 7,
};

fn pipeline() -> (Vec<u8>, Vec<u8>, Vec<u8>) {
  let code = program(
    0,
    &[F {
      arity: 2,
      entry: 0,
      blocks: vec![
        (2, I::Primitive(2, vec![O::Local(0), O::Local(1)], 1)),
        (
          3,
          I::Primitive(
            1,
            vec![O::Local(2), O::Literal(V::Word(0x0102_0304))],
            2,
          ),
        ),
        (4, I::Primitive(8, vec![O::Local(3), O::Literal(V::Word(33))], 3)),
        (5, I::Primitive(11, vec![O::Local(4)], 4)),
        (6, I::Primitive(34, vec![O::Local(5)], 5)),
        (7, I::Ret(O::Local(6))),
      ],
    }],
  );
  let word =
    0x89ab_cdefu32.wrapping_mul(17).wrapping_sub(0x0102_0304).rotate_right(33);
  (
    code,
    input(&[V::Word(0x89ab_cdef), V::Word(17)]),
    output(&V::Bytes(blake3::hash(&word.to_le_bytes()).as_bytes().to_vec())),
  )
}

#[test]
fn word_arithmetic_composes_with_byte_conversion_and_guest_hashing() {
  let compiled = compile(PIPELINE, 33, Blake3Backend::PackedWordsV0);
  let (code, args, result) = pipeline();
  check_execution(&compiled, &code, &args, &result);
  let statement = expected_statement(compiled.profile(), &code, &args, &result);
  eprintln!(
    "Crypto pipeline statement {:?}; nu={}, m={}, largest_log_k={}",
    statement
      .limbs()
      .iter()
      .flat_map(|word| [word.lo, word.hi])
      .collect::<Vec<_>>(),
    compiled.nu,
    compiled.params.m,
    compiled.tables.iter().map(|table| table.k().ilog2()).max().unwrap()
  );
  // Independently computed by the pure Lean codec, execution and BLAKE3
  // suite Tests.Ixby.Flock.Words, not by importing the native implementation.
  assert_eq!(
    statement
      .limbs()
      .iter()
      .flat_map(|word| [word.lo, word.hi])
      .collect::<Vec<_>>(),
    [
      14389074313148614759,
      10767949013559195315,
      6352501931959032028,
      13433562327032146821
    ]
  );
}

const CHILD: &str = "IXBY_FLOCK_CRYPTO_EXEC_VERIFY_CHILD";
const TEST: &str = "ixby::exec::crypto_tests::complete_crypto_exec_proofs_verify_in_isolation_and_reject_spliced_word_rows";

fn isolated(expected: ExecStatementDigest, proof: &[u8], mode: &str) -> bool {
  use std::{
    io::Write,
    process::{Command, Stdio},
  };
  let mut child = Command::new(std::env::current_exe().unwrap())
    .args(["--ignored", "--exact", TEST, "--test-threads=1", "--nocapture"])
    .current_dir(std::env::temp_dir())
    .env_clear()
    .env(CHILD, mode)
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
      "isolated crypto Exec verifier rejected: {}",
      String::from_utf8_lossy(&result.stderr)
    );
  }
  result.status.success()
}

#[test]
#[ignore = "all 35 existing crypto opcodes, word/byte/hash composition, isolated verifiers and malicious word wiring"]
fn complete_crypto_exec_proofs_verify_in_isolation_and_reject_spliced_word_rows()
 {
  use std::{io::Read, time::Instant};
  if let Ok(mode) = std::env::var(CHILD) {
    let mut bytes = Vec::new();
    std::io::stdin()
      .take(proof::MAX_BYTES + 33)
      .read_to_end(&mut bytes)
      .unwrap();
    assert!((32..=proof::MAX_BYTES as usize + 32).contains(&bytes.len()));
    // Only verifier-owned fixtures and S+proof; no private program, input,
    // output, reference execution, host hash result, or witness exists here.
    let compiled = match mode.as_str() {
      "full" => setup(),
      "pipeline" => compile(PIPELINE, 33, Blake3Backend::PackedWordsV0),
      "legacy-pipeline" => compile(PIPELINE, 33, Blake3Backend::LegacyOptionF),
      _ => panic!("unapproved verifier fixture"),
    };
    compiled
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
    assert!(isolated(expected, &bytes, "full"), "crypto case {index}");
    eprintln!(
      "Crypto Exec case {index}/49: {} proof bytes, prove {:.3}s, fresh verify {:.3}s",
      bytes.len(),
      proving.as_secs_f64(),
      start.elapsed().as_secs_f64()
    );
    assert_eq!(identity, compiled.identities());
    if index == 0 {
      let old = byte_tests::setup();
      assert!(old.verify(expected, &bytes).is_err());
      let mut renamed = bytes.clone();
      renamed[8..40].copy_from_slice(&old.identities().digest());
      assert!(old.verify(expected, &renamed).is_err());
      let reduced = PrimitiveSet::with_crypto(
        &PrimitiveSet::crypto()
          .opcodes()
          .filter(|op| *op != 2)
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
      renamed[8..40].copy_from_slice(&other.identities().digest());
      assert!(other.verify(expected, &renamed).is_err());
      let mut wrong = result.clone();
      *wrong.last_mut().unwrap() ^= 1;
      assert!(
        compiled
          .verify(
            expected_statement(compiled.profile(), &code, &args, &wrong),
            &bytes
          )
          .is_err()
      );
    }
  }
  let (code, args, result) =
    operation(6, &[V::Word(0x89ab_cdef), V::Word(33)], &V::Word(0));
  let expected = expected_statement(compiled.profile(), &code, &args, &result);
  for opcode_splice in [false, true] {
    let bytes =
      spliced_word_proof(&compiled, expected, &code, &args, opcode_splice);
    assert!(
      !isolated(expected, &bytes, "full"),
      "locally valid word splice must fail wiring"
    );
  }
  let (code, args, result) = pipeline();
  for (backend, mode) in [
    (Blake3Backend::PackedWordsV0, "pipeline"),
    (Blake3Backend::LegacyOptionF, "legacy-pipeline"),
  ] {
    let pipeline = compile(PIPELINE, 33, backend);
    let expected =
      expected_statement(pipeline.profile(), &code, &args, &result);
    let bytes = pipeline.prove(expected, &code, &args).unwrap();
    assert!(isolated(expected, &bytes, mode));
    eprintln!(
      "Crypto {mode}: {} proof bytes; setup={}",
      bytes.len(),
      blake3::Hash::from_bytes(pipeline.identities().digest()).to_hex()
    );
    if backend == Blake3Backend::LegacyOptionF {
      let packed = compile(PIPELINE, 33, Blake3Backend::PackedWordsV0);
      assert_ne!(packed.identities(), pipeline.identities());
      assert!(packed.verify(expected, &bytes).is_err());
      let mut renamed = bytes;
      renamed[8..40].copy_from_slice(&packed.identities().digest());
      assert!(packed.verify(expected, &renamed).is_err());
    }
  }
}

fn spliced_word_proof(
  compiled: &CompiledExec,
  expected: ExecStatementDigest,
  code: &[u8],
  args: &[u8],
  opcode_splice: bool,
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
  let gate = &compiled.machine.primitive_gate;
  let slot = compiled.machine.primitive_slots.prepare;
  let index = compiled.shape.registry_slot(slot);
  let mut rows = witness.rows::<PrimitivePrepareGate>(slot).to_vec();
  let mut forged = rows[0].inputs().to_vec();
  if opcode_splice {
    forged[1].lo ^= 14u64 << 32;
  }
  // shl -> rotr
  else {
    forged[5].lo ^= 32;
  } // shift count 33 -> 1
  let mut result = Vec::new();
  rows[0] = gate.eval(&forged, &(), &mut result);
  assert_eq!(result[7], F128::ZERO); // Fully recomputed locally valid row.
  assert_ne!(result[1], F128::ZERO);
  drivers[index] = UnionSlotProverInput::in_place(
    move |dst| gate.generate_witness_into(&rows, dst),
    compiled.tables[index].csc_lincheck_circuit(),
  );
  compiled.prove_rows(&public, drivers).unwrap()
}
