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
    bytes: 256,
    functions: 2,
    blocks: 4,
    operands: 2,
  },
  control: ControlCapacities { locals: 4, continuations: 2, arguments: 2 },
  input: InputCapacities { bytes: 64, values: 2 },
  output_bytes: 64,
  steps: 24,
};

pub(super) fn setup() -> CompiledExec {
  compile_exec_profile(
    SemanticProfile::scalar(CAPACITY).unwrap(),
    CAPACITY,
    PrimitiveSet::scalar(),
  )
  .unwrap()
}

#[test]
fn canonical_profile_and_setup_admission_are_independent_of_guest_artifacts() {
  let profile = SemanticProfile::scalar(CAPACITY).unwrap();
  assert_eq!(
    SemanticProfile::from_bytes(&profile.to_bytes()).unwrap(),
    profile
  );
  for position in [0, 3, 4, 7, 8, 11] {
    let mut bytes = profile.to_bytes();
    bytes[position] ^= 1;
    assert!(SemanticProfile::from_bytes(&bytes).is_err());
  }
  // Parsing revision 1 does not upgrade an approved revision-0 setup.
  let mut nat_v1 = profile.to_bytes();
  nat_v1[4] = 1;
  nat_v1[8] = 1;
  assert!(
    compile_exec_profile(
      SemanticProfile::from_bytes(&nat_v1).unwrap(),
      CAPACITY,
      PrimitiveSet::scalar()
    )
    .is_err()
  );
  nat_v1[40] = 96;
  assert!(
    compile_exec_profile(
      SemanticProfile::from_bytes(&nat_v1).unwrap(),
      CAPACITY,
      PrimitiveSet::scalar()
    )
    .is_err()
  );
  assert!(SemanticProfile::from_bytes(&profile.to_bytes()[..67]).is_err());
  assert!(
    SemanticProfile::from_bytes(
      &[profile.to_bytes().as_slice(), &[0]].concat()
    )
    .is_err()
  );
  for index in 0..14 {
    let mut parameters = profile.parameters();
    parameters[index] += 1;
    if let Ok(profile) = SemanticProfile::new(parameters) {
      assert!(
        compile_exec_profile(profile, CAPACITY, PrimitiveSet::scalar())
          .is_err()
      );
    }
  }
  let first = setup();
  let second = setup();
  assert_eq!(first.identities(), second.identities());
  assert_eq!(
    blake3::Hash::from_bytes(first.identities().digest()).to_hex().as_str(),
    "41163b87f03675917ac93824d8b1c11ab0c489c2fc2e03abece34d11fa3255f7"
  );
  assert_eq!(first.public.outputs(), 2);
  assert_eq!(
    first
      .public
      .words()
      .iter()
      .filter(|word| matches!(word, crate::ixby::io::PublicWord::Output(_)))
      .count(),
    2
  );
  assert_eq!(first.lincheck_circuits().len(), 23);
  assert_eq!(
    first.transcript_domain(),
    [profile::TRANSCRIPT_DOMAIN, first.identities().digest().as_slice()]
      .concat()
  );
  assert!(
    first.verify_for_replay(ExecStatementDigest([0; 32]), &[0; 128]).is_err()
  );
  assert_eq!(
    first.input.private_words(),
    1 + CAPACITY.program.data_words() + 1 + CAPACITY.input.data_words()
  );
  assert_eq!(first.shape.counts.len(), 23);
  eprintln!(
    "Exec census: nu={}, m={}, table rows={:?}",
    first.nu, first.params.m, first.shape.counts
  );
}

#[test]
fn profile_and_expected_statement_match_the_existing_pure_lean_golden() {
  use crate::ixby::commitment::tests::{
    GOLDEN_INPUT, GOLDEN_OUTPUT, GOLDEN_PROFILE, GOLDEN_PROGRAM,
  };
  let profile = SemanticProfile::from_bytes(GOLDEN_PROFILE).unwrap();
  assert_eq!(profile.to_bytes().as_slice(), GOLDEN_PROFILE);
  assert_eq!(
    expected_statement(profile, GOLDEN_PROGRAM, GOLDEN_INPUT, GOLDEN_OUTPUT)
      .limbs(),
    [
      flock_prover::field::F128::new(6407977636521055359, 3463446082552244464),
      flock_prover::field::F128::new(6667175477628965062, 16312016406872336668),
    ]
  );
  // Logical limits in this older codec vector do not match the small native
  // execution capacity. Byte conformance must not silently admit that setup.
  assert!(
    compile_exec_profile(profile, CAPACITY, PrimitiveSet::scalar()).is_err()
  );
}

#[test]
fn canonical_bytes_execute_and_bind_the_expected_full_statement() {
  let compiled = setup();
  let profile = compiled.profile();
  for (code, args, result) in cases() {
    let expected = expected_statement(profile, &code, &args, &result);
    let private = [
      proof::buffer(CAPACITY.program.bytes, &code).unwrap(),
      proof::buffer(CAPACITY.input.bytes, &args).unwrap(),
    ]
    .concat();
    let witness =
      compiled.shape.run(&compiled.input.assign(&private).unwrap(), &[]);
    assert_eq!(
      witness.public,
      compiled.public.instantiate(&expected.limbs()).unwrap()
    );
    assert!(
      compiled.prove(ExecStatementDigest([0; 32]), &code, &args).is_err()
    );
  }
}

pub(super) fn cases() -> Vec<(Vec<u8>, Vec<u8>, Vec<u8>)> {
  let mut cases = crate::ixby::machine::tests::cases();
  let value = |words: [flock_prover::field::F128; 2]| match words[0].lo {
    1 => V::Bool(words[1].lo as u8),
    2 => V::Word(words[1].lo as u32),
    3 => V::Field(words[1].lo),
    4 => V::Ext(words[1].lo, words[1].hi),
    5 => V::Erased,
    _ => panic!("test oracle scalar"),
  };
  for opcode in PrimitiveSet::scalar().opcodes() {
    let (args, result) = crate::ixby::primitive::tests::oracle(
      opcode,
      u32::MAX,
      1,
      0xffff_ffff_0000_0000,
      1,
    );
    let arity = args.len() as u32;
    let code = program(
      0,
      &[F {
        arity,
        entry: 0,
        blocks: vec![
          (arity, I::Primitive(opcode, (0..arity).map(O::Local).collect(), 1)),
          (arity + 1, I::Ret(O::Local(arity))),
        ],
      }],
    );
    cases.push((
      code,
      input(&args.into_iter().map(value).collect::<Vec<_>>()),
      output(&value(result)),
    ));
  }
  cases
}
