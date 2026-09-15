use super::*;
use crate::ixby::{
  byte_value::ByteCapacity,
  decode::test_support::{
    FunctionImage as F, Instruction as I, Operand as O, Value as V, advice,
    program,
  },
  nat_value::NatCapacity,
};
fn revision(mut bytes: Vec<u8>) -> Vec<u8> {
  bytes[4] = 1;
  bytes
}
fn setup() -> ProgramDecodeGate {
  ProgramDecodeGate::new(
    3,
    ProgramCapacities { bytes: 160, functions: 1, blocks: 3, operands: 2 },
    ControlCapacities { locals: 3, continuations: 1, arguments: 2 },
    PrimitiveSet::crypto_nat(),
  )
  .unwrap()
  .with_byte_values(ByteDecodeLayout {
    capacity: ByteCapacity::new(17).unwrap(),
    base: 0,
  })
  .unwrap()
  .with_nat_values(NatCapacity::new(9).unwrap())
  .unwrap()
}
fn case() -> F {
  F {
    arity: 1,
    entry: 0,
    blocks: vec![
      (1, I::CaseNat(O::Local(0), 1, 2)),
      (1, I::Ret(O::Literal(V::Nat(vec![])))),
      (2, I::Ret(O::Local(1))),
    ],
  }
}
fn check(gate: &ProgramDecodeGate, r1cs: &BlockR1cs, code: &[u8], good: bool) {
  let input = advice(gate.capacity.bytes, code);
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&input, bits));
  let residual = 128 * (gate.input_count() + gate.decoded_words());
  assert_eq!(bits[residual], !good, "code {code:?}");
  assert!(r1cs.satisfies(&bits));
  bits[residual] ^= true;
  assert!(!r1cs.satisfies(&bits));
}

#[test]
fn nat_program_checks_both_case_targets_arities_and_unreachable_instructions() {
  let gate = setup();
  let r1cs = gate.r1cs();
  let code = revision(program(0, &[case()]));
  check(&gate, &r1cs, &code, true);
  for end in 0..code.len() {
    check(&gate, &r1cs, &code[..end], false);
  }
  for (zero, successor) in
    [(2, 1), (3, 2), (1, 3), (1, u32::MAX), (u32::MAX, 2)]
  {
    let mut bad = case();
    bad.blocks[0].1 = I::CaseNat(O::Local(0), zero, successor);
    check(&gate, &r1cs, &revision(program(0, &[bad])), false);
  }
  for (block, locals) in [(1, 2), (2, 1), (2, 3)] {
    let mut bad = case();
    bad.blocks[block].0 = locals;
    check(&gate, &r1cs, &revision(program(0, &[bad])), false);
  }
  for (opcode, args) in [
    (35, vec![O::Local(0)]),
    (42, vec![O::Local(0); 2]),
    (35, vec![O::Local(1); 2]),
  ] {
    let bad = F {
      arity: 1,
      entry: 0,
      blocks: vec![
        (1, I::Ret(O::Local(0))),
        (1, I::Primitive(opcode, args, 2)),
        (2, I::Ret(O::Local(1))),
      ],
    };
    check(&gate, &r1cs, &revision(program(0, &[bad])), false);
  }
}

#[test]
fn nat_program_checks_all_seven_opcodes_canonical_literals_and_revision_separation()
 {
  let gate = setup();
  let r1cs = gate.r1cs();
  for opcode in 35..42 {
    let f = F {
      arity: 1,
      entry: 0,
      blocks: vec![
        (
          1,
          I::Primitive(
            opcode,
            vec![O::Local(0), O::Literal(V::Nat(vec![255, 1]))],
            1,
          ),
        ),
        (2, I::Ret(O::Local(1))),
      ],
    };
    check(&gate, &r1cs, &revision(program(0, &[f])), true);
  }
  for data in [vec![0], vec![1, 0], vec![0, 2], vec![1, 1, 1]] {
    let bad = F {
      arity: 1,
      entry: 0,
      blocks: vec![
        (1, I::Ret(O::Local(0))),
        (0, I::Ret(O::Literal(V::Nat(data)))),
      ],
    };
    check(&gate, &r1cs, &revision(program(0, &[bad])), false);
  }
  let code = revision(program(0, &[case()]));
  let mut bad = code.clone();
  bad[4] = 0;
  check(&gate, &r1cs, &bad, false);
  let mut old = setup();
  old.nat_capacity = None;
  old.primitives = PrimitiveSet::crypto();
  old.plan = Arc::new(OnceLock::new());
  check(&old, &old.r1cs(), &bad, false);
  let input = advice(gate.capacity.bytes, &code);
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&input, bits));
  for word in 0..gate.output_count() {
    for bit in [0, 31, 32, 63, 64, 127] {
      let column = 128 * (gate.input_count() + word) + bit;
      bits[column] ^= true;
      assert!(!r1cs.satisfies(&bits));
      bits[column] ^= true;
    }
  }
}
