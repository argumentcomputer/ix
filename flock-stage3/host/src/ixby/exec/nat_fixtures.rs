use super::*;
use crate::ixby::{
  control::ControlCapacities,
  decode::{
    InputCapacities, ProgramCapacities,
    test_support::{
      CtorId, FunctionImage as F, Instruction as I, Operand as O, Value as V,
      input, object_program, output, program,
    },
  },
};
use num_bigint::BigUint;

pub(super) const CAPACITY: MachineCapacities = MachineCapacities {
  program: ProgramCapacities {
    bytes: 256,
    functions: 2,
    blocks: 3,
    operands: 2,
  },
  control: ControlCapacities { locals: 4, continuations: 2, arguments: 2 },
  input: InputCapacities { bytes: 192, values: 2 },
  output_bytes: 192,
  steps: 8,
};

pub(super) fn setup() -> CompiledExec {
  setup_with_bits(192)
}
pub(super) fn setup_with_bits(bits: usize) -> CompiledExec {
  let bytes = ByteCapacity::new(33).unwrap();
  let objects = ObjectCapacity::new(2, 3, 7).unwrap();
  let nats = NatCapacity::new(bits).unwrap();
  compile_exec_nat_profile(
    SemanticProfile::nat(CAPACITY, bytes, Some(objects), nats).unwrap(),
    CAPACITY,
    (bytes, Some(objects), nats),
    PrimitiveSet::crypto_nat(),
    Blake3Backend::PackedWordsV0,
  )
  .unwrap()
}
pub(super) fn revision(mut bytes: Vec<u8>) -> Vec<u8> {
  bytes[4..8].copy_from_slice(&1u32.to_le_bytes());
  bytes
}
pub(super) fn nat(value: impl Into<BigUint>) -> V {
  let mut bytes = value.into().to_bytes_le();
  while bytes.last() == Some(&0) {
    bytes.pop();
  }
  V::Nat(bytes)
}
fn tuple(
  code: Vec<u8>,
  values: &[V],
  result: &V,
) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
  (revision(code), revision(input(values)), revision(output(result)))
}
pub(super) fn operation(
  opcode: u8,
  args: &[V],
  result: &V,
) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
  let arity = args.len() as u32;
  tuple(
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
    args,
    result,
  )
}
pub(super) fn cases() -> Vec<(Vec<u8>, Vec<u8>, Vec<u8>)> {
  let a: BigUint = (BigUint::from(1u32) << 160usize)
    + (BigUint::from(1u32) << 64usize)
    + 137u32;
  let b: BigUint = (BigUint::from(1u32) << 79usize) + 3u32;
  let small: BigUint = (BigUint::from(1u32) << 95usize) + 7u32;
  let values = [nat(a.clone()), nat(b.clone())];
  let mut cases = vec![
    operation(35, &values, &nat(&a + &b)),
    operation(36, &values, &nat(&a - &b)),
    operation(37, &[nat(small.clone()), nat(b.clone())], &nat(&small * &b)),
    operation(38, &values, &nat(&a / &b)),
    operation(39, &values, &nat(&a % &b)),
    operation(40, &values, &V::Bool(0)),
    operation(41, &values, &V::Bool(0)),
    operation(36, &[nat(b.clone()), nat(a.clone())], &nat(0u32)),
    operation(38, &[nat(a.clone()), nat(0u32)], &nat(0u32)),
    operation(39, &[nat(a.clone()), nat(0u32)], &nat(a.clone())),
    operation(40, &[nat(a.clone()), nat(a.clone())], &V::Bool(1)),
    operation(41, &[nat(b.clone()), nat(a.clone())], &V::Bool(1)),
    operation(0, &[V::Word(u32::MAX), V::Word(1)], &V::Word(0)),
    operation(
      34,
      &[V::Bytes(b"nat and bytes stay distinct".to_vec())],
      &V::Bytes(
        blake3::hash(b"nat and bytes stay distinct").as_bytes().to_vec(),
      ),
    ),
  ];
  for value in [nat(0u32), nat(1u32), nat(a.clone())] {
    cases.push(tuple(
      program(
        0,
        &[F { arity: 1, entry: 0, blocks: vec![(1, I::Ret(O::Local(0)))] }],
      ),
      std::slice::from_ref(&value),
      &value,
    ));
    cases.push(tuple(
      program(
        0,
        &[F {
          arity: 0,
          entry: 0,
          blocks: vec![(0, I::Ret(O::Literal(value.clone())))],
        }],
      ),
      &[],
      &value,
    ));
  }
  for value in [BigUint::from(0u32), BigUint::from(1u32), a.clone()] {
    let result =
      if value == BigUint::from(0u32) { nat(0u32) } else { nat(&value - 1u32) };
    cases.push(tuple(
      program(
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
      ),
      &[nat(value)],
      &result,
    ));
  }
  let id = CtorId { block: [0xb7; 32], member: u32::MAX, tag: 0x8000_0000 };
  let object =
    V::Ctor(id.clone(), vec![nat(a.clone()), V::Bytes(vec![1, 2, 3])]);
  cases.push(tuple(
    object_program(
      0,
      &[(id.clone(), 2)],
      &[F { arity: 1, entry: 0, blocks: vec![(1, I::Ret(O::Local(0)))] }],
    ),
    std::slice::from_ref(&object),
    &object,
  ));
  cases.push(tuple(
    object_program(
      0,
      &[(id.clone(), 2)],
      &[F {
        arity: 2,
        entry: 0,
        blocks: vec![
          (2, I::Construct(0, vec![O::Local(0), O::Local(1)], 1)),
          (3, I::Project(O::Local(2), 0, 2)),
          (4, I::Ret(O::Local(3))),
        ],
      }],
    ),
    &[nat(a.clone()), V::Bytes(vec![1, 2, 3])],
    &nat(a.clone()),
  ));
  cases.push(tuple(
    object_program(
      0,
      &[(id, 2)],
      &[F {
        arity: 1,
        entry: 0,
        blocks: vec![
          (1, I::CaseCtor(O::Local(0), vec![(0, 1)])),
          (3, I::Primitive(35, vec![O::Local(1), O::Literal(nat(1u32))], 2)),
          (4, I::Ret(O::Local(3))),
        ],
      }],
    ),
    &[object],
    &nat(&a + 1u32),
  ));
  cases.push(tuple(
    program(
      0,
      &[
        F {
          arity: 1,
          entry: 0,
          blocks: vec![
            (1, I::Call(Some(1), vec![O::Local(0)], 1)),
            (2, I::Ret(O::Local(1))),
          ],
        },
        F {
          arity: 1,
          entry: 0,
          blocks: vec![
            (1, I::Primitive(35, vec![O::Local(0), O::Literal(nat(1u32))], 1)),
            (2, I::Ret(O::Local(1))),
          ],
        },
      ],
    ),
    &[nat(a.clone())],
    &nat(&a + 1u32),
  ));
  // Tail recursion over exact predecessors reuses the same bounded code.
  for value in [0u32, 1, 2] {
    cases.push(tuple(
      program(
        0,
        &[F {
          arity: 1,
          entry: 0,
          blocks: vec![
            (1, I::CaseNat(O::Local(0), 1, 2)),
            (1, I::Ret(O::Local(0))),
            (2, I::Tail(None, vec![O::Local(1)])),
          ],
        }],
      ),
      &[nat(value)],
      &nat(0u32),
    ));
  }
  cases
}
