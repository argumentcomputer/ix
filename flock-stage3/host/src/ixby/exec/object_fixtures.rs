use super::*;
use crate::ixby::{
  control::ControlCapacities,
  decode::{
    InputCapacities, ProgramCapacities,
    test_support::{
      CtorId, FunctionImage as F, Instruction as I, Operand as O, Value as V,
      input, object_program, output,
    },
  },
};

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
  let bytes = ByteCapacity::new(33).unwrap();
  let objects = ObjectCapacity::new(2, 3, 7).unwrap();
  compile_exec_object_profile(
    SemanticProfile::objects(CAPACITY, bytes, objects).unwrap(),
    CAPACITY,
    bytes,
    objects,
    PrimitiveSet::crypto(),
    Blake3Backend::PackedWordsV0,
  )
  .unwrap()
}
fn empty_id() -> CtorId {
  CtorId { block: [0x11; 32], member: u32::MAX, tag: 0x8000_0000 }
}
fn pair_id() -> CtorId {
  CtorId { block: [0x91; 32], member: u32::MAX, tag: 0x8000_0000 }
}
fn constructors() -> Vec<(CtorId, u32)> {
  vec![(empty_id(), 0), (pair_id(), 2)]
}
fn empty() -> V {
  V::Ctor(empty_id(), vec![])
}
fn pair(a: V, b: V) -> V {
  V::Ctor(pair_id(), vec![a, b])
}
fn example(
  functions: Vec<F>,
  args: &[V],
  result: V,
) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
  (object_program(0, &constructors(), &functions), input(args), output(&result))
}
pub(super) fn cases() -> Vec<(Vec<u8>, Vec<u8>, Vec<u8>)> {
  let bytes = V::Bytes((0..33).map(|i| (i * 73 + 19) as u8).collect());
  let nested = pair(pair(V::Word(11), V::Word(22)), V::Erased);
  let mut cases = vec![
    example(
      vec![F {
        arity: 0,
        entry: 0,
        blocks: vec![(0, I::Construct(0, vec![], 1)), (1, I::Ret(O::Local(0)))],
      }],
      &[],
      empty(),
    ),
    example(
      vec![F {
        arity: 2,
        entry: 0,
        blocks: vec![
          (2, I::Construct(1, vec![O::Local(0), O::Local(1)], 1)),
          (3, I::Ret(O::Local(2))),
        ],
      }],
      &[bytes.clone(), V::Word(17)],
      pair(bytes.clone(), V::Word(17)),
    ),
    example(
      vec![F { arity: 1, entry: 0, blocks: vec![(1, I::Ret(O::Local(0)))] }],
      std::slice::from_ref(&nested),
      nested.clone(),
    ),
    example(
      vec![F {
        arity: 1,
        entry: 0,
        blocks: vec![
          (1, I::Construct(1, vec![O::Local(0), O::Local(0)], 1)),
          (2, I::Ret(O::Local(1))),
        ],
      }],
      &[pair(V::Word(11), V::Word(22))],
      pair(pair(V::Word(11), V::Word(22)), pair(V::Word(11), V::Word(22))),
    ),
  ];
  for (field, result) in [(0, bytes.clone()), (1, V::Ext(17, 19))] {
    cases.push(example(
      vec![F {
        arity: 1,
        entry: 0,
        blocks: vec![
          (1, I::Project(O::Local(0), field, 1)),
          (2, I::Ret(O::Local(1))),
        ],
      }],
      &[pair(bytes.clone(), V::Ext(17, 19))],
      result,
    ));
  }
  let case = F {
    arity: 1,
    entry: 0,
    blocks: vec![
      (1, I::CaseCtor(O::Local(0), vec![(1, 1), (0, 2)])),
      (3, I::Ret(O::Local(2))),
      (1, I::Ret(O::Literal(V::Word(9)))),
    ],
  };
  cases.push(example(
    vec![case.clone()],
    &[pair(V::Word(11), V::Word(22))],
    V::Word(22),
  ));
  cases.push(example(vec![case], &[empty()], V::Word(9)));
  let callee = F {
    arity: 2,
    entry: 0,
    blocks: vec![
      (2, I::Construct(1, vec![O::Local(1), O::Local(0)], 1)),
      (3, I::Ret(O::Local(2))),
    ],
  };
  for tail in [false, true] {
    let blocks = if tail {
      vec![(2, I::Tail(Some(1), vec![O::Local(0), O::Local(1)]))]
    } else {
      vec![
        (2, I::Call(Some(1), vec![O::Local(0), O::Local(1)], 1)),
        (3, I::Ret(O::Local(2))),
      ]
    };
    cases.push(example(
      vec![F { arity: 2, entry: 0, blocks }, callee.clone()],
      &[bytes.clone(), V::Word(17)],
      pair(V::Word(17), bytes.clone()),
    ));
  }
  // A constructor saved in the caller must survive a call and resume intact.
  cases.push(example(
    vec![
      F {
        arity: 1,
        entry: 0,
        blocks: vec![
          (1, I::Call(Some(1), vec![O::Local(0)], 1)),
          (2, I::Ret(O::Local(0))),
        ],
      },
      F {
        arity: 1,
        entry: 0,
        blocks: vec![(1, I::Copy(O::Local(0), 1)), (2, I::Ret(O::Local(1)))],
      },
    ],
    std::slice::from_ref(&nested),
    nested.clone(),
  ));
  // Project bytes, hash the constrained selection, then return canonical bytes.
  let data: Vec<_> = (0..33).map(|i| (i * 73 + 19) as u8).collect();
  cases.push(example(
    vec![F {
      arity: 1,
      entry: 0,
      blocks: vec![
        (1, I::Project(O::Local(0), 0, 1)),
        (2, I::Primitive(34, vec![O::Local(1)], 2)),
        (3, I::Ret(O::Local(2))),
      ],
    }],
    &[pair(bytes, V::Erased)],
    V::Bytes(blake3::hash(&data).as_bytes().to_vec()),
  ));
  cases.push(example(
    vec![F {
      arity: 1,
      entry: 0,
      blocks: vec![
        (1, I::Project(O::Local(0), u32::MAX, 1)),
        (2, I::Ret(O::Local(1))),
      ],
    }],
    &[V::Erased],
    V::Erased,
  ));
  // Read an object allocated by this very execution, not only an input tree.
  cases.push(example(
    vec![F {
      arity: 2,
      entry: 0,
      blocks: vec![
        (2, I::Construct(1, vec![O::Local(0), O::Local(1)], 1)),
        (3, I::Project(O::Local(2), 1, 2)),
        (4, I::Ret(O::Local(3))),
      ],
    }],
    &[V::Word(11), V::Ext(17, 19)],
    V::Ext(17, 19),
  ));
  cases.push(example(
    vec![F {
      arity: 0,
      entry: 0,
      blocks: vec![
        (
          0,
          I::Construct(
            1,
            vec![O::Literal(V::Word(11)), O::Literal(V::Word(22))],
            1,
          ),
        ),
        (1, I::CaseCtor(O::Local(0), vec![(1, 2)])),
        (3, I::Ret(O::Local(2))),
      ],
    }],
    &[],
    V::Word(22),
  ));
  // The full declaration identity is guest data, not part of backend setup.
  for component in 0..3 {
    let mut id = pair_id();
    match component {
      0 => id.block[31] ^= 0x80,
      1 => id.member ^= 1,
      _ => id.tag ^= 1,
    }
    let value = V::Ctor(id.clone(), vec![V::Word(11), empty()]);
    cases.push((
      object_program(
        0,
        &[(empty_id(), 0), (id, 2)],
        &[F { arity: 1, entry: 0, blocks: vec![(1, I::Ret(O::Local(0)))] }],
      ),
      input(std::slice::from_ref(&value)),
      output(&value),
    ));
  }
  // Tail-recursive traversal consumes zero, one or two constructor cells.
  let walk = F {
    arity: 1,
    entry: 0,
    blocks: vec![
      (1, I::CaseCtor(O::Local(0), vec![(0, 1), (1, 2)])),
      (1, I::Ret(O::Literal(V::Word(42)))),
      (3, I::Tail(None, vec![O::Local(2)])),
    ],
  };
  for value in [
    empty(),
    pair(V::Word(11), empty()),
    pair(V::Word(11), pair(V::Word(22), empty())),
  ] {
    cases.push(example(vec![walk.clone()], &[value], V::Word(42)));
  }
  cases
}
