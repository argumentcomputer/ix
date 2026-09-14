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
    functions: 3,
    blocks: 3,
    operands: 2,
  },
  control: ControlCapacities { locals: 4, continuations: 3, arguments: 2 },
  input: InputCapacities { bytes: 192, values: 2 },
  output_bytes: 192,
  steps: 12,
};
pub(super) fn setup() -> CompiledExec {
  let bytes = ByteCapacity::new(33).unwrap();
  let objects = ObjectCapacity::new(2, 3, 7).unwrap();
  compile_exec_application_profile(
    SemanticProfile::objects(CAPACITY, bytes, objects).unwrap(),
    CAPACITY,
    (bytes, objects, None),
    PrimitiveSet::crypto(),
    Blake3Backend::PackedWordsV0,
  )
  .unwrap()
}
pub(super) fn ctor_id() -> CtorId {
  CtorId { block: [0x91; 32], member: u32::MAX, tag: 0x8000_0000 }
}
pub(super) fn pair(a: V, b: V) -> V {
  V::Ctor(ctor_id(), vec![a, b])
}
pub(super) fn example(
  functions: Vec<F>,
  args: &[V],
  result: V,
) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
  (
    object_program(0, &[(ctor_id(), 2)], &functions),
    input(args),
    output(&result),
  )
}
pub(super) fn word(n: u32) -> O {
  O::Literal(V::Word(n))
}
pub(super) fn function(arity: u32, blocks: Vec<(u32, I)>) -> F {
  F { arity, entry: 0, blocks }
}
pub(super) fn identity(arity: u32, index: u32) -> F {
  function(arity, vec![(arity, I::Ret(O::Local(index)))])
}
pub(super) fn cases() -> Vec<(Vec<u8>, Vec<u8>, Vec<u8>)> {
  let add = function(
    2,
    vec![
      (2, I::Primitive(0, vec![O::Local(0), O::Local(1)], 1)),
      (3, I::Ret(O::Local(2))),
    ],
  );
  let mut cases = vec![
    example(
      vec![
        function(
          0,
          vec![(0, I::Closure(1, vec![word(11)], 1)), (1, I::Ret(O::Local(0)))],
        ),
        identity(2, 1),
      ],
      &[],
      V::Pap(1, vec![V::Word(11)]),
    ),
    example(
      vec![
        function(
          0,
          vec![(0, I::Closure(1, vec![], 1)), (1, I::Ret(O::Local(0)))],
        ),
        identity(1, 0),
      ],
      &[],
      V::Pap(1, vec![]),
    ),
  ];
  // Empty application is identity for every value, even non-functions.
  for value in [
    V::Word(42),
    V::Erased,
    pair(V::Word(11), V::Word(22)),
    V::Pap(1, vec![V::Word(11)]),
    V::Bytes(vec![0, 255]),
  ] {
    cases.push(example(
      vec![
        function(1, vec![(1, I::TailApply(O::Local(0), vec![]))]),
        identity(2, 1),
      ],
      std::slice::from_ref(&value),
      value.clone(),
    ));
  }
  cases.push(example(
    vec![function(
      0,
      vec![(0, I::TailApply(O::Literal(V::Erased), vec![word(11), word(22)]))],
    )],
    &[],
    V::Erased,
  ));
  cases.push(example(
    vec![
      function(1, vec![(1, I::TailApply(O::Local(0), vec![word(11)]))]),
      identity(2, 1),
    ],
    &[V::Pap(1, vec![])],
    V::Pap(1, vec![V::Word(11)]),
  ));
  cases.push(example(
    vec![
      function(1, vec![(1, I::TailApply(O::Local(0), vec![word(42)]))]),
      identity(1, 0),
    ],
    &[V::Pap(1, vec![])],
    V::Word(42),
  ));
  cases.push(example(
    vec![
      function(1, vec![(1, I::TailApply(O::Local(0), vec![word(31)]))]),
      add.clone(),
    ],
    &[V::Pap(1, vec![V::Word(11)])],
    V::Word(42),
  ));
  cases.push(example(
    vec![
      function(
        1,
        vec![
          (1, I::Apply(O::Local(0), vec![word(30)], 1)),
          (2, I::Primitive(0, vec![O::Local(1), word(1)], 2)),
          (3, I::Ret(O::Local(2))),
        ],
      ),
      add.clone(),
    ],
    &[V::Pap(1, vec![V::Word(11)])],
    V::Word(42),
  ));
  for tail in [false, true] {
    let mut blocks = vec![(0, I::Closure(1, vec![word(11)], 1))];
    blocks.extend(if tail {
      vec![(1, I::TailApply(O::Local(0), vec![word(31)]))]
    } else {
      vec![
        (1, I::Apply(O::Local(0), vec![word(31)], 2)),
        (2, I::Ret(O::Local(1))),
      ]
    });
    cases.push(example(
      vec![function(0, blocks), add.clone()],
      &[],
      V::Word(42),
    ));
  }
  // The apply-rest continuation must run before the outer let's resume frame.
  for tail in [false, true] {
    let blocks = if tail {
      vec![(1, I::TailApply(O::Local(0), vec![word(11), word(22)]))]
    } else {
      vec![
        (1, I::Apply(O::Local(0), vec![word(11), word(22)], 1)),
        (2, I::Ret(O::Local(1))),
      ]
    };
    cases.push(example(
      vec![
        function(1, blocks),
        function(
          1,
          vec![(1, I::Closure(2, vec![], 1)), (2, I::Ret(O::Local(1)))],
        ),
        identity(1, 0),
      ],
      &[V::Pap(1, vec![])],
      V::Word(22),
    ));
  }
  // A direct call returns a PAP; over-applying its erased result remains erased.
  cases.push(example(
    vec![
      function(
        0,
        vec![
          (0, I::Call(Some(1), vec![], 1)),
          (1, I::TailApply(O::Local(0), vec![word(11), word(22)])),
        ],
      ),
      function(
        0,
        vec![(0, I::Closure(2, vec![], 1)), (1, I::Ret(O::Local(0)))],
      ),
      function(1, vec![(1, I::Ret(O::Literal(V::Erased)))]),
    ],
    &[],
    V::Erased,
  ));
  cases.push(example(
    vec![
      function(
        1,
        vec![
          (1, I::Project(O::Local(0), 0, 1)),
          (2, I::TailApply(O::Local(1), vec![word(31)])),
        ],
      ),
      add,
    ],
    &[pair(V::Pap(1, vec![V::Word(11)]), V::Erased)],
    V::Word(42),
  ));
  for captured in
    [V::Pap(2, vec![]), pair(V::Word(11), V::Erased), V::Bytes(vec![3, 2, 1])]
  {
    cases.push(example(
      vec![
        function(1, vec![(1, I::TailApply(O::Local(0), vec![word(0)]))]),
        identity(2, 0),
        identity(1, 0),
      ],
      &[V::Pap(1, vec![captured.clone()])],
      captured,
    ));
  }
  let data = vec![3, 2, 1];
  cases.push(example(
    vec![
      function(1, vec![(1, I::TailApply(O::Local(0), vec![word(0)]))]),
      function(
        2,
        vec![
          (2, I::Primitive(34, vec![O::Local(0)], 1)),
          (3, I::Ret(O::Local(2))),
        ],
      ),
    ],
    &[V::Pap(1, vec![V::Bytes(data.clone())])],
    V::Bytes(blake3::hash(&data).as_bytes().to_vec()),
  ));
  // Runtime constructors may capture previously allocated PAPs.
  cases.push(example(
    vec![
      function(
        0,
        vec![
          (0, I::Closure(1, vec![], 1)),
          (1, I::Construct(0, vec![O::Local(0), O::Local(0)], 2)),
          (2, I::Ret(O::Local(1))),
        ],
      ),
      identity(1, 0),
    ],
    &[],
    pair(V::Pap(1, vec![]), V::Pap(1, vec![])),
  ));
  // Runtime PAPs can capture constructor values, and retain oldest-first order.
  cases.push(example(
    vec![
      function(
        2,
        vec![
          (2, I::Closure(1, vec![O::Local(0)], 1)),
          (3, I::Ret(O::Local(2))),
        ],
      ),
      identity(2, 0),
    ],
    &[pair(V::Word(11), V::Erased), V::Word(99)],
    V::Pap(1, vec![pair(V::Word(11), V::Erased)]),
  ));
  let literal = V::Bytes(vec![0x80, 0x03, 0xff]);
  cases.push(example(
    vec![function(
      0,
      vec![(0, I::TailApply(O::Literal(literal.clone()), vec![]))],
    )],
    &[],
    literal,
  ));
  let subtract = function(
    2,
    vec![
      (2, I::Primitive(1, vec![O::Local(0), O::Local(1)], 1)),
      (3, I::Ret(O::Local(2))),
    ],
  );
  cases.push(example(
    vec![
      function(1, vec![(1, I::TailApply(O::Local(0), vec![word(9)]))]),
      subtract,
    ],
    &[V::Pap(1, vec![V::Word(41)])],
    V::Word(32),
  ));
  // Repeated applications retain capture order and make progress toward saturation.
  cases.push(example(
    vec![
      function(
        1,
        vec![
          (1, I::Apply(O::Local(0), vec![word(11)], 1)),
          (2, I::TailApply(O::Local(1), vec![word(22)])),
        ],
      ),
      identity(2, 0),
    ],
    &[V::Pap(1, vec![])],
    V::Word(11),
  ));
  cases
}
