use aiur::bytecode::{
  Binary, Entry, Function, Instruction as Op, Program, Type, VERSION,
};
use aiur::execute::QueryInput;
use aiur::field::PrimeField;
use aiur::value::{IoType, Value};
use serde_json::json;

fn function(name: &str, registers: usize, code: Vec<Op>) -> Function {
  Function {
    name: name.into(),
    params: vec![Type::Field],
    result: Type::Field,
    registers,
    code,
  }
}
fn program(functions: Vec<Function>, root: usize) -> Program {
  Program {
    version: VERSION,
    modulus: 65_537,
    functions,
    enums: vec![],
    tables: vec![],
    maps: vec![],
    entries: vec![Entry {
      name: "main".into(),
      function: root,
      inputs: vec![IoType::Field],
      output: Some(IoType::Field),
    }],
  }
}
fn fib() -> Function {
  function(
    "fib",
    7,
    vec![
      Op::Branch { tests: vec![(0, 0)], otherwise: 3 },
      Op::Literal { dest: 1, value: 0 },
      Op::Ret { value: vec![1] },
      Op::Branch { tests: vec![(0, 1)], otherwise: 6 },
      Op::Literal { dest: 1, value: 1 },
      Op::Ret { value: vec![1] },
      Op::Literal { dest: 1, value: 1 },
      Op::Binary { dest: 2, operator: Binary::Sub, left: 0, right: 1 },
      Op::Call { function: 0, args: vec![2], dest: vec![3] },
      Op::Binary { dest: 4, operator: Binary::Sub, left: 2, right: 1 },
      Op::Call { function: 0, args: vec![4], dest: vec![5] },
      Op::Binary { dest: 6, operator: Binary::Add, left: 3, right: 5 },
      Op::Ret { value: vec![6] },
    ],
  )
}

#[test]
fn memoized_fibonacci_and_isolated_sessions() {
  let p = program(vec![fib()], 0).check().unwrap();
  let result = p.execute("main", vec![20]).unwrap();
  assert_eq!(result.output, vec![6765]);
  assert_eq!(result.queries.len(), 21);
  assert!(result.instructions < 250);
  assert_eq!(
    result
      .queries
      .get(&QueryInput { function: 0, args: vec![18] })
      .unwrap()
      .multiplicity,
    2
  );
  let again = p.execute("main", vec![20]).unwrap();
  assert_eq!(result.queries, again.queries);
}

#[cfg(feature = "function-profile")]
#[test]
fn function_profile_tracks_recursive_misses_and_cached_calls_without_changing_records()
 {
  let root = function(
    "root",
    4,
    vec![
      Op::Call { function: 0, args: vec![0], dest: vec![1] },
      Op::Call { function: 0, args: vec![0], dest: vec![2] },
      Op::Binary { dest: 3, operator: Binary::Add, left: 1, right: 2 },
      Op::Ret { value: vec![3] },
    ],
  );
  let p = program(vec![fib(), root], 1).check().unwrap();
  let hints = p.prepare_hints(&[]).unwrap();
  let normal = hints.execute("main", vec![20]).unwrap();
  let mut profile = aiur::function_profile::FunctionProfiler::new(2);
  let measured =
    hints.execute_profiled("main", vec![20], &mut profile).unwrap();
  assert_eq!(measured.output, normal.output);
  assert_eq!(measured.queries, normal.queries);
  assert_eq!(measured.instructions, normal.instructions);
  assert!(profile.is_complete());
  let fib = &profile.functions[0];
  let root = &profile.functions[1];
  assert_eq!((fib.calls, fib.cache_hits), (40, 19));
  assert_eq!((root.calls, root.cache_hits), (1, 0));
  assert_eq!(root.inclusive_ns, root.self_ns + fib.self_ns);
  assert!(fib.inclusive_ns >= fib.self_ns);
  assert!(fib.cached_ns <= fib.self_ns);
}

#[test]
fn constant_division_respects_joins_and_register_overwrites() {
  let joined = function(
    "joined",
    3,
    vec![
      Op::Literal { dest: 1, value: 3 },
      Op::Branch { tests: vec![(0, 15)], otherwise: 4 },
      Op::Literal { dest: 1, value: 5 },
      Op::Jump { target: 4 },
      Op::Binary { dest: 2, operator: Binary::Div, left: 0, right: 1 },
      Op::Ret { value: vec![2] },
    ],
  );
  let mut p = program(vec![joined], 0);
  p.modulus = 97;
  let p = p.check().unwrap();
  assert_eq!(p.execute("main", vec![15]).unwrap().output, [3]);
  assert_eq!(p.execute("main", vec![9]).unwrap().output, [3]);

  let overwritten = function(
    "overwritten",
    3,
    vec![
      Op::Literal { dest: 1, value: 3 },
      Op::Binary { dest: 1, operator: Binary::Add, left: 0, right: 1 },
      Op::Binary { dest: 2, operator: Binary::Div, left: 0, right: 1 },
      Op::Ret { value: vec![2] },
    ],
  );
  let mut p = program(vec![overwritten], 0);
  p.modulus = 97;
  assert_eq!(p.check().unwrap().execute("main", vec![3]).unwrap().output, [49]);
}

#[test]
fn copies_read_all_sources_before_writing_destinations() {
  let swap = function(
    "swap",
    2,
    vec![
      Op::Literal { dest: 1, value: 7 },
      Op::Copy { dest: vec![0, 1], source: vec![1, 0] },
      Op::Binary { dest: 0, operator: Binary::Sub, left: 0, right: 1 },
      Op::Ret { value: vec![0] },
    ],
  );
  let mut p = program(vec![swap], 0);
  p.modulus = 97;
  assert_eq!(
    p.check().unwrap().execute("main", vec![13]).unwrap().output,
    [91]
  );
}

#[test]
fn return_folding_preserves_simultaneous_copies_joins_and_instruction_counts() {
  let mut f = function(
    "tail",
    3,
    vec![
      Op::Literal { dest: 1, value: 7 },
      Op::Branch { tests: vec![(0, 0)], otherwise: 4 },
      Op::Copy { dest: vec![0, 1], source: vec![1, 0] },
      Op::Jump { target: 5 },
      // Repeated destinations use the last source, read before any write.
      Op::Copy { dest: vec![1, 1], source: vec![1, 0] },
      Op::Copy { dest: vec![2], source: vec![0] },
      Op::Copy { dest: vec![0, 1], source: vec![1, 2] },
      Op::Guard { tests: vec![], message: "unused".into() },
      Op::Ret { value: vec![0, 1] },
      // Unreachable malformed operations must not crash the linker.
      Op::Store {
        r#type: Type::Enum { name: "unknown".into() },
        value: vec![],
        dest: 999,
      },
      Op::Copy { dest: vec![0], source: vec![] },
      Op::Ret { value: vec![0] },
    ],
  );
  f.result = Type::Tuple { items: vec![Type::Field, Type::Field] };
  let mut p = program(vec![f], 0);
  p.entries[0].output = None;
  let p = p.check().unwrap();
  let zero = p.execute("main", vec![0]).unwrap();
  assert_eq!(zero.output, [0, 7]);
  assert_eq!(zero.instructions, 8);
  let other = p.execute("main", vec![13]).unwrap();
  assert_eq!(other.output, [13, 13]);
  assert_eq!(other.instructions, 7);
}

#[test]
fn distinct_entries_into_a_skipped_prefix_keep_their_instruction_counts() {
  let f = function(
    "prefix",
    2,
    vec![
      Op::Branch { tests: vec![(0, 0)], otherwise: 3 },
      Op::Guard { tests: vec![], message: "skipped".into() },
      Op::Guard { tests: vec![], message: "skipped".into() },
      Op::Neg { dest: 1, source: 0 },
      Op::Guard { tests: vec![], message: "return suffix".into() },
      Op::Ret { value: vec![1] },
    ],
  );
  let p = program(vec![f], 0).check().unwrap();
  let zero = p.execute("main", vec![0]).unwrap();
  assert_eq!(zero.output, [0]);
  assert_eq!(zero.instructions, 6);
  let other = p.execute("main", vec![1]).unwrap();
  assert_eq!(other.output, [65_536]);
  assert_eq!(other.instructions, 4);
}

#[test]
fn folded_return_still_checks_enum_tags_and_padding_at_the_original_pc() {
  use aiur::bytecode::{Constructor, Enum};
  let mut f = function(
    "bad_result",
    4,
    vec![
      Op::Literal { dest: 1, value: 7 },
      Op::Copy { dest: vec![2, 3], source: vec![0, 1] },
      Op::Jump { target: 3 },
      Op::Ret { value: vec![2, 3] },
    ],
  );
  f.result = Type::Enum { name: "Maybe".into() };
  let mut p = program(vec![f], 0);
  p.entries[0].output = None;
  p.enums = vec![Enum {
    name: "Maybe".into(),
    constructors: vec![
      Constructor { name: "None".into(), fields: vec![] },
      Constructor { name: "Some".into(), fields: vec![Type::Field] },
    ],
  }];
  let p = p.check().unwrap();
  for (tag, message) in [(2, "invalid enum tag"), (0, "nonzero enum padding")] {
    let error = p.execute("main", vec![tag]).unwrap_err();
    assert_eq!(error.instruction, 3);
    assert_eq!(error.message, message);
  }
  assert_eq!(p.execute("main", vec![1]).unwrap().output, [1, 7]);
}

#[test]
fn hits_do_not_reexecute_callees_and_counts_do_not_wrap_in_the_field() {
  let leaf = function("leaf", 1, vec![Op::Ret { value: vec![0] }]);
  let parent = function(
    "parent",
    2,
    vec![
      Op::Call { function: 0, args: vec![0], dest: vec![1] },
      Op::Call { function: 0, args: vec![0], dest: vec![1] },
      Op::Ret { value: vec![1] },
    ],
  );
  let mut calls =
    vec![Op::Call { function: 1, args: vec![0], dest: vec![1] }; 5];
  calls.push(Op::Ret { value: vec![1] });
  let root = function("root", 2, calls);
  let mut p = program(vec![leaf, parent, root], 2);
  p.modulus = 2;
  let result = p.check().unwrap().execute("main", vec![1]).unwrap();
  assert_eq!(
    result
      .queries
      .get(&QueryInput { function: 2, args: vec![1] })
      .unwrap()
      .multiplicity,
    1
  );
  assert_eq!(
    result
      .queries
      .get(&QueryInput { function: 1, args: vec![1] })
      .unwrap()
      .multiplicity,
    5
  );
  assert_eq!(
    result
      .queries
      .get(&QueryInput { function: 0, args: vec![1] })
      .unwrap()
      .multiplicity,
    2
  );
}

#[test]
fn mutual_recursion_uses_a_vm_stack() {
  fn countdown(name: &str, next: usize) -> Function {
    function(
      name,
      3,
      vec![
        Op::Branch { tests: vec![(0, 0)], otherwise: 2 },
        Op::Ret { value: vec![0] },
        Op::Literal { dest: 1, value: 1 },
        Op::Binary { dest: 2, operator: Binary::Sub, left: 0, right: 1 },
        Op::Call { function: next, args: vec![2], dest: vec![1] },
        Op::Ret { value: vec![1] },
      ],
    )
  }
  let p =
    program(vec![countdown("a", 1), countdown("b", 0)], 0).check().unwrap();
  let result = p.execute("main", vec![20_000]).unwrap();
  assert_eq!(result.output, vec![0]);
  assert_eq!(result.queries.len(), 20_001);
}

#[test]
fn pending_cycle_is_an_error() {
  let p = program(
    vec![function(
      "cycle",
      1,
      vec![
        Op::Call { function: 0, args: vec![0], dest: vec![0] },
        Op::Ret { value: vec![0] },
      ],
    )],
    0,
  )
  .check()
  .unwrap();
  assert!(
    p.execute("main", vec![1])
      .unwrap_err()
      .message
      .contains("already being evaluated")
  );
  assert!(
    p.execute("hidden", vec![1]).unwrap_err().message.contains("unselected")
  );
}

#[test]
fn invalid_control_flow_and_uninitialized_reads_are_rejected() {
  for code in [
    vec![Op::Jump { target: 0 }],
    vec![Op::Ret { value: vec![1] }],
    vec![Op::Literal { dest: 2, value: 3 }, Op::Ret { value: vec![0] }],
    vec![
      Op::Branch { tests: vec![(0, 0)], otherwise: 2 },
      Op::Literal { dest: 1, value: 0 },
      Op::Ret { value: vec![1] },
    ],
  ] {
    assert!(program(vec![function("bad", 2, code)], 0).check().is_err());
  }
}

#[test]
fn inactive_failures_are_not_evaluated() {
  let p = program(
    vec![function(
      "lazy",
      2,
      vec![
        Op::Branch { tests: vec![(0, 0)], otherwise: 2 },
        Op::Ret { value: vec![0] },
        Op::Literal { dest: 1, value: 0 },
        Op::Binary { dest: 1, operator: Binary::Div, left: 0, right: 1 },
        Op::Ret { value: vec![1] },
      ],
    )],
    0,
  )
  .check()
  .unwrap();
  assert_eq!(p.execute("main", vec![0]).unwrap().output, vec![0]);
  assert!(
    p.execute("main", vec![1])
      .unwrap_err()
      .message
      .contains("division by zero")
  );
}

#[test]
fn missing_nondeterministic_data_is_an_error() {
  let p = program(
    vec![function(
      "hint",
      2,
      vec![
        Op::Hint {
          channel: String::new(),
          r#type: Type::Field,
          key_type: Type::Field,
          key: vec![0],
          dest: vec![1],
        },
        Op::Ret { value: vec![1] },
      ],
    )],
    0,
  )
  .check()
  .unwrap();
  let error = p.execute("main", vec![1]).unwrap_err();
  assert_eq!(error.instruction, 0);
  assert!(error.message.contains("missing hint"));
}

#[test]
fn typed_rom_interning_and_capacity() {
  let code = vec![
    Op::Store { r#type: Type::Field, value: vec![0], dest: 1 },
    Op::Store { r#type: Type::Field, value: vec![0], dest: 2 },
    Op::Load { r#type: Type::Field, pointer: 1, dest: vec![2] },
    Op::Ret { value: vec![2] },
  ];
  let p = program(vec![function("rom", 3, code)], 0).check().unwrap();
  let result = p.execute("main", vec![9]).unwrap();
  assert_eq!(result.output, vec![9]);
  assert_eq!(result.memory.len(), 1);
  assert_eq!(result.memory.get(0).unwrap().multiplicity, 3);
  let code = vec![
    Op::Store { r#type: Type::Field, value: vec![0], dest: 1 },
    Op::Literal { dest: 2, value: 1 },
    Op::Store { r#type: Type::Field, value: vec![2], dest: 1 },
    Op::Store { r#type: Type::Tuple { items: vec![] }, value: vec![], dest: 1 },
    Op::Ret { value: vec![0] },
  ];
  let mut p = program(vec![function("full", 3, code)], 0);
  p.modulus = 2;
  // Capacity is per payload width: two width-one cells and one width-zero
  // cell fit in characteristic two.
  let record = p.check().unwrap().execute("main", vec![0]).unwrap();
  assert_eq!(record.memory.len(), 3);
  let pair = Type::Tuple { items: vec![Type::Field; 2] };
  let mut p = program(
    vec![function(
      "full_width",
      3,
      vec![
        Op::Literal { dest: 2, value: 1 },
        Op::Store { r#type: pair.clone(), value: vec![0, 0], dest: 1 },
        Op::Store { r#type: pair.clone(), value: vec![0, 2], dest: 1 },
        Op::Store { r#type: pair, value: vec![2, 0], dest: 1 },
        Op::Ret { value: vec![0] },
      ],
    )],
    0,
  );
  p.modulus = 2;
  assert!(
    p.check()
      .unwrap()
      .execute("main", vec![0])
      .unwrap_err()
      .message
      .contains("capacity")
  );
}

#[test]
fn memory_index_survives_growth_and_shares_equal_width_encodings() {
  let tuple = Type::Tuple { items: vec![Type::Field] };
  let mut code = vec![
    Op::Store { r#type: Type::Field, value: vec![0], dest: 2 },
    Op::Store { r#type: tuple.clone(), value: vec![0], dest: 3 },
  ];
  for value in 1..1024 {
    code.push(Op::Literal { dest: 1, value });
    code.push(Op::Store { r#type: Type::Field, value: vec![1], dest: 4 });
  }
  // Threading the jump must retain the destination store's linked type.
  code.push(Op::Jump { target: code.len() + 1 });
  code.push(Op::Store { r#type: Type::Field, value: vec![0], dest: 4 });
  code.push(Op::AssertEq {
    runtime_check: true,
    left: vec![2],
    right: vec![4],
    message: None,
  });
  code.push(Op::Load { r#type: Type::Field, pointer: 2, dest: vec![0] });
  code.push(Op::Ret { value: vec![0] });
  let checked =
    program(vec![function("growth", 5, code.clone())], 0).check().unwrap();
  let record = checked.execute("main", vec![0]).unwrap();
  assert_eq!(record.output, [0]);
  assert_eq!(record.memory.len(), 1024);
  assert_eq!(record.memory.get(0).unwrap().multiplicity, 4);
  assert_eq!(*record.memory.get(0).unwrap().cell.r#type, Type::Field);
  let load = code.len() - 2;
  code[load] = Op::Load { r#type: tuple, pointer: 2, dest: vec![0] };
  let checked = program(vec![function("same_encoding", 5, code.clone())], 0)
    .check()
    .unwrap();
  assert_eq!(checked.execute("main", vec![0]).unwrap().output, [0]);
  code[load] = Op::Load {
    r#type: Type::Tuple { items: vec![Type::Field; 2] },
    pointer: 2,
    dest: vec![0, 1],
  };
  let checked =
    program(vec![function("absent_width", 5, code)], 0).check().unwrap();
  assert!(
    checked
      .execute("main", vec![0])
      .unwrap_err()
      .message
      .contains("dangling pointer")
  );
}

#[test]
fn structured_io_roundtrips_and_validates_all_enum_padding() {
  let f = PrimeField::new(97).unwrap();
  let unit = IoType::Enum {
    name: "Unit".into(),
    constructors: vec![("Unit".into(), vec![])],
  };
  let ty = IoType::Struct {
    name: "Packet".into(),
    fields: vec![
      ("units".into(), IoType::Array { element: Box::new(unit), length: 3 }),
      (
        "values".into(),
        IoType::Enum {
          name: "Choice".into(),
          constructors: vec![
            ("None".into(), vec![]),
            (
              "Some".into(),
              vec![IoType::Array {
                element: Box::new(IoType::Field),
                length: 2,
              }],
            ),
          ],
        },
      ),
      ("singleton".into(), IoType::Tuple { items: vec![IoType::Field] }),
    ],
  };
  let value = ty.read_json(&json!({"singleton":[4],"values":{"Some":[[7,8]]},"units":[{"Unit":[]},{"Unit":[]},{"Unit":[]}]})).unwrap();
  let flat = ty.flatten(&value, f).unwrap();
  assert_eq!(flat, vec![1, 7, 8, 4]);
  assert_eq!(ty.unflatten(&flat, f).unwrap(), value);
  assert_eq!(
    value.to_string(),
    "Packet { units: [Unit::Unit, Unit::Unit, Unit::Unit], values: Choice::Some([7, 8]), singleton: (4,) }"
  );
  assert!(ty.unflatten(&[2, 0, 0, 4], f).is_err());
  assert!(ty.unflatten(&[0, 1, 0, 4], f).is_err());
  assert!(IoType::Field.flatten(&Value::from(97), f).is_err());
  assert!(
    IoType::Tuple { items: vec![] }
      .flatten(&Value::Array { items: vec![] }, f)
      .is_err()
  );
}
