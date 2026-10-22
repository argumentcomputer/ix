use aiur::bytecode::{
  Constructor, Entry, Enum, Function, Instruction as Op, Program, Type, VERSION,
};
use aiur::execute::QueryInput;
use aiur::hints::HintEntry;
use aiur::value::IoType;

fn function(name: &str, registers: usize, code: Vec<Op>) -> Function {
  Function {
    name: name.into(),
    params: vec![Type::Field],
    result: Type::Field,
    registers,
    code,
  }
}

fn program(functions: Vec<Function>, entry: usize) -> Program {
  Program {
    version: VERSION,
    modulus: 97,
    functions,
    enums: vec![],
    tables: vec![],
    maps: vec![],
    entries: vec![Entry {
      name: "main".into(),
      function: entry,
      inputs: vec![IoType::Field],
      output: None,
    }],
  }
}

fn hint(key: usize, dest: usize) -> Op {
  Op::Hint {
    channel: String::new(),
    r#type: Type::Field,
    key_type: Type::Field,
    key: vec![key],
    dest: vec![dest],
  }
}

fn row(key: u64, output: u64) -> HintEntry {
  HintEntry {
    channel: String::new(),
    r#type: Type::Field,
    key_type: Type::Field,
    key: vec![key],
    output: vec![output],
  }
}

#[test]
fn dynamic_keys_and_cached_queries() {
  let child = function(
    "child",
    2,
    vec![hint(0, 1), hint(1, 1), Op::Ret { value: vec![1] }],
  );
  let parent = function(
    "parent",
    2,
    vec![
      Op::Call { function: 0, args: vec![0], dest: vec![1] },
      Op::Call { function: 0, args: vec![0], dest: vec![1] },
      hint(1, 1),
      Op::Ret { value: vec![1] },
    ],
  );
  let p = program(vec![child, parent], 1).check().unwrap();
  let entries = [row(4, 5), row(5, 6), row(6, 7)];
  let result = p.execute_with_hints("main", vec![4], &entries).unwrap();
  assert_eq!(result.output, vec![7]);
  // Reusing validated advice must not warm the query cache. Each invocation
  // still executes the same instructions and records its own multiplicities.
  let prepared = p.prepare_hints(&entries).unwrap();
  for _ in 0..2 {
    let repeated = prepared.execute("main", vec![4]).unwrap();
    assert_eq!(repeated.output, result.output);
    assert_eq!(repeated.queries, result.queries);
    assert_eq!(repeated.instructions, result.instructions);
  }
  let child =
    &result.queries.get(&QueryInput { function: 0, args: vec![4] }).unwrap();
  assert_eq!(child.multiplicity, 2);
  assert_eq!(child.output, [6]);
  let parent =
    &result.queries.get(&QueryInput { function: 1, args: vec![4] }).unwrap();
  assert_eq!(parent.output, [7]);
  // A fresh session can select different witnesses for the same root query.
  let again = p
    .execute_with_hints("main", vec![4], &[row(4, 5), row(5, 6), row(6, 8)])
    .unwrap();
  assert_eq!(again.output, vec![8]);
  assert!(
    p.execute("main", vec![4]).unwrap_err().message.contains("missing hint")
  );
}

#[test]
fn types_disambiguate_identical_word_encodings() {
  let nominal = |name: &str| Type::Enum { name: name.into() };
  let single = Type::Tuple { items: vec![Type::Field] };
  let signatures = [
    (Type::Field, Type::Field),
    (Type::Field, single),
    (Type::Field, nominal("A")),
    (Type::Field, nominal("B")),
    (nominal("A"), Type::Field),
    (nominal("B"), Type::Field),
  ];
  let mut instructions = signatures
    .iter()
    .enumerate()
    .map(|(i, (result, key))| Op::Hint {
      channel: if i >= 4 { format!("result{i}") } else { String::new() },
      r#type: result.clone(),
      key_type: key.clone(),
      key: vec![0],
      dest: vec![i + 1],
    })
    .collect::<Vec<_>>();
  instructions.push(Op::Ret { value: (1..=6).collect() });
  let mut f = function("typed", 7, instructions);
  f.result = Type::Tuple {
    items: signatures.iter().map(|(result, _)| result.clone()).collect(),
  };
  let mut p = program(vec![f], 0);
  p.enums = ["A", "B"]
    .map(|name| Enum {
      name: name.into(),
      constructors: vec![Constructor {
        name: "Wrap".into(),
        fields: vec![Type::Field],
      }],
    })
    .to_vec();
  let entries = signatures
    .iter()
    .enumerate()
    .map(|(i, (result, key))| HintEntry {
      channel: if i >= 4 { format!("result{i}") } else { String::new() },
      r#type: result.clone(),
      key_type: key.clone(),
      key: vec![7],
      output: vec![i as u64 + 10],
    })
    .collect::<Vec<_>>();
  let result =
    p.check().unwrap().execute_with_hints("main", vec![7], &entries).unwrap();
  assert_eq!(result.output, vec![10, 11, 12, 13, 14, 15]);
}

#[test]
fn repeated_identical_data_is_allowed_but_conflicts_are_errors() {
  let p = program(
    vec![function("hinted", 2, vec![hint(0, 1), Op::Ret { value: vec![1] }])],
    0,
  )
  .check()
  .unwrap();
  let result =
    p.execute_with_hints("main", vec![4], &[row(4, 5), row(4, 5)]).unwrap();
  assert_eq!(result.output, vec![5]);
  assert!(
    p.execute_with_hints("main", vec![4], &[row(4, 5), row(4, 6)])
      .unwrap_err()
      .message
      .contains("conflicting hint entries")
  );
  // Conflict checking also covers data the execution would never request.
  assert!(
    p.execute_with_hints("main", vec![4], &[row(4, 5), row(9, 1), row(9, 2)])
      .unwrap_err()
      .message
      .contains("conflicting hint entries")
  );
}

#[test]
fn inactive_sites_do_not_request_answers() {
  let p = program(
    vec![function(
      "lazy",
      2,
      vec![
        Op::Branch { tests: vec![(0, 0)], otherwise: 2 },
        Op::Ret { value: vec![0] },
        hint(0, 1),
        Op::Ret { value: vec![1] },
      ],
    )],
    0,
  )
  .check()
  .unwrap();
  let result = p.execute("main", vec![0]).unwrap();
  assert_eq!(result.output, [0]);
  let error = p.execute("main", vec![1]).unwrap_err();
  assert_eq!(error.instruction, 2);
  assert_eq!(error.function, "lazy");
}

#[test]
fn skipped_dispatch_preserves_logical_counts_and_hint_sites() {
  let p = program(
    vec![function(
      "threaded",
      2,
      vec![
        Op::Guard { tests: vec![], message: "unreachable".into() },
        Op::Copy { dest: vec![0], source: vec![0] },
        Op::AssertEq {
          runtime_check: true,
          left: vec![0],
          right: vec![0],
          message: None,
        },
        Op::Branch { tests: vec![], otherwise: 6 },
        Op::Jump { target: 6 },
        // Validation permits arbitrary unreachable instructions.
        Op::Literal { dest: usize::MAX, value: u64::MAX },
        hint(0, 1),
        Op::Copy { dest: vec![], source: vec![] },
        Op::Ret { value: vec![1] },
      ],
    )],
    0,
  )
  .check()
  .unwrap();
  let result = p.execute_with_hints("main", vec![4], &[row(4, 5)]).unwrap();
  assert_eq!(result.output, [5]);
  assert_eq!(result.instructions, 8);
  let error = p.execute("main", vec![4]).unwrap_err();
  assert_eq!(error.function, "threaded");
  assert_eq!(error.instruction, 6);
}

#[test]
fn flat_data_validates_nested_tags_padding_fields_widths_and_pointers() {
  let nominal = |name: &str| Type::Enum { name: name.into() };
  let mut p =
    program(vec![function("identity", 1, vec![Op::Ret { value: vec![0] }])], 0);
  p.enums = vec![
    Enum {
      name: "Inner".into(),
      constructors: vec![
        Constructor { name: "None".into(), fields: vec![] },
        Constructor { name: "Some".into(), fields: vec![Type::Field] },
      ],
    },
    Enum {
      name: "Outer".into(),
      constructors: vec![
        Constructor { name: "Empty".into(), fields: vec![] },
        Constructor { name: "Wrap".into(), fields: vec![nominal("Inner")] },
      ],
    },
    Enum {
      name: "HiddenPointer".into(),
      constructors: vec![
        Constructor { name: "Empty".into(), fields: vec![] },
        Constructor {
          name: "Ptr".into(),
          fields: vec![Type::Ptr { target: Box::new(Type::Field) }],
        },
      ],
    },
  ];
  let p = p.check().unwrap();
  let good = HintEntry {
    channel: String::new(),
    r#type: nominal("Outer"),
    key_type: nominal("Outer"),
    key: vec![1, 1, 7],
    output: vec![1, 0, 0],
  };
  p.execute_with_hints("main", vec![0], std::slice::from_ref(&good)).unwrap();
  for (words, expected) in [
    (vec![1, 2, 0], "invalid enum tag"),
    (vec![1, 0, 1], "nonzero enum padding"),
    (vec![0, 1, 0], "nonzero enum padding"),
    (vec![1, 1, 97], "noncanonical"),
    (vec![1, 1], "width"),
  ] {
    for key in [false, true] {
      let mut bad = good.clone();
      if key {
        bad.key = words.clone();
      } else {
        bad.output = words.clone();
      }
      let error = p.execute_with_hints("main", vec![0], &[bad]).unwrap_err();
      assert!(error.message.contains(expected), "{}", error.message);
    }
  }
  let pointer = HintEntry {
    channel: String::new(),
    r#type: nominal("HiddenPointer"),
    key_type: Type::Field,
    key: vec![0],
    output: vec![0, 0],
  };
  assert!(
    p.execute_with_hints("main", vec![0], &[pointer])
      .unwrap_err()
      .message
      .contains("pointers")
  );
  let unknown = HintEntry {
    channel: String::new(),
    r#type: nominal("Unknown"),
    ..row(0, 1)
  };
  assert!(
    p.execute_with_hints("main", vec![0], &[unknown])
      .unwrap_err()
      .message
      .contains("unknown enum")
  );
}

#[test]
fn zero_width_answers_still_have_distinct_nominal_keys() {
  let unit = Type::Enum { name: "Unit".into() };
  let mut f = function(
    "unit",
    1,
    vec![
      Op::Hint {
        channel: String::new(),
        r#type: unit.clone(),
        key_type: unit.clone(),
        key: vec![],
        dest: vec![],
      },
      Op::Ret { value: vec![] },
    ],
  );
  f.result = unit.clone();
  let mut p = program(vec![f], 0);
  p.enums.push(Enum {
    name: "Unit".into(),
    constructors: vec![Constructor { name: "Unit".into(), fields: vec![] }],
  });
  let p = p.check().unwrap();
  let wrong_key = HintEntry {
    channel: String::new(),
    r#type: unit.clone(),
    key_type: Type::Tuple { items: vec![] },
    key: vec![],
    output: vec![],
  };
  assert!(
    p.execute_with_hints("main", vec![0], &[wrong_key])
      .unwrap_err()
      .message
      .contains("missing hint")
  );
  let entry = HintEntry {
    channel: String::new(),
    r#type: unit.clone(),
    key_type: unit,
    key: vec![],
    output: vec![],
  };
  let result = p.execute_with_hints("main", vec![0], &[entry]).unwrap();
  assert!(result.output.is_empty());
  assert_eq!(result.instructions, 2);
}

#[test]
fn code_channels_are_bound_once_and_capture_configuration() {
  use aiur::hints::HintChannels;
  use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
  };
  let named = |channel: &str, key, dest| Op::Hint {
    channel: channel.into(),
    r#type: Type::Field,
    key_type: Type::Field,
    key: vec![key],
    dest: vec![dest],
  };
  let child = function(
    "child",
    3,
    vec![named("plus", 0, 1), named("times", 1, 2), Op::Ret { value: vec![2] }],
  );
  let parent = function(
    "parent",
    2,
    vec![
      Op::Call { function: 0, args: vec![0], dest: vec![1] },
      Op::Call { function: 0, args: vec![0], dest: vec![1] },
      Op::Ret { value: vec![1] },
    ],
  );
  let program = program(vec![child, parent], 1).check().unwrap();
  let calls = Arc::new(AtomicUsize::new(0));
  let prepared = {
    let mut channels = HintChannels::new();
    for (name, offset, scale) in [("plus", 3, 1), ("times", 0, 2)] {
      let calls = calls.clone();
      channels
        .insert(name, Type::Field, Type::Field, move |input, output| {
          calls.fetch_add(1, Ordering::Relaxed);
          output[0] = (input[0] + offset) * scale;
          Ok(())
        })
        .unwrap();
    }
    program.prepare_hint_channels(&[], &channels).unwrap()
    // The registry is dropped: execution only has the bound closures.
  };
  let code = prepared.execute("main", vec![4]).unwrap();
  assert_eq!(code.output, [14]);
  assert_eq!(calls.load(Ordering::Relaxed), 2); // cached child is not called again
  let data = program
    .execute_with_hints(
      "main",
      vec![4],
      &[
        HintEntry { channel: "plus".into(), ..row(4, 7) },
        HintEntry { channel: "times".into(), ..row(7, 14) },
      ],
    )
    .unwrap();
  assert_eq!(code.queries, data.queries);
  assert_eq!(code.instructions, data.instructions);
  assert_eq!(prepared.execute("main", vec![5]).unwrap().output, [16]);
  assert_eq!(calls.load(Ordering::Relaxed), 4);
}

#[test]
fn channel_outputs_remain_untrusted_constants() {
  use aiur::hints::HintChannels;
  let result_type = Type::Enum { name: "Choice".into() };
  let mut function = function(
    "choose",
    3,
    vec![
      Op::Hint {
        channel: "choice".into(),
        r#type: result_type.clone(),
        key_type: Type::Field,
        key: vec![0],
        dest: vec![1, 2],
      },
      Op::Ret { value: vec![1, 2] },
    ],
  );
  function.result = result_type.clone();
  let mut source = program(vec![function], 0);
  source.enums.push(Enum {
    name: "Choice".into(),
    constructors: vec![
      Constructor { name: "None".into(), fields: vec![] },
      Constructor { name: "Some".into(), fields: vec![Type::Field] },
    ],
  });
  let program = source.check().unwrap();
  for (words, error) in [
    ([2, 0], "invalid enum tag"),
    ([0, 1], "nonzero enum padding"),
    ([1, 97], "noncanonical"),
  ] {
    for fixed in [false, true] {
      let mut channels = HintChannels::new();
      if fixed {
        channels
          .insert_fixed::<1, 2>(
            "choice",
            Type::Field,
            result_type.clone(),
            move |_| Ok(words),
          )
          .unwrap();
      } else {
        channels
          .insert("choice", Type::Field, result_type.clone(), move |_, out| {
            out.copy_from_slice(&words);
            Ok(())
          })
          .unwrap();
      }
      assert!(
        program
          .prepare_hint_channels(&[], &channels)
          .unwrap()
          .execute("main", vec![0])
          .unwrap_err()
          .message
          .contains(error)
      );
    }
  }
  let mut wrong = HintChannels::new();
  wrong.insert("choice", Type::Field, Type::Field, |_, _| Ok(())).unwrap();
  assert!(
    program
      .prepare_hint_channels(&[], &wrong)
      .err()
      .unwrap()
      .contains("signature mismatch")
  );
  assert!(
    wrong
      .insert("choice", Type::Field, Type::Field, |_, _| Ok(()))
      .unwrap_err()
      .contains("duplicate")
  );
  let mut pointer = HintChannels::new();
  pointer
    .insert(
      "unused",
      Type::Ptr { target: Box::new(Type::Field) },
      Type::Field,
      |_, _| Ok(()),
    )
    .unwrap();
  assert!(
    program
      .prepare_hint_channels(&[], &pointer)
      .err()
      .unwrap()
      .contains("pointers")
  );
}

#[test]
fn data_channels_are_functions_of_the_constant_key() {
  let p = program(
    vec![function("hinted", 2, vec![hint(0, 1), Op::Ret { value: vec![1] }])],
    0,
  )
  .check()
  .unwrap();
  let entries = [row(4, 5), HintEntry { channel: "other".into(), ..row(4, 6) }];
  assert_eq!(
    p.execute_with_hints("main", vec![4], &entries).unwrap().output,
    [5]
  );
  // The expected result type must not select a different answer to the same
  // channel and Constant; use another channel for that operation instead.
  let conflict =
    HintEntry { r#type: Type::Tuple { items: vec![Type::Field] }, ..row(4, 5) };
  assert!(
    p.prepare_hints(&[row(4, 5), conflict])
      .err()
      .unwrap()
      .contains("conflicting")
  );
}

#[test]
fn fixed_hints_bind_linked_registers_and_preserve_nominal_signatures() {
  use aiur::hints::HintChannels;
  let pair = Type::Tuple { items: vec![Type::Field; 2] };
  let mut f = function(
    "swap",
    4,
    vec![
      Op::Copy { source: vec![0, 1], dest: vec![2, 3] },
      Op::Hint {
        channel: "swap".into(),
        key_type: pair.clone(),
        r#type: pair.clone(),
        key: vec![2, 3],
        dest: vec![0, 1],
      },
      Op::Ret { value: vec![0, 1] },
    ],
  );
  f.params = vec![pair.clone()];
  f.result = pair.clone();
  let mut source = program(vec![f], 0);
  source.entries[0].inputs =
    vec![IoType::Tuple { items: vec![IoType::Field; 2] }];
  let program = source.check().unwrap();
  let mut channels = HintChannels::new();
  channels
    .insert_fixed::<2, 2>("swap", pair.clone(), pair.clone(), |[a, b]| {
      Ok([b, a])
    })
    .unwrap();
  let prepared = program.prepare_hint_channels(&[], &channels).unwrap();
  drop(channels);
  let actual = prepared.execute("main", vec![2, 5]).unwrap();
  let expected = program
    .execute_with_hints(
      "main",
      vec![2, 5],
      &[HintEntry {
        channel: "swap".into(),
        key_type: pair.clone(),
        r#type: pair.clone(),
        key: vec![2, 5],
        output: vec![5, 2],
      }],
    )
    .unwrap();
  assert_eq!(actual.output, [5, 2]);
  assert_eq!(actual.queries, expected.queries);
  assert_eq!(actual.instructions, expected.instructions);
  let mut wrong = HintChannels::new();
  wrong
    .insert_fixed::<1, 2>("swap", pair.clone(), pair.clone(), |[x]| Ok([x, x]))
    .unwrap();
  assert!(
    program
      .prepare_hint_channels(&[], &wrong)
      .err()
      .unwrap()
      .contains("fixed arity")
  );
  let mut wrong = HintChannels::new();
  wrong
    .insert_fixed::<2, 2>("swap", pair.clone(), pair, |_| {
      Err("provider failure".into())
    })
    .unwrap();
  assert!(
    program
      .prepare_hint_channels(&[], &wrong)
      .unwrap()
      .execute("main", vec![2, 5])
      .unwrap_err()
      .message
      .contains("provider failure")
  );
}
