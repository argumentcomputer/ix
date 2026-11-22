use aiur::{
  FieldWord, Program,
  bytecode::{Binary, Entry, Function, Instruction as I, Map, Table, Type},
  field::FieldBackend,
  hints::HintChannels,
  value::IoType,
};
use ix_proof_compression::{aiur_backend::Bn254, kzg::Scalar};

fn program(
  inputs: usize,
  outputs: usize,
  registers: usize,
  code: Vec<I<FieldWord>>,
) -> Program<FieldWord> {
  Program {
    version: aiur::bytecode::VERSION,
    modulus: Bn254.modulus(),
    functions: vec![Function {
      name: "main".into(),
      params: vec![Type::Field; inputs],
      result: Type::Tuple { items: vec![Type::Field; outputs] },
      registers,
      code,
    }],
    enums: vec![],
    tables: vec![],
    maps: vec![],
    entries: vec![Entry {
      name: "main".into(),
      function: 0,
      inputs: vec![IoType::Field; inputs],
      output: Some(IoType::Tuple { items: vec![IoType::Field; outputs] }),
    }],
  }
}

fn word(value: Scalar) -> FieldWord {
  Bn254.to_word(value)
}

#[test]
fn canonical_conversion_retains_high_limbs_and_rejects_overflow() {
  let minus_one = Bn254.neg(Bn254.one());
  let high = FieldWord::from_limbs_le([7, 1, 1, 0]);
  let decoded = Bn254.decode_words(&[word(minus_one), high]).unwrap();
  assert_eq!(decoded[0], minus_one);
  assert_eq!(word(decoded[1]), high);
  assert!(Bn254.try_to_u64(decoded[0]).is_err());
  assert!(Bn254.try_to_u64(decoded[1]).is_err());
  assert_eq!(Bn254.try_to_u64(Bn254.from_u64(u64::MAX)).unwrap(), u64::MAX);
  assert!(Bn254.decode_words(&[Bn254.modulus()]).is_err());
  assert!(
    Bn254.decode_words(&[FieldWord::from_limbs_le([u64::MAX; 4])]).is_err()
  );
  assert_eq!(Bn254.from_word(Bn254.modulus()), Bn254.zero());
}

#[test]
fn interpreter_uses_bn254_arithmetic_for_inputs_and_folded_constants() {
  let minus_one = Bn254.neg(Bn254.one());
  let p = program(
    1,
    5,
    9,
    vec![
      I::Literal { dest: 1, value: FieldWord::ONE },
      I::Literal { dest: 2, value: 2.into() },
      I::Literal { dest: 3, value: word(minus_one) },
      I::Binary { dest: 4, operator: Binary::Add, left: 0, right: 1 },
      I::Binary { dest: 5, operator: Binary::Div, left: 1, right: 0 },
      I::Binary { dest: 6, operator: Binary::Div, left: 1, right: 2 },
      I::Binary { dest: 7, operator: Binary::Mul, left: 3, right: 3 },
      I::Binary { dest: 8, operator: Binary::Sub, left: 1, right: 3 },
      I::Ret { value: vec![4, 5, 6, 7, 8] },
    ],
  )
  .check_with(Bn254)
  .unwrap();
  let record = p.execute("main", vec![minus_one]).unwrap();
  assert_eq!(
    record.output,
    vec![
      Bn254.zero(),
      minus_one,
      Bn254.inverse(Bn254.from_u64(2)).unwrap(),
      Bn254.one(),
      Bn254.from_u64(2),
    ]
  );
  assert!(p.execute("main", vec![Bn254.zero()]).is_err());
  assert!(p.output_value("main", &record).is_err());
}

#[test]
fn calls_maps_memory_and_host_hints_keep_distinct_high_limbs() {
  let keys = [
    FieldWord::from_limbs_le([7, 1, 0, 0]),
    FieldWord::from_limbs_le([7, 2, 0, 0]),
  ];
  let values =
    [Bn254.neg(Bn254.one()), Bn254.inverse(Bn254.from_u64(2)).unwrap()];
  let mut source = program(
    1,
    2,
    6,
    vec![
      I::Call { function: 1, args: vec![0], dest: vec![1] },
      I::Call { function: 1, args: vec![0], dest: vec![2] },
      I::Store { r#type: Type::Field, value: vec![2], dest: 3 },
      I::Load { r#type: Type::Field, pointer: 3, dest: vec![4] },
      I::Hint {
        channel: "square".into(),
        r#type: Type::Field,
        key_type: Type::Field,
        key: vec![4],
        dest: vec![5],
      },
      I::Ret { value: vec![1, 5] },
    ],
  );
  source.tables = vec![
    Table {
      name: "keys".into(),
      r#type: Type::Tuple { items: vec![Type::Field] },
      rows: keys.iter().map(|&key| vec![key]).collect(),
    },
    Table {
      name: "values".into(),
      r#type: Type::Field,
      rows: values.iter().map(|&value| vec![word(value)]).collect(),
    },
  ];
  source.maps = vec![Map {
    name: "lookup".into(),
    params: vec![Type::Field],
    result: Type::Field,
    input: 0,
    output: 1,
  }];
  let p = source.clone().check_with(Bn254).unwrap();
  let mut channels = HintChannels::new();
  channels
    .insert("square", Type::Field, Type::Field, |input, output| {
      output[0] = Bn254.mul(input[0], input[0]);
      Ok(())
    })
    .unwrap();
  let prepared = p.prepare_hint_channels(&[], &channels).unwrap();
  for (key, value) in keys.into_iter().zip(values) {
    let record =
      prepared.execute("main", Bn254.decode_words(&[key]).unwrap()).unwrap();
    assert_eq!(record.output, vec![value, Bn254.mul(value, value)]);
    assert_eq!(record.memory.len(), 1);
    assert_eq!(record.memory.get(0).unwrap().cell.value, &[value]);
  }
  assert!(prepared.execute("main", vec![Bn254.from_u64(7)]).is_err());
  source.tables[0].rows = vec![vec![0.into()], vec![1.into()]];
  let dense = source.check_with(Bn254).unwrap();
  let dense = dense.prepare_hint_channels(&[], &channels).unwrap();
  for low in [0, 1] {
    assert!(dense.execute("main", vec![Bn254.from_u64(low)]).is_ok());
    let high = Bn254.from_word(FieldWord::from_limbs_le([low, 1, 0, 0]));
    assert!(dense.execute("main", vec![high]).is_err());
  }
}

#[test]
fn function_memoization_distinguishes_wide_keys_with_identical_low_limbs() {
  let mut source = program(
    2,
    2,
    4,
    vec![
      I::Call { function: 1, args: vec![0], dest: vec![2] },
      I::Call { function: 1, args: vec![1], dest: vec![3] },
      I::Ret { value: vec![2, 3] },
    ],
  );
  source.functions.push(Function {
    name: "identity".into(),
    params: vec![Type::Field],
    result: Type::Field,
    registers: 1,
    code: vec![I::Ret { value: vec![0] }],
  });
  let p = source.check_with(Bn254).unwrap();
  let low = Bn254.one();
  let high = Bn254.from_word(FieldWord::from_limbs_le([1, 1, 0, 0]));
  for input in [vec![low, high], vec![high, low]] {
    assert_eq!(p.execute("main", input.clone()).unwrap().output, input);
  }
}

#[test]
fn wide_pointer_cannot_alias_a_valid_low_address() {
  let p = program(
    0,
    1,
    4,
    vec![
      I::Literal { dest: 0, value: 42.into() },
      I::Store { r#type: Type::Field, value: vec![0], dest: 1 },
      I::Literal { dest: 2, value: FieldWord::from_limbs_le([0, 1, 0, 0]) },
      I::Load { r#type: Type::Field, pointer: 2, dest: vec![3] },
      I::Ret { value: vec![3] },
    ],
  )
  .check_with(Bn254)
  .unwrap();
  assert!(p.execute("main", vec![]).is_err());
}

#[test]
fn byte_hints_reject_a_wide_value_instead_of_returning_its_low_bytes() {
  for (name, width) in [("bytes_le", 8), ("u32.bytes", 4)] {
    let p = program(
      1,
      width,
      width + 1,
      vec![
        I::Hint {
          channel: name.into(),
          key_type: Type::Field,
          r#type: Type::Tuple { items: vec![Type::Field; width] },
          key: vec![0],
          dest: (1..=width).collect(),
        },
        I::Ret { value: (1..=width).collect() },
      ],
    )
    .check_with(Bn254)
    .unwrap();
    let mut channels = HintChannels::new();
    aiur::library::u64::register(&mut channels, Bn254).unwrap();
    aiur::library::u32::register(&mut channels, Bn254).unwrap();
    let prepared = p.prepare_hint_channels(&[], &channels).unwrap();
    let record = prepared.execute("main", vec![Bn254.from_u64(256)]).unwrap();
    assert_eq!(
      record.output,
      Bn254.decode(&[0, 1, 0, 0, 0, 0, 0, 0][..width]).unwrap()
    );
    let high = Bn254.from_word(FieldWord::from_limbs_le([256, 1, 0, 0]));
    assert!(prepared.execute("main", vec![high]).is_err());
  }
}

#[test]
fn stream_reads_reject_wide_channels_and_offsets() {
  use aiur::library::{
    advice::Advice,
    io::{Stream, StreamAdvice, Streams},
  };

  let p = program(
    2,
    1,
    3,
    vec![
      I::Hint {
        channel: "read".into(),
        key_type: Type::Tuple { items: vec![Type::Field; 2] },
        r#type: Type::Field,
        key: vec![0, 1],
        dest: vec![2],
      },
      I::Ret { value: vec![2] },
    ],
  )
  .check_with(Bn254)
  .unwrap();
  let streams =
    Streams(vec![Stream { channel: 0, key: vec![], values: vec![42] }]);
  let mut bindings = [HintChannels::new(), HintChannels::new()];
  streams
    .prepare(Bn254)
    .unwrap()
    .register_read::<1>("read", true, &mut bindings[0])
    .unwrap();
  Advice::from_streams(Bn254, &streams)
    .unwrap()
    .register_read::<1>("read", true, &mut bindings[1])
    .unwrap();
  for channels in bindings {
    let prepared = p.prepare_hint_channels(&[], &channels).unwrap();
    assert_eq!(
      prepared.execute("main", vec![Bn254.zero(); 2]).unwrap().output,
      vec![Bn254.from_u64(42)]
    );
    let high = Bn254.from_word(FieldWord::from_limbs_le([0, 1, 0, 0]));
    for args in [vec![high, Bn254.zero()], vec![Bn254.zero(), high]] {
      assert!(prepared.execute("main", args).is_err());
    }
  }
}

#[test]
fn wide_guards_compare_every_limb_and_reject_noncanonical_constants() {
  let high = FieldWord::from_limbs_le([7, 1, 0, 0]);
  let mut source = program(
    1,
    1,
    2,
    vec![
      I::Branch { tests: vec![(0, high)], otherwise: 3 },
      I::Literal { dest: 1, value: 1.into() },
      I::Ret { value: vec![1] },
      I::Guard { tests: vec![(0, 7.into())], message: "expected seven".into() },
      I::Literal { dest: 1, value: 2.into() },
      I::Ret { value: vec![1] },
    ],
  );
  let p = source.clone().check_with(Bn254).unwrap();
  assert_eq!(
    p.execute("main", vec![Bn254.from_word(high)]).unwrap().output,
    vec![Bn254.one()]
  );
  assert_eq!(
    p.execute("main", vec![Bn254.from_u64(7)]).unwrap().output,
    vec![Bn254.from_u64(2)]
  );
  assert!(
    p.execute(
      "main",
      vec![Bn254.from_word(FieldWord::from_limbs_le([7, 2, 0, 0]))]
    )
    .is_err()
  );
  for pc in [0, 1, 3] {
    let mut bad = source.clone();
    match &mut bad.functions[0].code[pc] {
      I::Branch { tests, .. } | I::Guard { tests, .. } => {
        tests[0].1 = Bn254.modulus()
      },
      I::Literal { value, .. } => *value = Bn254.modulus(),
      _ => unreachable!(),
    }
    assert!(bad.check_with(Bn254).is_err());
  }
  source.modulus = 97.into();
  assert!(source.check_with(Bn254).is_err());
}

#[test]
fn wide_enum_tag_cannot_alias_a_small_constructor() {
  use aiur::bytecode::{Constructor, Enum};

  let mut source = program(1, 1, 1, vec![I::Ret { value: vec![0] }]);
  let ty = Type::Enum { name: "Mode".into() };
  let io = IoType::Enum {
    name: "Mode".into(),
    constructors: vec![("A".into(), vec![]), ("B".into(), vec![])],
  };
  source.enums = vec![Enum {
    name: "Mode".into(),
    constructors: vec![
      Constructor { name: "A".into(), fields: vec![] },
      Constructor { name: "B".into(), fields: vec![] },
    ],
  }];
  source.functions[0].params = vec![ty.clone()];
  source.functions[0].result = ty;
  source.entries[0].inputs = vec![io.clone()];
  source.entries[0].output = Some(io);
  let p = source.check_with(Bn254).unwrap();
  for tag in [0, 1] {
    assert!(p.execute("main", vec![Bn254.from_u64(tag)]).is_ok());
    let high = Bn254.from_word(FieldWord::from_limbs_le([tag, 1, 0, 0]));
    assert!(p.execute("main", vec![high]).is_err());
  }
}

#[test]
fn lean_bn254_program_executes_with_native_field_semantics() {
  let bytes = include_bytes!("../../aiur/tests/fixtures/bn254-execution.ixa");
  let package = aiur::artifact::WidePackage::decode(bytes).unwrap();
  assert_eq!(package.encode().unwrap(), bytes);
  let p = package.program.check_with(Bn254).unwrap();
  let zero = Bn254.zero();
  let one = Bn254.one();
  let two = Bn254.from_u64(2);
  let minus_one = Bn254.neg(one);
  let cases = [
    ("add_one", vec![minus_one], zero),
    ("inverse", vec![two], Bn254.inverse(two).unwrap()),
    ("minus_one", vec![], minus_one),
    ("literal_minus_one", vec![], minus_one),
    ("choice", vec![zero], minus_one),
    ("choice", vec![minus_one], one),
    ("choice", vec![two], two),
    ("guarded", vec![minus_one], minus_one),
    ("table", vec![zero], minus_one),
    ("table", vec![minus_one], Bn254.from_u64(7)),
    ("memory_roundtrip", vec![minus_one], Bn254.neg(two)),
  ];
  for (entry, args, expected) in cases {
    let name = format!("BN254::{entry}");
    assert_eq!(
      p.execute(&name, args).unwrap().output,
      vec![expected],
      "{name}"
    );
  }
  for (entry, argument) in
    [("inverse", zero), ("guarded", zero), ("table", one)]
  {
    assert!(p.execute(&format!("BN254::{entry}"), vec![argument]).is_err());
  }
}
