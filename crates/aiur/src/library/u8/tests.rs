use super::*;
use crate::{
  bytecode::{Map, Program, Table, Type, VERSION},
  field::{NativeField, PrimeField},
  maps::MapRecord,
};
use multi_stark::p3_goldilocks::Goldilocks;

fn pairs<B: FieldBackend>(field: B, permuted: bool) -> CheckedProgram<B> {
  let mut rows: Vec<_> =
    (0..256).flat_map(|a| (0..256).map(move |b| vec![a, b])).collect();
  if permuted {
    rows.swap(0, 256);
  }
  let params = vec![Type::Field; 2];
  let result = Type::Tuple { items: vec![] };
  Program {
    version: VERSION,
    modulus: field.modulus(),
    functions: vec![],
    enums: vec![],
    entries: vec![],
    maps: vec![Map {
      name: "UInt8::range_pair".into(),
      params: params.clone(),
      result: result.clone(),
      input: 0,
      output: 1,
    }],
    tables: vec![
      Table {
        name: "inputs".into(),
        r#type: Type::Tuple { items: params },
        rows,
      },
      Table {
        name: "outputs".into(),
        r#type: result,
        rows: vec![vec![]; 65536],
      },
    ],
  }
  .check_with(field)
  .unwrap()
}

fn all_pairs<B: FieldBackend>(field: B) {
  let program = pairs(field, false);
  let mut overrides = MapOverrides::new();
  register_maps(&program, &mut overrides).unwrap();
  let binding = overrides.bind(&program).unwrap().remove(0);
  let mut record = MapRecord::new(binding);
  for _ in 0..2 {
    for args in &program.tables[0] {
      record.call(args, &mut []).unwrap();
    }
  }
  assert_eq!(&*record.counts, &vec![2; 65536]);
  // In particular (0, 256) must not alias (1, 0) when packing the key.
  for (a, b) in
    [(0, 256), (256, 0), (0, field.modulus() - 1), (field.modulus() - 1, 0)]
  {
    let args = [field.from_u64(a), field.from_u64(b)];
    assert!(
      record.call(&args, &mut []).unwrap_err().contains("no table entry")
    );
  }
  assert_eq!(&*record.counts, &vec![2; 65536]);
  record.counts[0] = u64::MAX;
  assert!(
    record
      .call(&[field.zero(), field.zero()], &mut [])
      .unwrap_err()
      .contains("multiplicity overflow")
  );
  assert_eq!(record.counts[0], u64::MAX);
}

#[test]
fn byte_indices_cover_every_pair_and_keep_integer_multiplicities() {
  all_pairs(PrimeField::new(65537).unwrap());
  all_pairs(NativeField::<Goldilocks>::new());
}

#[test]
fn reordered_byte_tables_fall_back_and_native_representations_compare_by_value()
{
  let field = NativeField::<Goldilocks>::new();
  for permuted in [false, true] {
    let program = pairs(field, permuted);
    let mut overrides = MapOverrides::new();
    register_maps(&program, &mut overrides).unwrap();
    let mut record =
      MapRecord::new(overrides.bind(&program).unwrap().remove(0));
    for one in [field.one(), Goldilocks::new(field.modulus() + 1)] {
      record.call(&[one, field.zero()], &mut []).unwrap();
    }
    let row = if permuted { 0 } else { 256 };
    assert_eq!(record.counts.iter().filter(|&&count| count != 0).count(), 1);
    assert_eq!(record.counts[row], 2);
    assert_eq!(record.binding.input(row), [field.one(), field.zero()]);
  }
}

#[test]
fn direct_byte_maps_and_word_hints_match_table_and_closure_execution() {
  use crate::{
    bytecode::{Entry, Function, Instruction},
    hints::HintChannels,
    value::IoType,
  };
  let field = NativeField::<Goldilocks>::new();
  let f = Type::Field;
  let unit = Type::Tuple { items: vec![] };
  let pair_t = Type::Tuple { items: vec![f.clone(), f.clone()] };
  let bytes4 = Type::Tuple { items: vec![f.clone(); 4] };
  let bytes8 = Type::Tuple { items: vec![f.clone(); 8] };

  let u8_in: Vec<Vec<u64>> = (0..256).map(|a| vec![a]).collect();
  let sum_in: Vec<Vec<u64>> = (0..768).map(|a| vec![a]).collect();
  let pair_in: Vec<Vec<u64>> =
    (0..256).flat_map(|a| (0..256).map(move |b| vec![a, b])).collect();

  let bit_out: Vec<Vec<u64>> =
    (0..256).map(|x| (0..8).map(|i| (x >> i) & 1).collect()).collect();
  let pair_unit: Vec<Vec<u64>> = vec![vec![]; 65536];
  let xor_out: Vec<Vec<u64>> =
    pair_in.iter().map(|r| vec![r[0] ^ r[1]]).collect();
  let and_out: Vec<Vec<u64>> =
    pair_in.iter().map(|r| vec![r[0] & r[1]]).collect();
  let or_out: Vec<Vec<u64>> =
    pair_in.iter().map(|r| vec![r[0] | r[1]]).collect();
  let lt_out: Vec<Vec<u64>> =
    pair_in.iter().map(|r| vec![u64::from(r[0] < r[1])]).collect();
  let add_out: Vec<Vec<u64>> = pair_in
    .iter()
    .map(|r| vec![(r[0] + r[1]) & 255, (r[0] + r[1]) >> 8])
    .collect();
  let sub_out: Vec<Vec<u64>> = pair_in
    .iter()
    .map(|r| vec![r[0].wrapping_sub(r[1]) & 255, u64::from(r[0] < r[1])])
    .collect();
  let mul_out: Vec<Vec<u64>> = pair_in
    .iter()
    .map(|r| vec![(r[0] * r[1]) & 255, (r[0] * r[1]) >> 8])
    .collect();
  let split4_out: Vec<Vec<u64>> = pair_in
    .iter()
    .map(|r| {
      let x = r[0] ^ r[1];
      vec![x >> 4, (x & 15) << 4]
    })
    .collect();
  let split7_out: Vec<Vec<u64>> = pair_in
    .iter()
    .map(|r| {
      let x = r[0] ^ r[1];
      vec![x >> 7, (x & 127) << 1]
    })
    .collect();
  let sum_out: Vec<Vec<u64>> = (0..768).map(|x| vec![x & 255]).collect();

  let unary_t = Type::Tuple { items: vec![f.clone()] };
  // Tables: 0=u8_in, 1=sum_in, 2=pair_in, 3..15=outputs
  let tables = vec![
    Table {
      name: "u8_in".into(),
      r#type: unary_t.clone(),
      rows: u8_in.clone(),
    },
    Table { name: "sum_in".into(), r#type: unary_t, rows: sum_in },
    Table { name: "pair_in".into(), r#type: pair_t.clone(), rows: pair_in },
    Table { name: "u8_id".into(), r#type: f.clone(), rows: u8_in },
    Table { name: "bit_out".into(), r#type: bytes8.clone(), rows: bit_out },
    Table { name: "pair_unit".into(), r#type: unit.clone(), rows: pair_unit },
    Table { name: "xor_out".into(), r#type: f.clone(), rows: xor_out },
    Table { name: "and_out".into(), r#type: f.clone(), rows: and_out },
    Table { name: "or_out".into(), r#type: f.clone(), rows: or_out },
    Table { name: "lt_out".into(), r#type: f.clone(), rows: lt_out },
    Table { name: "add_out".into(), r#type: pair_t.clone(), rows: add_out },
    Table { name: "sub_out".into(), r#type: pair_t.clone(), rows: sub_out },
    Table { name: "mul_out".into(), r#type: pair_t.clone(), rows: mul_out },
    Table {
      name: "split4_out".into(),
      r#type: pair_t.clone(),
      rows: split4_out,
    },
    Table {
      name: "split7_out".into(),
      r#type: pair_t.clone(),
      rows: split7_out,
    },
    Table { name: "sum_out".into(), r#type: f.clone(), rows: sum_out },
  ];
  let maps = vec![
    Map {
      name: "UInt8::from_field".into(),
      params: vec![f.clone()],
      result: f.clone(),
      input: 0,
      output: 3,
    },
    Map {
      name: "UInt8::raw_bit_decomposition".into(),
      params: vec![f.clone()],
      result: bytes8.clone(),
      input: 0,
      output: 4,
    },
    Map {
      name: "UInt8::range_pair".into(),
      params: vec![f.clone(), f.clone()],
      result: unit,
      input: 2,
      output: 5,
    },
    Map {
      name: "UInt8::raw_xor".into(),
      params: vec![f.clone(), f.clone()],
      result: f.clone(),
      input: 2,
      output: 6,
    },
    Map {
      name: "UInt8::raw_and".into(),
      params: vec![f.clone(), f.clone()],
      result: f.clone(),
      input: 2,
      output: 7,
    },
    Map {
      name: "UInt8::raw_or".into(),
      params: vec![f.clone(), f.clone()],
      result: f.clone(),
      input: 2,
      output: 8,
    },
    Map {
      name: "UInt8::raw_lt".into(),
      params: vec![f.clone(), f.clone()],
      result: f.clone(),
      input: 2,
      output: 9,
    },
    Map {
      name: "UInt8::raw_add".into(),
      params: vec![f.clone(), f.clone()],
      result: pair_t.clone(),
      input: 2,
      output: 10,
    },
    Map {
      name: "UInt8::raw_sub".into(),
      params: vec![f.clone(), f.clone()],
      result: pair_t.clone(),
      input: 2,
      output: 11,
    },
    Map {
      name: "UInt8::raw_mul".into(),
      params: vec![f.clone(), f.clone()],
      result: pair_t.clone(),
      input: 2,
      output: 12,
    },
    Map {
      name: "UInt8::raw_xor_split4".into(),
      params: vec![f.clone(), f.clone()],
      result: pair_t.clone(),
      input: 2,
      output: 13,
    },
    Map {
      name: "UInt8::raw_xor_split7".into(),
      params: vec![f.clone(), f.clone()],
      result: pair_t.clone(),
      input: 2,
      output: 14,
    },
    Map {
      name: "UInt8::raw_sum_byte".into(),
      params: vec![f.clone()],
      result: f.clone(),
      input: 1,
      output: 15,
    },
  ];
  // Function 0 exercises all 13 direct maps (including aliased src==dst) plus
  // all 6 direct hints (`u32.*` and `bytes_le`).
  let code = vec![
    // Function callables: 0 = main, 1..=13 = maps above.
    Instruction::Call { function: 1, args: vec![0], dest: vec![0] }, // aliased from_field
    Instruction::Call { function: 3, args: vec![0, 1], dest: vec![] }, // range_pair
    Instruction::Call { function: 4, args: vec![0, 1], dest: vec![2] }, // xor
    Instruction::Call { function: 5, args: vec![0, 1], dest: vec![3] }, // and
    Instruction::Call { function: 6, args: vec![0, 1], dest: vec![4] }, // or
    Instruction::Call { function: 7, args: vec![0, 1], dest: vec![5] }, // lt
    Instruction::Call { function: 8, args: vec![0, 1], dest: vec![6, 7] }, // add
    Instruction::Call { function: 9, args: vec![0, 1], dest: vec![8, 9] }, // sub
    Instruction::Call { function: 10, args: vec![0, 1], dest: vec![10, 11] }, // mul
    Instruction::Call { function: 11, args: vec![0, 1], dest: vec![12, 13] }, // split4
    Instruction::Call { function: 12, args: vec![0, 1], dest: vec![14, 15] }, // split7
    Instruction::Call { function: 13, args: vec![2], dest: vec![16] }, // sum_byte
    Instruction::Call { function: 2, args: vec![0], dest: (17..25).collect() }, // bit_decomp
    // Hints: u32.bytes, u32.sub, u32.add, u32.add3, u32.lt, bytes_le
    Instruction::Hint {
      channel: "u32.bytes".into(),
      key_type: f.clone(),
      r#type: bytes4.clone(),
      key: vec![0],
      dest: vec![25, 26, 27, 28],
    },
    Instruction::Hint {
      channel: "u32.sub".into(),
      key_type: pair_t.clone(),
      r#type: bytes4.clone(),
      key: vec![0, 1],
      dest: vec![29, 30, 31, 32],
    },
    Instruction::Hint {
      channel: "u32.add".into(),
      key_type: Type::Tuple { items: vec![bytes4.clone(), bytes4.clone()] },
      r#type: bytes4.clone(),
      key: vec![25, 26, 27, 28, 29, 30, 31, 32],
      dest: vec![33, 34, 35, 36],
    },
    Instruction::Hint {
      channel: "u32.add3".into(),
      key_type: Type::Tuple {
        items: vec![bytes4.clone(), bytes4.clone(), bytes4.clone()],
      },
      r#type: bytes4.clone(),
      key: vec![25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36],
      dest: vec![37, 38, 39, 40],
    },
    Instruction::Hint {
      channel: "u32.lt".into(),
      key_type: pair_t.clone(),
      r#type: Type::Tuple { items: vec![bytes4.clone(); 3] },
      key: vec![0, 1],
      dest: (41..53).collect(),
    },
    Instruction::Hint {
      channel: "bytes_le".into(),
      key_type: f.clone(),
      r#type: bytes8.clone(),
      key: vec![10],
      dest: (53..61).collect(),
    },
    Instruction::Ret { value: (2..61).collect() },
  ];
  let program = Program {
    version: VERSION,
    modulus: field.modulus(),
    enums: vec![],
    tables,
    maps,
    functions: vec![Function {
      name: "all_ops".into(),
      params: vec![f.clone(), f.clone()],
      result: Type::Tuple { items: vec![f.clone(); 59] },
      registers: 61,
      code,
    }],
    entries: vec![Entry {
      name: "all_ops".into(),
      function: 0,
      inputs: vec![IoType::Field, IoType::Field],
      output: None,
    }],
  };
  let native = program.clone().check_with(field).unwrap();
  let prime =
    program.check_with(PrimeField::new(field.modulus()).unwrap()).unwrap();

  let mut native_hints = HintChannels::new();
  crate::library::u32::register(&mut native_hints, field).unwrap();
  crate::library::u64::register(&mut native_hints, field).unwrap();
  let mut native_maps = MapOverrides::new();
  register_maps(&native, &mut native_maps).unwrap();
  let direct_exec = native
    .prepare_hint_channels(&[], &native_hints)
    .unwrap()
    .with_map_overrides(&native_maps)
    .unwrap();
  let table_exec = native.prepare_hint_channels(&[], &native_hints).unwrap();

  let pf = prime.field();
  let mut prime_hints = HintChannels::new();
  crate::library::u32::register(&mut prime_hints, pf).unwrap();
  crate::library::u64::register(&mut prime_hints, pf).unwrap();
  let mut prime_maps = MapOverrides::new();
  register_maps(&prime, &mut prime_maps).unwrap();
  let closure_exec = prime
    .prepare_hint_channels(&[], &prime_hints)
    .unwrap()
    .with_map_overrides(&prime_maps)
    .unwrap();

  for (a, b) in [(0u64, 0u64), (1, 255), (255, 1), (173, 99), (128, 128)] {
    let args_n = [field.from_u64(a), field.from_u64(b)];
    let direct = direct_exec.execute("all_ops", args_n.to_vec()).unwrap();
    let table = table_exec.execute("all_ops", args_n.to_vec()).unwrap();
    let closure = closure_exec.execute("all_ops", vec![a, b]).unwrap();
    assert_eq!(direct.output, table.output);
    assert_eq!(direct.queries, table.queries);
    assert_eq!(direct.instructions, table.instructions);
    assert_eq!(
      direct.output.iter().map(|&v| field.to_u64(v)).collect::<Vec<_>>(),
      closure.output
    );
    assert_eq!(direct.instructions, closure.instructions);
  }
  // Out-of-range byte fails identically on direct and table paths.
  let err_direct = direct_exec
    .execute("all_ops", vec![field.from_u64(256), field.zero()])
    .unwrap_err();
  let err_table = table_exec
    .execute("all_ops", vec![field.from_u64(256), field.zero()])
    .unwrap_err();
  assert_eq!(err_direct.instruction, err_table.instruction);
  assert_eq!(err_direct.message, err_table.message);

  // Also verify FillPlan direct map/hint evaluation matches reference replay
  // bit-for-bit across all 13 direct byte maps and 6 direct word hints.
  let mut steps = Vec::new();
  let mut next_dest = 2usize;
  for (pc, op) in native.program().functions[0].code.iter().enumerate() {
    match op {
      Instruction::Call { function, args, dest } => {
        let name = native.callable_name(*function).unwrap().to_owned();
        steps.push(crate::trace::PopulationStep {
          guard: crate::trace::Polynomial::Const(1),
          action: crate::trace::Action::Call {
            name,
            args: args
              .iter()
              .map(|&r| crate::trace::Polynomial::Var(r))
              .collect(),
            dest: dest.clone(),
          },
        });
        next_dest = next_dest.max(dest.iter().copied().max().unwrap_or(0) + 1);
      },
      Instruction::Hint { channel, r#type, key_type, key, dest } => {
        steps.push(crate::trace::PopulationStep {
          guard: crate::trace::Polynomial::Const(1),
          action: crate::trace::Action::Hint {
            channel: channel.clone(),
            instruction: pc,
            r#type: r#type.clone(),
            key_type: key_type.clone(),
            key: key
              .iter()
              .map(|&r| crate::trace::Polynomial::Var(r))
              .collect(),
            dest: dest.clone(),
          },
        });
        next_dest = next_dest.max(dest.iter().copied().max().unwrap_or(0) + 1);
      },
      Instruction::Binary { dest, left, right, .. } => {
        steps.push(crate::trace::PopulationStep {
          guard: crate::trace::Polynomial::Const(1),
          action: crate::trace::Action::Assign {
            dest: vec![*dest],
            values: vec![crate::trace::Polynomial::Add(Box::new([
              crate::trace::Polynomial::Var(*left),
              crate::trace::Polynomial::Var(*right),
            ]))],
          },
        });
        next_dest = next_dest.max(*dest + 1);
      },
      Instruction::Ret { .. } => (),
      other => panic!("unexpected instruction in all_ops: {other:?}"),
    }
  }
  let out_start = next_dest;
  let total_witnesses = out_start + 59;
  let writes: Vec<_> = (0..out_start)
    .map(|col| crate::trace::ColumnWrite {
      column: col,
      source: col,
      guard: crate::trace::Polynomial::Const(1),
    })
    .collect();
  let artifact = crate::trace::TraceArtifact {
    version: 3,
    modulus: field.modulus(),
    limbs: vec![],
    functions: vec![crate::trace::FunctionPlan {
      name: "all_ops".into(),
      chip: "all_ops".into(),
      witnesses: total_witnesses,
      inputs: vec![0, 1],
      output: (out_start..total_witnesses).collect(),
      steps,
      writes,
    }],
    chips: vec![crate::trace::Chip {
      name: "all_ops".into(),
      width: out_start + 1,
      activation: out_start,
      inputs: vec![0, 1],
      output: (2..61).map(crate::trace::Polynomial::Var).collect(),
      constraints: vec![],
      sends: vec![],
      memory: vec![],
      depth: Default::default(),
    }],
    groups: vec![],
  };
  let plan = crate::trace::TracePlan::new(&native, artifact).unwrap();
  for (a, b) in [(0u64, 0u64), (1, 255), (255, 1), (173, 99), (128, 128)] {
    let args = [field.from_u64(a), field.from_u64(b)];
    let record = direct_exec.execute("all_ops", args.to_vec()).unwrap();
    let fast = plan.generate(&record, "all_ops", &args, true).unwrap();
    let reference =
      plan.generate_reference(&record, "all_ops", &args, true).unwrap();
    assert_eq!(fast, reference);
  }
}
