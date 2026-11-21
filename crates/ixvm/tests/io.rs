//! Exercise the embedding's vector-backed IO through the public hint API.
use aiur::{
  bytecode::{Entry, Function, Instruction, Program, Type, VERSION},
  field::{FieldBackend, NativeField, PrimeField},
  hints::{HintChannels, HintEntry},
  value::IoType,
};

#[path = "../src/io.rs"]
mod io;

fn row(channel: u64, offset: u64, value: u64) -> HintEntry {
  HintEntry {
    channel: io::READ_CHANNEL.into(),
    key_type: Type::Tuple { items: vec![Type::Field; 2] },
    r#type: Type::Field,
    key: vec![channel, offset],
    output: vec![value],
  }
}

fn program(modulus: u64) -> Program {
  Program {
    version: VERSION,
    modulus,
    enums: vec![],
    tables: vec![],
    maps: vec![],
    functions: vec![Function {
      name: "read".into(),
      params: vec![Type::Field; 2],
      result: Type::Field,
      registers: 3,
      code: vec![
        Instruction::Hint {
          channel: io::READ_CHANNEL.into(),
          key_type: row(2, 0, 0).key_type,
          r#type: Type::Field,
          key: vec![0, 1],
          dest: vec![2],
        },
        Instruction::Ret { value: vec![2] },
      ],
    }],
    entries: vec![Entry {
      name: "read".into(),
      function: 0,
      inputs: vec![IoType::Field; 2],
      output: Some(IoType::Field),
    }],
  }
}

fn dense_matches_data<B: FieldBackend>(field: B) {
  let p = program(field.modulus()).check_with(field).unwrap();
  // Unsorted input, overlapping offsets across channels, an identical
  // duplicate and a zero byte must all retain the original data semantics.
  let rows = vec![
    row(4, 1, 19),
    row(2, 1, 31),
    row(4, 0, 0),
    row(2, 0, 27),
    row(2, 1, 31),
  ];
  let mut channels = HintChannels::new();
  assert!(io::register(field, &rows, &mut channels).unwrap());
  let code = p.prepare_hint_channels(&[], &channels).unwrap();
  let data = p.prepare_hints(&rows).unwrap();
  for key in [[2, 1], [4, 0], [2, 0], [4, 1], [2, 1]] {
    let args = field.decode(&key).unwrap();
    let actual = code.execute("read", args.clone()).unwrap();
    let expected = data.execute("read", args).unwrap();
    assert_eq!(actual.output, expected.output);
    assert_eq!(actual.queries, expected.queries);
    assert_eq!(actual.instructions, expected.instructions);
  }
  for key in [[2, 2], [4, 2], [3, 0], [2, field.modulus() - 1]] {
    let args = field.decode(&key).unwrap();
    assert!(
      code
        .execute("read", args.clone())
        .unwrap_err()
        .message
        .contains("missing hint")
    );
    assert!(data.execute("read", args).is_err());
  }
}

#[test]
fn dense_vectors_match_maps_with_native_and_runtime_fields() {
  dense_matches_data(NativeField::<multi_stark::types::Val>::new());
  dense_matches_data(PrimeField::new(97).unwrap());
}

#[test]
fn sparse_or_other_channels_keep_data_fallback() {
  let field = PrimeField::new(97).unwrap();
  let p = program(field.modulus()).check_with(field).unwrap();
  for rows in [
    vec![row(2, 0, 11), row(2, 2, 13)],
    vec![row(3, 0, 17)],
    vec![row(2, 96, 21)],
  ] {
    let mut channels = HintChannels::new();
    assert!(!io::register(field, &rows, &mut channels).unwrap());
    let prepared = p.prepare_hint_channels(&rows, &channels).unwrap();
    for entry in &rows {
      assert_eq!(
        prepared.execute("read", entry.key.clone()).unwrap().output,
        entry.output
      );
    }
    assert!(
      prepared
        .execute("read", vec![2, 1])
        .unwrap_err()
        .message
        .contains("missing hint")
    );
  }
}

#[test]
fn malformed_or_conflicting_dense_data_is_rejected() {
  let field = PrimeField::new(97).unwrap();
  let mut wrong_type = row(2, 0, 1);
  wrong_type.r#type = Type::Tuple { items: vec![Type::Field] };
  let mut wrong_width = row(2, 0, 1);
  wrong_width.key.pop();
  for rows in [
    vec![row(2, 0, 97)],
    vec![row(2, 97, 1)],
    vec![row(2, 0, 1), row(2, 0, 2)],
    vec![wrong_type],
    vec![wrong_width],
  ] {
    assert!(io::register(field, &rows, &mut HintChannels::new()).is_err());
  }
}

#[test]
fn byte_range_still_belongs_to_aiur_constraints() {
  let field = NativeField::<multi_stark::types::Val>::new();
  let p = program(field.modulus()).check_with(field).unwrap();
  let mut channels = HintChannels::new();
  // The hint has type Field, not opaque U8. Its consumer must still perform
  // UInt8::from_field, just as with the original data-backed hints.
  assert!(io::register(field, &[row(2, 0, 256)], &mut channels).unwrap());
  let prepared = p.prepare_hint_channels(&[], &channels).unwrap();
  let result =
    prepared.execute("read", field.decode(&[2, 0]).unwrap()).unwrap();
  assert_eq!(result.output, field.decode(&[256]).unwrap());
}
