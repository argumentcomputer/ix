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
