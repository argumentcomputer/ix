//! The generated executor must reproduce the interpreter's record, row for
//! row, and its failures, at the same function and instruction.
use aiur::bytecode::Program;
use aiur::bytecode::Type;
use aiur::execute::ExecutionError;
use aiur::field::{FieldBackend, NativeField};
use aiur::hints::HintEntry;
use aiur::native::record_diff;
use multi_stark::p3_goldilocks::Goldilocks;

aiur_macros::kernel!(Coverage, "tests/fixtures/coverage.json");

fn program() -> Program {
  serde_json::from_slice(include_bytes!("fixtures/coverage.json")).unwrap()
}

fn hints() -> Vec<HintEntry> {
  (0..32)
    .map(|key| HintEntry {
      channel: String::new(),
      r#type: Type::Field,
      key_type: Type::Field,
      key: vec![key],
      output: vec![key * 7 + 1],
    })
    .collect()
}

const CASES: &[(&str, &[u64])] = &[
  ("main", &[0, 1, 2, 5, 12, 31]),
  ("fib", &[0, 1, 20]),
  ("even", &[0, 7, 40]),
  ("rom", &[0, 3]),
  ("table", &[0, 7, 8, 1000]),
  ("guard", &[5, 4]),
  ("divide", &[1, 9, 0]),
  ("assert", &[3, 4]),
  ("fail", &[0, 1]),
  ("cycle", &[0]),
  ("dangling", &[0, 17]),
  ("unchecked", &[3, 8]),
  ("xored", &[0, 2, 3, 4, 9]),
];

fn same_error(a: &ExecutionError, b: &ExecutionError) -> bool {
  a.function == b.function
    && a.instruction == b.instruction
    && a.message == b.message
}

fn check<B: FieldBackend>(
  program: &aiur::bytecode::CheckedProgram<B>,
  field: B,
) {
  let prepared = program.prepare_hints(&hints()).unwrap();
  let native = prepared.bind_native::<Coverage>().unwrap();
  let mut successes = 0;
  let mut failures = 0;
  for (entry, inputs) in CASES {
    for &x in *inputs {
      let args = vec![field.from_u64(x)];
      let a = prepared.execute(entry, args.clone());
      let b = native.execute(entry, args);
      match (a, b) {
        (Ok(a), Ok(b)) => {
          record_diff(&a, &b).unwrap_or_else(|e| panic!("{entry}({x}): {e}"));
          successes += 1;
        },
        (Err(a), Err(b)) => {
          assert!(same_error(&a, &b), "{entry}({x}): {a} vs {b}");
          failures += 1;
        },
        (a, b) => panic!(
          "{entry}({x}): interpreter {:?}, native {:?}",
          a.map(|r| r.output),
          b.map(|r| r.output)
        ),
      }
    }
  }
  assert!(
    successes >= 20 && failures >= 9,
    "{successes} successes, {failures} failures"
  );
}

#[test]
fn native_records_match_the_interpreter_over_a_prime_field() {
  let program = program().check().unwrap();
  check(&program, program.field());
}

#[test]
fn native_records_match_the_interpreter_over_goldilocks() {
  let program = program().check_field::<Goldilocks>().unwrap();
  check(&program, NativeField::<Goldilocks>::new());
}

#[test]
fn binding_rejects_a_different_program() {
  let mut changed = program();
  changed.functions[9].name = "divide2".into();
  let changed = changed.check().unwrap();
  let prepared = changed.prepare_hints(&hints()).unwrap();
  match prepared.bind_native::<Coverage>() {
    Err(e) => assert!(e.contains("fingerprint"), "{e}"),
    Ok(_) => panic!("a kernel bound to a different program"),
  }
}

#[test]
fn native_records_match_the_interpreter_with_map_overrides() {
  let program = program().check_field::<Goldilocks>().unwrap();
  let field = NativeField::<Goldilocks>::new();
  let mut overrides = aiur::maps::MapOverrides::new();
  overrides
    .insert_fixed::<1, 1>("double", move |[x]| {
      let x = field.to_u64(x);
      if x >= 8 {
        return Err("double: input out of range".into());
      }
      Ok((usize::try_from(x).unwrap(), [field.from_u64(2 * x)]))
    })
    .unwrap();
  let prepared = program
    .prepare_hints(&hints())
    .unwrap()
    .with_map_overrides(&overrides)
    .unwrap();
  let native = prepared.bind_native::<Coverage>().unwrap();
  for (entry, inputs) in
    [("table", &[0u64, 5, 7, 8, 1000][..]), ("main", &[0, 3, 12][..])]
  {
    for &x in inputs {
      let args = vec![field.from_u64(x)];
      match (prepared.execute(entry, args.clone()), native.execute(entry, args))
      {
        (Ok(a), Ok(b)) => {
          record_diff(&a, &b).unwrap_or_else(|e| panic!("{entry}({x}): {e}"))
        },
        (Err(a), Err(b)) => {
          assert!(same_error(&a, &b), "{entry}({x}): {a} vs {b}")
        },
        _ => panic!("{entry}({x}): only one executor failed"),
      }
    }
  }
}

#[test]
fn binding_rejects_an_override_that_disagrees_with_its_table() {
  let program = program().check_field::<Goldilocks>().unwrap();
  let field = NativeField::<Goldilocks>::new();
  let mut overrides = aiur::maps::MapOverrides::new();
  overrides
    .insert_fixed::<2, 1>("xor", move |[a, b]| {
      let (a, b) = (field.to_u64(a), field.to_u64(b));
      if a >= 4 || b >= 4 {
        return Err("xor: input out of range".into());
      }
      let row = usize::try_from(a * 4 + b).unwrap();
      Ok((row, [field.from_u64((a ^ b) + u64::from(row == 5))]))
    })
    .unwrap();
  let prepared = program
    .prepare_hints(&hints())
    .unwrap()
    .with_map_overrides(&overrides)
    .unwrap();
  match prepared.bind_native::<Coverage>() {
    Err(e) => assert!(e.contains("disagrees"), "{e}"),
    Ok(_) => {
      panic!("bound a kernel to an override that disagrees with its table")
    },
  }
}
