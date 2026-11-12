use aiur::{
  FieldWord,
  artifact::WidePackage,
  field::FieldBackend,
  trace::{Action, Polynomial, TracePlan},
};
use ix_proof_compression::aiur_backend::Bn254;

#[test]
fn compiled_and_reference_population_agree_on_native_bn254_rows() {
  let package = WidePackage::decode(include_bytes!(
    "../../aiur/tests/fixtures/bn254-trace.ixa"
  ))
  .unwrap();
  let artifact = package.trace.unwrap();
  let mut program = package.program.check_with(Bn254).unwrap();
  program.track_depth(&artifact).unwrap();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let entry = "BN254Trace::run";
  for n in [0, 1, 3, 17] {
    for x in [Bn254.zero(), Bn254.neg(Bn254.one())] {
      let args = vec![Bn254.from_u64(n), x];
      let record = program.execute(entry, args.clone()).unwrap();
      let expected = if x == Bn254.zero() {
        Bn254.sub(Bn254.from_u64(n), Bn254.one())
      } else {
        Bn254.from_u64(n + 6)
      };
      assert_eq!(record.output, vec![expected]);
      for pad in [false, true] {
        let compiled = plan.generate(&record, entry, &args, pad).unwrap();
        let reference =
          plan.generate_reference(&record, entry, &args, pad).unwrap();
        assert_eq!(compiled, reference);
        plan.check(&record, &compiled, entry, &args).unwrap();
        let public = plan.public_args(&record, entry, &args).unwrap();
        let claim = plan.public_claim(entry, &public, &record.output).unwrap();
        assert_eq!(claim.last(), Some(&expected));
      }
    }
  }
}

#[test]
fn parallel_population_preserves_recursive_gap_counts() {
  let package = WidePackage::decode(include_bytes!(
    "../../aiur/tests/fixtures/bn254-gap.ixa"
  ))
  .unwrap();
  let artifact = package.trace.unwrap();
  let mut program = package.program.check_with(Bn254).unwrap();
  program.track_depth(&artifact).unwrap();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let args = vec![Bn254.from_u64(2048), Bn254.neg(Bn254.one())];
  let record = program.execute("BN254Gap::run", args.clone()).unwrap();
  let compiled = plan.generate(&record, "BN254Gap::run", &args, true).unwrap();
  let reference =
    plan.generate_reference(&record, "BN254Gap::run", &args, true).unwrap();
  assert_eq!(compiled, reference);
  assert!(!compiled.ranges.0.is_empty());
  plan.check(&record, &compiled, "BN254Gap::run", &args).unwrap();
}

#[test]
fn both_population_engines_reject_a_wide_memory_address() {
  let mut package = WidePackage::decode(include_bytes!(
    "../../aiur/tests/fixtures/bn254-trace.ixa"
  ))
  .unwrap();
  let artifact = package.trace.as_mut().unwrap();
  let action = artifact
    .functions
    .iter_mut()
    .flat_map(|f| &mut f.steps)
    .find_map(|step| match &mut step.action {
      Action::Load { address, .. } => Some(address),
      _ => None,
    })
    .expect("fixture must replay a load");
  *action = Polynomial::Const(FieldWord::from_limbs_le([0, 1, 0, 0]));
  let artifact = package.trace.unwrap();
  let mut program = package.program.check_with(Bn254).unwrap();
  program.track_depth(&artifact).unwrap();
  let args = vec![Bn254.from_u64(3), Bn254.neg(Bn254.one())];
  let entry = "BN254Trace::run";
  let record = program.execute(entry, args.clone()).unwrap();
  let plan = TracePlan::new(&program, artifact).unwrap();
  for result in [
    plan.generate(&record, entry, &args, true),
    plan.generate_reference(&record, entry, &args, true),
  ] {
    assert!(result.unwrap_err().contains("ROM address overflow"));
  }
}

#[test]
fn depth_range_maps_validate_the_entire_native_value() {
  use aiur::bytecode::{Map, Table, Type};

  let mut package = WidePackage::decode(include_bytes!(
    "../../aiur/tests/fixtures/bn254-trace.ixa"
  ))
  .unwrap();
  let mut artifact = package.trace.take().unwrap();
  artifact.limbs = vec![4];
  let input = package.program.tables.len();
  package.program.tables.extend([
    Table {
      name: "range-input".into(),
      r#type: Type::Tuple { items: vec![Type::Field] },
      rows: (0..16).map(|n| vec![FieldWord::from(n)]).collect(),
    },
    Table {
      name: "range-output".into(),
      r#type: Type::Tuple { items: vec![] },
      rows: vec![vec![]; 16],
    },
  ]);
  package.program.maps.push(Map {
    name: "Depth::range4".into(),
    params: vec![Type::Field],
    result: Type::Tuple { items: vec![] },
    input,
    output: input + 1,
  });
  let mut valid = package.program.clone().check_with(Bn254).unwrap();
  valid.track_depth(&artifact).unwrap();
  assert!(TracePlan::new(&valid, artifact.clone()).is_ok());
  package.program.tables[input].rows[7][0] =
    FieldWord::from_limbs_le([7, 1, 0, 0]);
  let mut invalid = package.program.check_with(Bn254).unwrap();
  invalid.track_depth(&artifact).unwrap();
  let error = TracePlan::new(&invalid, artifact).err().unwrap();
  assert!(error.contains("malformed depth range map"));
}
