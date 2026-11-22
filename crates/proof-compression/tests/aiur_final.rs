use std::sync::{Arc, OnceLock};

use aiur::{
  artifact::WidePackage, bytecode::Type, field::FieldBackend,
  hints::HintChannels, maps::MapOverrides, trace::TracePlan,
};
use ix_proof_compression::{
  aiur_backend::{
    Bn254, fq, g1,
    kzg::Compiler,
    kzg_advice as wire, pairing,
    pairing::final_program::{Program, statement_arguments},
  },
  kzg::Scalar,
};

#[path = "../examples/aiur_final_fixture/input.rs"]
mod input;

const ENTRY: &str = "CompressFinal::verify_v1";

fn plan() -> &'static TracePlan<'static, Bn254> {
  static PLAN: OnceLock<TracePlan<'static, Bn254>> = OnceLock::new();
  PLAN.get_or_init(|| {
    let package = WidePackage::decode(include_bytes!(
      "../../aiur/tests/fixtures/compress-final.ixa"
    ))
    .unwrap();
    let trace = package.trace.unwrap();
    let mut program = package.program.check_with(Bn254).unwrap();
    program.track_depth(&trace).unwrap();
    TracePlan::new(Arc::new(program), trace).unwrap()
  })
}

fn execute(
  fixture: &input::Fixture,
  statement: &[u8; 32],
  stage: Scalar,
  proof: Vec<u8>,
  policy: Vec<u8>,
) -> Result<aiur::Execution<Bn254>, String> {
  let mut hints = HintChannels::new();
  aiur::library::u32::register(&mut hints, Bn254).unwrap();
  aiur::library::u64::register(&mut hints, Bn254).unwrap();
  fq::register(&mut hints).unwrap();
  g1::register(&mut hints).unwrap();
  pairing::register(&mut hints).unwrap();
  wire::register(&mut hints).unwrap();
  wire::Inputs::new(fixture.key.clone(), fixture.claims.clone(), proof, policy)
    .unwrap()
    .register(&mut hints)
    .unwrap();
  hints
    .insert_fixed::<0, 1>(
      "kzg.final.stage",
      Type::Tuple { items: vec![] },
      Type::Field,
      move |[]| Ok([stage]),
    )
    .unwrap();
  let mut maps = MapOverrides::new();
  aiur::library::u8::register_maps(plan().program(), &mut maps).unwrap();
  plan()
    .program()
    .prepare_hint_channels(&[], &hints)
    .unwrap()
    .with_map_overrides(&maps)
    .unwrap()
    .execute(ENTRY, statement_arguments(statement).to_vec())
    .map_err(|error| error.to_string())
}

#[test]
fn final_source_binds_statement_policy_stage_and_pairing() {
  let fixture = input::Fixture::new();
  assert_eq!(
    fixture.configuration.to_json().unwrap(),
    include_bytes!("../../aiur/tests/fixtures/compress-final.json")
  );
  let _ = fixture.inputs();
  let mut hints = HintChannels::new();
  fixture.configuration.register_stage(&mut hints, 1).unwrap();
  assert!(fixture.configuration.register_stage(&mut hints, 0).is_err());
  assert!(fixture.configuration.register_stage(&mut hints, 2).is_err());
  let bytes = include_bytes!("../../aiur/tests/fixtures/compress-final.ixa");
  let pin = *blake3::hash(bytes).as_bytes();
  assert!(Program::from_bytes(bytes, &[0; 32]).is_err());
  let program = Program::from_bytes(bytes, &pin).unwrap();
  let record =
    program.execute(&fixture.inputs(), &fixture.statement, 1).unwrap();
  assert!(record.output.is_empty());
  let compiler = Compiler::new(plan()).unwrap();
  let heights = compiler.row_counts(&record).unwrap();
  let cells: usize = heights
    .iter()
    .zip(compiler.inputs())
    .map(|(height, input)| height * input.main_width)
    .sum();
  eprintln!(
    "terminal verifier: {cells} main cells, max height {}",
    heights.iter().max().unwrap()
  );
  drop(record);
  for index in [0, 15, 16, 31] {
    let mut statement = fixture.statement;
    statement[index] ^= 1;
    assert!(
      execute(
        &fixture,
        &statement,
        Bn254.one(),
        fixture.proof.clone(),
        fixture.policy.clone()
      )
      .is_err()
    );
  }
  for stage in [0, 2, 1 << 32] {
    assert!(
      execute(
        &fixture,
        &fixture.statement,
        Bn254.from_u64(stage),
        fixture.proof.clone(),
        fixture.policy.clone()
      )
      .is_err()
    );
  }
  let mut policy = fixture.policy.clone();
  policy[8] ^= 1;
  assert!(
    execute(
      &fixture,
      &fixture.statement,
      Bn254.one(),
      fixture.proof.clone(),
      policy
    )
    .is_err()
  );
  assert!(
    execute(
      &fixture,
      &fixture.statement,
      Bn254.one(),
      fixture.forged_opening.clone(),
      fixture.policy.clone()
    )
    .is_err(),
    "terminal pairing accepted a forged KZG opening"
  );
}
