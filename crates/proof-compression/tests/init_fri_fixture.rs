#[allow(dead_code)]
#[path = "../src/bin/support/init_fri.rs"]
mod init_fri;

#[test]
fn saved_init_fri_proof_and_public_statement_verify() {
  let fixture = init_fri::load(
    &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
      .join("tests/fixtures/init-fri"),
  )
  .unwrap();
  assert_eq!(fixture.proof.to_bytes().unwrap().len(), 1_530_149);
  let plan = ix_proof_compression::fri::VerifierPlan::validate(
    &fixture.key,
    fixture.profile,
    Default::default(),
  )
  .unwrap();
  plan.identity(&fixture.schema).unwrap();
}
