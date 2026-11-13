use aiur::{artifact::WidePackage, field::FieldBackend};
use ix_proof_compression::{
  aiur_backend::{
    Bn254,
    kzg::Compiler,
    kzg_advice::{Inputs, Policy},
    pairing::final_program::{
      ACCUMULATOR_ENTRY, AccumulatorProgram, Configuration, Program,
      statement_arguments,
    },
    plonk::{Exporter, FORMAT, TERMINAL_FORMAT, public_bytes},
  },
  kzg::{Srs, VerifierParams},
};

#[path = "../examples/aiur_final_fixture/input.rs"]
mod input;

#[test]
fn terminal_export_binds_private_outputs_configuration_and_original_statement()
{
  let path = std::env::var_os("IX_AIUR_TERMINAL_ARTIFACT").map_or_else(
    || {
      std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../aiur/tests/fixtures/compress-final-accumulator.ixa")
    },
    std::path::PathBuf::from,
  );
  let bytes = std::fs::read(path).unwrap();
  let program =
    AccumulatorProgram::from_bytes(&bytes, blake3::hash(&bytes).as_bytes())
      .unwrap();
  assert!(
    Program::from_bytes(&bytes, blake3::hash(&bytes).as_bytes()).is_err()
  );
  let fixture = input::Fixture::new();
  let arguments = statement_arguments(&fixture.statement);
  assert!(
    program
      .execute_with_record_limit(&fixture.inputs(), &fixture.statement, 1, 0)
      .is_err()
  );
  assert!(
    program
      .execute_with_record_limit(&fixture.inputs(), &fixture.statement, 1, 1)
      .is_err()
  );
  let record =
    program.execute(&fixture.inputs(), &fixture.statement, 1).unwrap();
  assert_eq!(record.output.len(), 18);
  let compiler = Compiler::new(program.plan()).unwrap();
  let capacities: Vec<_> = compiler
    .row_counts(&record)
    .unwrap()
    .into_iter()
    .map(|n| n.max(1))
    .collect();
  let public =
    program.plan().public_args(&record, ACCUMULATOR_ENTRY, &arguments).unwrap();
  let exporter = Exporter::terminal(
    program.plan(),
    &capacities,
    &public,
    &record.output,
    &fixture.configuration,
  )
  .unwrap();
  assert_eq!(exporter.schema().format, TERMINAL_FORMAT);
  assert_eq!(exporter.schema().public_inputs, 2);
  assert_eq!(exporter.schema().private_outputs, 18);
  assert!(exporter.schema().pairing.is_some());
  let generic = Exporter::new(
    program.plan(),
    &capacities,
    ACCUMULATOR_ENTRY,
    &public,
    &record.output,
  )
  .unwrap();
  assert_eq!(generic.schema().format, FORMAT);
  assert_eq!(generic.schema().public_inputs, 20);
  assert_eq!(generic.schema().private_outputs, 0);
  assert!(generic.schema().pairing.is_none());

  let witness = exporter.binary_witness(&record, &arguments).unwrap();
  let public_count = u32::from_be_bytes(witness[..4].try_into().unwrap());
  let secret_count = u32::from_be_bytes(witness[4..8].try_into().unwrap());
  let main_cells: usize =
    exporter.schema().circuits.iter().map(|c| c.rows * c.main_width).sum();
  assert_eq!(public_count, 2);
  assert_eq!(usize::try_from(secret_count).unwrap(), main_cells + 18);
  assert_eq!(
    &witness[witness.len() - 18 * 32..],
    public_bytes(&record.output).unwrap()
  );

  let wrong_srs =
    Srs::unsafe_dev_setup_prefix(64, (1 << 24) - 1, b"wrong terminal anchors");
  let parameters = VerifierParams::with_max_trace_len(&wrong_srs, 1 << 24);
  let policy = Policy::new(
    &parameters,
    *blake3::hash(&fixture.key).as_bytes(),
    31,
    [0; 32],
    47,
  )
  .unwrap();
  let wrong_configuration =
    Configuration::new(&policy, &parameters, 1, true).unwrap();
  assert!(
    Exporter::terminal(
      program.plan(),
      &capacities,
      &public,
      &record.output,
      &wrong_configuration
    )
    .err()
    .unwrap()
    .contains("trusted configuration")
  );

  let mut package = WidePackage::decode(&bytes).unwrap();
  let table = package
    .program
    .tables
    .iter_mut()
    .find(|t| t.name == "CompressFinal::configuration_outputs")
    .unwrap();
  table.rows[0][8] =
    Bn254.to_word(Bn254.from_word(table.rows[0][8]) + Bn254.one());
  let changed = package.encode().unwrap();
  let changed_program =
    AccumulatorProgram::from_bytes(&changed, blake3::hash(&changed).as_bytes())
      .unwrap();
  assert!(
    Exporter::terminal(
      changed_program.plan(),
      &capacities,
      &public,
      &record.output,
      &fixture.configuration
    )
    .err()
    .unwrap()
    .contains("trusted configuration")
  );

  let mut wrong_statement = fixture.statement;
  wrong_statement[0] ^= 1;
  assert!(program.execute(&fixture.inputs(), &wrong_statement, 1).is_err());
  assert!(program.execute(&fixture.inputs(), &fixture.statement, 0).is_err());
  assert!(program.execute(&fixture.inputs(), &fixture.statement, 2).is_err());
  let bad = Inputs::new(
    fixture.key.clone(),
    fixture.claims.clone(),
    fixture.forged_opening.clone(),
    fixture.policy.clone(),
  )
  .unwrap();
  let deferred = program.execute(&bad, &fixture.statement, 1).unwrap();
  assert_eq!(deferred.output.len(), 18);
  assert_ne!(deferred.output, record.output);
}
