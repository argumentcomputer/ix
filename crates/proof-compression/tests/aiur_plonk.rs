use aiur::{artifact::WidePackage, field::FieldBackend, trace::TracePlan};
use ix_proof_compression::aiur_backend::{
  Bn254, kzg::Compiler, plonk::Exporter,
};
use p3_matrix::Matrix;
use std::sync::Arc;

fn plan() -> TracePlan<'static, Bn254> {
  let package = WidePackage::decode(include_bytes!(
    "../../aiur/tests/fixtures/bn254-trace.ixa"
  ))
  .unwrap();
  let trace = package.trace.unwrap();
  let mut program = package.program.check_with(Bn254).unwrap();
  program.track_depth(&trace).unwrap();
  TracePlan::new(Arc::new(program), trace).unwrap()
}

#[test]
fn compiler_export_matches_gnark_recursion_map_rom_fixture() {
  let plan = plan();
  let entry = "BN254Trace::run";
  let args = [Bn254.from_u64(3), Bn254.neg(Bn254.one())];
  let record = plan.program().execute(entry, args.to_vec()).unwrap();
  let public = plan.public_args(&record, entry, &args).unwrap();
  let compiler = Compiler::new(&plan).unwrap();
  let traces = compiler.generate(&record, entry, &args).unwrap();
  let capacities: Vec<_> =
    traces.iter().map(|trace| trace.height().max(1)).collect();
  let exporter =
    Exporter::new(&plan, &capacities, entry, &public, &record.output).unwrap();
  let schema: serde_json::Value = serde_json::from_slice(include_bytes!(
    "../../../tools/gnark/testdata/aiur/schema.json"
  ))
  .unwrap();
  let witness: serde_json::Value = serde_json::from_slice(include_bytes!(
    "../../../tools/gnark/testdata/aiur/witness.json"
  ))
  .unwrap();
  assert_eq!(serde_json::to_value(exporter.schema()).unwrap(), schema);
  assert_eq!(
    serde_json::to_value(exporter.witness(&record, &args).unwrap()).unwrap(),
    witness
  );
  let mut changed_args = args;
  changed_args[0] = Bn254.from_u64(0);
  let smaller = plan.program().execute(entry, changed_args.to_vec()).unwrap();
  let smaller_public =
    plan.public_args(&smaller, entry, &changed_args).unwrap();
  let smaller_exporter =
    Exporter::new(&plan, &capacities, entry, &smaller_public, &smaller.output)
      .unwrap();
  assert_eq!(serde_json::to_value(smaller_exporter.schema()).unwrap(), schema);
  assert_ne!(
    serde_json::to_value(exporter.witness(&smaller, &changed_args).unwrap())
      .unwrap(),
    witness
  );
  let args = [Bn254.from_u64(12), Bn254.neg(Bn254.one())];
  let larger = plan.program().execute(entry, args.to_vec()).unwrap();
  assert!(exporter.witness(&larger, &args).unwrap_err().contains("capacity"));
  let mut wrong = capacities.clone();
  wrong[0] = 0;
  assert!(
    Exporter::new(&plan, &wrong, entry, &public, &record.output).is_err()
  );
  wrong[0] = 3;
  assert!(
    Exporter::new(&plan, &wrong, entry, &public, &record.output).is_err()
  );
  assert!(
    Exporter::new(&plan, &capacities[..1], entry, &public, &record.output)
      .is_err()
  );
}

#[cfg(feature = "plonk")]
#[test]
fn gnark_archive_compiles_the_generic_export() {
  let plan = plan();
  let entry = "BN254Trace::run";
  let args = [Bn254.from_u64(3), Bn254.neg(Bn254.one())];
  let record = plan.program().execute(entry, args.to_vec()).unwrap();
  let public = plan.public_args(&record, entry, &args).unwrap();
  let compiler = Compiler::new(&plan).unwrap();
  let capacities: Vec<_> = compiler
    .generate(&record, entry, &args)
    .unwrap()
    .iter()
    .map(|trace| trace.height().max(1))
    .collect();
  let exporter =
    Exporter::new(&plan, &capacities, entry, &public, &record.output).unwrap();
  let directory = std::env::temp_dir()
    .join(format!("ix-aiur-plonk-compile-{}", std::process::id()));
  std::fs::create_dir(&directory).unwrap();
  let path = directory.join("circuit.bin");
  let info = ix_proof_compression::aiur_backend::plonk::gnark::compile(
    exporter.schema(),
    &path,
  )
  .unwrap();
  assert_eq!(info.domain, 32768);
  assert_eq!(info.public_inputs, 3);
  assert_eq!(info.commitments, 1);
  assert!(info.constraints > 30_000);
  assert!(std::fs::metadata(path).unwrap().len() > 0);
  std::fs::remove_dir_all(directory).unwrap();
}
