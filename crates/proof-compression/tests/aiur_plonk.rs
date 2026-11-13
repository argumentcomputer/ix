use aiur::{artifact::WidePackage, field::FieldBackend, trace::TracePlan};
use ix_proof_compression::aiur_backend::{
  Bn254, kzg::Compiler, plonk::Exporter,
};
use p3_matrix::Matrix;
use std::sync::Arc;

#[test]
fn aiur_domain_limit_requires_the_exact_ignition_opening_prefix() {
  use ix_proof_compression::{
    aiur_backend::plonk::MAX_DOMAIN, pipeline::plonk_limits::ParameterSize,
  };
  let ceremony_powers = 100_800_000;
  assert_eq!(MAX_DOMAIN, 1 << 26);
  let size = ParameterSize::for_domain(MAX_DOMAIN).unwrap();
  assert_eq!(size.opening_powers(), MAX_DOMAIN + 3);
  assert!(size.check_capacity(MAX_DOMAIN, ceremony_powers - 1).is_err());
  assert!(size.check_capacity(MAX_DOMAIN + 2, ceremony_powers - 1).is_err());
  assert!(size.check_capacity(MAX_DOMAIN + 3, ceremony_powers - 1).is_ok());
  assert!(ParameterSize::for_domain(MAX_DOMAIN * 2).is_err());
  assert!(MAX_DOMAIN * 2 + 3 > ceremony_powers);
}

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
  assert_eq!(
    exporter.binary_witness(&record, &args).unwrap(),
    include_bytes!("../../../tools/gnark/testdata/aiur/witness.bin")
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

#[cfg(feature = "plonk")]
#[test]
#[ignore = "requires independently authenticated IX_AIUR_PLONK_SRS and IX_AIUR_PLONK_SRS_BLAKE3"]
fn retained_backend_proves_distinct_calls_with_one_ignition_key() {
  use ix_proof_compression::aiur_backend::plonk::gnark;
  use sha2::{Digest, Sha256};
  let srs =
    std::path::PathBuf::from(std::env::var_os("IX_AIUR_PLONK_SRS").unwrap());
  let receipt = std::env::var("IX_AIUR_PLONK_SRS_BLAKE3").unwrap();
  let plan = plan();
  let entry = "BN254Trace::run";
  let args = [Bn254.from_u64(3), Bn254.neg(Bn254.one())];
  let record = plan.program().execute(entry, args.to_vec()).unwrap();
  let public = plan.public_args(&record, entry, &args).unwrap();
  let compiler = Compiler::new(&plan).unwrap();
  let capacities: Vec<_> = compiler
    .row_counts(&record)
    .unwrap()
    .into_iter()
    .map(|n| n.max(1))
    .collect();
  let exporter =
    Exporter::new(&plan, &capacities, entry, &public, &record.output).unwrap();
  let stamp = std::time::SystemTime::now()
    .duration_since(std::time::UNIX_EPOCH)
    .unwrap()
    .as_nanos();
  let directory = std::env::temp_dir()
    .join(format!("ix-aiur-plonk-retained-{}-{stamp}", std::process::id()));
  std::fs::create_dir(&directory).unwrap();
  let circuit = directory.join("compiled.bin");
  let info = gnark::compile(exporter.schema(), &circuit).unwrap();
  let bytes = std::fs::read(&circuit).unwrap();
  let hash = gnark::Artifact {
    sha256: format!("{:x}", Sha256::digest(&bytes)),
    bytes: bytes.len() as u64,
  };
  let output = directory.join("prepared");
  let manifest = gnark::prepare(&gnark::Preparation {
    schema: exporter.schema(),
    circuit: &circuit,
    circuit_hash: &hash,
    info: &info,
    srs: &srs,
    srs_blake3: &receipt,
    lagrange: &directory.join("lagrange.bin"),
    lagrange_sha256: "",
    output: &output,
  })
  .unwrap();
  let key = std::fs::read(output.join("verifying-key.bin")).unwrap();
  let key_pin: [u8; 32] = Sha256::digest(&key).into();
  let anchors = gnark::anchors(
    &ix_proof_compression::pipeline::ignition_parameters().unwrap(),
  );
  let mut prover =
    gnark::Prover::open(&output, &manifest, gnark::Backend::Cpu).unwrap();
  for args in [args, [Bn254.zero(), Bn254.zero()]] {
    let record = plan.program().execute(entry, args.to_vec()).unwrap();
    let call = plan.public_args(&record, entry, &args).unwrap();
    let expected =
      plan.public_claim(entry, &call, &record.output).unwrap()[2..].to_vec();
    let witness = exporter.binary_witness(&record, &args).unwrap();
    let mut wrong = expected.clone();
    wrong[0] += Bn254.one();
    assert!(prover.prove(&witness, &wrong).is_err());
    let proof = prover.prove(&witness, &expected).unwrap();
    assert_eq!(proof.solidity.len(), 864);
    gnark::verify(&key, &key_pin, &proof.native, &expected, &anchors).unwrap();
    assert!(
      gnark::verify(&key, &key_pin, &proof.native, &wrong, &anchors).is_err()
    );
    let mut wrong_pin = key_pin;
    wrong_pin[0] ^= 1;
    assert!(
      gnark::verify(&key, &wrong_pin, &proof.native, &expected, &anchors)
        .is_err()
    );
    let mut wrong_anchors = anchors.clone();
    wrong_anchors[0] ^= 1;
    assert!(
      gnark::verify(&key, &key_pin, &proof.native, &expected, &wrong_anchors)
        .is_err()
    );
  }
  prover.close().unwrap();
  std::fs::remove_dir_all(directory).unwrap();
}
