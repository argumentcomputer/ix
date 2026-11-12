//! Export a compiler-produced recursion/map/ROM regression for the generic
//! PLONK frontend. The emitted statement is a typed Aiur call.

use aiur::{artifact::WidePackage, field::FieldBackend, trace::TracePlan};
use ix_proof_compression::aiur_backend::{
  Bn254, kzg::Compiler, plonk::Exporter,
};
use p3_matrix::Matrix;
use std::{path::PathBuf, sync::Arc};

fn main() -> Result<(), Box<dyn std::error::Error>> {
  let args: Vec<_> = std::env::args().skip(1).collect();
  if args.len() != 1 && args.len() != 3 {
    return Err(
      "usage: aiur_plonk_fixture OUTPUT_DIRECTORY [--srs-domain POWER_OF_TWO]"
        .into(),
    );
  }
  let directory = PathBuf::from(&args[0]);
  if args.len() == 3 {
    if args[1] != "--srs-domain" {
      return Err("expected --srs-domain".into());
    }
    #[cfg(feature = "plonk")]
    {
      let setup = ix_proof_compression::pipeline::SetupConfig::from_env(false)?;
      ix_proof_compression::pipeline::plonk::export_parameters(
        args[2].parse()?,
        &directory.join("srs.bin"),
        &setup,
      )?;
      return Ok(());
    }
    #[cfg(not(feature = "plonk"))]
    return Err("SRS export requires --features plonk".into());
  }
  std::fs::create_dir(&directory)?;
  let package = WidePackage::decode(include_bytes!(
    "../../aiur/tests/fixtures/bn254-trace.ixa"
  ))?;
  let trace = package.trace.ok_or("missing compiler trace")?;
  let mut program = package.program.check_with(Bn254)?;
  program.track_depth(&trace)?;
  let plan = TracePlan::new(Arc::new(program), trace)?;
  let entry = "BN254Trace::run";
  let args = [Bn254.from_u64(3), Bn254.neg(Bn254.one())];
  let record = plan.program().execute(entry, args.to_vec())?;
  let public = plan.public_args(&record, entry, &args)?;
  let compiler = Compiler::new(&plan)?;
  let traces = compiler.generate(&record, entry, &args)?;
  let capacities: Vec<_> =
    traces.iter().map(|trace| trace.height().max(1)).collect();
  let exporter =
    Exporter::new(&plan, &capacities, entry, &public, &record.output)?;
  std::fs::write(
    directory.join("schema.json"),
    serde_json::to_vec_pretty(exporter.schema())?,
  )?;
  std::fs::write(
    directory.join("witness.json"),
    serde_json::to_vec_pretty(&exporter.witness(&record, &args)?)?,
  )?;
  let layout = plan.layout()?;
  let (chip_index, chip) = plan
    .artifact()
    .chips
    .iter()
    .enumerate()
    .find(|(_, chip)| chip.depth.column.is_some())
    .ok_or("missing recursive chip")?;
  let placement = &layout.placements[chip_index];
  let mutations = serde_json::json!({
    "depth": [placement.circuit, placement.columns[chip.depth.column.unwrap()]],
    "activation": [placement.circuit, placement.selector],
    "multiplicity": [placement.circuit, traces[placement.circuit].width - 1],
    "rom_count": [compiler.names().iter().position(|name| name.starts_with("<ROM:")).unwrap(), 0],
    "rom_address": [compiler.names().iter().position(|name| name.starts_with("<ROM:")).unwrap(), 2],
    "rom_value": [compiler.names().iter().position(|name| name.starts_with("<ROM:")).unwrap(), 3],
    "map_count": [compiler.names().iter().position(|name| name.starts_with("<table:")).unwrap(), 0],
  });
  std::fs::write(
    directory.join("mutations.json"),
    serde_json::to_vec_pretty(&mutations)?,
  )?;
  println!(
    "Aiur PLONK fixture: {} circuits, capacities {:?}, {} public fields",
    capacities.len(),
    capacities,
    exporter.schema().public_inputs
  );
  Ok(())
}
