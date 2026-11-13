//! Size the complete terminal relation with gnark's constrained pairing gadget.
//! The predecessor is a development regression, not an Init compression proof.

#[path = "aiur_final_fixture/input.rs"]
mod input;
#[cfg(feature = "plonk")]
#[path = "aiur_pairing_profile/plonk_cost.rs"]
mod plonk_cost;

use ix_proof_compression::aiur_backend::{
  kzg::Compiler,
  pairing::final_program::{
    ACCUMULATOR_ENTRY, AccumulatorProgram, statement_arguments,
  },
  plonk::Exporter,
};
use std::{fs, path::Path, time::Instant};

fn main() -> Result<(), Box<dyn std::error::Error>> {
  let args: Vec<_> = std::env::args().skip(1).collect();
  let [artifact, output, flags @ ..] = args.as_slice() else {
    return Err("usage: aiur_terminal_profile ARTIFACT NEW_OUTPUT [--compile-plonk] [--estimate-plonk]".into());
  };
  if flags.iter().any(|flag| {
    !matches!(flag.as_str(), "--compile-plonk" | "--estimate-plonk")
  }) {
    return Err("unsupported terminal profile option".into());
  }
  let out = Path::new(output);
  fs::create_dir(out)?;
  let bytes = fs::read(artifact)?;
  let pin = blake3::hash(&bytes);
  let program = AccumulatorProgram::from_bytes(&bytes, pin.as_bytes())?;
  let fixture = input::Fixture::new();
  let _ = &fixture.forged_opening;
  let started = Instant::now();
  let record = program.execute(&fixture.inputs(), &fixture.statement, 1)?;
  let execution_seconds = started.elapsed().as_secs_f64();
  let arguments = statement_arguments(&fixture.statement);
  let compiler = Compiler::new(program.plan())?;
  let capacities: Vec<_> = compiler
    .row_counts(&record)?
    .into_iter()
    .map(|height| height.max(1))
    .collect();
  let public =
    program.plan().public_args(&record, ACCUMULATOR_ENTRY, &arguments)?;
  let exporter = Exporter::terminal(
    program.plan(),
    &capacities,
    &public,
    &record.output,
    &fixture.configuration,
  )?;
  let schema = serde_json::to_vec(exporter.schema())?;
  fs::write(out.join("schema.json"), &schema)?;
  #[cfg_attr(not(feature = "plonk"), allow(unused_mut))]
  let mut report = serde_json::json!({
    "format":"ix-aiur-terminal-gadget-cost-v1",
    "scope":"Development predecessor; complete terminal relation uses gnark PairingCheck. Not Init compression.",
    "artifact_blake3":pin.to_hex().as_str(),"execution_seconds":execution_seconds,
    "main_cells":compiler.inputs().iter().zip(&capacities).map(|(input,rows)|input.main_width*rows).sum::<usize>(),
    "max_height":capacities.iter().max(),"public_fields":exporter.schema().public_inputs,
    "private_outputs":exporter.schema().private_outputs,"schema_bytes":schema.len()
  });
  fs::write(out.join("cost.json"), serde_json::to_vec_pretty(&report)?)?;
  if !flags.is_empty() {
    #[cfg(feature = "plonk")]
    {
      if flags.iter().any(|flag| flag == "--estimate-plonk") {
        report["plonk_estimate"] =
          plonk_cost::estimate(exporter.schema(), out)?;
      }
      if flags.iter().any(|flag| flag == "--compile-plonk") {
        let started = Instant::now();
        let info = ix_proof_compression::aiur_backend::plonk::gnark::compile(
          exporter.schema(),
          &out.join("circuit.bin"),
        )?;
        report["plonk"] = serde_json::json!({"constraints":info.constraints,"domain":info.domain,"public_inputs":info.public_inputs,"commitments":info.commitments,"compile_seconds":started.elapsed().as_secs_f64(),"within_target_domain":info.domain<=1<<24});
      }
    }
    #[cfg(not(feature = "plonk"))]
    return Err("PLONK compilation requires --features plonk".into());
  }
  fs::write(out.join("cost.json"), serde_json::to_vec_pretty(&report)?)?;
  println!("{}", serde_json::to_string_pretty(&report)?);
  Ok(())
}
