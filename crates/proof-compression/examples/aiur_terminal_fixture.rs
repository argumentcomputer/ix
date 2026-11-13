//! Terminal-backend fixtures from the actual deferred Aiur verifier program.
//! The predecessor is a deterministic development proof, not an Init proof.

#[path = "aiur_final_fixture/input.rs"]
mod input;

use ix_proof_compression::aiur_backend::{
  kzg::Compiler,
  kzg_advice::Inputs,
  pairing::final_program::{
    ACCUMULATOR_ENTRY, AccumulatorProgram, statement_arguments,
  },
  plonk::{Exporter, public_bytes},
};
use std::{fs, path::Path};

fn main() -> Result<(), Box<dyn std::error::Error>> {
  let args: Vec<_> = std::env::args().skip(1).collect();
  let [artifact, output] = args.as_slice() else {
    return Err(
      "usage: aiur_terminal_fixture ACCUMULATOR_ARTIFACT NEW_OUTPUT".into(),
    );
  };
  let bytes = fs::read(artifact)?;
  let pin = blake3::hash(&bytes);
  let program = AccumulatorProgram::from_bytes(&bytes, pin.as_bytes())?;
  let fixture = input::Fixture::new();
  let out = Path::new(output);
  fs::create_dir(out)?;
  let arguments = statement_arguments(&fixture.statement);
  let compiler = Compiler::new(program.plan())?;
  let mut reports = vec![];
  let forged = Inputs::new(
    fixture.key.clone(),
    fixture.claims.clone(),
    fixture.forged_opening.clone(),
    fixture.policy.clone(),
  )?;
  for (name, inputs) in [("honest", fixture.inputs()), ("forged", forged)] {
    let record = program.execute(&inputs, &fixture.statement, 1)?;
    let capacities: Vec<_> =
      compiler.row_counts(&record)?.into_iter().map(|n| n.max(1)).collect();
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
    let witness = exporter.binary_witness(&record, &arguments)?;
    fs::write(out.join(format!("{name}-schema.json")), &schema)?;
    fs::write(out.join(format!("{name}-witness.bin")), &witness)?;
    fs::write(
      out.join(format!("{name}-private.bin")),
      public_bytes(&record.output)?,
    )?;
    reports.push(serde_json::json!({
      "case":name,"source_execution_passed":true,
      "public_inputs":exporter.schema().public_inputs,
      "private_outputs":exporter.schema().private_outputs,
      "schema_bytes":schema.len(),"witness_bytes":witness.len(),
      "schema_blake3":blake3::hash(&schema).to_hex().as_str(),
      "main_cells":compiler.inputs().iter().zip(&capacities).map(|(input,rows)|input.main_width*rows).sum::<usize>(),
      "max_height":capacities.iter().max()
    }));
  }
  fs::write(out.join("public.bin"), public_bytes(&arguments)?)?;
  let report = serde_json::json!({
    "format":"ix-aiur-terminal-gadget-fixture-v1",
    "scope":"Development predecessor; source execution defers pairing. The constrained terminal backend must reject the forged-opening case.",
    "artifact_blake3":pin.to_hex().as_str(),"cases":reports
  });
  fs::write(out.join("report.json"), serde_json::to_vec_pretty(&report)?)?;
  println!("{}", serde_json::to_string_pretty(&report)?);
  Ok(())
}
