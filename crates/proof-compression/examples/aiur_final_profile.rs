//! Size and prove the deterministic terminal-verifier regression. Its setup
//! and predecessor key are test fixtures, not production authorization.

#[path = "aiur_final_fixture/input.rs"]
mod input;

use ix_proof_compression::{
  aiur_backend::{
    kzg::{Backend, Compiler},
    pairing::final_program::{ENTRY, Program, statement_arguments},
  },
  kzg::{KzgConfig, Srs},
};
use std::{fs, path::PathBuf, sync::Arc, time::Instant};

fn main() -> Result<(), Box<dyn std::error::Error>> {
  let args: Vec<_> = std::env::args().skip(1).collect();
  if args.len() < 2
    || args[2..].iter().any(|flag| !matches!(flag.as_str(), "--prove-kzg"))
  {
    return Err(
      "usage: aiur_final_profile ARTIFACT NEW_OUTPUT [--prove-kzg]".into(),
    );
  }
  let directory = PathBuf::from(&args[1]);
  fs::create_dir(&directory)?;
  let bytes = fs::read(&args[0])?;
  let fixture = input::Fixture::new();
  if fixture.configuration.to_json()?
    != include_bytes!("../../aiur/tests/fixtures/compress-final.json")
  {
    return Err("terminal fixture configuration drift".into());
  }
  // The explicit artifact path selects a local sizing input, not a deployed key.
  let program = Program::from_bytes(&bytes, blake3::hash(&bytes).as_bytes())?;
  let start = Instant::now();
  let record = program.execute(&fixture.inputs(), &fixture.statement, 1)?;
  let execution = start.elapsed().as_secs_f64();
  let inputs = statement_arguments(&fixture.statement);
  let compiler = Compiler::new(program.plan())?;
  let capacities: Vec<_> = compiler
    .row_counts(&record)?
    .into_iter()
    .map(|height| height.max(1))
    .collect();
  let cells: usize = capacities
    .iter()
    .zip(compiler.inputs())
    .map(|(height, input)| height * input.main_width)
    .sum();
  let mut report = serde_json::json!({
    "format":"ix-aiur-final-fixture-cost-v1", "scope":"development regression, not Init compression",
    "artifact_blake3":blake3::hash(&bytes).to_hex().as_str(),
    "execution_seconds":execution,"main_cells":cells,"max_height":capacities.iter().max(),
    "public_fields":program.plan().public_claim(ENTRY, &program.plan().public_args(&record, ENTRY, &inputs)?, &record.output)?.len() - 2,
  });
  fs::write(directory.join("cost.json"), serde_json::to_vec_pretty(&report)?)?;
  if args.iter().any(|flag| flag == "--prove-kzg") {
    let height = *capacities.iter().max().ok_or("empty final capacity")?;
    let srs =
      Arc::new(Srs::unsafe_dev_setup(height, b"aiur-final-outer-test-only"));
    let backend = Backend::new(program.plan(), KzgConfig::new(srs, 8))?;
    let start = Instant::now();
    let witness = backend.generate(&record, ENTRY, &inputs)?;
    let proof = backend.prove(ENTRY, &inputs, &record.output, witness)?;
    backend.verify(ENTRY, &inputs, &record.output, &proof)?;
    let mut changed = fixture.statement;
    changed[31] ^= 1;
    if backend
      .verify(ENTRY, &statement_arguments(&changed), &record.output, &proof)
      .is_ok()
    {
      return Err("terminal proof accepted a changed statement".into());
    }
    report["kzg_prove_seconds"] = start.elapsed().as_secs_f64().into();
    fs::write(
      directory.join("cost.json"),
      serde_json::to_vec_pretty(&report)?,
    )?;
  }
  fs::write(directory.join("cost.json"), serde_json::to_vec_pretty(&report)?)?;
  println!("{}", serde_json::to_string_pretty(&report)?);
  let _ = fixture.forged_opening;
  Ok(())
}
