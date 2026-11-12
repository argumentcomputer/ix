//! Deterministic test-only predecessor and fixed terminal configuration.
//! The development setup is unsuitable for production verification.

#[path = "aiur_final_fixture/input.rs"]
mod input;

fn main() -> Result<(), Box<dyn std::error::Error>> {
  let args: Vec<_> = std::env::args_os().skip(1).collect();
  if args.len() != 1 {
    return Err("usage: aiur_final_fixture NEW_DIRECTORY".into());
  }
  let directory = std::path::PathBuf::from(&args[0]);
  std::fs::create_dir(&directory)?;
  let fixture = input::Fixture::new();
  let _ = fixture.inputs();
  for (name, bytes) in [
    ("configuration.json", fixture.configuration.to_json()?),
    ("key.bin", fixture.key),
    ("claims.bin", fixture.claims),
    ("proof.bin", fixture.proof),
    ("policy.bin", fixture.policy),
    ("forged-opening.bin", fixture.forged_opening),
    ("statement.bin", fixture.statement.to_vec()),
  ] {
    std::fs::write(directory.join(name), bytes)?;
  }
  println!("test-only terminal configuration: {}", directory.display());
  Ok(())
}
