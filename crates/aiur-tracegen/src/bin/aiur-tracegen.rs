//! `aiur-tracegen ARTIFACT [OUT_DIR] [SELECTION]`: describe a binary
//! compiler artifact and emit its compiled row writers. Prints the
//! fingerprint and the compiled and skipped circuits; with `OUT_DIR`, writes the CUDA units
//! and the description there. `SELECTION` is `all` or a JSON array of
//! circuit names.
use aiur_tracegen::cuda::{Selection, emit};
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
  let args: Vec<String> = std::env::args().collect();
  let artifact =
    args.get(1).ok_or("usage: aiur-tracegen ARTIFACT [OUT_DIR] [SELECTION]")?;
  let artifact = aiur_tracegen::describe_file(std::path::Path::new(artifact))?;
  let selection = match args.get(3).map(String::as_str) {
    None | Some("all") => Selection::All,
    Some(names) => Selection::Named(serde_json::from_str(names)?),
  };
  let emitted = emit(&artifact, &selection, "cli")?;
  println!("fingerprint {}", artifact.fingerprint);
  for c in &emitted.circuits {
    println!(
      "compiled {} ({} members, {} bytes of CUDA)",
      c.name,
      c.members.len(),
      c.source.len()
    );
  }
  for (name, reason) in &emitted.skipped {
    println!("skipped {name}: {reason}");
  }
  if let Some(dir) = args.get(2) {
    let dir = std::path::Path::new(dir);
    std::fs::create_dir_all(dir)?;
    std::fs::write(
      dir.join("description.json"),
      serde_json::to_vec(&artifact.description)?,
    )?;
    for c in &emitted.circuits {
      std::fs::write(dir.join(&c.file), &c.source)?;
    }
  }
  Ok(())
}
