//! Tools over the prover library for the check scripts.
//!
//! `ranges PROOF OUTPUT SIZE` writes the range advice of a raw proof:
//! `preamble.bin`, `ranges.json` and per node `N.statement`, with `N.proofs`
//! for leaves.
use ix_prover::{protocol::atomic_json, tools};
use serde_json::json;
use std::path::Path;

fn ranges(proof: &Path, out: &Path, size: &str) -> Result<(), String> {
  let size: usize = size.parse().map_err(|e| format!("range size: {e}"))?;
  let bytes = std::fs::read(proof).map_err(|e| e.to_string())?;
  let (preamble, nodes) = tools::ranges(&bytes, size)?;
  std::fs::create_dir_all(out).map_err(|e| e.to_string())?;
  let write = |name: String, bytes: &[u8]| {
    std::fs::write(out.join(name), bytes).map_err(|e| e.to_string())
  };
  write("preamble.bin".into(), &preamble)?;
  for (id, node) in nodes.iter().enumerate() {
    write(format!("{id}.statement"), &node.statement)?;
    if node.children.is_empty() {
      write(format!("{id}.proofs"), &node.proofs)?;
    }
  }
  let specs: Vec<_> = nodes
    .iter()
    .map(|n| json!({"lo":n.lo, "hi":n.hi, "children":n.children}))
    .collect();
  atomic_json(&out.join("ranges.json"), &specs)
}

fn main() {
  let args: Vec<String> = std::env::args().collect();
  let result = match args.get(1).map(String::as_str) {
    Some("ranges") if args.len() == 5 => {
      ranges(Path::new(&args[2]), Path::new(&args[3]), &args[4])
    },
    _ => Err("usage: ix-prover ranges PROOF OUTPUT SIZE".into()),
  };
  if let Err(error) = result {
    eprintln!("ix-prover: {error}");
    std::process::exit(1);
  }
}
