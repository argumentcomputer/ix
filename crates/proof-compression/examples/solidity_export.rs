//! Export a fixed Keccak KZG verifier and native conformance vectors.
use ix_proof_compression::pipeline::{
  export_solidity_verifier, write_solidity_fixture,
};
use std::path::Path;

fn main() -> Result<(), Box<dyn std::error::Error>> {
  let args: Vec<_> = std::env::args().skip(1).collect();
  match args.iter().map(String::as_str).collect::<Vec<_>>().as_slice() {
    ["fixture", dir, sol] => write_solidity_fixture(Path::new(dir), Path::new(sol)),
    ["export", verifier, packet, digest, dir, sol] => export_solidity_verifier(
      Path::new(verifier), Path::new(packet), digest, Path::new(dir), Path::new(sol)),
    _ => Err("usage: solidity_export fixture <output-dir> <GeneratedVerifier.sol> | export <verifier.bin> <packet.bin> <trusted-verifier-blake3> <output-dir> <GeneratedVerifier.sol>".into()),
  }
}
