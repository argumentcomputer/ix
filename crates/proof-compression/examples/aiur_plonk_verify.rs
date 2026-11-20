//! Verify a terminal PLONK certificate of the compression pipeline against a
//! verifying key pinned by the caller and a statement the caller computed.
//!
//! ```text
//! aiur_plonk_verify VERIFYING_KEY KEY_BLAKE3 PROOF STATEMENT
//! ```
//!
//! - `VERIFYING_KEY`: the gnark PLONK verifying key (`verifying-key.bin` of the
//!   prepared terminal), which must hash to `KEY_BLAKE3`.
//! - `PROOF`: the native gnark proof (`plonk/proof.bin`, 584 bytes).
//! - `STATEMENT`: the 32-byte terminal statement as 64 hex digits. Its two
//!   little-endian 128-bit halves are the circuit's public inputs
//!   (`statement_arguments`, as the terminal stage derives them). Nothing in
//!   the proof or in a prover's files is read for them.
//!
//! The key's KZG anchors (`[1]G1`, `[1]G2`, `[τ]G2`) must be those of the
//! Ignition parameters this build bundles (`pipeline::ignition_parameters`,
//! the release recursive key), so a key set up over any other SRS, a
//! development SRS with a known trapdoor included, is refused.
//!
//! Output: `key ready: …` once the key is pinned and the anchors are loaded,
//! before the proof is read; then `ACCEPT: …` (exit 0) or `REJECT: …`
//! (exit 1). A failure before `key ready` exits 2.

#[cfg(not(feature = "plonk"))]
fn main() -> Result<(), Box<dyn std::error::Error>> {
  Err("aiur_plonk_verify requires --features plonk".into())
}

#[cfg(feature = "plonk")]
fn main() -> std::process::ExitCode {
  verify::main()
}

#[cfg(feature = "plonk")]
mod verify {
  use ix_proof_compression::{
    aiur_backend::{pairing::final_program::statement_arguments, plonk::gnark},
    pipeline::ignition_parameters,
  };
  use sha2::{Digest, Sha256};
  use std::{fs, process::ExitCode, time::Instant};

  fn hex32(s: &str) -> Result<[u8; 32], String> {
    if s.len() != 64 {
      return Err(format!("{s}: not 64 hex digits"));
    }
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
      *byte = u8::from_str_radix(&s[2 * i..2 * i + 2], 16)
        .map_err(|_| format!("{s}: not hexadecimal"))?;
    }
    Ok(out)
  }

  fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
  }

  pub(super) fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let [_, key_path, key_pin, proof_path, statement] = args.as_slice() else {
      eprintln!(
        "usage: aiur_plonk_verify VERIFYING_KEY KEY_BLAKE3 PROOF STATEMENT"
      );
      return ExitCode::from(2);
    };
    let setup = || -> Result<_, String> {
      let pin = hex32(key_pin)?;
      let statement = hex32(statement)?;
      let key = fs::read(key_path).map_err(|e| format!("{key_path}: {e}"))?;
      let parameters = ignition_parameters().map_err(|e| e.to_string())?;
      Ok((pin, statement, key, gnark::anchors(&parameters)))
    };
    let (pin, statement, key, anchors) = match setup() {
      Ok(v) => v,
      Err(e) => {
        eprintln!("error: {e}");
        return ExitCode::from(2);
      },
    };
    let key_blake3 = *blake3::hash(&key).as_bytes();
    if key_blake3 != pin {
      println!(
        "REJECT: verifying key {key_path} has BLAKE3 {}, not the pinned {}",
        hex(&key_blake3),
        hex(&pin)
      );
      return ExitCode::from(1);
    }
    let key_sha256: [u8; 32] = Sha256::digest(&key).into();
    println!(
      "key ready: verifying key BLAKE3 {} SHA-256 {} ({} bytes); anchors of the bundled Ignition parameters, BLAKE3 {}",
      hex(&key_blake3),
      hex(&key_sha256),
      key.len(),
      blake3::hash(&anchors).to_hex()
    );
    let arguments = statement_arguments(&statement);
    println!(
      "statement {}: public inputs {} {}",
      hex(&statement),
      arguments[0].0,
      arguments[1].0
    );
    let proof = match fs::read(proof_path) {
      Ok(p) => p,
      Err(e) => {
        println!("REJECT: {proof_path}: {e}");
        return ExitCode::from(1);
      },
    };
    let started = Instant::now();
    match gnark::verify(&key, &key_sha256, &proof, &arguments, &anchors) {
      Ok(()) => {
        println!(
          "ACCEPT: PLONK proof {} ({} bytes) verifies statement {} under key {} ({:.3} s)",
          blake3::hash(&proof).to_hex(),
          proof.len(),
          hex(&statement),
          hex(&key_blake3),
          started.elapsed().as_secs_f64()
        );
        ExitCode::SUCCESS
      },
      Err(e) => {
        println!("REJECT: {e}");
        ExitCode::from(1)
      },
    }
  }
}
