//! Provision an authenticated cache from stock Filecoin `challenge_19`.

use ix_proof_compression::kzg::srs::filecoin::{
  FILECOIN_CHALLENGE_19_BLAKE2B, FILECOIN_CHALLENGE_19_MIRROR_URL,
  FILECOIN_CHALLENGE_19_URL, FILECOIN_MAX_TRACE_LEN,
  FILECOIN_PUBLIC_MAX_DEGREE, filecoin_setup_id, import_filecoin_challenge,
  load_filecoin_cache,
};
use std::{path::Path, time::Instant};

fn main() -> Result<(), Box<dyn std::error::Error>> {
  fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
  }

  fn parse_digest(value: &str) -> Result<[u8; 32], Box<dyn std::error::Error>> {
    if value.len() != 64 || !value.is_ascii() {
      return Err("manifest digest must have 64 hexadecimal characters".into());
    }
    let mut digest = [0; 32];
    for (i, byte) in digest.iter_mut().enumerate() {
      *byte = u8::from_str_radix(&value[2 * i..2 * i + 2], 16)?;
    }
    Ok(digest)
  }

  fn prefix(log: &str) -> Result<usize, Box<dyn std::error::Error>> {
    let log: u32 = log.parse()?;
    if !(1..=27).contains(&log) {
      return Err("prefix log must be in 1..=27".into());
    }
    Ok(1usize << log)
  }

  let args: Vec<_> = std::env::args().skip(1).collect();
  let start = Instant::now();
  match args.iter().map(String::as_str).collect::<Vec<_>>().as_slice() {
        ["info"] => {
            println!("source_url={FILECOIN_CHALLENGE_19_URL}");
            println!("mirror_url={FILECOIN_CHALLENGE_19_MIRROR_URL}");
            println!("source_blake2b={}", hex(&FILECOIN_CHALLENGE_19_BLAKE2B));
            println!("public_max_degree={FILECOIN_PUBLIC_MAX_DEGREE}");
            println!("max_trace_len={FILECOIN_MAX_TRACE_LEN}");
            println!("setup_id={}", hex(&filecoin_setup_id()));
        }
        ["import", source, cache, log] => {
            let prefix_len = prefix(log)?;
            eprintln!("Reading the complete 72 GiB source and validating {prefix_len} retained G1 powers; this is one-time provisioning.");
            let receipt = import_filecoin_challenge(Path::new(source), Path::new(cache), prefix_len)?;
            println!("prefix_len={}", receipt.prefix_len);
            println!("manifest_blake3={}", hex(&receipt.digest));
            println!("setup_id={}", hex(&filecoin_setup_id()));
            eprintln!("Import completed in {:.3}s. Pin manifest_blake3 in trusted configuration; a digest read from an untrusted sidecar is not authentication.", start.elapsed().as_secs_f64());
        }
        ["verify", cache, digest, log] => {
            let srs = load_filecoin_cache(Path::new(cache), parse_digest(digest)?, prefix(log)?)?;
            println!("loaded_prefix_len={}", srs.g1.len());
            println!("public_max_degree={FILECOIN_PUBLIC_MAX_DEGREE}");
            println!("setup_id={}", hex(&filecoin_setup_id()));
            eprintln!("Authenticated prefix loaded in {:.3}s", start.elapsed().as_secs_f64());
        }
        _ => return Err(concat!(
            "usage: kzg_filecoin_import info\n",
            "       kzg_filecoin_import import <challenge_19> <new-cache> <log-prefix:1..27>\n",
            "       kzg_filecoin_import verify <cache> <trusted-manifest-blake3> <log-prefix:1..27>",
        ).into()),
    }
  Ok(())
}
