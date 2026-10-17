//! Prepare deterministic development parameters separately from proof timings.

use ix_proof_compression::kzg::{Scalar, Srs, curve};
use multi_stark::traits::TwoAdicField;
use std::{path::Path, time::Instant};

fn main() -> Result<(), Box<dyn std::error::Error>> {
  let args: Vec<_> = std::env::args().skip(1).collect();
  let [directory, log, seed] = args.as_slice() else {
    return Err(
      "usage: kzg_dev_srs <cache-directory> <log-powers> <seed>".into(),
    );
  };
  let log: usize = log.parse()?;
  if !(1..=Scalar::TWO_ADICITY).contains(&log) {
    return Err("unsupported SRS size".into());
  }
  let count =
    1usize.checked_shl(u32::try_from(log)?).ok_or("SRS size overflow")?;
  let started = Instant::now();
  let srs = Srs::unsafe_dev_setup_prefix_in_cache_directory(
    count,
    count - 1,
    seed.as_bytes(),
    Path::new(directory),
  )?;
  println!(
    "{}",
    serde_json::json!({
      "curve": curve::NAME,
      "known_trapdoor": true,
      "powers": count,
      "seed": seed,
      "public_max_degree": srs.public_setup.max_degree,
      "public_setup_id": blake3::Hash::from_bytes(srs.public_setup.id).to_hex().as_str(),
      "elapsed_seconds": started.elapsed().as_secs_f64(),
    })
  );
  Ok(())
}
