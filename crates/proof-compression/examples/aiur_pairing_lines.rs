//! Generate immutable prepared-line fixtures from independently chosen G2 anchors.

use ark_bn254::G2Affine;
use ark_ec::AffineRepr;
use ark_serialize::CanonicalSerialize;
use ix_proof_compression::{
  aiur_backend::pairing, recursive::native_field::integer,
};
use std::{fs, path::PathBuf};

fn main() -> Result<(), Box<dyn std::error::Error>> {
  let directory = PathBuf::from(
    std::env::args().nth(1).ok_or("usage: aiur_pairing_lines NEW_DIRECTORY")?,
  );
  fs::create_dir(&directory)?;
  let ignition = std::env::args().any(|arg| arg == "--ignition");
  let parameters = if ignition {
    Some(ix_proof_compression::pipeline::ignition_parameters()?)
  } else {
    None
  };
  let anchors =
    parameters.as_ref().map_or([G2Affine::generator(); 2], |parameters| {
      pairing::verifier_anchors(parameters).1
    });
  let rows = pairing::fixed_lines(anchors)?;
  let lines = rows
    .iter()
    .map(|row| {
      row
        .iter()
        .map(|value| integer(*value).to_string())
        .collect::<Vec<_>>()
        .join(" ")
    })
    .collect::<Vec<_>>()
    .join("\n")
    + "\n";
  fs::write(directory.join("lines.txt"), &lines)?;
  let mut encoded = vec![];
  for point in anchors {
    point.serialize_compressed(&mut encoded)?;
  }
  fs::write(directory.join("anchors.bin"), &encoded)?;
  let provenance = serde_json::json!({
    "format":"ix-aiur-bn254-fixed-lines-v1",
    "anchors": if ignition { "released Ignition G2/tauG2 anchors" } else { "two copies of ark-bn254 0.5.0 G2 generator" },
    "verifier_parameters_blake3": parameters.as_ref().map(|parameters| parameters.to_bytes().map(|bytes| blake3::hash(&bytes).to_hex().to_string())).transpose()?,
    "anchor_blake3":blake3::hash(&encoded).to_hex().as_str(),
    "anchor_bytes":encoded,
    "anchor_coordinates":anchors.map(|point| [point.x.c0.to_string(),point.x.c1.to_string(),point.y.c0.to_string(),point.y.c1.to_string()]),
    "lines_blake3":blake3::hash(lines.as_bytes()).to_hex().as_str(),
    "rows":rows.len(),"fields_per_row":51,
    "field_limb_bits":80,"prepared_source":"ark-ec 0.5.0 bn::G2Prepared"
  });
  fs::write(
    directory.join("provenance.json"),
    serde_json::to_vec_pretty(&provenance)?,
  )?;
  println!("prepared {} authenticated constant rows", rows.len());
  Ok(())
}
