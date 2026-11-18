//! Count an independently authenticated terminal input without proving traces.
//! The input manifest and compiler artifact pins are supplied separately.
use aiur::field::FieldBackend;
use ark_ec::{AffineRepr, pairing::Pairing};
use ark_ff::Zero;
use ark_serialize::CanonicalDeserialize;
use ix_proof_compression::aiur_backend::{
  Bn254, g1,
  kzg::Compiler,
  kzg_advice::{Inputs, MAX_BYTES},
  pairing::final_program::AccumulatorProgram,
  plonk::{MAX_DOMAIN, public_bytes},
};
use serde::Deserialize;
use std::{
  fs,
  path::{Path, PathBuf},
  time::Instant,
};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct File {
  path: PathBuf,
  blake3: String,
}

impl File {
  fn read(&self, directory: &Path) -> Result<Vec<u8>> {
    let path = if self.path.is_absolute() {
      self.path.clone()
    } else {
      directory.join(&self.path)
    };
    if fs::metadata(&path)?.len() > u64::try_from(MAX_BYTES)? {
      return Err("terminal source file exceeds 64 MiB".into());
    }
    let bytes = fs::read(path)?;
    if blake3::hash(&bytes) != blake3::Hash::from_hex(&self.blake3)? {
      return Err("terminal source file differs from its trusted pin".into());
    }
    Ok(bytes)
  }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
  format: String,
  key: File,
  claims: File,
  proof: File,
  policy: File,
  statement: String,
  stage: u32,
}

fn main() -> Result<()> {
  let args: Vec<_> = std::env::args().skip(1).collect();
  let [artifact, artifact_pin, manifest, manifest_pin, record_limit, output] =
    args.as_slice()
  else {
    return Err("usage: aiur_terminal_count ARTIFACT ARTIFACT_BLAKE3 INPUT_MANIFEST MANIFEST_BLAKE3 MAX_RECORD_BYTES NEW_OUTPUT".into());
  };
  let artifact = fs::read(artifact)?;
  let artifact_pin = blake3::Hash::from_hex(artifact_pin)?;
  let program =
    AccumulatorProgram::from_bytes(&artifact, artifact_pin.as_bytes())?;
  let manifest_path = Path::new(manifest);
  let manifest_bytes = fs::read(manifest_path)?;
  let manifest_pin = blake3::Hash::from_hex(manifest_pin)?;
  if blake3::hash(&manifest_bytes) != manifest_pin {
    return Err("terminal manifest differs from its independent pin".into());
  }
  let manifest: Manifest = serde_json::from_slice(&manifest_bytes)?;
  if manifest.format != "ix-aiur-terminal-input-v1" || manifest.stage == 0 {
    return Err("invalid terminal input manifest".into());
  }
  let directory = manifest_path.parent().unwrap_or_else(|| Path::new("."));
  let inputs = Inputs::new(
    manifest.key.read(directory)?,
    manifest.claims.read(directory)?,
    manifest.proof.read(directory)?,
    manifest.policy.read(directory)?,
  )?;
  let statement = blake3::Hash::from_hex(&manifest.statement)?;
  let output = Path::new(output);
  fs::create_dir(output)?;
  let started = Instant::now();
  let record = program.execute_with_record_limit(
    &inputs,
    statement.as_bytes(),
    manifest.stage,
    record_limit.parse()?,
  )?;
  let execution_seconds = started.elapsed().as_secs_f64();
  let table = program
    .plan()
    .program()
    .program()
    .tables
    .iter()
    .find(|table| table.name == "CompressFinal::configuration_outputs")
    .ok_or("missing fixed terminal configuration")?;
  if table.rows.len() != 1 || table.rows[0].len() != 138 {
    return Err("invalid terminal configuration layout".into());
  }
  let bytes = table.rows[0][8..136]
    .iter()
    .map(|&word| {
      u8::try_from(Bn254.try_to_u64(Bn254.from_word(word))?)
        .map_err(|error| error.to_string())
    })
    .collect::<std::result::Result<Vec<_>, String>>()?;
  let mut encoded = bytes.as_slice();
  let anchors = [
    ark_bn254::G2Affine::deserialize_compressed(&mut encoded)?,
    ark_bn254::G2Affine::deserialize_compressed(&mut encoded)?,
  ];
  if !encoded.is_empty() || anchors.iter().any(AffineRepr::is_zero) {
    return Err("invalid fixed terminal pairing anchors".into());
  }
  let points =
    [g1::decode(&record.output[..9])?, g1::decode(&record.output[9..])?];
  if !ark_bn254::Bn254::multi_pairing(points, anchors).is_zero() {
    return Err(
      "terminal source output fails the native pairing equation".into(),
    );
  }
  let private = public_bytes(&record.output)?;
  fs::write(output.join("private-outputs.bin"), &private)?;
  let compiler = Compiler::new(program.plan())?;
  let heights = compiler.row_counts(&record)?;
  let circuits: Vec<_> = compiler.inputs().iter().zip(compiler.names()).zip(&heights).map(|((input,name),height)|serde_json::json!({
    "name":name,"height":height,"main_width":input.main_width,"main_cells":height*input.main_width,
    "lookup_slots":height*input.lookups.len(),"fixed_cells":input.preprocessed.as_ref().map_or(0,|matrix|matrix.values.len())
  })).collect();
  let main_cells: usize = compiler
    .inputs()
    .iter()
    .zip(&heights)
    .map(|(input, height)| height * input.main_width)
    .sum();
  let functions = program.plan().function_chips().iter().enumerate().map(|(index,&chip)| {
    Ok(serde_json::json!({"name":program.plan().program().program().functions[index].name,
      "chip":program.plan().artifact().chips[chip].name,"rows":record.queries.callable_rows(index).ok_or("missing function rows")?}))
  }).collect::<std::result::Result<Vec<_>,String>>()?;
  let report = serde_json::json!({
    "format":"ix-aiur-terminal-count-v1",
    "scope":"Authenticated source execution and exact padded row counts only; no proving traces or full PLONK circuit allocated.",
    "artifact_blake3":artifact_pin.to_hex().as_str(),"manifest_blake3":manifest_pin.to_hex().as_str(),
    "statement":manifest.statement,"stage":manifest.stage,"instructions":record.instructions,
    "execution_seconds":execution_seconds,"record":record.storage_usage(),
    "main_cells":main_cells,"private_outputs":record.output.len(),"max_height":heights.iter().max(),
    "private_output_blake3":blake3::hash(&private).to_hex().as_str(),"native_pairing_verified":true,
    "within_2_24_main_cell_budget":main_cells+record.output.len()<=1<<24,
    "within_exporter_main_cell_limit":main_cells+record.output.len()<=MAX_DOMAIN,
    "actual_plonk_constraints_measured":false,"circuits":circuits,"function_rows":functions
  });
  fs::write(output.join("profile.json"), serde_json::to_vec_pretty(&report)?)?;
  println!(
    "{}",
    serde_json::to_string_pretty(
      &serde_json::json!({"main_cells":main_cells,"max_height":heights.iter().max(),"execution_seconds":execution_seconds})
    )?
  );
  Ok(())
}
