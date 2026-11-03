use crate::protocol::{Kind, atomic_json};
use aiur::field::NativeField;
use aiur::trace::stark::{Backend, BatchProof};
use multi_stark::{p3_field::PrimeField64, types::Val};
use serde_json::{Value, json};
use std::path::Path;

pub fn report(output: &Path, kind: Kind, report: &Value) -> Result<(), String> {
  let path = match kind {
    Kind::Ixvm => {
      std::path::PathBuf::from(format!("{}.report.json", output.display()))
    },
    Kind::Recursion => {
      std::fs::create_dir_all(output).map_err(|e| e.to_string())?;
      output.join("report.json")
    },
  };
  atomic_json(&path, report)
}

/// Writes a verified proof, its verifying key and claims next to `output`
/// (an IxVM proof file, or a recursive proof's directory), and with
/// `export_input` the JSON invocation of a verifier over it.
#[allow(clippy::too_many_arguments)]
pub fn proof(
  output: &Path,
  export_input: bool,
  kind: Kind,
  backend: &Backend<'_, '_, NativeField<Val>>,
  entry: &str,
  args: &[Val],
  proof: &BatchProof,
  mut result: Value,
) -> Result<Value, String> {
  let key = backend.verifying_key_bytes()?;
  let claims =
    stark_verifier::claims_bytes(&[backend.claim(entry, args, &[])?]);
  let raw = proof.to_bytes().map_err(|e| e.to_string())?;
  let write = |path: std::path::PathBuf, bytes: &[u8]| {
    std::fs::write(path, bytes).map_err(|e| e.to_string())
  };
  match kind {
    Kind::Ixvm => {
      let mut bytes = b"IXAIUR2\0".to_vec();
      bytes.extend_from_slice(&raw);
      write(output.to_path_buf(), &bytes)?;
      write(format!("{}.vk", output.display()).into(), &key)?;
      write(format!("{}.claims", output.display()).into(), &claims)?;
    },
    Kind::Recursion => {
      std::fs::create_dir_all(output).map_err(|e| e.to_string())?;
      write(output.join("proof.bin"), &raw)?;
      write(output.join("key.bin"), &key)?;
      write(output.join("claims.bin"), &claims)?;
      atomic_json(
        &output.join("public.json"),
        &json!({"entry":entry, "args":args.iter().map(Val::as_canonical_u64).collect::<Vec<_>>()}),
      )?;
      if export_input {
        atomic_json(
          &output.join("input.json"),
          &stark_verifier::invocation(&key, &claims, &raw),
        )?;
      }
    },
  }
  result["verified"] = true.into();
  result["shards"] = proof.proofs.len().into();
  result["proof_bytes"] = raw.len().into();
  result["key_digest"] = blake3::hash(&key).to_hex().to_string().into();
  report(output, kind, &result)?;
  Ok(result)
}
