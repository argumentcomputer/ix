use crate::protocol::{Job, Kind, atomic_json};
use aiur::field::NativeField;
use aiur::trace::stark::{Backend, BatchProof};
use multi_stark::{p3_field::PrimeField64, types::Val};
use serde_json::{Value, json};

pub fn report(job: &Job, kind: Kind, report: &Value) -> Result<(), String> {
  let path = match kind {
    Kind::Ixvm => {
      std::path::PathBuf::from(format!("{}.report.json", job.output.display()))
    },
    Kind::Recursion => {
      std::fs::create_dir_all(&job.output).map_err(|e| e.to_string())?;
      job.output.join("report.json")
    },
  };
  atomic_json(&path, report)
}

pub fn proof(
  job: &Job,
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
      write(job.output.clone(), &bytes)?;
      write(format!("{}.vk", job.output.display()).into(), &key)?;
      write(format!("{}.claims", job.output.display()).into(), &claims)?;
    },
    Kind::Recursion => {
      std::fs::create_dir_all(&job.output).map_err(|e| e.to_string())?;
      write(job.output.join("proof.bin"), &raw)?;
      write(job.output.join("key.bin"), &key)?;
      write(job.output.join("claims.bin"), &claims)?;
      atomic_json(
        &job.output.join("public.json"),
        &json!({"entry":entry, "args":args.iter().map(Val::as_canonical_u64).collect::<Vec<_>>()}),
      )?;
      atomic_json(
        &job.output.join("input.json"),
        &stark_verifier::invocation(&key, &claims, &raw),
      )?;
    },
  }
  result["verified"] = true.into();
  result["shards"] = proof.proofs.len().into();
  result["proof_bytes"] = raw.len().into();
  result["key_digest"] = blake3::hash(&key).to_hex().to_string().into();
  report(job, kind, &result)?;
  Ok(result)
}
