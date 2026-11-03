use aiur::trace::stark::planning::Options;
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

#[derive(Clone, Copy, Debug, Deserialize, Serialize)]
#[serde(rename_all = "lowercase")]
pub(crate) enum Kind {
  Ixvm,
  Recursion,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Artifact {
  pub(crate) path: PathBuf,
  pub(crate) kind: Kind,
  /// The BLAKE3 digest the artifact must have (`aiur::artifact::Digest`).
  pub(crate) digest: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Config {
  pub(crate) artifacts: Vec<Artifact>,
  pub(crate) devices: Vec<Option<i32>>,
  pub(crate) exec_jobs: usize,
  pub(crate) threads_per_prover: usize,
  pub(crate) max_ram_bytes: u64,
  #[serde(default)]
  pub(crate) record_limit_bytes: Option<usize>,
  #[serde(default)]
  pub(crate) parent_pid: Option<u32>,
  #[serde(default)]
  pub(crate) texray: bool,
  /// Workspace reserved per CUDA lane, instead of the size derived from
  /// the committed-cell limit.
  #[serde(default)]
  pub workspace_per_lane_bytes: Option<u64>,
}

#[derive(Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Job {
  pub(crate) id: String,
  pub(crate) artifact: PathBuf,
  pub(crate) input: PathBuf,
  pub(crate) output: PathBuf,
  #[serde(default)]
  pub(crate) options: Options,
  #[serde(default)]
  pub(crate) priority: bool,
}

pub(crate) fn atomic_json(
  path: &Path,
  value: &impl Serialize,
) -> Result<(), String> {
  use std::io::Write;
  let tmp = path.with_extension(format!("tmp.{}", std::process::id()));
  // Recursive inputs encode each proof byte as a JSON number. Without a
  // buffer every token is its own write syscall: seconds per proof.
  let mut file = std::io::BufWriter::new(
    std::fs::File::create(&tmp).map_err(|e| e.to_string())?,
  );
  serde_json::to_writer(&mut file, value).map_err(|e| e.to_string())?;
  file.flush().map_err(|e| e.to_string())?;
  drop(file);
  std::fs::rename(tmp, path).map_err(|e| e.to_string())
}

pub(crate) fn read_json<T: serde::de::DeserializeOwned>(
  path: &Path,
) -> Result<T, String> {
  let file = std::fs::File::open(path)
    .map_err(|e| format!("{}: {e}", path.display()))?;
  serde_json::from_reader(std::io::BufReader::new(file))
    .map_err(|e| format!("{}: {e}", path.display()))
}
