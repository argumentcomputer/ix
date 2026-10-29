use aiur::trace::stark::planning::Options;
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

#[derive(Clone, Copy, Debug, Deserialize, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Kind {
  Ixvm,
  Recursion,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Artifact {
  pub path: PathBuf,
  pub kind: Kind,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Config {
  pub artifacts: Vec<Artifact>,
  pub devices: Vec<Option<i32>>,
  pub exec_jobs: usize,
  pub threads_per_prover: usize,
  pub max_ram_bytes: u64,
  #[serde(default)]
  pub record_limit_bytes: Option<usize>,
  #[serde(default)]
  pub parent_pid: Option<u32>,
  #[serde(default)]
  pub texray: bool,
}

#[derive(Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Job {
  pub id: String,
  pub artifact: PathBuf,
  pub input: PathBuf,
  pub output: PathBuf,
  #[serde(default)]
  pub options: Options,
  #[serde(default)]
  pub priority: bool,
}

pub fn atomic_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
  let tmp = path.with_extension(format!("tmp.{}", std::process::id()));
  let file = std::fs::File::create(&tmp).map_err(|e| e.to_string())?;
  serde_json::to_writer(file, value).map_err(|e| e.to_string())?;
  std::fs::rename(tmp, path).map_err(|e| e.to_string())
}

pub fn read_json<T: serde::de::DeserializeOwned>(
  path: &Path,
) -> Result<T, String> {
  let file = std::fs::File::open(path)
    .map_err(|e| format!("{}: {e}", path.display()))?;
  serde_json::from_reader(std::io::BufReader::new(file))
    .map_err(|e| format!("{}: {e}", path.display()))
}
