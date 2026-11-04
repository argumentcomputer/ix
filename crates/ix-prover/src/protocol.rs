pub use crate::request::Request;
pub use aiur::trace::stark::planning::{Options, RetentionPolicy};
use serde::{Deserialize, Serialize};
use std::path::Path;

#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum Kind {
  Ixvm,
  Recursion,
}

pub fn atomic_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
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

pub fn read_json<T: serde::de::DeserializeOwned>(
  path: &Path,
) -> Result<T, String> {
  let file = std::fs::File::open(path)
    .map_err(|e| format!("{}: {e}", path.display()))?;
  serde_json::from_reader(std::io::BufReader::new(file))
    .map_err(|e| format!("{}: {e}", path.display()))
}
