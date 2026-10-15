//! Stage output files: bincode metadata and atomic file publication.
use super::fixed_cache::Shape;
use crate::kzg::Scalar;
use multi_stark::plonkish::MultiStarkCircuit;
use serde::{Serialize, de::DeserializeOwned};
use std::{
  fs::{self, File},
  io::{self, BufReader, BufWriter, Read, Write},
  path::{Path, PathBuf},
  sync::atomic::{AtomicU64, Ordering},
};

pub(crate) type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

/// The shape and public claims of a stage's proof, which the next stage
/// needs to rebuild the verifier.
#[derive(serde::Serialize, serde::Deserialize)]
pub(crate) struct Manifest {
  pub(crate) widths: Vec<usize>,
  pub(crate) heights: Vec<usize>,
  pub(crate) claims: Vec<Vec<Scalar>>,
}

impl Manifest {
  /// The manifest of a compiled circuit, checked against the shape of a
  /// restored fixed-preprocessing cache entry when there is one.
  pub(crate) fn for_compiled(
    compiled: &MultiStarkCircuit<Scalar>,
    claims: Vec<Vec<Scalar>>,
    cached: Option<&Shape>,
  ) -> Result<Self> {
    let mut manifest = Self { widths: vec![], heights: vec![], claims };
    if cached.is_some_and(|shape| {
      shape.widths.len() != compiled.num_circuits()
        || shape.heights.len() != compiled.num_circuits()
    }) {
      return Err(
        "cached trace count differs from the compiled circuit".into(),
      );
    }
    for i in 0..compiled.num_circuits() {
      let (height, width) =
        compiled.trace_dimensions(i).ok_or("missing compiled trace")?;
      if let Some(shape) = cached
        && (shape.widths[i] != width || shape.heights[i] != height)
      {
        return Err(
          "cached fixed trace dimensions differ from the compiled circuit"
            .into(),
        );
      }
      manifest.widths.push(width);
      manifest.heights.push(height);
    }
    Ok(manifest)
  }
}

/// A staging path beside `path` that no other writer, in this process or
/// another, stages to. The suffix follows the whole file name, so a partial
/// file left behind by a crash never carries the name or extension of a
/// finished one.
pub(crate) fn temporary_path(path: &Path) -> PathBuf {
  static NEXT: AtomicU64 = AtomicU64::new(0);
  let mut name =
    path.file_name().map_or_else(Default::default, ToOwned::to_owned);
  name.push(format!(
    ".partial-{}-{}",
    std::process::id(),
    NEXT.fetch_add(1, Ordering::Relaxed)
  ));
  path.with_file_name(name)
}

/// Move a completely written `temporary` file to `path` so that both its
/// contents and the rename survive a crash: the temporary is synced before
/// the rename and the containing directory after it.
pub(crate) fn persist(temporary: &Path, path: &Path) -> io::Result<()> {
  File::open(temporary)?.sync_all()?;
  fs::rename(temporary, path)?;
  sync_directory(path.parent().unwrap_or_else(|| Path::new(".")))
}

pub(crate) fn sync_directory(directory: &Path) -> io::Result<()> {
  let directory =
    if directory.as_os_str().is_empty() { Path::new(".") } else { directory };
  File::open(directory)?.sync_all()
}

/// Write `bytes` to `path` through a staged file, so a crash leaves either
/// the previous file or the complete new one.
pub(crate) fn write_atomic(path: &Path, bytes: &[u8]) -> io::Result<()> {
  let temp = temporary_path(path);
  fs::write(&temp, bytes)?;
  persist(&temp, path)
}

pub(crate) fn save<T: Serialize>(path: &Path, value: &T) -> Result<()> {
  let temp = temporary_path(path);
  let mut f = BufWriter::new(File::create(&temp)?);
  bincode::serde::encode_into_std_write(
    value,
    &mut f,
    bincode::config::standard(),
  )?;
  f.flush()?;
  drop(f);
  persist(&temp, path)?;
  Ok(())
}

pub(crate) fn load<T: DeserializeOwned>(path: &Path) -> Result<T> {
  let mut f = BufReader::new(File::open(path)?);
  let value =
    bincode::serde::decode_from_std_read(&mut f, bincode::config::standard())?;
  let mut tail = [0];
  if f.read(&mut tail)? != 0 {
    return Err("trailing metadata".into());
  }
  Ok(value)
}
