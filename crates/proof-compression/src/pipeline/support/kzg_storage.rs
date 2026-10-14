//! Staged trace files: bincode metadata and zstd-framed canonical scalars.
//! Matrices stream through `pzstd` when it is installed and `zstd` otherwise;
//! both read either output. `IX_KZG_TRACE_CODEC` forces one of them.
use crate::kzg::{Scalar, encoding};
use multi_stark::system::CircuitInputs;
use p3_matrix::{Matrix, dense::RowMajorMatrix};
use serde::{Serialize, de::DeserializeOwned};
use std::{
  fs::{self, File},
  io::{self, BufReader, BufWriter, Read, Write},
  path::{Path, PathBuf},
  process::{Child, Command, Stdio},
  sync::{
    OnceLock,
    atomic::{AtomicU64, Ordering},
  },
};

pub(crate) type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

#[derive(serde::Serialize, serde::Deserialize)]
pub(crate) struct Manifest {
  pub(crate) widths: Vec<usize>,
  pub(crate) heights: Vec<usize>,
  pub(crate) claims: Vec<Vec<Scalar>>,
}

fn trace_codec() -> io::Result<&'static str> {
  match std::env::var("IX_KZG_TRACE_CODEC").as_deref() {
    Ok("pzstd") => Ok("pzstd"),
    Ok("zstd") => Ok("zstd"),
    Ok("auto") | Err(std::env::VarError::NotPresent) => {
      static AVAILABLE: OnceLock<&str> = OnceLock::new();
      Ok(AVAILABLE.get_or_init(|| {
        if Command::new("pzstd")
          .arg("--version")
          .stdout(Stdio::null())
          .stderr(Stdio::null())
          .status()
          .is_ok_and(|status| status.success())
        {
          "pzstd"
        } else {
          "zstd"
        }
      }))
    },
    _ => Err(io::Error::new(
      io::ErrorKind::InvalidInput,
      "IX_KZG_TRACE_CODEC must be auto, pzstd, or zstd",
    )),
  }
}

/// A codec child that is killed and reaped if its stream is dropped early.
struct ReapedChild(Child);

impl Drop for ReapedChild {
  fn drop(&mut self) {
    if !matches!(self.0.try_wait(), Ok(Some(_))) {
      let _ = self.0.kill();
      let _ = self.0.wait();
    }
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

/// Move a completely written `temporary` file or directory to `path` so that
/// both its contents and the rename survive a crash: the temporary is synced
/// before the rename and the containing directory after it.
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

pub(crate) fn write_matrix(
  path: &Path,
  m: &RowMajorMatrix<Scalar>,
) -> Result<()> {
  write_matrix_with_codec(path, m, trace_codec()?)
}

fn write_matrix_with_codec(
  path: &Path,
  m: &RowMajorMatrix<Scalar>,
  codec: &str,
) -> Result<()> {
  let temp = temporary_path(path);
  let mut command = Command::new(codec);
  command.args(["-q", "-1", "-c"]);
  if codec == "zstd" {
    command.arg("-T0");
  }
  let mut child = ReapedChild(
    command.stdin(Stdio::piped()).stdout(File::create(&temp)?).spawn()?,
  );
  let mut w = BufWriter::with_capacity(1 << 20, child.0.stdin.take().unwrap());
  w.write_all(&(m.width() as u64).to_le_bytes())?;
  w.write_all(&(m.height() as u64).to_le_bytes())?;
  encoding::write_scalars(&mut w, &m.values)?;
  w.flush()?;
  drop(w);
  if !child.0.wait()?.success() {
    return Err("zstd write failed".into());
  }
  persist(&temp, path)?;
  Ok(())
}

pub(crate) fn read_matrix_bounded(
  path: &Path,
  max_height: usize,
) -> Result<RowMajorMatrix<Scalar>> {
  read_matrix_with_codec(path, max_height, trace_codec()?, None)
}

/// Read a staged matrix whose dimensions the manifest already fixes.
pub(crate) fn read_matrix_with_shape(
  path: &Path,
  width: usize,
  height: usize,
) -> Result<RowMajorMatrix<Scalar>> {
  read_matrix_with_codec(path, height, trace_codec()?, Some((width, height)))
}

fn read_matrix_with_codec(
  path: &Path,
  max_height: usize,
  codec: &str,
  expected: Option<(usize, usize)>,
) -> Result<RowMajorMatrix<Scalar>> {
  let mut child = ReapedChild(
    Command::new(codec)
      .args(["-q", "-d", "-c"])
      .arg(path)
      .stdout(Stdio::piped())
      .spawn()?,
  );
  let mut r = BufReader::with_capacity(1 << 20, child.0.stdout.take().unwrap());
  let mut b = [0; 8];
  r.read_exact(&mut b)?;
  let width = usize::try_from(u64::from_le_bytes(b))?;
  r.read_exact(&mut b)?;
  let height = usize::try_from(u64::from_le_bytes(b))?;
  if width == 0
    || !height.is_power_of_two()
    || width > 1024
    || height > max_height
  {
    return Err("bad matrix dimensions".into());
  }
  if expected.is_some_and(|shape| shape != (width, height)) {
    return Err("matrix dimensions differ from the staged manifest".into());
  }
  let count = width.checked_mul(height).ok_or("matrix overflow")?;
  let values = encoding::read_scalars(&mut r, count)?;
  if io::copy(&mut r, &mut io::sink())? != 0 {
    return Err("trailing matrix bytes".into());
  }
  drop(r);
  if !child.0.wait()?.success() {
    return Err("zstd read failed".into());
  }
  Ok(RowMajorMatrix::new(values, width))
}

pub(crate) fn definition(
  dir: &Path,
  index: usize,
  max_height: usize,
) -> Result<CircuitInputs<Scalar>> {
  let mut input: CircuitInputs<Scalar> =
    load(&dir.join(format!("{index}.meta")))?;
  input.preprocessed = Some(read_matrix_bounded(
    &dir.join(format!("{index}.fixed.zst")),
    max_height,
  )?);
  Ok(input)
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::traits::{Algebra, Field};

  #[test]
  fn parallel_frames_and_legacy_streams_are_interoperable() -> Result<()> {
    let dir = std::env::temp_dir()
      .join(format!("kzg-trace-codecs-{}", std::process::id()));
    fs::create_dir(&dir)?;
    let matrix = RowMajorMatrix::new(
      (0..4 * (1 << 17))
        .map(|i| {
          let value = Scalar::from_usize(i * 7919);
          value * value - Scalar::ONE
        })
        .collect(),
      4,
    );
    let mut codecs = vec!["zstd"];
    if Command::new("pzstd")
      .arg("--version")
      .stdout(Stdio::null())
      .stderr(Stdio::null())
      .status()
      .is_ok_and(|status| status.success())
    {
      codecs.push("pzstd");
    }
    for encoder in &codecs {
      let path = dir.join(format!("{encoder}.zst"));
      write_matrix_with_codec(&path, &matrix, encoder)?;
      for decoder in &codecs {
        assert_eq!(
          matrix,
          read_matrix_with_codec(&path, 1 << 17, decoder, None)?
        );
        assert!(
          read_matrix_with_codec(&path, 1 << 17, decoder, Some((3, 1 << 17)))
            .is_err()
        );
      }
    }
    fs::remove_dir_all(dir)?;
    Ok(())
  }
}
