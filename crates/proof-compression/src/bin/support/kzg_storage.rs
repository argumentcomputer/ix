use ix_proof_compression::kzg::Scalar;
use multi_stark::system::CircuitInputs;
use p3_matrix::{Matrix, dense::RowMajorMatrix};
use serde::{Serialize, de::DeserializeOwned};
use std::{
  fs::{self, File},
  io::{self, BufReader, BufWriter, Read, Write},
  path::Path,
  process::{Command, Stdio},
};
pub(crate) type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
#[derive(serde::Serialize, serde::Deserialize)]
pub(crate) struct Manifest {
  pub(crate) widths: Vec<usize>,
  pub(crate) heights: Vec<usize>,
  pub(crate) claims: Vec<Vec<Scalar>>,
}
pub(crate) fn save<T: Serialize>(path: &Path, value: &T) -> Result<()> {
  let temp = path.with_extension("partial");
  let mut f = BufWriter::new(File::create(&temp)?);
  bincode::serde::encode_into_std_write(
    value,
    &mut f,
    bincode::config::standard(),
  )?;
  f.flush()?;
  drop(f);
  fs::rename(temp, path)?;
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
  let temp = path.with_extension("partial");
  let mut child = Command::new("zstd")
    .args(["-q", "-1", "-T4", "-c"])
    .stdin(Stdio::piped())
    .stdout(File::create(&temp)?)
    .spawn()?;
  let mut w = BufWriter::with_capacity(1 << 20, child.stdin.take().unwrap());
  w.write_all(&(m.width() as u64).to_le_bytes())?;
  w.write_all(&(m.height() as u64).to_le_bytes())?;
  for value in &m.values {
    for limb in value.canonical_limbs_le() {
      w.write_all(&limb.to_le_bytes())?;
    }
  }
  w.flush()?;
  drop(w);
  if !child.wait()?.success() {
    return Err("zstd write failed".into());
  }
  fs::rename(temp, path)?;
  Ok(())
}
pub(crate) fn read_matrix(path: &Path) -> Result<RowMajorMatrix<Scalar>> {
  read_matrix_bounded(path, 1 << 24)
}
pub(crate) fn read_matrix_bounded(
  path: &Path,
  max_height: usize,
) -> Result<RowMajorMatrix<Scalar>> {
  let mut child = Command::new("zstd")
    .args(["-q", "-d", "-c"])
    .arg(path)
    .stdout(Stdio::piped())
    .spawn()?;
  let mut r = BufReader::with_capacity(1 << 20, child.stdout.take().unwrap());
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
  let mut values =
    Vec::with_capacity(width.checked_mul(height).ok_or("matrix overflow")?);
  for _ in 0..width * height {
    let mut limbs = [0; 4];
    for limb in &mut limbs {
      r.read_exact(&mut b)?;
      *limb = u64::from_le_bytes(b);
    }
    values.push(Scalar::from_limbs_le(limbs));
  }
  if io::copy(&mut r, &mut io::sink())? != 0 {
    return Err("trailing matrix bytes".into());
  }
  drop(r);
  if !child.wait()?.success() {
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
