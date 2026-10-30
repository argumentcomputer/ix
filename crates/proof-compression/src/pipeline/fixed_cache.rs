//! Trusted local preprocessing, independent of each proof's witness and
//! openings. Entries are keyed by the cache format and the stage verifying
//! key, which commits to the fixed polynomials, so rebuilding the executable
//! keeps them valid.
//! The root is `CompressConfig::fixed_cache`, or `<stage>/kzg/fixed-cache`.
//! Fixed columns are tens of gigabytes per stage, so stages read them from
//! the cache in place and never keep their own copy; only the small setup
//! metadata, which later stages read from the stage directory, is staged.
use super::{
  prover::{self, FixedSetup},
  storage::{self, Manifest, Result},
};
use crate::kzg::{KzgConfig, Scalar};
use multi_stark::plonkish::MultiStarkCircuit;
use serde::{Deserialize, Serialize};
use std::{
  fs::{self, File},
  io,
  path::{Path, PathBuf},
};

#[derive(Serialize, Deserialize)]
pub(crate) struct Shape {
  pub(crate) widths: Vec<usize>,
  pub(crate) heights: Vec<usize>,
}

#[derive(Serialize, Deserialize)]
struct CachedFile {
  name: String,
  size: u64,
  /// BLAKE3 of the file at publication, checked on every restore. Checkpoint
  /// readers only detect changes made after they index a file, so a
  /// checkpoint damaged in the cache would otherwise be proved against.
  digest: [u8; 32],
}

#[derive(Serialize, Deserialize)]
struct Entry {
  identity: [u8; 32],
  shape: Shape,
  files: Vec<CachedFile>,
}

impl Entry {
  fn size(&self) -> u64 {
    self.files.iter().map(|file| file.size).sum()
  }
}

/// Whether a stage's fixed preprocessing was already published or has just
/// been, and its size in bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Prepared {
  Present { bytes: u64 },
  Published { bytes: u64 },
}

pub(crate) struct FixedCache {
  identity: [u8; 32],
  directory: PathBuf,
}

fn file_digest(path: &Path) -> io::Result<[u8; 32]> {
  let mut hasher = blake3::Hasher::new();
  hasher.update_mmap_rayon(path)?;
  Ok(*hasher.finalize().as_bytes())
}

impl FixedCache {
  /// Bump the format tag whenever the cached files' layout or contents change
  /// for the same verifying key; restores check each file's digest, and a
  /// stale layout fails the final proof verification.
  pub(crate) fn from_identity(root: &Path, vk: &[u8]) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"ix/kzg-fixed-cache/bn254/v2");
    hasher.update(vk);
    let identity = *hasher.finalize().as_bytes();
    Self::new(root, identity)
  }

  fn new(root: &Path, identity: [u8; 32]) -> Self {
    Self {
      identity,
      directory: root
        .join(blake3::Hash::from_bytes(identity).to_hex().as_str()),
    }
  }

  #[tracing::instrument(
    level = "info",
    skip_all,
    name = "compression/cache_restore"
  )]
  pub(crate) fn restore(&self, staged: &Path) -> Result<Option<Shape>> {
    let Some(entry) = self.checked_entry()? else {
      eprintln!("Fixed preprocessing cache miss: {}", self.directory.display());
      return Ok(None);
    };
    fs::create_dir_all(staged.join("kzg"))?;
    for CachedFile { name, .. } in
      entry.files.iter().filter(|f| is_setup(&f.name))
    {
      let destination = staged.join(name);
      if destination.try_exists()? {
        return Err(
          format!("refusing to replace {}", destination.display()).into(),
        );
      }
      fs::copy(self.directory.join(name), destination)?;
    }
    eprintln!("Reused fixed preprocessing: {}", self.directory.display());
    Ok(Some(entry.shape))
  }

  /// The published entry, after checking its identity, shape and every
  /// file's size and digest, or `None` when nothing is published.
  fn checked_entry(&self) -> Result<Option<Entry>> {
    let ready = self.directory.join("ready.bin");
    if !ready.try_exists()? {
      return Ok(None);
    }
    let entry: Entry = storage::load(&ready)?;
    if entry.identity != self.identity
      || entry.shape.widths.is_empty()
      || entry.shape.widths.len() != entry.shape.heights.len()
      || entry.files.len() != entry.shape.widths.len() * 2
    {
      return Err("fixed cache identity or shape mismatch".into());
    }
    let expected = file_names(entry.shape.widths.len());
    for (file, expected) in entry.files.iter().zip(expected) {
      let path = self.directory.join(&file.name);
      if file.name != expected
        || fs::metadata(&path)?.len() != file.size
        || file_digest(&path)? != file.digest
      {
        return Err("fixed cache entry is incomplete or damaged".into());
      }
    }
    Ok(Some(entry))
  }

  /// The published entry's total size, after checking it as a restore does,
  /// or `None` when nothing is published.
  pub(crate) fn check(&self) -> Result<Option<u64>> {
    Ok(self.checked_entry()?.map(|entry| entry.size()))
  }

  /// The circuit metadata and fixed commitment of every partition of a
  /// checked entry, as its `setup-{i}.bin` files record them.
  pub(crate) fn setup_parts(&self) -> Result<Vec<FixedSetup>> {
    let entry = self.checked_entry()?.ok_or("fixed cache entry is missing")?;
    entry
      .files
      .iter()
      .filter(|file| is_setup(&file.name))
      .map(|file| storage::load(&self.directory.join(&file.name)))
      .collect()
  }

  /// The fixed setup of `compiled` under `config`, from the published entry
  /// when it checks, otherwise committed into a staging directory beside the
  /// entry and published, as a stage's proof would leave it.
  pub(crate) fn prepare(
    &self,
    config: &KzgConfig,
    compiled: &MultiStarkCircuit<Scalar>,
  ) -> Result<(Vec<FixedSetup>, Prepared)> {
    if let Some(bytes) = self.check()? {
      return Ok((self.setup_parts()?, Prepared::Present { bytes }));
    }
    let staged = storage::temporary_path(&self.directory);
    let result = (|| -> Result<Vec<FixedSetup>> {
      fs::create_dir_all(staged.join("kzg"))?;
      let manifest = Manifest::for_compiled(compiled, vec![], None)?;
      storage::save(&staged.join("manifest.bin"), &manifest)?;
      let parts =
        prover::fixed_setup_in(config, compiled, &staged.join("kzg"))?;
      self.publish(&staged)?;
      Ok(parts)
    })();
    match fs::remove_dir_all(&staged) {
      Ok(()) => {},
      Err(error) if error.kind() == io::ErrorKind::NotFound => {},
      Err(error) => return Err(error.into()),
    }
    let parts = result?;
    let bytes =
      self.check()?.ok_or("published fixed cache entry is missing")?;
    Ok((parts, Prepared::Published { bytes }))
  }

  #[cfg(test)]
  pub(crate) fn directory(&self) -> &Path {
    &self.directory
  }

  /// The directory the prover reads and writes fixed checkpoints in: the
  /// published entry when there is one, so its fixed columns are read in
  /// place, otherwise `staged`, from which `publish` moves them.
  pub(crate) fn fixed_directory(&self, staged: &Path) -> Result<PathBuf> {
    Ok(if self.directory.join("ready.bin").try_exists()? {
      self.directory.join("kzg")
    } else {
      staged.join("kzg")
    })
  }

  /// Publish only after the proof using these parameters has verified.
  /// The cache directory must be trusted like the development SRS cache;
  /// metadata and field decoding detect truncation, not a malicious producer.
  #[tracing::instrument(
    level = "info",
    skip_all,
    name = "compression/cache_publish"
  )]
  pub(crate) fn publish(&self, staged: &Path) -> Result<()> {
    if self.directory.join("ready.bin").try_exists()? {
      return remove_staged_fixed(staged);
    }
    let manifest: Manifest = storage::load(&staged.join("manifest.bin"))?;
    let temporary = storage::temporary_path(&self.directory);
    fs::create_dir_all(temporary.join("kzg"))?;
    let mut files = Vec::new();
    for name in file_names(manifest.widths.len()) {
      let source = staged.join(&name);
      let size = fs::metadata(&source)?.len();
      let digest = file_digest(&source)?;
      let published = temporary.join(&name);
      if is_setup(&name) {
        fs::copy(&source, &published)?;
      } else {
        move_file(&source, &published)?;
      }
      File::open(published)?.sync_all()?;
      files.push(CachedFile { name, size, digest });
    }
    storage::save(
      &temporary.join("ready.bin"),
      &Entry {
        identity: self.identity,
        shape: Shape { widths: manifest.widths, heights: manifest.heights },
        files,
      },
    )?;
    storage::sync_directory(&temporary.join("kzg"))?;
    match storage::persist(&temporary, &self.directory) {
      Ok(()) => (),
      Err(_) if self.directory.join("ready.bin").try_exists()? => {
        fs::remove_dir_all(temporary)?;
      },
      Err(error) => return Err(error.into()),
    }
    eprintln!("Published fixed preprocessing: {}", self.directory.display());
    Ok(())
  }
}

fn file_names(count: usize) -> impl Iterator<Item = String> {
  (0..count)
    .flat_map(|i| [format!("kzg/setup-{i}.bin"), format!("kzg/fixed-{i}.bin")])
}

fn is_setup(name: &str) -> bool {
  name.starts_with("kzg/setup-")
}

/// Drop the fixed columns a stage wrote while another run published the
/// same entry first.
fn remove_staged_fixed(staged: &Path) -> Result<()> {
  let Ok(entries) = fs::read_dir(staged.join("kzg")) else {
    return Ok(());
  };
  for entry in entries {
    let path = entry?.path();
    let name = path.file_name().and_then(|name| name.to_str());
    if name.is_some_and(|name| name.starts_with("fixed-")) {
      fs::remove_file(path)?;
    }
  }
  Ok(())
}

fn move_file(source: &Path, destination: &Path) -> Result<()> {
  if destination.try_exists()? {
    return Err(
      format!("refusing to replace {}", destination.display()).into(),
    );
  }
  match fs::rename(source, destination) {
    Ok(()) => Ok(()),
    Err(error) if error.kind() == io::ErrorKind::CrossesDevices => {
      fs::copy(source, destination)?;
      fs::remove_file(source)?;
      Ok(())
    },
    Err(error) => Err(error.into()),
  }
}
