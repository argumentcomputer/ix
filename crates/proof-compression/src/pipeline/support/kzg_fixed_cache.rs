//! Trusted local preprocessing, independent of each proof's witness and
//! openings. Entries are keyed by the executable digest and the stage
//! profile, so a rebuilt binary never reuses another build's preprocessing.
//! The root is `IX_KZG_FIXED_CACHE`, or `<stage>/kzg/fixed-cache`.
use super::kzg_storage::{self as storage, Manifest, Result};
use serde::{Deserialize, Serialize};
use std::{
  fs::{self, File},
  io,
  path::{Path, PathBuf},
  sync::OnceLock,
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
  /// Absent for checkpoint files, which record a digest that every read
  /// verifies; hashing them again here would cost a minute per restore.
  digest: Option<[u8; 32]>,
}

fn self_verifying(name: &str) -> bool {
  name.starts_with("kzg/fixed-")
}

#[derive(Serialize, Deserialize)]
struct Entry {
  identity: [u8; 32],
  shape: Shape,
  files: Vec<CachedFile>,
}

pub(crate) struct FixedCache {
  identity: [u8; 32],
  directory: PathBuf,
}

pub(crate) fn executable_digest() -> Result<[u8; 32]> {
  static DIGEST: OnceLock<[u8; 32]> = OnceLock::new();
  if let Some(digest) = DIGEST.get() {
    return Ok(*digest);
  }
  let digest = file_digest(&std::env::current_exe()?)?;
  Ok(*DIGEST.get_or_init(|| digest))
}

fn file_digest(path: &Path) -> io::Result<[u8; 32]> {
  let mut hasher = blake3::Hasher::new();
  hasher.update_reader(File::open(path)?)?;
  Ok(*hasher.finalize().as_bytes())
}

fn root(stage: &Path) -> PathBuf {
  std::env::var_os("IX_KZG_FIXED_CACHE")
    .map_or_else(|| stage.join("kzg/fixed-cache"), PathBuf::from)
}

impl FixedCache {
  /// The executable digest conservatively binds the compiler, lowering,
  /// dependency versions, SRS recipe, and all circuit implementation choices.
  pub(crate) fn for_stage(directory: &Path, profile: &[u8]) -> Result<Self> {
    let cache = Self::from_profile(&root(directory), profile)?;
    let mut marker = cache.identity.to_vec();
    marker.extend_from_slice(&executable_digest()?);
    fs::write(directory.join("fixed-cache-id.bin"), marker)?;
    Ok(cache)
  }

  pub(crate) fn from_profile(root: &Path, profile: &[u8]) -> Result<Self> {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"ix/kzg-fixed-cache/v3");
    hasher.update(&executable_digest()?);
    hasher.update(profile);
    let identity = *hasher.finalize().as_bytes();
    Ok(Self::new(root, identity))
  }

  pub(crate) fn for_prove(directory: &Path) -> Result<Option<Self>> {
    let marker = match fs::read(directory.join("fixed-cache-id.bin")) {
      Ok(bytes) => bytes,
      Err(error) if error.kind() == io::ErrorKind::NotFound => {
        return Ok(None);
      },
      Err(error) => return Err(error.into()),
    };
    if marker.len() != 64 || marker[32..] != executable_digest()? {
      return Err("fixed cache was staged by a different executable".into());
    }
    let identity = marker[..32].try_into().unwrap();
    Ok(Some(Self::new(&root(directory), identity)))
  }

  fn new(root: &Path, identity: [u8; 32]) -> Self {
    Self {
      identity,
      directory: root
        .join(blake3::Hash::from_bytes(identity).to_hex().as_str()),
    }
  }

  pub(crate) fn restore(&self, staged: &Path) -> Result<Option<Shape>> {
    let ready = self.directory.join("ready.bin");
    if !ready.try_exists()? {
      eprintln!("Fixed preprocessing cache miss: {}", self.directory.display());
      return Ok(None);
    }
    let entry: Entry = storage::load(&ready)?;
    if entry.identity != self.identity
      || entry.shape.widths.is_empty()
      || entry.shape.widths.len() != entry.shape.heights.len()
      || entry.files.len() != entry.shape.widths.len() * 3
    {
      return Err("fixed cache identity or shape mismatch".into());
    }
    let expected = file_names(entry.shape.widths.len());
    for (file, expected) in entry.files.iter().zip(expected) {
      let path = self.directory.join(&file.name);
      let damaged = match file.digest {
        Some(digest) => file_digest(&path)? != digest,
        None => false,
      };
      if file.name != expected
        || fs::metadata(&path)?.len() != file.size
        || damaged
      {
        return Err("fixed cache entry is incomplete or damaged".into());
      }
    }
    fs::create_dir_all(staged.join("kzg"))?;
    for CachedFile { name, .. } in &entry.files {
      // A directory staged again keeps the files of its earlier staging,
      // possibly from another executable; the cache entry supersedes them.
      let target = staged.join(name);
      match fs::remove_file(&target) {
        Ok(()) => (),
        Err(error) if error.kind() == io::ErrorKind::NotFound => (),
        Err(error) => return Err(error.into()),
      }
      link_or_copy(&self.directory.join(name), &target)?;
    }
    eprintln!("Reused fixed preprocessing: {}", self.directory.display());
    Ok(Some(entry.shape))
  }

  /// Publish only after the proof using these parameters has verified.
  /// The cache directory must be trusted like the development SRS cache;
  /// metadata and field decoding detect truncation, not a malicious producer.
  pub(crate) fn publish(&self, staged: &Path) -> Result<()> {
    if self.directory.join("ready.bin").try_exists()? {
      return Ok(());
    }
    let manifest: Manifest = storage::load(&staged.join("manifest.bin"))?;
    let temporary = storage::temporary_path(&self.directory);
    fs::create_dir_all(temporary.join("kzg"))?;
    let mut files = Vec::new();
    for name in file_names(manifest.widths.len()) {
      let source = staged.join(&name);
      let size = fs::metadata(&source)?.len();
      let digest =
        if self_verifying(&name) { None } else { Some(file_digest(&source)?) };
      let published = temporary.join(&name);
      link_or_copy(&source, &published)?;
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
  (0..count).flat_map(|i| {
    [
      format!("{i}.meta"),
      format!("kzg/setup-{i}.bin"),
      format!("kzg/fixed-{i}.bin"),
    ]
  })
}

fn link_or_copy(source: &Path, destination: &Path) -> Result<()> {
  if destination.try_exists()? {
    return Err(
      format!("refusing to replace {}", destination.display()).into(),
    );
  }
  match fs::hard_link(source, destination) {
    Ok(()) => Ok(()),
    Err(error) if error.kind() == io::ErrorKind::CrossesDevices => {
      fs::copy(source, destination)?;
      Ok(())
    },
    Err(error) => Err(error.into()),
  }
}
