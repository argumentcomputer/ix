//! Stage output files: bincode metadata and atomic file publication.
use super::fixed_cache::Shape;
use crate::kzg::{
  curve::{Bn254, KzgCurve},
  field::CurveScalar,
};
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
#[serde(bound = "")]
pub(crate) struct Manifest<C: KzgCurve = Bn254> {
  pub(crate) widths: Vec<usize>,
  pub(crate) heights: Vec<usize>,
  pub(crate) claims: Vec<Vec<CurveScalar<C>>>,
}

impl<C: KzgCurve> Manifest<C> {
  /// The manifest of a compiled circuit, checked against the shape of a
  /// restored fixed-preprocessing cache entry when there is one.
  pub(crate) fn for_compiled(
    compiled: &MultiStarkCircuit<CurveScalar<C>>,
    claims: Vec<Vec<CurveScalar<C>>>,
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

/// Publish a complete cache directory without exposing partially prepared
/// keys. Concurrent writers retain the first complete directory instead of
/// replacing it with another key.
#[cfg(all(test, feature = "groth16"))]
pub(crate) fn prepare_cached_directory(
  path: &Path,
  prepare: impl FnOnce(&Path) -> Result<()>,
) -> Result<()> {
  if path.try_exists()? {
    return Ok(());
  }
  let parent = path.parent().ok_or("cache directory has no parent")?;
  fs::create_dir_all(parent)?;
  let temporary = temporary_path(path);
  fs::create_dir(&temporary)?;
  let result = prepare(&temporary).and_then(|()| {
    sync_directory(&temporary)?;
    match fs::rename(&temporary, path) {
      Ok(()) => sync_directory(parent).map_err(Into::into),
      Err(error)
        if matches!(
          error.kind(),
          io::ErrorKind::AlreadyExists | io::ErrorKind::DirectoryNotEmpty
        ) && path.is_dir() =>
      {
        Ok(())
      },
      Err(error) => Err(error.into()),
    }
  });
  if temporary.exists() {
    let _ = fs::remove_dir_all(&temporary);
  }
  result
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

#[cfg(all(
  target_os = "linux",
  any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "riscv64"
  )
))]
fn fadvise(fd: std::os::fd::RawFd, offset: i64, len: i64, advice: i32) {
  unsafe extern "C" {
    fn posix_fadvise(fd: i32, offset: i64, len: i64, advice: i32) -> i32;
  }
  // Best-effort kernel page-cache hint; ignoring errors never affects results.
  let _ = unsafe { posix_fadvise(fd, offset, len, advice) };
}

/// Hint to the OS that `file` will be read sequentially.
pub(crate) fn fadvise_sequential(file: &File) {
  #[cfg(all(
    target_os = "linux",
    any(
      target_arch = "x86_64",
      target_arch = "aarch64",
      target_arch = "riscv64"
    )
  ))]
  {
    use std::os::fd::AsRawFd;
    const POSIX_FADV_SEQUENTIAL: i32 = 2;
    fadvise(file.as_raw_fd(), 0, 0, POSIX_FADV_SEQUENTIAL);
  }
  #[cfg(not(all(
    target_os = "linux",
    any(
      target_arch = "x86_64",
      target_arch = "aarch64",
      target_arch = "riscv64"
    )
  )))]
  let _ = file;
}

/// Available host RAM in GiB (read from `/proc/meminfo` on Linux).
pub(crate) fn available_host_gib() -> Option<usize> {
  #[cfg(target_os = "linux")]
  {
    let meminfo = fs::read_to_string("/proc/meminfo").ok()?;
    let parse_kib = |key: &str| -> Option<usize> {
      meminfo
        .lines()
        .find_map(|line| line.strip_prefix(key))?
        .split_whitespace()
        .next()?
        .parse::<usize>()
        .ok()
    };
    let kib = parse_kib("MemAvailable:").or_else(|| parse_kib("MemTotal:"))?;
    Some(kib >> 20)
  }
  #[cfg(not(target_os = "linux"))]
  {
    None
  }
}

/// Total host RAM in GiB, cached for the lifetime of the process.
#[cfg(all(
  target_os = "linux",
  any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "riscv64"
  )
))]
fn total_host_gib() -> Option<usize> {
  static TOTAL: std::sync::OnceLock<Option<usize>> = std::sync::OnceLock::new();
  *TOTAL.get_or_init(|| {
    let meminfo = fs::read_to_string("/proc/meminfo").ok()?;
    let kib = meminfo
      .lines()
      .find_map(|line| line.strip_prefix("MemTotal:"))?
      .split_whitespace()
      .next()?
      .parse::<usize>()
      .ok()?;
    Some(kib >> 20)
  })
}

/// Whether `fadvise_dontneed` should evict page-cache entries. On hosts with
/// `< 192 GiB` total RAM (or when `IX_KZG_DISK_SPILL` is explicitly enabled),
/// evicting prevents multi-gigabyte cache scans from competing with prover
/// working sets; on high-RAM hosts keeping the fixed-preprocessing cache hot in
/// page cache avoids redundant disk I/O across cosets and stages.
#[cfg(all(
  target_os = "linux",
  any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "riscv64"
  )
))]
fn should_evict_page_cache() -> bool {
  const PAGE_CACHE_KEEP_RAM_GIB: usize = 192;
  let explicit_spill = matches!(
    std::env::var("IX_KZG_DISK_SPILL").as_deref(),
    Ok("1" | "true" | "yes")
  );
  explicit_spill
    || total_host_gib().is_none_or(|gib| gib < PAGE_CACHE_KEEP_RAM_GIB)
}

/// Hint to the OS that `[offset, offset + len)` of `file` (`len == 0` for the
/// whole file) can be evicted from the page cache to bound resident memory.
pub(crate) fn fadvise_dontneed(file: &File, offset: u64, len: u64) {
  #[cfg(all(
    target_os = "linux",
    any(
      target_arch = "x86_64",
      target_arch = "aarch64",
      target_arch = "riscv64"
    )
  ))]
  {
    if !should_evict_page_cache() {
      return;
    }
    use std::os::fd::AsRawFd;
    const POSIX_FADV_DONTNEED: i32 = 4;
    if let (Ok(offset), Ok(len)) = (i64::try_from(offset), i64::try_from(len)) {
      fadvise(file.as_raw_fd(), offset, len, POSIX_FADV_DONTNEED);
    }
  }
  #[cfg(not(all(
    target_os = "linux",
    any(
      target_arch = "x86_64",
      target_arch = "aarch64",
      target_arch = "riscv64"
    )
  )))]
  let _ = (file, offset, len);
}

/// Best-effort host allocator purge at stage and partition boundaries so
/// released multi-gigabyte arenas return to the OS promptly.
pub(crate) fn release_host_memory() {
  #[cfg(all(target_os = "linux", target_env = "gnu"))]
  {
    use std::ffi::{c_char, c_void};
    unsafe extern "C" {
      fn dlsym(handle: *mut c_void, symbol: *const c_char) -> *mut c_void;
      fn malloc_trim(pad: usize) -> i32;
    }
    // RTLD_DEFAULT is NULL on glibc Linux. If the embedding binary links
    // mimalloc dynamically, ask it to purge abandoned arenas first.
    let mi_collect =
      unsafe { dlsym(std::ptr::null_mut(), c"mi_collect".as_ptr()) };
    if !mi_collect.is_null() {
      // SAFETY: `mi_collect` has C signature `void mi_collect(bool force)`.
      let collect: unsafe extern "C" fn(bool) =
        unsafe { std::mem::transmute(mi_collect) };
      unsafe { collect(true) };
    }
    let _ = unsafe { malloc_trim(0) };
  }
}

/// Stream-hash a file with BLAKE3 using a bounded buffer so multi-gigabyte
/// cache files are never memory-mapped into `VmRSS`/`VmHWM`.
pub(crate) fn blake3_file(path: &Path) -> io::Result<[u8; 32]> {
  const CHUNK_BYTES: usize = 16 << 20;
  const RAYON_THRESHOLD: usize = 128 << 10;

  let mut file = File::open(path)?;
  fadvise_sequential(&file);
  let mut hasher = blake3::Hasher::new();
  let mut buffer = vec![0u8; CHUNK_BYTES];
  let mut offset: u64 = 0;
  loop {
    let mut filled = 0;
    while filled < buffer.len() {
      match file.read(&mut buffer[filled..]) {
        Ok(0) => break,
        Ok(n) => filled += n,
        Err(error) if error.kind() == io::ErrorKind::Interrupted => {},
        Err(error) => return Err(error),
      }
    }
    if filled == 0 {
      break;
    }
    if filled >= RAYON_THRESHOLD {
      hasher.update_rayon(&buffer[..filled]);
    } else {
      hasher.update(&buffer[..filled]);
    }
    if let Ok(len) = u64::try_from(filled) {
      fadvise_dontneed(&file, offset, len);
      offset = offset.saturating_add(len);
    }
    if filled < buffer.len() {
      break;
    }
  }
  Ok(*hasher.finalize().as_bytes())
}

#[cfg(all(test, feature = "groth16"))]
mod tests {
  use super::*;
  use crate::test_support::TempDir;

  #[test]
  fn key_cache_publishes_only_complete_keys_and_preserves_the_first()
  -> Result<()> {
    let temporary = TempDir::new("key-cache");
    let directory = temporary.join("keys");
    let failed = prepare_cached_directory(&directory, |staging| {
      write_atomic(&staging.join("key"), b"incomplete")?;
      Err("setup failed".into())
    });
    assert!(failed.is_err());
    assert!(!directory.exists());
    prepare_cached_directory(&directory, |staging| {
      write_atomic(&staging.join("key"), b"first complete key")?;
      Ok(())
    })?;
    prepare_cached_directory(&directory, |_| {
      panic!("must reuse the completed key")
    })?;
    assert_eq!(fs::read(directory.join("key"))?, b"first complete key");
    Ok(())
  }
}
