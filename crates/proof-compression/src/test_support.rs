//! Helpers shared by the unit tests.
use std::{
  fs,
  ops::Deref,
  path::{Path, PathBuf},
  sync::atomic::{AtomicU64, Ordering},
};

/// A fresh, empty directory under the system temporary directory. It is
/// removed with its contents on drop, so a failing test leaves nothing
/// behind; a test may also delete it early.
pub(crate) struct TempDir(PathBuf);

impl TempDir {
  pub(crate) fn new(name: &str) -> Self {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let path = std::env::temp_dir().join(format!(
      "ix-{name}-{}-{}",
      std::process::id(),
      NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&path).unwrap();
    Self(path)
  }
}

impl Deref for TempDir {
  type Target = Path;

  fn deref(&self) -> &Path {
    &self.0
  }
}

impl AsRef<Path> for TempDir {
  fn as_ref(&self) -> &Path {
    &self.0
  }
}

impl Drop for TempDir {
  fn drop(&mut self) {
    let _ = fs::remove_dir_all(&self.0);
  }
}
