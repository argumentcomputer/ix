use std::{
  fs::{self, OpenOptions},
  io::Write,
  path::Path,
  sync::atomic::{AtomicU64, Ordering},
};

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

/// A reader sees either the previous complete partition or the next one.
pub(super) fn write_atomic(path: &Path, bytes: &[u8]) -> Result<(), String> {
  let parent = path
    .parent()
    .filter(|p| !p.as_os_str().is_empty())
    .unwrap_or_else(|| Path::new("."));
  fs::create_dir_all(parent)
    .map_err(|error| format!("create {}: {error}", parent.display()))?;
  let mut name =
    path.file_name().ok_or("manifest path has no filename")?.to_os_string();
  name.push(format!(
    ".tmp.{}.{}",
    std::process::id(),
    NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
  ));
  let temporary = parent.join(name);
  let mut file = OpenOptions::new()
    .write(true)
    .create_new(true)
    .open(&temporary)
    .map_err(|error| format!("create {}: {error}", temporary.display()))?;
  let result = (|| -> std::io::Result<()> {
    file.write_all(bytes)?;
    file.sync_all()?;
    fs::rename(&temporary, path)?;
    Ok(())
  })();
  if result.is_err() {
    let _ = fs::remove_file(&temporary);
  }
  result.map_err(|error| format!("write manifest {}: {error}", path.display()))
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn replacement_is_complete_and_failed_writes_leave_no_temporary() {
    let dir = std::env::temp_dir().join(format!(
      "ix-refined-manifest-{}-{}",
      std::process::id(),
      NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
    ));
    let path = dir.join("partition.ixes");
    write_atomic(&path, b"first partition").unwrap();
    write_atomic(&path, b"refined partition").unwrap();
    assert_eq!(fs::read(&path).unwrap(), b"refined partition");
    let directory_target = dir.join("directory");
    fs::create_dir(&directory_target).unwrap();
    assert!(write_atomic(&directory_target, b"invalid target").is_err());
    assert!(directory_target.is_dir());
    assert_eq!(fs::read_dir(&dir).unwrap().count(), 2);
    fs::remove_dir_all(dir).unwrap();
  }
}
