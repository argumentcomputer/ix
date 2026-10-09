//! Locally generated verifier configurations, separate from proof-store hints.
use super::*;
use std::{
  fs,
  io::Write,
  path::PathBuf,
  time::{SystemTime, UNIX_EPOCH},
};

pub(super) struct Settings {
  pub root_hash: String,
  pub params_hash: String,
  pub root_log: u32,
  pub kzg_log: u32,
  pub claim_len: usize,
}

impl Settings {
  pub(super) fn new(
    vk: &[u8],
    params: &[u8],
    root_log: u32,
    kzg_log: u32,
    claim_len: usize,
  ) -> Self {
    Self {
      root_hash: blake3::hash(vk).to_hex().to_string(),
      params_hash: blake3::hash(params).to_hex().to_string(),
      root_log,
      kzg_log,
      claim_len,
    }
  }

  pub(super) fn id(&self) -> String {
    let mut h = blake3::Hasher::new();
    // Bump whenever circuit construction, normalization or security settings change.
    h.update(b"ix/fixed-compression/v1");
    h.update(self.root_hash.as_bytes());
    h.update(self.params_hash.as_bytes());
    h.update(&self.root_log.to_le_bytes());
    h.update(&self.kzg_log.to_le_bytes());
    h.update(&(self.claim_len as u64).to_le_bytes());
    h.finalize().to_hex().to_string()
  }
}

pub(super) struct Entry {
  pub settings: Settings,
  pub srs_path: PathBuf,
  pub key_bytes: Vec<u8>,
}

pub(super) fn decode_id(id: &str) -> pipeline::Result<[u8; 32]> {
  if id.len() != 64
    || !id.bytes().all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
  {
    return Err("invalid compression configuration identifier".into());
  }
  let mut bytes = [0; 32];
  for (i, byte) in bytes.iter_mut().enumerate() {
    *byte = u8::from_str_radix(&id[i * 2..i * 2 + 2], 16)?;
  }
  Ok(bytes)
}

pub(super) fn active(dir: &Path) -> pipeline::Result<String> {
  let id = fs::read_to_string(dir.join("default")).map_err(|e| {
    format!(
      "no active compression configuration; run `ix compression setup`: {e}"
    )
  })?;
  decode_id(id.trim())?;
  Ok(id.trim().to_string())
}

fn temporary(dir: &Path) -> pipeline::Result<PathBuf> {
  let stamp = SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos();
  Ok(dir.join(format!(".setup-{}-{stamp}", std::process::id())))
}

fn write_atomic(
  path: &Path,
  write: impl FnOnce(&mut File) -> pipeline::Result<()>,
) -> pipeline::Result<()> {
  let tmp = temporary(path.parent().ok_or("missing configuration directory")?)?;
  let mut f = File::options().write(true).create_new(true).open(&tmp)?;
  let result = (|| -> pipeline::Result<()> {
    write(&mut f)?;
    f.sync_all()?;
    drop(f);
    fs::rename(&tmp, path)?;
    Ok(())
  })();
  if result.is_err() {
    let _ = fs::remove_file(tmp);
  }
  result
}

pub(super) fn activate(dir: &Path, id: &str) -> pipeline::Result<()> {
  decode_id(id)?;
  write_atomic(&dir.join("default"), |f| Ok(f.write_all(id.as_bytes())?))
}

fn srs_location(srs: &Path, dev: bool) -> pipeline::Result<String> {
  if dev {
    return Ok(String::new());
  }
  Ok(
    fs::canonicalize(srs)?.to_str().ok_or("SRS path is not UTF-8")?.to_string(),
  )
}

/// The SRS path is not part of circuit identity. Re-running setup with the
/// same parameters at a new path must update the proving source as well.
/// Called only after the existing verifier and the supplied SRS are validated.
pub(super) fn reuse(
  dir: &Path,
  id: &str,
  srs: &Path,
  dev: Option<&Srs>,
) -> pipeline::Result<()> {
  decode_id(id)?;
  let base = dir.join(id);
  let path = base.join("settings.json");
  let mut value: serde_json::Value = serde_json::from_slice(&fs::read(&path)?)?;
  value["srs"] = srs_location(srs, dev.is_some())?.into();
  value["dev_srs"] = dev.is_some().into();
  if let Some(srs) = dev {
    write_atomic(&base.join("development.srs"), |f| Ok(srs.write(f)?))?;
  }
  let bytes = serde_json::to_vec_pretty(&value)?;
  write_atomic(&path, |f| Ok(f.write_all(&bytes)?))?;
  activate(dir, id)
}

pub(super) fn load(dir: &Path, id: &str, vk: &[u8]) -> pipeline::Result<Entry> {
  decode_id(id)?;
  let base = dir.join(id);
  let bytes = fs::read(base.join("settings.json")).map_err(|e| format!("compression configuration {id} is not available locally; run matching `ix compression setup`: {e}"))?;
  let value: serde_json::Value = serde_json::from_slice(&bytes)?;
  let string = |name| -> pipeline::Result<String> {
    Ok(
      value
        .get(name)
        .and_then(|v| v.as_str())
        .ok_or("invalid local compression settings")?
        .to_string(),
    )
  };
  let number = |name| -> pipeline::Result<u32> {
    Ok(u32::try_from(
      value
        .get(name)
        .and_then(|v| v.as_u64())
        .ok_or("invalid local compression settings")?,
    )?)
  };
  if number("version")? != 1 {
    return Err("unsupported local compression settings".into());
  }
  let settings = Settings {
    root_hash: string("root")?,
    params_hash: string("parameters")?,
    root_log: number("root_log_height")?,
    kzg_log: number("kzg_log_height")?,
    claim_len: number("claim_len")? as usize,
  };
  if settings.id() != id
    || settings.root_hash != blake3::hash(vk).to_hex().as_str()
    || !(1..=26).contains(&settings.root_log)
    || !(16..=26).contains(&settings.kzg_log)
  {
    return Err(
      "local compression configuration does not match this aggregate backend"
        .into(),
    );
  }
  let key_bytes = fs::read(base.join("verifier.bin"))?;
  if blake3::hash(&key_bytes).to_hex().as_str() != string("verifier")? {
    return Err(
      "local compression verifier is corrupt; remove this configuration directory and rerun setup".into(),
    );
  }
  let srs_path = if value.get("dev_srs").and_then(|v| v.as_bool()) == Some(true)
  {
    base.join("development.srs")
  } else {
    PathBuf::from(string("srs")?)
  };
  Ok(Entry { settings, srs_path, key_bytes })
}

pub(super) fn publish(
  dir: &Path,
  settings: &Settings,
  key: &[u8],
  srs: &Path,
  dev: Option<&Srs>,
) -> pipeline::Result<()> {
  fs::create_dir_all(dir)?;
  let tmp = temporary(dir)?;
  fs::create_dir(&tmp)?;
  let result = (|| -> pipeline::Result<()> {
    let id = settings.id();
    let path = srs_location(srs, dev.is_some())?;
    if let Some(srs) = dev {
      let mut file = File::options()
        .write(true)
        .create_new(true)
        .open(tmp.join("development.srs"))?;
      srs.write(&mut file)?;
      file.sync_all()?;
    }
    let record = serde_json::json!({"version": 1, "root": settings.root_hash, "parameters": settings.params_hash,
      "root_log_height": settings.root_log, "kzg_log_height": settings.kzg_log, "claim_len": settings.claim_len,
      "verifier": blake3::hash(key).to_hex().as_str(), "srs": path, "dev_srs": dev.is_some()});
    for (name, bytes) in [
      ("verifier.bin", key.to_vec()),
      ("settings.json", serde_json::to_vec_pretty(&record)?),
    ] {
      let mut file =
        File::options().write(true).create_new(true).open(tmp.join(name))?;
      file.write_all(&bytes)?;
      file.sync_all()?;
    }
    fs::rename(&tmp, dir.join(&id))?;
    activate(dir, &id)
  })();
  if result.is_err() {
    let _ = fs::remove_dir_all(tmp);
  }
  result
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn local_configuration_identity_and_atomic_publication()
  -> pipeline::Result<()> {
    let settings = || Settings::new(b"root", b"params", 20, 24, 18);
    let id = settings().id();
    for other in [
      Settings::new(b"other", b"params", 20, 24, 18),
      Settings::new(b"root", b"other", 20, 24, 18),
      Settings::new(b"root", b"params", 21, 24, 18),
      Settings::new(b"root", b"params", 20, 25, 18),
      Settings::new(b"root", b"params", 20, 24, 19),
    ] {
      assert_ne!(id, other.id());
    }
    let dir = temporary(&std::env::temp_dir())?;
    fs::create_dir(&dir)?;
    let result = (|| -> pipeline::Result<()> {
      assert!(active(&dir).is_err());
      assert!(load(&dir, "../default", b"root").is_err());
      assert!(load(&dir, &id, b"root").is_err());
      let srs = dir.join("test.srs");
      fs::write(&srs, b"storage test only")?;
      // Storage/checksum checks do not deserialize a cryptographic key.
      publish(&dir, &settings(), b"key", &srs, None)?;
      assert_eq!(active(&dir)?, id);
      let entry = load(&dir, &id, b"root")?;
      assert_eq!(entry.key_bytes, b"key");
      assert_eq!(entry.srs_path, srs);
      assert!(load(&dir, &id, b"wrong backend").is_err());
      assert!(publish(&dir, &settings(), b"replacement", &srs, None).is_err());
      assert_eq!(load(&dir, &id, b"root")?.key_bytes, b"key");
      let changed = Settings::new(b"root", b"params", 21, 24, 18);
      assert!(
        publish(&dir, &changed, b"key", &dir.join("missing"), None).is_err()
      );
      assert_eq!(active(&dir)?, id);
      let moved = dir.join("moved.srs");
      fs::rename(&srs, &moved)?;
      reuse(&dir, &id, &moved, None)?;
      assert_eq!(load(&dir, &id, b"root")?.srs_path, moved);
      assert_eq!(load(&dir, &id, b"root")?.key_bytes, b"key");
      fs::remove_file(&moved)?;
      // Verification can load the key after the proving SRS is removed.
      assert!(load(&dir, &id, b"root").is_ok());
      fs::write(dir.join(&id).join("verifier.bin"), b"corrupt")?;
      assert!(load(&dir, &id, b"root").is_err());
      assert_eq!(fs::read_dir(&dir)?.count(), 2); // configuration + default
      Ok(())
    })();
    fs::remove_dir_all(dir)?;
    result
  }
}
