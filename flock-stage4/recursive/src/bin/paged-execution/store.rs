use anyhow::{Context, Result, ensure};
use flock_prover::field::F128;
use ix_flock_recursion::{MAX_PAGED_TREE_BYTES, PagedNodeProof};
use ixby_flock::{
  hash::pack_bytes, ixby::ixbf_decode::paged::endpoints::Component,
};
use serde_json::json;
use std::{
  io::{Read, Write},
  path::{Path, PathBuf},
  time::Instant,
};

pub(super) struct Store {
  directory: PathBuf,
  resume: bool,
}
impl Store {
  pub(super) fn open(
    directory: PathBuf,
    resume: bool,
    config: serde_json::Value,
  ) -> Result<Self> {
    if resume {
      let previous: serde_json::Value =
        serde_json::from_slice(&read(&directory.join("run.json"), 8192)?)?;
      ensure!(
        previous == config,
        "resume profile, class or source identity differs"
      );
    } else {
      std::fs::create_dir(&directory)?;
      write_new(
        &directory.join("run.json"),
        &serde_json::to_vec_pretty(&config)?,
      )?;
    }
    Ok(Self { directory, resume })
  }
  pub(super) fn existing(directory: PathBuf) -> Result<Self> {
    let config: serde_json::Value =
      serde_json::from_slice(&read(&directory.join("run.json"), 8192)?)?;
    ensure!(
      config["format"] == "IxBy/paged-execution-run/v0",
      "run directory format"
    );
    Ok(Self { directory, resume: true })
  }
  pub(super) fn directory(&self) -> &Path {
    &self.directory
  }
  pub(super) fn save_bytes(&self, name: &str, bytes: &[u8]) -> Result<()> {
    let path = self.directory.join(name);
    if path.exists() {
      ensure!(
        read(&path, bytes.len() as u64)? == bytes,
        "existing {name} differs"
      );
      return Ok(());
    }
    if let Some(parent) = path.parent() {
      std::fs::create_dir_all(parent)?;
    }
    let temporary =
      path.with_extension(format!("partial-{}", std::process::id()));
    write_new(&temporary, bytes)?;
    std::fs::rename(temporary, path)?;
    Ok(())
  }
  pub(super) fn get(&self, name: &str, width: usize) -> Result<PagedNodeProof> {
    let statement = words(
      &read(
        &self.directory.join(format!("{name}.statement")),
        u64::try_from(width)?.checked_mul(16).context("statement size")?,
      )?,
      width,
    )?;
    let proof = read(
      &self.directory.join(format!("{name}.flock")),
      MAX_PAGED_TREE_BYTES,
    )?;
    Ok(PagedNodeProof { statement, proof })
  }
  pub(super) fn prove(
    &self,
    name: &str,
    expected: &[F128],
    prove: impl FnOnce() -> Result<Vec<u8>>,
    verify: impl Fn(&[u8]) -> Result<()>,
  ) -> Result<()> {
    let started = Instant::now();
    let proof_name = format!("{name}.flock");
    let statement_name = format!("{name}.statement");
    if self.resume
      && self.directory.join(&proof_name).exists()
      && self.directory.join(&statement_name).exists()
    {
      let saved = self.get(name, expected.len())?;
      ensure!(saved.statement == expected, "cached {name} statement differs");
      verify(&saved.proof)
        .with_context(|| format!("cached {name} proof rejected"))?;
      eprintln!(
        "{}",
        json!({"event":"reused","name":name,
        "seconds":started.elapsed().as_secs_f64()})
      );
      return Ok(());
    }
    let proof = prove().with_context(|| format!("proving {name}"))?;
    verify(&proof).with_context(|| format!("verifying {name}"))?;
    // Replace only incomplete pairs in this matching run directory. Every
    // complete cached pair is verified above and is never silently replaced.
    for (filename, bytes) in [
      (&proof_name, proof.as_slice()),
      (&statement_name, words_bytes(expected).as_slice()),
    ] {
      let path = self.directory.join(filename);
      if self.resume && path.exists() {
        std::fs::remove_file(&path)?;
      }
      self.save_bytes(filename, bytes)?;
    }
    eprintln!(
      "{}",
      json!({"event":"proved","name":name,"bytes":proof.len(),
      "seconds":started.elapsed().as_secs_f64()})
    );
    Ok(())
  }
}
pub(super) fn leaf_name(component: Component, index: usize) -> String {
  format!("leaves/{:02}/{:07}/{index:010}", component as usize, index / 1024)
}
pub(super) fn node_name(
  component: Component,
  start: usize,
  count: usize,
) -> String {
  if count == 1 {
    return leaf_name(component, start);
  }
  format!(
    "nodes/{:02}/{count:010}/{:07}/{start:010}",
    component as usize,
    start / 1024
  )
}
pub(super) fn read(path: &Path, limit: u64) -> Result<Vec<u8>> {
  let mut bytes = Vec::new();
  std::fs::File::open(path)
    .with_context(|| format!("open {}", path.display()))?
    .take(limit + 1)
    .read_to_end(&mut bytes)?;
  ensure!(
    bytes.len() as u64 <= limit,
    "file exceeds bound: {}",
    path.display()
  );
  Ok(bytes)
}
pub(super) fn write_new(path: &Path, bytes: &[u8]) -> Result<()> {
  let mut file =
    std::fs::OpenOptions::new().write(true).create_new(true).open(path)?;
  file.write_all(bytes)?;
  file.sync_all()?;
  Ok(())
}
pub(super) fn words(bytes: &[u8], width: usize) -> Result<Vec<F128>> {
  ensure!(
    bytes.len() == width.checked_mul(16).context("statement width overflow")?,
    "statement byte width"
  );
  Ok(bytes.as_chunks::<16>().0.iter().map(|b| pack_bytes(b)).collect())
}
pub(super) fn words_bytes(words: &[F128]) -> Vec<u8> {
  words
    .iter()
    .flat_map(|v| {
      let mut bytes = [0; 16];
      bytes[..8].copy_from_slice(&v.lo.to_le_bytes());
      bytes[8..].copy_from_slice(&v.hi.to_le_bytes());
      bytes
    })
    .collect()
}
pub(super) fn join(
  component: Component,
  left: &[F128],
  right: &[F128],
) -> Result<Vec<F128>> {
  let shared = match component {
    Component::ConstructorIds => {
      anyhow::bail!("constructor ID component is indivisible")
    },
    Component::References => 5,
    Component::OutputBytes
    | Component::ProgramCommitment
    | Component::InputCommitment
    | Component::OutputCommitment => 7,
    _ => 3,
  };
  let width = component.range().len();
  ensure!(
    left.len() == width && right.len() == width,
    "component statement width"
  );
  let boundary = (width - shared) / 2;
  ensure!(left[..shared] == right[..shared], "component shared fields differ");
  ensure!(
    left[shared + boundary..] == right[shared..shared + boundary],
    "component boundary differs"
  );
  Ok([&left[..shared + boundary], &right[shared + boundary..]].concat())
}

#[cfg(test)]
mod tests {
  use super::*;
  #[test]
  fn resumption_checks_configuration_statement_and_proof_before_reuse() {
    let directory = std::env::temp_dir().join(format!(
      "ixby-execution-store-{}-{}",
      std::process::id(),
      std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos()
    ));
    let config = json!({"format":"IxBy/paged-execution-run/v0","test":true});
    let store = Store::open(directory.clone(), false, config.clone()).unwrap();
    let expected = [F128::ONE, F128::new(0, 1 << 63)];
    let proof = b"fixture proof";
    let verify = |bytes: &[u8]| {
      ensure!(bytes == proof, "wrong proof");
      Ok(())
    };
    store
      .prove("test-record", &expected, || Ok(proof.to_vec()), verify)
      .unwrap();
    drop(store);
    assert!(
      Store::open(directory.clone(), true, json!({"different":true})).is_err()
    );
    let store = Store::open(directory.clone(), true, config).unwrap();
    store
      .prove(
        "test-record",
        &expected,
        || panic!("cached proof was regenerated"),
        verify,
      )
      .unwrap();
    assert!(
      store
        .prove(
          "test-record",
          &[F128::ONE; 2],
          || panic!("wrong statement was regenerated"),
          verify
        )
        .is_err()
    );
    std::fs::write(directory.join("test-record.flock"), b"damaged").unwrap();
    assert!(
      store
        .prove(
          "test-record",
          &expected,
          || panic!("invalid complete proof was regenerated"),
          verify
        )
        .is_err()
    );
    // A crash between the two atomic writes leaves an incomplete pair, which
    // may be regenerated only after proving and checking its expected record.
    std::fs::remove_file(directory.join("test-record.statement")).unwrap();
    store
      .prove("test-record", &expected, || Ok(proof.to_vec()), verify)
      .unwrap();
    assert_eq!(store.get("test-record", 2).unwrap().statement, expected);
    assert!(store.save_bytes("test-record.flock", b"replacement").is_err());
    std::fs::remove_dir_all(directory).unwrap();
  }
}
