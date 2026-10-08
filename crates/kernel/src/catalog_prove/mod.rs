//! Catalog-bound incremental proving. Catalogs describe current snapshots;
//! immutable corpus objects and exact claims carry evidence across revisions.
//! Cryptographic verification is delegated to the same `ix` executable that
//! proves and aggregates, before a completed record is published.

mod plan;
mod run;
#[cfg(test)]
mod tests;

use ix_common::address::Address;
use ixon::{
  Env,
  catalog::{self, Catalog, CatalogStorage},
};
use serde_json::{Value, json};
use std::{
  fs,
  io::Read,
  path::{Path, PathBuf},
};

pub use run::run_catalog;

const SCHEMA: &str = "ix-catalog-proving/1";
const RECORD: &str = "proving.json";

/// Execution budgets affect scheduling, not the compatible proof profile.
pub struct Options {
  pub catalog: PathBuf,
  pub base: Option<PathBuf>,
  pub executable: PathBuf,
  pub allow_axioms: Option<PathBuf>,
  pub shards: usize,
  pub structural_above: usize,
  pub max_ram: usize,
  pub jobs: usize,
  pub exec_jobs: usize,
  pub lanes: usize,
  pub trace_shards: bool,
  pub plan_only: bool,
  pub verify_only: bool,
}

impl Options {
  pub fn from_json(value: &Value) -> Result<Self, String> {
    let optional_path = |key: &str| -> Result<Option<PathBuf>, String> {
      match value.get(key) {
        None | Some(Value::Null) => Ok(None),
        Some(Value::String(s)) if !s.is_empty() => Ok(Some(PathBuf::from(s))),
        _ => Err(format!("{key} must be a nonempty path or null")),
      }
    };
    let number = |key: &str, default| -> Result<usize, String> {
      value.get(key).map_or(Ok(default), |v| {
        let n = v
          .as_u64()
          .ok_or_else(|| format!("{key} must be a natural number"))?;
        usize::try_from(n).map_err(|_| format!("{key} is too large"))
      })
    };
    let flag = |key: &str| -> Result<bool, String> {
      value.get(key).map_or(Ok(false), |v| {
        v.as_bool().ok_or_else(|| format!("{key} must be boolean"))
      })
    };
    Ok(Self {
      catalog: PathBuf::from(string(value, "catalog")?),
      base: optional_path("base")?,
      executable: PathBuf::from(string(value, "executable")?),
      allow_axioms: optional_path("allowAxioms")?,
      shards: number("shards", 0)?,
      structural_above: number("structuralAbove", 4096)?,
      max_ram: number("maxRam", 0)?,
      jobs: number("jobs", 0)?,
      exec_jobs: number("execJobs", 0)?,
      lanes: number("lanes", 0)?,
      trace_shards: flag("traceShards")?,
      plan_only: flag("planOnly")?,
      verify_only: flag("verifyOnly")?,
    })
  }
}

fn read(path: &Path) -> Result<Vec<u8>, String> {
  fs::read(path).map_err(|e| format!("read {}: {e}", path.display()))
}

fn read_json(path: &Path) -> Result<Value, String> {
  serde_json::from_slice(&read(path)?)
    .map_err(|e| format!("parse {}: {e}", path.display()))
}

fn file_hash(path: &Path) -> Result<Address, String> {
  let mut file = fs::File::open(path)
    .map_err(|e| format!("open {}: {e}", path.display()))?;
  let mut hasher = blake3::Hasher::new();
  let mut buf = vec![0; 1024 * 1024];
  loop {
    let count = file
      .read(&mut buf)
      .map_err(|e| format!("hash {}: {e}", path.display()))?;
    if count == 0 {
      break;
    }
    hasher.update(&buf[..count]);
  }
  Ok(Address::from_blake3_hash(hasher.finalize()))
}

fn string<'a>(value: &'a Value, key: &str) -> Result<&'a str, String> {
  value
    .get(key)
    .and_then(Value::as_str)
    .ok_or_else(|| format!("missing string {key}"))
}

fn address(s: &str) -> Result<Address, String> {
  if s.len() != 64 || !s.bytes().all(|b| b.is_ascii_hexdigit()) {
    return Err(format!("invalid address {s:?}"));
  }
  Address::from_hex(s).ok_or_else(|| format!("invalid address {s}"))
}

fn addresses(value: &Value) -> Result<Vec<Address>, String> {
  let values = value.as_array().ok_or("expected address array")?;
  values
    .iter()
    .map(|v| address(v.as_str().ok_or("expected address string")?))
    .collect()
}

fn addresses_json(values: &[Address]) -> Value {
  json!(values.iter().map(Address::hex).collect::<Vec<_>>())
}

fn digest_json(value: &Value) -> Address {
  Address::hash(value.to_string().as_bytes())
}

fn atomic_write(path: &Path, bytes: &[u8]) -> Result<(), String> {
  use std::{
    io::Write,
    sync::atomic::{AtomicU64, Ordering},
  };
  static SERIAL: AtomicU64 = AtomicU64::new(0);
  let tmp = path.with_extension(format!(
    "tmp.{}.{}",
    std::process::id(),
    SERIAL.fetch_add(1, Ordering::Relaxed)
  ));
  let result = (|| {
    let mut file = fs::OpenOptions::new()
      .write(true)
      .create_new(true)
      .open(&tmp)
      .map_err(|e| format!("create {}: {e}", tmp.display()))?;
    file
      .write_all(bytes)
      .and_then(|()| file.sync_all())
      .map_err(|e| format!("write {}: {e}", tmp.display()))?;
    fs::rename(&tmp, path)
      .map_err(|e| format!("publish {}: {e}", path.display()))
  })();
  if result.is_err() {
    let _ = fs::remove_file(&tmp);
  }
  result
}

fn write_json(path: &Path, value: &Value) -> Result<(), String> {
  let mut bytes =
    serde_json::to_vec_pretty(value).map_err(|e| e.to_string())?;
  bytes.push(b'\n');
  atomic_write(path, &bytes)
}

struct Snapshot {
  catalog: Catalog,
  manifest_hash: Address,
  pieces: Vec<PathBuf>,
  addresses: Vec<Address>,
}

impl Snapshot {
  fn load(dir: &Path) -> Result<Self, String> {
    let manifest_bytes = read(&dir.join(catalog::MANIFEST_FILE))?;
    let cat = Catalog::from_bytes(&manifest_bytes)?;
    catalog::verify(&cat, dir, true)?;
    let pieces: Vec<_> = match &cat.storage {
      CatalogStorage::Fat(_) => cat
        .members
        .iter()
        .map(|m| dir.join(format!("{}.ixe", m.label)))
        .collect(),
      CatalogStorage::Chunked(_) => {
        return Err(
          "incremental proving currently requires a fat catalog".into(),
        );
      },
    };
    let mut addresses = Vec::new();
    for path in &pieces {
      let piece = catalog::open_piece(path)?;
      if !piece.index.assumptions.is_empty() {
        return Err("fat catalog member is not closed".into());
      }
      addresses.extend(piece.index.consts.iter().map(|c| c.addr.clone()));
    }
    addresses.sort_unstable();
    addresses.dedup();
    if addresses.is_empty() {
      return Err("cannot prove an empty catalog".into());
    }
    Ok(Self {
      catalog: cat,
      manifest_hash: Address::hash(&manifest_bytes),
      pieces,
      addresses,
    })
  }

  fn check_binding(&self, record: &Value) -> Result<(), String> {
    if string(record, "schema")? != SCHEMA
      || string(record, "snapshotHash")? != self.manifest_hash.hex()
      || string(record, "contentRoot")? != self.catalog.content_root.hex()
      || string(record, "membersRoot")? != self.catalog.members_root.hex()
    {
      return Err("proving record does not bind this catalog manifest and its logical roots".into());
    }
    Ok(())
  }

  fn check_coverage(&self, inventory: &plan::Inventory) -> Result<(), String> {
    if let Some(missing) = self
      .addresses
      .iter()
      .find(|a| inventory.addresses.binary_search(a).is_err())
    {
      return Err(format!(
        "current snapshot subject {} is not covered by the corpus",
        missing.hex()
      ));
    }
    Ok(())
  }
}

struct Artifacts {
  work: PathBuf,
  env_path: PathBuf,
  manifest_path: PathBuf,
  env: Env,
  inventory: plan::Inventory,
  manifest: crate::shard::ShardManifest,
  leaves: Vec<plan::Leaf>,
}

impl Artifacts {
  fn open(work: PathBuf) -> Result<Self, String> {
    let env_path = work.join("corpus.ixe");
    let manifest_path = work.join("shards.ixes");
    let env = Env::get_anon_mmap(&env_path)?;
    let inventory = plan::Inventory::read(&env)?;
    let manifest =
      crate::shard::ShardManifest::from_bytes(&read(&manifest_path)?)?;
    let leaves = plan::leaves(&env, &inventory, &manifest)?;
    Ok(Self { work, env_path, manifest_path, env, inventory, manifest, leaves })
  }

  fn recorded(
    dir: &Path,
    snapshot: &Snapshot,
    record: &Value,
    profile: &Value,
  ) -> Result<Self, String> {
    snapshot.check_binding(record)?;
    if string(record, "status")? != "certified" {
      return Err("base catalog has not been certified".into());
    }
    if record.get("profile") != Some(profile) {
      return Err(
        "incompatible proving profile (executable, parameters or axiom policy)"
          .into(),
      );
    }
    let work = dir.join("proving").join(digest_json(profile).hex());
    let artifacts = Self::open(work)?;
    if string(record, "corpusFileHash")?
      != file_hash(&artifacts.env_path)?.hex()
      || string(record, "partitionHash")?
        != file_hash(&artifacts.manifest_path)?.hex()
      || string(record, "corpusRoot")?
        != inventory_root(&artifacts.inventory)?.hex()
    {
      return Err("recorded corpus or partition changed".into());
    }
    snapshot.check_coverage(&artifacts.inventory)?;
    artifacts.inventory.check_axioms(&addresses(&profile["allowedAxioms"])?)?;
    if record.get("axioms")
      != Some(&addresses_json(&artifacts.inventory.axioms))
    {
      return Err("recorded axiom inventory does not match the corpus".into());
    }
    let stored = record["leaves"].as_array().ok_or("missing leaf records")?;
    if stored.len() != artifacts.leaves.len() {
      return Err("incomplete leaf inventory".into());
    }
    for (leaf, saved) in artifacts.leaves.iter().zip(stored) {
      let mut expected = leaf.json();
      expected["proof"] =
        Value::String(address(string(saved, "proof")?)?.hex());
      if saved != &expected {
        return Err(
          "recorded leaf claim or coverage differs from the partition".into(),
        );
      }
    }
    address(string(record, "rootProof")?)?;
    Ok(artifacts)
  }
}

fn inventory_root(inventory: &plan::Inventory) -> Result<Address, String> {
  ixon::merkle::merkle_root_canonical_sorted(&inventory.addresses)
    .ok_or_else(|| "empty corpus".into())
}

fn make_profile(
  options: &Options,
  prior: Option<&Value>,
) -> Result<Value, String> {
  let mut allowed = if let Some(path) = &options.allow_axioms {
    let text = fs::read_to_string(path)
      .map_err(|e| format!("read axiom policy {}: {e}", path.display()))?;
    text
      .lines()
      .map(|s| s.split('#').next().unwrap_or("").trim())
      .filter(|s| !s.is_empty())
      .map(address)
      .collect::<Result<Vec<_>, _>>()?
  } else if let Some(record) = prior {
    addresses(&record["profile"]["allowedAxioms"])?
  } else {
    Vec::new()
  };
  allowed.sort_unstable();
  allowed.dedup();
  Ok(
    json!({"schema": "ix-catalog-profile/1", "executable": file_hash(&options.executable)?.hex(),
    "objectFormat": Env::OBJECT_FORMAT, "structuralAbove": options.structural_above,
    "allowedAxioms": addresses_json(&allowed)}),
  )
}
