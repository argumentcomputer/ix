//! Aggregation store.

use super::{plan::SlotSpec, prepare::PreparedShard, statement::Statement};
use aiur::synthesis::{AiurProof, AiurSystem};
use ix_common::address::Address;
use ixon::Proof as IxonProof;
use rustc_hash::FxHashMap;
use std::{
  fs,
  path::{Path, PathBuf},
  sync::Arc,
};

pub(super) fn store_path(root: &Path, address: &Address) -> PathBuf {
  let hex = address.hex();
  root.join(&hex[0..2]).join(&hex[2..4]).join(&hex[4..6]).join(&hex[6..])
}

pub(super) fn read_store(
  root: &Path,
  address: &Address,
) -> Result<Vec<u8>, String> {
  let path = store_path(root, address);
  fs::read(&path).map_err(|error| format!("read {}: {error}", path.display()))
}

pub(super) fn write_store(
  root: &Path,
  bytes: &[u8],
) -> Result<Address, String> {
  let address = Address::hash(bytes);
  let path = store_path(root, &address);
  let parent = path.parent().ok_or("store path has no parent")?;
  fs::create_dir_all(parent)
    .map_err(|error| format!("create {}: {error}", parent.display()))?;
  fs::write(&path, bytes)
    .map_err(|error| format!("write {}: {error}", path.display()))?;
  Ok(address)
}

pub(super) fn decode_wrapper(bytes: &[u8]) -> Result<IxonProof, String> {
  let mut cursor = bytes;
  let proof = IxonProof::get(&mut cursor)?;
  if !cursor.is_empty() {
    return Err(format!("{} trailing bytes after proof wrapper", cursor.len()));
  }
  Ok(proof)
}

pub(super) fn load_input_proofs(
  proof_hexes: &str,
  store_dir: &Path,
  prepared: &[PreparedShard],
) -> Result<Vec<Arc<IxonProof>>, String> {
  let values: Vec<&str> =
    proof_hexes.lines().filter(|line| !line.is_empty()).collect();
  if values.len() != prepared.len() {
    return Err(format!(
      "aggregate requires exactly {} shard proofs; got {}",
      prepared.len(),
      values.len()
    ));
  }
  let by_digest: FxHashMap<Address, usize> = prepared
    .iter()
    .enumerate()
    .map(|(index, shard)| (Address::hash(&shard.statement.claim_bytes), index))
    .collect();
  if by_digest.len() != prepared.len() {
    return Err("two reconstructed shard claims have the same digest".into());
  }
  let mut proofs: Vec<Option<Arc<IxonProof>>> = vec![None; prepared.len()];
  for value in values {
    let address = Address::from_hex(value).ok_or_else(|| {
      format!("shard proof is not a 64-character address: {value}")
    })?;
    let bytes = read_store(store_dir, &address)?;
    if Address::hash(&bytes) != address {
      return Err(format!(
        "shard proof store object {} has the wrong digest",
        address.hex()
      ));
    }
    let wrapper = decode_wrapper(&bytes).map_err(|error| {
      format!("decode shard proof {}: {error}", address.hex())
    })?;
    let mut claim_bytes = Vec::new();
    wrapper.claim.put(&mut claim_bytes);
    let digest = Address::hash(&claim_bytes);
    let shard = by_digest.get(&digest).copied().ok_or_else(|| {
      format!("proof {} matches no manifest shard", address.hex())
    })?;
    if wrapper.claim != prepared[shard].statement.claim {
      return Err(format!(
        "proof {} hit a claim-digest collision for shard {}",
        address.hex(),
        prepared[shard].original_id
      ));
    }
    if proofs[shard].is_some() {
      return Err(format!(
        "more than one proof supplied for shard {}",
        prepared[shard].original_id
      ));
    }
    proofs[shard] = Some(Arc::new(wrapper));
  }
  proofs
    .into_iter()
    .enumerate()
    .map(|(index, proof)| {
      proof.ok_or_else(|| {
        format!("no proof supplied for shard {}", prepared[index].original_id)
      })
    })
    .collect()
}

pub(super) fn cache_address(
  cache_dir: &Path,
  key: &Address,
) -> Option<Address> {
  let path = cache_dir.join(key.hex());
  let raw = fs::read_to_string(path).ok()?;
  Address::from_hex(raw.trim())
}

pub(super) fn load_cached(
  system: &AiurSystem,
  store_dir: &Path,
  cache_dir: Option<&Path>,
  slot_index: usize,
  spec: &SlotSpec,
) -> Option<(AiurProof, Address)> {
  let cache_dir = cache_dir?;
  let address = cache_address(cache_dir, &spec.cache_key)?;
  let reject = |reason: &str| {
    eprintln!(
      "[aggregate] slot {slot_index}: cache miss (wrapper {} rejected: {reason})",
      address.hex()
    );
  };
  let bytes = match read_store(store_dir, &address) {
    Ok(bytes) => bytes,
    Err(error) => {
      reject(&error);
      return None;
    },
  };
  if Address::hash(&bytes) != address {
    reject("store object has a different content digest");
    return None;
  }
  let wrapper = match decode_wrapper(&bytes) {
    Ok(wrapper) => wrapper,
    Err(error) => {
      reject(&error);
      return None;
    },
  };
  if wrapper.claim != spec.statement.claim {
    reject("bundled claim does not match the expected statement");
    return None;
  }
  let proof = match AiurProof::from_bytes(&wrapper.proof) {
    Ok(proof) => proof,
    Err(error) => {
      reject(&format!("proof deserialization failed: {error}"));
      return None;
    },
  };
  if let Err(error) = system.verify(&spec.outer_claim, &proof) {
    reject(&format!("native verification failed: {error:?}"));
    return None;
  }
  eprintln!("[aggregate] slot {slot_index}: cache hit {}", address.hex());
  Some((proof, address))
}

pub(super) fn wrapper_bytes(
  statement: &Statement,
  proof: &AiurProof,
) -> Result<Vec<u8>, String> {
  let proof_bytes = proof.to_bytes().map_err(|error| {
    format!("aggregate proof serialization failed: {error}")
  })?;
  let wrapper = IxonProof::new(statement.claim.clone(), proof_bytes);
  let mut bytes = Vec::new();
  wrapper.put(&mut bytes);
  Ok(bytes)
}

pub(super) fn wrapper_address(
  statement: &Statement,
  proof: &AiurProof,
) -> Result<Address, String> {
  Ok(Address::hash(&wrapper_bytes(statement, proof)?))
}

pub(super) fn persist_wrapper(
  store_dir: &Path,
  statement: &Statement,
  proof: &AiurProof,
) -> Result<Address, String> {
  write_store(store_dir, &statement.claim_bytes)?;
  write_store(store_dir, &wrapper_bytes(statement, proof)?)
}

pub(super) fn persist_cached(
  store_dir: &Path,
  cache_dir: Option<&Path>,
  write_outputs: bool,
  slot_index: usize,
  spec: &SlotSpec,
  proof: &AiurProof,
) -> Option<Address> {
  if !write_outputs {
    return None;
  }
  let cache_dir = cache_dir?;
  match (|| -> Result<Address, String> {
    let address = persist_wrapper(store_dir, &spec.statement, proof)?;
    fs::create_dir_all(cache_dir).map_err(|error| {
      format!("create aggregate cache {}: {error}", cache_dir.display())
    })?;
    let destination = cache_dir.join(spec.cache_key.hex());
    let temporary = cache_dir.join(format!(
      "{}.tmp.{}.{}",
      spec.cache_key.hex(),
      std::process::id(),
      slot_index
    ));
    fs::write(&temporary, format!("{}\n", address.hex())).map_err(|error| {
      format!("write cache index {}: {error}", temporary.display())
    })?;
    fs::rename(&temporary, &destination).map_err(|error| {
      format!(
        "publish cache index {} -> {}: {error}",
        temporary.display(),
        destination.display()
      )
    })?;
    Ok(address)
  })() {
    Ok(address) => {
      eprintln!(
        "[aggregate] slot {slot_index}: cached proof {}",
        address.hex()
      );
      Some(address)
    },
    Err(error) => {
      eprintln!(
        "[aggregate] slot {slot_index}: warning: could not persist cache entry: {error}"
      );
      None
    },
  }
}
