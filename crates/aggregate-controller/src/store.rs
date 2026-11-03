//! The content-addressed store, the aggregate cache and the shard-proof
//! index.

use crate::{
  plan::SlotSpec, prepare::PreparedShard, protocol::ChildKind,
  statement::Statement,
};
use ix_common::address::Address;
use ixon::Proof as IxonProof;
use rustc_hash::FxHashMap;
use std::{
  fs,
  path::{Path, PathBuf},
  sync::Arc,
};

pub fn store_path(root: &Path, address: &Address) -> PathBuf {
  let hex = address.hex();
  root.join(&hex[0..2]).join(&hex[2..4]).join(&hex[4..6]).join(&hex[6..])
}

pub fn read_store(root: &Path, address: &Address) -> Result<Vec<u8>, String> {
  let path = store_path(root, address);
  fs::read(&path).map_err(|error| format!("read {}: {error}", path.display()))
}

pub fn write_store(root: &Path, bytes: &[u8]) -> Result<Address, String> {
  let address = Address::hash(bytes);
  let path = store_path(root, &address);
  let parent = path.parent().ok_or("store path has no parent")?;
  fs::create_dir_all(parent)
    .map_err(|error| format!("create {}: {error}", parent.display()))?;
  // Published by rename so a reader never sees a partial object, and
  // several writers of one object (other threads, other processes) each
  // rename their own complete copy into place.
  static WRITES: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
  let temporary = parent.join(format!(
    "{}.tmp.{}.{}",
    address.hex(),
    std::process::id(),
    WRITES.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
  ));
  fs::write(&temporary, bytes)
    .map_err(|error| format!("write {}: {error}", temporary.display()))?;
  fs::rename(&temporary, &path).map_err(|error| {
    format!("publish {} -> {}: {error}", temporary.display(), path.display())
  })?;
  Ok(address)
}

pub fn decode_wrapper(bytes: &[u8]) -> Result<IxonProof, String> {
  let mut cursor = bytes;
  let proof = IxonProof::get(&mut cursor)?;
  if !cursor.is_empty() {
    return Err(format!("{} trailing bytes after proof wrapper", cursor.len()));
  }
  Ok(proof)
}

/// The proofs supplied to a run, each bound by claim digest to a manifest
/// shard (a claim proof) or to an aggregate slot of the plan (a proof of
/// that slot's statement, which covers the subtree under it).
pub struct InputProofs {
  /// Per manifest shard.
  pub claims: Vec<Option<Arc<IxonProof>>>,
  /// Per plan slot, with the wrapper's store address.
  pub aggregates: Vec<Option<(Arc<IxonProof>, Address)>>,
}

impl InputProofs {
  pub fn none(shards: usize, slots: usize) -> Self {
    Self { claims: vec![None; shards], aggregates: vec![None; slots] }
  }
}

/// Reads the supplied proof wrappers (one store address per line) and binds
/// each to the shard claim or aggregate slot statement it proves. A proof of
/// no statement in the plan, or a second proof of one, is rejected; which of
/// them a run needs is decided once the cache has been consulted.
pub fn load_input_proofs<C>(
  proof_hexes: &str,
  store_dir: &Path,
  prepared: &[PreparedShard],
  specs: &[SlotSpec<C>],
) -> Result<InputProofs, String> {
  let by_digest: FxHashMap<Address, usize> = prepared
    .iter()
    .enumerate()
    .map(|(index, shard)| (Address::hash(&shard.statement.claim_bytes), index))
    .collect();
  if by_digest.len() != prepared.len() {
    return Err("two reconstructed shard claims have the same digest".into());
  }
  let mut slots_by_digest: FxHashMap<Address, Vec<usize>> =
    FxHashMap::default();
  for (index, spec) in specs.iter().enumerate() {
    if spec.kind == ChildKind::Aggr {
      slots_by_digest
        .entry(Address::hash(&spec.statement.claim_bytes))
        .or_default()
        .push(index);
    }
  }
  let mut inputs = InputProofs::none(prepared.len(), specs.len());
  for value in proof_hexes.lines().filter(|line| !line.is_empty()) {
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
    let wrapper = Arc::new(decode_wrapper(&bytes).map_err(|error| {
      format!("decode shard proof {}: {error}", address.hex())
    })?);
    let mut claim_bytes = Vec::new();
    wrapper.claim.put(&mut claim_bytes);
    let digest = Address::hash(&claim_bytes);
    if let Some(&shard) = by_digest.get(&digest) {
      if wrapper.claim != prepared[shard].statement.claim {
        return Err(format!(
          "proof {} hit a claim-digest collision for shard {}",
          address.hex(),
          prepared[shard].original_id
        ));
      }
      if inputs.claims[shard].is_some() {
        return Err(format!(
          "more than one proof supplied for shard {}",
          prepared[shard].original_id
        ));
      }
      inputs.claims[shard] = Some(wrapper);
    } else if let Some(slots) = slots_by_digest.get(&digest) {
      for &slot in slots {
        if wrapper.claim != specs[slot].statement.claim {
          return Err(format!(
            "proof {} hit a claim-digest collision for slot {slot}",
            address.hex()
          ));
        }
        if inputs.aggregates[slot].is_some() {
          return Err(format!("more than one proof supplied for slot {slot}"));
        }
        inputs.aggregates[slot] = Some((wrapper.clone(), address.clone()));
      }
    } else {
      return Err(format!(
        "proof {} matches no statement of the manifest plan",
        address.hex()
      ));
    }
  }
  Ok(inputs)
}

pub fn cache_address(cache_dir: &Path, key: &Address) -> Option<Address> {
  let path = cache_dir.join(key.hex());
  let raw = fs::read_to_string(path).ok()?;
  Address::from_hex(raw.trim())
}

/// A slot's proof from the aggregate cache, checked against the slot's
/// statement and verified natively; `None` (with the reason on stderr) when
/// absent or not acceptable. `decode` and `verify` are the backend's.
pub fn load_cached<C, P>(
  store_dir: &Path,
  cache_dir: Option<&Path>,
  slot_index: usize,
  spec: &SlotSpec<C>,
  decode: impl FnOnce(&[u8]) -> Result<P, String>,
  verify: impl FnOnce(&C, &P) -> Result<(), String>,
) -> Option<(P, Address)> {
  load_cached_claim(
    store_dir,
    cache_dir,
    &format!("slot {slot_index}"),
    &spec.cache_key,
    &spec.statement.claim,
    &spec.outer_claim,
    decode,
    verify,
  )
}

/// [`load_cached`] for any proof the cache holds under `cache_key`: a
/// proof of `claim`, whose outer claim is `outer`. `label` names it in the
/// log.
#[allow(clippy::too_many_arguments)]
pub fn load_cached_claim<C, P>(
  store_dir: &Path,
  cache_dir: Option<&Path>,
  label: &str,
  cache_key: &Address,
  claim: &ixon::Claim,
  outer: &C,
  decode: impl FnOnce(&[u8]) -> Result<P, String>,
  verify: impl FnOnce(&C, &P) -> Result<(), String>,
) -> Option<(P, Address)> {
  let cache_dir = cache_dir?;
  let address = cache_address(cache_dir, cache_key)?;
  let reject = |reason: &str| {
    eprintln!(
      "[aggregate] {label}: cache miss (wrapper {} rejected: {reason})",
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
  if wrapper.claim != *claim {
    reject("bundled claim does not match the expected statement");
    return None;
  }
  let proof = match decode(&wrapper.proof) {
    Ok(proof) => proof,
    Err(error) => {
      reject(&format!("proof deserialization failed: {error}"));
      return None;
    },
  };
  if let Err(error) = verify(outer, &proof) {
    reject(&format!("native verification failed: {error}"));
    return None;
  }
  eprintln!("[aggregate] {label}: cache hit {}", address.hex());
  Some((proof, address))
}

/// The `ixon` proof wrapper of `statement`'s claim; `proof` is the
/// backend's encoding of the proof, or why it could not be encoded.
pub fn wrapper_bytes(
  statement: &Statement,
  proof: Result<Vec<u8>, String>,
) -> Result<Vec<u8>, String> {
  claim_wrapper_bytes(&statement.claim, proof)
}

/// [`wrapper_bytes`] for any claim.
pub fn claim_wrapper_bytes(
  claim: &ixon::Claim,
  proof: Result<Vec<u8>, String>,
) -> Result<Vec<u8>, String> {
  let proof_bytes = proof.map_err(|error| {
    format!("aggregate proof serialization failed: {error}")
  })?;
  let wrapper = IxonProof::new(claim.clone(), proof_bytes);
  let mut bytes = Vec::new();
  wrapper.put(&mut bytes);
  Ok(bytes)
}

pub fn persist_wrapper(
  store_dir: &Path,
  statement: &Statement,
  proof: Result<Vec<u8>, String>,
) -> Result<Address, String> {
  persist_claim_wrapper(
    store_dir,
    &statement.claim,
    &statement.claim_bytes,
    proof,
  )
}

/// [`persist_wrapper`] for any claim; `claim_bytes` is its serialization.
pub fn persist_claim_wrapper(
  store_dir: &Path,
  claim: &ixon::Claim,
  claim_bytes: &[u8],
  proof: Result<Vec<u8>, String>,
) -> Result<Address, String> {
  write_store(store_dir, claim_bytes)?;
  write_store(store_dir, &claim_wrapper_bytes(claim, proof)?)
}

/// Persists a slot's proof and publishes its cache entry. `Ok(None)` when
/// the run writes nothing or has no cache; a failure is an error, since a
/// run's success promises that its proofs are where a later run (a resume,
/// or the final run after subtree lanes) will look for them.
pub fn persist_cached<C>(
  store_dir: &Path,
  cache_dir: Option<&Path>,
  write_outputs: bool,
  slot_index: usize,
  spec: &SlotSpec<C>,
  proof: impl FnOnce() -> Result<Vec<u8>, String>,
) -> Result<Option<Address>, String> {
  persist_cached_claim(
    store_dir,
    cache_dir,
    write_outputs,
    &format!("slot {slot_index}"),
    &spec.cache_key,
    &spec.statement.claim,
    &spec.statement.claim_bytes,
    proof,
  )
}

/// [`persist_cached`] for any proof of `claim` (serialized as
/// `claim_bytes`) cached under `cache_key`. `label` names it in the log.
#[allow(clippy::too_many_arguments)]
pub fn persist_cached_claim(
  store_dir: &Path,
  cache_dir: Option<&Path>,
  write_outputs: bool,
  label: &str,
  cache_key: &Address,
  claim: &ixon::Claim,
  claim_bytes: &[u8],
  proof: impl FnOnce() -> Result<Vec<u8>, String>,
) -> Result<Option<Address>, String> {
  static PUBLISHES: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
  if !write_outputs {
    return Ok(None);
  }
  let Some(cache_dir) = cache_dir else {
    return Ok(None);
  };
  match (|| -> Result<Address, String> {
    let address =
      persist_claim_wrapper(store_dir, claim, claim_bytes, proof())?;
    fs::create_dir_all(cache_dir).map_err(|error| {
      format!("create aggregate cache {}: {error}", cache_dir.display())
    })?;
    let destination = cache_dir.join(cache_key.hex());
    let temporary = cache_dir.join(format!(
      "{}.tmp.{}.{}",
      cache_key.hex(),
      std::process::id(),
      PUBLISHES.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
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
      eprintln!("[aggregate] {label}: cached proof {}", address.hex());
      Ok(Some(address))
    },
    Err(error) => Err(format!("{label}: could not persist its proof: {error}")),
  }
}

/// The shard-proof index entry of a claim, written like Stage 1 writes it.
pub fn index_claim(
  index_dir: &Path,
  claim_bytes: &[u8],
  address: &Address,
) -> Result<(), String> {
  fs::create_dir_all(index_dir)
    .map_err(|error| format!("create {}: {error}", index_dir.display()))?;
  let digest = Address::hash(claim_bytes);
  let temporary =
    index_dir.join(format!("{}.tmp.{}", digest.hex(), std::process::id()));
  fs::write(&temporary, format!("{}\n", address.hex()))
    .and_then(|()| fs::rename(&temporary, index_dir.join(digest.hex())))
    .map_err(|error| format!("shard-proof index: {error}"))
}
