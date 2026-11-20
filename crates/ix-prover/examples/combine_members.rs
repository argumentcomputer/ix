//! Membership of named constants in an environment's aggregate CheckEnv
//! claim: the claim `ix prove --aggregate` proves for `ENV` under the
//! partition `MANIFEST`, and, for each name, its constant's Ixon address and
//! the Merkle path from that address's leaf to the claim's subject root, in
//! the format `ix_aggr` reads discharge paths in (`1 ‖ steps ‖ (side ‖
//! sibling)*`), which `AiurCombine::aiur_combine` reads too.
//!
//! ```text
//! combine_members ENV.ixe MANIFEST.ixes OUT_DIR [STRUCTURAL_ABOVE] -- NAME...
//! ```
//!
//! Writes `ix-claim.bin` (the expected root claim), `root.bin` (its subject
//! root), and per name `NAME.addr` and `NAME.path`, and checks every path
//! against the root before writing it.
use aggregate_controller::{advice::path_payload, plan, prepare, statement};
use ix_common::address::Address;
use ix_prover::request::Environment;
use ixon::{Claim, shard::ShardManifest};
use serde_json::json;
use std::{error::Error, fs, path::Path};

type R<T> = Result<T, Box<dyn Error>>;

fn fold(leaf: &Address, path: &[u8]) -> R<Address> {
  let (&present, rest) = path.split_first().ok_or("empty path")?;
  if present != 1 {
    return Err("absent path".into());
  }
  let (&steps, mut rest) = rest.split_first().ok_or("no step count")?;
  let mut hash = ixon::merkle::leaf_hash(leaf);
  for _ in 0..steps {
    let side = rest[0];
    let sibling = Address::from_slice(&rest[1..33]).map_err(|e| format!("{e:?}"))?;
    hash = if side == 0 {
      ixon::merkle::node_hash(&sibling, &hash)
    } else {
      ixon::merkle::node_hash(&hash, &sibling)
    };
    rest = &rest[33..];
  }
  if !rest.is_empty() {
    return Err("trailing path bytes".into());
  }
  Ok(hash)
}

fn main() -> R<()> {
  let args: Vec<String> = std::env::args().skip(1).collect();
  let split = args.iter().position(|a| a == "--").ok_or("usage: combine_members ENV.ixe MANIFEST.ixes OUT_DIR [STRUCTURAL_ABOVE] -- NAME...")?;
  let (head, names) = (&args[..split], &args[split + 1..]);
  if !(3..=4).contains(&head.len()) || names.is_empty() {
    return Err("usage: combine_members ENV.ixe MANIFEST.ixes OUT_DIR [STRUCTURAL_ABOVE] -- NAME...".into());
  }
  let environment = Environment::open(head[0].as_ref())?;
  let env = environment.env();
  let manifest = ShardManifest::from_bytes(&fs::read(&head[1])?)?;
  let structural_above: usize = head.get(3).map(|v| v.parse()).transpose()?.unwrap_or(0);
  let ctx = aggregate_controller::claim_context(env, false)?;
  let prepared = prepare::prepare_run(&ctx, env, &manifest)?;
  let specs = plan::build_statement_specs(&prepared, structural_above)?;
  let root: &statement::Statement = &specs.last().ok_or("no root statement")?.statement;
  prepare::validate_root_statement(&prepared, &specs.last().unwrap().statement)?;
  let Claim::CheckEnv { root: subject_root, assumptions, .. } = &root.claim else {
    return Err("the root claim is not a CheckEnv".into());
  };
  if assumptions.is_some() {
    return Err("the root claim has assumptions".into());
  }
  let out = Path::new(&head[2]);
  fs::create_dir_all(out)?;
  fs::write(out.join("ix-claim.bin"), &root.claim_bytes)?;
  fs::write(out.join("root.bin"), subject_root.as_bytes())?;
  let mut members = Vec::new();
  for name in names {
    let named = env
      .named
      .iter()
      .find(|entry| entry.key().pretty() == *name)
      .map(|entry| entry.value().clone())
      .ok_or_else(|| format!("no constant named {name}"))?;
    let addr = named.addr.clone();
    let owner = *prepared
      .owner_by_address
      .get(&addr)
      .ok_or_else(|| format!("{name} ({}) is not a subject of the claim", addr.hex()))?;
    let path = root
      .subjects
      .merkle_proof(&addr, owner)
      .ok_or_else(|| format!("no path for {name}"))?;
    let payload = path_payload(Some(&path))?;
    if fold(&addr, &payload)? != *subject_root {
      return Err(format!("the path of {name} does not reach the subject root").into());
    }
    fs::write(out.join(format!("{name}.addr")), addr.as_bytes())?;
    fs::write(out.join(format!("{name}.path")), &payload)?;
    members.push(json!({ "name": name, "address": addr.hex(), "steps": path.len(), "shard": owner }));
  }
  let report = json!({
    "claim_blake3": blake3::hash(&root.claim_bytes).to_hex().to_string(),
    "subject_root": subject_root.hex(),
    "constants": prepared.env_count,
    "shards": manifest.shards.len(),
    "structural_above": structural_above,
    "members": members,
  });
  fs::write(out.join("members.json"), serde_json::to_vec_pretty(&report)?)?;
  println!("{report}");
  Ok(())
}
