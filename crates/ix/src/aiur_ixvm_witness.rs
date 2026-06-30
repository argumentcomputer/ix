//! Rust port of `IxVM.ClaimHarness.buildShardCheckEnvWitness`.
//!
//! Replaces the Lean-side IOBuffer construction (~92% of shard
//! wall time on heavy partitions) with a direct Rust implementation
//! that builds `aiur::execute::IOBuffer` without per-byte boxing
//! into Lean values.
//!
//! Mirrors the per-channel layout documented in
//! `Ix/IxVM/ClaimHarness.lean`:
//!
//! | Tier  | ch | purpose                  | key            | value     |
//! |-------|----|--------------------------|----------------|-----------|
//! | Ctrl  | 0  | claim wire bytes         | claim_digest   | bytes     |
//! | Ctrl  | 1  | assumption tree bytes    | tree.root      | bytes     |
//! | Const | 2  | constant wire bytes      | const addr     | bytes     |
//! | Const | 3  | Defn reducibility hint   | Defn addr      | single G  |
//! | Blob  | 4  | blob discriminator       | addr           | one byte  |
//! | Blob  | 5  | blob raw bytes           | blob addr      | bytes     |
//!
//! Soundness model unchanged — every byte-stream is blake3-verified
//! kernel-side against its content-addressed key.
//!
//! # Parallelism
//!
//! Two hot phases use rayon for thread-level parallelism:
//!
//! * **Closure walk** (`closure_from_set`): each owned addr's
//!   transitive walk runs on its own thread; results are unioned
//!   into a `DashSet` to dedupe across threads.
//! * **Byte→G conversion** (`add_entries`): for each addr in the
//!   closure, the per-const `(key, data)` tuple is built in parallel
//!   with rayon's `par_bridge`. Only the final IOBuffer assembly
//!   (extending channel arenas + inserting into the key→(idx,len)
//!   map) runs serially, since the arena `idx` is monotonic.

use dashmap::DashSet;
use multi_stark::p3_field::PrimeCharacteristicRing;
use rayon::prelude::*;
use rustc_hash::FxHashSet;

use aiur::G;
use aiur::execute::{IOBuffer, IOKeyInfo};
use ix_common::address::Address;
use ix_common::env::ReducibilityHints;
use ixon::Env;
use ixon::assumption_tree::AssumptionTree;
use ixon::constant::ConstantInfo;
use ixon::proof::Claim;

/// Append `data` to the per-channel arena and record `(idx, len)`
/// in the `(channel, key)` info map.
#[inline]
fn extend(io: &mut IOBuffer, channel: G, key: Vec<G>, data: Vec<G>) {
  let arena = io.data.entry(channel).or_default();
  let idx = arena.len();
  let len = data.len();
  arena.extend(data);
  io.map.insert((channel, key), IOKeyInfo { idx, len });
}

#[inline]
fn addr_key(addr: &Address) -> Vec<G> {
  addr.as_bytes().iter().map(|b| G::from_u8(*b)).collect()
}

#[inline]
fn bytes_to_g(bytes: &[u8]) -> Vec<G> {
  bytes.iter().map(|b| G::from_u8(*b)).collect()
}

/// Mirror of `IxVM.ClaimHarness.hintToG`:
/// `Opaque → 0`, `Abbrev → 0xFFFFFFFF`, `Regular n → min(1+n, 0xFFFFFFFE)`.
fn hint_to_g(h: &ReducibilityHints) -> G {
  let v: u64 = match h {
    ReducibilityHints::Opaque => 0,
    ReducibilityHints::Abbrev => 0xFFFF_FFFF,
    ReducibilityHints::Regular(n) => {
      let v = (1u64).saturating_add(u64::from(*n));
      v.min(0xFFFF_FFFE)
    },
  };
  G::from_u64(v)
}

/// Single-source transitive closure over `Constant.refs` + projection
/// blocks. Sequential BFS.
fn closure_from(env: &Env, target: &Address, visited: &DashSet<Address>) {
  let mut stack: Vec<Address> = vec![target.clone()];
  while let Some(addr) = stack.pop() {
    if !visited.insert(addr.clone()) {
      continue;
    }
    let Some(c) = env.get_const(&addr) else {
      continue;
    };
    for r in &c.refs {
      if !visited.contains(r) {
        stack.push(r.clone());
      }
    }
    let block = match &c.info {
      ConstantInfo::IPrj(p) => Some(&p.block),
      ConstantInfo::CPrj(p) => Some(&p.block),
      ConstantInfo::RPrj(p) => Some(&p.block),
      ConstantInfo::DPrj(p) => Some(&p.block),
      _ => None,
    };
    if let Some(b) = block {
      if !visited.contains(b) {
        stack.push(b.clone());
      }
    }
  }
}

/// Parallel transitive closure: each owned addr's walk runs on its
/// own thread, results unioned via the shared `DashSet`.
fn closure_from_set(env: &Env, owned: &[Address]) -> FxHashSet<Address> {
  let visited: DashSet<Address> = DashSet::new();
  owned.par_iter().for_each(|a| closure_from(env, a, &visited));
  visited.into_iter().collect()
}

/// Per-channel entry produced by the parallel scan over the closure.
/// Sorted into the IOBuffer in a serial fold afterwards.
struct ChannelEntries {
  /// ch 2 const entries: `(key, bytes-as-G)`.
  consts: Vec<(Vec<G>, Vec<G>)>,
  /// ch 5 blob entries: `(key, bytes-as-G)`.
  blobs: Vec<(Vec<G>, Vec<G>)>,
  /// ch 4 discriminator: `(key, [g])` — `g` is `1` for const, `0` for blob.
  discs: Vec<(Vec<G>, G)>,
  /// ch 3 Defn hint: `(key, hint-G)`.
  hints: Vec<(Vec<G>, G)>,
}

impl ChannelEntries {
  fn new() -> Self {
    Self {
      consts: Vec::new(),
      blobs: Vec::new(),
      discs: Vec::new(),
      hints: Vec::new(),
    }
  }
}

/// Build the per-channel `(key, data)` tuples for every addr in
/// `closure`. Byte→G conversion runs in parallel; the IOBuffer
/// assembly is sequential because arena `idx` must be monotonic.
fn add_entries_parallel(
  env: &Env,
  closure: &FxHashSet<Address>,
  io: &mut IOBuffer,
) {
  let ch_const = G::from_u8(2);
  let ch_hint = G::from_u8(3);
  let ch_disc = G::from_u8(4);
  let ch_blob = G::from_u8(5);
  let g_zero = G::ZERO;
  let g_one = G::ONE;

  // Pull the set of addrs we'll touch as a Vec for parallel iteration.
  let closure_vec: Vec<Address> = closure.iter().cloned().collect();

  // Phase A: parallel byte conversion per closure addr. Each thread
  // produces its own partial `ChannelEntries`.
  let partials: Vec<ChannelEntries> = closure_vec
    .par_chunks(256)
    .map(|chunk| {
      let mut p = ChannelEntries::new();
      for addr in chunk {
        let key = addr_key(addr);
        // Const lookup first.
        if let Some(lc) = env.consts.get(addr) {
          let data = bytes_to_g(lc.raw_bytes());
          p.consts.push((key.clone(), data));
          p.discs.push((key, g_one));
          continue;
        }
        // Blob lookup.
        if let Some(blob) = env.blobs.get(addr) {
          let data = bytes_to_g(blob.value());
          p.blobs.push((key.clone(), data));
          p.discs.push((key, g_zero));
          continue;
        }
        // Neither — closure includes some addresses (e.g. blob refs
        // from const.refs) that may not be in env.blobs if the env
        // doesn't carry them; skip silently to mirror the Lean side.
      }
      // Hints come from env.anon_hints (sidecar). Collect per chunk.
      for addr in chunk {
        if let Some(h) = env.anon_hints.get(addr) {
          p.hints.push((addr_key(addr), hint_to_g(h)));
        }
      }
      p
    })
    .collect();

  // Phase B: serial assembly into the IOBuffer.
  for p in partials {
    for (key, data) in p.consts {
      extend(io, ch_const, key, data);
    }
    for (key, data) in p.blobs {
      extend(io, ch_blob, key, data);
    }
    for (key, disc) in p.discs {
      extend(io, ch_disc, key, vec![disc]);
    }
    for (key, hint) in p.hints {
      extend(io, ch_hint, key, vec![hint]);
    }
  }
}

/// Build a `CheckEnv`-shaped shard witness directly in Rust. Returns
/// `(claim, claim_digest_input, io_buffer)` ready to feed to
/// `crate::ix::aiur_ixvm_runner::execute_ixvm`.
pub fn build_shard_check_env_witness(
  env: &Env,
  owned: &[Address],
) -> Result<(Claim, Vec<G>, IOBuffer), String> {
  let owned_set: FxHashSet<Address> = owned.iter().cloned().collect();

  // Transitive closure over `Constant.refs` + projection blocks, parallel
  // per owned addr.
  let closure = closure_from_set(env, owned);

  let mut closure_vec: Vec<Address> = closure.iter().cloned().collect();
  closure_vec.sort();
  let frontier: Vec<Address> = closure_vec
    .iter()
    .filter(|a| !owned_set.contains(*a))
    .cloned()
    .collect();
  let env_tree = AssumptionTree::canonical(&closure_vec)
    .ok_or_else(|| "build_shard_check_env_witness: empty closure".to_string())?;
  let asm_tree = AssumptionTree::canonical(&frontier);

  let claim = Claim::CheckEnv {
    root: env_tree.root(),
    assumptions: asm_tree.as_ref().map(|t| t.root()),
  };
  let mut claim_bytes: Vec<u8> = Vec::new();
  claim.put(&mut claim_bytes);
  let digest = Address::hash(&claim_bytes);
  let digest_key = addr_key(&digest);

  let mut io = IOBuffer {
    data: rustc_hash::FxHashMap::default(),
    map: rustc_hash::FxHashMap::default(),
  };
  // ch 0: claim bytes
  extend(&mut io, G::ZERO, digest_key.clone(), bytes_to_g(&claim_bytes));
  // ch 2/3/4/5 per-const/blob/hint entries — parallel byte conversion.
  add_entries_parallel(env, &closure, &mut io);
  // ch 1: env tree
  extend(
    &mut io,
    G::ONE,
    addr_key(&env_tree.root()),
    bytes_to_g(&env_tree.ser()),
  );
  // ch 1: asm tree (if present)
  if let Some(at) = asm_tree {
    extend(&mut io, G::ONE, addr_key(&at.root()), bytes_to_g(&at.ser()));
  }

  Ok((claim, digest_key, io))
}
