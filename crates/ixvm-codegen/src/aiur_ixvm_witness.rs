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
//! | ch | purpose                  | key            | value     |
//! |----|--------------------------|----------------|-----------|
//! | 0  | claim wire bytes         | claim_digest   | bytes     |
//! | 1  | assumption tree bytes    | tree.root      | bytes     |
//! | 2  | constant wire bytes      | const addr     | bytes     |
//! | 3  | Defn reducibility hint   | Defn addr      | single G  |
//! | 4  | blob raw bytes           | blob addr      | bytes     |
//!
//! An address is seeded on ch 2 iff it is a constant and on ch 4 iff it
//! is a blob; the two sets are disjoint. The kernel derives which it is
//! from Expr context, so no discriminator entry is shipped.
//!
//! Every byte-stream is blake3-verified kernel-side against its
//! content-addressed key.
//!
//! # Parallelism
//!
//! The byte scope is computed by `witness_scope`, which delegates to
//! `Env::bfs_closure` — a single sequential BFS that parses each closure
//! member exactly once. The hot phase that follows uses rayon:
//!
//! * **Byte→G conversion** (`add_entries`): for each addr in the
//!   closure, the per-const `(key, data)` tuple is built in parallel
//!   with rayon's `par_bridge`. Only the final IOBuffer assembly
//!   (extending channel arenas + inserting into the key→(idx,len)
//!   map) runs serially, since the arena `idx` is monotonic.

use multi_stark::p3_field::PrimeCharacteristicRing;
use rayon::prelude::*;
use rustc_hash::FxHashSet;

use aiur::G;
use aiur::execute::{IOBuffer, IOKeyInfo};
use ix_common::address::Address;
use ix_common::env::ReducibilityHints;
use ix_common::prim_addrs::PrimAddrs;
use ixon::Env;
use ixon::assumption_tree::AssumptionTree;
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

/// Per-channel entry produced by the parallel scan over the closure.
/// Sorted into the IOBuffer in a serial fold afterwards.
struct ChannelEntries {
  /// ch 2 const entries: `(key, bytes-as-G)`. Constants only — an address
  /// is seeded on ch 2 iff it is a constant and on ch 4 iff it is a blob,
  /// and the two sets are disjoint.
  consts: Vec<(Vec<G>, Vec<G>)>,
  /// ch 4 blob entries: `(key, bytes-as-G)`.
  blobs: Vec<(Vec<G>, Vec<G>)>,
  /// ch 3 Defn hint: `(key, hint-G)`.
  hints: Vec<(Vec<G>, G)>,
}

impl ChannelEntries {
  fn new() -> Self {
    Self { consts: Vec::new(), blobs: Vec::new(), hints: Vec::new() }
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
  let ch_blob = G::from_u8(4);

  // Pull the set of addrs we'll touch as a Vec for parallel iteration.
  let closure_vec: Vec<Address> = closure.iter().cloned().collect();

  // Phase A: parallel byte conversion per closure addr. Each thread
  // produces its own partial `ChannelEntries`. A constant goes to ch 2
  // and a blob to ch 4; nothing is seeded on both. The kernel derives
  // blob-vs-constant from Expr context, so no marker entry is needed.
  let partials: Vec<ChannelEntries> = closure_vec
    .par_chunks(256)
    .map(|chunk| {
      let mut p = ChannelEntries::new();
      for addr in chunk {
        let key = addr_key(addr);
        // Const lookup first.
        if let Some(lc) = env.consts.get(addr) {
          let data = bytes_to_g(lc.raw_bytes());
          p.consts.push((key, data));
          continue;
        }
        // Blob lookup.
        if let Some(blob) = env.blobs.get(addr) {
          let data = bytes_to_g(blob.value());
          p.blobs.push((key, data));
        }
        // Neither — closure includes some addresses (e.g. blob refs
        // from const.refs) that may not be in env.blobs if the env
        // doesn't carry them; skip silently to mirror the Lean side.
      }
      // Hints come from env.anon_hints (sidecar). Collect per chunk.
      for addr in chunk {
        if let Some(h) = env.anon_hints.get(addr) {
          p.hints.push((addr_key(addr), hint_to_g(&h)));
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
    for (key, hint) in p.hints {
      extend(io, ch_hint, key, vec![hint]);
    }
  }
}

/// Build a `Check { const_addr, assumptions=None }` claim witness
/// directly in Rust. Returns `(claim, claim_digest_input, io_buffer)`
/// ready to feed to `crate::ix::aiur_ixvm_runner::execute_ixvm`.
///
/// Mirrors `IxVM.ClaimHarness.buildClaimWitness` on the
/// `Claim.check addr none` branch: the witness scope seeds ch 2/3/4,
/// claim bytes go to ch 0. Asm-tree variant deferred — caller falls
/// back to Lean witness when `asm = Some _`.
pub fn build_claim_check_witness(
  env: &Env,
  target: &Address,
) -> Result<(Claim, Vec<G>, IOBuffer), String> {
  let closure: FxHashSet<Address> =
    witness_scope(env, std::slice::from_ref(target));

  let claim = Claim::Check { const_addr: target.clone(), assumptions: None };
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
  // ch 2/3/4: per-const/hint/blob entries — parallel byte conversion.
  add_entries_parallel(env, &closure, &mut io);

  Ok((claim, digest_key, io))
}

/// Every primitive address the kernel can name, as the Lean seeder sees
/// them: the parity table plus the reserved reduction markers. Built from
/// `ix_common::prim_addrs::PrimAddrs`, which the `prim-addrs` parity test
/// pins against `Ix.Tc.PrimAddrs`, so both seeders cover the same set by
/// construction.
fn prim_addrs() -> Vec<Address> {
  let mut v: Vec<Address> = PrimAddrs::lean_parity_table()
    .iter()
    .map(|(name, hex)| {
      Address::from_hex(hex)
        .unwrap_or_else(|| panic!("primitive {name}: invalid address hex"))
    })
    .collect();
  v.extend(PrimAddrs::reserved_marker_addrs().iter().map(|(_, a)| a.clone()));
  v
}

/// The full WITNESS byte scope for `roots`: the env dependency closure
/// plus every primitive present in the env.
///
/// `Env::bfs_closure` follows `refs`, each projection's `block` pointer,
/// AND — for a `Muts` block — every member/constructor projection
/// address it derives. That last edge is what the kernel needs: its
/// lazy `get_ci` synthesizes IPrj/CPrj/RPrj/DPrj wrapper addrs via
/// kernel-side blake3 and faults their bytes from ch 2, so wrappers
/// over a closure block must ship even when no `Constant.refs` edge
/// reaches them. The closure already carries them — expanding a wrapper
/// only re-adds its (already present) block — so no reverse scan of the
/// env is needed.
///
/// Primitives are seeded on top because the kernel FABRICATES references
/// to them while reducing — `Const(nat_succ_addr(), ..)` and friends are
/// built from addresses hardcoded in the Aiur source, not discovered by
/// walking `refs` — and `get_ci` then faults their bytes from ch 2 like
/// any other constant. Such a primitive need not appear anywhere in the
/// target's ref closure, so a closure-only scope aborts with `invalid IO
/// key`. Intersected with `env.consts`: a primitive the env does not
/// carry is one the check cannot reach.
///
/// Every witness builder goes through here, so the byte scope cannot
/// drift apart per call site. Mirrors
/// `Ix.IxVM.ClaimHarness.closureFromBase`.
fn witness_scope(env: &Env, roots: &[Address]) -> FxHashSet<Address> {
  let mut scope = env.bfs_closure(roots);
  for a in prim_addrs() {
    if env.consts.contains_key(&a) {
      scope.insert(a);
    }
  }
  scope
}

/// Shard `CheckEnv` witness: thin-frontier claim (see
/// `ixon::shard_claim`) plus the `bfs_closure` byte scope the kernel
/// needs for its blake3-synthesized projection addresses. The frontier
/// membership set stays at `closure_from` granularity — the claim's walk
/// only follows refs + Prj→block edges; the block→wrapper edges
/// `bfs_closure` adds are byte scope only.
pub fn build_shard_check_env_witness(
  env: &Env,
  owned: &[Address],
) -> Result<(Claim, Vec<G>, IOBuffer), String> {
  // Claim + THIN frontier from the shared convention module — the
  // single source of truth for shard CheckEnv digests (see
  // ixon::shard_claim; Lean mirror:
  // IxVM.ClaimHarness.shardCheckEnvClaimThin).
  let (claim, frontier) = ixon::shard_claim::shard_check_env_claim(env, owned)
    .ok_or_else(|| {
      "build_shard_check_env_witness: empty owned set".to_string()
    })?;
  let mut owned_sorted: Vec<Address> = owned.to_vec();
  owned_sorted.sort();
  let owned_tree =
    AssumptionTree::canonical(&owned_sorted).ok_or_else(|| {
      "build_shard_check_env_witness: empty owned set".to_string()
    })?;
  let asm_tree = AssumptionTree::canonical(&frontier);
  debug_assert_eq!(
    claim,
    Claim::CheckEnv {
      root: owned_tree.root(),
      assumptions: asm_tree.as_ref().map(|t| t.root()),
    }
  );
  let mut claim_bytes: Vec<u8> = Vec::new();
  claim.put(&mut claim_bytes);
  let digest = Address::hash(&claim_bytes);
  let digest_key = addr_key(&digest);

  let mut io = IOBuffer {
    data: rustc_hash::FxHashMap::default(),
    map: rustc_hash::FxHashMap::default(),
  };
  extend(&mut io, G::ZERO, digest_key.clone(), bytes_to_g(&claim_bytes));
  let byte_scope = witness_scope(env, owned);
  add_entries_parallel(env, &byte_scope, &mut io);
  extend(
    &mut io,
    G::ONE,
    addr_key(&owned_tree.root()),
    bytes_to_g(&owned_tree.ser()),
  );
  if let Some(at) = asm_tree {
    extend(&mut io, G::ONE, addr_key(&at.root()), bytes_to_g(&at.ser()));
  }

  Ok((claim, digest_key, io))
}
