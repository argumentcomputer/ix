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
///
/// A member of `stop` is included but not expanded: it is ingressed as a
/// type-only axiom, so its own references are never followed. That halt is
/// the whole saving — without it a shard drags in its frontier's entire
/// transitive closure.
fn closure_from(
  env: &Env,
  target: &Address,
  visited: &DashSet<Address>,
  stop: &FxHashSet<Address>,
) {
  let mut stack: Vec<Address> = vec![target.clone()];
  while let Some(addr) = stack.pop() {
    if !visited.insert(addr.clone()) {
      continue;
    }
    if stop.contains(&addr) {
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
    if let Some(b) = block
      && !visited.contains(b)
    {
      stack.push(b.clone());
    }
  }
}

/// Parallel transitive closure: each owned addr's walk runs on its
/// own thread, results unioned via the shared `DashSet`.
fn closure_from_set(
  env: &Env,
  owned: &[Address],
  stop: &FxHashSet<Address>,
) -> FxHashSet<Address> {
  let visited: DashSet<Address> = DashSet::new();
  owned.par_iter().for_each(|a| closure_from(env, a, &visited, stop));
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
///
/// `addr_only` entries ship position-only: a kind-2 discriminator and nothing else —
/// no ch-2 bytes for the kernel to blake3, no hint. The kernel fabricates
/// a fail-closed node at their position (`load_with_deps` kind-2 arm), so
/// refs to them resolve instead of dangling, and any semantic use aborts
/// naming the address.
fn add_entries_parallel(
  env: &Env,
  closure: &FxHashSet<Address>,
  addr_only: &FxHashSet<Address>,
  io: &mut IOBuffer,
) {
  let ch_const = G::from_u8(2);
  let ch_hint = G::from_u8(3);
  let ch_disc = G::from_u8(4);
  let ch_blob = G::from_u8(5);
  let g_zero = G::ZERO;
  let g_one = G::ONE;
  let g_addr_only = G::from_u8(2);

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
        if addr_only.contains(addr) {
          p.discs.push((key, g_addr_only));
          continue;
        }
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
        }
        // Neither — closure includes some addresses (e.g. blob refs
        // from const.refs) that may not be in env.blobs if the env
        // doesn't carry them; skip silently to mirror the Lean side.
      }
      // Hints come from env.anon_hints (sidecar). Collect per chunk.
      for addr in chunk {
        if !addr_only.contains(addr)
          && let Some(h) = env.anon_hints.get(addr)
        {
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
    for (key, disc) in p.discs {
      extend(io, ch_disc, key, vec![disc]);
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
/// `Claim.check addr none` branch: closure-from-addr seeds ch 2/3/4/5,
/// claim bytes go to ch 0. Asm-tree variant deferred — caller falls
/// back to Lean witness when `asm = Some _`.
pub fn build_claim_check_witness(
  env: &Env,
  target: &Address,
) -> Result<(Claim, Vec<G>, IOBuffer), String> {
  // Transitive closure rooted at `target`.
  let closure: FxHashSet<Address> =
    closure_from_set(env, std::slice::from_ref(target), &FxHashSet::default());

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
  // ch 2/3/4/5: per-const/blob/hint entries — parallel byte conversion.
  // Full-closure single-const checks ship no address-only entries.
  add_entries_parallel(env, &closure, &FxHashSet::default(), &mut io);

  Ok((claim, digest_key, io))
}

/// Build a `CheckEnv`-shaped shard witness directly in Rust. Returns
/// `(claim, claim_digest_input, io_buffer)` ready to feed to
/// `crate::ix::aiur_ixvm_runner::execute_ixvm`.
/// `owned` / `foreign` / `stubbed` all come from the `.ixes` manifest: the
/// blocks this shard checks, the blocks it ingresses without checking, and the
/// subset of those ingressed as type-only axioms.
///
/// The ingress set is taken from the manifest rather than re-derived here.
/// Walking the environment cannot reproduce it: stopping at a stub would miss
/// the constants the stub's own TYPE mentions, which still have to resolve,
/// and following them needs the type-reference graph that only the profile
/// carries. Taking the set wholesale also removes any chance of the host and
/// the packer disagreeing about what a shard ingresses.
pub fn build_shard_check_env_witness(
  env: &Env,
  owned: &[Address],
  foreign: &[Address],
  stubbed: &[Address],
  addr_only: &FxHashSet<Address>,
) -> Result<(Claim, Vec<G>, IOBuffer), String> {
  let owned_set: FxHashSet<Address> = owned.iter().cloned().collect();
  // A shard never stubs what it owns.
  let stub_set: FxHashSet<Address> =
    stubbed.iter().filter(|a| !owned_set.contains(*a)).cloned().collect();
  // Address-only entries are the stubs a classification run proved
  // unconsulted; they ship position-only. Only a stub may drop to
  // address-only — the claim and trees are
  // identical either way, so the split never reaches the digest.
  let addr_only_set: FxHashSet<Address> =
    addr_only.iter().filter(|a| stub_set.contains(*a)).cloned().collect();

  let mut closure: FxHashSet<Address> =
    owned.iter().chain(foreign.iter()).cloned().collect();
  // The manifest lists BLOCKS, and blobs are not blocks — but a constant's
  // ref table points at them for string and Nat literals, and the kernel
  // reads their bytes wherever they occur. Pull in every blob any ingressed
  // constant references — INCLUDING stubs': whether a given stub ships as
  // a type-only stub or address-only is a per-run witness decision made AFTER
  // the claim exists, and the env tree (hence the claim digest) must not
  // depend on it. An unread blob leaf costs nothing — the kernel loads
  // blob bytes on demand, so bytes nobody converts are never hashed.
  //
  // Constant refs pointing outside the ingress set are left out on purpose:
  // they get a discriminator below but no bytes, so they poison if an
  // expression actually dereferences one.
  let referenced_blobs: Vec<Address> = closure
    .iter()
    .filter_map(|a| env.get_const(a))
    .flat_map(|c| c.refs.clone())
    .filter(|r| env.blobs.contains_key(r))
    .collect();
  closure.extend(referenced_blobs);

  let mut closure_vec: Vec<Address> = closure.iter().cloned().collect();
  closure_vec.sort();
  let frontier: Vec<Address> =
    closure_vec.iter().filter(|a| !owned_set.contains(*a)).cloned().collect();
  let env_tree = AssumptionTree::canonical(&closure_vec).ok_or_else(|| {
    "build_shard_check_env_witness: empty closure".to_string()
  })?;
  let asm_tree = AssumptionTree::canonical(&frontier);
  // Only stubs actually reached: the partition works on blocks, so it may
  // name constants this shard's walk never touched.
  let mut stub_vec: Vec<Address> =
    stub_set.iter().filter(|a| closure.contains(*a)).cloned().collect();
  stub_vec.sort();
  let stub_tree = AssumptionTree::canonical(&stub_vec);

  let claim = Claim::CheckEnv {
    root: env_tree.root(),
    assumptions: asm_tree.as_ref().map(|t| t.root()),
    stubbed: stub_tree.as_ref().map(|t| t.root()),
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
  // Classified-unconsulted stubs ship ADDRESS-ONLY: position-only, no
  // bytes, no hashing; the rest of the stubs keep their type bytes.
  add_entries_parallel(env, &closure, &addr_only_set, &mut io);
  // Every ref of an ingressed BYTE-BEARING constant needs a ch-4
  // discriminator even when the target is not ingressed: the kernel
  // classifies refs from that channel and an address with no entry fails
  // the read outright. A constant outside the ingress set gets the
  // discriminator alone, so it resolves to poison. Refs of an
  // address-only entry are never classified — it is not converted; a
  // type-only stub IS, so its
  // type refs need their discriminators like anyone else's.
  let outside: FxHashSet<Address> = closure
    .iter()
    .filter(|a| !addr_only_set.contains(*a))
    .filter_map(|a| env.get_const(a))
    .flat_map(|c| c.refs.clone())
    .filter(|r| !closure.contains(r))
    .collect();
  for r in &outside {
    if env.get_const(r).is_some() {
      extend(&mut io, G::from_u8(4), addr_key(r), vec![G::ONE]);
    }
  }
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
  // ch 1: stub tree (if present)
  if let Some(st) = stub_tree {
    extend(&mut io, G::ONE, addr_key(&st.root()), bytes_to_g(&st.ser()));
  }

  Ok((claim, digest_key, io))
}
