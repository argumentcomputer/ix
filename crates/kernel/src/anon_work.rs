//! Anon-mode work enumeration over `IxonEnv::consts`.
//!
//! Identifies the set of kernel-checkable target addresses without
//! consulting any metadata sections (`named`/`names`/`comms`), so it
//! works against an env loaded via [`ixon::env::Env::get_anon`].
//!
//! The set produced here is the canonical work set for anon-mode
//! typechecking: it matches `rs_kernel_check_anon` in
//! `crates/ffi/src/kernel.rs` and is what an Aiur-style verifier
//! commits to. Callers iterate the returned `Vec<AnonWorkItem>` and
//! invoke `TypeChecker::check_const` on each item's `primary` address;
//! the kernel's internal block coordination handles checking every
//! member + ctor of `Block` items.
//!
//! ## Enumeration rules
//!
//! For each entry in `env.consts`:
//! - Projection variants (IPrj/CPrj/RPrj/DPrj) are skipped — they're
//!   covered by checking their parent Muts block.
//! - Standalone variants (Defn/Recr/Axio/Quot) emit one `Standalone`
//!   work item with the constant's own address.
//! - Muts blocks materialize to enumerate members, then emit one
//!   `Block` item whose `primary` is the first member's projection
//!   address (and `targets` includes that primary plus every other
//!   member's projection plus one CPrj per constructor of each
//!   inductive member). Checking the primary triggers the kernel's
//!   block-coordination logic which covers every target.
//!
//! Dispatch on the outer `Tag4` byte via
//! [`ixon::lazy::LazyConstant::peek_variant`] avoids body parse +
//! `Arc<Expr>` allocation for the ~95% of constants that are
//! standalones or projections.

use ix_common::address::Address;
use ixon::env::Env as IxonEnv;
use ixon::lazy::ConstVariantTag;

use crate::ingress::{
  anon_ctor_proj_addr, anon_defn_proj_addr, anon_indc_proj_addr,
  anon_recr_proj_addr,
};

/// A single anon-mode work item — one `tc.check_const(primary)` per
/// item suffices to typecheck every address in `targets`.
#[derive(Clone, Debug)]
pub enum AnonWorkItem {
  /// A standalone (Defn/Recr/Axio/Quot) constant. `addr` is both the
  /// kernel-checked target and the only address this item covers.
  Standalone { addr: Address },
  /// A Muts block. Checking `primary` (the first member's projection
  /// address) drives the kernel's block coordination, which in turn
  /// typechecks every entry in `targets`. `targets[0] == primary`.
  /// `block_addr` is the block's own `env.consts` key (the `Tag::Muts`
  /// entry) — distinct from the projection `targets`, and the address
  /// other constants' `refs` use to reference the block. Carried so the
  /// set of `consts` keys a checked item certifies ([`proven_targets`])
  /// is in the same address space as `Constant.refs`.
  ///
  /// [`proven_targets`]: AnonWorkItem::proven_targets
  Block { block_addr: Address, primary: Address, targets: Vec<Address> },
}

impl AnonWorkItem {
  /// The address to pass to `tc.check_const`.
  pub fn primary(&self) -> &Address {
    match self {
      AnonWorkItem::Standalone { addr } => addr,
      AnonWorkItem::Block { primary, .. } => primary,
    }
  }

  /// Every kernel-checked target this item covers (one for
  /// `Standalone`, `targets.len()` for `Block`).
  pub fn targets(&self) -> &[Address] {
    match self {
      AnonWorkItem::Standalone { addr } => core::slice::from_ref(addr),
      AnonWorkItem::Block { targets, .. } => targets,
    }
  }

  /// Every `env.consts` key this item certifies (proves) well-typed when
  /// its `primary` is checked — the *proven targets*, in the same address
  /// space as `Constant.refs`, so a dependency ref can be matched against
  /// the union of `proven_targets()` over all checked items: refs in that
  /// union are already certified, the rest are the claim's open assumptions
  /// (resolved later against other proofs). Unlike
  /// [`targets`](Self::targets) (the addresses the kernel actually walks),
  /// a `Block`'s proven set also includes the block's own `consts` key:
  /// for a `Standalone` it's just its address; for a `Block` it's
  /// `block_addr` plus every projection target (members + ctors). The
  /// union of `proven_targets()` over a full `build_anon_work` is exactly
  /// `env.consts.keys()`.
  pub fn proven_targets(&self) -> Vec<Address> {
    match self {
      AnonWorkItem::Standalone { addr } => vec![addr.clone()],
      AnonWorkItem::Block { block_addr, targets, .. } => {
        let mut v = Vec::with_capacity(1 + targets.len());
        v.push(block_addr.clone());
        v.extend(targets.iter().cloned());
        v
      },
    }
  }
}

/// Enumerate the anon-mode kernel work set from `env.consts`.
///
/// Returns one `AnonWorkItem` per kernel-checkable group of
/// constants. The total number of checked target addresses is
/// `work.iter().map(|w| w.targets().len()).sum()`.
///
/// Errors only on a corrupted env (missing const at an enumerated
/// address, or a Tag4 head byte that doesn't correspond to a known
/// `ConstantInfo` variant).
pub fn build_anon_work(env: &IxonEnv) -> Result<Vec<AnonWorkItem>, String> {
  use ConstVariantTag as Tag;
  use ixon::constant::ConstantInfo as CI;
  use ixon::constant::MutConst as MC;

  let mut work: Vec<AnonWorkItem> = Vec::new();

  // Sort keys for deterministic ordering across runs.
  let mut keys: Vec<Address> =
    env.consts.iter().map(|e| e.key().clone()).collect();
  keys.sort_unstable();

  for addr in keys {
    let lc = env.consts.get(&addr).ok_or_else(|| {
      format!("build_anon_work: missing const at {}", addr.hex())
    })?;
    let tag = lc.value().peek_variant().map_err(|e| {
      format!("build_anon_work: peek_variant {}: {e}", addr.hex())
    })?;
    match tag {
      Tag::IPrj | Tag::CPrj | Tag::RPrj | Tag::DPrj => {
        // Skip — covered by parent block.
      },
      Tag::Defn | Tag::Recr | Tag::Axio | Tag::Quot => {
        work.push(AnonWorkItem::Standalone { addr: addr.clone() });
      },
      Tag::Muts => {
        // Materialize once to enumerate members; the `Arc<Constant>`
        // drops at the end of this arm — no cache retention.
        let constant = lc.value().get().map_err(|e| {
          format!("build_anon_work: materialize Muts {}: {e}", addr.hex())
        })?;
        let CI::Muts(members) = &constant.info else {
          return Err(format!(
            "build_anon_work: Tag::Muts but ConstantInfo is {:?} at {}",
            constant.info.variant(),
            addr.hex()
          ));
        };
        let mut targets: Vec<Address> = Vec::new();
        for (i, member) in members.iter().enumerate() {
          let i = i as u64;
          let member_addr = match member {
            MC::Defn(_) => anon_defn_proj_addr(&addr, i),
            MC::Indc(_) => anon_indc_proj_addr(&addr, i),
            MC::Recr(_) => anon_recr_proj_addr(&addr, i),
          };
          targets.push(member_addr);
          if let MC::Indc(ind) = member {
            for cidx in 0..ind.ctors.len() as u64 {
              targets.push(anon_ctor_proj_addr(&addr, i, cidx));
            }
          }
        }
        if targets.is_empty() {
          continue;
        }
        let primary = targets[0].clone();
        work.push(AnonWorkItem::Block {
          block_addr: addr.clone(),
          primary,
          targets,
        });
      },
    }
  }

  Ok(work)
}

/// The full dependency-closure address set of `roots`: their transitive Expr
/// `refs` PLUS each projection's structural `block: Address`. A refs-only walk
/// misses the block — projections (IPrj/CPrj/RPrj/DPrj) point at their Muts
/// block via a struct field, not the Expr ref table — so the kernel couldn't
/// resolve the projection and would spuriously fail. The returned set includes
/// constant AND referenced-blob addresses (external refs absent from `source`
/// are included as addresses but have no bytes to copy).
pub fn closure_addrs(
  source: &IxonEnv,
  roots: &[Address],
) -> std::collections::HashSet<Address> {
  // The traversal lives in `ixon` (`Env::bfs_closure`) so bundle
  // pruning/validation and the shard sub-env share one edge
  // definition; this wrapper keeps the kernel-side std-HashSet
  // signature.
  source.bfs_closure(roots).into_iter().collect()
}

/// Build a closure sub-env: serialize only the BFS dependency closure of
/// `roots` (their transitive `Constant.refs` plus referenced literal blobs),
/// copying each constant's GENUINE bytes via `store_const_lazy` so the guest's
/// per-const integrity check (`hash(bytes) == addr`) and the env merkle root
/// still hold. The guest decodes this instead of the whole env, so it pays only
/// its closure's decode — essential for envs that don't fit the guest whole
/// (Init, 184 MB doesn't fit the 512 MB Zisk guest). Missing hints are
/// performance-only: ingress falls back to `Regular(0)`, so the typecheck
/// result — and thus the committed claim — is unchanged.
/// External refs (not in `source`) are omitted and remain open assumptions,
/// exactly as in whole-env.
///
/// Host-only: builds an `Env` via the `store_*` helpers, which are gated to
/// non-riscv64 (see `Env::store_blob`). The guest receives an already-built
/// sub-env from the host and only enumerates it via `build_anon_work`.
#[cfg(not(target_arch = "riscv64"))]
pub fn build_sub_env(
  source: &IxonEnv,
  roots: &[Address],
) -> Result<Vec<u8>, String> {
  let sub = sub_env_of(source, roots);
  let mut buf = Vec::new();
  sub.put(&mut buf).map_err(|e| format!("sub-env serialize: {e}"))?;
  Ok(buf)
}

/// The in-memory closure sub-env behind [`build_sub_env`]: copy the BFS
/// dependency closure of `roots` (genuine bytes + blobs + reducibility
/// hints), no Named section.
#[cfg(not(target_arch = "riscv64"))]
fn sub_env_of(source: &IxonEnv, roots: &[Address]) -> IxonEnv {
  let closure = closure_addrs(source, roots);
  let sub = IxonEnv::new();
  for addr in &closure {
    if let Some(bytes) = source.get_const_bytes(addr) {
      sub.store_const_lazy(addr.clone(), bytes);
    } else if let Some(blob) = source.get_blob(addr) {
      sub.store_blob(blob);
    }
    // else: external ref absent from `source` — omit; stays an open assumption.
    // Carry the constant's reducibility hint so the guest reproduces vanilla
    // kernel behavior; without hints the kernel forces `Regular(0)` and does
    // extra def-eq work (the ~30% check overhead).
    if let Some(h) = source.anon_hints.get(addr) {
      sub.anon_hints.insert(addr.clone(), *h);
    }
  }
  sub
}

/// [`build_sub_env`] plus a name→address entry for every closure constant
/// named in the FULL view of the same env — a standalone `.ixe` whose names
/// still resolve (for `--consts`-style tools), extracted without recompiling
/// from source.
///
/// METADATA IS DROPPED: each copied entry is `Named::with_addr` (empty
/// `ConstantMeta`), because real metadata references name addresses
/// throughout its tree and carrying it would require the full env's
/// hash-consed name index. The extract serves the ANON pipeline
/// (`check-rs --anon`, the zkVM hosts, `ix profile`/`ix shard`,
/// `bench-typecheck`), where metadata is never read and reducibility hints
/// travel in the `anon_hints` section instead. Meta-mode tools need the
/// source env.
#[cfg(not(target_arch = "riscv64"))]
pub fn build_sub_env_named(
  source: &IxonEnv,
  full: &IxonEnv,
  roots: &[Address],
) -> Result<Vec<u8>, String> {
  use ix_common::env::NameData;

  let sub = sub_env_of(source, roots);
  // The Named section serializes keys as name HASHES resolved through the
  // names section, so each key's component chain must be interned too.
  fn intern_chain(sub: &IxonEnv, name: &ix_common::env::Name) {
    let addr = Address::from_blake3_hash(*name.get_hash());
    if sub.get_name(&addr).is_some() {
      return;
    }
    match name.as_data() {
      NameData::Anonymous(_) => {},
      NameData::Str(parent, _, _) | NameData::Num(parent, _, _) => {
        intern_chain(sub, parent);
      },
    }
    sub.store_name(addr, name.clone());
  }
  for e in full.named.iter() {
    if sub.get_const(&e.value().addr).is_some() {
      intern_chain(&sub, e.key());
      sub.register_name(
        e.key().clone(),
        ixon::env::Named::with_addr(e.value().addr.clone()),
      );
    }
  }
  let mut buf = Vec::new();
  sub.put(&mut buf).map_err(|e| format!("sub-env serialize: {e}"))?;
  Ok(buf)
}

/// The ingress-block address that owns `addr`: a projection (IPrj/CPrj/RPrj/
/// DPrj) maps to its Muts `block`; anything else is its own block. Used to map
/// a resolved constant address to the `build_anon_work` item that covers it
/// (standalone → itself; a mutual-block member → the whole block).
pub fn block_of_addr(env: &IxonEnv, addr: &Address) -> Address {
  use ixon::constant::ConstantInfo as CI;
  match env.get_const(addr) {
    Some(c) => match &c.info {
      CI::IPrj(p) => p.block.clone(),
      CI::CPrj(p) => p.block.clone(),
      CI::RPrj(p) => p.block.clone(),
      CI::DPrj(p) => p.block.clone(),
      _ => addr.clone(),
    },
    None => addr.clone(),
  }
}

/// The ingress-block address of a work item's `primary` — the key for matching
/// a resolved target constant to the work item that covers it.
pub fn work_block_addr(env: &IxonEnv, item: &AnonWorkItem) -> Address {
  block_of_addr(env, item.primary())
}
