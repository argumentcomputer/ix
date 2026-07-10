//! Environment for storing Ixon data.

use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::VecDeque;
use std::sync::Arc;

use ix_common::address::Address;
use ix_common::env::{Name, ReducibilityHints};

use super::comm::Comm;
use super::constant::Constant;
use super::lazy::LazyConstant;
use super::map::IxonMap;
use super::metadata::{ConstantMeta, ConstantMetaInfo};

/// Metadata representation inside [`Named`]: structured (default) or
/// demoted to its self-contained serialized form
/// ([`ConstantMeta::put_raw`]), which costs a fraction of the
/// pointer-rich structured DAG and is decoded on demand. The demoted
/// form is chosen at registration under `IX_COMPILE_META=demote`.
#[derive(Clone, Debug)]
enum MetaRepr {
  Structured(Arc<ConstantMeta>),
  Bytes(Arc<[u8]>),
}

impl MetaRepr {
  fn structured(meta: ConstantMeta) -> Self {
    MetaRepr::Structured(Arc::new(meta))
  }

  fn demoted(meta: &ConstantMeta) -> Self {
    let mut buf = Vec::new();
    meta
      .put_raw(&mut buf)
      .expect("ConstantMeta::put_raw cannot fail on in-memory metadata");
    MetaRepr::Bytes(buf.into())
  }

  /// Materialize. Cheap `Arc` clone for `Structured`; a fresh decode per
  /// call for `Bytes` (nothing is cached — mirroring `LazyConstant`).
  fn decode(&self) -> Arc<ConstantMeta> {
    match self {
      MetaRepr::Structured(m) => m.clone(),
      MetaRepr::Bytes(b) => {
        let mut slice: &[u8] = b;
        Arc::new(
          ConstantMeta::get_raw(&mut slice)
            .expect("Named meta bytes produced by put_raw failed to decode"),
        )
      },
    }
  }
}

/// A named constant with metadata.
#[derive(Clone, Debug)]
pub struct Named {
  /// Address of the constant (in consts map)
  pub addr: Address,
  /// Typed metadata for this constant (includes mutual context in `all`
  /// field). Private repr: structured, or demoted to serialized bytes —
  /// read through [`Self::meta`].
  meta: MetaRepr,
  /// For aux_gen-rewritten constants: the original Lean constant's compiled
  /// form (address + metadata). Ingress uses `addr`/`meta` (the canonical
  /// aux_gen form). Decompile uses `original` for faithful roundtrip of
  /// binder names and other cosmetic metadata.
  original: Option<(Address, MetaRepr)>,
}

impl Named {
  pub fn new(addr: Address, meta: ConstantMeta) -> Self {
    Named { addr, meta: MetaRepr::structured(meta), original: None }
  }

  pub fn with_addr(addr: Address) -> Self {
    Named {
      addr,
      meta: MetaRepr::structured(ConstantMeta::default()),
      original: None,
    }
  }

  /// The constant's metadata. Cheap (`Arc` clone) for structured
  /// entries; a fresh decode per call for demoted ones.
  pub fn meta(&self) -> Arc<ConstantMeta> {
    self.meta.decode()
  }

  /// The aux_gen original form, if recorded (see field docs).
  pub fn original(&self) -> Option<(Address, Arc<ConstantMeta>)> {
    self.original.as_ref().map(|(a, m)| (a.clone(), m.decode()))
  }

  pub fn has_original(&self) -> bool {
    self.original.is_some()
  }

  /// Record the aux_gen original form. Stored in the same repr as
  /// `self.meta`, so demoted entries stay fully demoted.
  pub fn set_original(&mut self, addr: Address, meta: ConstantMeta) {
    let repr = match &self.meta {
      MetaRepr::Structured(_) => MetaRepr::structured(meta),
      MetaRepr::Bytes(_) => MetaRepr::demoted(&meta),
    };
    self.original = Some((addr, repr));
  }

  pub fn clear_original(&mut self) {
    self.original = None;
  }

  /// Convert both metadata slots to the serialized-bytes repr.
  pub fn demote(&mut self) {
    if let MetaRepr::Structured(m) = &self.meta {
      self.meta = MetaRepr::demoted(m);
    }
    if let Some((a, MetaRepr::Structured(m))) = &self.original {
      self.original = Some((a.clone(), MetaRepr::demoted(m)));
    }
  }

  /// Whether the primary metadata slot holds structured metadata.
  pub fn is_meta_structured(&self) -> bool {
    matches!(self.meta, MetaRepr::Structured(_))
  }
}

/// Nested-auxiliary layout info for a mutual inductive block.
///
/// Paired perm + source_ctor_counts so consumers have everything needed to
/// correctly permute source-order aux motives/minors into canonical
/// positions. Both arrays have one entry per source-walk-discovered aux.
///
/// This lives in `ixon::env` (not `ix_compile::surgery`, where it originated)
/// so it can be persisted into the serialized Ixon environment as a
/// side-table on [`Env::aux_layouts`]. The surgery layer re-exports it.
///
/// Keyed by `<source_all[0]>` — the first inductive in the Lean source's
/// mutual block, which is what Lean hangs `.rec_N` / `.below_N` /
/// `.brecOn_N` names off.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuxLayout {
  /// `perm[source_j] = canonical_i`: Lean's source-walk position to
  /// our canonical hash-sorted position.
  pub perm: Vec<usize>,
  /// Number of constructors for the aux inductive at source position j.
  /// Same count regardless of which position the aux ends up at
  /// canonically (it's a property of the external nested inductive).
  pub source_ctor_counts: Vec<usize>,
}

/// One constant in a [`LazyIndex`]: its content address plus the byte window
/// `[offset, offset+len)` of its serialized Tag4 body within the source buffer.
/// No bytes are copied — the consumer (the Lean lazy loader) slices its own
/// copy of the buffer at these offsets.
#[derive(Debug, Clone)]
pub struct LazyConstSlice {
  pub addr: Address,
  pub offset: usize,
  pub len: usize,
}

/// One named entry in a [`LazyIndex`]: just the `name → addr` mapping plus the
/// per-`Defn` reducibility hint (the only metadata the typecheck circuit
/// consumes). The heavy `ExprMetaArena` is parsed (to advance the cursor and
/// handle every metadata variant, e.g. `CallSite`) but discarded.
#[derive(Debug, Clone)]
pub struct LazyNamed {
  pub name: Name,
  pub addr: Address,
  pub hint: Option<ReducibilityHints>,
}

/// Compile-accumulator spill mode, parsed once from `IX_COMPILE_SPILL`.
///
/// - `Off` (default): `store_const` keeps a materialized `Arc<Constant>`
///   cache next to the serialized bytes.
/// - `Demote`: `store_const` stores bytes only; `get_const` re-parses per
///   access (the lazy-load policy — see `LazyConstant` docs).
/// - `Mmap`: demote plus spilling the bytes to a file-backed mapping
///   (see the `spill` module docs).
///
/// Host-only: the guest builds `Env` via deserialization and never calls
/// `store_const`.
#[cfg(not(target_arch = "riscv64"))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpillMode {
  Off,
  Demote,
  Mmap,
}

/// `IX_COMPILE_META=demote` stores registered names' metadata as
/// serialized bytes instead of structured `ConstantMeta` (see
/// [`Named::demote`]). Default: structured — today's behavior.
#[cfg(not(target_arch = "riscv64"))]
pub static META_DEMOTE: std::sync::LazyLock<bool> =
  std::sync::LazyLock::new(|| {
    match std::env::var("IX_COMPILE_META").as_deref() {
      Ok("demote") => true,
      Ok("structured") | Err(_) => false,
      Ok(other) => {
        eprintln!(
          "[ixon] IX_COMPILE_META={other:?} not recognized \
           (expected structured|demote); using structured"
        );
        false
      },
    }
  });

#[cfg(not(target_arch = "riscv64"))]
pub static SPILL_MODE: std::sync::LazyLock<SpillMode> =
  std::sync::LazyLock::new(|| {
    match std::env::var("IX_COMPILE_SPILL").as_deref() {
      Ok("demote") => SpillMode::Demote,
      Ok("mmap") => SpillMode::Mmap,
      Ok("off") | Err(_) => SpillMode::Off,
      Ok(other) => {
        eprintln!(
          "[ixon] IX_COMPILE_SPILL={other:?} not recognized \
           (expected off|demote|mmap); using off"
        );
        SpillMode::Off
      },
    }
  });

/// Composition of [`Env::consts`], from [`Env::const_cache_stats`].
#[derive(Clone, Copy, Debug, Default)]
pub struct ConstCacheStats {
  /// Total entries in the consts map.
  pub entries: usize,
  /// Summed `raw_bytes()` length across all entries.
  pub bytes: usize,
  /// Entries holding a materialized `Arc<Constant>` cache.
  pub materialized: usize,
}

/// Result of [`Env::parse_lazy_index`]: a metadata-light, zero-copy view of an
/// `.ixe` buffer suitable for the anon/lazy check path. Constants are byte
/// windows (offsets), `named` is `name → addr` + hint, and `blobs` are copied
/// (they are small and the kernel ingests their bytes directly).
#[derive(Debug, Clone, Default)]
pub struct LazyIndex {
  pub consts: Vec<LazyConstSlice>,
  pub named: Vec<LazyNamed>,
  pub blobs: Vec<(Address, Vec<u8>)>,
}

/// The Ixon environment.
///
/// Contains five maps:
/// - `consts`: Alpha-invariant constants indexed by content hash,
///   stored lazily as serialized bytes ([`LazyConstant`]) and
///   materialized on demand.
/// - `named`: Named references with metadata and mutual context
/// - `blobs`: Raw data (strings, nats, files)
/// - `names`: Hash-consed Lean.Name components (Address -> Name)
/// - `comms`: Cryptographic commitments (secrets)
#[derive(Debug, Default)]
pub struct Env {
  /// Alpha-invariant constants: Address -> LazyConstant (raw bytes +
  /// optional materialized cache; see [`LazyConstant`]).
  pub consts: IxonMap<Address, LazyConstant>,
  /// Named references: Name -> (constant address, metadata, ctx)
  pub named: IxonMap<Name, Named>,
  /// Raw data blobs: Address -> bytes
  pub blobs: IxonMap<Address, Vec<u8>>,
  /// Hash-consed Lean.Name components: Address -> Name
  pub names: IxonMap<Address, Name>,
  /// Cryptographic commitments: commitment Address -> Comm
  pub comms: IxonMap<Address, Comm>,
  /// Reducibility hints sidecar harvested by [`Env::get_anon`] from the
  /// otherwise-discarded Named section. Keyed by the constant's
  /// projection/standalone address (i.e. `Named.addr` — the address the
  /// kernel sees, **not** the name-hash address). Empty for envs loaded
  /// via [`Env::get`] / [`Env::new`] / `store_*`; meta-mode ingress
  /// pulls hints directly from `Named.meta` and ignores this field.
  ///
  /// Anon-mode ingress passes these hints through to
  /// `ingress_defn` so the kernel's lazy-delta tiebreak
  /// (`def_eq::def_rank_id`) sees realistic heights instead of the
  /// constant `Regular(0)` fallback. Hints are performance advice —
  /// supplying them in anon mode does not relax the kernel's
  /// metadata-free correctness model.
  pub anon_hints: FxHashMap<Address, ReducibilityHints>,
  /// Spill file state for `IX_COMPILE_SPILL=mmap` (see the `spill`
  /// module docs). `Unopened` until the first spill-mode `store_const`.
  /// Not carried by `Clone` — a cloned env starts a fresh spill file;
  /// its mmap-backed entries keep their `Arc<Mmap>` windows regardless.
  #[cfg(not(target_arch = "riscv64"))]
  pub(crate) spill: std::sync::Mutex<crate::spill::SpillSlot>,
}

impl Env {
  pub fn new() -> Self {
    Env {
      consts: IxonMap::new(),
      named: IxonMap::new(),
      blobs: IxonMap::new(),
      names: IxonMap::new(),
      comms: IxonMap::new(),
      anon_hints: FxHashMap::default(),
      #[cfg(not(target_arch = "riscv64"))]
      spill: Default::default(),
    }
  }

  /// Store a blob and return its content address.
  ///
  /// Host-only because `IxonMap` is `DashMap` here (interior-mutable `&self`
  /// inserts). On `riscv64` `IxonMap` is `FxHashMap`, which requires `&mut`;
  /// the guest builds `Env` via `Env::get` deserialization and doesn't need
  /// the store helpers.
  #[cfg(not(target_arch = "riscv64"))]
  pub fn store_blob(&self, bytes: Vec<u8>) -> Address {
    let addr = Address::hash(&bytes);
    self.blobs.insert(addr.clone(), bytes);
    addr
  }

  /// Get a blob by address.
  pub fn get_blob(&self, addr: &Address) -> Option<Vec<u8>> {
    self.blobs.get(addr).map(|r| r.clone())
  }

  /// Store a structured constant under `addr`.
  ///
  /// Serializes the constant once. In the default [`SpillMode::Off`],
  /// the [`LazyConstant`] cache is pre-populated so `get_const` is
  /// free; under `IX_COMPILE_SPILL=demote|mmap` the structured value is
  /// dropped and the entry costs only its bytes (`get_const` re-parses
  /// per access). Compilation never reads stored constants back, so the
  /// modes differ only in memory footprint and later readers' CPU cost.
  ///
  /// Host-only — see `store_blob`.
  #[cfg(not(target_arch = "riscv64"))]
  pub fn store_const(&self, addr: Address, constant: Constant) {
    self.store_const_with_mode(addr, constant, *SPILL_MODE);
  }

  /// `store_const` with an explicit mode, bypassing `IX_COMPILE_SPILL`.
  /// Exists so tests can drive `Demote`/`Mmap` without process-global
  /// env-var races.
  #[cfg(not(target_arch = "riscv64"))]
  pub fn store_const_with_mode(
    &self,
    addr: Address,
    constant: Constant,
    mode: SpillMode,
  ) {
    match mode {
      SpillMode::Off => {
        self.consts.insert(addr, LazyConstant::from_constant(constant));
      },
      // In the spill modes a re-store of an existing address is a no-op:
      // content-addressing guarantees identical bytes, re-inserting
      // would downgrade an already-sealed mmap window back to heap, and
      // re-appending would duplicate the bytes in the spill file.
      // (Alpha-collapsed blocks re-store the shared address once per
      // member.) `Off` keeps insert-overwrite: there a re-store can
      // upgrade a cache-less lazy-loaded entry to a cached one.
      SpillMode::Demote => {
        if self.consts.contains_key(&addr) {
          return;
        }
        self
          .consts
          .insert(addr, LazyConstant::from_constant_uncached(constant));
      },
      SpillMode::Mmap => {
        if self.consts.contains_key(&addr) {
          return;
        }
        let mut buf = Vec::new();
        constant.put(&mut buf);
        let bytes: Arc<[u8]> = buf.into();
        // Heap entry first so the address is immediately readable; the
        // spill seal swaps it to an mmap window later.
        self
          .consts
          .insert(addr.clone(), LazyConstant::from_bytes(bytes.clone()));
        self.spill_append(addr, &bytes);
      },
    }
  }

  /// Append one entry to the spill file, sealing (and swapping the
  /// sealed entries to mmap windows) when a segment fills. Any I/O
  /// error disables spilling for this env: heap-backed entries remain
  /// valid, sealed windows keep their mappings.
  #[cfg(not(target_arch = "riscv64"))]
  fn spill_append(&self, addr: Address, bytes: &[u8]) {
    use crate::spill::{SpillSlot, SpillState};
    let mut slot = self.spill.lock().unwrap();
    if matches!(*slot, SpillSlot::Unopened) {
      match SpillState::create() {
        Ok(st) => *slot = SpillSlot::Active(st),
        Err(e) => {
          eprintln!(
            "[ixon] spill file creation failed ({e}); \
             falling back to heap-backed entries"
          );
          *slot = SpillSlot::Disabled;
        },
      }
    }
    let SpillSlot::Active(st) = &mut *slot else { return };
    match st.append(addr, bytes) {
      Ok(None) => {},
      Ok(Some((mmap, entries))) => {
        if std::env::var("IX_QUIET").is_err() {
          eprintln!(
            "[ixon] spill segment {} sealed: {} entries, file {:.1} MiB",
            st.segments_sealed,
            entries.len(),
            st.file_len() as f64 / (1024.0 * 1024.0),
          );
        }
        for (a, off, len) in entries {
          self
            .consts
            .insert(a, LazyConstant::from_mmap_slice(mmap.clone(), off, len));
        }
      },
      Err(e) => {
        eprintln!(
          "[ixon] spill write failed ({e}); \
           falling back to heap-backed entries"
        );
        *slot = SpillSlot::Disabled;
      },
    }
  }

  /// Spill file observability: `(file_bytes, segments_sealed,
  /// unsealed_entry_count)`, or `None` if spilling never activated.
  #[cfg(not(target_arch = "riscv64"))]
  pub fn spill_stats(&self) -> Option<(u64, usize, usize)> {
    match &*self.spill.lock().unwrap() {
      crate::spill::SpillSlot::Active(st) => {
        Some((st.file_len(), st.segments_sealed, st.pending_count()))
      },
      _ => None,
    }
  }

  /// Store an already-serialized constant under `addr` (lazy load path).
  /// `bytes` must be exactly what `Constant::put` produced for `addr`.
  /// Host-only — see `store_blob`.
  #[cfg(not(target_arch = "riscv64"))]
  pub fn store_const_lazy(&self, addr: Address, bytes: Arc<[u8]>) {
    self.consts.insert(addr, LazyConstant::from_bytes(bytes));
  }

  /// Store a constant as a window into a memory-mapped `.ixe` file.
  /// `(mmap, offset, len)` must reference exactly what `Constant::put`
  /// produced for `addr`. Used by [`Env::get_anon_mmap`] to avoid
  /// heap-copying on-disk bytes — the OS page cache backs the slice.
  /// Host-only — see `store_blob`.
  #[cfg(not(target_arch = "riscv64"))]
  pub fn store_const_lazy_mmap(
    &self,
    addr: Address,
    mmap: Arc<memmap2::Mmap>,
    offset: usize,
    len: usize,
  ) {
    self.consts.insert(addr, LazyConstant::from_mmap_slice(mmap, offset, len));
  }

  /// Get a constant by address, materializing on demand.
  ///
  /// Returns `None` if the address is not present or materialization
  /// fails (e.g., corrupt bytes). Use [`Self::try_get_const`] to
  /// inspect materialization errors.
  pub fn get_const(&self, addr: &Address) -> Option<Arc<Constant>> {
    self.consts.get(addr).and_then(|r| r.value().get().ok())
  }

  /// Get a constant by address, returning materialization errors.
  pub fn try_get_const(
    &self,
    addr: &Address,
  ) -> Option<Result<Arc<Constant>, String>> {
    self.consts.get(addr).map(|r| r.value().get())
  }

  /// Get the raw serialized bytes of a constant without materializing it.
  pub fn get_const_bytes(&self, addr: &Address) -> Option<Arc<[u8]>> {
    self.consts.get(addr).map(|r| Arc::from(r.value().raw_bytes()))
  }

  /// Register a named constant. Under `IX_COMPILE_META=demote` the
  /// entry's metadata is stored in its serialized-bytes form (see
  /// [`Named::demote`]) — the structured DAG costs a large multiple of
  /// its encoding and compilation never reads it back.
  /// Host-only — see `store_blob`.
  #[cfg(not(target_arch = "riscv64"))]
  pub fn register_name(&self, name: Name, mut named: Named) {
    if *META_DEMOTE {
      named.demote();
    }
    self.named.insert(name, named);
  }

  /// Look up a name.
  pub fn lookup_name(&self, name: &Name) -> Option<Named> {
    self.named.get(name).map(|r| r.clone())
  }

  /// Store a hash-consed name component. Host-only — see `store_blob`.
  #[cfg(not(target_arch = "riscv64"))]
  pub fn store_name(&self, addr: Address, name: Name) {
    self.names.insert(addr, name);
  }

  /// Get a name by address.
  pub fn get_name(&self, addr: &Address) -> Option<Name> {
    self.names.get(addr).map(|r| r.clone())
  }

  /// Store a commitment. Host-only — see `store_blob`.
  #[cfg(not(target_arch = "riscv64"))]
  pub fn store_comm(&self, addr: Address, comm: Comm) {
    self.comms.insert(addr, comm);
  }

  /// Get a commitment by address.
  pub fn get_comm(&self, addr: &Address) -> Option<Comm> {
    self.comms.get(addr).map(|r| r.clone())
  }

  /// Number of constants.
  pub fn const_count(&self) -> usize {
    self.consts.len()
  }

  /// Composition of the consts map: entry count, summed serialized byte
  /// length, and how many entries hold a materialized `Arc<Constant>`
  /// cache (see [`LazyConstant::is_materialized`]). O(n) scan over the
  /// map; used to split the accumulator's footprint into structured-cache
  /// vs raw-bytes shares.
  pub fn const_cache_stats(&self) -> ConstCacheStats {
    let mut stats = ConstCacheStats::default();
    for entry in self.consts.iter() {
      stats.entries += 1;
      stats.bytes += entry.value().raw_bytes().len();
      stats.materialized += usize::from(entry.value().is_materialized());
    }
    stats
  }

  /// Number of named entries.
  pub fn named_count(&self) -> usize {
    self.named.len()
  }

  /// Addresses of the named constants the kernel typechecker would
  /// iterate via `check_const` — every entry in `env.named` minus the
  /// `Muts` mutual-block pointers (which aren't standalone checkables).
  /// Matches `crates/ffi/src/kernel.rs::all_checkable_ixon_names` but
  /// returns addresses rather than names and skips the sort.
  pub fn checkable_addrs(&self) -> Vec<Address> {
    self
      .named
      .iter()
      .filter(|e| {
        !matches!(e.value().meta().info, ConstantMetaInfo::Muts { .. })
      })
      .map(|e| e.value().addr.clone())
      .collect()
  }

  /// Number of hash-consed name components.
  pub fn name_count(&self) -> usize {
    self.names.len()
  }

  /// Number of blobs.
  pub fn blob_count(&self) -> usize {
    self.blobs.len()
  }

  /// Number of commitments.
  pub fn comm_count(&self) -> usize {
    self.comms.len()
  }

  /// BFS-collect all addresses transitively reachable from `root` via
  /// the `Constant.refs` field. The returned set includes `root` itself.
  ///
  /// Addresses that are referenced but not present in `self.consts` are
  /// still added to the set (so verifiers see external assumptions)
  /// but we cannot recurse into them.
  ///
  /// Visited constants are materialized via [`LazyConstant::get`];
  /// subsequent BFS passes over the same closure are free.
  pub fn bfs_refs(&self, root: &Address) -> FxHashSet<Address> {
    let mut visited: FxHashSet<Address> = FxHashSet::default();
    let mut queue: VecDeque<Address> = VecDeque::new();
    visited.insert(root.clone());
    queue.push_back(root.clone());
    while let Some(addr) = queue.pop_front() {
      // Materialize the constant just long enough to read its refs.
      // Drop the DashMap guard before recursing so concurrent BFS
      // calls don't deadlock on the same shard.
      let refs: Option<Vec<Address>> = self
        .consts
        .get(&addr)
        .and_then(|r| r.value().get().ok())
        .map(|c| c.refs.clone());
      if let Some(rs) = refs {
        for r in rs {
          if visited.insert(r.clone()) {
            queue.push_back(r);
          }
        }
      }
    }
    visited
  }

  /// Transitive dep addresses of `root`, excluding `root` itself. Sorted
  /// lex-ascending for canonical use (e.g., feeding `merkle_root_canonical`).
  pub fn transitive_deps_excl(&self, root: &Address) -> Vec<Address> {
    let mut set = self.bfs_refs(root);
    set.remove(root);
    let mut v: Vec<Address> = set.into_iter().collect();
    v.sort_unstable();
    v
  }
}

impl Clone for Env {
  // `mut` is only needed on `riscv64` where `IxonMap` wraps `FxHashMap` and
  // `insert` takes `&mut self`; on host `DashMap::insert` takes `&self`.
  #[cfg_attr(not(target_arch = "riscv64"), allow(unused_mut))]
  fn clone(&self) -> Self {
    let mut consts = IxonMap::new();
    for entry in self.consts.iter() {
      consts.insert(entry.key().clone(), entry.value().clone());
    }

    let mut named = IxonMap::new();
    for entry in self.named.iter() {
      named.insert(entry.key().clone(), entry.value().clone());
    }

    let mut blobs = IxonMap::new();
    for entry in self.blobs.iter() {
      blobs.insert(entry.key().clone(), entry.value().clone());
    }

    let mut names = IxonMap::new();
    for entry in self.names.iter() {
      names.insert(entry.key().clone(), entry.value().clone());
    }

    let mut comms = IxonMap::new();
    for entry in self.comms.iter() {
      comms.insert(entry.key().clone(), entry.value().clone());
    }

    Env {
      consts,
      named,
      blobs,
      names,
      comms,
      anon_hints: self.anon_hints.clone(),
      // A cloned env starts a fresh spill file; already-sealed mmap
      // windows travel inside the cloned LazyConstants.
      #[cfg(not(target_arch = "riscv64"))]
      spill: Default::default(),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::constant::{Axiom, Constant, ConstantInfo};
  use crate::expr::Expr;
  use ix_common::env::Name;
  use std::sync::Arc;

  fn n(s: &str) -> Name {
    Name::str(Name::anon(), s.to_string())
  }

  fn dummy_constant() -> Constant {
    Constant::new(ConstantInfo::Axio(Axiom {
      is_unsafe: false,
      lvls: 0,
      typ: Arc::new(Expr::Sort(0)),
    }))
  }

  #[test]
  fn store_and_get_blob() {
    let env = Env::new();
    let data = vec![1, 2, 3, 4, 5];
    let addr = env.store_blob(data.clone());
    assert_eq!(env.get_blob(&addr), Some(data));
    // Same content produces same address
    let addr2 = env.store_blob(vec![1, 2, 3, 4, 5]);
    assert_eq!(addr, addr2);
  }

  #[test]
  fn store_and_get_const() {
    let env = Env::new();
    let constant = dummy_constant();
    let addr = Address::hash(b"test-constant");
    env.store_const(addr.clone(), constant.clone());
    let got = env.get_const(&addr).unwrap();
    assert_eq!(*got, constant);
  }

  /// Distinct axiom per `lvls` so each store gets its own address.
  fn axiom_with_lvls(lvls: u64) -> Constant {
    Constant::new(ConstantInfo::Axio(Axiom {
      is_unsafe: false,
      lvls,
      typ: Arc::new(Expr::Sort(0)),
    }))
  }

  /// Preset an Active spill state with a tiny segment so a handful of
  /// stores force seals (bypasses the env-var-driven `SpillState::create`).
  fn preset_tiny_spill(env: &Env, segment_bytes: usize) {
    let dir = std::env::temp_dir();
    *env.spill.lock().unwrap() = crate::spill::SpillSlot::Active(
      crate::spill::SpillState::create_in(dir.to_str().unwrap(), segment_bytes)
        .unwrap(),
    );
  }

  #[test]
  fn store_const_mmap_seals_segments_and_roundtrips() {
    let env = Env::new();
    preset_tiny_spill(&env, 256);
    let mut stored = Vec::new();
    for i in 0..64 {
      let c = axiom_with_lvls(i);
      let (addr, _) = c.commit();
      env.store_const_with_mode(addr.clone(), c.clone(), SpillMode::Mmap);
      stored.push((addr, c));
    }
    let (file_bytes, segments, unsealed) = env.spill_stats().unwrap();
    assert!(segments >= 1, "no segment sealed (file {file_bytes}B)");
    assert!(unsealed < 64, "nothing was sealed");
    // Every entry — mmap-backed or still-heap — verifies and roundtrips.
    for (addr, c) in &stored {
      let entry = env.consts.get(addr).unwrap();
      assert!(entry.value().verify_address(addr));
      assert!(!entry.value().is_materialized());
      drop(entry);
      assert_eq!(*env.get_const(addr).unwrap(), *c);
    }
  }

  #[test]
  fn demoted_named_roundtrips_and_serializes_identically() {
    let addr = Address::hash(b"demoted-named-target");
    // Empty metadata: no name references, so `Env::put` needs no name
    // index entries. Name-ref-rich raw/indexed equivalence is covered
    // by `metadata::tests::test_constant_meta_indexed_roundtrip`.
    let meta = ConstantMeta::default();
    let mut structured = Named::new(addr.clone(), meta.clone());
    structured.set_original(addr.clone(), meta.clone());
    let mut demoted = structured.clone();
    demoted.demote();

    assert!(structured.is_meta_structured());
    assert!(!demoted.is_meta_structured());
    // Accessors agree between reprs.
    assert_eq!(*structured.meta(), *demoted.meta());
    assert!(demoted.has_original());
    let (sa, sm) = structured.original().unwrap();
    let (da, dm) = demoted.original().unwrap();
    assert_eq!(sa, da);
    assert_eq!(*sm, *dm);

    // Envs whose named entries differ only in repr serialize identically.
    let mk_env = |named: &Named| {
      let env = Env::new();
      env.register_name(n("target"), named.clone());
      let mut buf = Vec::new();
      env.put(&mut buf).unwrap();
      buf
    };
    assert_eq!(mk_env(&structured), mk_env(&demoted));
  }

  #[test]
  fn env_put_identical_across_spill_modes() {
    let build = |mode: SpillMode, tiny_spill: bool| {
      let env = Env::new();
      if tiny_spill {
        preset_tiny_spill(&env, 128);
      }
      for i in 0..32 {
        let c = axiom_with_lvls(i);
        let (addr, _) = c.commit();
        env.store_const_with_mode(addr, c, mode);
      }
      let mut buf = Vec::new();
      env.put(&mut buf).unwrap();
      buf
    };
    let off = build(SpillMode::Off, false);
    let demote = build(SpillMode::Demote, false);
    let mmap = build(SpillMode::Mmap, true);
    assert_eq!(off, demote);
    assert_eq!(off, mmap);
  }

  #[test]
  fn register_and_lookup_name() {
    let env = Env::new();
    let name = n("MyConst");
    let addr = Address::hash(b"my-const-addr");
    let named = Named::with_addr(addr.clone());
    env.register_name(name.clone(), named.clone());
    let got = env.lookup_name(&name).unwrap();
    assert_eq!(got.addr, addr);
  }

  #[test]
  fn store_and_get_name_component() {
    let env = Env::new();
    let name = n("Component");
    let addr = Address::hash(b"name-component");
    env.store_name(addr.clone(), name.clone());
    assert_eq!(env.get_name(&addr), Some(name));
  }

  #[test]
  fn store_and_get_comm() {
    let env = Env::new();
    let secret = Address::hash(b"secret");
    let payload = Address::hash(b"payload");
    let comm = Comm::new(secret.clone(), payload.clone());
    let comm_addr = Address::hash(b"comm-addr");
    env.store_comm(comm_addr.clone(), comm.clone());
    let got = env.get_comm(&comm_addr).unwrap();
    assert_eq!(got, comm);
  }

  #[test]
  fn counts() {
    let env = Env::new();
    assert_eq!(env.const_count(), 0);
    assert_eq!(env.named_count(), 0);
    assert_eq!(env.blob_count(), 0);
    assert_eq!(env.name_count(), 0);
    assert_eq!(env.comm_count(), 0);

    env.store_blob(vec![1]);
    assert_eq!(env.blob_count(), 1);

    env.store_const(Address::hash(b"c1"), dummy_constant());
    assert_eq!(env.const_count(), 1);

    env.register_name(n("x"), Named::with_addr(Address::hash(b"x")));
    assert_eq!(env.named_count(), 1);

    env.store_name(Address::hash(b"n1"), n("n"));
    assert_eq!(env.name_count(), 1);

    env.store_comm(
      Address::hash(b"cm"),
      Comm::new(Address::hash(b"s"), Address::hash(b"p")),
    );
    assert_eq!(env.comm_count(), 1);
  }

  #[test]
  fn missing_keys_return_none() {
    let env = Env::new();
    let missing = Address::hash(b"nonexistent");
    assert!(env.get_blob(&missing).is_none());
    assert!(env.get_const(&missing).is_none());
    assert!(env.lookup_name(&n("missing")).is_none());
    // addr_to_name reverse index was removed (unsound for alpha-equivalent constants)
    assert!(env.get_name(&missing).is_none());
    assert!(env.get_comm(&missing).is_none());
  }

  #[test]
  fn blob_content_addressing() {
    let env = Env::new();
    let addr1 = env.store_blob(vec![1, 2, 3]);
    let addr2 = env.store_blob(vec![4, 5, 6]);
    // Different content produces different addresses
    assert_ne!(addr1, addr2);
    // Same content produces same address
    let addr3 = env.store_blob(vec![1, 2, 3]);
    assert_eq!(addr1, addr3);
  }

  /// Build a constant with the given refs (for BFS tests). `discriminator`
  /// is folded into `lvls` so callers can produce content-distinct
  /// constants when the same ref-set would otherwise collide (e.g.
  /// two independent leaf nodes both with empty refs).
  fn const_with_refs(refs: Vec<Address>) -> Constant {
    const_with_refs_discriminator(refs, 0)
  }

  fn const_with_refs_discriminator(
    refs: Vec<Address>,
    discriminator: u64,
  ) -> Constant {
    Constant::with_tables(
      ConstantInfo::Axio(Axiom {
        is_unsafe: false,
        lvls: discriminator,
        typ: Arc::new(Expr::Sort(0)),
      }),
      Vec::new(),
      refs,
      Vec::new(),
    )
  }

  /// Store a constant at its true content address and return that
  /// address. Use this instead of `store_const(Address::hash(b"a"),
  /// ...)` for tests that round-trip through `Env::put`/`Env::get`;
  /// the load path verifies `Address::hash(bytes) == addr` per
  /// entry, so fake keys are rejected.
  fn store_canonical(env: &Env, c: Constant) -> Address {
    let (addr, _) = c.commit();
    env.store_const(addr.clone(), c);
    addr
  }

  #[test]
  fn bfs_refs_singleton_no_deps() {
    let env = Env::new();
    let a = Address::hash(b"a");
    env.store_const(a.clone(), const_with_refs(vec![]));
    let visited = env.bfs_refs(&a);
    assert_eq!(visited.len(), 1);
    assert!(visited.contains(&a));
  }

  #[test]
  fn bfs_refs_transitive() {
    // a -> b -> c, a -> d
    let env = Env::new();
    let a = Address::hash(b"a");
    let b = Address::hash(b"b");
    let c = Address::hash(b"c");
    let d = Address::hash(b"d");
    env.store_const(a.clone(), const_with_refs(vec![b.clone(), d.clone()]));
    env.store_const(b.clone(), const_with_refs(vec![c.clone()]));
    env.store_const(c.clone(), const_with_refs(vec![]));
    env.store_const(d.clone(), const_with_refs(vec![]));
    let visited = env.bfs_refs(&a);
    assert_eq!(visited.len(), 4);
    assert!(visited.contains(&a));
    assert!(visited.contains(&b));
    assert!(visited.contains(&c));
    assert!(visited.contains(&d));
  }

  #[test]
  fn bfs_refs_cycle_terminates() {
    // a -> b -> a (cyclic, should not infinite-loop)
    let env = Env::new();
    let a = Address::hash(b"a");
    let b = Address::hash(b"b");
    env.store_const(a.clone(), const_with_refs(vec![b.clone()]));
    env.store_const(b.clone(), const_with_refs(vec![a.clone()]));
    let visited = env.bfs_refs(&a);
    assert_eq!(visited.len(), 2);
  }

  #[test]
  fn bfs_refs_includes_external_addresses() {
    // a -> b, where b is referenced but not stored in env. We still
    // surface b in the visited set so callers see the external dep.
    let env = Env::new();
    let a = Address::hash(b"a");
    let b = Address::hash(b"b-external");
    env.store_const(a.clone(), const_with_refs(vec![b.clone()]));
    let visited = env.bfs_refs(&a);
    assert!(visited.contains(&a));
    assert!(visited.contains(&b));
  }

  #[test]
  fn transitive_deps_excl_excludes_root() {
    // a -> b -> c
    let env = Env::new();
    let a = Address::hash(b"a");
    let b = Address::hash(b"b");
    let c = Address::hash(b"c");
    env.store_const(a.clone(), const_with_refs(vec![b.clone()]));
    env.store_const(b.clone(), const_with_refs(vec![c.clone()]));
    env.store_const(c.clone(), const_with_refs(vec![]));
    let deps = env.transitive_deps_excl(&a);
    assert!(!deps.contains(&a));
    assert!(deps.contains(&b));
    assert!(deps.contains(&c));
    assert_eq!(deps.len(), 2);
  }

  #[test]
  fn transitive_deps_excl_is_sorted() {
    let env = Env::new();
    let a = Address::hash(b"a");
    // Use multiple deps; the returned Vec should be in sorted order
    // regardless of how the BFS visited them.
    let mut refs: Vec<Address> =
      (0..16).map(|i| Address::hash(format!("dep-{i}").as_bytes())).collect();
    env.store_const(a.clone(), const_with_refs(refs.clone()));
    for r in &refs {
      env.store_const(r.clone(), const_with_refs(vec![]));
    }
    refs.sort_unstable();
    let deps = env.transitive_deps_excl(&a);
    assert_eq!(deps, refs);
  }

  #[test]
  fn transitive_deps_excl_empty_for_root_with_no_refs() {
    let env = Env::new();
    let a = Address::hash(b"a");
    env.store_const(a.clone(), const_with_refs(vec![]));
    assert!(env.transitive_deps_excl(&a).is_empty());
  }

  /// Round-trips an env through serialize → deserialize so the
  /// deserialized side holds purely lazy entries, then asserts that
  /// a `transitive_deps_excl(seed)` walk only touches constants
  /// reachable from `seed` (correctness of the BFS).
  ///
  /// Lazy-loaded `LazyConstant`s no longer cache materialized values
  /// (see `src/ix/ixon/lazy.rs` "Cache policy" docs), so we can't
  /// observe materialization via `is_materialized()` after a walk —
  /// that observable was always-false. Instead we assert the BFS
  /// returns exactly the closure, and that `is_materialized()` stays
  /// false everywhere (proving the load path doesn't accidentally
  /// pre-populate the cache).
  #[test]
  fn lazy_sparsity_only_materializes_closure() {
    // Build a small env: a→b→c, and an independent d. Each const is
    // stored at its true content address (round-trip through `put`+`get`
    // verifies `Address::hash(bytes) == addr`). The `d` discriminator
    // avoids a content-hash collision with `c` (both have empty refs).
    let env = Env::new();
    let c = store_canonical(&env, const_with_refs(vec![]));
    let b = store_canonical(&env, const_with_refs(vec![c.clone()]));
    let a = store_canonical(&env, const_with_refs(vec![b.clone()]));
    let d = store_canonical(&env, const_with_refs_discriminator(vec![], 1));

    // Serialize → deserialize so all entries are lazy-from-bytes.
    let mut buf = Vec::new();
    env.put(&mut buf).unwrap();
    let loaded = Env::get(&mut buf.as_slice()).unwrap();
    for entry in loaded.consts.iter() {
      assert!(
        !entry.value().is_materialized(),
        "freshly-loaded entry {:?} should not be materialized",
        entry.key()
      );
    }

    // BFS the closure of `a`; should hit {a, b, c} but not `d`.
    let deps = loaded.transitive_deps_excl(&a);
    let dep_set: FxHashSet<Address> = deps.iter().cloned().collect();
    assert!(dep_set.contains(&b), "`b` reachable from `a`");
    assert!(dep_set.contains(&c), "`c` reachable from `a` via `b`");
    assert!(!dep_set.contains(&d), "`d` should not be in `a`'s closure");
    assert!(!dep_set.contains(&a), "deps_excl excludes the seed");

    // Even after the BFS, no entries should report as materialized:
    // lazy-loaded `LazyConstant`s parse fresh on each `get()` and
    // don't cache (env-side caching is what kept mathlib's RSS at
    // ~30GB; the cache-free policy is what made `--anon` viable).
    for entry in loaded.consts.iter() {
      assert!(
        !entry.value().is_materialized(),
        "entry {:?} should remain unmaterialized after BFS",
        entry.key()
      );
    }
  }
}
