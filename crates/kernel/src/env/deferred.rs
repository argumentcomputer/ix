//! Deferred (on-demand) ingestion of constants into a [`KEnv`].
//!
//! A caller that would ingest many constants eagerly but needs few of them
//! can instead *register* each one with the environment and convert it only
//! when something reads it. The environment then behaves, for every reader,
//! as if the registered constants had been inserted at registration time:
//!
//! * [`KEnv::get`] (the `consts` map) still holds only materialized
//!   constants. Readers that must see registered ones go through
//!   `TypeChecker::try_get_const` (which asks the checker's
//!   `DeferredSource` to materialize on a miss) or materialize themselves
//!   after asking [`KEnv::pending`].
//! * [`KEnv::view_ids`] enumerates the ids an eager ingestion would hold, in
//!   the order its `consts` map would iterate them. The view's hash table
//!   receives exactly the insert calls the eager map would receive — every
//!   [`KEnv::insert`] and every registration, but not the materializing
//!   inserts ([`KEnv::insert_materialized`]), which have no eager
//!   counterpart. hashbrown's layout is a function of that call sequence
//!   (keys and order; an insert of a present key can still grow a full
//!   table), so the two tables iterate alike. `Primitives::from_env`
//!   resolves primitive ids from this view, because it keeps the first id
//!   it meets per address.
//!
//! The kernel itself never converts a registered constant: what a pending
//! entry stands for ([`Deferred`]) is interpreted by the registering caller,
//! which installs itself on each `TypeChecker` it builds over the
//! environment (`TypeChecker::with_deferred_source`).

use rustc_hash::FxHashMap;

use ix_common::env::Name;

use super::super::id::KId;
use super::super::mode::KernelMode;

/// What a registered-but-unconverted constant stands for. The registering
/// caller defines the meaning; the kernel only stores and hands it back.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Deferred {
  /// The source constant `name`, at full fidelity.
  Full(Name),
  /// Constructor `ctor` of inductive `induct` (position `cidx` among its
  /// constructors), as ingested together with its inductive.
  Ctor { induct: Name, ctor: Name, cidx: u64 },
  /// A type-only axiom stub of the source constant `name`.
  Stub(Name),
}

/// Bookkeeping for deferred ingestion; see the module documentation.
pub(crate) struct DeferredIngress<M: KernelMode> {
  /// Every id inserted into or registered with the environment. Receives
  /// the same insert calls as an eagerly ingested `consts` map would, so it
  /// has that map's key set and iteration order (see the module docs).
  view: FxHashMap<KId<M>, ()>,
  /// Registered ids not yet materialized.
  pending: FxHashMap<KId<M>, Deferred>,
  /// Counters, for diagnostics only.
  pub(crate) stats: DeferredStats,
}

/// Counters of one environment's deferred ingestion.
#[derive(Clone, Copy, Debug, Default)]
pub struct DeferredStats {
  /// Registrations (constants an eager ingestion would have converted).
  pub registered: u64,
  /// Registered constants converted because a reader needed them.
  pub materialized: u64,
  /// Registered constants overwritten by a direct insert before any
  /// reader needed them (an eager ingestion would have converted them and
  /// then lost the conversion to the same overwrite).
  pub superseded: u64,
}

impl<M: KernelMode> Default for DeferredIngress<M> {
  fn default() -> Self {
    DeferredIngress {
      view: FxHashMap::default(),
      pending: FxHashMap::default(),
      stats: DeferredStats::default(),
    }
  }
}

impl<M: KernelMode> DeferredIngress<M> {
  /// Record an insert of `id` into `consts` (called by `KEnv::insert`).
  /// A pending registration of the same id is superseded by it.
  pub(crate) fn note_insert(&mut self, id: &KId<M>) {
    if self.pending.remove(id).is_some() {
      self.stats.superseded += 1;
    }
    self.view.insert(id.clone(), ());
  }

  /// Register `id` as standing for `what`, replacing an earlier
  /// registration of the same id. The caller guarantees `id` is not in
  /// `consts`.
  pub(crate) fn register(&mut self, id: KId<M>, what: Deferred) {
    self.stats.registered += 1;
    self.view.insert(id.clone(), ());
    self.pending.insert(id, what);
  }

  pub(crate) fn pending(&self, id: &KId<M>) -> Option<&Deferred> {
    self.pending.get(id)
  }

  pub(crate) fn view_contains(&self, id: &KId<M>) -> bool {
    self.view.contains_key(id)
  }

  /// Remove and return the registration of `id`, counting it as
  /// materialized: the caller is about to insert its conversion.
  pub(crate) fn take_pending(&mut self, id: &KId<M>) -> Option<Deferred> {
    let what = self.pending.remove(id)?;
    self.stats.materialized += 1;
    Some(what)
  }

  pub(crate) fn view_ids(&self) -> impl Iterator<Item = &KId<M>> + '_ {
    self.view.keys()
  }

  pub(crate) fn view_len(&self) -> usize {
    self.view.len()
  }
}
