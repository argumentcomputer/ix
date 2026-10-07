//! Pass 3, the faithful rewrite (`IX_PASS3=images`), in the Rust compiler
//! (M6R slices 1 and 2). The specification is `docs/compiler-passes.md` §4; the
//! reference is the Lean compiler's switch-on output (`Ix/Compile/Pass/*`,
//! `Ix/Compile/Image/*`).
//!
//! Module map (Lean to Rust):
//!
//! | Lean | Rust |
//! |---|---|
//! | `Pass/Names.lean` | [`names`] |
//! | `Canon/Expr.lean`, `Image/Expr.lean` | [`expr`] |
//! | `Image/Develop.lean` | [`develop`] |
//! | `Image/Spec.lean` | [`spec`] |
//! | `Image/Build.lean` | [`build`] |
//! | `Pass/ImageView.lean` | [`view`] |
//! | `Pass/Translate.lean` | [`translate`] |
//! | `Pass/SideCar.lean` | [`sidecar`] |
//! | `Pass/Driver.lean` | [`driver`] |
//!
//! `Pass/Opt/{Core,Engine,O1..O6,O11a}.lean` are [`opt`] (slice 2). `Clique/**` and `Pass/Cliques.lean` are [`clique`] (slice 3). Not yet
//! ported: the proof-justified passes
//! O7-O12 and the unit pass O11b (slice 4), the closure producers and pack
//! (slice 5).

pub mod build;
pub mod clique;
pub mod develop;
pub mod driver;
pub mod expr;
pub mod names;
pub mod opt;
pub mod sidecar;
pub mod spec;
pub mod translate;
pub mod view;

use std::cell::RefCell;

use dashmap::DashMap;

use ix_common::env::{Name, RecursorVal};

use self::view::ComponentRecord;

/// The Pass 3 records the driver carries from block to block (the Lean
/// `CompileEnv.p3*` tables), all insert-once.
#[derive(Default)]
pub struct Pass3State {
  /// Image-kind head to its Lean block key (`all[0]`).
  pub heads: DashMap<Name, Name>,
  /// Lean block key to its `all`.
  pub blocks: DashMap<Name, Vec<Name>>,
  /// Pass 2's canonical recursors, by aux-gen name.
  pub canon_recs: DashMap<Name, RecursorVal>,
  /// The classes and nested permutation of each compiled component of a
  /// changed block, by member (what the view reads of Pass 1).
  pub components: DashMap<Name, ComponentRecord>,
  /// The compile's non-canonical set (`CompileEnv.p3NonCanonical`): the
  /// recorded declines of the definitional passes, by constant, merged from
  /// the blocks that compiled (a later cause of one constant replaces an
  /// earlier one, as the Lean map insert does).
  pub non_canonical: DashMap<Name, String>,
  /// The changed-clique table (`CompileEnv.p3Cliques`, `scheduleCliques`):
  /// member or carried lemma to (Lean's `all`, the carried lemmas).
  pub cliques: clique::hook::CliqueTable,
  /// The encoding roots (`CompileEnv.p3CliqueRoots`).
  pub clique_roots: rustc_hash::FxHashMap<Name, Vec<Name>>,
  /// The references of the blocks that reference a clique's encoding
  /// constant (what `cliqueCallers` reads of `p3BlockRefs`).
  pub clique_refs: rustc_hash::FxHashMap<Name, Vec<Name>>,
  /// The plan table (`CompileEnv.p3CliquePlans`), a memo of `planClique`
  /// keyed by the clique's first member, first entry kept.
  pub clique_plans: DashMap<Name, clique::transport::CliqueOutcome>,
}

/// A record the aux tail made, journaled for the side-car edit.
pub struct Journal {
  /// Names claimed by the tail (`claim_aux_name`), in claim order.
  pub claimed: Vec<Name>,
  /// Synthetic `Muts` entries the tail registered.
  pub muts: Vec<Name>,
  /// Names the tail would have released to the scheduler.
  pub pending: Vec<Name>,
  /// The canonical recursors the tail generated (Pass 2).
  pub recs: Vec<(Name, RecursorVal)>,
  /// The number of canonical nested auxiliaries of the component.
  pub n_canonical_aux: usize,
  /// The canonical recursors of the block's Prop `IndPredBelow` family.
  pub below_recs: Vec<(Name, RecursorVal)>,
}

thread_local! {
  static JOURNAL: RefCell<Option<Journal>> = const { RefCell::new(None) };
}

/// Start journaling the aux tail's registrations on this thread.
pub fn journal_start() {
  JOURNAL.with(|j| {
    *j.borrow_mut() = Some(Journal {
      claimed: Vec::new(),
      muts: Vec::new(),
      pending: Vec::new(),
      recs: Vec::new(),
      n_canonical_aux: 0,
      below_recs: Vec::new(),
    })
  });
}

/// Stop journaling, returning what was journaled.
pub fn journal_take() -> Option<Journal> {
  JOURNAL.with(|j| j.borrow_mut().take())
}

pub fn journal_active() -> bool {
  JOURNAL.with(|j| j.borrow().is_some())
}

pub fn journal_claim(n: &Name) {
  JOURNAL.with(|j| {
    if let Some(jr) = j.borrow_mut().as_mut() {
      jr.claimed.push(n.clone());
    }
  });
}

pub fn journal_muts(n: &Name) {
  JOURNAL.with(|j| {
    if let Some(jr) = j.borrow_mut().as_mut() {
      jr.muts.push(n.clone());
    }
  });
}

pub fn journal_recs(recs: Vec<(Name, RecursorVal)>, n_canonical_aux: usize) {
  JOURNAL.with(|j| {
    if let Some(jr) = j.borrow_mut().as_mut() {
      jr.recs.extend(recs);
      jr.n_canonical_aux = n_canonical_aux;
    }
  });
}

pub fn journal_below_recs(recs: Vec<(Name, RecursorVal)>) {
  JOURNAL.with(|j| {
    if let Some(jr) = j.borrow_mut().as_mut() {
      jr.below_recs.extend(recs);
    }
  });
}

/// Defer the release of `names` to the end of the edit while journaling;
/// returns them back when no journal is active (release now).
pub fn journal_defer_pending(names: Vec<Name>) -> Option<Vec<Name>> {
  JOURNAL.with(|j| match j.borrow_mut().as_mut() {
    Some(jr) => {
      jr.pending.extend(names);
      None
    },
    None => Some(names),
  })
}

/// Release aux names to the scheduler, or defer them while the aux tail is
/// journaled (see [`journal_defer_pending`]).
pub fn release_pending(stt: &crate::compile::CompileState, names: Vec<Name>) {
  if names.is_empty() {
    return;
  }
  // the Pass 3 journal first (the side-car edit), then the block log (the
  // release waits for the block to compile, `block_txn`)
  if let Some(names) = journal_defer_pending(names)
    && let Some(names) = crate::compile::block_txn::defer_pending(names)
  {
    stt.aux_gen_pending.lock().unwrap().extend(names);
  }
}
