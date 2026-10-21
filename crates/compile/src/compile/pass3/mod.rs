//! Pass 3, the faithful rewrite, in the Rust compiler. The reference is the
//! Lean compiler's `Ix.Compile.Image` (the image generator) and
//! `Ix.Compile.Pass`; the parity of the two image constructions is the
//! `pass3-rust-parity` suite, the parity of the compiles the byte legs
//! (`ix compile-lean --rust-check`).
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
//! The driver's two hooks run in every whole-environment compile
//! (`compile_env`): after the aux tail of a changed block
//! ([`driver::edit_changed_block`]) and before a block compiles
//! ([`driver::compile_block`]). No call-site plan is registered: the
//! callers of a changed block's auxiliaries are rewritten through the images.
//! The optimisation passes are not here.

pub mod build;
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
use std::sync::Arc;

use dashmap::DashMap;

use ix_common::env::{Expr, Name, RecursorVal};

use self::view::{BlockView, ComponentRecord, Expansion};

/// The Pass 3 records the driver carries from block to block (the Lean
/// `CompileEnv.p3*` tables). Every record table is insert-once, and a new
/// entry is logged for the failed-block rollback (`block_txn`); the two memo
/// tables keep their first entry.
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
  /// The compile's non-canonical set (`CompileEnv.p3NonCanonical`), reported
  /// by `CompileEnvStatus.nonCanonical`: the recorded declines of the
  /// definitional passes, by constant. No pass is wired yet, so it stays
  /// empty.
  pub non_canonical: DashMap<Name, String>,
  /// Stable views: entered only once every original member of the block is
  /// compiled.
  pub views: DashMap<Name, Arc<BlockView>>,
  /// The image memo: recursor images and their types, built from a stable
  /// view, and definitional heads' expansions rewritten from stable views
  /// (`compile_image_block`; Lean `CompileEnv.p3ImageExps`).
  pub image_exps: DashMap<Name, (Expansion, Expr)>,
}

/// A record the aux tail made, journaled for the side-car edit.
#[derive(Default)]
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
  JOURNAL.with(|j| *j.borrow_mut() = Some(Journal::default()));
}

/// Stop journaling, returning what was journaled.
pub fn journal_take() -> Option<Journal> {
  JOURNAL.with(|j| j.borrow_mut().take())
}

/// Whether the aux tail is being journaled on this thread.
pub fn journal_active() -> bool {
  JOURNAL.with(|j| j.borrow().is_some())
}

fn with_journal(f: impl FnOnce(&mut Journal)) {
  JOURNAL.with(|j| {
    if let Some(jr) = j.borrow_mut().as_mut() {
      f(jr)
    }
  });
}

pub fn journal_claim(n: &Name) {
  with_journal(|jr| jr.claimed.push(n.clone()));
}

pub fn journal_muts(n: &Name) {
  with_journal(|jr| jr.muts.push(n.clone()));
}

pub fn journal_recs(recs: Vec<(Name, RecursorVal)>, n_canonical_aux: usize) {
  with_journal(|jr| {
    jr.recs.extend(recs);
    jr.n_canonical_aux = n_canonical_aux;
  });
}

pub fn journal_below_recs(recs: Vec<(Name, RecursorVal)>) {
  with_journal(|jr| jr.below_recs.extend(recs));
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

/// Release aux names to the scheduler: the Pass 3 journal first (the
/// side-car edit decides which names are released), then the block log (the
/// release waits for the block to compile, `block_txn`).
pub fn release_pending(stt: &crate::compile::CompileState, names: Vec<Name>) {
  if names.is_empty() {
    return;
  }
  if let Some(names) = journal_defer_pending(names) {
    crate::compile::block_txn::release_pending(stt, names);
  }
}
