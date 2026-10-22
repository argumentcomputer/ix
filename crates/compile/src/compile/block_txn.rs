//! A failed block publishes nothing (the Lean drivers' behaviour,
//! `Ix.CompileDriver`: a block's state is merged only when the block compiles
//! and its claims pass).
//!
//! The Rust compiler publishes a block's results into the shared compile
//! state as it goes: the primary projections are registered before the
//! auxiliary tail runs, and the tail registers its auxiliaries as each one
//! compiles. While a scheduled block compiles, every name it newly enters
//! into a published table is logged here (thread-local: a block compiles on
//! one thread), and the names it would release to the scheduler early are
//! deferred to the block's end. Original metadata and hint writes are staged
//! until [`commit`] has checked every promotion claim. When the block fails,
//! [`rollback`] removes exactly what it entered, so nothing of it is visible
//! to a dependent, which then fails with a missing constant, as on the Lean
//! side, and the deferred names are dropped (the Lean drivers release nothing
//! of a failed block).
//!
//! Only names a block *newly* entered are logged (an insert into a vacant
//! entry), so a name another block owns (an identical re-claim) is never
//! removed. Nor is its `Named` entry ever replaced: an identical re-claim
//! does not own the entry ([`holds_compiled_claim`], [`holds_aux_claim`]),
//! so the re-claiming block registers nothing for it, and its rollback has
//! nothing of the owner's to restore (`CompileState::claim_and_register_*`).
//! Anonymous constants and blobs the failed block stored stay in the
//! content-addressed tables: no name refers to them, and another block may
//! have stored the same content.

use std::cell::RefCell;

use ix_common::address::Address;
use ix_common::env::{Name, ReducibilityHints};
use ixon::CompileError;
use ixon::metadata::ConstantMeta;
use rustc_hash::FxHashMap;

use super::CompileState;
use super::original_data::{Captured, Receipt};

pub struct Promotion {
  pub name: Name,
  pub addr: Address,
  pub meta: ConstantMeta,
  pub captured: Option<Captured>,
}

/// What a block entered into the published tables.
#[derive(Default)]
pub struct BlockTxn {
  /// Original metadata is not published until the entire block succeeds.
  /// A source family can include members outside the scheduled block;
  /// rolling back old snapshots could otherwise overwrite another worker's
  /// promotion.
  pub promotions: Vec<Promotion>,
  /// Final per-name hints, including removals, before publication.
  pub hints: FxHashMap<Name, Option<ReducibilityHints>>,
  /// Names newly registered in `env.named`.
  pub named: Vec<Name>,
  /// Names newly entered into `name_to_addr`.
  pub compiled: Vec<Name>,
  /// Names newly entered into `aux_name_to_addr`.
  pub aux: Vec<Name>,
  /// Pass 3 records newly entered (image-kind heads, Lean blocks, canonical
  /// recursors, component records).
  pub p3_heads: Vec<Name>,
  pub p3_blocks: Vec<Name>,
  pub p3_canon_recs: Vec<Name>,
  pub p3_components: Vec<Name>,
  /// Names the block would have released to the scheduler early.
  pub pending: Vec<Name>,
  /// Non-canonical outcomes become visible only after the whole block commits.
  pub declines: Vec<(Name, String)>,
}

thread_local! {
  static TXN: RefCell<Option<BlockTxn>> = const { RefCell::new(None) };
}

/// Start logging this thread's publications (a scheduled block begins).
pub fn start() {
  TXN.with(|t| *t.borrow_mut() = Some(BlockTxn::default()));
}

/// Stop logging, returning the log.
pub fn take() -> Option<BlockTxn> {
  TXN.with(|t| t.borrow_mut().take())
}

fn with(f: impl FnOnce(&mut BlockTxn)) {
  TXN.with(|t| {
    if let Some(x) = t.borrow_mut().as_mut() {
      f(x)
    }
  });
}

pub fn log_named(n: &Name) {
  with(|x| x.named.push(n.clone()));
}

/// Stage original metadata while a transaction is active. Outside a scheduled
/// block, return the payload to the direct caller for immediate promotion.
pub fn defer_promotion(promotion: Promotion) -> Option<Promotion> {
  TXN.with(|t| match t.borrow_mut().as_mut() {
    Some(x) => {
      x.promotions.push(promotion);
      None
    },
    None => Some(promotion),
  })
}

/// Called only after every fallible check. Bind the captured data to the Named
/// entry actually updated, not an earlier snapshot of another worker's entry.
pub fn publish_promotion(stt: &CompileState, p: Promotion) -> Option<Receipt> {
  let mut entry = stt.env.named.get_mut(&p.name)?;
  let published = entry.addr.clone();
  entry.value_mut().set_original(p.addr, p.meta);
  p.captured.map(|data| data.at(p.name, published))
}

/// Check every address claim before publishing any original metadata. Claims
/// entered here remain in the active transaction's rollback log on error.
/// No existing metadata is restored from an earlier concurrent snapshot.
pub fn commit(stt: &CompileState) -> Result<(), CompileError> {
  let (promotions, hints) = TXN.with(|t| {
    t.borrow_mut()
      .as_mut()
      .map(|x| {
        (std::mem::take(&mut x.promotions), std::mem::take(&mut x.hints))
      })
      .unwrap_or_default()
  });
  for p in &promotions {
    let addr = stt.aux_name_to_addr.get(&p.name).map(|r| r.value().clone());
    if let Some(addr) = addr {
      stt.claim_compiled_name(&p.name, &addr)?;
    }
  }
  let receipts: Vec<_> =
    promotions.into_iter().filter_map(|p| publish_promotion(stt, p)).collect();
  for (n, hint) in hints {
    match hint {
      Some(h) => {
        stt.def_hints.insert(n, h);
      },
      None => {
        stt.def_hints.remove(&n);
      },
    }
  }
  stt.original_receipts.lock().unwrap().extend(receipts);
  Ok(())
}

/// Preserve the compiler's last write, without exposing a failed original
/// compilation's hints (including writes for other source-family members).
pub fn defer_hint(n: &Name, hint: Option<ReducibilityHints>) -> bool {
  TXN.with(|t| match t.borrow_mut().as_mut() {
    Some(x) => {
      x.hints.insert(n.clone(), hint);
      true
    },
    None => false,
  })
}

/// A transaction reads its own last hint write; the outer option distinguishes
/// an explicit removal from a name not written in this transaction.
pub fn hint(n: &Name) -> Option<Option<ReducibilityHints>> {
  TXN.with(|t| t.borrow().as_ref().and_then(|x| x.hints.get(n).copied()))
}

pub fn log_compiled(n: &Name) {
  with(|x| x.compiled.push(n.clone()));
}

pub fn log_aux(n: &Name) {
  with(|x| x.aux.push(n.clone()));
}

/// Whether the active transaction entered `n` into `name_to_addr` itself
/// ([`log_compiled`]): an identical re-claim later in the same block still
/// owns the name's `Named` entry. `false` outside a transaction. Read only on
/// a re-claim, so the linear scan of the block's log stays off the common
/// path.
pub fn holds_compiled_claim(n: &Name) -> bool {
  TXN.with(|t| t.borrow().as_ref().is_some_and(|x| x.compiled.contains(n)))
}

/// Whether the active transaction entered `n` into `aux_name_to_addr`
/// itself ([`log_aux`]); see [`holds_compiled_claim`].
pub fn holds_aux_claim(n: &Name) -> bool {
  TXN.with(|t| t.borrow().as_ref().is_some_and(|x| x.aux.contains(n)))
}

pub fn log_p3_head(n: &Name) {
  with(|x| x.p3_heads.push(n.clone()));
}

pub fn log_p3_block(n: &Name) {
  with(|x| x.p3_blocks.push(n.clone()));
}

pub fn log_p3_canon_rec(n: &Name) {
  with(|x| x.p3_canon_recs.push(n.clone()));
}

pub fn log_p3_component(n: &Name) {
  with(|x| x.p3_components.push(n.clone()));
}

/// Defer the release of `names` to the end of the block while logging;
/// returns them back when no log is active (release now).
pub fn defer_pending(names: Vec<Name>) -> Option<Vec<Name>> {
  TXN.with(|t| match t.borrow_mut().as_mut() {
    Some(x) => {
      x.pending.extend(names);
      None
    },
    None => Some(names),
  })
}

/// Release `names` to the scheduler: at the end of the block when a log is
/// active ([`defer_pending`]), now otherwise.
pub fn release_pending(stt: &CompileState, names: Vec<Name>) {
  if let Some(names) = defer_pending(names) {
    stt.aux_gen_pending.lock().unwrap().extend(names);
  }
}

/// Stage successful rewrite reports until the block's final commit. A
/// direct caller outside a scheduled transaction publishes immediately.
pub fn record_declines(stt: &CompileState, rows: Vec<(Name, String)>) {
  if rows.is_empty() {
    return;
  }
  let immediate = TXN.with(|t| match t.borrow_mut().as_mut() {
    Some(x) => {
      x.declines.extend(rows);
      None
    },
    None => Some(rows),
  });
  if let Some(rows) = immediate {
    for (name, cause) in rows {
      stt.p3.non_canonical.insert(name, cause);
    }
  }
}

/// Remove what a failed block entered into the published tables.
pub fn rollback(stt: &CompileState, txn: &BlockTxn) {
  for n in &txn.named {
    stt.env.named.remove(n);
    stt.def_hints.remove(n);
  }
  for n in &txn.compiled {
    stt.name_to_addr.remove(n);
    stt.blocks.remove(n);
  }
  for n in &txn.aux {
    stt.aux_name_to_addr.remove(n);
    stt.aux_gen_extra_names.remove(n);
    stt.blocks.remove(n);
  }
  for n in &txn.p3_heads {
    stt.p3.heads.remove(n);
  }
  for n in &txn.p3_blocks {
    stt.p3.blocks.remove(n);
  }
  for n in &txn.p3_canon_recs {
    stt.p3.canon_recs.remove(n);
  }
  for n in &txn.p3_components {
    stt.p3.components.remove(n);
  }
}

/// End the block's log: on success commit its staged promotions and hints
/// ([`commit`]) and release its deferred names to the scheduler; on failure,
/// a failed commit included, roll back what it entered and drop the deferred
/// names. Returns the commit's error, if the block had compiled.
pub fn finish(stt: &CompileState, failed: bool) -> Result<(), CompileError> {
  let committed = if failed { Ok(()) } else { commit(stt) };
  if let Some(txn) = take() {
    if failed || committed.is_err() {
      rollback(stt, &txn);
    } else {
      for (name, cause) in txn.declines {
        stt.p3.non_canonical.insert(name, cause);
      }
      if !txn.pending.is_empty() {
        stt.aux_gen_pending.lock().unwrap().extend(txn.pending);
      }
    }
  }
  committed
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::compile::pass3::expr::dotted;

  #[test]
  fn decline_reports_wait_for_commit_and_failed_blocks_drop_them() {
    let stt = CompileState::default();
    let name = dotted("declined");
    start();
    record_declines(&stt, vec![(name.clone(), "first".into())]);
    assert!(stt.p3.non_canonical.is_empty());
    finish(&stt, true).unwrap();
    assert!(stt.p3.non_canonical.is_empty());

    start();
    record_declines(&stt, vec![(name.clone(), "committed".into())]);
    assert!(stt.p3.non_canonical.is_empty());
    finish(&stt, false).unwrap();
    assert_eq!(
      stt.p3.non_canonical.get(&name).map(|v| v.value().clone()),
      Some("committed".into())
    );
  }
}
