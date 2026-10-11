//! A failed block publishes nothing (the Lean driver's behaviour,
//! `CompileDriver`: a block's state is merged only when the block compiles).
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
//! to a dependent, which then fails with a missing constant, as on the Lean side.
//!
//! Only names a block *newly* entered are logged (an insert into a vacant
//! entry), so a name another block owns (an identical re-claim) is never
//! removed. Anonymous constants and blobs the failed block stored stay in the
//! content-addressed tables: no name refers to them, and another block may
//! have stored the same content.

use std::cell::RefCell;

use ix_common::address::Address;
use ix_common::env::{Name, ReducibilityHints};
use ixon::CompileError;
use ixon::metadata::ConstantMeta;
use rustc_hash::FxHashMap;

use super::CompileState;

/// What a block entered into the published tables.
#[derive(Default)]
pub struct BlockTxn {
  /// Original metadata is not published until the entire block succeeds.
  /// A source family can include members outside the scheduled SCC; rolling
  /// back old snapshots could otherwise overwrite another worker's promotion.
  pub promotions: Vec<(Name, Address, ConstantMeta)>,
  /// Final per-name hints, including removals, before publication.
  pub hints: FxHashMap<Name, Option<ReducibilityHints>>,
  /// Names newly registered in `env.named`.
  pub named: Vec<Name>,
  /// Names newly entered into `name_to_addr`.
  pub compiled: Vec<Name>,
  /// Names newly entered into `aux_name_to_addr`.
  pub aux: Vec<Name>,
  /// Pass 3 records newly entered (image-kind heads, Lean blocks).
  pub p3_heads: Vec<Name>,
  pub p3_blocks: Vec<Name>,
  /// Names the block would have released to the scheduler early.
  pub pending: Vec<Name>,
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
pub fn defer_promotion(
  n: &Name,
  addr: Address,
  meta: ConstantMeta,
) -> Option<(Address, ConstantMeta)> {
  TXN.with(|t| match t.borrow_mut().as_mut() {
    Some(x) => {
      x.promotions.push((n.clone(), addr, meta));
      None
    },
    None => Some((addr, meta)),
  })
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
  for (n, _, _) in &promotions {
    let addr = stt.aux_name_to_addr.get(n).map(|r| r.value().clone());
    if let Some(addr) = addr {
      stt.claim_compiled_name(n, &addr)?;
    }
  }
  for (n, addr, meta) in promotions {
    if let Some(mut entry) = stt.env.named.get_mut(&n) {
      entry.value_mut().set_original(addr, meta);
    }
  }
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

pub fn log_p3_head(n: &Name) {
  with(|x| x.p3_heads.push(n.clone()));
}

pub fn log_p3_block(n: &Name) {
  with(|x| x.p3_blocks.push(n.clone()));
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
}
