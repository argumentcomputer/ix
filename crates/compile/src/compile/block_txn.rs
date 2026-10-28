//! A failed block publishes nothing (the Lean drivers' behaviour,
//! `Ix.CompileDriver`: a block's state is merged only when the block compiles
//! and its claims pass).
//!
//! The Rust compiler publishes a block's results into the shared compile
//! state as it goes: each member's projection is registered as it compiles.
//! While a scheduled block compiles, every name it newly enters into a
//! published table is logged here (thread-local: a block compiles on one
//! thread), and its hint writes are staged until [`commit`]. When the block
//! fails, [`rollback`] removes exactly what it entered, so nothing of it is
//! visible to a dependent, which then fails with a missing constant, as on
//! the Lean side.
//!
//! Only names a block *newly* entered are logged (an insert into a vacant
//! entry), so a name another block owns (an identical re-claim) is never
//! removed. Nor is its `Named` entry ever replaced: an identical re-claim
//! does not own the entry ([`holds_compiled_claim`]), so the re-claiming
//! block registers nothing for it, and its rollback has nothing of the
//! owner's to restore (`CompileState::claim_and_register_compiled`).
//! Anonymous constants and blobs the failed block stored stay in the
//! content-addressed tables: no name refers to them, and another block may
//! have stored the same content.

use std::cell::RefCell;

use ix_common::env::{Name, ReducibilityHints};
use rustc_hash::FxHashMap;

use super::CompileState;

/// What a block entered into the published tables.
#[derive(Default)]
pub struct BlockTxn {
  /// Final per-name hints, including removals, before publication.
  pub hints: FxHashMap<Name, Option<ReducibilityHints>>,
  /// Names newly registered in `env.named`.
  pub named: Vec<Name>,
  /// Names newly entered into `name_to_addr`.
  pub compiled: Vec<Name>,
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

/// Publish the active block's staged hints. Called only once the block has
/// compiled.
pub fn commit(stt: &CompileState) {
  let hints = TXN.with(|t| {
    t.borrow_mut()
      .as_mut()
      .map(|x| std::mem::take(&mut x.hints))
      .unwrap_or_default()
  });
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
}

/// Preserve the compiler's last write, without exposing a failed block's
/// hints.
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

/// Whether the active transaction entered `n` into `name_to_addr` itself
/// ([`log_compiled`]): an identical re-claim later in the same block still
/// owns the name's `Named` entry. `false` outside a transaction. Read only on
/// a re-claim, so the linear scan of the block's log stays off the common
/// path.
pub fn holds_compiled_claim(n: &Name) -> bool {
  TXN.with(|t| t.borrow().as_ref().is_some_and(|x| x.compiled.contains(n)))
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
}

/// End the block's log: on success publish its staged hints ([`commit`]);
/// on failure roll back what it entered and drop its hints.
pub fn finish(stt: &CompileState, failed: bool) {
  if !failed {
    commit(stt);
  }
  if let Some(txn) = take()
    && failed
  {
    rollback(stt, &txn);
  }
}
