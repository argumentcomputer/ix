//! A failed block publishes nothing (the Lean driver's behaviour,
//! `CompileDriver`: a block's state is merged only when the block compiles).
//!
//! The Rust compiler publishes a block's results into the shared compile
//! state as it goes: the primary projections are registered before the
//! auxiliary tail runs, and the tail registers its auxiliaries as each one
//! compiles. While a scheduled block compiles, every name it newly enters
//! into a published table is logged here (thread-local: a block compiles on
//! one thread), and the names it would release to the scheduler early are
//! deferred to the block's end. When the block fails, [`rollback`] removes
//! exactly what it entered, so nothing of it is visible to a dependent, which
//! then fails with a missing constant, as on the Lean side.
//!
//! Only names a block *newly* entered are logged (an insert into a vacant
//! entry), so a name another block owns (an identical re-claim) is never
//! removed. Anonymous constants and blobs the failed block stored stay in the
//! content-addressed tables: no name refers to them, and another block may
//! have stored the same content.

use std::cell::RefCell;

use ix_common::env::Name;

use super::CompileState;

/// What a block entered into the published tables.
#[derive(Default)]
pub struct BlockTxn {
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
