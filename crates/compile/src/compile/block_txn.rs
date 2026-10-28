//! Publish a scheduled block only after compilation and all publication
//! checks succeed. The active thread stages every table write; its lookups
//! can read those writes, while other workers see only committed blocks.
//!
//! Commit validates the entire batch under the state's publication lock
//! before inserting anything. A late conflict is a block failure, including
//! when another worker claimed the same name or address after staging.
//! Failed batches are dropped, never deleted from shared tables: a successful
//! concurrent block may own identical content. This matches the Lean drivers'
//! check-then-merge behaviour, including partial serialized output.

use std::cell::RefCell;

use ix_common::{
  address::Address,
  env::{Name, ReducibilityHints},
};
use ixon::{CompileError, LazyConstant, env::Named};
use rustc_hash::{FxHashMap, FxHashSet};

use super::{CompileState, name_claim_conflict, publication::conflict};

#[derive(Default)]
pub(super) struct BlockTxn {
  pub constants: FxHashMap<Address, LazyConstant>,
  pub blobs: FxHashMap<Address, Vec<u8>>,
  pub names: FxHashMap<Address, Name>,
  pub named: FxHashMap<Name, Named>,
  pub claims: FxHashMap<Name, Address>,
  pub blocks: FxHashMap<Name, Vec<Vec<Name>>>,
  pub hints: FxHashMap<Name, Option<ReducibilityHints>>,
}

thread_local! {
  static TXN: RefCell<Option<BlockTxn>> = const { RefCell::new(None) };
}

/// Begin this thread's scheduled block. Nested transactions are a caller error.
pub fn start() {
  TXN.with(|t| {
    let mut current = t.borrow_mut();
    assert!(current.is_none(), "a block transaction is already active");
    *current = Some(BlockTxn::default());
  });
}

/// Access this thread's staged writes. Callers must not recursively access
/// the transaction while this closure holds its borrow.
pub(super) fn with<T>(f: impl FnOnce(Option<&mut BlockTxn>) -> T) -> T {
  TXN.with(|t| f(t.borrow_mut().as_mut()))
}

fn publish(stt: &CompileState, txn: BlockTxn) -> Result<(), CompileError> {
  // All compiler writers, including direct callers without a transaction,
  // hold this lock. Checks and inserts form one indivisible writer operation.
  let _publication = stt.publication_lock.lock().unwrap();
  for (addr, pending) in &txn.constants {
    if let Some(existing) = stt.env.consts.get(addr)
      && existing.raw_bytes() != pending.raw_bytes()
    {
      return Err(conflict("constant"));
    }
  }
  for (addr, pending) in &txn.blobs {
    if let Some(existing) = stt.env.blobs.get(addr)
      && existing.value() != pending
    {
      return Err(conflict("blob"));
    }
  }
  let mut reclaimed = FxHashSet::default();
  for (name, addr) in &txn.claims {
    if let Some(existing) = stt.name_to_addr.get(name) {
      if existing.value() != addr {
        return Err(name_claim_conflict(name, existing.value(), addr));
      }
      reclaimed.insert(name.clone());
    }
  }

  // No fallible check remains. Existing identical records and names keep
  // their owner; a repeated write within this batch keeps its last value.
  for (addr, constant) in txn.constants {
    stt.env.consts.entry(addr).or_insert(constant);
  }
  for (addr, bytes) in txn.blobs {
    stt.env.blobs.entry(addr).or_insert(bytes);
  }
  for (addr, name) in txn.names {
    stt.env.names.entry(addr).or_insert(name);
  }
  for (name, named) in txn.named {
    if !reclaimed.contains(&name) {
      stt.env.named.insert(name, named);
    }
  }
  for (name, classes) in txn.blocks {
    if !reclaimed.contains(&name) {
      stt.blocks.insert(name, classes);
    }
  }
  for (name, hint) in txn.hints {
    if reclaimed.contains(&name) {
      continue;
    }
    match hint {
      Some(hint) => {
        stt.def_hints.insert(name, hint);
      },
      None => {
        stt.def_hints.remove(&name);
      },
    }
  }
  // Publish resolution last, after the records and metadata it exposes.
  // The scheduler releases dependents only after this function returns.
  for (name, addr) in txn.claims {
    stt.name_to_addr.entry(name).or_insert(addr);
  }
  Ok(())
}

/// End this thread's block. Drop failed output, or validate and publish the
/// complete successful batch. A commit conflict must be reported as the
/// block's failure before the scheduler releases its dependents.
pub fn finish(stt: &CompileState, failed: bool) -> Result<(), CompileError> {
  let txn = TXN.with(|t| t.borrow_mut().take());
  if let Some(txn) = txn
    && !failed
  {
    publish(stt, txn)?;
  }
  Ok(())
}
