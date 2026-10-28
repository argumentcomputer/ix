//! Anonymous publication preserves every previously stored payload. Address
//! equality alone is not evidence of byte equality. Each comparison and insert
//! holds the same map entry guard, including when compiler workers race. The
//! Lean drivers check the same before merging a block
//! (`Ix.CompileM.checkCompiledBlock`, `Ix.CompileM.storeBlob`).

use dashmap::mapref::entry::Entry;
use ix_common::address::Address;
use ixon::{CompileError, LazyConstant, constant::Constant, env::DEMOTE};

use super::{CompileState, block_txn};

pub(super) fn conflict(kind: &str) -> CompileError {
  CompileError::InvalidMutualBlock {
    reason: format!("anonymous publication: conflicting {kind} payload"),
  }
}

impl CompileState {
  /// Store a compiled constant under `addr`, already serialized to `bytes` by
  /// the caller (who hashed them to `addr`), so it is not serialized again: an
  /// existing entry must hold the same bytes, or the store is the conflict
  /// error and the entry is kept.
  pub(crate) fn store_const_bytes(
    &self,
    addr: Address,
    bytes: Vec<u8>,
    constant: Constant,
  ) -> Result<(), CompileError> {
    self.store_const_bytes_demoted(addr, bytes, constant, *DEMOTE)
  }

  fn store_const_bytes_demoted(
    &self,
    addr: Address,
    bytes: Vec<u8>,
    constant: Constant,
    demote: bool,
  ) -> Result<(), CompileError> {
    // Built outside the map lock. Both storage policies compare the actual
    // bytes; neither overwrites nor silently accepts a conflicting key.
    let pending = LazyConstant::from_serialized(constant, bytes, !demote);
    block_txn::with(|txn| {
      if let Some(txn) = txn {
        if let Some(existing) = txn.constants.get(&addr) {
          if existing.raw_bytes() != pending.raw_bytes() {
            return Err(conflict("constant"));
          }
        } else if let Some(existing) = self.env.consts.get(&addr) {
          if existing.raw_bytes() != pending.raw_bytes() {
            return Err(conflict("constant"));
          }
        } else {
          txn.constants.insert(addr, pending);
        }
        return Ok(());
      }
      let _publication = self.publication_lock.lock().unwrap();
      match self.env.consts.entry(addr) {
        Entry::Occupied(entry) => {
          if entry.get().raw_bytes() != pending.raw_bytes() {
            return Err(conflict("constant"));
          }
        },
        Entry::Vacant(entry) => {
          entry.insert(pending);
        },
      }
      Ok(())
    })
  }

  /// Store a blob under its content address: an existing entry must hold the
  /// same bytes, or the store is the conflict error and the entry is kept.
  pub(crate) fn store_blob(
    &self,
    bytes: Vec<u8>,
  ) -> Result<Address, CompileError> {
    let addr = Address::hash(&bytes);
    block_txn::with(|txn| {
      if let Some(txn) = txn {
        if let Some(existing) = txn.blobs.get(&addr) {
          if existing != &bytes {
            return Err(conflict("blob"));
          }
        } else if let Some(existing) = self.env.blobs.get(&addr) {
          if existing.value() != &bytes {
            return Err(conflict("blob"));
          }
        } else {
          txn.blobs.insert(addr.clone(), bytes);
        }
        return Ok(addr);
      }
      let _publication = self.publication_lock.lock().unwrap();
      match self.env.blobs.entry(addr.clone()) {
        Entry::Occupied(entry) => {
          if *entry.get() != bytes {
            return Err(conflict("blob"));
          }
        },
        Entry::Vacant(entry) => {
          entry.insert(bytes);
        },
      }
      Ok(addr)
    })
  }
}

#[cfg(test)]
mod tests {
  use std::sync::{Arc, Barrier};

  use ix_common::env::{
    AxiomVal, ConstantInfo as LeanConstantInfo, ConstantVal, DataValue,
    DefinitionSafety, DefinitionVal, Env as LeanEnv, Expr as LeanExpr, Level,
    Literal, Name, ReducibilityHints, SourceInfo, Syntax,
  };
  use ixon::{
    constant::{Axiom, ConstantInfo},
    expr::Expr,
  };

  use super::*;
  use crate::compile::{
    BlockCache, CompileOptions, block_txn, compile_const, compile_data_value,
    compile_env_with_options, compile_name, store_string,
  };
  use crate::graph::NameSet;

  fn constant(lvls: u64) -> Constant {
    Constant::new(ConstantInfo::Axio(Axiom {
      is_unsafe: false,
      lvls,
      typ: Expr::sort(0),
    }))
  }

  fn bytes(c: &Constant) -> Vec<u8> {
    let mut out = Vec::new();
    c.put(&mut out);
    out
  }

  fn name(s: &str) -> Name {
    Name::str(Name::anon(), s.to_owned())
  }

  fn axiom(n: &Name) -> LeanConstantInfo {
    LeanConstantInfo::AxiomInfo(AxiomVal {
      cnst: ConstantVal {
        name: n.clone(),
        level_params: vec![],
        typ: LeanExpr::sort(Level::succ(Level::zero())),
      },
      is_unsafe: false,
    })
  }

  fn definition(n: &Name, value: LeanExpr, all: Vec<Name>) -> LeanConstantInfo {
    LeanConstantInfo::DefnInfo(DefinitionVal {
      cnst: ConstantVal {
        name: n.clone(),
        level_params: vec![],
        typ: LeanExpr::sort(Level::succ(Level::zero())),
      },
      value,
      hints: ReducibilityHints::Opaque,
      safety: DefinitionSafety::Safe,
      all,
    })
  }

  fn artifact(stt: &CompileState) -> Vec<u8> {
    let mut bytes = Vec::new();
    stt.env.put(&mut bytes).unwrap();
    bytes
  }

  #[test]
  fn refused_mutual_block_preserves_the_complete_owner_artifact() {
    let (f, g) = (name("refusedMember"), name("existingOwner"));
    let mut owner_env = LeanEnv::default();
    owner_env.insert(g.clone(), axiom(&g));
    let stt = CompileState::default();
    let owner = compile_const(
      &g,
      &[g.clone()].into_iter().collect(),
      &Arc::new(owner_env),
      &mut BlockCache::default(),
      &stt,
    )
    .unwrap();
    let before = artifact(&stt);
    let mut members = LeanEnv::default();
    let all = vec![f.clone(), g.clone()];
    members.insert(
      f.clone(),
      definition(&f, LeanExpr::cnst(g.clone(), vec![]), all.clone()),
    );
    members.insert(
      g.clone(),
      definition(&g, LeanExpr::cnst(f.clone(), vec![]), all.clone()),
    );
    let all: NameSet = all.into_iter().collect();
    block_txn::start();
    let result = compile_const(
      &f,
      &all,
      &Arc::new(members),
      &mut BlockCache::default(),
      &stt,
    );
    block_txn::finish(&stt, result.is_err()).unwrap();
    let error = result.unwrap_err().to_string();
    assert!(error.contains("conflicting claims for name 'existingOwner'"));
    assert_eq!(stt.resolve_addr(&g), Some(owner.clone()));
    assert_eq!(stt.env.named.get(&g).unwrap().addr, owner.clone());
    let keys: Vec<_> = stt.env.consts.iter().map(|e| e.key().clone()).collect();
    assert_eq!(keys, vec![owner], "failed block leaked anonymous records");
    assert!(stt.blocks.is_empty(), "failed block leaked class ordering");
    assert_eq!(artifact(&stt), before, "failed block changed partial output");
  }

  #[test]
  fn scheduled_failure_preserves_the_successful_subset_artifact() {
    let (owner, bad, dependent) =
      (name("owner"), name("badProjection"), name("dependent"));
    let mut success = LeanEnv::default();
    success.insert(owner.clone(), axiom(&owner));
    let options = CompileOptions { max_workers: Some(2) };
    let expected =
      compile_env_with_options(&Arc::new(success.clone()), options).unwrap();
    let mut input = success;
    input.insert(
      bad.clone(),
      definition(
        &bad,
        LeanExpr::proj(
          owner.clone(),
          bignat::Nat(num_bigint::BigUint::from(1u64) << 64u32),
          LeanExpr::lit(Literal::StrVal("failed-block-literal".to_owned())),
        ),
        vec![bad.clone()],
      ),
    );
    input.insert(
      dependent.clone(),
      definition(
        &dependent,
        LeanExpr::cnst(bad.clone(), vec![]),
        vec![dependent.clone()],
      ),
    );
    let actual = compile_env_with_options(&Arc::new(input), options).unwrap();
    assert_eq!(actual.ungrounded.len(), 2);
    assert!(
      actual.ungrounded.get(&bad).unwrap().contains("proj index too large")
    );
    assert!(actual.ungrounded.contains_key(&dependent));
    assert_eq!(actual.env.consts.len(), expected.env.consts.len());
    assert_eq!(actual.env.named.len(), expected.env.named.len());
    assert_eq!(artifact(&actual), artifact(&expected));
  }

  #[test]
  fn successful_mutual_block_publishes_all_tables_with_identical_bytes() {
    let (f, g) = (name("firstMember"), name("secondMember"));
    let mut env = LeanEnv::default();
    let all = vec![f.clone(), g.clone()];
    env.insert(
      f.clone(),
      definition(&f, LeanExpr::cnst(g.clone(), vec![]), all.clone()),
    );
    env.insert(
      g.clone(),
      definition(&g, LeanExpr::cnst(f.clone(), vec![]), all.clone()),
    );
    let env = Arc::new(env);
    let all: NameSet = all.into_iter().collect();
    let run = |stt: &CompileState| {
      compile_const(&f, &all, &env, &mut BlockCache::default(), stt).unwrap()
    };
    let direct = CompileState::default();
    let expected = run(&direct);
    direct.finalize_hints();
    let staged = CompileState::default();
    block_txn::start();
    assert_eq!(run(&staged), expected);
    assert_eq!(staged.resolve_addr(&f), Some(expected));
    assert_eq!(artifact(&staged), artifact(&CompileState::default()));
    assert!(staged.blocks.is_empty());
    assert!(staged.def_hints.is_empty());
    block_txn::finish(&staged, false).unwrap();
    staged.finalize_hints();
    assert_eq!(staged.blocks.len(), 2);
    assert_eq!(staged.def_hints.len(), 2);
    assert_eq!(artifact(&staged), artifact(&direct));
  }

  fn store_named_record(stt: &CompileState, n: &Name, lvls: u64) -> Address {
    let c = constant(lvls);
    let key = Address::hash(&bytes(&c));
    stt.store_const(key.clone(), c).unwrap();
    compile_name(n, stt).unwrap();
    stt
      .claim_and_register_compiled(n, ixon::env::Named::with_addr(key.clone()))
      .unwrap();
    stt.record_hint(n, Some(ReducibilityHints::Abbrev));
    stt.register_block(n.clone(), vec![vec![n.clone()]]);
    key
  }

  #[test]
  fn concurrent_identical_success_survives_either_failure_order() {
    for failure_first in [false, true] {
      let stt = CompileState::default();
      let n = name("sharedOwner");
      let ready = Barrier::new(2);
      let ordered = Barrier::new(2);
      std::thread::scope(|scope| {
        let successful = scope.spawn(|| {
          block_txn::start();
          store_named_record(&stt, &n, 0);
          ready.wait();
          if failure_first {
            ordered.wait();
          }
          block_txn::finish(&stt, false).unwrap();
          if !failure_first {
            ordered.wait();
          }
        });
        let failed = scope.spawn(|| {
          block_txn::start();
          store_named_record(&stt, &n, 0);
          store_named_record(&stt, &name("failedOnly"), 1);
          store_string("failed-only-literal", &stt).unwrap();
          ready.wait();
          if !failure_first {
            ordered.wait();
          }
          block_txn::finish(&stt, true).unwrap();
          if failure_first {
            ordered.wait();
          }
        });
        successful.join().unwrap();
        failed.join().unwrap();
      });
      stt.finalize_hints();
      let expected = CompileState::default();
      store_named_record(&expected, &n, 0);
      expected.finalize_hints();
      assert_eq!(artifact(&stt), artifact(&expected));
      assert_eq!(stt.blocks.len(), 1);
      assert_eq!(stt.def_hints.len(), 1);
      assert_eq!(stt.name_to_addr.len(), 1);
    }
  }

  #[test]
  fn concurrent_conflicting_batches_publish_only_the_winner() {
    let stt = CompileState::default();
    let key = Address::hash(b"forced shared batch key");
    let ready = Barrier::new(2);
    let stage = |stt: &CompileState, side: u64| {
      stt.store_const(key.clone(), constant(side)).unwrap();
      let n = name(if side == 0 { "leftBatch" } else { "rightBatch" });
      compile_name(&n, stt).unwrap();
      stt
        .claim_and_register_compiled(
          &n,
          ixon::env::Named::with_addr(key.clone()),
        )
        .unwrap();
    };
    let winner = std::thread::scope(|scope| {
      let run = |side| {
        block_txn::start();
        stage(&stt, side);
        ready.wait();
        block_txn::finish(&stt, false)
      };
      let left = scope.spawn(move || run(0));
      let right = scope.spawn(move || run(1));
      let left = left.join().unwrap();
      let right = right.join().unwrap();
      assert_ne!(left.is_ok(), right.is_ok());
      let winner = if left.is_ok() { 0 } else { 1 };
      assert_eq!(
        left.err().or_else(|| right.err()),
        Some(conflict("constant"))
      );
      winner
    });
    let expected = CompileState::default();
    stage(&expected, winner);
    assert_eq!(artifact(&stt), artifact(&expected));
  }

  #[test]
  fn late_conflicts_refuse_the_entire_batch_without_partial_publication() {
    for kind in ["constant", "blob", "claim"] {
      let stt = CompileState::default();
      let claimed = name("lateClaim");
      block_txn::start();
      let key = store_named_record(&stt, &claimed, 0);
      store_named_record(&stt, &name("unrelatedStagedName"), 2);
      let blob = store_string("late-blob", &stt).unwrap();
      assert!(stt.env.consts.is_empty());
      std::thread::scope(|scope| {
        scope
          .spawn(|| match kind {
            "constant" => stt.store_const(key, constant(1)).unwrap(),
            "blob" => {
              // Deliberately poison the address after the block staged it.
              let _publication = stt.publication_lock.lock().unwrap();
              stt.env.blobs.insert(blob, b"existing bytes".to_vec());
            },
            "claim" => {
              store_named_record(&stt, &claimed, 1);
            },
            _ => unreachable!(),
          })
          .join()
          .unwrap();
      });
      let before = artifact(&stt);
      let error = block_txn::finish(&stt, false).unwrap_err();
      if kind == "claim" {
        assert!(error.to_string().contains("conflicting claims for name"));
      } else {
        assert_eq!(error, conflict(kind));
      }
      assert_eq!(artifact(&stt), before, "late {kind} conflict leaked output");
      let expected_names = usize::from(kind == "claim");
      assert_eq!(stt.name_to_addr.len(), expected_names);
      assert_eq!(stt.blocks.len(), expected_names);
      assert_eq!(stt.def_hints.len(), expected_names);
      assert!(block_txn::with(|txn| txn.is_none()));
    }
  }

  impl CompileState {
    fn store_const_demoted(
      &self,
      addr: Address,
      constant: Constant,
      demote: bool,
    ) -> Result<(), CompileError> {
      self.store_const_bytes_demoted(addr, bytes(&constant), constant, demote)
    }

    fn store_const(
      &self,
      addr: Address,
      constant: Constant,
    ) -> Result<(), CompileError> {
      self.store_const_bytes(addr, bytes(&constant), constant)
    }
  }

  #[test]
  fn aliases_agree_and_conflicts_preserve_the_old_payload_in_both_modes() {
    for demote in [false, true] {
      let stt = CompileState::default();
      let old = constant(0);
      let payload = bytes(&old);
      let key = Address::hash(&payload);
      stt.store_const_demoted(key.clone(), old.clone(), demote).unwrap();
      stt.store_const_demoted(key.clone(), old, demote).unwrap();
      // Deliberately inconsistent key, not a cryptographic collision.
      let err = stt
        .store_const_demoted(key.clone(), constant(1), demote)
        .expect_err("same key with different bytes must fail");
      assert_eq!(err, conflict("constant"));
      assert_eq!(stt.env.consts.get(&key).unwrap().raw_bytes(), payload);
      assert_eq!(stt.env.consts.len(), 1);
    }
  }

  #[test]
  fn lazy_prior_entries_are_checked_without_materializing_them() {
    let stt = CompileState::default();
    let incoming = constant(0);
    let key = Address::hash(&bytes(&incoming));
    // A malformed lazy record is still a prior payload to preserve. Comparing
    // raw bytes must neither parse it nor silently treat the key as a match.
    stt.env.store_const_lazy(key.clone(), vec![0xff].into());
    assert_eq!(
      stt.store_const(key.clone(), incoming),
      Err(conflict("constant"))
    );
    assert_eq!(stt.env.consts.get(&key).unwrap().raw_bytes(), &[0xff]);
  }

  #[test]
  fn constant_and_blob_address_spaces_remain_separate() {
    let stt = CompileState::default();
    let key = store_string("literal", &stt).unwrap();
    stt.store_const(key.clone(), constant(0)).unwrap();
    assert_eq!(stt.env.get_blob(&key).unwrap(), b"literal");
    assert_eq!(
      stt.env.consts.get(&key).unwrap().raw_bytes(),
      bytes(&constant(0))
    );
  }

  #[test]
  fn metadata_writers_propagate_blob_conflicts() {
    let stt = CompileState::default();
    let key = Address::hash(b"component");
    stt.env.blobs.insert(key.clone(), b"old payload".to_vec());
    assert_eq!(store_string("component", &stt), Err(conflict("blob")));
    let name = Name::str(Name::anon(), "component".to_owned());
    assert_eq!(compile_name(&name, &stt), Err(conflict("blob")));
    assert!(
      !stt.env.names.contains_key(&Address::from_blake3_hash(*name.get_hash()))
    );
    let syntax = Syntax::Atom(SourceInfo::None, "component".to_owned());
    assert_eq!(
      compile_data_value(&DataValue::OfSyntax(Box::new(syntax)), &stt),
      Err(conflict("blob"))
    );
    assert_eq!(stt.env.get_blob(&key).unwrap(), b"old payload");
  }

  #[test]
  fn compilation_refuses_a_poisoned_prior_record_before_registering_the_name() {
    use crate::compile::{BlockCache, block_txn, compile_const};
    use crate::graph::NameSet;
    use ix_common::env::{
      AxiomVal, ConstantInfo as LeanConstantInfo, ConstantVal, Env,
      Expr as LeanExpr, Level,
    };
    use std::sync::Arc;

    let name = Name::str(Name::anon(), "publicationAxiom".to_owned());
    let mut env = Env::default();
    env.insert(
      name.clone(),
      LeanConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: name.clone(),
          level_params: vec![],
          typ: LeanExpr::sort(Level::zero()),
        },
        is_unsafe: false,
      }),
    );
    let env = Arc::new(env);
    let all: NameSet = [name.clone()].into_iter().collect();
    let run = |stt: &CompileState| {
      compile_const(&name, &all, &env, &mut BlockCache::default(), stt)
    };
    let key = run(&CompileState::default()).unwrap();
    let stt = CompileState::default();
    stt.env.store_const_lazy(key.clone(), vec![0xff].into());
    block_txn::start();
    let result = run(&stt);
    block_txn::finish(&stt, true).unwrap();
    assert_eq!(result, Err(conflict("constant")));
    assert!(!stt.env.named.contains_key(&name));
    assert!(!stt.name_to_addr.contains_key(&name));
    assert_eq!(stt.env.consts.get(&key).unwrap().raw_bytes(), &[0xff]);
  }

  #[test]
  fn concurrent_conflicting_writers_cannot_overwrite_the_winner() {
    for demote in [false, true] {
      let stt = CompileState::default();
      let key = Address::hash(b"forced shared key");
      let barrier = Barrier::new(2);
      std::thread::scope(|scope| {
        let left = scope.spawn(|| {
          barrier.wait();
          stt.store_const_demoted(key.clone(), constant(0), demote)
        });
        let right = scope.spawn(|| {
          barrier.wait();
          stt.store_const_demoted(key.clone(), constant(1), demote)
        });
        let left = left.join().unwrap();
        let right = right.join().unwrap();
        assert_ne!(left.is_ok(), right.is_ok());
        let winner = if left.is_ok() { 0 } else { 1 };
        assert_eq!(
          stt.env.consts.get(&key).unwrap().raw_bytes(),
          bytes(&constant(winner))
        );
        assert_eq!(
          left.err().or_else(|| right.err()),
          Some(conflict("constant"))
        );
      });
    }
  }

  #[test]
  fn concurrent_identical_writers_both_succeed() {
    let stt = CompileState::default();
    let key = Address::hash(&bytes(&constant(0)));
    let barrier = Barrier::new(2);
    std::thread::scope(|scope| {
      let left = scope.spawn(|| {
        barrier.wait();
        stt.store_const_demoted(key.clone(), constant(0), false)
      });
      let right = scope.spawn(|| {
        barrier.wait();
        stt.store_const_demoted(key.clone(), constant(0), true)
      });
      left.join().unwrap().unwrap();
      right.join().unwrap().unwrap();
    });
    assert_eq!(stt.env.consts.len(), 1);
    assert_eq!(
      stt.env.consts.get(&key).unwrap().raw_bytes(),
      bytes(&constant(0))
    );
  }
}
