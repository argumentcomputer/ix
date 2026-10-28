//! Anonymous publication preserves every previously stored payload. Address
//! equality alone is not evidence of byte equality. Each comparison and insert
//! holds the same map entry guard, including when compiler workers race. The
//! Lean drivers check the same before merging a block
//! (`Ix.CompileM.checkCompiledBlock`, `Ix.CompileM.storeBlob`).

use dashmap::mapref::entry::Entry;
use ix_common::address::Address;
use ixon::{CompileError, LazyConstant, constant::Constant, env::DEMOTE};

use super::CompileState;

fn conflict(kind: &str) -> CompileError {
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
  }

  /// Store a blob under its content address: an existing entry must hold the
  /// same bytes, or the store is the conflict error and the entry is kept.
  pub(crate) fn store_blob(
    &self,
    bytes: Vec<u8>,
  ) -> Result<Address, CompileError> {
    let addr = Address::hash(&bytes);
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
    block_txn::finish(&stt, result.is_err());
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
    let expected = compile_env_with_options(&Arc::new(success.clone()), options)
      .unwrap();
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
    assert!(actual.ungrounded.get(&bad).unwrap().contains("proj index too large"));
    assert!(actual.ungrounded.contains_key(&dependent));
    assert_eq!(actual.env.consts.len(), expected.env.consts.len());
    assert_eq!(actual.env.named.len(), expected.env.named.len());
    assert_eq!(artifact(&actual), artifact(&expected));
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
    let txn = block_txn::take().unwrap();
    block_txn::rollback(&stt, &txn);
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
