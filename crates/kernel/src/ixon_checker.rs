//! Checking boundary for decoded Ixon environments.
//!
//! Callers decode .ixe bytes with Ixon before constructing this checker.
//!
//! The worker environment is private: every declaration enters through the
//! kernel's address-verified ingress, which checks local definition cycles
//! before admitting a block. External dependencies are Ixon content
//! addresses, so checking a declaration need not rewalk their expression trees.
//! As with `TypeChecker::check_const`, referenced declarations are assumptions;
//! check every work item to certify a complete environment.

use ix_common::address::Address;
use ixon::env::Env;

use crate::env::KEnv;
use crate::error::TcError;
use crate::id::KId;
use crate::mode::Anon;
use crate::profile::ProfileSink;
use crate::tc::TypeChecker;

/// Diagnostics for the final member of the most recent block check.
#[derive(Default)]
pub struct CheckStats {
  pub fuel_used: u64,
  pub def_eq_peak: u32,
  pub hot_misses: String,
}

/// A worker whose kernel declarations come exclusively from Ixon ingress.
pub struct IxonChecker<'a> {
  source: &'a Env,
  kernel: KEnv<Anon>,
  last_check: CheckStats,
  debug_label: Option<String>,
}

impl<'a> IxonChecker<'a> {
  pub fn new(source: &'a Env) -> Self {
    Self {
      source,
      kernel: KEnv::new(),
      last_check: CheckStats::default(),
      debug_label: None,
    }
  }

  /// Check one standalone declaration or the whole block containing `addr`.
  pub fn check_const(&mut self, addr: &Address) -> Result<(), TcError<Anon>> {
    let mut checker =
      TypeChecker::new_with_lazy_anon(&mut self.kernel, self.source);
    checker.ixon_ingress = true;
    if let Some(label) = &self.debug_label {
      checker.set_debug_label(label.clone());
    }
    let result = checker.check_const(&KId::new(addr.clone(), ()));
    self.last_check = CheckStats {
      fuel_used: checker.fuel_used(),
      def_eq_peak: checker.def_eq_peak,
      hot_misses: checker.hot_miss_summary(),
    };
    checker.finish_constant_accounting();
    result
  }

  pub fn last_check(&self) -> &CheckStats {
    &self.last_check
  }

  pub fn set_debug_label(&mut self, label: String) {
    self.debug_label = Some(label);
  }

  pub fn perf(&self) -> &crate::perf::PerfCounters {
    &self.kernel.perf
  }

  pub fn clear_releasing_memory(&mut self) {
    self.kernel.clear_releasing_memory();
  }

  pub fn clear_with_capacity_limit(&mut self, max_capacity: usize) {
    self.kernel.clear_with_capacity_limit(max_capacity);
  }

  pub fn clear_reduction_caches(&mut self) {
    self.kernel.clear_reduction_caches();
  }

  pub fn set_profile_sink(&mut self, sink: ProfileSink) {
    self.kernel.profile_sink = Some(sink);
  }

  pub fn take_profile_sink(&mut self) -> Option<ProfileSink> {
    self.kernel.profile_sink.take()
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use ix_common::env::DefinitionSafety;
  use ixon::constant::{
    Constant, ConstantInfo, DefKind, Definition, MutConst, defn_proj_constant,
  };
  use ixon::expr::Expr;
  use ixon::univ::Univ;
  use std::sync::Arc;

  fn definition(value: Expr) -> Definition {
    Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ: Arc::new(Expr::Sort(1)),
      value: Arc::new(value),
    }
  }

  fn store(env: &Env, constant: Constant) -> Address {
    let addr = constant.commit().0;
    env.store_const(addr.clone(), constant);
    addr
  }

  fn sorts(constant: &mut Constant) {
    constant.univs = vec![Univ::zero(), Univ::succ(Univ::zero())];
  }

  fn loaded(env: &Env) -> Env {
    let mut bytes = Vec::new();
    env.put(&mut bytes).unwrap();
    Env::get_anon(&mut bytes.as_slice()).unwrap()
  }

  #[test]
  fn ixon_check_keeps_external_dependencies_lazy() {
    let env = Env::new();
    let mut base = Constant::new(ConstantInfo::Defn(definition(Expr::Sort(0))));
    sorts(&mut base);
    let mut addr = store(&env, base);
    for _ in 0..1024 {
      let mut c =
        Constant::new(ConstantInfo::Defn(definition(Expr::Ref(0, vec![]))));
      sorts(&mut c);
      c.refs.push(addr);
      addr = store(&env, c);
    }
    let source = loaded(&env);
    let mut checker = IxonChecker::new(&source);
    checker.check_const(&addr).unwrap();
    // Only the root and its direct reference's type are needed. Regressing
    // to a closure walk would materialize all 1025 declarations here.
    assert_eq!(checker.kernel.consts.len(), 2);
  }

  #[test]
  fn ixon_admission_rejects_local_cycles_atomically() {
    for cyclic in [false, true] {
      let env = Env::new();
      let mut block = Constant::new(ConstantInfo::Muts(vec![
        MutConst::Defn(definition(Expr::Rec(1, vec![]))),
        MutConst::Defn(definition(if cyclic {
          Expr::Rec(0, vec![])
        } else {
          Expr::Sort(0)
        })),
      ]));
      sorts(&mut block);
      let block_addr = store(&env, block);
      let first = store(&env, defn_proj_constant(0, block_addr.clone()));
      store(&env, defn_proj_constant(1, block_addr));
      let source = loaded(&env);
      let mut checker = IxonChecker::new(&source);
      let result = checker.check_const(&first);
      if cyclic {
        assert!(
          result
            .unwrap_err()
            .to_string()
            .contains("cyclic definition dependency")
        );
        assert!(checker.kernel.consts.is_empty());
        assert!(checker.kernel.blocks.is_empty());
      } else {
        result.unwrap();
      }
    }
  }

  #[test]
  fn ixon_admission_verifies_in_memory_address_bindings() {
    let source = Env::new();
    let mut c = Constant::new(ConstantInfo::Defn(definition(Expr::Sort(0))));
    sorts(&mut c);
    let addr = Address::hash(b"wrong map key");
    source.store_const(addr.clone(), c);
    assert!(IxonChecker::new(&source).check_const(&addr).is_err());
  }

  #[test]
  fn ixon_admission_verifies_every_projection_before_publishing_a_block() {
    let source = Env::new();
    let mut block = Constant::new(ConstantInfo::Muts(vec![
      MutConst::Defn(definition(Expr::Sort(0))),
      MutConst::Defn(definition(Expr::Sort(0))),
    ]));
    sorts(&mut block);
    let block_addr = store(&source, block);
    let first = store(&source, defn_proj_constant(0, block_addr.clone()));
    let sibling = defn_proj_constant(1, block_addr.clone()).commit().0;
    // The requested projection and block are valid. Its sibling's bytes lie
    // about the index, and must not be hidden by ingress of the whole block.
    source.store_const(sibling, defn_proj_constant(0, block_addr));
    let source = loaded(&source);
    let mut checker = IxonChecker::new(&source);
    assert!(checker.check_const(&first).is_err());
    assert!(checker.kernel.consts.is_empty());
  }
}
