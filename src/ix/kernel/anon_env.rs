//! `AnonEnv<'a>` — restricted view over `IxonEnv` exposing only the
//! anonymous (metadata-free) sections.
//!
//! Held in lieu of `&IxonEnv` everywhere the anon-mode kernel needs
//! env access (constant materialization, blob lookup, dependency
//! walking). Crucially, it does **not** expose `named`, `names`, or
//! `comms` — Lean.Name → metadata mappings that the anon kernel must
//! never consult.
//!
//! Two construction paths:
//!
//! 1. [`AnonEnv::from_env`] — borrowed view over an existing
//!    `IxonEnv`. The full env may still have metadata sections
//!    populated, but anon-mode code can't reach them through this
//!    wrapper.
//!
//! 2. [`Env::get_anon`] (Phase 3) — built fresh from `.ixe` bytes
//!    with the named/names/comms sections skipped during load.
//!
//! Either way, code parameterized over `&AnonEnv<'_>` is structurally
//! prevented from accessing metadata.

use rustc_hash::FxHashSet;
use std::collections::VecDeque;
use std::sync::Arc;

use crate::ix::address::Address;
use crate::ix::ixon::constant::Constant;
use crate::ix::ixon::env::Env as IxonEnv;

/// Anonymous-only view over an `IxonEnv`.
#[derive(Clone, Copy, Debug)]
pub struct AnonEnv<'a> {
  inner: &'a IxonEnv,
}

impl<'a> AnonEnv<'a> {
  /// Construct a view that exposes only the anonymous sections.
  pub fn from_env(env: &'a IxonEnv) -> Self {
    AnonEnv { inner: env }
  }

  /// Materialize the constant at `addr`.
  pub fn get_const(&self, addr: &Address) -> Option<Arc<Constant>> {
    self.inner.get_const(addr)
  }

  /// Raw constant bytes (no materialization).
  pub fn get_const_bytes(&self, addr: &Address) -> Option<Arc<[u8]>> {
    self.inner.get_const_bytes(addr)
  }

  /// Whether a constant is present in this view.
  pub fn contains_const(&self, addr: &Address) -> bool {
    self.inner.consts.contains_key(addr)
  }

  /// Number of constants.
  pub fn const_count(&self) -> usize {
    self.inner.const_count()
  }

  /// Get a blob by address (needed by anon ingress for string/nat
  /// literals embedded in expressions).
  pub fn get_blob(&self, addr: &Address) -> Option<Vec<u8>> {
    self.inner.get_blob(addr)
  }

  /// BFS-collect all addresses transitively reachable from `root`
  /// via `Constant.refs`. The returned set includes `root`.
  ///
  /// Materializes every visited constant. Constants outside the
  /// closure are not touched.
  pub fn bfs_refs(&self, root: &Address) -> FxHashSet<Address> {
    let mut visited: FxHashSet<Address> = FxHashSet::default();
    let mut queue: VecDeque<Address> = VecDeque::new();
    visited.insert(root.clone());
    queue.push_back(root.clone());
    while let Some(addr) = queue.pop_front() {
      let refs: Option<Vec<Address>> =
        self.get_const(&addr).map(|c| c.refs.clone());
      if let Some(rs) = refs {
        for r in rs {
          if visited.insert(r.clone()) {
            queue.push_back(r);
          }
        }
      }
    }
    visited
  }

  /// Transitive dep addresses of `root`, excluding `root`, sorted.
  pub fn transitive_deps_excl(&self, root: &Address) -> Vec<Address> {
    let mut set = self.bfs_refs(root);
    set.remove(root);
    let mut v: Vec<Address> = set.into_iter().collect();
    v.sort_unstable();
    v
  }

}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::env::Name;
  use crate::ix::ixon::constant::{Axiom, ConstantInfo};
  use crate::ix::ixon::env::Named;
  use crate::ix::ixon::expr::Expr;

  fn axiom_const_with_refs(refs: Vec<Address>) -> Constant {
    Constant::with_tables(
      ConstantInfo::Axio(Axiom {
        is_unsafe: false,
        lvls: 0,
        typ: Expr::sort(0),
      }),
      Vec::new(),
      refs,
      Vec::new(),
    )
  }

  fn n(s: &str) -> Name {
    Name::str(Name::anon(), s.to_string())
  }

  #[test]
  fn from_env_exposes_consts_and_blobs() {
    let env = IxonEnv::new();
    let a = Address::hash(b"a");
    env.store_const(a.clone(), axiom_const_with_refs(vec![]));
    let blob_addr = env.store_blob(b"hello".to_vec());
    let view = AnonEnv::from_env(&env);
    assert!(view.contains_const(&a));
    assert_eq!(view.const_count(), 1);
    assert_eq!(view.get_blob(&blob_addr), Some(b"hello".to_vec()));
  }

  #[test]
  fn bfs_refs_via_view_matches_env() {
    let env = IxonEnv::new();
    let a = Address::hash(b"a");
    let b = Address::hash(b"b");
    let c = Address::hash(b"c");
    env.store_const(a.clone(), axiom_const_with_refs(vec![b.clone()]));
    env.store_const(b.clone(), axiom_const_with_refs(vec![c.clone()]));
    env.store_const(c.clone(), axiom_const_with_refs(vec![]));
    let view = AnonEnv::from_env(&env);
    let visited = view.bfs_refs(&a);
    assert_eq!(visited.len(), 3);
    assert!(visited.contains(&a));
    assert!(visited.contains(&b));
    assert!(visited.contains(&c));
  }

  /// The wrapper exposes no API to reach the named map. Compile-time
  /// guarantee: this test just checks that we can construct an
  /// `AnonEnv` from an env whose `named` map is populated, and the
  /// public surface gives us no way to reach those entries.
  #[test]
  fn no_public_named_access() {
    let env = IxonEnv::new();
    let a = Address::hash(b"a");
    env.store_const(a.clone(), axiom_const_with_refs(vec![]));
    env.register_name(n("MyConst"), Named::with_addr(a.clone()));
    assert_eq!(env.named_count(), 1);
    let view = AnonEnv::from_env(&env);
    // `view.contains_const(&a)` works — `view.lookup_name(...)` doesn't exist.
    assert!(view.contains_const(&a));
    // (No assertion possible against absence of an API — this test
    // documents intent.)
  }
}
