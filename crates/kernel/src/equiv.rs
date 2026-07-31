//! Union-find (disjoint set) for context-aware definitional equality caching.
//!
//! Provides O(α(n)) amortized equivalence checks via weighted quick-union
//! with path halving. Keys retain the expression hash, context hash, the
//! context-suffix radius used to construct that hash, and the expression's
//! intrinsic local-binder radius.

use rustc_hash::FxHashMap;

use super::env::{Addr, CtxAddr};

/// One expression in one context-suffix interpretation.
///
/// The radius is semantically load-bearing even if two suffix calculations
/// emit the same digest: DefEq transport is justified only at a common
/// requested radius. Keeping it in the union-find key prevents transitive
/// components from joining equality results established at different radii.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EqKey {
  pub expr_addr: Addr,
  pub ctx_addr: CtxAddr,
  /// Radius at which `ctx_addr` was computed for this comparison.
  pub lbr: u64,
  /// Intrinsic local-binder radius of the expression at `expr_addr`.
  pub expr_lbr: u64,
}

impl EqKey {
  pub fn new(
    expr_addr: Addr,
    ctx_addr: CtxAddr,
    lbr: u64,
    expr_lbr: u64,
  ) -> Self {
    Self { expr_addr, ctx_addr, lbr, expr_lbr }
  }

  /// Whether two representatives can safely reuse a DefEq cache context.
  /// Their intrinsic expression radii must reconstruct the requested radius
  /// at which the context digest was computed.
  pub fn root_cache_scope_matches(
    left: &Self,
    right: &Self,
    ctx_addr: CtxAddr,
    lbr: u64,
  ) -> bool {
    left.ctx_addr == ctx_addr
      && right.ctx_addr == ctx_addr
      && left.lbr == lbr
      && right.lbr == lbr
      && left.expr_lbr.max(right.expr_lbr) == lbr
  }
}

/// Union-find structure for tracking definitional equality between
/// context-aware expression keys.
#[derive(Debug, Clone)]
pub struct EquivManager {
  /// Map from composite key to union-find node index.
  key_to_node: FxHashMap<EqKey, usize>,
  /// `parent[i]` = parent of node `i`. Root if `parent[i] == i`.
  parent: Vec<usize>,
  /// `rank[i]` = upper bound on height of subtree rooted at `i`.
  rank: Vec<usize>,
  /// Reverse map: node index → composite key.
  node_to_key: Vec<EqKey>,
}

impl Default for EquivManager {
  fn default() -> Self {
    Self::new()
  }
}

impl EquivManager {
  pub fn new() -> Self {
    EquivManager {
      key_to_node: FxHashMap::default(),
      parent: Vec::new(),
      rank: Vec::new(),
      node_to_key: Vec::new(),
    }
  }

  /// Reset all equivalence information.
  pub fn clear(&mut self) {
    self.key_to_node.clear();
    self.parent.clear();
    self.rank.clear();
    self.node_to_key.clear();
  }

  /// Get or create a node index for a composite key.
  fn node_for_key(&mut self, key: EqKey) -> usize {
    if let Some(&node) = self.key_to_node.get(&key) {
      return node;
    }
    let node = self.parent.len();
    self.parent.push(node);
    self.rank.push(0);
    self.node_to_key.push(key);
    self.key_to_node.insert(key, node);
    node
  }

  /// Find root with path halving (every other node → grandparent).
  fn find(&mut self, mut node: usize) -> usize {
    while self.parent[node] != node {
      self.parent[node] = self.parent[self.parent[node]];
      node = self.parent[node];
    }
    node
  }

  /// Union by rank. Returns true if sets were different.
  fn union(&mut self, a: usize, b: usize) -> bool {
    let ra = self.find(a);
    let rb = self.find(b);
    if ra == rb {
      return false;
    }
    if self.rank[ra] < self.rank[rb] {
      self.parent[ra] = rb;
    } else if self.rank[ra] > self.rank[rb] {
      self.parent[rb] = ra;
    } else {
      self.parent[rb] = ra;
      self.rank[ra] += 1;
    }
    true
  }

  /// Check if two composite keys are equivalent.
  ///
  /// Takes keys by reference — callers in the `is_def_eq` hot path
  /// already hold `EqKey` tuples as local bindings, and forcing them to
  /// pass by value would require an Arc-clone on each component. With
  /// by-ref we avoid that clone entirely (see `src/ix/kernel/def_eq.rs`
  /// for the caller pattern).
  pub fn is_equiv(&mut self, k1: &EqKey, k2: &EqKey) -> bool {
    if k1 == k2 {
      return true;
    }
    let n1 = match self.key_to_node.get(k1) {
      Some(&n) => n,
      None => return false,
    };
    let n2 = match self.key_to_node.get(k2) {
      Some(&n) => n,
      None => return false,
    };
    self.find(n1) == self.find(n2)
  }

  /// Find the root representative key for a given composite key.
  /// Returns None if the key is not in the union-find.
  ///
  /// Like `is_equiv`, takes the lookup key by reference so callers can
  /// reuse a single `EqKey` binding across multiple queries without
  /// cloning it for each call.
  pub fn find_root_key(&mut self, key: &EqKey) -> Option<EqKey> {
    let node = *self.key_to_node.get(key)?;
    let root = self.find(node);
    Some(self.node_to_key[root])
  }

  /// Record that two composite keys are definitionally equal.
  ///
  /// Kept by-value because `node_for_key` inserts the key into the
  /// internal `key_to_node` map on first observation, requiring
  /// ownership transfer. Callers that have already consumed their
  /// `EqKey`s should clone at the call site, not here.
  pub fn add_equiv(&mut self, k1: EqKey, k2: EqKey) {
    let n1 = self.node_for_key(k1);
    let n2 = self.node_for_key(k2);
    self.union(n1, n2);
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn addr(n: u64) -> Addr {
    n
  }

  fn ctx(n: u64) -> CtxAddr {
    blake3::hash(&n.to_le_bytes())
  }

  #[test]
  fn test_basic_equiv() {
    let mut em = EquivManager::new();
    let zero = ctx(0);
    let a = EqKey::new(addr(100), zero, 0, 0);
    let b = EqKey::new(addr(200), zero, 0, 0);
    assert!(!em.is_equiv(&a, &b));
    em.add_equiv(a, b);
    assert!(em.is_equiv(&a, &b));
    assert!(em.is_equiv(&b, &a));
  }

  #[test]
  fn test_transitivity() {
    let mut em = EquivManager::new();
    let zero = ctx(0);
    let a = EqKey::new(addr(100), zero, 0, 0);
    let b = EqKey::new(addr(200), zero, 0, 0);
    let c = EqKey::new(addr(300), zero, 0, 0);
    em.add_equiv(a, b);
    em.add_equiv(b, c);
    assert!(em.is_equiv(&a, &c));
  }

  #[test]
  fn test_context_isolation() {
    let mut em = EquivManager::new();
    let ctx1 = ctx(1);
    let ctx2 = ctx(2);
    let a1 = EqKey::new(addr(100), ctx1, 1, 1);
    let b1 = EqKey::new(addr(200), ctx1, 1, 1);
    let a2 = EqKey::new(addr(100), ctx2, 1, 1);
    let b2 = EqKey::new(addr(200), ctx2, 1, 1);
    em.add_equiv(a1, b1);
    assert!(em.is_equiv(&a1, &b1));
    assert!(!em.is_equiv(&a2, &b2));
  }

  #[test]
  fn test_radius_isolation() {
    let mut em = EquivManager::new();
    let zero = ctx(0);
    let a1 = EqKey::new(addr(100), zero, 1, 1);
    let b1 = EqKey::new(addr(200), zero, 1, 1);
    let a2 = EqKey::new(addr(100), zero, 2, 1);
    let b2 = EqKey::new(addr(200), zero, 2, 1);
    em.add_equiv(a1, b1);
    assert!(em.is_equiv(&a1, &b1));
    assert!(!em.is_equiv(&a2, &b2));
  }

  #[test]
  fn test_intrinsic_radius_isolation() {
    let mut em = EquivManager::new();
    let zero = ctx(0);
    let a1 = EqKey::new(addr(100), zero, 2, 1);
    let b1 = EqKey::new(addr(200), zero, 2, 2);
    let a2 = EqKey::new(addr(100), zero, 2, 2);
    let b2 = EqKey::new(addr(200), zero, 2, 2);
    em.add_equiv(a1, b1);
    assert!(em.is_equiv(&a1, &b1));
    assert!(!em.is_equiv(&a2, &b2));
  }

  #[test]
  fn test_root_cache_scope_requires_intrinsic_radius() {
    let scope = ctx(0);
    let low_left = EqKey::new(addr(100), scope, 2, 1);
    let low_right = EqKey::new(addr(200), scope, 2, 1);
    let high_right = EqKey::new(addr(200), scope, 2, 2);

    assert!(!EqKey::root_cache_scope_matches(&low_left, &low_right, scope, 2));
    assert!(EqKey::root_cache_scope_matches(&low_left, &high_right, scope, 2));
  }
}
