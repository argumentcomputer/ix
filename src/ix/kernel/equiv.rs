//! Union-find (disjoint set) for context-aware definitional equality caching.
//!
//! Provides O(α(n)) amortized equivalence checks via weighted quick-union
//! with path halving. Keys are `(ptr_key, ctx_component)` pairs: closed
//! expressions use ctx=0, open expressions under let-bindings use ctx_id.

use rustc_hash::FxHashMap;

/// Composite key: (expression pointer, context component).
type EqKey = (usize, usize);

/// Union-find structure for tracking definitional equality between
/// (ptr_key, ctx_component) pairs.
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
  pub fn is_equiv(&mut self, k1: EqKey, k2: EqKey) -> bool {
    if k1 == k2 {
      return true;
    }
    let n1 = match self.key_to_node.get(&k1) {
      Some(&n) => n,
      None => return false,
    };
    let n2 = match self.key_to_node.get(&k2) {
      Some(&n) => n,
      None => return false,
    };
    self.find(n1) == self.find(n2)
  }

  /// Find the root representative key for a given composite key.
  /// Returns None if the key is not in the union-find.
  pub fn find_root_key(&mut self, key: EqKey) -> Option<EqKey> {
    let node = *self.key_to_node.get(&key)?;
    let root = self.find(node);
    Some(self.node_to_key[root])
  }

  /// Record that two composite keys are definitionally equal.
  pub fn add_equiv(&mut self, k1: EqKey, k2: EqKey) {
    let n1 = self.node_for_key(k1);
    let n2 = self.node_for_key(k2);
    self.union(n1, n2);
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_basic_equiv() {
    let mut em = EquivManager::new();
    assert!(!em.is_equiv((100, 0), (200, 0)));
    em.add_equiv((100, 0), (200, 0));
    assert!(em.is_equiv((100, 0), (200, 0)));
    assert!(em.is_equiv((200, 0), (100, 0)));
  }

  #[test]
  fn test_transitivity() {
    let mut em = EquivManager::new();
    em.add_equiv((100, 0), (200, 0));
    em.add_equiv((200, 0), (300, 0));
    assert!(em.is_equiv((100, 0), (300, 0)));
    assert!(em.is_equiv((300, 0), (100, 0)));
  }

  #[test]
  fn test_non_equivalent() {
    let mut em = EquivManager::new();
    em.add_equiv((100, 0), (200, 0));
    assert!(!em.is_equiv((100, 0), (400, 0)));
  }

  #[test]
  fn test_reflexive() {
    let mut em = EquivManager::new();
    assert!(em.is_equiv((100, 0), (100, 0)));
  }

  #[test]
  fn test_clear() {
    let mut em = EquivManager::new();
    em.add_equiv((100, 0), (200, 0));
    assert!(em.is_equiv((100, 0), (200, 0)));
    em.clear();
    assert!(!em.is_equiv((100, 0), (200, 0)));
  }

  #[test]
  fn test_large_chain() {
    let mut em = EquivManager::new();
    for i in 0..100 {
      em.add_equiv((i, 0), (i + 1, 0));
    }
    assert!(em.is_equiv((0, 0), (100, 0)));
    assert!(!em.is_equiv((0, 0), (200, 0)));
  }

  #[test]
  fn test_context_isolation() {
    let mut em = EquivManager::new();
    // Same ptrs, different contexts — should NOT be equivalent
    em.add_equiv((100, 1), (200, 1));
    assert!(em.is_equiv((100, 1), (200, 1)));
    assert!(!em.is_equiv((100, 2), (200, 2)));
  }

  #[test]
  fn test_closed_exprs_share_across_contexts() {
    let mut em = EquivManager::new();
    // Closed expressions use ctx=0, shared across all contexts
    em.add_equiv((100, 0), (200, 0));
    assert!(em.is_equiv((100, 0), (200, 0)));
  }
}
