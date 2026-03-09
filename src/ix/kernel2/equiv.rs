//! Union-find (disjoint set) for pointer-based definitional equality caching.
//!
//! This provides O(alpha(n)) amortized equivalence checks via
//! weighted quick-union with path compression, keyed by pointer addresses.

use rustc_hash::FxHashMap;

/// Union-find structure for tracking definitional equality between `Val`
/// pointer addresses.
#[derive(Debug, Clone)]
pub struct EquivManager {
  /// Map from pointer address to union-find node index.
  addr_to_node: FxHashMap<usize, usize>,
  /// parent[i] = parent of node i. If parent[i] == i, it's a root.
  parent: Vec<usize>,
  /// rank[i] = upper bound on height of subtree rooted at i.
  rank: Vec<usize>,
}

impl Default for EquivManager {
  fn default() -> Self {
    Self::new()
  }
}

impl EquivManager {
  pub fn new() -> Self {
    EquivManager {
      addr_to_node: FxHashMap::default(),
      parent: Vec::new(),
      rank: Vec::new(),
    }
  }

  /// Reset all equivalence information.
  pub fn clear(&mut self) {
    self.addr_to_node.clear();
    self.parent.clear();
    self.rank.clear();
  }

  /// Get or create a node index for a pointer address.
  fn to_node(&mut self, ptr: usize) -> usize {
    if let Some(&node) = self.addr_to_node.get(&ptr) {
      return node;
    }
    let node = self.parent.len();
    self.parent.push(node);
    self.rank.push(0);
    self.addr_to_node.insert(ptr, node);
    node
  }

  /// Find the root of the set containing `node`, with path compression.
  fn find(&mut self, mut node: usize) -> usize {
    while self.parent[node] != node {
      // Path halving: make every other node point to its grandparent
      self.parent[node] = self.parent[self.parent[node]];
      node = self.parent[node];
    }
    node
  }

  /// Merge the sets containing `a` and `b`. Returns true if they were
  /// in different sets (i.e., the merge was non-trivial).
  fn union(&mut self, a: usize, b: usize) -> bool {
    let ra = self.find(a);
    let rb = self.find(b);
    if ra == rb {
      return false;
    }
    // Union by rank
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

  /// Check if two pointer addresses are in the same equivalence class.
  pub fn is_equiv(&mut self, ptr1: usize, ptr2: usize) -> bool {
    let n1 = match self.addr_to_node.get(&ptr1) {
      Some(&n) => n,
      None => return false,
    };
    let n2 = match self.addr_to_node.get(&ptr2) {
      Some(&n) => n,
      None => return false,
    };
    self.find(n1) == self.find(n2)
  }

  /// Record that two pointer addresses are definitionally equal.
  pub fn add_equiv(&mut self, ptr1: usize, ptr2: usize) {
    let n1 = self.to_node(ptr1);
    let n2 = self.to_node(ptr2);
    self.union(n1, n2);
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_equiv_manager() {
    let mut em = EquivManager::new();

    // Initially nothing is equivalent
    assert!(!em.is_equiv(100, 200));

    // Add equivalence
    em.add_equiv(100, 200);
    assert!(em.is_equiv(100, 200));
    assert!(em.is_equiv(200, 100));

    // Transitivity
    em.add_equiv(200, 300);
    assert!(em.is_equiv(100, 300));

    // Non-equivalent
    assert!(!em.is_equiv(100, 400));

    // Clear
    em.clear();
    assert!(!em.is_equiv(100, 200));
  }
}
