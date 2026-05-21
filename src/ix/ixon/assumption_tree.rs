//! Serializable merkle tree over `Address` leaves.
//!
//! Used to recover the leaf set committed to by a conditional claim's
//! `assumptions` root. The root alone tells the verifier *which* set
//! was assumed; the AssumptionTree carries the actual leaves so the
//! verifier can inspect them (e.g., "do I trust each of these axioms?").
//!
//! Two construction modes — both produce the same `Node`-shaped trees,
//! differ only in how leaves are arranged:
//!
//! - `canonical(leaves)` builds the same shape that
//!   [`merkle_root_canonical`] hashes, so
//!   `Self::canonical(L).map(|t| t.root()) == merkle_root_canonical(L)`.
//!   Includes `Padding` nodes at every level where odd-leaf padding
//!   happened in the canonical builder.
//! - `join(l, r)` is free-form O(1) composition; result root matches
//!   [`merkle_join`].
//!
//! ## Serialization
//!
//! Tag4 size 2 under flag 0xE:
//!
//! ```text
//! [Tag4(0xE, 2) = 0xE2] [body]
//!
//! body recursive:
//!   Leaf(addr):  [0x00] [addr:32]
//!   Padding:     [0x01]
//!   Node(l, r):  [0x02] [body l] [body r]
//! ```
//!
//! A `Padding` node represents the zero-sentinel slot used by the
//! canonical builder to even out odd levels. Its root is exactly
//! `zero_address()`, matching the bare 32-byte zero that merkle.rs
//! mixes into odd-level hashing. Splitting it from `Leaf` keeps
//! `leaves()` clean (it returns only real leaves, not the synthetic
//! padding addresses).

use crate::ix::address::Address;

use super::merkle::{MerklePath, leaf_hash, node_hash, zero_address};
use super::proof::{FLAG_CLAIM, VARIANT_ASSUMPTION_TREE};
use super::tag::Tag4;

// Body-tag bytes (within the AssumptionTree-flagged payload).
const BODY_LEAF: u8 = 0x00;
const BODY_PADDING: u8 = 0x01;
const BODY_NODE: u8 = 0x02;

/// A merkle tree over `Address` leaves with explicit shape.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AssumptionTree {
  /// A real assumption leaf.
  Leaf(Address),
  /// Canonical-builder padding. Root is `zero_address()` — matches the
  /// raw-zero sentinel mixed in by `merkle_root_canonical` at odd-count
  /// levels.
  Padding,
  /// Internal node combining two subtrees.
  Node(Box<AssumptionTree>, Box<AssumptionTree>),
}

impl AssumptionTree {
  // ---- Construction ----

  /// Build the canonical sorted+padded merkle tree over a leaf set.
  ///
  /// Returns `None` if `leaves` is empty (post-dedup). For a single
  /// leaf returns `Leaf(only)`. Otherwise builds the same shape that
  /// `merkle_root_canonical` produces, with `Padding` nodes wherever
  /// odd-level zero-padding occurs.
  pub fn canonical(leaves: &[Address]) -> Option<Self> {
    let mut sorted: Vec<Address> = leaves.to_vec();
    sorted.sort_unstable();
    sorted.dedup();
    if sorted.is_empty() {
      return None;
    }
    if sorted.len() == 1 {
      return Some(AssumptionTree::Leaf(sorted.into_iter().next().unwrap()));
    }
    let mut level: Vec<AssumptionTree> =
      sorted.into_iter().map(AssumptionTree::Leaf).collect();
    while level.len() > 1 {
      let mut next = Vec::with_capacity(level.len().div_ceil(2));
      let mut iter = level.into_iter().peekable();
      while iter.peek().is_some() {
        let l = iter.next().unwrap();
        let r = iter.next().unwrap_or(AssumptionTree::Padding);
        next.push(AssumptionTree::Node(Box::new(l), Box::new(r)));
      }
      level = next;
    }
    Some(level.into_iter().next().unwrap())
  }

  /// Combine two existing subtrees into a new free-form node in O(1).
  #[inline]
  pub fn join(left: Self, right: Self) -> Self {
    AssumptionTree::Node(Box::new(left), Box::new(right))
  }

  // ---- Queries ----

  /// Recursively compute the root hash.
  pub fn root(&self) -> Address {
    match self {
      AssumptionTree::Leaf(addr) => leaf_hash(addr),
      AssumptionTree::Padding => zero_address(),
      AssumptionTree::Node(l, r) => node_hash(&l.root(), &r.root()),
    }
  }

  /// In-order traversal of real leaves (skips `Padding`).
  pub fn leaves(&self) -> Vec<Address> {
    let mut out = Vec::new();
    self.collect_leaves(&mut out);
    out
  }

  fn collect_leaves(&self, out: &mut Vec<Address>) {
    match self {
      AssumptionTree::Leaf(addr) => out.push(addr.clone()),
      AssumptionTree::Padding => {},
      AssumptionTree::Node(l, r) => {
        l.collect_leaves(out);
        r.collect_leaves(out);
      },
    }
  }

  /// True iff `target` appears as a `Leaf` somewhere in the tree.
  pub fn contains(&self, target: &Address) -> bool {
    match self {
      AssumptionTree::Leaf(addr) => addr == target,
      AssumptionTree::Padding => false,
      AssumptionTree::Node(l, r) => l.contains(target) || r.contains(target),
    }
  }

  /// Produce a merkle membership path for `target`. Returns `None` if
  /// `target` is not a `Leaf` in the tree. Empty path for a
  /// single-leaf tree.
  ///
  /// Path is in leaf-to-root order: `path[0]` is the immediate sibling
  /// of the leaf, `path[N-1]` is the root-level sibling. Matches the
  /// order expected by `verify_merkle_proof`.
  pub fn merkle_proof(&self, target: &Address) -> Option<MerklePath> {
    let mut path: MerklePath = Vec::new();
    if self.search_path(target, &mut path) { Some(path) } else { None }
  }

  /// Recursive helper: if `target` is in this subtree, push the sibling
  /// at this level (after the recursive call returns) and return true.
  /// Since pushes happen on the way back up, `path[0]` ends up as the
  /// deepest (closest-to-leaf) sibling — leaf-to-root order.
  fn search_path(&self, target: &Address, path: &mut MerklePath) -> bool {
    match self {
      AssumptionTree::Leaf(addr) => addr == target,
      AssumptionTree::Padding => false,
      AssumptionTree::Node(l, r) => {
        if l.search_path(target, path) {
          // Target was in left subtree; sibling = r.root(), sibling
          // is on the right (is_left = false).
          path.push((r.root(), false));
          true
        } else if r.search_path(target, path) {
          // Target was in right subtree; sibling = l.root(), sibling
          // is on the left (is_left = true).
          path.push((l.root(), true));
          true
        } else {
          false
        }
      },
    }
  }

  // ---- Serialization ----

  /// Serialize with Tag4(0xE, 2) outer header + recursive body.
  pub fn put(&self, buf: &mut Vec<u8>) {
    Tag4::new(FLAG_CLAIM, VARIANT_ASSUMPTION_TREE).put(buf);
    self.put_body(buf);
  }

  fn put_body(&self, buf: &mut Vec<u8>) {
    match self {
      AssumptionTree::Leaf(addr) => {
        buf.push(BODY_LEAF);
        buf.extend_from_slice(addr.as_bytes());
      },
      AssumptionTree::Padding => {
        buf.push(BODY_PADDING);
      },
      AssumptionTree::Node(l, r) => {
        buf.push(BODY_NODE);
        l.put_body(buf);
        r.put_body(buf);
      },
    }
  }

  /// Deserialize: expects Tag4(0xE, 2) outer header.
  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let tag = Tag4::get(buf)?;
    if tag.flag != FLAG_CLAIM || tag.size != VARIANT_ASSUMPTION_TREE {
      return Err(format!(
        "AssumptionTree::get: expected Tag4{{0xE, 2}}, got Tag4{{{}, {}}}",
        tag.flag, tag.size,
      ));
    }
    Self::get_body(buf)
  }

  fn get_body(buf: &mut &[u8]) -> Result<Self, String> {
    let (tag, rest) =
      buf.split_first().ok_or("AssumptionTree: EOF reading body tag")?;
    *buf = rest;
    match *tag {
      BODY_LEAF => {
        if buf.len() < 32 {
          return Err(format!(
            "AssumptionTree: Leaf needs 32 bytes, have {}",
            buf.len()
          ));
        }
        let (head, rest) = buf.split_at(32);
        *buf = rest;
        let addr = Address::from_slice(head)
          .map_err(|_e| "AssumptionTree: invalid leaf address".to_string())?;
        Ok(AssumptionTree::Leaf(addr))
      },
      BODY_PADDING => Ok(AssumptionTree::Padding),
      BODY_NODE => {
        let l = Self::get_body(buf)?;
        let r = Self::get_body(buf)?;
        Ok(AssumptionTree::Node(Box::new(l), Box::new(r)))
      },
      b => Err(format!("AssumptionTree: invalid body tag 0x{:02X}", b)),
    }
  }

  /// Serialize to a fresh Vec.
  pub fn ser(&self) -> Vec<u8> {
    let mut buf = Vec::new();
    self.put(&mut buf);
    buf
  }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
  use super::super::merkle::{
    merkle_join, merkle_root_canonical, verify_merkle_proof,
  };
  use super::*;

  fn addr(seed: &[u8]) -> Address {
    Address::hash(seed)
  }

  // ---------- Construction ----------

  #[test]
  fn canonical_empty_is_none() {
    assert!(AssumptionTree::canonical(&[]).is_none());
  }

  #[test]
  fn canonical_single_leaf() {
    let a = addr(b"only");
    let t = AssumptionTree::canonical(std::slice::from_ref(&a)).unwrap();
    assert_eq!(t, AssumptionTree::Leaf(a));
  }

  #[test]
  fn canonical_two_leaves_no_padding() {
    let a = addr(b"a");
    let b = addr(b"b");
    let t = AssumptionTree::canonical(&[a.clone(), b.clone()]).unwrap();
    // sorted -> [min, max]; tree is Node(Leaf(min), Leaf(max))
    let (lo, hi) = if a < b { (a, b) } else { (b, a) };
    assert_eq!(
      t,
      AssumptionTree::Node(
        Box::new(AssumptionTree::Leaf(lo)),
        Box::new(AssumptionTree::Leaf(hi))
      )
    );
  }

  #[test]
  fn canonical_three_leaves_has_padding() {
    let a = addr(b"a");
    let b = addr(b"b");
    let c = addr(b"c");
    let t = AssumptionTree::canonical(&[a, b, c]).unwrap();
    // We don't pin down exact shape (depends on sort order) but the
    // tree must include at least one Padding node.
    fn has_padding(t: &AssumptionTree) -> bool {
      match t {
        AssumptionTree::Padding => true,
        AssumptionTree::Leaf(_) => false,
        AssumptionTree::Node(l, r) => has_padding(l) || has_padding(r),
      }
    }
    assert!(has_padding(&t));
  }

  // ---------- Root agreement ----------

  #[test]
  fn canonical_root_matches_merkle_root_canonical_single() {
    let a = addr(b"only");
    let t = AssumptionTree::canonical(std::slice::from_ref(&a)).unwrap();
    assert_eq!(Some(t.root()), merkle_root_canonical(&[a]));
  }

  #[test]
  fn canonical_root_matches_merkle_root_canonical_pairs() {
    for n in 2..=10 {
      let leaves: Vec<Address> =
        (0..n).map(|i| addr(format!("leaf-{i}").as_bytes())).collect();
      let t = AssumptionTree::canonical(&leaves).unwrap();
      assert_eq!(
        Some(t.root()),
        merkle_root_canonical(&leaves),
        "mismatch at n={n}"
      );
    }
  }

  #[test]
  fn canonical_root_dedups_like_primitive() {
    let a = addr(b"a");
    let b = addr(b"b");
    let t =
      AssumptionTree::canonical(&[a.clone(), a.clone(), b.clone()]).unwrap();
    assert_eq!(Some(t.root()), merkle_root_canonical(&[a, b]));
  }

  #[test]
  fn join_root_matches_merkle_join() {
    let a = addr(b"a");
    let b = addr(b"b");
    let l = AssumptionTree::canonical(std::slice::from_ref(&a)).unwrap();
    let r = AssumptionTree::canonical(std::slice::from_ref(&b)).unwrap();
    let joined = AssumptionTree::join(l.clone(), r.clone());
    assert_eq!(joined.root(), merkle_join(&l.root(), &r.root()));
  }

  // ---------- Leaves + contains ----------

  #[test]
  fn leaves_skip_padding() {
    let a = addr(b"a");
    let b = addr(b"b");
    let c = addr(b"c");
    let mut leaves = vec![a.clone(), b.clone(), c.clone()];
    leaves.sort_unstable();
    let t = AssumptionTree::canonical(&[a, b, c]).unwrap();
    assert_eq!(t.leaves(), leaves);
  }

  #[test]
  fn contains_matches_leaves() {
    let a = addr(b"a");
    let b = addr(b"b");
    let c = addr(b"c");
    let absent = addr(b"absent");
    let t =
      AssumptionTree::canonical(&[a.clone(), b.clone(), c.clone()]).unwrap();
    assert!(t.contains(&a));
    assert!(t.contains(&b));
    assert!(t.contains(&c));
    assert!(!t.contains(&absent));
  }

  // ---------- Merkle proofs ----------

  #[test]
  fn merkle_proof_single_leaf_empty_path() {
    let a = addr(b"only");
    let t = AssumptionTree::canonical(std::slice::from_ref(&a)).unwrap();
    let path = t.merkle_proof(&a).unwrap();
    assert!(path.is_empty());
    assert!(verify_merkle_proof(&t.root(), &a, &path));
  }

  #[test]
  fn merkle_proof_roundtrip_all_leaves() {
    for n in 1..=8 {
      let leaves: Vec<Address> =
        (0..n).map(|i| addr(format!("leaf-{i}").as_bytes())).collect();
      let t = AssumptionTree::canonical(&leaves).unwrap();
      let root = t.root();
      for leaf in t.leaves() {
        let path = t.merkle_proof(&leaf).expect("leaf present");
        assert!(
          verify_merkle_proof(&root, &leaf, &path),
          "verify failed for n={n}, leaf={}",
          leaf.hex()
        );
      }
    }
  }

  #[test]
  fn merkle_proof_nonmember_is_none() {
    let a = addr(b"a");
    let b = addr(b"b");
    let absent = addr(b"absent");
    let t = AssumptionTree::canonical(&[a, b]).unwrap();
    assert!(t.merkle_proof(&absent).is_none());
  }

  #[test]
  fn merkle_proof_through_join() {
    let a = addr(b"a");
    let b = addr(b"b");
    let c = addr(b"c");
    let left = AssumptionTree::canonical(&[a.clone(), b.clone()]).unwrap();
    let right = AssumptionTree::canonical(std::slice::from_ref(&c)).unwrap();
    let joined = AssumptionTree::join(left, right);
    for leaf in [a, b, c] {
      let path = joined.merkle_proof(&leaf).expect("leaf present in join");
      assert!(verify_merkle_proof(&joined.root(), &leaf, &path));
    }
  }

  // ---------- Serialization ----------

  #[test]
  fn serde_roundtrip_leaf() {
    let t = AssumptionTree::Leaf(addr(b"x"));
    let bytes = t.ser();
    assert_eq!(bytes[0], 0xE2, "outer tag is 0xE2");
    assert_eq!(bytes[1], BODY_LEAF, "body tag is 0x00 (Leaf)");
    assert_eq!(bytes.len(), 1 + 1 + 32);
    let parsed = AssumptionTree::get(&mut &bytes[..]).unwrap();
    assert_eq!(parsed, t);
  }

  #[test]
  fn serde_roundtrip_padding() {
    let t = AssumptionTree::Padding;
    let bytes = t.ser();
    assert_eq!(bytes[0], 0xE2);
    assert_eq!(bytes[1], BODY_PADDING);
    assert_eq!(bytes.len(), 2);
    let parsed = AssumptionTree::get(&mut &bytes[..]).unwrap();
    assert_eq!(parsed, t);
  }

  #[test]
  fn serde_roundtrip_node_simple() {
    let a = addr(b"a");
    let b = addr(b"b");
    let t = AssumptionTree::Node(
      Box::new(AssumptionTree::Leaf(a)),
      Box::new(AssumptionTree::Leaf(b)),
    );
    let bytes = t.ser();
    assert_eq!(bytes[0], 0xE2);
    assert_eq!(bytes[1], BODY_NODE);
    assert_eq!(bytes[2], BODY_LEAF);
    // Tag + Node tag + Leaf tag + 32 + Leaf tag + 32 = 1 + 1 + 1 + 32 + 1 + 32
    assert_eq!(bytes.len(), 1 + 1 + (1 + 32) + (1 + 32));
    let parsed = AssumptionTree::get(&mut &bytes[..]).unwrap();
    assert_eq!(parsed, t);
  }

  #[test]
  fn serde_roundtrip_canonical_trees() {
    for n in 1..=10 {
      let leaves: Vec<Address> =
        (0..n).map(|i| addr(format!("leaf-{i}").as_bytes())).collect();
      let t = AssumptionTree::canonical(&leaves).unwrap();
      let bytes = t.ser();
      let parsed = AssumptionTree::get(&mut &bytes[..]).unwrap();
      assert_eq!(parsed, t);
      assert_eq!(parsed.root(), t.root());
    }
  }

  #[test]
  fn serde_rejects_wrong_tag() {
    // Tag4(0xE, 3) = Eval claim, not AssumptionTree.
    let bytes = [0xE3, 0x00, 0x00];
    assert!(AssumptionTree::get(&mut &bytes[..]).is_err());
  }

  #[test]
  fn serde_rejects_invalid_body_tag() {
    // 0xE2 outer + 0x99 invalid body tag
    let bytes = [0xE2, 0x99];
    assert!(AssumptionTree::get(&mut &bytes[..]).is_err());
  }
}
