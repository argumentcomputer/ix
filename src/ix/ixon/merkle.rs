//! Canonical and free-form Merkle trees over `Address` leaves.
//!
//! Two construction modes share the same hash primitives:
//!
//! - **Canonical** (`merkle_root_canonical`): lex-sorted, deduped leaves;
//!   odd levels padded with the zero sentinel. Used for env merkle roots
//!   (deterministic env identity) and as the default builder for
//!   assumption-tree roots.
//! - **Free-form** (`merkle_join`): O(1) composition of two existing
//!   subtree roots into a new root. Used to aggregate the assumption
//!   sets of two claims without re-sorting all leaves.
//!
//! ## Domain separation
//!
//! Leaves are hashed as `blake3(0x00 || addr)` and internal nodes as
//! `blake3(0x01 || left || right)`. Follows RFC 6962 (Certificate
//! Transparency) convention. Strictly speaking the prefix bytes are
//! redundant for our scheme because leaf inputs (32 B) and node inputs
//! (64 B) have distinct lengths — so cross-length Blake3 collision is
//! the only attack vector and that's infeasible. But the prefix bytes
//! make the security argument structural rather than parametric, robust
//! under future refactors (variable-length leaves, raw-address mixing
//! into trees) and hash swaps (Poseidon2 sponge has fixed arity and
//! doesn't give the length argument for free).
//!
//! ## Odd-leaf padding
//!
//! The canonical builder pads odd levels with a fixed `[0u8; 32]`
//! sentinel rather than duplicating the trailing leaf. Duplication
//! introduces CVE-2012-2459-style malleability where two distinct leaf
//! lists can produce the same root.

use crate::ix::address::Address;

/// Domain-separation prefix for leaf hashes.
pub const LEAF_DOMAIN: u8 = 0x00;

/// Domain-separation prefix for internal-node hashes.
pub const NODE_DOMAIN: u8 = 0x01;

/// Zero sentinel used to pad odd levels of canonical trees.
pub const ZERO_SENTINEL: [u8; 32] = [0u8; 32];

// ---------------------------------------------------------------------------
// Primitives
// ---------------------------------------------------------------------------

/// Hash a leaf value into its canonical leaf-level digest.
#[inline]
pub fn leaf_hash(addr: &Address) -> Address {
  let mut h = blake3::Hasher::new();
  h.update(&[LEAF_DOMAIN]);
  h.update(addr.as_bytes());
  Address::from_blake3_hash(h.finalize())
}

/// Hash a pair of child digests into their parent internal-node digest.
#[inline]
pub fn node_hash(left: &Address, right: &Address) -> Address {
  let mut h = blake3::Hasher::new();
  h.update(&[NODE_DOMAIN]);
  h.update(left.as_bytes());
  h.update(right.as_bytes());
  Address::from_blake3_hash(h.finalize())
}

/// The fixed zero-sentinel address used as canonical-tree padding.
#[inline]
pub fn zero_address() -> Address {
  Address::from_slice(&ZERO_SENTINEL).expect("zero sentinel is 32 bytes")
}

// ---------------------------------------------------------------------------
// Canonical builder
// ---------------------------------------------------------------------------

/// Build the canonical merkle root over a leaf set. Leaves are lex-sorted
/// and deduplicated before hashing. Returns:
///
/// - `None` if `leaves` is empty (post-dedup).
/// - `Some(leaf_hash(x))` for a single leaf (no internal node).
/// - Otherwise an internal-node root with odd levels padded by
///   `zero_address()`.
pub fn merkle_root_canonical(leaves: &[Address]) -> Option<Address> {
  let mut sorted: Vec<Address> = leaves.to_vec();
  sorted.sort_unstable();
  sorted.dedup();
  if sorted.is_empty() {
    return None;
  }
  if sorted.len() == 1 {
    return Some(leaf_hash(&sorted[0]));
  }
  let mut level: Vec<Address> = sorted.iter().map(leaf_hash).collect();
  let zero = zero_address();
  while level.len() > 1 {
    let mut next = Vec::with_capacity(level.len().div_ceil(2));
    let mut i = 0;
    while i < level.len() {
      let l = &level[i];
      let r = level.get(i + 1).unwrap_or(&zero);
      next.push(node_hash(l, r));
      i += 2;
    }
    level = next;
  }
  Some(level.into_iter().next().unwrap())
}

// ---------------------------------------------------------------------------
// Free-form composition
// ---------------------------------------------------------------------------

/// Combine two existing subtree roots into a new free-form root in O(1).
///
/// The result is a non-canonical tree even if both inputs were canonical;
/// the verifier accepts both forms and the leaf set is recovered by
/// walking the tree from witness data, not by assuming any specific
/// shape.
#[inline]
pub fn merkle_join(left: &Address, right: &Address) -> Address {
  node_hash(left, right)
}

// ---------------------------------------------------------------------------
// Membership proofs
// ---------------------------------------------------------------------------

/// A merkle-path step: `(sibling, is_left)`. `is_left = true` means the
/// sibling sits on the left side at this level, so verification combines
/// it as `node_hash(sibling, current)`; otherwise `node_hash(current,
/// sibling)`.
pub type MerklePath = Vec<(Address, bool)>;

/// Produce a sibling-path for `target` in the canonical tree over
/// `leaves`. Returns `None` if `target` is not in the (post-dedup) leaf
/// set. Returns an empty path for a single-leaf tree.
pub fn merkle_proof_canonical(
  leaves: &[Address],
  target: &Address,
) -> Option<MerklePath> {
  let mut sorted: Vec<Address> = leaves.to_vec();
  sorted.sort_unstable();
  sorted.dedup();
  let mut pos = sorted.binary_search(target).ok()?;
  if sorted.len() == 1 {
    return Some(Vec::new());
  }
  let mut level: Vec<Address> = sorted.iter().map(leaf_hash).collect();
  let zero = zero_address();
  let mut path: MerklePath = Vec::new();
  while level.len() > 1 {
    let sibling_idx = pos ^ 1;
    let sibling = level.get(sibling_idx).cloned().unwrap_or_else(|| zero.clone());
    let is_left = pos & 1 == 1;
    path.push((sibling, is_left));
    // Build next level.
    let mut next = Vec::with_capacity(level.len().div_ceil(2));
    let mut i = 0;
    while i < level.len() {
      let l = &level[i];
      let r = level.get(i + 1).unwrap_or(&zero);
      next.push(node_hash(l, r));
      i += 2;
    }
    level = next;
    pos /= 2;
  }
  Some(path)
}

/// Verify a merkle membership proof against any root (canonical or
/// free-form). The path is shape-agnostic — verification just hashes
/// upward using each sibling at its recorded side.
pub fn verify_merkle_proof(
  root: &Address,
  leaf: &Address,
  path: &[(Address, bool)],
) -> bool {
  let mut current = leaf_hash(leaf);
  for (sibling, is_left) in path {
    current = if *is_left {
      node_hash(sibling, &current)
    } else {
      node_hash(&current, sibling)
    };
  }
  current == *root
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
  use super::*;
  use quickcheck::{Arbitrary, Gen};

  fn addr(seed: &[u8]) -> Address {
    Address::hash(seed)
  }

  // ---------- Canonical builder ----------

  #[test]
  fn canonical_empty() {
    assert!(merkle_root_canonical(&[]).is_none());
  }

  #[test]
  fn canonical_single() {
    let a = addr(b"only");
    let root = merkle_root_canonical(std::slice::from_ref(&a)).unwrap();
    assert_eq!(root, leaf_hash(&a));
  }

  #[test]
  fn canonical_sort_invariant() {
    let a = addr(b"a");
    let b = addr(b"b");
    let r1 = merkle_root_canonical(&[a.clone(), b.clone()]).unwrap();
    let r2 = merkle_root_canonical(&[b, a]).unwrap();
    assert_eq!(r1, r2);
  }

  #[test]
  fn canonical_dedup() {
    let a = addr(b"a");
    let b = addr(b"b");
    let r1 =
      merkle_root_canonical(&[a.clone(), a.clone(), b.clone()]).unwrap();
    let r2 = merkle_root_canonical(&[a, b]).unwrap();
    assert_eq!(r1, r2);
  }

  #[test]
  fn canonical_distinguishes() {
    let a = addr(b"a");
    let b = addr(b"b");
    let r1 = merkle_root_canonical(std::slice::from_ref(&a)).unwrap();
    let r2 = merkle_root_canonical(&[a, b]).unwrap();
    assert_ne!(r1, r2);
  }

  #[test]
  fn canonical_no_malleability() {
    // [a, a] deduplicates to [a], producing leaf_hash(a). A two-leaf
    // tree built from [a, a] without dedup would produce node_hash(
    // leaf_hash(a), leaf_hash(a)), which must differ.
    let a = addr(b"a");
    let deduped = merkle_root_canonical(&[a.clone(), a.clone()]).unwrap();
    let two_leaf_no_dedup = node_hash(&leaf_hash(&a), &leaf_hash(&a));
    assert_ne!(deduped, two_leaf_no_dedup);
    assert_eq!(deduped, leaf_hash(&a));
  }

  // ---------- Domain separation ----------

  #[test]
  fn leaf_vs_node_disjoint() {
    let a = addr(b"a");
    let z = zero_address();
    // leaf_hash(a) = blake3(0x00 || a)
    // node_hash(a, ZERO) = blake3(0x01 || a || ZERO)
    // Different domain prefixes AND different input lengths.
    assert_ne!(leaf_hash(&a), node_hash(&a, &z));
  }

  // ---------- Free-form (merkle_join) ----------

  #[test]
  fn join_is_node_hash() {
    let a = addr(b"a");
    let b = addr(b"b");
    assert_eq!(merkle_join(&a, &b), node_hash(&a, &b));
  }

  #[test]
  fn join_non_commutative() {
    let a = addr(b"a");
    let b = addr(b"b");
    assert_ne!(merkle_join(&a, &b), merkle_join(&b, &a));
  }

  #[test]
  fn join_canonical_inequal() {
    // Building a free-form tree by joining two canonical subtrees over
    // {a, b} and {c} produces a different root than the canonical tree
    // over {a, b, c} — and that's fine. Same leaf set, different
    // protocol-level claims.
    let a = addr(b"a");
    let b = addr(b"b");
    let c = addr(b"c");
    let left = merkle_root_canonical(&[a.clone(), b.clone()]).unwrap();
    let right = merkle_root_canonical(std::slice::from_ref(&c)).unwrap();
    let joined = merkle_join(&left, &right);
    let canonical = merkle_root_canonical(&[a, b, c]).unwrap();
    assert_ne!(joined, canonical);
  }

  #[test]
  fn join_composes_membership() {
    // After joining two canonical subtrees, leaves on each side are
    // still provable by appending the join-step sibling to their
    // sub-proofs.
    let a = addr(b"a");
    let b = addr(b"b");
    let c = addr(b"c");
    let left_leaves = vec![a.clone(), b.clone()];
    let right_leaves = vec![c.clone()];
    let left_root = merkle_root_canonical(&left_leaves).unwrap();
    let right_root = merkle_root_canonical(&right_leaves).unwrap();
    let joined = merkle_join(&left_root, &right_root);

    // Prove `a` is in the joined tree: sub-proof through left subtree,
    // then sibling = right_root (on the right), so is_left = false.
    let mut path = merkle_proof_canonical(&left_leaves, &a).unwrap();
    path.push((right_root.clone(), false));
    assert!(verify_merkle_proof(&joined, &a, &path));

    // Prove `c` is in the joined tree: empty sub-proof (single-leaf
    // right subtree), then sibling = left_root on the left.
    let mut path = merkle_proof_canonical(&right_leaves, &c).unwrap();
    path.push((left_root, true));
    assert!(verify_merkle_proof(&joined, &c, &path));
  }

  // ---------- Membership ----------

  #[test]
  fn proof_single_leaf() {
    let a = addr(b"only");
    let root = merkle_root_canonical(std::slice::from_ref(&a)).unwrap();
    let path = merkle_proof_canonical(std::slice::from_ref(&a), &a).unwrap();
    assert!(path.is_empty());
    assert!(verify_merkle_proof(&root, &a, &path));
  }

  #[test]
  fn proof_two_leaves() {
    let a = addr(b"a");
    let b = addr(b"b");
    let leaves = vec![a.clone(), b.clone()];
    let root = merkle_root_canonical(&leaves).unwrap();
    let path_a = merkle_proof_canonical(&leaves, &a).unwrap();
    let path_b = merkle_proof_canonical(&leaves, &b).unwrap();
    assert!(verify_merkle_proof(&root, &a, &path_a));
    assert!(verify_merkle_proof(&root, &b, &path_b));
  }

  #[test]
  fn proof_three_leaves_odd_padding() {
    let a = addr(b"a");
    let b = addr(b"b");
    let c = addr(b"c");
    let leaves = vec![a.clone(), b.clone(), c.clone()];
    let root = merkle_root_canonical(&leaves).unwrap();
    for leaf in &leaves {
      let path = merkle_proof_canonical(&leaves, leaf).unwrap();
      assert!(verify_merkle_proof(&root, leaf, &path));
    }
  }

  #[test]
  fn proof_rejects_nonmember_direct() {
    let a = addr(b"a");
    let b = addr(b"b");
    let leaves = vec![a.clone(), b];
    let x = addr(b"x");
    assert!(merkle_proof_canonical(&leaves, &x).is_none());
  }

  // ---------- Quickcheck properties ----------

  // Small helper: distinct random addresses.
  fn gen_distinct_addrs(g: &mut Gen, n: usize) -> Vec<Address> {
    let mut seen: std::collections::HashSet<Address> =
      std::collections::HashSet::new();
    while seen.len() < n {
      seen.insert(Address::arbitrary(g));
    }
    seen.into_iter().collect()
  }

  #[quickcheck]
  fn prop_proof_roundtrip_canonical(seed: u8) -> bool {
    let mut g = Gen::new(16);
    // 1..=12 leaves
    let n = ((seed as usize) % 12) + 1;
    let leaves = gen_distinct_addrs(&mut g, n);
    let root = merkle_root_canonical(&leaves).unwrap();
    leaves.iter().all(|leaf| {
      let path = merkle_proof_canonical(&leaves, leaf).unwrap();
      verify_merkle_proof(&root, leaf, &path)
    })
  }

  #[quickcheck]
  fn prop_proof_rejects_nonmember(seed: u8) -> bool {
    let mut g = Gen::new(16);
    let n = ((seed as usize) % 10) + 1;
    let leaves = gen_distinct_addrs(&mut g, n);
    let root = merkle_root_canonical(&leaves).unwrap();
    // Fresh address: definitely not in `leaves`.
    let mut nonmember = Address::arbitrary(&mut g);
    while leaves.contains(&nonmember) {
      nonmember = Address::arbitrary(&mut g);
    }
    // Any path the prover *could* try for a nonmember fails. Quick
    // check: take a real member's path and try to verify it against
    // the nonmember leaf.
    let real_leaf = &leaves[0];
    let real_path = merkle_proof_canonical(&leaves, real_leaf).unwrap();
    !verify_merkle_proof(&root, &nonmember, &real_path)
  }

  #[quickcheck]
  fn prop_proof_roundtrip_joined(seed: u8) -> bool {
    let mut g = Gen::new(16);
    let n_left = ((seed as usize) % 5) + 1;
    let n_right = (((seed >> 4) as usize) % 5) + 1;
    let left_leaves = gen_distinct_addrs(&mut g, n_left);
    let right_leaves = gen_distinct_addrs(&mut g, n_right);
    let left_root = merkle_root_canonical(&left_leaves).unwrap();
    let right_root = merkle_root_canonical(&right_leaves).unwrap();
    let joined = merkle_join(&left_root, &right_root);

    let left_ok = left_leaves.iter().all(|leaf| {
      let mut path = merkle_proof_canonical(&left_leaves, leaf).unwrap();
      path.push((right_root.clone(), false));
      verify_merkle_proof(&joined, leaf, &path)
    });
    let right_ok = right_leaves.iter().all(|leaf| {
      let mut path = merkle_proof_canonical(&right_leaves, leaf).unwrap();
      path.push((left_root.clone(), true));
      verify_merkle_proof(&joined, leaf, &path)
    });
    left_ok && right_ok
  }
}
