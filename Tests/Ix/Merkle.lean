/-
  Canonical-builder, free-form composition, and membership-proof tests
  for `Ix.Merkle`.
-/

module
public import Ix.Merkle
public import LSpec

open LSpec
open Ix.Merkle

set_option compiler.extract_closed false

private def addr (seed : String) : Address :=
  Address.blake3 seed.toUTF8

/-! ## Canonical builder -/

private def canonicalUnits : LSpec.Spec := do
  itBool "canonical_empty → none" (merkleRootCanonical #[] == none)
  itBool "canonical_single = leafHash"
    (let a := addr "a"; merkleRootCanonical #[a] == some (leafHash a))
  itBool "canonical_sort_invariant [a,b] = [b,a]"
    (let a := addr "a"; let b := addr "b"
     merkleRootCanonical #[a, b] == merkleRootCanonical #[b, a])
  itBool "canonical_dedup [a,a,b] = [a,b]"
    (let a := addr "a"; let b := addr "b"
     merkleRootCanonical #[a, a, b] == merkleRootCanonical #[a, b])
  itBool "canonical_distinguishes [a] ≠ [a,b]"
    (let a := addr "a"; let b := addr "b"
     !(merkleRootCanonical #[a] == merkleRootCanonical #[a, b]))
  itBool "canonical_three_leaves nonempty"
    (let a := addr "a"; let b := addr "b"; let c := addr "c"
     (merkleRootCanonical #[a, b, c]).isSome)
  itBool "canonical_no_malleability"
    -- [a, a] post-dedup is [a], yielding leafHash a.
    -- A two-leaf tree node_hash(leaf_hash(a), leaf_hash(a)) is different.
    (let a := addr "a"
     merkleRootCanonical #[a, a] == some (leafHash a)
       && !(merkleRootCanonical #[a, a] == some (nodeHash (leafHash a) (leafHash a))))

/-! ## Domain separation -/

private def domainSepUnits : LSpec.Spec := do
  itBool "leaf_vs_node_disjoint"
    (let a := addr "a"; !(leafHash a == nodeHash a zeroAddress))

/-! ## Free-form (merkleJoin) -/

private def joinUnits : LSpec.Spec := do
  itBool "join_is_node_hash"
    (let a := addr "a"; let b := addr "b"; merkleJoin a b == nodeHash a b)
  itBool "join_non_commutative"
    (let a := addr "a"; let b := addr "b"; !(merkleJoin a b == merkleJoin b a))
  itBool "join_canonical_inequal"
    -- Free-form tree of {a,b}{c} ≠ canonical tree of {a,b,c}.
    (let a := addr "a"; let b := addr "b"; let c := addr "c"
     let left  := (merkleRootCanonical #[a, b]).get!
     let right := (merkleRootCanonical #[c]).get!
     let joined := merkleJoin left right
     let canon := (merkleRootCanonical #[a, b, c]).get!
     !(joined == canon))

/-! ## Membership proofs -/

private def membershipUnits : LSpec.Spec := do
  itBool "proof_single_leaf empty path"
    (let a := addr "a"
     (merkleProofCanonical #[a] a).get!.isEmpty
      && verifyMerkleProof (leafHash a) a #[])
  itBool "proof_two_leaves roundtrip"
    (let a := addr "a"; let b := addr "b"
     let leaves := #[a, b]
     let root := (merkleRootCanonical leaves).get!
     let path_a := (merkleProofCanonical leaves a).get!
     let path_b := (merkleProofCanonical leaves b).get!
     verifyMerkleProof root a path_a && verifyMerkleProof root b path_b)
  itBool "proof_three_leaves all members"
    (let a := addr "a"; let b := addr "b"; let c := addr "c"
     let leaves := #[a, b, c]
     let root := (merkleRootCanonical leaves).get!
     let path_a := (merkleProofCanonical leaves a).get!
     let path_b := (merkleProofCanonical leaves b).get!
     let path_c := (merkleProofCanonical leaves c).get!
     verifyMerkleProof root a path_a
     && verifyMerkleProof root b path_b
     && verifyMerkleProof root c path_c)
  itBool "proof_rejects_nonmember_direct"
    (let a := addr "a"; let b := addr "b"
     (merkleProofCanonical #[a, b] (addr "x")) == none)

/-! ## Join composes membership -/

private def joinMembershipUnits : LSpec.Spec := do
  itBool "join_composes_left"
    (let a := addr "a"; let b := addr "b"; let c := addr "c"
     let leftLeaves := #[a, b]
     let rightLeaves := #[c]
     let leftRoot := (merkleRootCanonical leftLeaves).get!
     let rightRoot := (merkleRootCanonical rightLeaves).get!
     let joined := merkleJoin leftRoot rightRoot
     let path := (merkleProofCanonical leftLeaves a).get!
     verifyMerkleProof joined a (path.push (rightRoot, false)))
  itBool "join_composes_right"
    (let a := addr "a"; let b := addr "b"; let c := addr "c"
     let leftLeaves := #[a, b]
     let rightLeaves := #[c]
     let leftRoot := (merkleRootCanonical leftLeaves).get!
     let rightRoot := (merkleRootCanonical rightLeaves).get!
     let joined := merkleJoin leftRoot rightRoot
     let path := (merkleProofCanonical rightLeaves c).get!
     verifyMerkleProof joined c (path.push (leftRoot, true)))

/-! ## Suite -/

public def Tests.Merkle.suite : LSpec.Spec := do
  canonicalUnits
  domainSepUnits
  joinUnits
  membershipUnits
  joinMembershipUnits
