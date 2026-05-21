/-
  Canonical-builder, free-form composition, and membership-proof tests
  for `Ix.Merkle`.
-/

module
public import Ix.Merkle
public import LSpec

open LSpec
open Ix.Merkle

private def addr (seed : String) : Address :=
  Address.blake3 seed.toUTF8

/-! ## Canonical builder -/

private def canonicalUnits : TestSeq :=
  let a := addr "a"
  let b := addr "b"
  let c := addr "c"
  test "canonical_empty → none" (merkleRootCanonical #[] == none)
  ++ test "canonical_single = leafHash"
       (merkleRootCanonical #[a] == some (leafHash a))
  ++ test "canonical_sort_invariant [a,b] = [b,a]"
       (merkleRootCanonical #[a, b] == merkleRootCanonical #[b, a])
  ++ test "canonical_dedup [a,a,b] = [a,b]"
       (merkleRootCanonical #[a, a, b] == merkleRootCanonical #[a, b])
  ++ test "canonical_distinguishes [a] ≠ [a,b]"
       (!(merkleRootCanonical #[a] == merkleRootCanonical #[a, b]))
  ++ test "canonical_three_leaves nonempty"
       ((merkleRootCanonical #[a, b, c]).isSome)
  ++ test "canonical_no_malleability"
       -- [a, a] post-dedup is [a], yielding leafHash a.
       -- A two-leaf tree node_hash(leaf_hash(a), leaf_hash(a)) is different.
       (merkleRootCanonical #[a, a]
         == some (leafHash a)
         && !(merkleRootCanonical #[a, a]
              == some (nodeHash (leafHash a) (leafHash a))))

/-! ## Domain separation -/

private def domainSepUnits : TestSeq :=
  let a := addr "a"
  test "leaf_vs_node_disjoint"
    (!(leafHash a == nodeHash a zeroAddress))

/-! ## Free-form (merkleJoin) -/

private def joinUnits : TestSeq :=
  let a := addr "a"
  let b := addr "b"
  let c := addr "c"
  test "join_is_node_hash" (merkleJoin a b == nodeHash a b)
  ++ test "join_non_commutative" (!(merkleJoin a b == merkleJoin b a))
  ++ test "join_canonical_inequal"
       -- Free-form tree of {a,b}{c} ≠ canonical tree of {a,b,c}.
       (let left  := (merkleRootCanonical #[a, b]).get!
        let right := (merkleRootCanonical #[c]).get!
        let joined := merkleJoin left right
        let canon := (merkleRootCanonical #[a, b, c]).get!
        !(joined == canon))

/-! ## Membership proofs -/

private def membershipUnits : TestSeq :=
  let a := addr "a"
  let b := addr "b"
  let c := addr "c"
  let leaves := #[a, b, c]
  let root := (merkleRootCanonical leaves).get!
  test "proof_single_leaf empty path"
    ((merkleProofCanonical #[a] a).get!.isEmpty
     && verifyMerkleProof (leafHash a) a #[])
  ++ test "proof_two_leaves roundtrip"
       (let leaves := #[a, b]
        let root := (merkleRootCanonical leaves).get!
        let path_a := (merkleProofCanonical leaves a).get!
        let path_b := (merkleProofCanonical leaves b).get!
        verifyMerkleProof root a path_a && verifyMerkleProof root b path_b)
  ++ test "proof_three_leaves all members"
       (let path_a := (merkleProofCanonical leaves a).get!
        let path_b := (merkleProofCanonical leaves b).get!
        let path_c := (merkleProofCanonical leaves c).get!
        verifyMerkleProof root a path_a
        && verifyMerkleProof root b path_b
        && verifyMerkleProof root c path_c)
  ++ test "proof_rejects_nonmember_direct"
       ((merkleProofCanonical #[a, b] (addr "x")) == none)

/-! ## Join composes membership -/

private def joinMembershipUnits : TestSeq :=
  let a := addr "a"
  let b := addr "b"
  let c := addr "c"
  let leftLeaves := #[a, b]
  let rightLeaves := #[c]
  let leftRoot := (merkleRootCanonical leftLeaves).get!
  let rightRoot := (merkleRootCanonical rightLeaves).get!
  let joined := merkleJoin leftRoot rightRoot
  test "join_composes_left"
    (let path := (merkleProofCanonical leftLeaves a).get!
     verifyMerkleProof joined a (path.push (rightRoot, false)))
  ++ test "join_composes_right"
       (let path := (merkleProofCanonical rightLeaves c).get!
        verifyMerkleProof joined c (path.push (leftRoot, true)))

/-! ## Suite -/

public def Tests.Merkle.suite : List TestSeq := [
  canonicalUnits,
  domainSepUnits,
  joinUnits,
  membershipUnits,
  joinMembershipUnits,
]

