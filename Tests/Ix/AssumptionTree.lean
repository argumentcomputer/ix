/-
  Tests for `Ix.AssumptionTree`.
-/

module
public import Ix.AssumptionTree
public import LSpec

open LSpec
open Ix.AssumptionTree
open Ix.Merkle (merkleRootCanonical merkleJoin verifyMerkleProof)
open Ixon (runGet)

private def addr (s : String) : Address := Address.blake3 s.toUTF8

/-! ## Canonical construction -/

private partial def hasPad : Ix.AssumptionTree → Bool
  | .padding => true
  | .leaf _ => false
  | .node l r => hasPad l || hasPad r

private def canonicalUnits : TestSeq :=
  let a := addr "a"
  let b := addr "b"
  let c := addr "c"
  test "canonical of empty is none" ((Ix.AssumptionTree.canonical #[]) == none)
  ++ test "canonical of single leaf"
       ((Ix.AssumptionTree.canonical #[a]) == some (.leaf a))
  ++ test "canonical of three leaves contains padding"
       (let t := (Ix.AssumptionTree.canonical #[a, b, c]).get!
        hasPad t)

/-! ## Root agreement with `merkleRootCanonical` -/

private def rootAgreementUnits : TestSeq :=
  let mkLeaves (n : Nat) : Array Address :=
    Array.range n |>.map fun i => addr s!"leaf-{i}"
  let check (n : Nat) : Bool :=
    let leaves := mkLeaves n
    let t := (Ix.AssumptionTree.canonical leaves).get!
    some t.root == merkleRootCanonical leaves
  test "root matches merkleRootCanonical for n=1" (check 1)
  ++ test "root matches merkleRootCanonical for n=2" (check 2)
  ++ test "root matches merkleRootCanonical for n=3" (check 3)
  ++ test "root matches merkleRootCanonical for n=4" (check 4)
  ++ test "root matches merkleRootCanonical for n=5" (check 5)
  ++ test "root matches merkleRootCanonical for n=7" (check 7)
  ++ test "root matches merkleRootCanonical for n=8" (check 8)

/-! ## Join agreement -/

private def joinUnits : TestSeq :=
  let a := addr "a"
  let b := addr "b"
  let l := (Ix.AssumptionTree.canonical #[a]).get!
  let r := (Ix.AssumptionTree.canonical #[b]).get!
  let joined := Ix.AssumptionTree.join l r
  test "join root matches merkleJoin"
    (joined.root == merkleJoin l.root r.root)

/-! ## Leaves + contains -/

private def leavesUnits : TestSeq :=
  let a := addr "a"
  let b := addr "b"
  let c := addr "c"
  let absent := addr "absent"
  let t := (Ix.AssumptionTree.canonical #[a, b, c]).get!
  -- Sorted leaves.
  let sorted := (#[a, b, c]).qsort fun a b => compare a b == .lt
  test "leaves skip padding and yield sorted set"
    (t.leaves == sorted)
  ++ test "contains true for members"
       (t.contains a && t.contains b && t.contains c)
  ++ test "contains false for nonmember"
       (!t.contains absent)

/-! ## Merkle proofs -/

private def merkleProofUnits : TestSeq :=
  let mkLeaves (n : Nat) : Array Address :=
    Array.range n |>.map fun i => addr s!"leaf-{i}"
  let checkAll (n : Nat) : Bool :=
    let leaves := mkLeaves n
    let t := (Ix.AssumptionTree.canonical leaves).get!
    let root := t.root
    t.leaves.all fun leaf =>
      match t.merkleProof leaf with
      | none => false
      | some path => verifyMerkleProof root leaf path
  test "single-leaf empty path verifies"
    (let a := addr "x"
     let t : Ix.AssumptionTree := .leaf a
     let ok : Bool := match t.merkleProof a with
       | some path => path.isEmpty && verifyMerkleProof t.root a path
       | none => false
     ok)
  ++ test "all leaves prove for n=2" (checkAll 2)
  ++ test "all leaves prove for n=3" (checkAll 3)
  ++ test "all leaves prove for n=5" (checkAll 5)
  ++ test "all leaves prove for n=8" (checkAll 8)
  ++ test "nonmember returns none"
       (let leaves := mkLeaves 3
        let t := (Ix.AssumptionTree.canonical leaves).get!
        t.merkleProof (addr "absent") == none)

/-! ## Serialization -/

private def serdeRoundtrip (t : Ix.AssumptionTree) : Bool :=
  let bytes := Ix.AssumptionTree.ser t
  match runGet Ix.AssumptionTree.get bytes with
  | .ok t' => t == t'
  | .error _ => false

private def serdeUnits : TestSeq :=
  let a := addr "a"
  let b := addr "b"
  let leaf := Ix.AssumptionTree.leaf a
  let pad := Ix.AssumptionTree.padding
  let nodeLeaves :=
    Ix.AssumptionTree.node (Ix.AssumptionTree.leaf a) (Ix.AssumptionTree.leaf b)
  let canon := (Ix.AssumptionTree.canonical #[a, b, addr "c"]).get!
  -- Outer tag byte
  let leafBytes := Ix.AssumptionTree.ser leaf
  let padBytes  := Ix.AssumptionTree.ser pad
  let nodeBytes := Ix.AssumptionTree.ser nodeLeaves
  test "outer tag byte is 0xE2 (Leaf)"  (leafBytes.data[0]! == 0xE2)
  ++ test "outer tag byte is 0xE2 (Padding)" (padBytes.data[0]! == 0xE2)
  ++ test "outer tag byte is 0xE2 (Node)" (nodeBytes.data[0]! == 0xE2)
  ++ test "Leaf body tag is 0x00" (leafBytes.data[1]! == 0x00)
  ++ test "Padding body tag is 0x01" (padBytes.data[1]! == 0x01)
  ++ test "Node body tag is 0x02" (nodeBytes.data[1]! == 0x02)
  ++ test "Leaf total bytes" (leafBytes.size == 1 + 1 + 32)
  ++ test "Padding total bytes" (padBytes.size == 2)
  ++ test "Node total bytes" (nodeBytes.size == 1 + 1 + (1 + 32) + (1 + 32))
  -- Roundtrips
  ++ test "roundtrip Leaf" (serdeRoundtrip leaf)
  ++ test "roundtrip Padding" (serdeRoundtrip pad)
  ++ test "roundtrip Node simple" (serdeRoundtrip nodeLeaves)
  ++ test "roundtrip canonical n=3" (serdeRoundtrip canon)

/-! ## Suite -/

public def Tests.AssumptionTree.suite : List TestSeq := [
  canonicalUnits,
  rootAgreementUnits,
  joinUnits,
  leavesUnits,
  merkleProofUnits,
  serdeUnits,
]
