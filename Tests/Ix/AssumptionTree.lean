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

set_option compiler.extract_closed false

private def addr (s : String) : Address := Address.blake3 s.toUTF8

/-! ## Canonical construction -/

private partial def hasPad : Ix.AssumptionTree → Bool
  | .padding => true
  | .leaf _ => false
  | .node l r => hasPad l || hasPad r

private def canonicalUnits : LSpec.Spec := do
  itBool "canonical of empty is none" ((Ix.AssumptionTree.canonical #[]) == none)
  itBool "canonical of single leaf"
    (let a := addr "a"; (Ix.AssumptionTree.canonical #[a]) == some (.leaf a))
  itBool "canonical of three leaves contains padding"
    (let a := addr "a"; let b := addr "b"; let c := addr "c"
     let t := (Ix.AssumptionTree.canonical #[a, b, c]).get!
     hasPad t)

/-! ## Root agreement with `merkleRootCanonical` -/

private def rootAgreementUnits : LSpec.Spec := do
  let mkLeaves (n : Nat) : Array Address :=
    Array.range n |>.map fun i => addr s!"leaf-{i}"
  let check (n : Nat) : Bool :=
    let leaves := mkLeaves n
    let t := (Ix.AssumptionTree.canonical leaves).get!
    some t.root == merkleRootCanonical leaves
  itBool "root matches merkleRootCanonical for n=1" (check 1)
  itBool "root matches merkleRootCanonical for n=2" (check 2)
  itBool "root matches merkleRootCanonical for n=3" (check 3)
  itBool "root matches merkleRootCanonical for n=4" (check 4)
  itBool "root matches merkleRootCanonical for n=5" (check 5)
  itBool "root matches merkleRootCanonical for n=7" (check 7)
  itBool "root matches merkleRootCanonical for n=8" (check 8)

/-! ## Join agreement -/

private def joinUnits : LSpec.Spec := do
  it "join root matches merkleJoin" do
    let a := addr "a"
    let b := addr "b"
    let l := (Ix.AssumptionTree.canonical #[a]).get!
    let r := (Ix.AssumptionTree.canonical #[b]).get!
    let joined := Ix.AssumptionTree.join l r
    expect (joined.root == merkleJoin l.root r.root)

/-! ## Leaves + contains -/

private def leavesUnits : LSpec.Spec := do
  it "leaves skip padding and yield sorted set" do
    let a := addr "a"
    let b := addr "b"
    let c := addr "c"
    let t := (Ix.AssumptionTree.canonical #[a, b, c]).get!
    let sorted := (#[a, b, c]).qsort fun a b => compare a b == .lt
    expect (t.leaves == sorted)
  it "contains true for members" do
    let a := addr "a"
    let b := addr "b"
    let c := addr "c"
    let t := (Ix.AssumptionTree.canonical #[a, b, c]).get!
    expect (t.contains a && t.contains b && t.contains c)
  it "contains false for nonmember" do
    let a := addr "a"
    let b := addr "b"
    let c := addr "c"
    let absent := addr "absent"
    let t := (Ix.AssumptionTree.canonical #[a, b, c]).get!
    expect (!t.contains absent)

/-! ## Merkle proofs -/

private def merkleProofUnits : LSpec.Spec := do
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
  itBool "single-leaf empty path verifies"
    (let a := addr "x"
     let t : Ix.AssumptionTree := .leaf a
     match t.merkleProof a with
     | some path => path.isEmpty && verifyMerkleProof t.root a path
     | none => false)
  itBool "all leaves prove for n=2" (checkAll 2)
  itBool "all leaves prove for n=3" (checkAll 3)
  itBool "all leaves prove for n=5" (checkAll 5)
  itBool "all leaves prove for n=8" (checkAll 8)
  itBool "nonmember returns none"
    (let leaves := mkLeaves 3
     let t := (Ix.AssumptionTree.canonical leaves).get!
     t.merkleProof (addr "absent") == none)

/-! ## Serialization -/

private def serdeRoundtrip (t : Ix.AssumptionTree) : Bool :=
  let bytes := Ix.AssumptionTree.ser t
  match runGet Ix.AssumptionTree.get bytes with
  | .ok t' => t == t'
  | .error _ => false

private def serdeUnits : LSpec.Spec := do
  let mkLeaf := fun () => Ix.AssumptionTree.leaf (addr "a")
  let mkPad := fun () => Ix.AssumptionTree.padding
  let mkNode := fun () =>
    Ix.AssumptionTree.node (Ix.AssumptionTree.leaf (addr "a")) (Ix.AssumptionTree.leaf (addr "b"))
  let mkCanon := fun () => (Ix.AssumptionTree.canonical #[addr "a", addr "b", addr "c"]).get!
  itBool "outer tag byte is 0xE2 (Leaf)" ((Ix.AssumptionTree.ser (mkLeaf ())).data[0]! == 0xE2)
  itBool "outer tag byte is 0xE2 (Padding)" ((Ix.AssumptionTree.ser (mkPad ())).data[0]! == 0xE2)
  itBool "outer tag byte is 0xE2 (Node)" ((Ix.AssumptionTree.ser (mkNode ())).data[0]! == 0xE2)
  itBool "Leaf body tag is 0x00" ((Ix.AssumptionTree.ser (mkLeaf ())).data[1]! == 0x00)
  itBool "Padding body tag is 0x01" ((Ix.AssumptionTree.ser (mkPad ())).data[1]! == 0x01)
  itBool "Node body tag is 0x02" ((Ix.AssumptionTree.ser (mkNode ())).data[1]! == 0x02)
  itBool "Leaf total bytes" ((Ix.AssumptionTree.ser (mkLeaf ())).size == 1 + 1 + 32)
  itBool "Padding total bytes" ((Ix.AssumptionTree.ser (mkPad ())).size == 2)
  itBool "Node total bytes" ((Ix.AssumptionTree.ser (mkNode ())).size == 1 + 1 + (1 + 32) + (1 + 32))
  -- Roundtrips
  itBool "roundtrip Leaf" (serdeRoundtrip (mkLeaf ()))
  itBool "roundtrip Padding" (serdeRoundtrip (mkPad ()))
  itBool "roundtrip Node simple" (serdeRoundtrip (mkNode ()))
  itBool "roundtrip canonical n=3" (serdeRoundtrip (mkCanon ()))

/-! ## Suite -/

public def Tests.AssumptionTree.suite : LSpec.Spec := do
  canonicalUnits
  rootAgreementUnits
  joinUnits
  leavesUnits
  merkleProofUnits
  serdeUnits
