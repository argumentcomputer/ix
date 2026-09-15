/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.SourceMeaning
import Ix.AssumptionTree

/-! Total checking of Ix's existing Merkle-tree wire representation. The
public slot determines whether leaves mean constant addresses, environment
roots, or logical-axiom addresses. Padding is never a declaration. -/

namespace Ix.Certified

instance addressLawfulBEq : LawfulBEq Address where
  eq_of_beq := by
    intro a b h
    change (a.hash.data == b.hash.data) = true at h
    cases a
    cases b
    exact congrArg Address.mk (congrArg ByteArray.mk (eq_of_beq h))
  rfl := by
    intro a
    change (a.hash.data == a.hash.data) = true
    exact beq_self_eq_true _

def treeRoot : AssumptionTree → Address
  | .leaf address => Merkle.leafHash address
  | .padding => Merkle.zeroAddress
  | .node left right => Merkle.nodeHash (treeRoot left) (treeRoot right)

def treeLeaves : AssumptionTree → List Address
  | .leaf address => [address]
  | .padding => []
  | .node left right => treeLeaves left ++ treeLeaves right

def putTreeBody : AssumptionTree → Ixon.PutM Unit
  | .leaf address => do Ixon.putU8 0; Ixon.Serialize.put address
  | .padding => Ixon.putU8 1
  | .node left right => do
    Ixon.putU8 2
    putTreeBody left
    putTreeBody right

def treeBytes (tree : AssumptionTree) : ByteArray := Ixon.runPut do
  Ixon.putTag4 ⟨AssumptionTree.FLAG, AssumptionTree.VARIANT⟩
  putTreeBody tree

def getTreeBody : Nat → Ixon.GetM AssumptionTree
  | 0 => throw "certified tree depth limit"
  | fuel + 1 => do
    match ← Ixon.getU8 with
    | 0 => return .leaf (← Ixon.Serialize.get)
    | 1 => return .padding
    | 2 => return .node (← getTreeBody fuel) (← getTreeBody fuel)
    | _ => throw "invalid certified tree node"

def getTree (fuel : Nat) : Ixon.GetM AssumptionTree := do
  let tag ← Ixon.getTag4
  if tag.flag != AssumptionTree.FLAG || tag.size != AssumptionTree.VARIANT then
    throw "invalid certified tree tag"
  getTreeBody fuel

structure TreeOpening (fuel : Nat) (root : Address) (bytes : ByteArray) where
  tree : AssumptionTree
  parsing : Ixon.runGetExact (getTree fuel) bytes = .ok tree
  canonical : treeBytes tree = bytes
  rootBound : treeRoot tree = root
  addresses : ∀ address ∈ treeLeaves tree, address.hash.size = 32

def readTree? (fuel : Nat) (root : Address) (bytes : ByteArray) :
    Option (TreeOpening fuel root bytes) :=
  match hp : Ixon.runGetExact (getTree fuel) bytes with
  | .error _ => none
  | .ok tree =>
    if hc : treeBytes tree = bytes then
      if hr : treeRoot tree = root then
        if ha : (treeLeaves tree).all (fun address => address.hash.size == 32) = true then
          some ⟨tree, hp, hc, hr, by simpa using List.all_eq_true.mp ha⟩
        else none
      else none
    else none

structure OptionalTreeOpening (fuel : Nat) (root : Option Address) (bytes : Option ByteArray) where
  leaves : List Address
  evidence : match root, bytes with
    | none, none => leaves = []
    | some root, some bytes => ∃ opening : TreeOpening fuel root bytes, treeLeaves opening.tree = leaves
    | _, _ => False

def readOptionalTree? (fuel : Nat) (root : Option Address) (bytes : Option ByteArray) :
    Option (OptionalTreeOpening fuel root bytes) :=
  match root, bytes with
  | none, none => some ⟨[], rfl⟩
  | some root, some bytes => do
    let opening ← readTree? fuel root bytes
    return ⟨treeLeaves opening.tree, ⟨opening, rfl⟩⟩
  | _, _ => none

def TreeMembership (root target : Address) : Prop :=
  ∃ tree, treeRoot tree = root ∧ target ∈ treeLeaves tree ∧
    ∀ address ∈ treeLeaves tree, address.hash.size = 32

/-- Membership is a structural assertion only. No environment or typing
judgment occurs in its conclusion. -/
theorem TreeOpening.membership (opening : TreeOpening fuel root bytes) {target : Address}
    (h : target ∈ treeLeaves opening.tree) : TreeMembership root target :=
  ⟨opening.tree, opening.rootBound, h, opening.addresses⟩

theorem treeLeaves_join (left right : AssumptionTree) (address : Address) :
    address ∈ treeLeaves (.node left right) ↔ address ∈ treeLeaves left ∨ address ∈ treeLeaves right :=
  List.mem_append

theorem TreeOpening.unique {a b : TreeOpening fuel root bytes} : a.tree = b.tree :=
  Except.ok.inj (a.parsing.symm.trans b.parsing)

end Ix.Certified
