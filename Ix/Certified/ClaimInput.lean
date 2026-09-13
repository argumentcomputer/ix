/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.Envelope
import Ix.Theory.Certified.ClaimComposition

namespace Ix.Certified

open Ix.Theory Ix.Theory.Certified Ix.Theory.Model

def sameMembers {α : Type _} [DecidableEq α] (a b : List α) : Bool :=
  a.all (b.contains ·) && b.all (a.contains ·)

theorem sameMembers_iff {α : Type _} [DecidableEq α] {a b : List α} :
    sameMembers a b = true ↔ ∀ x, x ∈ a ↔ x ∈ b := by
  simp only [sameMembers, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  exact ⟨fun h x => ⟨h.1 x, h.2 x⟩, fun h => ⟨fun x => (h x).mp, fun x => (h x).mpr⟩⟩

def claimFrontier : Ix.Claim → Option Address
  | .check _ frontier | .checkEnv _ frontier | .catalog _ _ frontier | .eval _ _ frontier => frontier
  | _ => none

structure SubjectView (fuel : Nat) (claim : Ix.Claim) (bytes : Option ByteArray) where
  addresses : List Address
  meaning : match claim with
    | .check address _ => bytes = none ∧ addresses = [address]
    | .checkEnv root _ => ∃ raw, bytes = some raw ∧
        ∃ opening : TreeOpening fuel root raw, treeLeaves opening.tree = addresses
    | _ => False

def readSubjectView? (fuel : Nat) (claim : Ix.Claim) (bytes : Option ByteArray) :
    Option (SubjectView fuel claim bytes) :=
  match claim, bytes with
  | .check address _, none => some ⟨[address], rfl, rfl⟩
  | .checkEnv root _, some raw => do
    let opening ← readTree? fuel root raw
    return ⟨treeLeaves opening.tree, raw, rfl, opening, rfl⟩
  | _, _ => none

def ownedReferences (signature : PrimitiveSignature Address) (refs : List (ConstRef Address)) :
    List (ConstRef Address) :=
  (refs.filter fun ref => ref != signature.falseType && ref != signature.falseElim).eraseDups

theorem mem_ownedReferences {signature : PrimitiveSignature Address} {refs : List (ConstRef Address)}
    {ref : ConstRef Address} : ref ∈ ownedReferences signature refs ↔
      ref ∈ refs ∧ ref ≠ signature.falseType ∧ ref ≠ signature.falseElim := by
  simp [ownedReferences]

structure LeafWitness where
  claim : Ix.Claim
  subjects : Option ByteArray
  frontierTree : Option ByteArray
  frontier : List (FrontierWitness Address)
  declarations : List (DeclarationWitness Address)

structure PreparedLeaf (fuel : Nat) (objects : Objects) (witness : LeafWitness) where
  subjectView : SubjectView fuel witness.claim witness.subjects
  subjectRefs : List (ConstRef Address)
  subjectsResolved : subjectView.addresses.flatMapM (subjectReferences? objects) = some subjectRefs
  frontierView : OptionalTreeOpening fuel (claimFrontier witness.claim) witness.frontierTree
  frontierRefs : List (ConstRef Address)
  frontierResolved : frontierView.leaves.flatMapM (subjectReferences? objects) = some frontierRefs
  frontierExact : ∀ ref, ref ∈ witness.frontier.map (·.ref) ↔ ref ∈ frontierRefs

def prepareLeaf? (fuel : Nat) (objects : Objects) (witness : LeafWitness) :
    Option (PreparedLeaf fuel objects witness) := do
  let subjectView ← readSubjectView? fuel witness.claim witness.subjects
  match hs : subjectView.addresses.flatMapM (subjectReferences? objects) with
  | none => none
  | some subjectRefs => do
    let frontierView ← readOptionalTree? fuel (claimFrontier witness.claim) witness.frontierTree
    match hf : frontierView.leaves.flatMapM (subjectReferences? objects) with
    | none => none
    | some frontierRefs =>
      if he : sameMembers (witness.frontier.map (·.ref)) frontierRefs = true then
        some ⟨subjectView, subjectRefs, hs, frontierView, frontierRefs, hf, sameMembers_iff.mp he⟩
      else none

def PreparedLeaf.node {fuel : Nat} {objects : Objects} {witness : LeafWitness}
    (leaf : PreparedLeaf fuel objects witness) (signature : PrimitiveSignature Address) : ClaimNode Address :=
  ⟨ownedReferences signature leaf.subjectRefs, witness.frontier, witness.declarations⟩

structure LeafInput (fuel : Nat) (objects : Objects) where
  witness : LeafWitness
  prepared : PreparedLeaf fuel objects witness

def readLeafInput? (fuel : Nat) (objects : Objects) (witness : LeafWitness) :
    Option (LeafInput fuel objects) := do
  let prepared ← prepareLeaf? fuel objects witness
  return ⟨witness, prepared⟩

def leafAddresses {fuel : Nat} {objects : Objects} (leaves : List (LeafInput fuel objects)) : List Address :=
  leaves.flatMap (·.prepared.subjectView.addresses)

def environmentRoot? : Ix.Claim → Option Address
  | .checkEnv root _ => some root
  | _ => none

structure ContentView (fuel : Nat) (claim : Ix.Claim) (subjects members : Option ByteArray)
    {objects : Objects} (leaves : List (LeafInput fuel objects)) where
  addresses : List Address
  exactLeaves : ∀ address, address ∈ addresses ↔ address ∈ leafAddresses leaves
  meaning : match claim with
    | .check address _ => subjects = none ∧ members = none ∧ addresses = [address]
    | .checkEnv root _ => members = none ∧ ∃ raw, subjects = some raw ∧
        ∃ opening : TreeOpening fuel root raw, treeLeaves opening.tree = addresses
    | .catalog memberRoot contentRoot _ => ∃ rawContent rawMembers,
        subjects = some rawContent ∧ members = some rawMembers ∧
        ∃ content : TreeOpening fuel contentRoot rawContent,
        ∃ membership : TreeOpening fuel memberRoot rawMembers,
          treeLeaves content.tree = addresses ∧
          ∃ roots, leaves.mapM (fun leaf => environmentRoot? leaf.witness.claim) = some roots ∧
            ∀ root, root ∈ treeLeaves membership.tree ↔ root ∈ roots
    | _ => False

def readContentView? (fuel : Nat) (claim : Ix.Claim) (subjects members : Option ByteArray)
    {objects : Objects} (leaves : List (LeafInput fuel objects)) :
    Option (ContentView fuel claim subjects members leaves) :=
  match claim, subjects, members with
  | .check address _, none, none =>
    if he : sameMembers [address] (leafAddresses leaves) = true then
      some ⟨[address], sameMembers_iff.mp he, rfl, rfl, rfl⟩
    else none
  | .checkEnv root _, some raw, none => do
    let opening ← readTree? fuel root raw
    if he : sameMembers (treeLeaves opening.tree) (leafAddresses leaves) = true then
      some ⟨treeLeaves opening.tree, sameMembers_iff.mp he, rfl, raw, rfl, opening, rfl⟩
    else none
  | .catalog memberRoot contentRoot _, some rawContent, some rawMembers => do
    let content ← readTree? fuel contentRoot rawContent
    let membership ← readTree? fuel memberRoot rawMembers
    match hr : leaves.mapM (fun leaf => environmentRoot? leaf.witness.claim) with
    | none => none
    | some roots =>
      if he : sameMembers (treeLeaves content.tree) (leafAddresses leaves) = true then
        if hm : sameMembers (treeLeaves membership.tree) roots = true then
          some ⟨treeLeaves content.tree, sameMembers_iff.mp he, rawContent, rawMembers, rfl, rfl,
            content, membership, rfl, roots, hr, sameMembers_iff.mp hm⟩
        else none
      else none
  | _, _, _ => none

end Ix.Certified
