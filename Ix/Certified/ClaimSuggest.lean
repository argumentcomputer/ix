/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certificate.Claims
import Ix.Certified.ClaimAccept
import Ix.Certified.ModelHints

/-! Untrusted witness construction. The acceptance path imports none of
these search functions and checks the public envelope and complete returned
witness again. Trees are hints whose public Merkle roots are checked. -/

namespace Ix.Certified

open Ix.Theory Ix.Theory.Certified Ix.Theory.Model

structure LeafHint where
  claim : Ix.Claim
  subjects : Option ByteArray
  frontierTree : Option ByteArray

structure LogicalHint where
  selection : InputSelection
  leaves : List LeafHint
  subjects : Option ByteArray
  members : Option ByteArray
  frontierTree : Option ByteArray
  axiomTree : Option ByteArray
  models : List ModelHint := []

/-- Header dependency order is independent of the Merkle tree's leaf order. -/
def frontierOrder? (fuel : Nat) (signature : PrimitiveSignature Address) (store : Store Address)
    (allowed pending visited active : List (ConstRef Address)) : Option (List (ConstRef Address)) :=
  match fuel, pending with
  | _, [] => some visited
  | 0, _ :: _ => none
  | fuel + 1, ref :: rest =>
    if ref = signature.falseType ∨ ref = signature.falseElim ∨ ref ∈ visited then
      frontierOrder? fuel signature store allowed rest visited active
    else if ref ∈ active ∨ ref ∉ allowed then none
    else do
      let type ← store.type ref
      let visited ← frontierOrder? fuel signature store allowed type.refs visited (ref :: active)
      frontierOrder? fuel signature store allowed rest (visited ++ [ref]) active

def frontierSuggestion? (fuel : Nat) (signature : PrimitiveSignature Address) (store : Store Address)
    (objects : Objects) (root : Option Address) (bytes : Option ByteArray) :
    Option (List (ConstRef Address) × List (FrontierWitness Address)) := do
  let opening ← readOptionalTree? fuel root bytes
  let refs ← opening.leaves.flatMapM (subjectReferences? objects)
  let ordered ← frontierOrder? fuel signature store refs refs [] []
  let (_, witnesses) ← Certificate.frontierWitnesses? fuel store signature.environment ordered
  return (ordered, witnesses)

def leafSuggestion? (fuel : Nat) (signature : PrimitiveSignature Address) (store : Store Address)
    (objects : Objects) (hint : LeafHint) (models : List (Certificate.Modeled.Candidate Address) := []) : Option LeafWitness := do
  let subjects ← readSubjectView? fuel hint.claim hint.subjects
  let refs ← subjects.addresses.flatMapM (subjectReferences? objects)
  let (frontier, _) ← frontierSuggestion? fuel signature store objects (claimFrontier hint.claim) hint.frontierTree
  let node ← Certificate.claimNode? fuel signature store frontier (ownedReferences signature refs) models
  return ⟨hint.claim, hint.subjects, hint.frontierTree, node.frontier, node.declarations⟩

def suggestLogical? (fuel : Nat) (source : Ixon.Env) (envelope : Envelope) (hint : LogicalHint) :
    Option LogicalWitness := do
  let (snapshot, _) ← readSnapshot? fuel source hint.selection {}
  let signature ← readSignature? envelope.profile snapshot.decodedObjects
  let store ← readStore? fuel snapshot.decodedObjects snapshot.decodedNaturals
  let models ← modelCandidates? snapshot.decodedObjects store hint.models
  let leaves ← hint.leaves.mapM (fun leaf => leafSuggestion? fuel signature store snapshot.decodedObjects leaf models)
  let (_, frontier) ← frontierSuggestion? fuel signature store snapshot.decodedObjects
    (claimFrontier envelope.claim) hint.frontierTree
  return ⟨hint.selection, leaves, hint.subjects, hint.members, hint.frontierTree, frontier, hint.axiomTree⟩

end Ix.Certified
