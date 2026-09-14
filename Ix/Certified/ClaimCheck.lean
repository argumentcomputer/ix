/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.ClaimInput

namespace Ix.Certified

open Ix.Theory Ix.Theory.Certified Ix.Theory.Model Ix.Theory.Model.SetTheory

universe v

structure LogicalWitness where
  selection : InputSelection
  leaves : List LeafWitness
  subjects : Option ByteArray
  members : Option ByteArray
  frontierTree : Option ByteArray
  frontier : List (FrontierWitness Address)
  axiomTree : Option ByteArray

structure LogicalChecking {source : Ixon.Env} (snapshot : SourceSnapshot source)
    (fuel : Nat) (envelope : Envelope) (witness : LogicalWitness) where
  uniqueSource : ((snapshot.blobs ++ snapshot.literalBlobs).map Prod.fst).Nodup
  signature : PrimitiveSignature Address
  signatureReading : readSignature? envelope.profile snapshot.decodedObjects = some signature
  store : Store Address
  storeReading : readStore? fuel snapshot.decodedObjects snapshot.decodedNaturals = some store
  leaves : List (LeafInput fuel snapshot.decodedObjects)
  leavesReading : witness.leaves.mapM (readLeafInput? fuel snapshot.decodedObjects) = some leaves
  content : ContentView fuel envelope.claim witness.subjects witness.members leaves
  subjects : List (ConstRef Address)
  subjectsReading : content.addresses.flatMapM (subjectReferences? snapshot.decodedObjects) = some subjects
  frontier : OptionalTreeOpening fuel (claimFrontier envelope.claim) witness.frontierTree
  frontierRefs : List (ConstRef Address)
  frontierReading : frontier.leaves.flatMapM (subjectReferences? snapshot.decodedObjects) = some frontierRefs
  batch : CheckedBatch.{0,v} fuel signature store (leaves.map (fun leaf => leaf.prepared.node signature))
  batchChecking : checkBatch? fuel signature store witness.frontier
    (leaves.map (fun leaf => leaf.prepared.node signature)) = some batch
  exactSubjects : ∀ ref, ref ∈ nodeSubjects batch.nodes ↔ ref ∈ ownedReferences signature subjects
  exactFrontier : ∀ ref, ref ∈ batch.receipt.frontier.refs ↔ ref ∈ frontierRefs
  axioms : OptionalTreeOpening fuel envelope.logicalAxioms witness.axiomTree
  axiomRefs : List (ConstRef Address)
  axiomsReading : axioms.leaves.flatMapM (subjectReferences? snapshot.decodedObjects) = some axiomRefs
  exactAxioms : ∀ ref, ref ∈ batch.logicalUses ↔ ref ∈ axiomRefs

def checkLogicalSnapshot? {source : Ixon.Env} (snapshot : SourceSnapshot source)
    (fuel : Nat) (envelope : Envelope) (witness : LogicalWitness) :
    Option (LogicalChecking.{v} snapshot fuel envelope witness) :=
  if hu : ((snapshot.blobs ++ snapshot.literalBlobs).map Prod.fst).Nodup then
    match hs : readSignature? envelope.profile snapshot.decodedObjects with
    | none => none
    | some signature =>
      match ht : readStore? fuel snapshot.decodedObjects snapshot.decodedNaturals with
      | none => none
      | some store =>
        match hl : witness.leaves.mapM (readLeafInput? fuel snapshot.decodedObjects) with
        | none => none
        | some leaves => do
          let content ← readContentView? fuel envelope.claim witness.subjects witness.members leaves
          match htargets : content.addresses.flatMapM (subjectReferences? snapshot.decodedObjects) with
          | none => none
          | some subjects => do
            let frontier ← readOptionalTree? fuel (claimFrontier envelope.claim) witness.frontierTree
            match hfrontier : frontier.leaves.flatMapM (subjectReferences? snapshot.decodedObjects) with
            | none => none
            | some frontierRefs =>
              match hc : checkBatch?.{0,v} fuel signature store witness.frontier
                  (leaves.map (fun leaf => leaf.prepared.node signature)) with
              | none => none
              | some batch =>
                if hsubjects : sameMembers (nodeSubjects batch.nodes) (ownedReferences signature subjects) = true then
                  if hf : sameMembers batch.receipt.frontier.refs frontierRefs = true then do
                    let axioms ← readOptionalTree? fuel envelope.logicalAxioms witness.axiomTree
                    match haxioms : axioms.leaves.flatMapM (subjectReferences? snapshot.decodedObjects) with
                    | none => none
                    | some axiomRefs =>
                      if ha : sameMembers batch.logicalUses axiomRefs = true then
                        some ⟨hu, signature, hs, store, ht, leaves, hl, content, subjects, htargets,
                          frontier, frontierRefs, hfrontier, batch, hc, sameMembers_iff.mp hsubjects,
                          sameMembers_iff.mp hf, axioms, axiomRefs, haxioms, sameMembers_iff.mp ha⟩
                      else none
                  else none
                else none
  else none

structure LogicalReceipt (source : Ixon.Env) (fuel : Nat) (envelope : Envelope) (witness : LogicalWitness) where
  snapshot : SourceSnapshot source
  checked : LogicalChecking.{v} snapshot fuel envelope witness
  supported : envelope.protocol = Protocol.current

/-- Every cache hit revalidates the actual complete claim. Only authenticated
data is reused; claim, policy, frontier and model checks run on every request. -/
def checkLogicalSource? (fuel : Nat) (source : Ixon.Env) (envelope : Envelope) (witness : LogicalWitness) :
    Read source (LogicalReceipt.{v} source fuel envelope witness) :=
  if hp : envelope.protocol = Protocol.current then do
    let snapshot ← readSnapshot? fuel source witness.selection
    match checkLogicalSnapshot?.{v} snapshot fuel envelope witness with
    | none => failure
    | some checked => return ⟨snapshot, checked, hp⟩
  else failure

end Ix.Certified
