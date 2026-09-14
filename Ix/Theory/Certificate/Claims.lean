/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certificate.Build
import Ix.Theory.Certified.Claims

namespace Ix.Theory.Certificate

open Model Certified

universe u
variable {β : Type u} [DecidableEq β] [Hints β]

/-- Untrusted construction of an ordered opaque frontier. The claim checker
independently re-reads each source type and verifies its formation. -/
def frontierWitnesses? (fuel : Nat) (store : Store β) (entries : Environment β) :
    List (ConstRef β) → Option (Environment β × List (FrontierWitness β))
  | [] => some (entries, [])
  | ref :: refs => match store.uvars ref, store.type ref with
    | some universes, some type => do
      let inferred ← inferSource? fuel universes entries [] type
      let .sort level := inferred.type | none
      let witness : FrontierWitness β := ⟨ref, annotations inferred.expression, level, inferred.witness⟩
      let reading ← readFrontierHeader? store witness
      let (entries', rest) ← frontierWitnesses? fuel store
        (entries.insert ref reading.header.entry) refs
      return (entries', witness :: rest)
    | _, _ => none

def claimNode? (fuel : Nat) (signature : PrimitiveSignature β) (store : Store β)
    (frontier subjects : List (ConstRef β)) (models : List (Modeled.Candidate β) := []) : Option (ClaimNode β) :=
  letI : Hints β := ⟨signature.natType⟩
  do
    let (entries, dependencies) ← frontierWitnesses? fuel store signature.environment frontier
    let (_, order) ← dependencyOrder? fuel signature store subjects frontier [] [] models
    let (_, declarations) ← declarationWitnesses? fuel store entries order
    return ⟨subjects, dependencies, declarations⟩

def batchFrontier? (fuel : Nat) (signature : PrimitiveSignature β) (store : Store β)
    (nodes : List (ClaimNode β)) : Option (List (FrontierWitness β)) :=
  letI : Hints β := ⟨signature.natType⟩
  do
    let subjects := nodes.flatMap (·.subjects)
    let refs := (nodes.flatMap fun node => node.frontier.map (·.ref)).filter
      (fun ref => !subjects.contains ref) |>.eraseDups
    return (← frontierWitnesses? fuel store signature.environment refs).2

end Ix.Theory.Certificate
