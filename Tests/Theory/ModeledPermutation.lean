/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Theory.Modeled

open Ix.Theory

namespace Tests.Theory.ModeledPermutation

open Ix.Theory.Model Ix.Theory.Certified Ix.Theory.Certificate Ix.Theory.Inductive
open Tests.Theory.Certified (primitives)
open Tests.Theory.Modeled (ref const)

set_option maxRecDepth 16384
set_option maxHeartbeats 32000000

def swap : ConstRef Nat → ConstRef Nat
  | .member 30 0 => .member 30 1
  | .member 30 1 => .member 30 0
  | .ctor 30 0 c => .ctor 30 1 c
  | .ctor 30 1 c => .ctor 30 0 c
  | .member 31 0 => .member 31 1
  | .member 31 1 => .member 31 0
  | ref => ref

def source : Block Nat := ModeledFixtures.permutedSource
def recursors : Block Nat := ModeledFixtures.permutedRecursors
def targets : List (ConstRef Nat) :=
  [ref 20, ref 40, ref 20, .ctor 20 0 0, .ctor 20 0 1, ref 43, ref 44]
def pairs : List (ConstRef Nat × ConstRef Nat) :=
  [ref 30, .ctor 30 0 0, ref 30 1, .ctor 30 1 0, .ctor 30 1 1, ref 31, ref 31 1].zip targets
def type (index : Nat) : VExpr Nat :=
  (((recursors.members[index]?).map Const.type).getD (.sort .zero)).mapRefs (Certificate.Modeled.target pairs)

/-- Reorder the complete motive/minor telescope when wrapping the earlier
models. Merely permuting addresses or constructor counts would not typecheck. -/
def body (index : Nat) : VExpr Nat := .lamN ((type index).telN 5)
  (.appN (const (if index = 0 then 42 else 41) 0 [.param 0]) [.bvar 3, .bvar 4, .bvar 1, .bvar 0, .bvar 2])
def block : Nat → Block Nat
  | 30 => source
  | 31 => recursors
  | 43 => ⟨[.defn 1 .definition (type 0) (body 0) .safe]⟩
  | 44 => ⟨[.defn 1 .definition (type 1) (body 1) .safe]⟩
  | n => Tests.Theory.Modeled.block n
def store : Store Nat where
  dom := List.range 45
  nodup := List.nodup_range
  blocks b := if b < 45 then some (block b) else none
  mem_dom b := by split <;> simp_all
def candidate : Certificate.Modeled.Candidate Nat := ⟨30, [ref 31, ref 31 1], targets, []⟩
def witnesses? := Certificate.storeWitness? 4000 primitives store [ref 31, ref 31 1] [candidate]
def accepted : Bool := witnesses?.any
  (acceptsStoreCertified.{0,0} 4000 primitives store [ref 30, ref 30 1, ref 31, ref 31 1])

#guard store.ctorRuleIndex? (.ctor 30 1 0) == some 1
#guard store.ctorRuleIndex? (.ctor 30 1 1) == some 2
#guard accepted
#guard (Certificate.storeWitness? 4000 primitives store [ref 31]
  [{ candidate with models := Tests.Theory.Modeled.modelTargets }]).isNone

def computed : VExpr Nat := .appN (const 31 1 [.succ .zero]) [
  .lam (const 30) (.sort .zero), .lam (const 30 1) (.sort .zero),
  .lam (const 30 1) (.lam (.sort .zero) (.bvar 0)), .bvar 1,
  .lam (const 30) (.lam (.sort .zero) (.bvar 0)),
  .app (.const (.ctor 30 1 1) [])
    (.app (.const (.ctor 30 0 0) []) (.const (.ctor 30 1 0) []))]
def input : ProofInput Nat := ⟨store, 0, Tests.Theory.Modeled.proof,
  .forallE (.sort .zero) (.forallE (.bvar 0) computed)⟩
def proofAccepted : Bool := (Certificate.proofWitness? 4000 primitives input [candidate]).any
  (acceptsCertified.{0,0} 4000 primitives input)
#guard proofAccepted

/-- Two fresh source auxiliary recursors may share one already checked model.
Their complete types and own rule statements still pass independent checks. -/
def mergedBlock : Nat → Block Nat
  | 45 => ⟨(Tests.Theory.Modeled.mutualRecursors.members[1]?).toList⟩
  | n => Tests.Theory.Modeled.block n
def mergedStore : Store Nat where
  dom := List.range 46
  nodup := List.nodup_range
  blocks b := if b < 46 then some (mergedBlock b) else none
  mem_dom b := by split <;> simp_all
def mergedCandidate : Certificate.Modeled.Candidate Nat :=
  ⟨30, [ref 31, ref 31 1, ref 45], Tests.Theory.Modeled.modelTargets ++ [ref 42], []⟩
def mergedWitnesses? := Certificate.storeWitness? 4000 primitives mergedStore [ref 31 1, ref 45] [mergedCandidate]
def mergedAccepted : Bool := mergedWitnesses?.any
  (acceptsStoreCertified.{0,0} 4000 primitives mergedStore [ref 31 1, ref 45])
#guard mergedAccepted
#guard (Certificate.storeWitness? 4000 primitives mergedStore [ref 45]
  [{ mergedCandidate with models := Tests.Theory.Modeled.modelTargets ++ [ref 41] }]).isNone

def mergedComputed : VExpr Nat := .appN (const 45 0 [.succ .zero]) [
  .lam (const 30) (.sort .zero), .lam (const 30 1) (.sort .zero), .bvar 1,
  .lam (const 30 1) (.lam (.sort .zero) (.bvar 0)),
  .lam (const 30) (.lam (.sort .zero) (.bvar 0)),
  .app (.const (.ctor 30 1 0) []) (.const (.ctor 30 0 0) [])]
def mergedInput : ProofInput Nat := ⟨mergedStore, 0, Tests.Theory.Modeled.proof,
  .forallE (.sort .zero) (.forallE (.bvar 0) mergedComputed)⟩
def mergedProofAccepted : Bool := (Certificate.proofWitness? 4000 primitives mergedInput [mergedCandidate]).any
  (acceptsCertified.{0,0} 4000 primitives mergedInput)
#guard mergedProofAccepted

end Tests.Theory.ModeledPermutation
