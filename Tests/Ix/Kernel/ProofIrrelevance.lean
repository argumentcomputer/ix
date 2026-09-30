/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Infer

/-! Proof irrelevance establishes proof values from inferred proposition types
or certified outer telescope annotations. It need not recursively compare the
types or recheck known proof arguments. The negative controls distinguish
proofs from propositions themselves and ordinary data. -/

open Ix.Kernel Ix.Kernel.Model

namespace Tests.Ix.Kernel.ProofIrrelevance

def entries : Environment Nat := fun _ => none

/-- `A B : Prop, a : A, b : B`; types are lifted by the ordinary context API. -/
def ctx : Context Nat :=
  let Γ : Context Nat := []
  let Γ := Context.push (.sort .zero) Γ
  let Γ := Context.push (.sort .zero) Γ
  let Γ := Context.push (.bvar 1) Γ
  Context.push (.bvar 1) Γ

def succeeds {α : Type} : Search α → Bool
  | .ok _ => true
  | .error _ => false

#guard succeeds (proofIrrelevance.{0,1} 100 entries ctx (.bvar 1) (.bvar 0))
#guard succeeds (proofIrrelevance.{0,1} 100 entries ctx (.bvar 0) (.bvar 1))
#guard succeeds (proofIrrelevance.{0,1} 100 entries ctx (.bvar 1) (.bvar 1))

-- `A` and `B` are proposition types, not proofs of propositions.
#guard !succeeds (proofIrrelevance.{0,1} 100 entries ctx (.bvar 3) (.bvar 2))
#guard !succeeds (proofIrrelevance.{0,1} 100 entries ctx (.bvar 1) (.bvar 2))
#guard !succeeds (proofIrrelevance.{0,1} 100 entries ctx (.bvar 2) (.bvar 1))
#guard !succeeds (proofIrrelevance.{0,1} 100 entries ctx (.bvar 0) (.sort .zero))

-- A missing local and exhausted search cannot supply a proof-irrelevance claim.
#guard !succeeds (proofIrrelevance.{0,1} 100 entries ctx (.bvar 0) (.bvar 4))
#guard !succeeds (proofIrrelevance.{0,1} 0 entries ctx (.bvar 1) (.bvar 0))

def prop : AExpr Nat := .sort .zero
def type0 : AExpr Nat := .sort (.succ .zero)
def proofType : AExpr Nat :=
  .forallE .always prop (.forallE .always (.bvar 0) (.bvar 1))
def proofLambda : AExpr Nat :=
  .lam .always prop (.lam .always (.bvar 0) (.bvar 0))

def proofEntries : Environment Nat := fun
  | .member 0 0 => some ⟨1, proofType, none, [], []⟩
  | .member 1 0 => some ⟨0, proofType, none, [], []⟩
  | .member 2 0 => some ⟨0, prop, none, [], []⟩
  | .member 3 0 => some ⟨0, .forallE .never type0 type0, none, [], []⟩
  | .member 4 0 => some ⟨1,
      .forallE (Certified.zeroCondition (.param 0)) (.sort (.param 0))
        (.forallE (Certified.zeroCondition (.param 0)) (.bvar 0) (.bvar 1)), none, [], []⟩
  | _ => none

def proofA : AExpr Nat := .const (.member 0 0) [.zero]
def proofB : AExpr Nat := .const (.member 1 0) []

-- Distinct proof constants and proof-valued lambdas are read before any
-- normalization or argument inference, including at small positive fuel.
#guard (inferA.{0,1} 64 entries [] proofLambda).isOk
#guard (quickProofIrrelevance.{0,1} proofEntries [] proofA proofB).isSome
#guard (quickProofIrrelevance.{0,1} proofEntries [] proofA proofLambda).isSome
#guard (isDefEq.{0,1} 1 proofEntries [] proofA proofB).isOk
#guard !(isDefEq.{0,1} 0 proofEntries [] proofA proofB).isOk
#guard (proofIrrelevance.{0,1} 1 proofEntries [] proofA proofB).isOk
#guard !(proofIrrelevance.{0,1} 0 proofEntries [] proofA proofB).isOk

-- Different arguments of a proof function need not be inferred by conversion.
-- Both applications here are nevertheless well typed by the ordinary checker.
def appliedProofA : AExpr Nat := .app proofA proofType
def appliedProofB : AExpr Nat := .app proofB (.forallE .always proofType proofType)
#guard (inferA.{0,1} 64 proofEntries [] appliedProofA).isOk
#guard (inferA.{0,1} 64 proofEntries [] appliedProofB).isOk
#guard (isDefEq.{0,1} 1 proofEntries [] appliedProofA appliedProofB).isOk

-- Only the instantiated outermost annotation is read. A polymorphic proof
-- cast can become proof-valued at zero, but not at a successor or free level.
#guard (proofValue.{0,1} proofEntries [] (.const (.member 4 0) [.zero])).isSome
#guard (isDefEq.{0,1} 1 proofEntries [] proofA (.const (.member 4 0) [.zero])).isOk
#guard (proofValue.{0,1} proofEntries [] (.const (.member 4 0) [.succ .zero])).isNone
#guard (proofValue.{0,1} proofEntries [] (.const (.member 4 0) [.param 0])).isNone
#guard (proofValue.{0,1} proofEntries [] (.const (.member 4 0) [])).isNone

-- Proposition expressions, proposition-valued constants and data-valued
-- functions do not license this shortcut.
#guard (proofValue.{0,1} proofEntries [] prop).isNone
#guard (proofValue.{0,1} proofEntries [] proofType).isNone
#guard (proofValue.{0,1} proofEntries [] (.const (.member 2 0) [])).isNone
#guard (proofValue.{0,1} proofEntries [] (.const (.member 3 0) [])).isNone
#guard (quickProofIrrelevance.{0,1} proofEntries [] proofA prop).isNone
#guard (quickProofIrrelevance.{0,1} proofEntries [] prop proofA).isNone

-- A missing constant or incorrect universe arity cannot produce a witness,
-- including underneath applications. Full inference still checks annotations.
#guard (proofValue.{0,1} proofEntries [] (.const (.member 0 0) [])).isNone
#guard (proofValue.{0,1} proofEntries [] (.const (.member 1 0) [.zero])).isNone
#guard (proofValue.{0,1} proofEntries [] (.app (.const (.member 0 0) []) prop)).isNone
#guard (proofValue.{0,1} proofEntries [] (.const (.member 5 0) [])).isNone
#guard !(inferA.{0,1} 64 entries [] (.lam .always type0 (.bvar 0))).isOk

-- The new shortcut preserves the existing total-work guard on isDefEqC.
#guard match isDefEqC.{0,1} 64 proofEntries [] proofA proofB (Cache.empty (fun _ => 0) 0) with
  | (.error .exhausted, _) => true
  | _ => false

def nestedProofType : Nat → AExpr Nat
  | 0 => proofType
  | n + 1 => .forallE .always proofType (nestedProofType n)

def largeProof : AExpr Nat := .app proofA (nestedProofType 10)

-- A known proof compared with a local proof requires inference of only the
-- local side. Rechecking the known side exceeds this call's small fuel.
#guard (inferA.{0,1} 64 proofEntries ctx largeProof).isOk
#guard !(inferA.{0,1} 8 proofEntries ctx largeProof).isOk
#guard (proofValue.{0,1} proofEntries ctx (.bvar 0)).isNone
#guard (isDefEq.{0,1} 8 proofEntries ctx largeProof (.bvar 0)).isOk
#guard (isDefEq.{0,1} 8 proofEntries ctx (.bvar 0) largeProof).isOk
#guard !(isDefEq.{0,1} 0 proofEntries ctx largeProof (.bvar 0)).isOk

-- An unknown proposition expression or missing local is not a proof witness.
#guard !(isDefEq.{0,1} 64 proofEntries ctx proofA (.bvar 2)).isOk
#guard !(isDefEq.{0,1} 64 proofEntries ctx (.bvar 2) proofA).isOk
#guard !(isDefEq.{0,1} 64 proofEntries ctx proofA (.bvar 4)).isOk
#guard match isDefEqC.{0,1} 64 proofEntries ctx largeProof (.bvar 0)
    (Cache.empty (fun _ => 0) 0) with
  | (.error .exhausted, _) => true
  | _ => false

-- Exhausted speculation must still allow ordinary zeta conversion. With
-- only one work unit, the unknown side cannot be inferred speculatively.
#guard match isDefEqC.{0,1} 16 proofEntries [] proofA (.letE proofType proofA (.bvar 0))
    (Cache.empty (fun _ => 0) 1) with
  | (.ok _, _) => true
  | _ => false

def proofResultType : AExpr Nat :=
  .forallE .always (nestedProofType 10) (nestedProofType 10)

def knownProposition : AExpr Nat :=
  .app (.app (.const (.member 5 0) []) proofResultType) largeProof

def formedEntries : Environment Nat := fun
  | .member 5 0 => some ⟨0,
      .forallE .never prop (.forallE .never (.bvar 0) prop), none, [], []⟩
  | .member 6 0 => some ⟨0, knownProposition, none, [], []⟩
  | r => proofEntries r

-- Obtain formedness only from successful full inference. Internal inference
-- may then reuse that evidence at a non-Prop application, preserving an
-- ordinary typing claim and the same cache partition.
def inferKnown (fuel : Nat) (e : AExpr Nat) : Bool :=
  match inferA.{0,1} 64 formedEntries [] e with
  | .ok h => (KM.run (fun _ => 0) (fuel * workPerFuel)
      (inferFormedC.{0,1} fuel formedEntries [] e h.claim.formed)).isOk
  | .error _ => false

#guard (inferA.{0,1} 64 formedEntries [] knownProposition).isOk
#guard !(inferA.{0,1} 8 formedEntries [] knownProposition).isOk
#guard inferKnown 8 knownProposition
#guard !inferKnown 0 knownProposition

-- Possibly-Prop application slots still validate their argument, even with
-- formedness available; this proof function retains the expensive residue.
#guard !inferKnown 8 largeProof

-- The public checker still rejects malformed application arguments. Its
-- lambda body-type check is the sole consumer of the new internal path.
#guard !(inferA.{0,1} 64 formedEntries []
  (.app (.app (.const (.member 5 0) []) proofType) prop)).isOk
#guard (inferA.{0,1} 16 formedEntries []
  (.lam .always proofType (.const (.member 6 0) []))).isOk

#guard match inferA.{0,1} 64 formedEntries [] knownProposition with
  | .ok h => match inferFormedC.{0,1} 8 formedEntries [] knownProposition h.claim.formed
      (Cache.empty (fun _ => 0) 0) with
    | (.error .exhausted, _) => true
    | _ => false
  | .error _ => false

end Tests.Ix.Kernel.ProofIrrelevance
