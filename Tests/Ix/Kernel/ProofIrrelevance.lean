/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Infer

/-! Proof irrelevance must establish that both inferred types inhabit `Prop`.
It need not recursively compare those types. The negative controls prevent
this shortcut from identifying propositions themselves or ordinary data. -/

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

end Tests.Ix.Kernel.ProofIrrelevance
