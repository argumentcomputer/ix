/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Infer

/-! # Typing primitives for declaration checking

The old branch validated typing witnesses here (`verifyType`). The kernel
instead infers: `checkSort` reads the sort of a type and `checkType` infers a
term's type and converts it to the expected one, each returning the semantic
claim. `CheckedClaim` wraps a proposition at the data universe so proof-
producing checks compose inside `Search` with the syntax they check. -/

namespace Ix.Kernel.Certified

open Model

universe u v

/-- An erased result at the data universe of the checked syntax. -/
structure CheckedClaim (claim : Prop) : Type u where
  down : claim

variable {β : Type u} [DecidableEq β]

/-- `e` is a type: infer its type and read the sort off its weak head normal
form. -/
def checkSort (fuel : Nat) (entries : Environment β) (Γ : Context β) (e : AExpr β) :
    Search (TypedSort.{u,v} entries Γ e) := do
  let ⟨S, hS⟩ ← inferA.{u,v} fuel entries Γ e
  sortOf (whnf.{u,v} fuel entries Γ S) hS

/-- Check against an already formed expected type in this exact environment
and context. Its formation evidence is reused, without another type check. -/
def checkAgainst (fuel : Nat) (entries : Environment β) (Γ : Context β) (e A : AExpr β)
    (formed : FormedClaim.{u,v} entries Γ A) :
    Search (CheckedClaim.{u} (TypingClaim.{u,v} entries Γ e A)) := do
  let ⟨B, hb⟩ ← inferA.{u,v} fuel entries Γ e
  let ⟨hc⟩ ← isDefEq.{u,v} fuel entries Γ B A
  return ⟨hb.convF formed hc⟩

/-- Check formation once before checking a term against its expected type. -/
def checkType (fuel : Nat) (entries : Environment β) (Γ : Context β) (e A : AExpr β) :
    Search (CheckedClaim.{u} (TypingClaim.{u,v} entries Γ e A)) := do
  let ⟨_, hA⟩ ← checkSort.{u,v} fuel entries Γ A
  checkAgainst.{u,v} fuel entries Γ e A hA.formed

/-- At the same fuel, successful checking is unchanged by obtaining expected
formation first. Both independent checks and the same conversion must still
succeed. When both checks fail, the first diagnostic may differ. -/
theorem checkType_acceptance (fuel : Nat) (entries : Environment β) (Γ : Context β)
    (e A : AExpr β) :
    (checkType.{u,v} fuel entries Γ e A).isOk =
      (do
        let ⟨B, hb⟩ ← inferA.{u,v} fuel entries Γ e
        let ⟨_, hA⟩ ← checkSort.{u,v} fuel entries Γ A
        let ⟨hc⟩ ← isDefEq.{u,v} fuel entries Γ B A
        pure (⟨hb.convF hA.formed hc⟩ : CheckedClaim.{u} (TypingClaim.{u,v} entries Γ e A))).isOk := by
  cases ht : inferA.{u,v} fuel entries Γ e <;>
    cases hA : checkSort.{u,v} fuel entries Γ A <;>
    simp [checkType, checkAgainst, ht, hA, bind, Except.bind, pure, Except.pure, Except.isOk] <;> rfl

end Ix.Kernel.Certified
