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
producing checks compose inside `Option` with the syntax they check. -/

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
    Option (TypedSort.{u,v} entries Γ e) := do
  let ⟨S, hS⟩ ← inferA.{u,v} fuel entries Γ e
  sortOf (whnf.{u,v} fuel entries Γ S) hS

/-- `e` has the type `A`: infer, check that `A` is a type, and convert. -/
def checkType (fuel : Nat) (entries : Environment β) (Γ : Context β) (e A : AExpr β) :
    Option (CheckedClaim.{u} (TypingClaim.{u,v} entries Γ e A)) := do
  let ⟨B, hb⟩ ← inferA.{u,v} fuel entries Γ e
  let ⟨_, hA⟩ ← checkSort.{u,v} fuel entries Γ A
  let ⟨hc⟩ ← isDefEq.{u,v} fuel entries Γ B A
  return ⟨hb.convF hA.formed hc⟩

end Ix.Kernel.Certified
