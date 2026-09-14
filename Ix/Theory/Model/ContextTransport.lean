/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Model.Judgment

/-!
# Transport across context extension

A valuation satisfying an extended context also satisfies its previous
context after dropping the newest variable. Consequently every existing
semantic typing claim can be lifted into that extension.
-/

namespace Ix.Theory.Model
universe u v
variable {β : Type u}

open SetTheory

theorem Context.Valid.pop {V : Type v} [SetTheory V]
    {constants : Assignment β V} {levels : List Nat} {Γ : Context β}
    {env : Nat → V} {A : AExpr β}
    (valid : (Γ.push A).Valid constants levels env) :
    Γ.Valid constants levels (Valuation.skip 1 0 env) := by
  intro i B found
  have previous := valid (i + 1) (B.liftN 1) (by simp [Context.push, found])
  simpa only [wellDenoted_liftN, interp_liftN, Valuation.skip, Nat.not_lt_zero,
    if_false, Nat.add_comm 1] using previous

theorem TypingClaim.weaken {entries : Environment β} {Γ : Context β}
    {e A : AExpr β} (typed : TypingClaim.{u,v} entries Γ e A) (D : AExpr β) :
    TypingClaim.{u,v} entries (Γ.push D) (e.liftN 1) (A.liftN 1) := by
  intro V _ constants realized levels env valid
  simpa only [wellDenoted_liftN, interp_liftN] using
    typed V constants realized levels (Valuation.skip 1 0 env) valid.pop

end Ix.Theory.Model
