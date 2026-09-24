/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Model.Judgment

/-! # Semantic rules for `let`

`letE t v b` is interpreted by substitution: its value is the body's value with
the bound variable set to the value of `v`. The typing rule mirrors
`TypingClaim.betaResult`, and zeta conversion needs no typing at all, since
`interp_inst` is an unconditional equation. The let's type annotation `t` is
checked by the kernel and recorded in `WellDenoted`, but carries no regime
condition and does not influence the interpretation. -/

namespace Ix.Kernel.Model

open SetTheory

universe u v

variable {β : Type u} {entries : Environment β} {Γ : Context β}

theorem TypingClaim.letE {t v b B : AExpr β} {l : VLevel}
    (ht : TypingClaim.{u,v} entries Γ t (.sort l))
    (hv : TypingClaim.{u,v} entries Γ v t)
    (hb : TypingClaim.{u,v} entries (Γ.push t) b B) :
    TypingClaim.{u,v} entries Γ (.letE t v b) (B.inst v) := by
  intro V _ constants hM levels env hΓ
  obtain ⟨htw, -, -⟩ := ht V constants hM levels env hΓ
  obtain ⟨hvw, -, hvm⟩ := hv V constants hM levels env hΓ
  obtain ⟨hbw, hBw, hbm⟩ := hb V constants hM levels
    (Valuation.cons (interp constants levels env v) env) (hΓ.push htw hvm)
  refine ⟨⟨htw, hvw, hbw⟩, ?_, ?_⟩
  · apply wellDenoted_inst
    · simpa using hvw
    · simpa using hBw
  · simpa only [interp, interp_inst, Valuation.skip_zero, Valuation.insert_zero] using hbm

/-- Zeta reduction: a `let` denotes its substituted body, unconditionally. -/
theorem ConversionClaim.zeta (t v b : AExpr β) :
    ConversionClaim.{u,v} entries Γ (.letE t v b) (b.inst v) := by
  intro V _ constants _ levels env _
  simp only [interp, interp_inst, Valuation.skip_zero, Valuation.insert_zero]

end Ix.Kernel.Model
