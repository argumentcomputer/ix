import Ix.Cert.PrefixCapabilities

/-! # Stored recursor rules at the fixed final interpretation

Prefix WF supplies every stored rule's header, RHS and nested-pin
resolution. The actual opening preserves it, so all readings agree at
the same acval, including the open pins at their exact rule-prefix depth.
-/

namespace Ix.Cert.PrefixRecRules

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open Ix.Cert.PrefixConstType

variable {md : Mode} {before final : Env md}

/-- The actual reverse opening introduces only sort-zero annotations. -/
theorem openRev_resolves {e : Ix.Kernel.Expr md}
    (resolves : e.constsResolve before = true) :
    ∀ d n, (Verify.openRev d n e).constsResolve before = true := by
  intro d n
  induction n with
  | zero => exact resolves
  | succ n ih =>
    show ((Verify.openRev d n e).instantiate1 (.fvar (d + n) (.sort .zero)) 0).constsResolve before = true
    exact Ix.Kernel.Expr.constsResolve_instantiate1 rfl 0 ih

variable {n : Key md} {cv : Ix.Kernel.ConstantVal md} {mI rP : Nat}
  {rules : List (RecRule md)} {rl : RecRule md}

/-- Resolution comes from THIS stored recursor and THIS rule's WF.
Every getD pin is covered, including the actual out-of-range default. -/
theorem stored_rule_resolves (wf : EnvWF before)
    (stored : before.find? n = some (.recInfo cv mI rP rules))
    (member : rl ∈ rules) (us : List Ix.Kernel.Level) :
    (cv.type.instantiateLevelParams cv.levelParams us).constsResolve before = true ∧
    ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us).constsResolve before = true ∧
    ∀ lvls pins, RecRule.fire rl = .nested lvls pins → ∀ i,
      (Verify.openRev 0 rP
        ((pins.getD i default).instantiateLevelParams cv.levelParams us)).constsResolve before = true := by
  obtain ⟨_, _, header, _, _, recWF, _, _⟩ := wf _ (Semantics.Env.find?_mem stored)
  obtain ⟨_, _, rhs, _, nested⟩ := recWF cv mI rP rules rfl rl member
  refine ⟨?_, ?_, ?_⟩
  · rw [Ix.Kernel.Expr.constsResolve_instantiateLevelParams]
    exact header
  · rw [Ix.Kernel.Expr.constsResolve_instantiateLevelParams]
    exact rhs
  · intro lvls pins fire i
    obtain ⟨_, _, pinsWF, _⟩ := nested lvls pins fire
    have pin : (pins.getD i default).constsResolve before = true := by
      by_cases bound : i < pins.length
      · exact (pinsWF _ (Ix.Kernel.getD_mem bound)).2.2.1
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
    apply openRev_resolves (d := 0) (n := rP)
    rw [Ix.Kernel.Expr.constsResolve_instantiateLevelParams]
    exact pin

/-- Model-free equations at arbitrary fixed acval: the header/RHS at zero,
and every actual nested open pin at rP. No input reading or grade is needed. -/
theorem stored_rule_readings (wf : EnvWF before)
    (lookup : FindPreserved before final) (slots : StoredHeadSlots before final)
    (acval : Key md → (LevelParam → Nat) → AnnotTerm) (φ : LevelParam → Nat)
    (stored : before.find? n = some (.recInfo cv mI rP rules))
    (member : rl ∈ rules) (us : List Ix.Kernel.Level) :
    denoteMeta acval before φ 0 (cv.type.instantiateLevelParams cv.levelParams us) =
      denoteMeta acval final φ 0 (cv.type.instantiateLevelParams cv.levelParams us) ∧
    denoteMeta acval before φ 0 ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us) =
      denoteMeta acval final φ 0 ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us) ∧
    ∀ lvls pins, RecRule.fire rl = .nested lvls pins → ∀ i,
      denoteMeta acval before φ rP
        (Verify.openRev 0 rP ((pins.getD i default).instantiateLevelParams cv.levelParams us)) =
      denoteMeta acval final φ rP
        (Verify.openRev 0 rP ((pins.getD i default).instantiateLevelParams cv.levelParams us)) := by
  obtain ⟨header, rhs, pins⟩ := stored_rule_resolves wf stored member us
  exact ⟨resolving_reading_eq acval φ 0 _ lookup slots header,
    resolving_reading_eq acval φ 0 _ lookup slots rhs,
    fun lvls ps fire i => resolving_reading_eq acval φ rP _ lookup slots (pins lvls ps fire i)⟩

end Ix.Cert.PrefixRecRules
