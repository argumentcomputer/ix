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

universe w

/-- Every stored fired rule uses the supplied FINAL law at the same acval.
Both existential readings move back; type premises move forward; the nested
comparison consumes a final pin reading by moving it back to the prefix. -/
theorem rec_rules_preserved {V : Type w} [SetTheory V]
    (M : Cached.StrongModel V final) (core : EnvModel V before)
    (valuation : core.acval = M.internal.base2.acval)
    (lookup : FindPreserved before final) (slots : StoredHeadSlots before final)
    (φ : LevelParam → Nat) : RecRules core φ := by
  intro n cv mI rP rules stored rl member active
  obtain ⟨bounds, levelsLaw⟩ :=
    M.internal.rec_rules φ n cv mI rP rules (lookup stored) rl member active
  refine ⟨bounds, ?_⟩
  intro us arity
  obtain ⟨Ra, rhsRead, rhsGrade, pinsGrade, law⟩ := levelsLaw us arity
  obtain ⟨headerEq, rhsEq, pinsEq⟩ :=
    stored_rule_readings core.wf lookup slots M.internal.base2.acval φ stored member us
  refine ⟨Ra, ?_, rhsGrade, ?_, ?_⟩
  · simpa only [valuation] using rhsEq.trans rhsRead
  · intro lvls pins fire i bound
    obtain ⟨vpa, pinRead, pinGrade⟩ := pinsGrade lvls pins fire i bound
    refine ⟨vpa, ?_, ?_⟩
    · simpa only [valuation] using (pinsEq lvls pins fire i).trans pinRead
    · intro ρ zs TVa restR length grades typeRead fit
      apply pinGrade ρ zs TVa restR length grades ?_ fit
      exact headerEq.symm.trans (by simpa only [valuation] using typeRead)
  · intro cvj cnP cnF ctorFound usj ρ xs ys TVa TVja restR restC
      lengthX lengthY ctorArity levels plain nested indexPin typeRead ctorRead fitR fitC
    have ctorResolved := (core.wf _ (Semantics.Env.find?_mem ctorFound)).2.2.1
    have ctorInst : (cvj.type.instantiateLevelParams cvj.levelParams usj).constsResolve before = true := by
      rw [Ix.Kernel.Expr.constsResolve_instantiateLevelParams]
      exact ctorResolved
    have ctorEq := resolving_reading_eq M.internal.base2.acval φ 0 _ lookup slots ctorInst
    simp only [valuation] at typeRead ctorRead fitR ⊢
    refine law cvj cnP cnF (lookup ctorFound) usj ρ xs ys TVa TVja restR restC
      lengthX lengthY ctorArity levels plain ?_ indexPin
      (headerEq.symm.trans typeRead) (ctorEq.symm.trans ctorRead) fitR fitC
    intro lvls pins fire i bound vpa finalRead
    apply nested lvls pins fire i bound vpa
    simpa only [valuation] using (pinsEq lvls pins fire i).trans finalRead

end Ix.Cert.PrefixRecRules

namespace Ix.Cert.ReferenceFronts

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model Ix.Kernel.SetTheory
open Ix.Kernel.Model.Rules (Graded)
open Ix.Cert.PrefixRecRules

universe w
variable {md : Mode} {ev : Evidences md} {ds : List (Declaration md)}
  {envA before : Env md} {i F : Nat} {cv : Ix.Kernel.ConstantVal md}
  {raw expected checked : Ix.Kernel.Expr md} {hint : ReducibilityHint}

/-- The actual indexed front supplies UNIVERSAL RecRules at the same final
interpretation, retaining every prior row and the target package. TowerOk,
NatOpRow, baseline typing/equality and source-model composition remain open. -/
theorem DefinitionFrontAt.final_prefix_rec_rules
    (front : DefinitionFrontAt ev ds envA i cv raw hint F before expected checked)
    (V : Type w) [SetTheory V] (M : Cached.StrongModel V envA) :
    ∃ core : EnvModel V before,
      core.acval = M.internal.base2.acval ∧ cvalOf core.acval = M.model.cval ∧
      AcvalValid core ∧ (∀ φ : LevelParam → Nat, NatHeads core φ) ∧ EqLaw core ∧
      AcvalDefnInst core ∧ (∀ φ : LevelParam → Nat, ConstType core φ) ∧
      CapsOk core ∧ (∀ φ : LevelParam → Nat, Rules.NatSuccRow core φ) ∧
      (∀ φ : LevelParam → Nat, RecRules core φ) ∧
      ∀ φ : LevelParam → Nat,
        ∃ ha,
          denoteMeta core.acval before φ 0 expected = some ha ∧ Graded V [] ha ∧
          denoteMeta core.acval before φ 0 checked = some (core.acval cv.name φ) ∧
          Graded V [] (core.acval cv.name φ) ∧
          ∀ ρ : BVarIdx → V, interp V ρ (core.acval cv.name φ) ∈ˢ interp V ρ ha := by
  obtain ⟨core, valuation, publicEq, valid, heads, eqLaw, definitions, types, caps, succ, target⟩ :=
    front.final_prefix_caps_succ V M
  exact ⟨core, valuation, publicEq, valid, heads, eqLaw, definitions, types, caps, succ,
    fun φ => rec_rules_preserved M core valuation front.lookup_preserved front.stored_head_slots φ,
    target⟩

end Ix.Cert.ReferenceFronts
