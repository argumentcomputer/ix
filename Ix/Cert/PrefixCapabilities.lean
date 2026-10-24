import Ix.Cert.PrefixConstType
import IxC.Kernel.Model.NatStep

/-! # Capability and successor rows at the fixed final interpretation

Actual prefix growth preserves the positive family guards. Its resolving
header equation transports the final model's capability readings without
changing the valuation or adding an eta-family premise to the unit law.
The successor row needs only the core, not the full strong-model invariant.
The remaining recursor, tower and arithmetic rows are still separate.
-/

namespace Ix.Cert.PrefixCapabilities

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open Ix.Cert.PrefixConstType

universe w
variable {md : Mode} {before final : Env md}

theorem eta_family_preserved (lookup : FindPreserved before final)
    {T : Key md} {caps : IndCaps md} (family : EtaFamilyStored before T caps) :
    EtaFamilyStored final T caps := by
  obtain ⟨C, ctorEq, nonreserved, ⟨cvC, nP, nF, found⟩, projections⟩ := family
  refine ⟨C, ctorEq, nonreserved, ⟨cvC, nP, nF, lookup found⟩, ?_⟩
  intro j bound
  obtain ⟨cv, mI, rP, rules, stored⟩ := projections j bound
  exact ⟨cv, mI, rP, rules, lookup stored⟩

/-- Both capability halves use the supplied final model. The unit half
retains its original contract with no EtaFamilyStored premise. -/
theorem capabilities_preserved {V : Type w} [SetTheory V]
    (M : Cached.StrongModel V final) (core : EnvModel V before)
    (valuation : core.acval = M.internal.base2.acval)
    (lookup : FindPreserved before final) (slots : StoredHeadSlots before final) :
    CapsOk core := by
  constructor
  · intro T cv caps found eta nonreserved family φ C ctorEq us arity
    obtain ⟨typeRead, reading, grade, law⟩ :=
      M.internal.caps_ok.1 T cv caps (lookup found) eta nonreserved
        (eta_family_preserved lookup family) φ C ctorEq us arity
    have resolved := (core.wf _ (Semantics.Env.find?_mem found)).2.2.1
    have instantiated : (cv.type.instantiateLevelParams cv.levelParams us).constsResolve before = true := by
      rw [Ix.Kernel.Expr.constsResolve_instantiateLevelParams]
      exact resolved
    have same := resolving_reading_eq M.internal.base2.acval φ 0 _ lookup slots instantiated
    refine ⟨typeRead, ?_, grade, ?_⟩
    · simpa only [valuation] using same.trans reading
    · simpa only [valuation] using law
  · intro T cv caps found unitlike nonreserved φ us arity
    obtain ⟨typeRead, reading, grade, law⟩ :=
      M.internal.caps_ok.2 T cv caps (lookup found) unitlike nonreserved φ us arity
    have resolved := (core.wf _ (Semantics.Env.find?_mem found)).2.2.1
    have instantiated : (cv.type.instantiateLevelParams cv.levelParams us).constsResolve before = true := by
      rw [Ix.Kernel.Expr.constsResolve_instantiateLevelParams]
      exact resolved
    have same := resolving_reading_eq M.internal.base2.acval φ 0 _ lookup slots instantiated
    refine ⟨typeRead, ?_, grade, ?_⟩
    · simpa only [valuation] using same.trans reading
    · simpa only [valuation] using law

/-- The existing literal successor argument uses only EnvModel fields.
No NatOps/recursor/tower law or full prefix model is supplied or assumed. -/
theorem nat_succ_row {V : Type w} [SetTheory V] (core : EnvModel V before)
    (φ : LevelParam → Nat) : Rules.NatSuccRow core φ := by
  intro d arg n Δa ea supported raw reading grade
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, foundN, foundZ, foundS,
      levelsN, levelsZ, levelsS, _⟩ := Ix.Kernel.natLitSupported_inv supported
  obtain ⟨fa, wa, headRead, argRead, rfl⟩ := denoteMeta_app_inv reading
  obtain rfl : fa = core.acval Ix.Kernel.natSuccName φ :=
    denoteMeta_head foundS
      (show (Ix.Kernel.ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams = [] from levelsS)
      headRead
  obtain rfl : wa = natLit core φ n :=
    Option.some.inj (argRead.symm.trans (denoteMeta_rawNatLit core supported raw d))
  refine ⟨natLit core φ (n + 1), denoteMeta_natLit_spine core supported d (n + 1), ?_, ?_⟩
  · rw [natLit_succ]
    exact grade
  · intro ρ _
    rw [natLit_succ]

end Ix.Cert.PrefixCapabilities

namespace Ix.Cert.ReferenceFronts

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model Ix.Kernel.SetTheory
open Ix.Kernel.Model.Rules (Graded)
open Ix.Cert.PrefixCapabilities

universe w
variable {md : Mode} {ev : Evidences md} {ds : List (Declaration md)}
  {envA before : Env md} {i F : Nat} {cv : Ix.Kernel.ConstantVal md}
  {raw expected checked : Ix.Kernel.Expr md} {hint : ReducibilityHint}

/-- The actual indexed front supplies capability and successor rows at
the same final interpretation. RecRules, TowerOk, NatOpRow, baseline
typing/equality and the full source-model composition remain open. -/
theorem DefinitionFrontAt.final_prefix_caps_succ
    (front : DefinitionFrontAt ev ds envA i cv raw hint F before expected checked)
    (V : Type w) [SetTheory V] (M : Cached.StrongModel V envA) :
    ∃ core : EnvModel V before,
      core.acval = M.internal.base2.acval ∧ cvalOf core.acval = M.model.cval ∧
      AcvalValid core ∧ (∀ φ : LevelParam → Nat, NatHeads core φ) ∧ EqLaw core ∧
      AcvalDefnInst core ∧ (∀ φ : LevelParam → Nat, ConstType core φ) ∧
      CapsOk core ∧ (∀ φ : LevelParam → Nat, Rules.NatSuccRow core φ) ∧
      ∀ φ : LevelParam → Nat,
        ∃ ha,
          denoteMeta core.acval before φ 0 expected = some ha ∧ Graded V [] ha ∧
          denoteMeta core.acval before φ 0 checked = some (core.acval cv.name φ) ∧
          Graded V [] (core.acval cv.name φ) ∧
          ∀ ρ : BVarIdx → V, interp V ρ (core.acval cv.name φ) ∈ˢ interp V ρ ha := by
  obtain ⟨core, valuation, publicEq, valid, heads, eqLaw, definitions, types, target⟩ :=
    front.final_prefix_const_ty V M
  exact ⟨core, valuation, publicEq, valid, heads, eqLaw, definitions, types,
    capabilities_preserved M core valuation front.lookup_preserved front.stored_head_slots,
    fun φ => nat_succ_row core φ, target⟩

end Ix.Cert.ReferenceFronts
