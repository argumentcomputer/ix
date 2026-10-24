import Ix.Cert.ReferenceFronts
import IxC.Kernel.Model.Annot.BitLemmas
import IxC.Kernel.Model.Tiers

/-! # Actual checked readings at a fixed interpretation across prefix growth

Full inference supplies the positive constant, literal and projection
lookups used by the reading. Preserving those lookups produces identical
readings with any FIXED acval, without a model of the smaller environment.
This does not transport arbitrary conversion derivations or source typing.
-/

namespace Ix.Cert.PrefixReadings

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open Ix.Kernel.Model.Rules (Frame Graded)
open Ix.Cert.ConversionValues ReferenceFronts

universe w
variable {md : Mode} {before final : Env md}

/-- A successful lookup-only guard that rejects absence keeps its verdict. -/
theorem lookup_guard (lookup : FindPreserved before final)
    (guard : Option (Ix.Kernel.ConstantInfo md) → Bool) (absent : guard none = false)
    {key : Key md} (held : guard (before.find? key) = true) :
    guard (final.find? key) = true := by
  cases found : before.find? key with
  | none => rw [found, absent] at held; exact nomatch held
  | some ci => rw [lookup found]; simpa only [found] using held

theorem nat_support (lookup : FindPreserved before final)
    (held : natLitSupported before = true) : natLitSupported final = true := by
  simp only [natLitSupported, Bool.and_eq_true] at held ⊢
  exact ⟨⟨lookup_guard lookup natIndOk rfl held.1.1,
    lookup_guard lookup natZeroOk rfl held.1.2⟩, lookup_guard lookup natSuccOk rfl held.2⟩

theorem string_support (lookup : FindPreserved before final)
    (held : strLitSupported before = true) : strLitSupported final = true := by
  simp only [strLitSupported, Bool.and_eq_true] at held ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := held
  exact ⟨⟨⟨⟨⟨⟨⟨nat_support lookup h0, lookup_guard lookup stringTyOk rfl h1⟩,
    lookup_guard lookup stringOfListTyOk rfl h2⟩, lookup_guard lookup listTyOk rfl h3⟩,
    lookup_guard lookup listNilTyOk rfl h4⟩, lookup_guard lookup listConsTyOk rfl h5⟩,
    lookup_guard lookup charTyOk rfl h6⟩, lookup_guard lookup charOfNatTyOk rfl h7⟩

/-- Only a PRESENT projection slot is transported. New slots are allowed. -/
theorem projection_slot (lookup : FindPreserved before final)
    {sn : Key md} {i : Nat} {entry : ProjEntry md}
    (found : before.findProj? sn i = some entry) : final.findProj? sn i = some entry := by
  obtain ⟨tbl, stored, bound, rfl⟩ := Env.findProj?_some found
  exact Env.findProj?_of_table (lookup stored) bound

/-- Both readings are constructed from the actual full-inference run.
The valuation is arbitrary and fixed; no EnvModel, interpretation equality,
input reading, literal-guard equality or absent-slot premise is needed. -/
theorem inferred_readings_preserved
    (acval : Key md → (LevelParam → Nat) → AnnotTerm) (φ : LevelParam → Nat)
    {F d : Nat} {e ty : Ix.Kernel.Expr md}
    (lookup : FindPreserved before final) (frame : Frame d e)
    (run : inferTypeCore .verified before F d e = .ok ty) :
    ∃ ea, denoteMeta acval before φ d e = some ea ∧ denoteMeta acval final φ d e = some ea := by
  induction F generalizing d e ty with
  | zero => rw [inferTypeCore_zero] at run; exact nomatch run
  | succ F ih =>
    cases e with
    | bvar i =>
      have bound := frame.2.1
      simp only [Ix.Kernel.Expr.looseBVarsBounded] at bound
      exact absurd (of_decide_eq_true bound) (Nat.not_lt_zero i)
    | sort u => exact ⟨_, denoteMeta_sort _ _ _, denoteMeta_sort _ _ _⟩
    | fvar idx dom => exact ⟨_, denoteMeta_fvar _ _ _ _, denoteMeta_fvar _ _ _ _⟩
    | const n us =>
      obtain ⟨ci, found, arity⟩ := inferTypeCore_const_inv_len run
      exact ⟨_, denoteMeta_const found arity, denoteMeta_const (lookup found) arity⟩
    | lit literal =>
      cases literal with
      | natVal n =>
        have support := inferTypeCore_natLit_inv run
        exact ⟨_, denoteMeta_natLit support, denoteMeta_natLit (nat_support lookup support)⟩
      | strVal s =>
        have support := inferTypeCore_strLit_inv run
        obtain ⟨nilStored, consStored⟩ := strLitSupported_listNames support
        have same : denoteMeta acval final φ d (.lit (.strVal s)) =
            denoteMeta acval before φ d (.lit (.strVal s)) := by
          rw [denoteMeta, ite_eq_left (string_support lookup support), denoteMeta, ite_eq_left support,
            ← levelParamsAt_congr lookup nilStored, ← levelParamsAt_congr lookup consStored]
        cases read : denoteMeta acval before φ d (.lit (.strVal s)) with
        | none => rw [denoteMeta, ite_eq_left support] at read; exact nomatch read
        | some ea => exact ⟨ea, rfl, same.trans read⟩
    | app fn arg =>
      obtain ⟨_, _, _, _, fnRun, _, _, _, argRun, _⟩ := inferTypeCore_app_inv run
      obtain ⟨fa, beforeFn, finalFn⟩ := ih frame.app_fn fnRun
      obtain ⟨aa, beforeArg, finalArg⟩ := ih frame.app_arg argRun
      exact ⟨_, by rw [denoteMeta_app, beforeFn, beforeArg]; rfl,
        by rw [denoteMeta_app, finalFn, finalArg]; rfl⟩
    | forallE dom body mb =>
      obtain ⟨_, _, _, _, domainRun, _, bodyRun, _, _, _⟩ := inferTypeCore_forall_inv run
      obtain ⟨da, beforeDom, finalDom⟩ := ih frame.forallE_ty domainRun
      obtain ⟨ba, beforeBody, finalBody⟩ := ih (frame.forallE_open frame.forallE_ty) bodyRun
      exact ⟨_, by rw [denoteMeta_forallE, beforeDom, beforeBody]; rfl,
        by rw [denoteMeta_forallE, finalDom, finalBody]; rfl⟩
    | lam dom body mb =>
      obtain ⟨_, _, _, domainRun, _, bodyRun, _, _, _⟩ := inferTypeCore_lam_inv run
      obtain ⟨da, beforeDom, finalDom⟩ := ih frame.lam_ty domainRun
      obtain ⟨ba, beforeBody, finalBody⟩ := ih (frame.lam_open frame.lam_ty) bodyRun
      exact ⟨_, by rw [denoteMeta_lam, beforeDom, beforeBody]; rfl,
        by rw [denoteMeta_lam, finalDom, finalBody]; rfl⟩
    | proj sn i pe =>
      obtain ⟨_, _, _, _, entry, subjectRun, _, _, slot, _, _, _, _, headEq⟩ :=
        inferTypeCore_proj_inv run
      subst headEq
      obtain ⟨pa, beforeSubject, finalSubject⟩ := ih frame.proj_arg subjectRun
      exact ⟨_, denoteMeta_proj_tower slot beforeSubject,
        denoteMeta_proj_tower (projection_slot lookup slot) finalSubject⟩
    | letE _ _ _ _ => exact (inferTypeCore_letE_inv run).elim

end Ix.Cert.PrefixReadings

namespace Ix.Cert.ReferenceFronts

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model Ix.Kernel.SetTheory
open Ix.Kernel.Model.Rules (Frame Graded)
open Ix.Cert.ConversionValues PrefixReadings

universe w
variable {md : Mode} {ev : Evidences md} {ds : List (Declaration md)}
  {envA before : Env md} {i F : Nat} {cv : Ix.Kernel.ConstantVal md}
  {raw expected checked : Ix.Kernel.Expr md} {hint : ReducibilityHint}

/-- The actual current-plus-suffix run preserves every successful prefix
lookup. The extension relation is an output, never a new front premise. -/
theorem DefinitionFrontAt.lookup_preserved
    (front : DefinitionFrontAt ev ds envA i cv raw hint F before expected checked) :
    FindPreserved before envA := by
  obtain ⟨_, _, _, step, suffix, _, _, _⟩ := front
  have rest : (.defnDecl cv raw hint :: ds.drop (i + 1)).foldlM
      (checkDecl .verified (fueledOps .verified F) ev) before = .ok envA := by
    rw [List.foldlM_cons, step]
    exact suffix
  intro n ci found
  exact (foldlM_checkDecl_post .verified (fueledOps .verified F) ev _ before envA rest).persist found

/-- Real header/value annotation and full inference produce both paired
readings. The interpretation is arbitrary and kept fixed on both sides. -/
theorem DefinitionFrontAt.readings_across
    (front : DefinitionFrontAt ev ds envA i cv raw hint F before expected checked)
    (acval : Key md → (LevelParam → Nat) → AnnotTerm) (φ : LevelParam → Nat) :
    ∃ ha va,
      denoteMeta acval before φ 0 expected = some ha ∧
      denoteMeta acval envA φ 0 expected = some ha ∧
      denoteMeta acval before φ 0 checked = some va ∧
      denoteMeta acval envA φ 0 checked = some va := by
  have lookup : FindPreserved before envA := front.lookup_preserved
  obtain ⟨_, _, _, _, _, header, value, _⟩ := front
  obtain ⟨_, _, _, _, bounded, closed, ann, _, _, _, _, headerInfer, _⟩ := header
  obtain ⟨_, valueInfer, _⟩ := value.2.2.2.2.2
  obtain ⟨ha, headerBefore, headerFinal⟩ := inferred_readings_preserved acval φ lookup
    (annotation_frame ann closed bounded) headerInfer
  obtain ⟨va, valueBefore, valueFinal⟩ := inferred_readings_preserved acval φ lookup
    (valueFront_frame value) valueInfer
  exact ⟨ha, va, headerBefore, headerFinal, valueBefore, valueFinal⟩

/-- The target's actual prefix header/body have their semantic package at
the EXACT supplied final interpretation. Its stored definition pins the
body reading; no prefix model or baseline typing/grade/equality is chosen.
Full model restriction and local-conversion transport remain separate. -/
theorem DefinitionFrontAt.final_semantic_front
    (front : DefinitionFrontAt ev ds envA i cv raw hint F before expected checked)
    (V : Type w) [SetTheory V] (M : Cached.StrongModel V envA) (φ : LevelParam → Nat) :
    ∃ ha,
      denoteMeta M.internal.base2.acval before φ 0 expected = some ha ∧
      denoteMeta M.internal.base2.acval envA φ 0 expected = some ha ∧
      Graded V [] ha ∧
      denoteMeta M.internal.base2.acval before φ 0 checked =
        some (M.internal.base2.acval cv.name φ) ∧
      Graded V [] (M.internal.base2.acval cv.name φ) ∧
      ∀ ρ : BVarIdx → V,
        interp V ρ (M.internal.base2.acval cv.name φ) ∈ˢ interp V ρ ha := by
  obtain ⟨ha, va, headerBefore, headerFinal, valueBefore, valueFinal⟩ :=
    front.readings_across M.internal.base2.acval φ
  obtain ⟨_, _, _, _, _, _, _, stored⟩ := front
  have member := Semantics.Env.find?_mem stored
  have pinned := M.internal.defn_reads φ ⟨cv.name, cv.levelParams, expected⟩ checked ⟨hint, member⟩
  have same := Option.some.inj (valueFinal.symm.trans pinned)
  rw [same] at valueBefore
  refine ⟨ha, headerBefore, headerFinal, ?_, valueBefore, ?_, ?_⟩
  · exact fun ρ _ => M.internal.type_wellDenotedV _ member φ ha headerFinal ρ
  · exact fun ρ _ => ⟨M.internal.base2.acval_wellDenoted _ φ ρ, M.internal.acval_validV _ φ ρ⟩
  · exact M.internal.mem_type _ member φ ha headerFinal

end Ix.Cert.ReferenceFronts
