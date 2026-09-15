/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Inductive.Admission

/-!
# Singleton admission from the production runs

The retained closed type checks required by the admission theorem are built
from the exact inference calls of the member classification pass and of the
recursor block's first pass, together with a finite inference tree for each
call, as the axiom and definition admissions do. Scope of every stored type
and rule comes from the validation calls of the same passes.
-/

namespace Ix.Kernel.Consistency.Inductive

open Theory Theory.Model Theory.Certified Theory.Certified.Ordinary Theory.Inductive

universe v

private theorem bind_success {α β : Type} {x : TcM .anon α} {k : α → TcM .anon β}
    {before after : TcState .anon} {value : β}
    (accepted : EStateM.bind x k before = .ok value after) :
    ∃ intermediate state, x before = .ok intermediate state ∧
      k intermediate state = .ok value after := by
  rw [EStateM.bind] at accepted
  cases run : x before with
  | error err state => rw [run] at accepted; contradiction
  | ok intermediate state =>
      rw [run] at accepted
      exact ⟨intermediate, state, rfl, accepted⟩

/-! ### Scope from validation -/

/-- Validation of any stored declaration begins by validating its type. -/
theorem validateConst_type_scoped {c : KConst .anon} {methods : Methods .anon}
    {before after : TcState .anon}
    (h : (RecM.validateConstWellScoped c).run methods before = .ok () after)
    {support : RunSupport} (coverage : c.ty.ValidationCoverage support)
    (collision : support.CollisionFree) : c.ty.Scoped 0 c.lvls.toNat := by
  unfold RecM.validateConstWellScoped at h
  simp only [ReaderT.run_bind] at h
  change EStateM.bind ((RecM.validateExprWellScoped c.ty 0 c.lvls.toNat).run methods) _ before = _ at h
  obtain ⟨⟨⟩, _, typeRun, _⟩ := bind_success h
  obtain ⟨_, _, _, hscoped⟩ := RecM.validateExprWellScoped_sound coverage collision typeRun
  exact hscoped

/-- A yielding loop body runs on every element of the list. -/
theorem forIn_yield_all {α : Type} {methods : Methods .anon}
    {f : α → PUnit → RecM .anon (ForInStep PUnit)} (P : α → Prop)
    (hf : ∀ a s x s', (f a ()).run methods s = .ok x s' → x = .yield () ∧ P a) :
    ∀ {l : List α} {s s' : TcState .anon}, (forIn l () f).run methods s = .ok () s' → ∀ a ∈ l, P a
  | [], _, _, _ => by simp
  | a :: l, s, s', h => by
      simp only [List.forIn_cons, ReaderT.run_bind] at h
      change EStateM.bind ((f a ()).run methods) _ s = _ at h
      obtain ⟨x, s1, hfa, h⟩ := bind_success h
      obtain ⟨rfl, hP⟩ := hf a s x s1 hfa
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hP
      · change (forIn l () f).run methods s1 = _ at h
        exact forIn_yield_all P hf h b hb

/-- Validation of a recursor validates every stored rule right-hand side. -/
theorem validateConst_rules_scoped {name : Mode.anon.F Name} {levelParams : Mode.anon.F (Array Name)}
    {k isUnsafe : Bool} {lvls params indices motives minors : UInt64} {block : KId .anon}
    {memberIdx : UInt64} {ty : KExpr .anon} {rules : Array (Kernel.RecRule .anon)}
    {leanAll : Mode.anon.F (Array (KId .anon))} {methods : Methods .anon} {before after : TcState .anon}
    (h : (RecM.validateConstWellScoped (KConst.recr name levelParams k isUnsafe lvls params indices
      motives minors block memberIdx ty rules leanAll)).run methods before = .ok () after)
    {support : RunSupport} (coverage : ∀ rule ∈ rules.toList, rule.rhs.ValidationCoverage support)
    (collision : support.CollisionFree) :
    ∀ rule ∈ rules.toList, rule.rhs.Scoped 0 lvls.toNat := by
  unfold RecM.validateConstWellScoped at h
  simp only [ReaderT.run_bind] at h
  change EStateM.bind ((RecM.validateExprWellScoped ty 0 lvls.toNat).run methods) _ before = _ at h
  obtain ⟨⟨⟩, validated, _, h⟩ := bind_success h
  simp only [← Array.forIn_toList] at h
  change EStateM.bind ((forIn rules.toList () _ : RecM .anon PUnit).run methods) _ validated = _ at h
  obtain ⟨⟨⟩, looped, hloop, _⟩ := bind_success h
  have hf : ∀ (rule : Kernel.RecRule .anon) (s : TcState .anon) (x : ForInStep PUnit) (s' : TcState .anon),
      ((fun rule (_ : PUnit) => (do
        RecM.validateExprWellScoped rule.rhs 0 lvls.toNat
        pure (ForInStep.yield PUnit.unit) : RecM .anon (ForInStep PUnit))) rule ()).run methods s =
        .ok x s' →
      x = .yield () ∧ (rule ∈ rules.toList → rule.rhs.Scoped 0 lvls.toNat) := by
    intro rule s x s' hb
    simp only [ReaderT.run_bind] at hb
    change EStateM.bind ((RecM.validateExprWellScoped rule.rhs 0 lvls.toNat).run methods) _ s = _ at hb
    obtain ⟨⟨⟩, s2, run, hb⟩ := bind_success hb
    change EStateM.Result.ok (ForInStep.yield ()) s2 = _ at hb
    cases hb
    refine ⟨rfl, fun hmem => ?_⟩
    obtain ⟨_, _, _, hscoped⟩ := RecM.validateExprWellScoped_sound (coverage rule hmem) collision run
    exact hscoped
  intro rule hmem
  exact forIn_yield_all _ hf hloop rule hmem hmem

/-! ### Retained checks from member runs -/

/-- A retained closed type check whose executed source is a stored
declaration's type, with the validation-derived scope of that type. -/
structure StoredTypeCheck (resolve : Address → Option (ConstRef Address))
    (entries : Model.Environment Address) (decl : KConst .anon) (type : AExpr Address) (level : VLevel) where
  check : SynthesisTypeCheck resolve entries type level
  source : check.source = decl.ty
  typeScoped : decl.ty.Scoped 0 decl.lvls.toNat

/-- The retained check of a classification member's actual inference call. -/
def MemberTypeRun.storedTypeCheck {member : KId .anon} {fuel : Nat} {before : TcState .anon}
    (run : MemberTypeRun member (methodsN fuel) before)
    {resolve : Address → Option (ConstRef Address)} {entries : Model.Environment Address}
    {type : AExpr Address} {level bound : VLevel}
    (tree : SynthesisInference resolve entries [] [] [] fuel run.validated run.concrete.ty type
      (.sort level) bound)
    (reading : readScopedExpr? resolve [] run.concrete.ty = some type.erase)
    {support : RunSupport} (coverage : run.concrete.ty.ValidationCoverage support)
    (collision : support.CollisionFree) :
    StoredTypeCheck resolve entries run.concrete type level where
  check :=
    { fuel, before := run.validated, after := run.typeState, source := run.concrete.ty,
      result := run.inferred, bound, inference := tree, reading, run := run.typeRun }
  source := rfl
  typeScoped := validateConst_type_scoped run.validationRun coverage collision

/-- The stored rules of a recursor block member are scoped by its validation. -/
theorem RecursorBlockTrace.rulesScoped {member : KId .anon} {methods : Methods .anon}
    {before : TcState .anon} (trace : RecursorBlockTrace member methods before)
    {name : Mode.anon.F Name} {levelParams : Mode.anon.F (Array Name)} {k isUnsafe : Bool}
    {lvls params indices motives minors : UInt64} {block : KId .anon} {memberIdx : UInt64}
    {ty : KExpr .anon} {rules : Array (Kernel.RecRule .anon)} {leanAll : Mode.anon.F (Array (KId .anon))}
    (concrete : trace.typeRun.concrete = KConst.recr name levelParams k isUnsafe lvls params indices
      motives minors block memberIdx ty rules leanAll)
    {support : RunSupport} (coverage : ∀ rule ∈ rules.toList, rule.rhs.ValidationCoverage support)
    (collision : support.CollisionFree) :
    ∀ rule ∈ rules.toList, rule.rhs.Scoped 0 lvls.toNat := by
  have h := trace.typeRun.validationRun
  rw [concrete] at h
  exact validateConst_rules_scoped h coverage collision

/-- The stored rules of a recursor declaration. -/
def storedRules : KConst .anon → List (Kernel.RecRule .anon)
  | .recr (rules := rules) .. => rules.toList
  | _ => []

/-! ### The run support -/

/-- Everything the admission theorem takes from the production runs: the
retained closed type checks of the stored family, every constructor, and the
recursor, and validation of the stored rules. -/
structure SingletonRunSupport (resolve : Address → Option (ConstRef Address))
    (entries : Model.Environment Address) (source recursor : Address) (family : KConst .anon)
    (ctors : List (KConst .anon)) (recr : KConst .anon) (shape : Shape Address) (mode : ElimMode) where
  familyLevel : VLevel
  familyCheck : StoredTypeCheck resolve entries family shape.type familyLevel
  constructorLevel : Nat → VLevel
  constructorCheck : ∀ (i : Nat) (ctor : Constructor Address) (decl : KConst .anon),
    shape.constructors[i]? = some ctor → ctors[i]? = some decl →
    StoredTypeCheck resolve (shape.familyEnvironment entries source) decl (ctor.type shape source)
      (constructorLevel i)
  recursorLevel : VLevel
  recursorCheck : StoredTypeCheck resolve (shape.constructorEnvironment entries source) recr
    (shape.recursorType source mode) recursorLevel
  rulesScoped : ∀ rule ∈ storedRules recr, rule.rhs.Scoped 0 recr.lvls.toNat

section

variable {resolve : Address → Option (ConstRef Address)} {entries : Model.Environment Address}
  {source recursor : Address} {family : KConst .anon} {ctors : List (KConst .anon)}
  {recr : KConst .anon} {shape : Shape Address} {mode : ElimMode}

def SingletonRunSupport.checks
    (R : SingletonRunSupport resolve entries source recursor family ctors recr shape mode)
    (hlen : ctors.length = shape.constructors.length) :
    SingletonChecks resolve entries source recursor shape mode where
  familyLevel := R.familyLevel
  familyCheck := R.familyCheck.check
  constructorLevel := R.constructorLevel
  constructorCheck := fun i ctor hc =>
    match hd : ctors[i]? with
    | some decl => (R.constructorCheck i ctor decl hc hd).check
    | none => by
        exfalso
        have hlt : i < ctors.length := by
          rw [hlen]
          exact (List.getElem?_eq_some_iff.mp hc).1
        rw [List.getElem?_eq_getElem hlt] at hd
        cases hd
  recursorLevel := R.recursorLevel
  recursorCheck := R.recursorCheck.check

end

/-! ### Scope from the witness readings -/

theorem recursorSourceCheck_block {resolve : Address → Option (ConstRef Address)}
    {shape : Shape Address} {source recursor : Address} {mode : ElimMode} {recr : KConst .anon}
    (check : recursorSourceCheck resolve shape source recursor mode recr = true) :
    ∃ k, recursorBlock? resolve recr = some ⟨[shape.recursorSource source recursor mode k]⟩ := by
  cases recr
  case recr name levelParams k isUnsafe lvls params indices motives minors block memberIdx ty rules leanAll =>
      simp only [recursorSourceCheck, Bool.and_eq_true, decide_eq_true_eq] at check
      exact ⟨k, check.1⟩
  all_goals simp [recursorSourceCheck] at check

theorem recursorBlock?_some {resolve : Address → Option (ConstRef Address)} {recr : KConst .anon}
    {block : Block Address} (h : recursorBlock? resolve recr = some block) :
    ∃ name levelParams k lvls params indices motives minors rblock memberIdx ty rules leanAll,
      recr = KConst.recr name levelParams k false lvls params indices motives minors rblock memberIdx ty
        rules leanAll ∧
      recursorBlockOf? resolve k lvls params indices motives minors ty rules.toList = some block := by
  unfold recursorBlock? at h
  split at h
  next name levelParams k lvls params indices motives minors rblock memberIdx ty rules leanAll =>
    exact ⟨name, levelParams, k, lvls, params, indices, motives, minors, rblock, memberIdx, ty, rules,
      leanAll, rfl, h⟩
  · contradiction

section

variable {resolve : Address → Option (ConstRef Address)} {entries : Model.Environment Address}
  {source recursor : Address} {family : KConst .anon} {ctors : List (KConst .anon)}
  {recr : KConst .anon} {shape : Shape Address} {mode : ElimMode}

/-- Scope of every stored type and rule follows from validation of the stored
declarations and their readings to the certified syntax. -/
theorem SingletonRunSupport.scope
    (R : SingletonRunSupport resolve entries source recursor family ctors recr shape mode)
    (check : singletonWitnessCheck resolve source recursor family ctors recr shape mode = true) :
    SingletonScope source recursor shape mode := by
  obtain ⟨hfam, hrec, _, hmode, hcondFamily, hcondCtors, _, hcondRec, hcondRules⟩ :=
    singletonWitnessCheck_sound check
  obtain ⟨lvls, params, ty, ctorIds, block, memberIdx, leanAll, name, levelParams, hfamily, hlvls,
    _, _, hreading, hlen, hctors⟩ := familyBlock?_family hfam
  have familyScoped := R.familyCheck.typeScoped
  rw [hfamily] at familyScoped
  change ty.Scoped 0 lvls.toNat at familyScoped
  rw [hlvls] at familyScoped
  obtain ⟨k, hblock⟩ := recursorSourceCheck_block hrec
  obtain ⟨rname, rlevelParams, k', rlvls, rparams, rindices, rmotives, rminors, rblock, rmemberIdx, rty,
    rules, rleanAll, hrecr, hof⟩ := recursorBlock?_some hblock
  obtain ⟨type, ruleDecls, htype, hrules, hblockEq⟩ := recursorBlockOf?_recursor hof
  simp only [Shape.recursorSource, Block.mk.injEq, List.cons.injEq, and_true,
    Const.recursor.injEq] at hblockEq
  obtain ⟨hrlvls, _, _, _, _, htypeEq, hrulesEq, _⟩ := hblockEq
  have hrecUvars : rlvls.toNat = mode.recUvars shape.universes := by
    have := modeOf_recUvars hmode
    rw [hfamily, hrecr] at this
    change rlvls.toNat = mode.recUvars lvls.toNat at this
    rw [this, hlvls]
  have recursorScoped := R.recursorCheck.typeScoped
  rw [hrecr] at recursorScoped
  change rty.Scoped 0 rlvls.toNat at recursorScoped
  rw [hrecUvars] at recursorScoped
  refine ⟨readScopedExpr?_annotated_scope hreading familyScoped hcondFamily, ?_,
    readScopedExpr?_annotated_scope (by rw [htype, htypeEq]) recursorScoped hcondRec, ?_⟩
  · intro ctor hmem
    obtain ⟨i, hc⟩ := List.mem_iff_getElem?.mp hmem
    obtain ⟨decl, hd, hread⟩ := hctors i ctor hc
    obtain ⟨cty, fields, induct, cidx, cname, clevelParams, hdecl, _, hcreading⟩ := readCtor?_source hread
    have ctorScoped := (R.constructorCheck i ctor decl hc hd).typeScoped
    rw [hdecl] at ctorScoped
    change cty.Scoped 0 lvls.toNat at ctorScoped
    rw [hlvls] at ctorScoped
    exact readScopedExpr?_annotated_scope hcreading ctorScoped (hcondCtors ctor hmem)
  · intro i ctor hc
    have hdecl : ruleDecls[i]? = some ⟨ctor.fields.length + ctor.recursive.length,
        (shape.ruleRhs source recursor mode i ctor).erase⟩ := by
      rw [← hrulesEq]
      simp only [List.getElem?_map, List.getElem?_zipIdx, hc, Option.map_some, Nat.zero_add]
    obtain ⟨hlenRules, hforward⟩ := mapM_some hrules
    have hlt : i < rules.toList.length := by
      rw [← hlenRules]
      exact (List.getElem?_eq_some_iff.mp hdecl).1
    obtain ⟨read, hread, hrule⟩ := hforward i rules.toList[i] (List.getElem?_eq_getElem hlt)
    rw [hdecl] at hread
    cases hread
    unfold readRule? at hrule
    obtain ⟨rhs, hrhs, hrhsEq⟩ := Option.map_eq_some_iff.mp hrule
    simp only [Theory.RecRule.mk.injEq] at hrhsEq
    have ruleScoped := R.rulesScoped rules.toList[i] (by rw [hrecr]; exact List.getElem_mem hlt)
    rw [hrecr] at ruleScoped
    change (rules.toList[i]).rhs.Scoped 0 rlvls.toNat at ruleScoped
    rw [hrecUvars] at ruleScoped
    exact readScopedExpr?_annotated_scope (by rw [hrhs, hrhsEq.2]) ruleScoped (hcondRules i ctor hc)

/-- Admission of a singleton block from its production runs: the certified
block condition and the published model extension. -/
theorem singleton_admission {store : Store Address}
    (check : singletonWitnessCheck resolve source recursor family ctors recr shape mode = true)
    (I : SingletonInterface resolve entries store source recursor family ctors recr shape mode)
    (R : SingletonRunSupport resolve entries source recursor family ctors recr shape mode)
    (seams : InductiveSeamAssumptions.{v} entries source recursor shape mode) :
    CheckedBlock.{0,v} entries store source recursor shape mode ∧
      (shape.publishedEnvironment entries source recursor mode).WF ∧
      ∀ (V : Type v) [SetTheory V] (constants : Assignment Address V), Realizes constants entries →
        Realizes (shape.recursorAssignment constants source recursor mode)
          (shape.publishedEnvironment entries source recursor mode) ∧
        Assignment.AgreesOn entries constants (shape.recursorAssignment constants source recursor mode) := by
  obtain ⟨hfam, _⟩ := singletonWitnessCheck_sound check
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hlen, _⟩ := familyBlock?_family hfam
  exact ⟨singleton_checkedBlock check I (R.scope check) (R.checks hlen) seams,
    singleton_published check I (R.scope check) (R.checks hlen) seams⟩

end

end Ix.Kernel.Consistency.Inductive
