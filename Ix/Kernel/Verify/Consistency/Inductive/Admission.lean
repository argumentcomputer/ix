/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Inductive.Formation
import Ix.Theory.Certified.Ordinary.Checked

/-!
# Admission of singleton inductive blocks through the certified witness

The certified `Ordinary.CheckedBlock` proposition is exactly what
`Ordinary.checkBlock` establishes and what `checkOrdinaryExtension?` consumes.
Here it is derived for a singleton shape from: the decidable witness check on
the stored declarations, retained closed type checks of the stored family,
constructor, and recursor types (the inference calls production makes on
every stored member), validation-derived scope, interface freshness and
reference facts, and an explicit record of the remaining seams. The published
model extension then follows from the certified realization theorems.
-/

namespace Ix.Kernel.Consistency.Inductive

open Theory Theory.Model Theory.Model.SetTheory Theory.Certified Theory.Certified.Ordinary
  Theory.Inductive

universe u v

theorem referencesIn_forallN_iff {β : Type u} {entries : Model.Environment β} {p : PropWhen} :
    ∀ {domains : List (AExpr β)} {body : AExpr β},
      (AExpr.forallN p domains body).ReferencesIn entries ↔
        (∀ A ∈ domains, A.ReferencesIn entries) ∧ body.ReferencesIn entries
  | [], body => by simp [AExpr.forallN]
  | A :: rest, body => by
      simp only [AExpr.forallN, List.mem_cons, forall_eq_or_imp]
      constructor
      · intro h
        have hA : A.ReferencesIn entries := fun r hr => h r (List.mem_append_left _ hr)
        have ht : (AExpr.forallN p rest body).ReferencesIn entries :=
          fun r hr => h r (List.mem_append_right _ hr)
        obtain ⟨hrest, hbody⟩ := referencesIn_forallN_iff.mp ht
        exact ⟨⟨hA, hrest⟩, hbody⟩
      · rintro ⟨⟨hA, hrest⟩, hbody⟩
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hA r hr
        · exact (referencesIn_forallN_iff.mpr ⟨hrest, hbody⟩) r hr

/-! ### Seams -/

/-- Certified conditions of a singleton block not yet derived from the
production run. Each field records the sole reason it remains open. -/
structure InductiveSeamAssumptions (entries : Model.Environment Address) (source recursor : Address)
    (shape : Shape Address) (mode : ElimMode) : Prop where
  /-- Production's A4 check (`checkFieldUniverses`) bounds every field sort
  by the family level through a `whnf`-driven loop over the opened telescope;
  identifying its iterations with the shape's fields needs the WHNF Pi-leaf
  contract (WP4). -/
  fieldBounds : ∀ ctor ∈ shape.constructors,
    TelescopeBound.{0,v} entries shape.parameterContext ctor.fields (some shape.level)
  /-- The same A4 bound for the domains of a recursive field, whose sort is
  only checked by production as part of the whole field type. -/
  recursiveBounds : ∀ ctor ∈ shape.constructors, ∀ field ∈ ctor.recursive,
    TelescopeBound.{0,v} entries (ctor.context shape) field.domains (some shape.level)
  /-- A recursive field after an earlier recursive field: the retained check
  forms its domains under the earlier recursive binders, and removing those
  binders semantically needs their inhabitation. -/
  laterRecursiveDomains : ∀ ctor ∈ shape.constructors, ∀ (j : Nat) (field : RecursiveField Address),
    ctor.recursive[j]? = some field → 0 < j → field.domains ≠ [] →
    Telescope.Formed.{0,v} entries (ctor.context shape) field.domains
  /-- Large elimination from a proposition with one constructor and ordinary
  fields: production decides it with inference-only field sorts
  (`isLargeEliminator`), whose contract is WP2. -/
  largeElimination : mode = .large → zeroCondition shape.level ≠ .never → shape.constructors ≠ [] →
    ¬ (∃ ctor, shape.constructors = [ctor] ∧ ctor.fields = []) → LargeEvidence.{0,v} entries shape
  /-- Production never types recursor rules: it compares the stored right-hand
  sides with the regenerated ones by definitional equality. The certified rule
  typing is only consumed by small-elimination proof irrelevance. -/
  ruleTyping : ∀ (i : Nat) (ctor : Constructor Address), shape.constructors[i]? = some ctor →
    (∃ l, TypingClaim.{0,v} (shape.recursorEnvironment entries source recursor mode) []
        (shape.ruleType source mode i ctor) (.sort l) ∧ (mode = .small → ∀ levels, l.eval levels = 0)) ∧
      TypingClaim.{0,v} (shape.recursorEnvironment entries source recursor mode) []
        (shape.ruleLhs source recursor mode i ctor) (shape.ruleType source mode i ctor) ∧
      TypingClaim.{0,v} (shape.recursorEnvironment entries source recursor mode) []
        (shape.ruleRhs source recursor mode i ctor) (shape.ruleType source mode i ctor)

/-! ### Interface, scope, and retained checks -/

/-- Interface facts about the preceding model environment and the store view. -/
structure SingletonInterface (resolve : Address → Option (ConstRef Address))
    (entries : Model.Environment Address) (store : Store Address) (source recursor : Address)
    (family : KConst .anon) (ctors : List (KConst .anon)) (recr : KConst .anon)
    (shape : Shape Address) (mode : ElimMode) : Prop where
  wf : entries.WF
  familyStored : store.blocks source = familyBlock? resolve family ctors
  recursorStored : store.blocks recursor = recursorBlock? resolve recr
  fresh : ∀ r ∈ shape.references source, entries r = none
  recursorFresh : entries (.member recursor 0) = none
  distinct : recursor ≠ source
  familyRefs : shape.type.ReferencesIn entries
  constructorRefs : ∀ ctor ∈ shape.constructors,
    (ctor.type shape source).ReferencesIn (shape.familyEnvironment entries source)
  recursorRefs : (shape.recursorType source mode).ReferencesIn (shape.constructorEnvironment entries source)
  ruleRefs : ∀ (i : Nat) (ctor : Constructor Address), shape.constructors[i]? = some ctor →
    (shape.ruleRhs source recursor mode i ctor).ReferencesIn
      (shape.recursorEnvironment entries source recursor mode)

/-- Scope of every stored type and rule, as established by production
validation of the stored declarations. -/
structure SingletonScope (source recursor : Address) (shape : Shape Address) (mode : ElimMode) : Prop where
  familyScope : shape.type.Scope shape.universes 0
  constructorScope : ∀ ctor ∈ shape.constructors, (ctor.type shape source).Scope shape.universes 0
  recursorScope : (shape.recursorType source mode).Scope (mode.recUvars shape.universes) 0
  ruleScope : ∀ (i : Nat) (ctor : Constructor Address), shape.constructors[i]? = some ctor →
    (shape.ruleRhs source recursor mode i ctor).Scope (mode.recUvars shape.universes) 0

/-- The retained closed type checks of the stored family, constructor, and
recursor types, each over the interface production checks it against. -/
structure SingletonChecks (resolve : Address → Option (ConstRef Address))
    (entries : Model.Environment Address) (source recursor : Address) (shape : Shape Address)
    (mode : ElimMode) where
  familyLevel : VLevel
  familyCheck : SynthesisTypeCheck resolve entries shape.type familyLevel
  constructorLevel : Nat → VLevel
  constructorCheck : ∀ (i : Nat) (ctor : Constructor Address), shape.constructors[i]? = some ctor →
    SynthesisTypeCheck resolve (shape.familyEnvironment entries source) (ctor.type shape source)
      (constructorLevel i)
  recursorLevel : VLevel
  recursorCheck : SynthesisTypeCheck resolve (shape.constructorEnvironment entries source)
    (shape.recursorType source mode) recursorLevel

/-! ### Derived formation facts -/

section Derived

variable {resolve : Address → Option (ConstRef Address)} {entries : Model.Environment Address}
  {source recursor : Address} {shape : Shape Address} {mode : ElimMode}

theorem SingletonChecks.parametersFormed (C : SingletonChecks resolve entries source recursor shape mode) :
    Telescope.Formed.{0,v} entries [] shape.parameters :=
  (formed_append_inv ((telescopeChecks (p := .never)
    (shape.parameters ++ shape.indices) (B := .sort shape.level) (closedScoped C.familyCheck)).1.formed
    (ContextFormation.empty entries))).1

/-- The parameter, field, and recursive telescopes of one constructor, as
checked by its retained closed type check. -/
theorem SingletonChecks.constructorTelescopes
    (C : SingletonChecks resolve entries source recursor shape mode) {i : Nat}
    {ctor : Constructor Address} (hc : shape.constructors[i]? = some ctor) :
    Telescope.Formed.{0,v} (shape.familyEnvironment entries source) shape.parameterContext ctor.fields ∧
      ∀ (j : Nat) (field : RecursiveField Address), ctor.recursive[j]? = some field → j = 0 →
        Telescope.Formed.{0,v} (shape.familyEnvironment entries source) (ctor.context shape)
          field.domains := by
  let check := closedScoped (C.constructorCheck i ctor hc)
  let params := telescopeChecks (p := zeroCondition shape.level) shape.parameters
    (B := AExpr.forallN (zeroCondition shape.level) ctor.fields
      (AExpr.forallN (zeroCondition shape.level) (ctor.recursiveTypes shape source)
        (shape.familyApp source (ctor.fields.length + ctor.recursive.length)
          (ctor.indices.map (AExpr.liftN ctor.recursive.length ·))))) check
  let fields := telescopeChecks (p := zeroCondition shape.level) ctor.fields params.2.val
  have hfields := fields.1.formed (ContextFormation.empty _)
  have hparamsCtx : params.2.val.context = shape.parameterContext := params.2.property
  refine ⟨hparamsCtx ▸ hfields, ?_⟩
  intro j field hf hj
  subst hj
  let recursive := telescopeChecks (p := zeroCondition shape.level)
    (ctor.recursiveTypes shape source) fields.2.val
  have hfirst : (ctor.recursiveTypes shape source)[0]? = some ((field.type shape source ctor.fields.length).liftN 0) := by
    simp [Constructor.recursiveTypes, Ordinary.recursiveTypesFrom, hf]
  obtain ⟨found, hfound⟩ := recursive.1.get 0 _ hfirst
  have hlift : (field.type shape source ctor.fields.length).liftN 0 = field.type shape source ctor.fields.length :=
    AExpr.liftN_zero _ _
  let found' := retypeCheck hlift found
  have hfound' : found'.context = fields.2.val.context := by
    rw [retypeCheck_context, hfound]
    rfl
  let domains := telescopeChecks (p := zeroCondition shape.level) field.domains
    (B := shape.familyApp source (ctor.fields.length + field.domains.length) field.indices) found'
  have hdomains := domains.1.formed (ContextFormation.empty _)
  have hctx : found'.context = ctor.context shape := by
    rw [hfound', fields.2.property, hparamsCtx]
    rfl
  exact hctx ▸ hdomains

end Derived

/-! ### The certified block -/

section Block

variable {resolve : Address → Option (ConstRef Address)} {entries : Model.Environment Address}
  {store : Store Address} {source recursor : Address} {family : KConst .anon}
  {ctors : List (KConst .anon)} {recr : KConst .anon} {shape : Shape Address} {mode : ElimMode}

theorem largeEvidence_of_syntax
    (seams : InductiveSeamAssumptions.{v} entries source recursor shape mode) (hmode : mode = .large) :
    LargeEvidence.{0,v} entries shape := by
  by_cases hz : zeroCondition shape.level = .never
  · left
    intro levels he
    have hc := zeroCondition_correct shape.level levels
    simp only [hz, PropWhen.holds_never, he, beq_self_eq_true, Bool.false_eq_true] at hc
  by_cases hempty : shape.constructors = []
  · exact Or.inr (Or.inl hempty)
  by_cases hone : ∃ ctor, shape.constructors = [ctor] ∧ ctor.fields = []
  · obtain ⟨ctor, hsingle, hfields⟩ := hone
    refine Or.inr (Or.inr ⟨ctor, hsingle, ?_⟩)
    rw [hfields]
    exact TelescopeProp.nil _ _ _
  exact seams.largeElimination hmode hz hempty hone

theorem singleton_checkedShape
    (check : singletonWitnessCheck resolve source recursor family ctors recr shape mode = true)
    (I : SingletonInterface resolve entries store source recursor family ctors recr shape mode)
    (S : SingletonScope source recursor shape mode)
    (C : SingletonChecks resolve entries source recursor shape mode)
    (seams : InductiveSeamAssumptions.{v} entries source recursor shape mode) :
    CheckedShape.{0,v} entries store source shape := by
  obtain ⟨hfam, _, hsingle, _, _, _, hmention, _, _⟩ := singletonWitnessCheck_sound check
  have hparams : Telescope.Formed.{0,v} entries [] shape.parameters := C.parametersFormed
  have hparamRefs : ∀ A ∈ shape.parameters, A.ReferencesIn entries := by
    have := (referencesIn_forallN_iff.mp (show (AExpr.forallN .never (shape.parameters ++ shape.indices)
      (.sort shape.level)).ReferencesIn entries from I.familyRefs)).1
    exact fun A hA => this A (List.mem_append_left _ hA)
  have hfamilyFresh : entries (.member source 0) = none := I.fresh _ (List.mem_cons_self ..)
  have realizable := family_realizable.{0,v} hsingle.1 S.familyScope I.familyRefs hfamilyFresh hparams
  have hparamCtx : ContextRefs entries shape.parameterContext :=
    ContextRefs.context shape.parameters (ContextRefs.nil entries) hparamRefs
  refine ⟨by rw [I.familyStored, hfam], I.fresh, ?_, S.familyScope, S.constructorScope, hparams,
    by rw [hsingle.1]; exact .nil, ?_⟩
  · intro A hA
    rcases List.mem_append.mp hA with hA | hA
    · exact hparamRefs A hA
    · rw [hsingle.1] at hA
      simp at hA
  · intro ctor hmem
    obtain ⟨i, hc⟩ := List.mem_iff_getElem?.mp hmem
    obtain ⟨hci, hrec⟩ := hsingle.2 ctor hmem
    obtain ⟨hfieldsNo, hdomainsNo⟩ := hmention ctor hmem
    have hrefs := I.constructorRefs ctor hmem
    obtain ⟨_, hrefs⟩ := referencesIn_forallN_iff.mp
      (show (AExpr.forallN (zeroCondition shape.level) shape.parameters _).ReferencesIn
        (shape.familyEnvironment entries source) from hrefs)
    obtain ⟨hfieldRefs, hrefs⟩ := referencesIn_forallN_iff.mp hrefs
    obtain ⟨hrecRefs, _⟩ := referencesIn_forallN_iff.mp hrefs
    have hfieldRefs' : ∀ A ∈ ctor.fields, A.ReferencesIn entries := fun A hA =>
      referencesIn_insert_inv (hfieldRefs A hA) (hfieldsNo A hA)
    obtain ⟨hfieldsFormed, hrecursiveFormed⟩ := C.constructorTelescopes hc
    refine ⟨?_, formed_of_insert I.wf hfamilyFresh realizable hfieldsFormed hparamCtx hfieldRefs',
      seams.fieldBounds ctor hmem, by rw [hsingle.1, hci]; exact ArgumentsFit.nil _ _, ?_⟩
    · intro A hA
      rcases List.mem_append.mp hA with hA | hA
      · exact hfieldRefs' A hA
      · rw [hci] at hA
        simp at hA
    · intro field hfield
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hfield
      have hfi := hrec field hfield
      have hdomainRefs : ∀ A ∈ field.domains, A.ReferencesIn entries := by
        intro A hA
        have hin : (field.type shape source ctor.fields.length).liftN j ∈ ctor.recursiveTypes shape source := by
          apply List.mem_of_getElem? (i := j)
          simp [Constructor.recursiveTypes, Ordinary.recursiveTypesFrom, hj]
        have htype := hrecRefs _ hin
        have htype' : (field.type shape source ctor.fields.length).ReferencesIn
            (shape.familyEnvironment entries source) := by
          intro r hr
          exact htype r (by rw [references_liftN]; exact hr)
        obtain ⟨hdomains, _⟩ := referencesIn_forallN_iff.mp
          (show (AExpr.forallN (zeroCondition shape.level) field.domains _).ReferencesIn
            (shape.familyEnvironment entries source) from htype')
        exact referencesIn_insert_inv (hdomains A hA) (hdomainsNo field hfield A hA)
      have hctorCtx : ContextRefs entries (ctor.context shape) :=
        ContextRefs.context ctor.fields hparamCtx hfieldRefs'
      refine ⟨?_, ?_, seams.recursiveBounds ctor hmem field hfield,
        by rw [hsingle.1, hfi]; exact ArgumentsFit.nil _ _⟩
      · intro A hA
        rcases List.mem_append.mp hA with hA | hA
        · exact hdomainRefs A hA
        · rw [hfi] at hA
          simp at hA
      · by_cases hempty : field.domains = []
        · rw [hempty]
          exact .nil
        · cases j with
          | zero =>
              exact formed_of_insert I.wf hfamilyFresh realizable
                (hrecursiveFormed 0 field hj rfl) hctorCtx hdomainRefs
          | succ j =>
              exact seams.laterRecursiveDomains ctor hmem (j + 1) field hj (Nat.succ_pos j) hempty

/-- The certified block condition for a singleton family, its constructors,
and its stored canonical recursor. -/
theorem singleton_checkedBlock
    (check : singletonWitnessCheck resolve source recursor family ctors recr shape mode = true)
    (I : SingletonInterface resolve entries store source recursor family ctors recr shape mode)
    (S : SingletonScope source recursor shape mode)
    (C : SingletonChecks resolve entries source recursor shape mode)
    (seams : InductiveSeamAssumptions.{v} entries source recursor shape mode) :
    CheckedBlock.{0,v} entries store source recursor shape mode := by
  obtain ⟨_, hrec, hsingle, _, _, _, _, _, _⟩ := singletonWitnessCheck_sound check
  refine ⟨singleton_checkedShape check I S C seams, ?_, ?_, ?_, ?_⟩
  · intro ctor hmem
    obtain ⟨i, hc⟩ := List.mem_iff_getElem?.mp hmem
    refine ⟨⟨S.constructorScope ctor hmem, by simp [Shape.constructorEntry], I.constructorRefs ctor hmem,
      by simp [Shape.constructorEntry], by simp [Shape.constructorEntry],
      by simp [Shape.constructorEntry], by simp [Shape.constructorEntry],
      by simp [Shape.constructorEntry]⟩, C.constructorLevel i, (C.constructorCheck i ctor hc).sound⟩
  · refine ⟨recursorSourceCheck_sound hrec I.recursorStored, ?_,
      ⟨S.recursorScope, by simp [Shape.recursorEntry], I.recursorRefs, by simp [Shape.recursorEntry],
        by simp [Shape.recursorEntry], by simp [Shape.recursorEntry], by simp [Shape.recursorEntry],
        by simp [Shape.recursorEntry]⟩, C.recursorLevel, C.recursorCheck.sound⟩
    simp [Shape.constructorEnvironment, Environment.overlay, Shape.constructorEntries,
      Shape.familyEnvironment, Environment.insert, I.distinct, I.recursorFresh]
  · cases mode with
    | small => trivial
    | large => exact largeEvidence_of_syntax seams rfl
  · intro i ctor hc
    have hci : ctor.indices = [] := (hsingle.2 ctor (List.mem_of_getElem? hc)).1
    obtain ⟨htype, hlhs, hrhs⟩ := seams.ruleTyping i ctor hc
    exact ⟨⟨ruleLhs_scope hci (S.ruleScope i ctor hc), S.ruleScope i ctor hc⟩,
      ⟨ruleLhs_referencesIn hci hc (I.ruleRefs i ctor hc), I.ruleRefs i ctor hc⟩, htype, hlhs, hrhs⟩

/-- The published environment is well formed, and every model of the
preceding interface extends to a model of the published one that keeps all
earlier interpretations. -/
theorem singleton_published
    (check : singletonWitnessCheck resolve source recursor family ctors recr shape mode = true)
    (I : SingletonInterface resolve entries store source recursor family ctors recr shape mode)
    (S : SingletonScope source recursor shape mode)
    (C : SingletonChecks resolve entries source recursor shape mode)
    (seams : InductiveSeamAssumptions.{v} entries source recursor shape mode) :
    (shape.publishedEnvironment entries source recursor mode).WF ∧
      ∀ (V : Type v) [SetTheory V] (constants : Assignment Address V), Realizes constants entries →
        Realizes (shape.recursorAssignment constants source recursor mode)
          (shape.publishedEnvironment entries source recursor mode) ∧
        Assignment.AgreesOn entries constants (shape.recursorAssignment constants source recursor mode) := by
  have checked := singleton_checkedBlock check I S C seams
  refine ⟨Shape.publishedEnvironment_wf checked I.wf, ?_⟩
  intro V _ constants hM
  exact ⟨Shape.publishedAssignment_realizes checked I.wf constants hM,
    Shape.publishedAssignment_agrees checked constants⟩

end Block

end Ix.Kernel.Consistency.Inductive
