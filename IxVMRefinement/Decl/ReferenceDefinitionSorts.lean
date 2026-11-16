import IxVMRefinement.Decl.ReferenceDefinitionTyping
import IxC.Kernel.Model.Rules.DefEqSoundKit

/-! # Sort agreement from actual definition fronts

A model's membership fact alone does not fix a universe. The conversion retained from
an actual definition check equates the two type readings instead. When those readings are
sorts, injectivity of the universe tower determines their levels and their zero-ness.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model Ix.Kernel.Semantics Ix.Kernel.SetModel Ix.Kernel.Term
open Ix.Kernel.Model.Rules (Frame)

universe u

/-- Conversion between two sorts equates their universe levels at every valuation. -/
theorem converted_sort_levels {V : Type u} [SetTheory V] {md : Mode} {env : Env md}
    (model : EnvModelM V .verified env) {left right : Level}
    (converted : Ix.Kernel.Rules.DefEq env 0 (.sort left) (.sort right))
    (φ : LevelParam → Nat) : left.eval φ = right.eval φ := by
  have leftFrame : Frame 0 (Expr.sort left : Expr md) := .of_not_hasFvar rfl rfl
  have rightFrame : Frame 0 (Expr.sort right : Expr md) := .of_not_hasFvar rfl rfl
  have leftContext : CtxOk model.base2 φ 0 [] (.sort left) := CtxOk.nil (Expr.fvarLeaves_eq_nil_of_not_hasFvar rfl)
  have rightContext : CtxOk model.base2 φ 0 [] (.sort right) := CtxOk.nil (Expr.fvarLeaves_eq_nil_of_not_hasFvar rfl)
  have equal := Ix.Kernel.Model.Rules.defeq_sound (φ := φ)
    (fun ψ => Ix.Kernel.Model.Rules.RulesInputs.ofSem model ψ) converted
    leftFrame rightFrame leftContext rightContext (denoteMeta_sort _ _ _) (denoteMeta_sort _ _ _)
    (fun _ _ => ⟨trivial, trivial⟩) (fun _ _ => ⟨trivial, trivial⟩)
  apply SetTheory.univ_inj (V := V)
  simpa only [interp_sort] using equal (fun _ => SetTheory.empty) (Sat_nil V _)

/-- The same actual conversion fixes the canonical zero-ness datum. -/
theorem converted_sort_zero {V : Type u} [SetTheory V] {md : Mode} {env : Env md}
    (model : EnvModelM V .verified env) {left right : Level}
    (converted : Ix.Kernel.Rules.DefEq env 0 (.sort left) (.sort right)) :
    Level.zeronessOf left = Level.zeronessOf right := by
  apply PropWhen.eq_of_holds
  intro φ
  rw [PropWhen.zeronessOf_sound, PropWhen.zeronessOf_sound, converted_sort_levels model converted φ]

/-- A checked definition whose value is a constant type cannot claim a different sort.
Both lookups are actual rows in the current reference prefix. -/
theorem DefinitionsTyped.constant_alias_sort {V : Type u} [SetTheory V] {env : Env .anon}
    (model : EnvModelM V .verified env) (typed : DefinitionsTyped env)
    {name bodyName : Key .anon} {cv : ConstantVal .anon} {body : ConstantInfo .anon}
    {levels : List Level} {hint : ReducibilityHint} {declared actual : Level}
    (aliasFound : env.find? name = some (.defnInfo cv (.const bodyName levels) hint))
    (bodyFound : env.find? bodyName = some body)
    (header : cv.type = .sort declared)
    (bodyHeader : body.toConstantVal.type.instantiateLevelParams body.toConstantVal.levelParams levels =
      .sort actual) :
    (∀ φ : LevelParam → Nat, declared.eval φ = actual.eval φ) ∧
      Level.zeronessOf declared = Level.zeronessOf actual := by
  obtain ⟨_, _, valueType, _, _, inferred, converted, _, _⟩ := typed name cv (.const bodyName levels) hint aliasFound
  obtain ⟨foundBody, found, _, _, typeEq⟩ := Ix.Kernel.Rules.Infer.const_inv inferred
  have same : foundBody = body := Option.some.inj (found.symm.trans bodyFound)
  subst foundBody
  rw [typeEq, bodyHeader, header] at converted
  exact ⟨fun φ => (converted_sort_levels model converted φ).symm, (converted_sort_zero model converted).symm⟩

/-- A checked definition whose value is a product retains its product's zero-ness datum. -/
theorem DefinitionsTyped.forall_alias_zero {V : Type u} [SetTheory V] {env : Env .anon}
    (model : EnvModelM V .verified env) (typed : DefinitionsTyped env)
    {name : Key .anon} {cv : ConstantVal .anon} {domain body : Expr .anon} {binderMeta : BinderMeta}
    {hint : ReducibilityHint} {declared : Level}
    (found : env.find? name = some (.defnInfo cv (.forallE domain body binderMeta) hint))
    (header : cv.type = .sort declared) : Level.zeronessOf declared = binderMeta.pw := by
  obtain ⟨_, _, valueType, _, _, inferred, converted, _, _⟩ := typed name cv _ hint found
  obtain ⟨_, domainLevel, _, bodyLevel, _, _, _, _, bodyZero, typeEq⟩ :=
    Ix.Kernel.Rules.Infer.forallE_inv inferred
  rw [typeEq, header] at converted
  exact (converted_sort_zero model converted).symm.trans bodyZero

end IxVM.Refinement.Decl
