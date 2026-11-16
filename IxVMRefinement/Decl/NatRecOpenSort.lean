import IxVMRefinement.Decl.NatRecDomainMetadata

/-! # Sort comparison at the actual natural-number step opener

The successor minor's expected sort redex mentions only its natural-number opener. A
satisfying frame for that opener is constructed using the pinned zero value; unrelated
caller variables are absent from the comparison. No satisfiability of their original
context and no principal-sort property of semantic recursor laws is assumed.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model Ix.Kernel.Semantics Ix.Kernel.SetModel Ix.Kernel.Term
open Ix.Kernel.Model.Rules (Frame)

universe u

private theorem nat_successor_motive_typed {md : Mode} {env : Env md} {depth : Nat} {sortLevel : Level}
    (natFound : env.find? natName = some natA) (succFound : env.find? natSuccName = some natSuccA) :
    Rules.Infer env .full (depth + 2)
      (.app (natSortMotive sortLevel) (.app (.const natSuccName []) (.fvar depth (.const natName []))))
      (.sort (.succ sortLevel)) := by
  have successor : Rules.Infer env .full (depth + 2) (.const natSuccName [])
      (.forallE (.const natName []) (.const natName []) default) := Rules.Infer.const succFound rfl rfl
  have argument : Rules.Infer env .full (depth + 2) (.fvar depth (.const natName [])) (.const natName []) :=
    Rules.Infer.fvar (by omega)
  have successorArg := Rules.Infer.app successor .refl argument Rules.DefEq.refl
  exact Rules.Infer.app (natSortMotive_typed natFound) .refl successorArg Rules.DefEq.refl

/-- A sort compared with the constant motive at the successor of the actual Nat opener agrees
with the motive's result level. All required context facts are constructed from the Nat pins. -/
theorem nat_successor_motive_sort_levels {V : Type u} [SetTheory V] {md : Mode} {env : Env md}
    (model : EnvModelM V .verified env) {depth : Nat} {comparedSort sortLevel : Level}
    (natFound : env.find? natName = some natA)
    (zeroFound : env.find? natZeroName = some natZeroA)
    (succFound : env.find? natSuccName = some natSuccA)
    (compared : Rules.DefEq env (depth + 2) (.sort comparedSort)
      (.app (natSortMotive sortLevel) (.app (.const natSuccName []) (.fvar depth (.const natName [])))))
    (φ : LevelParam → Nat) : comparedSort.eval φ = sortLevel.eval φ := by
  let tailContext : List AnnotTerm := List.replicate depth (.sort 0)
  let tailValues : Nat → V := fun _ => SetTheory.empty
  let natReading := model.base2.acval natName (Level.substFn φ [] [])
  let beforeOpen : Expr md := .app (natSortMotive sortLevel) (.app (.const natSuccName []) (.bvar 0))
  have tailLength : tailContext.length = depth := by simp only [tailContext, List.length_replicate]
  have natRead : ∀ d, denoteMeta model.base2.acval env φ d (.const natName []) = some natReading :=
    fun _ => denoteMeta_const natFound rfl
  have natGraded : Ix.Kernel.Model.Rules.Graded V tailContext natReading := fun ρ _ =>
    ⟨model.base2.acval_wellDenoted _ _ ρ, model.acval_validV _ _ ρ⟩
  have bodyContext : CtxOk model.base2 φ depth tailContext beforeOpen :=
    CtxOk.of_fvarLeaves_nil tailLength (Expr.fvarLeaves_eq_nil_of_not_hasFvar rfl)
  have natContext : CtxOk model.base2 φ depth tailContext (.const natName []) :=
    CtxOk.of_fvarLeaves_nil tailLength (Expr.fvarLeaves_eq_nil_of_not_hasFvar rfl)
  have openedContext := CtxOk.open bodyContext natContext (natRead depth) natGraded
  have expressionContext : CtxOk model.base2 φ (depth + 2) (.sort 0 :: natReading :: tailContext)
      (.app (natSortMotive sortLevel) (.app (.const natSuccName []) (.fvar depth (.const natName [])))) := by
    simpa only [beforeOpen, natSortMotive, Expr.instantiate1] using
      (CtxOk.weakenTop (Ba := .sort 0) openedContext)
  have openedFrame := Frame.open_body (d := depth) (bd := beforeOpen) (ty' := .const natName [])
    (Frame.of_not_hasFvar rfl rfl) (Expr.WScoped.of_not_hasFvar rfl) (by rfl)
    (Expr.LeavesBounded.of_not_hasFvar rfl)
  have expressionFrame : Frame (depth + 2)
      (.app (natSortMotive sortLevel) (.app (.const natSuccName []) (.fvar depth (.const natName [])))) := by
    have lifted : Frame (depth + 2) (beforeOpen.instantiate1 (.fvar depth (.const natName []))) :=
      ⟨Expr.WScoped.mono (by omega) openedFrame.1, openedFrame.2⟩
    simpa only [beforeOpen, natSortMotive, Expr.instantiate1] using lifted
  have tailSatisfied : Sat V tailContext tailValues := by
    intro i entry atIndex
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp (List.mem_of_getElem? atIndex)
    exact SetTheory.empty_mem_univ 0
  have zeroMember := model.mem_type natZeroA (List.mem_of_find?_eq_some zeroFound) φ natReading (natRead 0) tailValues
  have natSatisfied := Sat_cons V tailSatisfied zeroMember
  have satisfied : Sat V (.sort 0 :: natReading :: tailContext)
      (cons SetTheory.empty (cons (interp V tailValues (model.base2.acval natZeroName φ)) tailValues)) :=
    Sat_cons V natSatisfied (SetTheory.empty_mem_univ 0)
  have reduced : Rules.Red env (depth + 2)
      (.app (natSortMotive sortLevel) (.app (.const natSuccName []) (.fvar depth (.const natName []))))
      (.sort sortLevel) := Rules.Red.betaGate rfl
  exact framed_checked_sort_levels model (nat_successor_motive_typed natFound succFound)
    reduced compared expressionFrame expressionContext satisfied

/-- The actual comparison at the natural-number step opener fixes the product datum. -/
theorem nat_successor_motive_sort_zero {V : Type u} [SetTheory V] {md : Mode} {env : Env md}
    (model : EnvModelM V .verified env) {depth : Nat} {comparedSort sortLevel : Level}
    (natFound : env.find? natName = some natA)
    (zeroFound : env.find? natZeroName = some natZeroA)
    (succFound : env.find? natSuccName = some natSuccA)
    (compared : Rules.DefEq env (depth + 2) (.sort comparedSort)
      (.app (natSortMotive sortLevel) (.app (.const natSuccName []) (.fvar depth (.const natName []))))) :
    Level.zeronessOf comparedSort = Level.zeronessOf sortLevel := by
  apply PropWhen.eq_of_holds
  intro φ
  rw [PropWhen.zeronessOf_sound, PropWhen.zeronessOf_sound,
    nat_successor_motive_sort_levels model natFound zeroFound succFound compared φ]

end IxVM.Refinement.Decl
