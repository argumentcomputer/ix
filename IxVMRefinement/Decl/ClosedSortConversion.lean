import IxVMRefinement.Decl.NativeWrapperCoherence

/-! # Sort agreement through checked normalization

A typed comparison and an actual reduction are read in the same satisfying context.
For closed compared expressions an inhabited context of the required depth can always be
constructed. This equates universes without composing unchecked conversion derivations.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model Ix.Kernel.Semantics Ix.Kernel.SetModel Ix.Kernel.Term
open Ix.Kernel.Model.Rules (Frame)

universe u

/-- Actual checking and reduction identify sorts in a concrete satisfying frame. -/
theorem framed_checked_sort_levels {V : Type u} [SetTheory V] {md : Mode} {env : Env md}
    (model : EnvModelM V .verified env) {depth : Nat} {expression inferred : Expr md}
    {comparedSort reducedSort : Level}
    (typed : Rules.Infer env .full depth expression inferred)
    (reduced : Rules.Red env depth expression (.sort reducedSort))
    (compared : Rules.DefEq env depth (.sort comparedSort) expression)
    (expressionFrame : Frame depth expression)
    {φ : LevelParam → Nat} {context : List AnnotTerm} {ρ : Nat → V}
    (expressionContext : CtxOk model.base2 φ depth context expression)
    (satisfied : Sat V context ρ) : comparedSort.eval φ = reducedSort.eval φ := by
  have sortFrame : Frame depth (Expr.sort comparedSort : Expr md) := .of_not_hasFvar rfl rfl
  have sortContext : CtxOk model.base2 φ depth context (.sort comparedSort) :=
    CtxOk.of_fvarLeaves_nil expressionContext.length (Expr.fvarLeaves_eq_nil_of_not_hasFvar rfl)
  obtain ⟨reading, read⟩ := infer_reads model.base2 φ typed rfl expressionFrame.1 expressionFrame.2.1 expressionFrame.2.2
  have inputs := fun ψ => Ix.Kernel.Model.Rules.RulesInputs.ofSem model ψ
  obtain ⟨_, _, _, _, graded, _, _⟩ :=
    Ix.Kernel.Model.Rules.infer_sound inputs typed expressionFrame expressionContext read
  obtain ⟨_, _, reducedReading, reducedRead, _, reducedEqual⟩ :=
    Ix.Kernel.Model.Rules.red_sound inputs reduced expressionFrame expressionContext read graded
  rw [denoteMeta_sort] at reducedRead
  have reducedReadingEq := (Option.some.inj reducedRead).symm
  subst reducedReading
  have comparedEqual := Ix.Kernel.Model.Rules.defeq_sound inputs compared sortFrame expressionFrame
    sortContext expressionContext (denoteMeta_sort _ _ _) read (fun _ _ => ⟨trivial, trivial⟩) graded
  apply SetTheory.univ_inj (V := V)
  simpa only [interp_sort] using
    (comparedEqual _ satisfied).trans (reducedEqual _ satisfied)

/-- A sort compared with a closed, checked expression that reduces to a sort has the same level. -/
theorem closed_checked_sort_levels {V : Type u} [SetTheory V] {md : Mode} {env : Env md}
    (model : EnvModelM V .verified env) {depth : Nat} {expression inferred : Expr md}
    {comparedSort reducedSort : Level}
    (closed : expression.hasFvar = false) (bounded : expression.looseBVarsBounded 0 = true)
    (typed : Rules.Infer env .full depth expression inferred)
    (reduced : Rules.Red env depth expression (.sort reducedSort))
    (compared : Rules.DefEq env depth (.sort comparedSort) expression)
    (φ : LevelParam → Nat) : comparedSort.eval φ = reducedSort.eval φ := by
  let context : List AnnotTerm := List.replicate depth (.sort 0)
  have satisfied : Sat V context (fun _ => SetTheory.empty) := by
    intro i entry atIndex
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp (List.mem_of_getElem? atIndex)
    exact SetTheory.empty_mem_univ 0
  have expressionFrame : Frame depth expression := .of_not_hasFvar closed bounded
  have expressionContext : CtxOk model.base2 φ depth context expression :=
    CtxOk.of_fvarLeaves_nil (by simp only [context, List.length_replicate])
      (Expr.fvarLeaves_eq_nil_of_not_hasFvar closed)
  exact framed_checked_sort_levels model typed reduced compared expressionFrame expressionContext satisfied

/-- The actual checked comparison and reduction determine the canonical zero-ness datum. -/
theorem closed_checked_sort_zero {V : Type u} [SetTheory V] {md : Mode} {env : Env md}
    (model : EnvModelM V .verified env) {depth : Nat} {expression inferred : Expr md}
    {comparedSort reducedSort : Level}
    (closed : expression.hasFvar = false) (bounded : expression.looseBVarsBounded 0 = true)
    (typed : Rules.Infer env .full depth expression inferred)
    (reduced : Rules.Red env depth expression (.sort reducedSort))
    (compared : Rules.DefEq env depth (.sort comparedSort) expression) :
    Level.zeronessOf comparedSort = Level.zeronessOf reducedSort := by
  apply PropWhen.eq_of_holds
  intro φ
  rw [PropWhen.zeronessOf_sound, PropWhen.zeronessOf_sound,
    closed_checked_sort_levels model closed bounded typed reduced compared φ]

end IxVM.Refinement.Decl
