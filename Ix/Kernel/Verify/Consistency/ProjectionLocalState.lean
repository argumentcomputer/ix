/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.InferenceLocalState

/-!
# Local-state preservation by projection inference

The production parameter and field traversals preserve the caller's locals,
allocation bound and installed loader, on both success and partial failure.
The proof includes inductive result-sort classification, dependent field
substitution and Prop elimination checks. Recursive inference and direct
WHNF remain the smaller method contracts; lookup and universe-instantiation
effects are derived from the maintained local-state invariant.

This closes the projection premise of the general inference state frame.
Projection typing and the model interpretation of inductive declarations
remain separate semantic obligations.
-/

namespace Ix.Kernel.Consistency.FramesLocalState

private theorem forInList {methods : Methods .anon} (items : List α) (initial : β)
    (step : α → β → RecM .anon (ForInStep β))
    (framed : ∀ item value, FramesLocalState ((step item value).run methods)) :
    FramesLocalState ((forIn items initial step).run methods) := by
  induction items generalizing initial with
  | nil => exact pure _
  | cons item rest ih =>
      rw [List.forIn_cons]
      simp only [ReaderT.run_bind]
      apply bind (framed item initial)
      intro next
      cases next with
      | done value => exact pure _
      | yield value => exact ih value

private theorem forInRange {methods : Methods .anon} (range : Std.Legacy.Range) (initial : α)
    (step : Nat → α → RecM .anon (ForInStep α))
    (framed : ∀ index value, FramesLocalState ((step index value).run methods)) :
    FramesLocalState ((forIn range initial step).run methods) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact forInList _ _ _ framed

theorem peelProjForall {methods : Methods .anon}
    (whnf : ∀ term, FramesLocalState ((RecM.whnf term).run methods))
    (type : KExpr .anon) (error : String) :
    FramesLocalState ((RecM.peelProjForall type error).run methods) := by
  cases type <;> simp only [RecM.peelProjForall, ReaderT.run_bind]
  case all => exact pure _
  all_goals
    apply bind (whnf _)
    intro result
    cases result <;> first | exact pure _ | exact throw _

theorem instantiateProjParamStep {methods : Methods .anon}
    (whnf : ∀ term, FramesLocalState ((RecM.whnf term).run methods))
    (args : Array (KExpr .anon)) (index : Nat) (type : KExpr .anon) :
    FramesLocalState ((RecM.instantiateProjParamStep args index type).run methods) := by
  unfold RecM.instantiateProjParamStep
  simp only [ReaderT.run_bind]
  apply bind (peelProjForall whnf _ _)
  intro pair
  split
  · exact bind (runIntern _) (fun _ => pure _)
  · exact throw _

theorem instantiateProjParams {methods : Methods .anon}
    (whnf : ∀ term, FramesLocalState ((RecM.whnf term).run methods))
    (args : Array (KExpr .anon)) (numParams : Nat) (type : KExpr .anon) :
    FramesLocalState ((RecM.instantiateProjParams args numParams type).run methods) :=
  forInRange _ _ _ (instantiateProjParamStep whnf args)

theorem inductiveAppBinderStep {methods : Methods .anon}
    (whnf : ∀ term, FramesLocalState ((RecM.whnf term).run methods))
    (type : KExpr .anon) :
    FramesLocalState ((RecM.inductiveAppBinderStep type).run methods) := by
  unfold RecM.inductiveAppBinderStep
  simp only [ReaderT.run_bind]
  apply bind (whnf type)
  intro result
  cases result <;> first | exact pure _ | exact throw _

theorem inductiveAppBinders {methods : Methods .anon}
    (whnf : ∀ term, FramesLocalState ((RecM.whnf term).run methods))
    (binders : Nat) (type : KExpr .anon) :
    FramesLocalState ((RecM.inductiveAppBinders binders type).run methods) :=
  forInRange _ _ _ (fun _ => inductiveAppBinderStep whnf)

theorem inductiveAppResultIsProp {methods : Methods .anon}
    (whnf : ∀ term, FramesLocalState ((RecM.whnf term).run methods))
    (type : KExpr .anon) :
    FramesLocalState ((RecM.inductiveAppResultIsProp type).run methods) := by
  unfold RecM.inductiveAppResultIsProp
  simp only [ReaderT.run_bind]
  exact bind (whnf type) fun sortType => bind (ensureSortDirect whnf sortType) fun _ => pure _

theorem inductiveAppIsProp {methods : Methods .anon}
    (whnf : ∀ term, FramesLocalState ((RecM.whnf term).run methods))
    (id : KId .anon) (levels : Array (KUniv .anon)) (binders : Nat) :
    FramesLocalState ((RecM.inductiveAppIsProp id levels binders).run methods) := by
  unfold RecM.inductiveAppIsProp
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  apply bind (tryGetConst id)
  intro constant
  split
  · simp only [ReaderT.run_bind, pure_bind, ReaderT.run_monadLift]
    apply bind (instantiateUnivParams _ levels)
    intro instantiated
    exact bind (inductiveAppBinders whnf binders instantiated) (inductiveAppResultIsProp whnf)
  · exact fun before _ => .refl _

theorem inferProjFieldStep {methods : Methods .anon}
    (recursive : ∀ term, FramesLocalState (methods.infer term))
    (whnf : ∀ term, FramesLocalState ((RecM.whnf term).run methods))
    (id : KId .anon) (field : UInt64) (value : KExpr .anon)
    (prop : Bool) (index : Nat) (type : KExpr .anon) :
    FramesLocalState ((RecM.inferProjFieldStep id field value prop index type).run methods) := by
  unfold RecM.inferProjFieldStep
  simp only [ReaderT.run_bind]
  apply bind (peelProjForall whnf _ _)
  intro pair
  rcases pair with ⟨domain, body⟩
  split
  · cases prop with
    | false => exact pure _
    | true =>
        simp only [if_true, ReaderT.run_bind]
        apply bind (recursive domain)
        intro domainType
        apply bind (ensureSortDirect whnf domainType)
        intro level
        split
        · exact throw _
        · exact pure _
  · have tail : FramesLocalState ((do
        let projection ← TcM.intern (.mkPrj id index.toUInt64 value)
        let result ← TcM.runIntern (subst body projection 0)
        return ForInStep.yield result : RecM .anon (ForInStep (KExpr .anon))).run methods) := by
      simp only [ReaderT.run_bind, ReaderT.run_monadLift]
      exact bind (intern _) fun _ => bind (runIntern _) fun _ => pure _
    cases prop with
    | false => exact tail
    | true =>
        simp only [if_true, ReaderT.run_bind]
        apply bind (recursive domain)
        intro domainType
        apply bind (ensureSortDirect whnf domainType)
        intro level
        split
        · exact throw _
        · exact tail

theorem inferProjFieldsLoopStep {methods : Methods .anon}
    (recursive : ∀ term, FramesLocalState (methods.infer term))
    (whnf : ∀ term, FramesLocalState ((RecM.whnf term).run methods))
    (id : KId .anon) (field : UInt64) (value : KExpr .anon)
    (prop : Bool) (index : Nat) (state : Option (KExpr .anon) × KExpr .anon) :
    FramesLocalState ((RecM.inferProjFieldsLoopStep id field value prop index state).run methods) := by
  unfold RecM.inferProjFieldsLoopStep
  simp only [ReaderT.run_bind]
  exact bind (inferProjFieldStep recursive whnf id field value prop index state.2)
    fun next => by cases next <;> exact pure _

theorem inferProjFields {methods : Methods .anon}
    (recursive : ∀ term, FramesLocalState (methods.infer term))
    (whnf : ∀ term, FramesLocalState ((RecM.whnf term).run methods))
    (id : KId .anon) (field : UInt64) (value : KExpr .anon)
    (prop : Bool) (type : KExpr .anon) :
    FramesLocalState ((RecM.inferProjFields id field value prop type).run methods) := by
  unfold RecM.inferProjFields
  simp only [ReaderT.run_bind]
  apply bind (forInRange _ _ _ (inferProjFieldsLoopStep recursive whnf id field value prop))
  intro pair
  cases pair.1 <;> first | exact pure _ | exact throw _

theorem inferProj {methods : Methods .anon}
    (recursive : ∀ term, FramesLocalState (methods.infer term))
    (whnf : ∀ term, FramesLocalState ((RecM.whnf term).run methods))
    (id : KId .anon) (field : UInt64) (value type : KExpr .anon) :
    FramesLocalState ((RecM.inferProj id field value type).run methods) := by
  unfold RecM.inferProj
  simp only [ReaderT.run_bind]
  apply bind (whnf type)
  intro reduced
  generalize reduced.collectSpine = pair
  rcases pair with ⟨head, args⟩
  dsimp only
  split
  · split
    · exact throw _
    · simp only [ReaderT.run_bind, ReaderT.run_monadLift]
      apply bind (tryGetConst _)
      intro constant
      split
      · simp only [pure_bind]
        split
        · exact fun before _ => .refl _
        · simp only [ReaderT.run_bind, ReaderT.run_monadLift]
          apply bind (inductiveAppIsProp whnf _ _ _)
          intro prop
          apply bind (tryGetConst _)
          intro constructor
          cases constructor with
          | none => exact fun before _ => .refl _
          | some constant =>
              simp only [ReaderT.run_bind, ReaderT.run_monadLift]
              apply bind (instantiateUnivParams constant.ty _)
              intro instantiated
              apply bind (instantiateProjParams whnf args _ instantiated)
              intro parameterized
              exact inferProjFields recursive whnf id field value prop parameterized
      · exact fun before _ => .refl _
  · exact throw _

end Ix.Kernel.Consistency.FramesLocalState

namespace Ix.Kernel.Consistency

/-- Projection inference is discharged by the same smaller inference table
and direct reduction contract as the rest of the production inference body. -/
theorem infer_framesLocalState_of_whnf {methods : Methods .anon}
    (recursive : ∀ term, FramesLocalState (methods.infer term))
    (whnf : ∀ term, FramesLocalState ((RecM.whnf term).run methods))
    (conversion : ∀ left right, FramesLocalState (methods.isDefEq left right))
    (term : KExpr .anon) : FramesLocalState ((RecM.infer term).run methods) :=
  infer_framesLocalState recursive whnf conversion (FramesLocalState.inferProj recursive whnf) term

end Ix.Kernel.Consistency
