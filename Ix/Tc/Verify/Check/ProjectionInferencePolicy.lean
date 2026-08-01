import Ix.Tc.Verify.Check.UncachedInferencePolicy

/-!
# Operational policy for projection inference

This module discharges the operational premise left explicit by uncached
inference.  It follows the production projection helper through WHNF spine
exposure, lazy declaration lookup, inductive-result classification, universe
instantiation, parameter substitution, and the selected-field telescope.

The range-loop lemmas account for both `done` and `yield`, so early field
selection and every partial-error path preserve the caller's `inferOnly`
policy.  The final theorem combines this helper with the uncached dispatcher
and cache shell, reducing the current inference layer to the current WHNF
policy over a policy-framed smaller method table.
-/

namespace Ix.Tc

namespace RecM

private theorem forInList_preservesInferOnly
    {methods : Methods .anon}
    {step : alpha → beta → RecM .anon (ForInStep beta)}
    (hstep : ∀ item state,
      ((step item state).run methods).PreservesInferOnly) :
    ∀ (items : List alpha) (initial : beta),
      ((forIn (m := RecM .anon) items initial step).run methods).PreservesInferOnly
  | [], initial => by
      exact TcM.PreservesInferOnly.pure initial
  | item :: rest, initial => by
      rw [List.forIn_cons, ReaderT.run_bind]
      apply TcM.PreservesInferOnly.bind (hstep item initial)
      intro action
      cases action with
      | done result => exact TcM.PreservesInferOnly.pure result
      | yield next => exact forInList_preservesInferOnly hstep rest next

private theorem forInRange_preservesInferOnly
    {methods : Methods .anon}
    {step : Nat → beta → RecM .anon (ForInStep beta)}
    (hstep : ∀ item state,
      ((step item state).run methods).PreservesInferOnly)
    (range : _root_.Std.Legacy.Range) (initial : beta) :
    ((forIn (m := RecM .anon) range initial step).run methods).PreservesInferOnly := by
  rw [_root_.Std.Legacy.Range.forIn_eq_forIn_range']
  exact forInList_preservesInferOnly hstep _ initial

theorem peelProjForall_preservesInferOnly
    {methods : Methods .anon}
    (hwhnf : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly)
    (source : KExpr .anon) (err : String) :
    ((peelProjForall source err).run methods).PreservesInferOnly := by
  cases source <;> simp only [peelProjForall, pure_bind]
  all_goals
    first
    | exact TcM.PreservesInferOnly.pure _
    | (simp only [ReaderT.run_bind]
       apply TcM.PreservesInferOnly.bind (hwhnf _)
       intro reduced
       cases reduced <;> simp only <;>
         first
         | exact TcM.PreservesInferOnly.pure _
         | exact TcM.PreservesInferOnly.throw _)

theorem instantiateProjParamStep_preservesInferOnly
    {methods : Methods .anon}
    (hwhnf : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly)
    (args : Array (KExpr .anon)) (i : Nat) (ctorTy : KExpr .anon) :
    ((instantiateProjParamStep args i ctorTy).run methods).PreservesInferOnly := by
  unfold instantiateProjParamStep
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind
    (peelProjForall_preservesInferOnly hwhnf ctorTy _)
  intro peeled
  rcases peeled with ⟨_, body⟩
  split
  · simp only [ReaderT.run_bind, ReaderT.run_monadLift]
    apply TcM.PreservesInferOnly.bind
      (TcM.PreservesInferOnly.runIntern _)
    intro result
    exact TcM.PreservesInferOnly.pure (ForInStep.yield result)
  · exact TcM.PreservesInferOnly.throw _

theorem instantiateProjParams_preservesInferOnly
    {methods : Methods .anon}
    (hwhnf : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly)
    (args : Array (KExpr .anon)) (numParams : Nat)
    (ctorTy : KExpr .anon) :
    ((instantiateProjParams args numParams ctorTy).run methods).PreservesInferOnly := by
  unfold instantiateProjParams
  exact forInRange_preservesInferOnly
    (fun i current =>
      instantiateProjParamStep_preservesInferOnly hwhnf args i current)
    _ ctorTy

private theorem inferProjectionSort_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly)
    (source : KExpr .anon) :
    ((do
      let sourceTy ← inferCall source
      ensureSortDirect sourceTy).run methods).PreservesInferOnly := by
  simp only [ReaderT.run_bind, inferCall]
  apply TcM.PreservesInferOnly.bind (hmethods.infer source)
  intro sourceTy
  exact ensureSortDirect_preservesInferOnly hwhnf

private theorem inferProjFieldTail_preservesInferOnly
    {methods : Methods .anon} (structId : KId .anon) (i : Nat)
    (val body : KExpr .anon) :
    ((do
      let proj ← TcM.intern (.mkPrj structId i.toUInt64 val)
      let result ← TcM.runIntern (subst body proj 0)
      pure (ForInStep.yield result) :
      RecM .anon (ForInStep (KExpr .anon))).run methods).PreservesInferOnly := by
  change (do
    let proj ← TcM.intern (.mkPrj structId i.toUInt64 val)
    let result ← TcM.runIntern (subst body proj 0)
    pure (ForInStep.yield result) :
    TcM .anon (ForInStep (KExpr .anon))).PreservesInferOnly
  unfold TcM.intern
  apply TcM.PreservesInferOnly.bind
    (TcM.PreservesInferOnly.runIntern _)
  intro proj
  apply TcM.PreservesInferOnly.bind
    (TcM.PreservesInferOnly.runIntern (subst body proj 0))
  intro result
  exact TcM.PreservesInferOnly.pure (ForInStep.yield result)

theorem inferProjFieldStep_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly)
    (structId : KId .anon) (field : UInt64) (val : KExpr .anon)
    (isPropStruct : Bool) (i : Nat) (current : KExpr .anon) :
    ((inferProjFieldStep structId field val isPropStruct i current).run
      methods).PreservesInferOnly := by
  unfold inferProjFieldStep
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind
    (peelProjForall_preservesInferOnly hwhnf current _)
  intro peeled
  rcases peeled with ⟨dom, body⟩
  split
  · cases isPropStruct with
    | false => exact TcM.PreservesInferOnly.pure (ForInStep.done dom)
    | true =>
        simp only [if_true, ReaderT.run_bind, inferCall]
        apply TcM.PreservesInferOnly.bind (hmethods.infer dom)
        intro fieldSortTy
        apply TcM.PreservesInferOnly.bind
          (ensureSortDirect_preservesInferOnly hwhnf)
        intro fieldLevel
        split
        · exact TcM.PreservesInferOnly.throw _
        · exact TcM.PreservesInferOnly.pure (ForInStep.done dom)
  · cases isPropStruct with
    | false =>
        exact inferProjFieldTail_preservesInferOnly structId i val body
    | true =>
        simp only [if_true, ReaderT.run_bind, pure_bind,
          inferCall]
        apply TcM.PreservesInferOnly.bind (hmethods.infer dom)
        intro fieldSortTy
        apply TcM.PreservesInferOnly.bind
          (ensureSortDirect_preservesInferOnly hwhnf)
        intro fieldLevel
        split
        · exact TcM.PreservesInferOnly.throw _
        · exact inferProjFieldTail_preservesInferOnly structId i val body

theorem inferProjFieldsLoopStep_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly)
    (structId : KId .anon) (field : UInt64) (val : KExpr .anon)
    (isPropStruct : Bool) (i : Nat)
    (state : Option (KExpr .anon) × KExpr .anon) :
    ((inferProjFieldsLoopStep structId field val isPropStruct i state).run
      methods).PreservesInferOnly := by
  unfold inferProjFieldsLoopStep
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind
    (inferProjFieldStep_preservesInferOnly hmethods hwhnf structId field val
      isPropStruct i state.2)
  intro action
  cases action with
  | done result =>
      exact TcM.PreservesInferOnly.pure
        (ForInStep.done (some result, state.2))
  | yield next =>
      exact TcM.PreservesInferOnly.pure
        (ForInStep.yield (none, next))

theorem inferProjFields_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly)
    (structId : KId .anon) (field : UInt64) (val : KExpr .anon)
    (isPropStruct : Bool) (ctorTy : KExpr .anon) :
    ((inferProjFields structId field val isPropStruct ctorTy).run
      methods).PreservesInferOnly := by
  unfold inferProjFields
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind
    (forInRange_preservesInferOnly
      (fun i state =>
        inferProjFieldsLoopStep_preservesInferOnly hmethods hwhnf structId
          field val isPropStruct i state)
      _ ((none : Option (KExpr .anon)), ctorTy))
  intro state
  cases state.1 with
  | none => exact TcM.PreservesInferOnly.throw _
  | some result => exact TcM.PreservesInferOnly.pure result

theorem inductiveAppBinderStep_preservesInferOnly
    {methods : Methods .anon}
    (hwhnf : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly)
    (current : KExpr .anon) :
    ((inductiveAppBinderStep current).run methods).PreservesInferOnly := by
  unfold inductiveAppBinderStep
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind (hwhnf current)
  intro reduced
  cases reduced <;> simp only <;>
    first
    | exact TcM.PreservesInferOnly.pure _
    | exact TcM.PreservesInferOnly.throw _

theorem inductiveAppBinders_preservesInferOnly
    {methods : Methods .anon}
    (hwhnf : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly)
    (binders : Nat) (indTy : KExpr .anon) :
    ((inductiveAppBinders binders indTy).run methods).PreservesInferOnly := by
  unfold inductiveAppBinders
  exact forInRange_preservesInferOnly
    (fun _ current => inductiveAppBinderStep_preservesInferOnly hwhnf current)
    _ indTy

theorem inductiveAppResultIsProp_preservesInferOnly
    {methods : Methods .anon}
    (hwhnf : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly)
    (resultTy : KExpr .anon) :
    ((inductiveAppResultIsProp resultTy).run methods).PreservesInferOnly := by
  unfold inductiveAppResultIsProp
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind (hwhnf resultTy)
  intro sortTy
  apply TcM.PreservesInferOnly.bind
    (ensureSortDirect_preservesInferOnly hwhnf)
  intro level
  exact TcM.PreservesInferOnly.pure (univEq level .mkZero)

theorem inductiveAppIsProp_preservesInferOnly
    {methods : Methods .anon}
    (hwhnf : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly)
    (indId : KId .anon) (levels : Array (KUniv .anon))
    (binders : Nat) :
    ((inductiveAppIsProp indId levels binders).run methods).PreservesInferOnly := by
  unfold inductiveAppIsProp
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  apply TcM.PreservesInferOnly.bind
    (TcM.PreservesInferOnly.tryGetConst indId)
  intro declaration
  cases declaration with
  | none => exact TcM.PreservesInferOnly.throw _
  | some declaration =>
      cases declaration with
      | indc name levelParams lvls params indices isUnsafe block memberIdx
          indTy ctors leanAll =>
          apply TcM.PreservesInferOnly.bind
            (TcM.PreservesInferOnly.instantiateUnivParams indTy levels)
          intro instantiated
          apply TcM.PreservesInferOnly.bind
            (inductiveAppBinders_preservesInferOnly hwhnf binders
              instantiated)
          intro resultTy
          exact inductiveAppResultIsProp_preservesInferOnly hwhnf resultTy
      | _ => exact TcM.PreservesInferOnly.throw _

theorem inferProj_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly)
    (structId : KId .anon) (field : UInt64) (val valTy : KExpr .anon) :
    ((inferProj structId field val valTy).run methods).PreservesInferOnly := by
  unfold inferProj
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind (hwhnf valTy)
  intro reduced
  rcases hspine : reduced.collectSpine with ⟨head, args⟩
  cases head with
  | const headId levels info =>
      simp only
      split
      · exact TcM.PreservesInferOnly.throw _
      · simp only [ReaderT.run_bind, ReaderT.run_monadLift, pure_bind]
        apply TcM.PreservesInferOnly.bind
          (TcM.PreservesInferOnly.tryGetConst headId)
        intro declaration
        cases declaration with
        | none => exact TcM.PreservesInferOnly.throw _
        | some declaration =>
            cases declaration with
            | indc name levelParams lvls params indices isUnsafe block
                memberIdx indTy ctors leanAll =>
                simp only
                split
                · exact TcM.PreservesInferOnly.throw _
                · simp only [ReaderT.run_bind, ReaderT.run_monadLift]
                  apply TcM.PreservesInferOnly.bind
                    (inductiveAppIsProp_preservesInferOnly hwhnf headId
                      levels (params.toNat + indices.toNat))
                  intro isPropStruct
                  apply TcM.PreservesInferOnly.bind
                    (TcM.PreservesInferOnly.tryGetConst ctors[0]!)
                  intro constructor
                  cases constructor with
                  | none => exact TcM.PreservesInferOnly.throw _
                  | some constructor =>
                      simp only
                      apply TcM.PreservesInferOnly.bind
                        (TcM.PreservesInferOnly.instantiateUnivParams
                          constructor.ty levels)
                      intro instantiatedCtorTy
                      apply TcM.PreservesInferOnly.bind
                        (instantiateProjParams_preservesInferOnly hwhnf args
                          params.toNat instantiatedCtorTy)
                      intro parameterizedCtorTy
                      exact inferProjFields_preservesInferOnly hmethods hwhnf
                        structId field val isPropStruct parameterizedCtorTy
            | _ => exact TcM.PreservesInferOnly.throw _
  | _ => exact TcM.PreservesInferOnly.throw _

end RecM

namespace ProjectionInference

/-- The production projection helper preserves inference policy whenever its
smaller method table and the current WHNF layer do. -/
theorem preservesInferOnlyAt
    (methods : Methods .anon) (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly) :
    PreservesInferOnlyAt methods := by
  intro structId field val valTy
  exact RecM.inferProj_preservesInferOnly hmethods hwhnf structId field val
    valTy

end ProjectionInference

namespace RecM

/-- Discharge the uncached dispatcher's projection premise from the concrete
projection helper implementation. -/
theorem inferUncached_preservesInferOnly_of_whnf
    (methods : Methods .anon) (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly)
    (inferOnly : Bool) (source : KExpr .anon) :
    ((inferUncached inferCall inferOnly source).run methods).PreservesInferOnly :=
  inferUncached_preservesInferOnly methods hmethods hwhnf
    (ProjectionInference.preservesInferOnlyAt methods hmethods hwhnf)
    inferOnly source

/-- The production inference cache shell and uncached dispatcher together
preserve inference policy once the current WHNF layer is framed. -/
theorem infer_preservesInferOnly_of_whnf
    (methods : Methods .anon) (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly)
    (source : KExpr .anon) :
    ((infer source).run methods).PreservesInferOnly := by
  apply infer_preservesInferOnly methods
  exact inferUncached_preservesInferOnly_of_whnf methods hmethods hwhnf

end RecM

end Ix.Tc
