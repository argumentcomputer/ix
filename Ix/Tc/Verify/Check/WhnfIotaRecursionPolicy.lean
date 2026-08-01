import Ix.Tc.Verify.Check.WhnfIotaScopePolicy

/-!
# Operational inference-policy frame for iota recursion classification

This module verifies mutual-block discovery and the complete constructive
`computedIsRec` transaction used by struct eta.  It covers parameter peeling,
bounded field scanning, legacy-context restoration, provisional and final
cache writes, and cleanup of the provisional entry on classifier errors.
-/

namespace Ix.Tc

namespace RecM


private theorem forInList_preservesInferOnly
    {methods : Methods .anon}
    {step : alpha → beta → RecM .anon (ForInStep beta)}
    (hstep : ∀ item state,
      ((step item state).run methods).PreservesInferOnly) :
    ∀ (items : List alpha) (initial : beta),
      ((forIn (m := RecM .anon) items initial step).run
        methods).PreservesInferOnly
  | [], initial => TcM.PreservesInferOnly.pure initial
  | item :: rest, initial => by
      rw [List.forIn_cons, ReaderT.run_bind]
      apply TcM.PreservesInferOnly.bind (hstep item initial)
      intro action
      cases action with
      | done result => exact TcM.PreservesInferOnly.pure result
      | yield next => exact forInList_preservesInferOnly hstep rest next

private theorem forInArray_preservesInferOnly
    {methods : Methods .anon}
    {step : alpha → beta → RecM .anon (ForInStep beta)}
    (hstep : ∀ item state,
      ((step item state).run methods).PreservesInferOnly)
    (items : Array alpha) (initial : beta) :
    ((forIn (m := RecM .anon) items initial step).run
      methods).PreservesInferOnly := by
  rcases items with ⟨items⟩
  simp only [List.forIn_toArray]
  exact forInList_preservesInferOnly hstep items initial

private theorem forInRange_preservesInferOnly
    {methods : Methods .anon}
    {step : Nat → beta → RecM .anon (ForInStep beta)}
    (hstep : ∀ item state,
      ((step item state).run methods).PreservesInferOnly)
    (range : _root_.Std.Legacy.Range) (initial : beta) :
    ((forIn (m := RecM .anon) range initial step).run
      methods).PreservesInferOnly := by
  rw [_root_.Std.Legacy.Range.forIn_eq_forIn_range']
  exact forInList_preservesInferOnly hstep _ initial

theorem discoverBlockInductives_preservesInferOnly
    {methods : Methods .anon} (blockId : KId .anon) :
    ((discoverBlockInductives blockId).run methods).PreservesInferOnly := by
  unfold discoverBlockInductives
  refine bindTcM_preservesInferOnly
    (TcM.PreservesInferOnly.tryGetBlock blockId) ?_
  intro found
  cases found with
  | none => exact TcM.PreservesInferOnly.pure #[]
  | some members =>
      simp only []
      refine bind_preservesInferOnly
        (forInArray_preservesInferOnly (methods := methods)
          (items := members) (initial := #[]) ?_) ?_
      · intro id inds
        refine bindTcM_preservesInferOnly
          (TcM.PreservesInferOnly.tryGetConst id) ?_
        intro declaration
        cases declaration with
        | none =>
            exact TcM.PreservesInferOnly.pure (ForInStep.yield inds)
        | some declaration =>
            cases declaration with
            | indc =>
                exact TcM.PreservesInferOnly.pure
                  (ForInStep.yield (inds.push id))
            | axio | defn | quot | ctor | recr =>
                simp only [pure_bind]
                exact TcM.PreservesInferOnly.pure (ForInStep.yield inds)
      · intro result
        exact TcM.PreservesInferOnly.pure result

theorem computeIsRecParamStepAfterWhnf_preservesInferOnly
    {methods : Methods .anon} (source normalized : KExpr .anon) :
    ((computeIsRecParamStepAfterWhnf source normalized).run
      methods).PreservesInferOnly := by
  unfold computeIsRecParamStepAfterWhnf
  cases normalized with
  | all name bi domain body info =>
      refine bindTcM_preservesInferOnly
        (TcM.PreservesInferOnly.pushLocal domain) ?_
      intro _
      exact TcM.PreservesInferOnly.pure (ForInStep.yield body)
  | var | fvar | sort | const | app | lam | letE | prj | nat | str =>
      exact TcM.PreservesInferOnly.pure (ForInStep.done source)

theorem computeIsRecParamStep_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (source : KExpr .anon) :
    ((computeIsRecParamStep source).run methods).PreservesInferOnly := by
  unfold computeIsRecParamStep
  refine bind_preservesInferOnly
    (whnfRec_preservesInferOnly hmethods source) ?_
  intro normalized
  exact computeIsRecParamStepAfterWhnf_preservesInferOnly source normalized

theorem computeIsRecFieldStepAfterWhnf_preservesInferOnly
    {methods : Methods .anon} (blockAddrs : Array Address)
    (normalized : KExpr .anon) :
    ((computeIsRecFieldStepAfterWhnf blockAddrs normalized).run
      methods).PreservesInferOnly := by
  unfold computeIsRecFieldStepAfterWhnf
  cases normalized with
  | all name bi domain body info =>
      by_cases hmentions : exprMentionsAnyAddr domain blockAddrs
      · simp only [hmentions, if_pos]
        exact TcM.PreservesInferOnly.pure (BoundedStep.done true)
      · simp only [hmentions]
        simpa only [pure_bind] using
          (bindTcM_preservesInferOnly
            (methods := methods)
            (next := fun _ => pure (BoundedStep.next body))
            (TcM.PreservesInferOnly.pushLocal domain)
            (fun _ => by
              simpa only [ReaderT.run_pure] using
                (TcM.PreservesInferOnly.pure (BoundedStep.next body))))
  | var | fvar | sort | const | app | lam | letE | prj | nat | str =>
      exact TcM.PreservesInferOnly.pure (BoundedStep.done false)

theorem computeIsRecFieldStep_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (blockAddrs : Array Address) (source : KExpr .anon) :
    ((computeIsRecFieldStep blockAddrs source).run
      methods).PreservesInferOnly := by
  unfold computeIsRecFieldStep
  refine bind_preservesInferOnly
    (whnfRec_preservesInferOnly hmethods source) ?_
  intro normalized
  exact computeIsRecFieldStepAfterWhnf_preservesInferOnly
    blockAddrs normalized

theorem computeIsRecCtor_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (ctorTy : KExpr .anon) (nParams : Nat)
    (blockAddrs : Array Address) :
    ((computeIsRecCtor ctorTy nParams blockAddrs).run
      methods).PreservesInferOnly := by
  unfold computeIsRecCtor
  refine bindTcM_preservesInferOnly TcM.PreservesInferOnly.saveDepth ?_
  intro saved
  change (tryFinally
    ((do
      let ty ← forIn [0:nParams] ctorTy fun _ ty =>
        computeIsRecParamStep ty
      runBounded (computeIsRecFieldStep blockAddrs)
        maxWhnfFuel.toNat ty).run methods)
    (TcM.restoreDepth (m := .anon) saved)).PreservesInferOnly
  apply TcM.PreservesInferOnly.tryFinally
  · refine bind_preservesInferOnly
      (forInRange_preservesInferOnly
        (fun _ ty => computeIsRecParamStep_preservesInferOnly hmethods ty)
        [0:nParams] ctorTy) ?_
    intro ty
    exact runBounded_preservesInferOnly
      (fun source => computeIsRecFieldStep_preservesInferOnly
        hmethods blockAddrs source) maxWhnfFuel.toNat ty
  · exact TcM.PreservesInferOnly.restoreDepth saved

theorem computeIsRec_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (ctors : Array (KId .anon)) (nParams : Nat)
    (blockAddrs : Array Address) :
    ((computeIsRec ctors nParams blockAddrs).run
      methods).PreservesInferOnly := by
  unfold computeIsRec
  refine bind_preservesInferOnly
    (forInArray_preservesInferOnly (methods := methods)
      (items := ctors)
      (initial := (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)) ?_) ?_
  · intro ctorId state
    refine bindTcM_preservesInferOnly
      (TcM.PreservesInferOnly.tryGetConst ctorId) ?_
    intro declaration
    cases declaration with
    | none =>
        exact TcM.PreservesInferOnly.pure
          (ForInStep.yield
            (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit))
    | some declaration =>
        cases declaration with
        | ctor name levelParams isUnsafe lvls induct cidx params fields ty =>
            simp only [pure_bind]
            refine bind_preservesInferOnly
              (computeIsRecCtor_preservesInferOnly hmethods ty nParams
                blockAddrs) ?_
            intro found
            cases found with
            | true =>
                simp only [if_true]
                exact TcM.PreservesInferOnly.pure
                  (ForInStep.done
                    (⟨some true, PUnit.unit⟩ : MProd (Option Bool) PUnit))
            | false =>
                simp only [Bool.false_eq_true, if_false]
                exact TcM.PreservesInferOnly.pure
                  (ForInStep.yield
                    (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit))
        | axio | defn | quot | indc | recr =>
            exact TcM.PreservesInferOnly.pure
              (ForInStep.yield
                (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit))
  · intro result
    rcases result with ⟨found, _unit⟩
    cases found with
    | none =>
        simp only [pure_bind]
        exact TcM.PreservesInferOnly.pure false
    | some value => exact TcM.PreservesInferOnly.pure value

theorem cacheIsRec_preservesInferOnly
    {methods : Methods .anon} (ind : KId .anon) (value : Bool) :
    ((cacheIsRec ind value).run methods).PreservesInferOnly := by
  unfold cacheIsRec
  exact liftTcM_preservesInferOnly <|
    TcM.PreservesInferOnly.modify (fun _ => rfl)

theorem eraseCachedIsRec_preservesInferOnly
    {methods : Methods .anon} (ind : KId .anon) :
    ((eraseCachedIsRec ind).run methods).PreservesInferOnly := by
  unfold eraseCachedIsRec
  exact liftTcM_preservesInferOnly <|
    TcM.PreservesInferOnly.modify (fun _ => rfl)

theorem computedIsRecClassify_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (ind : KId .anon) (ctors : Array (KId .anon))
    (nParams : Nat) (blockAddrs : Array Address) :
    ((computedIsRecClassify ind ctors nParams blockAddrs).run
      methods).PreservesInferOnly := by
  unfold computedIsRecClassify
  change (tryCatch
    ((do
      let value ← computeIsRec ctors nParams blockAddrs
      cacheIsRec ind value
      return value).run methods)
    (fun err =>
      (do
        eraseCachedIsRec ind
        throw err : RecM .anon Bool).run methods)).PreservesInferOnly
  apply TcM.PreservesInferOnly.tryCatch
  · refine bind_preservesInferOnly
      (computeIsRec_preservesInferOnly hmethods ctors nParams blockAddrs) ?_
    intro value
    refine bind_preservesInferOnly
      (cacheIsRec_preservesInferOnly ind value) ?_
    intro _
    exact TcM.PreservesInferOnly.pure value
  · intro err
    refine bind_preservesInferOnly
      (eraseCachedIsRec_preservesInferOnly ind) ?_
    intro _
    exact TcM.PreservesInferOnly.throw err

attribute [local irreducible] computedIsRecClassify

theorem computedIsRecMiss_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (ind : KId .anon) (params : UInt64) (ctors : Array (KId .anon))
    (block : KId .anon) :
    ((computedIsRecMiss ind params ctors block).run
      methods).PreservesInferOnly := by
  unfold computedIsRecMiss
  refine bind_preservesInferOnly (cacheIsRec_preservesInferOnly ind true) ?_
  intro _
  refine bind_preservesInferOnly
    (discoverBlockInductives_preservesInferOnly block) ?_
  intro blockInds
  apply computedIsRecClassify_preservesInferOnly
  exact hmethods

theorem computedIsRec_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (ind : KId .anon) :
    ((computedIsRec ind).run methods).PreservesInferOnly := by
  unfold computedIsRec
  refine bindTcM_preservesInferOnly TcM.PreservesInferOnly.get ?_
  intro state
  cases hcached : state.env.isRecCache[ind.addr]? with
  | some value =>
      simp only []
      exact TcM.PreservesInferOnly.pure value
  | none =>
      simp only [pure_bind]
      refine bindTcM_preservesInferOnly
        (TcM.PreservesInferOnly.getConst ind) ?_
      intro declaration
      cases declaration with
      | indc name levelParams lvls params indices isUnsafe block memberIdx ty
          ctors leanAll =>
          exact computedIsRecMiss_preservesInferOnly hmethods ind params
            ctors block
      | axio | defn | quot | ctor | recr =>
          exact TcM.PreservesInferOnly.throw _

end RecM
end Ix.Tc
