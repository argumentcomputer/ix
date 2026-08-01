import Ix.Tc.Verify.Check.WhnfNatArgumentPolicy

/-!
# Operational inference-policy frame for native WHNF reduction

This module proves the complete policy frame for native reduction.  The
syntax-only front end produces a `NativeReductionPlan`; the marker executor
then owns lazy declaration lookup, universe instantiation, the recursive WHNF
callback, and restoration of the re-entrancy guard on both outcomes.
-/

namespace Ix.Tc

namespace RecM

private theorem prims_preservesInferOnly (methods : Methods .anon) :
    ((prims : RecM .anon (Primitives .anon)).run methods).PreservesInferOnly := by
  unfold prims
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
  intro state
  exact TcM.PreservesInferOnly.pure state.prims

theorem tryReduceNativeMarker_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (p : Primitives .anon) (isReduceBool : Bool) (id : KId .anon)
    (levels : Array (KUniv .anon)) :
    TcM.PreservesInferOnly
      ((tryReduceNativeMarker p isReduceBool id levels).run methods) := by
  unfold tryReduceNativeMarker
  refine bindTcM_preservesInferOnly
    (TcM.PreservesInferOnly.tryGetConst id) ?_
  intro found
  cases found with
  | none => exact TcM.PreservesInferOnly.pure none
  | some declaration =>
      cases declaration
      case defn name levelParams kind safety hints lvls type body leanAll
          block =>
        simp only [pure_bind]
        refine bindTcM_preservesInferOnly
          (TcM.PreservesInferOnly.instantiateUnivParams body levels) ?_
        intro instantiated
        refine bindTcM_preservesInferOnly
          (TcM.PreservesInferOnly.modify
            (f := fun state : TcState .anon =>
              { state with inNativeReduce := true })
            (fun _ => rfl)) ?_
        intro _
        refine bind_preservesInferOnly
          (x := try
            let result ← whnfRec instantiated
            pure (Except.ok result)
          catch error =>
            pure (Except.error error))
          (captureErrors_preservesInferOnly
            (whnfRec_preservesInferOnly hmethods instantiated)) ?_
        intro captured
        refine bindTcM_preservesInferOnly
          (TcM.PreservesInferOnly.modify
            (f := fun state : TcState .anon =>
              { state with inNativeReduce := false })
            (fun _ => rfl)) ?_
        intro _
        cases captured with
        | error error => exact TcM.PreservesInferOnly.throw error
        | ok result =>
            cases hbool : isReduceBool with
            | true =>
                simp only [if_true]
                cases hresult : result with
                | const resultId resultLevels resultInfo =>
                    simp only []
                    split <;> exact TcM.PreservesInferOnly.pure _
                | var | fvar | sort | app | lam | all | letE | prj | nat |
                      str =>
                    exact TcM.PreservesInferOnly.pure none
            | false =>
                simp only [Bool.false_eq_true, if_false]
                cases hresult : result <;>
                  exact TcM.PreservesInferOnly.pure _
      all_goals exact TcM.PreservesInferOnly.pure none

attribute [local irreducible] tryReduceNativeMarker

theorem tryReduceNative_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (source : KExpr .anon) :
    TcM.PreservesInferOnly ((tryReduceNative source).run methods) := by
  unfold tryReduceNative
  refine bindTcM_preservesInferOnly TcM.PreservesInferOnly.get ?_
  intro state
  cases hnoAccel : state.noAccel with
  | true =>
      simp only [if_true]
      exact TcM.PreservesInferOnly.pure none
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      rcases hspine : source.collectSpine with ⟨head, args⟩
      cases head with
      | const id levels info =>
          refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
          intro p
          simp only []
          cases hplan : planNativeReduction p source id.addr args with
          | done result => exact TcM.PreservesInferOnly.pure result
          | marker isReduceBool arg =>
              refine bindTcM_preservesInferOnly TcM.PreservesInferOnly.get ?_
              intro guardState
              cases hguard : guardState.inNativeReduce with
              | true =>
                  simp only [if_true]
                  exact TcM.PreservesInferOnly.pure none
              | false =>
                  simp only [Bool.false_eq_true, if_false]
                  cases harg : arg with
                  | const argId argLevels argInfo =>
                      exact tryReduceNativeMarker_preservesInferOnly hmethods
                        p isReduceBool argId argLevels
                  | var | fvar | sort | app | lam | all | letE | prj | nat |
                        str =>
                      exact TcM.PreservesInferOnly.pure none
      | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
          exact TcM.PreservesInferOnly.pure none

end RecM

end Ix.Tc
