import Ix.Tc.Verify.Check.WhnfProjectionPolicy

/-!
# Operational policy for Nat argument normalization and stuck offsets

This module proves that the shared Nat argument callback restores the
caller's inference policy through direct reduction, temporary local fuel,
successful callbacks, caught exhaustion, and propagated errors.  It then
closes the complete `tryNatOffsetStuck` classifier and rebuild path.
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

theorem whnfNatReducerArg_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (arg : KExpr .anon) :
    ((whnfNatReducerArg arg).run methods).PreservesInferOnly := by
  unfold whnfNatReducerArg
  refine bindTcM_preservesInferOnly TcM.PreservesInferOnly.get ?_
  intro observed
  cases hdirect : !arg.hasFVars || observed.eagerReduce with
  | true =>
      simp only [if_true]
      refine bind_preservesInferOnly
        (x := whnfRec arg)
        (whnfRec_preservesInferOnly hmethods arg) ?_
      intro reduced
      exact TcM.PreservesInferOnly.pure (some reduced)
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      refine bindTcM_preservesInferOnly TcM.PreservesInferOnly.get ?_
      intro (saved : TcState .anon)
      refine bindTcM_preservesInferOnly
        (TcM.PreservesInferOnly.modify
          (f := fun state : TcState .anon =>
            { state with recFuel :=
              (min saved.recFuel natReducerOpenArgRecFuel) })
          (fun _ => rfl)) ?_
      intro _
      refine bind_preservesInferOnly
        (x := try
          let reduced ← whnfRec arg
          pure (Except.ok reduced)
        catch error =>
          pure (Except.error error))
        (captureErrors_preservesInferOnly
          (whnfRec_preservesInferOnly hmethods arg)) ?_
      intro result
      refine bindTcM_preservesInferOnly TcM.PreservesInferOnly.get ?_
      intro afterCallback
      refine bindTcM_preservesInferOnly
        (TcM.PreservesInferOnly.modify
          (f := fun state : TcState .anon =>
            { state with recFuel := saved.recFuel -
              (min saved.recFuel
                (min saved.recFuel natReducerOpenArgRecFuel -
                  afterCallback.recFuel)) })
          (fun _ => rfl)) ?_
      intro _
      cases result with
      | ok reduced => exact TcM.PreservesInferOnly.pure (some reduced)
      | error error =>
          cases error <;>
            first
            | exact TcM.PreservesInferOnly.pure none
            | exact TcM.PreservesInferOnly.throw _

attribute [local irreducible] whnfNatReducerArg

theorem tryNatOffsetStuck_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (source : KExpr .anon) :
    ((tryNatOffsetStuck source).run methods).PreservesInferOnly := by
  unfold tryNatOffsetStuck
  refine bind_preservesInferOnly
    (x := prims) (prims_preservesInferOnly methods) ?_
  intro p
  cases hhead : !natOffsetStuckHead p source with
  | true =>
      simp only [if_true]
      exact TcM.PreservesInferOnly.pure none
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      rcases hspine : source.collectSpine with ⟨head, args⟩
      cases head with
      | const id levels info =>
          cases hshape :
              ((!(id.addr == p.natAdd.addr) &&
                  !(id.addr == p.natDiv.addr ||
                    id.addr == p.natMod.addr)) || args.size != 2) with
          | true =>
              simp only [hshape, if_true]
              exact TcM.PreservesInferOnly.pure none
          | false =>
              simp only [hshape, Bool.false_eq_true, if_false]
              refine bind_preservesInferOnly
                (x := whnfNatReducerArg args[1]!)
                (whnfNatReducerArg_preservesInferOnly hmethods args[1]!) ?_
              intro normalizedRight
              cases normalizedRight with
              | none =>
                  simp only
                  exact TcM.PreservesInferOnly.pure none
              | some right =>
                  simp only
                  cases hvalue : extractNatValue right p with
                  | none =>
                      simp only
                      exact TcM.PreservesInferOnly.pure none
                  | some value =>
                      simp only
                      cases hzero : value == 0 with
                      | true =>
                          simp only [if_true]
                          exact TcM.PreservesInferOnly.pure none
                      | false =>
                          simp only [Bool.false_eq_true, if_false]
                          cases hone :
                              (id.addr == p.natDiv.addr ||
                                id.addr == p.natMod.addr) && value == 1 with
                          | true =>
                              simp only [if_true]
                              exact TcM.PreservesInferOnly.pure none
                          | false =>
                              simp only [Bool.false_eq_true, if_false]
                              refine bind_preservesInferOnly
                                (x := whnfNatReducerArg args[0]!)
                                (whnfNatReducerArg_preservesInferOnly
                                  hmethods args[0]!) ?_
                              intro normalizedLeft
                              cases normalizedLeft with
                              | none =>
                                  simp only
                                  exact TcM.PreservesInferOnly.pure none
                              | some left =>
                                  simp only
                                  cases hliteral :
                                      (extractNatValue left p).isSome with
                                  | true =>
                                      simp only [if_true]
                                      exact TcM.PreservesInferOnly.pure none
                                  | false =>
                                      simp only [Bool.false_eq_true, if_false]
                                      refine bindIntern_preservesInferOnly
                                        (KExpr.mkApp
                                          (.const id levels info) left) ?_
                                      intro inner
                                      refine bindIntern_preservesInferOnly
                                        (KExpr.mkApp inner
                                          (natExprFromValue value)) ?_
                                      intro result
                                      exact TcM.PreservesInferOnly.pure
                                        (some result)
      | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
          exact TcM.PreservesInferOnly.pure none

end RecM

end Ix.Tc
