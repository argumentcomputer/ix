import Ix.Tc.Verify.Check.InferencePolicy

/-!
# Inference-policy frame for universe instantiation

`TcM.instantiateUnivParams` is a memoized `StateT` walk over an expression
DAG.  Its semantic verification needs collision and reachability resources,
but its operational noninterference fact does not: the walk can throw while
substituting a universe, and otherwise changes only its private memo table and
the kernel intern table.

This module proves that unconditional operational fact directly over the
production walker.  It covers memo hits, every expression constructor, the
constant-universe array loop, recursive child failures, interning, and memo
writes on both outcomes.
-/

namespace Ix.Tc

namespace TcM.PreservesInferOnly

theorem ofExcept (value : Except (TcError .anon) alpha) :
    (TcM.ofExcept value).PreservesInferOnly := by
  cases value with
  | ok value => exact pure value
  | error err => exact throw err

theorem map {x : TcM .anon alpha} (hx : x.PreservesInferOnly)
    (f : alpha → beta) : (f <$> x).PreservesInferOnly := by
  rw [← bind_pure_comp]
  exact bind hx fun value => pure (f value)

private def StatePreservesInferOnly
    (x : StateT sigma (TcM .anon) alpha) : Prop :=
  ∀ memo, (x.run memo).PreservesInferOnly

private theorem statePure (value : alpha) :
    StatePreservesInferOnly
      (Pure.pure value : StateT sigma (TcM .anon) alpha) := by
  intro memo
  simp only [StateT.run_pure]
  exact TcM.PreservesInferOnly.pure _

private theorem stateBind {x : StateT sigma (TcM .anon) alpha}
    {f : alpha → StateT sigma (TcM .anon) beta}
    (hx : StatePreservesInferOnly x)
    (hf : ∀ value, StatePreservesInferOnly (f value)) :
    StatePreservesInferOnly (x >>= f) := by
  intro memo
  simp only [StateT.run_bind]
  apply TcM.PreservesInferOnly.bind (hx memo)
  intro pair
  exact hf pair.1 pair.2

private theorem stateGet :
    StatePreservesInferOnly
      (MonadState.get : StateT sigma (TcM .anon) sigma) := by
  intro memo
  simp only [StateT.run_get]
  exact TcM.PreservesInferOnly.pure _

private theorem stateModify (f : sigma → sigma) :
    StatePreservesInferOnly
      (_root_.modify f : StateT sigma (TcM .anon) PUnit) := by
  intro memo
  simp only [StateT.run_modify]
  exact TcM.PreservesInferOnly.pure _

private theorem stateLift {x : TcM .anon alpha}
    (hx : x.PreservesInferOnly) :
    StatePreservesInferOnly
      (monadLift x : StateT sigma (TcM .anon) alpha) := by
  intro memo
  simp only [StateT.run_monadLift]
  apply TcM.PreservesInferOnly.bind hx
  intro value
  exact TcM.PreservesInferOnly.pure _

private theorem stateForInArray
    (items : Array alpha) (initial : beta)
    (step : alpha → beta →
      StateT sigma (TcM .anon) (ForInStep beta))
    (hstep : ∀ item state,
      StatePreservesInferOnly (step item state)) :
    StatePreservesInferOnly (forIn items initial step) := by
  rcases items with ⟨items⟩
  simp only [List.forIn_toArray]
  induction items generalizing initial with
  | nil =>
      simp
      exact statePure initial
  | cons item rest ih =>
      rw [List.forIn_cons]
      apply stateBind (hstep item initial)
      intro action
      cases action with
      | done result => exact statePure result
      | yield next => exact ih next

private theorem stateInternMemo (key : Address) (result : KExpr .anon) :
    StatePreservesInferOnly (do
      let interned ← monadLift (TcM.intern result)
      _root_.modify fun memo : Std.HashMap Address (KExpr .anon) =>
        memo.insert key interned
      Pure.pure interned) := by
  apply stateBind (stateLift (runIntern _))
  intro interned
  apply stateBind (stateModify _)
  intro _
  exact statePure interned

/-- Universe instantiation cannot change the inference-policy bit.  The
statement is unconditional because collision freedom is relevant to the
walker's semantic result, not to which `TcState` fields it can mutate. -/
theorem instantiateUnivParams (e : KExpr .anon)
    (us : Array (KUniv .anon)) :
    (TcM.instantiateUnivParams e us).PreservesInferOnly := by
  unfold TcM.instantiateUnivParams
  split
  · exact pure e
  · have hinner : ∀ (source : KExpr .anon),
        StatePreservesInferOnly (TcM.instUnivInner source us) := by
      intro source
      induction source with
      | var idx name info =>
          simp only [TcM.instUnivInner]
          apply stateBind stateGet
          intro memo
          split
          · exact statePure _
          · apply stateBind (stateModify _)
            intro _
            exact statePure (KExpr.var idx name info)
      | fvar id name info =>
          simp only [TcM.instUnivInner]
          apply stateBind stateGet
          intro memo
          split
          · exact statePure _
          · apply stateBind (stateModify _)
            intro _
            exact statePure (KExpr.fvar id name info)
      | sort u info =>
          simp only [TcM.instUnivInner]
          apply stateBind stateGet
          intro memo
          split
          · exact statePure _
          · apply stateBind (stateLift (ofExcept (substUniv u us)))
            intro resultUniv
            apply stateBind (statePure (KExpr.mkSort resultUniv))
            intro result
            exact stateInternMemo (KExpr.sort u info).addr result
      | const id levels info =>
          rw [TcM.instUnivInner]
          simp (config := { proj := false }) only []
          apply stateBind stateGet
          intro memo
          split
          · exact statePure _
          · apply stateBind
              (stateForInArray levels (Array.mkEmpty levels.size)
                (fun level current => do
                  let instantiated ←
                    monadLift (TcM.ofExcept (substUniv level us))
                  let next := current.push instantiated
                  Pure.pure PUnit.unit
                  Pure.pure (ForInStep.yield next))
                (by
                  intro level current
                  apply stateBind
                    (stateLift (ofExcept (substUniv level us)))
                  intro instantiated
                  exact statePure
                    (ForInStep.yield (current.push instantiated))))
            intro newLevels
            apply stateBind (statePure (KExpr.mkConst id newLevels))
            intro result
            exact stateInternMemo (KExpr.const id levels info).addr result
      | app f a info ihf iha =>
          rw [TcM.instUnivInner]
          simp (config := { proj := false }) only []
          apply stateBind stateGet
          intro memo
          split
          · exact statePure _
          · apply stateBind ihf
            intro resultF
            apply stateBind iha
            intro resultA
            apply stateBind (statePure (KExpr.mkApp resultF resultA))
            intro result
            exact stateInternMemo (KExpr.app f a info).addr result
      | lam name bi ty body info ihty ihbody =>
          rw [TcM.instUnivInner]
          simp (config := { proj := false }) only []
          apply stateBind stateGet
          intro memo
          split
          · exact statePure _
          · apply stateBind ihty
            intro resultTy
            apply stateBind ihbody
            intro resultBody
            apply stateBind
              (statePure (KExpr.mkLam name bi resultTy resultBody))
            intro result
            exact stateInternMemo (KExpr.lam name bi ty body info).addr result
      | all name bi ty body info ihty ihbody =>
          rw [TcM.instUnivInner]
          simp (config := { proj := false }) only []
          apply stateBind stateGet
          intro memo
          split
          · exact statePure _
          · apply stateBind ihty
            intro resultTy
            apply stateBind ihbody
            intro resultBody
            apply stateBind
              (statePure (KExpr.mkAll name bi resultTy resultBody))
            intro result
            exact stateInternMemo (KExpr.all name bi ty body info).addr result
      | letE name ty value body nondep info ihty ihvalue ihbody =>
          rw [TcM.instUnivInner]
          simp (config := { proj := false }) only []
          apply stateBind stateGet
          intro memo
          split
          · exact statePure _
          · apply stateBind ihty
            intro resultTy
            apply stateBind ihvalue
            intro resultValue
            apply stateBind ihbody
            intro resultBody
            apply stateBind
              (statePure
                (KExpr.mkLet name resultTy resultValue resultBody nondep))
            intro result
            exact stateInternMemo
              (KExpr.letE name ty value body nondep info).addr result
      | prj id field value info ih =>
          rw [TcM.instUnivInner]
          simp (config := { proj := false }) only []
          apply stateBind stateGet
          intro memo
          split
          · exact statePure _
          · apply stateBind ih
            intro resultValue
            apply stateBind
              (statePure (KExpr.mkPrj id field resultValue))
            intro result
            exact stateInternMemo (KExpr.prj id field value info).addr result
      | nat value blob info =>
          simp only [TcM.instUnivInner]
          apply stateBind stateGet
          intro memo
          split
          · exact statePure _
          · apply stateBind (stateModify _)
            intro _
            exact statePure (KExpr.nat value blob info)
      | str value blob info =>
          simp only [TcM.instUnivInner]
          apply stateBind stateGet
          intro memo
          split
          · exact statePure _
          · apply stateBind (stateModify _)
            intro _
            exact statePure (KExpr.str value blob info)
    have hrun := hinner e ({} : Std.HashMap Address (KExpr .anon))
    unfold StateT.run'
    exact map hrun Prod.fst

end TcM.PreservesInferOnly

end Ix.Tc
