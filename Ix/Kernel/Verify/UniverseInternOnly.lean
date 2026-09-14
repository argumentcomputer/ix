/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Monad

/-!
# Exact state effects of universe instantiation

The production memoized walker changes only its private scratch map and the
expression intern table. This exact frame holds for cache hits, all syntax
constructors, the level-array loop, and partial failures. It needs no hash or
semantic assumptions, and supports both the named policy proof and the direct
set-model state proof.

The structural walker proof is shared from the earlier inference-policy
development in `Check/UniverseInstantiationPolicy.lean`.
-/

namespace Ix.Kernel

/-- The action changes only the expression intern table, on success and on
failure. Its result may depend on that table; this contract concerns effects. -/
def TcM.InternOnly (action : TcM .anon α) : Prop :=
  ∀ before, match action before with
    | .ok _ after | .error _ after =>
      ∃ table, after = {before with env := {before.env with intern := table}}

namespace TcM.InternOnly

theorem pure (value : α) : (Pure.pure value : TcM .anon α).InternOnly :=
  fun before => ⟨before.env.intern, rfl⟩

theorem throw (error : TcError .anon) : (throw error : TcM .anon α).InternOnly :=
  fun before => ⟨before.env.intern, rfl⟩

theorem bind {action : TcM .anon α} {next : α → TcM .anon γ}
    (first : action.InternOnly) (rest : ∀ value, (next value).InternOnly) :
    (action >>= next).InternOnly := by
  intro before
  have intermediate := first before
  change match EStateM.bind action next before with
    | .ok _ after | .error _ after =>
      ∃ table, after = {before with env := {before.env with intern := table}}
  cases run : action before with
  | error error after => rw [EStateM.bind, run]; simpa only [run] using intermediate
  | ok value after =>
      rw [run] at intermediate
      obtain ⟨table, changed⟩ := intermediate
      rw [EStateM.bind, run]
      dsimp only
      have final := rest value after
      cases finished : next value after <;> rw [finished] at final <;>
        obtain ⟨newTable, changedAgain⟩ := final <;>
        exact ⟨newTable, by rw [changedAgain, changed]⟩

theorem runIntern (action : InternM .anon α) : (TcM.runIntern action).InternOnly :=
  fun before => ⟨(action before.env.intern).2, rfl⟩

theorem ofExcept (value : Except (TcError .anon) alpha) :
    (TcM.ofExcept value).InternOnly := by
  cases value with
  | ok value => exact pure value
  | error err => exact throw err

theorem map {x : TcM .anon alpha} (hx : x.InternOnly)
    (f : alpha → beta) : (f <$> x).InternOnly := by
  rw [← bind_pure_comp]
  exact bind hx fun value => pure (f value)

private def StateInternOnly
    (x : StateT sigma (TcM .anon) alpha) : Prop :=
  ∀ memo, (x.run memo).InternOnly

private theorem statePure (value : alpha) :
    StateInternOnly
      (Pure.pure value : StateT sigma (TcM .anon) alpha) := by
  intro memo
  simp only [StateT.run_pure]
  exact TcM.InternOnly.pure _

private theorem stateBind {x : StateT sigma (TcM .anon) alpha}
    {f : alpha → StateT sigma (TcM .anon) beta}
    (hx : StateInternOnly x)
    (hf : ∀ value, StateInternOnly (f value)) :
    StateInternOnly (x >>= f) := by
  intro memo
  simp only [StateT.run_bind]
  apply TcM.InternOnly.bind (hx memo)
  intro pair
  exact hf pair.1 pair.2

private theorem stateGet :
    StateInternOnly
      (MonadState.get : StateT sigma (TcM .anon) sigma) := by
  intro memo
  simp only [StateT.run_get]
  exact TcM.InternOnly.pure _

private theorem stateModify (f : sigma → sigma) :
    StateInternOnly
      (_root_.modify f : StateT sigma (TcM .anon) PUnit) := by
  intro memo
  simp only [StateT.run_modify]
  exact TcM.InternOnly.pure _

private theorem stateLift {x : TcM .anon alpha}
    (hx : x.InternOnly) :
    StateInternOnly
      (monadLift x : StateT sigma (TcM .anon) alpha) := by
  intro memo
  simp only [StateT.run_monadLift]
  apply TcM.InternOnly.bind hx
  intro value
  exact TcM.InternOnly.pure _

private theorem stateForInArray
    (items : Array alpha) (initial : beta)
    (step : alpha → beta →
      StateT sigma (TcM .anon) (ForInStep beta))
    (hstep : ∀ item state,
      StateInternOnly (step item state)) :
    StateInternOnly (forIn items initial step) := by
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
    StateInternOnly (do
      let interned ← monadLift (TcM.intern result)
      _root_.modify fun memo : Std.HashMap Address (KExpr .anon) =>
        memo.insert key interned
      Pure.pure interned) := by
  apply stateBind (stateLift (runIntern _))
  intro interned
  apply stateBind (stateModify _)
  intro _
  exact statePure interned

/-- Universe instantiation changes only the actual expression intern table.
The statement is unconditional: collision freedom constrains the returned
syntax, while this theorem covers the walker's state effects. -/
theorem instantiateUnivParams (e : KExpr .anon)
    (us : Array (KUniv .anon)) :
    (TcM.instantiateUnivParams e us).InternOnly := by
  unfold TcM.instantiateUnivParams
  split
  · exact pure e
  · have hinner : ∀ (source : KExpr .anon),
        StateInternOnly (TcM.instUnivInner source us) := by
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

end TcM.InternOnly

end Ix.Kernel
