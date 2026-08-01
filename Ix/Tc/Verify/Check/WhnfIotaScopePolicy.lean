import Ix.Tc.Verify.Check.WhnfIotaBasePolicy

/-!
# Operational inference-policy frame for scoped iota callbacks

This module verifies the legacy-context operations, balanced dispatch-depth
wrapper, bounded recursor-type telescope scan, and its error-safe depth
restoration.  These are the scoped callback primitives shared by struct eta
and K-like constructor synthesis.
-/

namespace Ix.Tc


namespace TcM.PreservesInferOnly

theorem pushLocal (ty : KExpr .anon) :
    (TcM.pushLocal ty).PreservesInferOnly := by
  intro before
  rfl

theorem popLocal :
    (TcM.popLocal (m := .anon)).PreservesInferOnly := by
  intro before
  rfl

theorem saveDepth :
    (TcM.saveDepth (m := .anon)).PreservesInferOnly := by
  intro before
  rfl

private theorem restoreDepthGo (saved : Nat) : ∀ fuel,
    (TcM.restoreDepth.go (m := .anon) saved fuel).PreservesInferOnly
  | 0 => by
      rw [TcM.restoreDepth.go]
      exact pure ()
  | fuel + 1 => by
      rw [TcM.restoreDepth.go]
      apply bind get
      intro state
      split
      · exact bind popLocal fun _ => restoreDepthGo saved fuel
      · exact pure ()

theorem restoreDepth (saved : Nat) :
    (TcM.restoreDepth (m := .anon) saved).PreservesInferOnly := by
  unfold TcM.restoreDepth
  apply bind get
  intro state
  exact restoreDepthGo saved (state.ctx.size - saved)

theorem enterDispatch :
    (RecM.enterDispatch (m := .anon)).PreservesInferOnly := by
  apply ofWF
  intro before
  unfold RecM.enterDispatch
  apply TcM.WF.bind
    (Q₁ := fun observed after => observed = before ∧ after = before)
    (TcM.WF.get fun _ => ⟨rfl, rfl⟩)
  intro observed after hread
  rcases hread with ⟨rfl, rfl⟩
  simp only
  split
  · exact TcM.WF.throw (fun _ => trivial)
  · exact TcM.WF.set (fun _ => rfl) (fun _ => trivial)

theorem exitDispatch :
    (RecM.exitDispatch (m := .anon)).PreservesInferOnly := by
  intro before
  rfl

end TcM.PreservesInferOnly

namespace RecM

theorem callIsDefEq_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (left right : KExpr .anon) :
    ((callIsDefEq left right).run methods).PreservesInferOnly := by
  unfold callIsDefEq
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.enterDispatch
  intro _
  change (tryFinally (methods.isDefEq left right)
    (RecM.exitDispatch (m := .anon))).PreservesInferOnly
  exact TcM.PreservesInferOnly.tryFinally
    (hmethods.isDefEq left right) TcM.PreservesInferOnly.exitDispatch

theorem peelMajorForalls_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly) :
    ∀ fuel source,
      ((peelMajorForalls fuel source).run methods).PreservesInferOnly
  | 0, source => by
      rw [peelMajorForalls]
      exact TcM.PreservesInferOnly.pure source
  | fuel + 1, source => by
      rw [peelMajorForalls]
      refine bind_preservesInferOnly
        (whnfRec_preservesInferOnly hmethods source) ?_
      intro normalized
      cases normalized with
      | all name bi domain body info =>
          simp only [ReaderT.run_bind, ReaderT.run_monadLift]
          apply TcM.PreservesInferOnly.bind
            (TcM.PreservesInferOnly.pushLocal domain)
          intro _
          exact peelMajorForalls_preservesInferOnly hmethods fuel body
      | var | fvar | sort | const | app | lam | letE | prj | nat | str =>
          exact TcM.PreservesInferOnly.throw _

theorem scanMajorInductiveStep_preservesInferOnly
    {methods : Methods .anon} (next : KExpr .anon → RecM .anon (KId .anon))
    (hnext : ∀ source, ((next source).run methods).PreservesInferOnly)
    (normalized : KExpr .anon) :
    ((scanMajorInductiveStep next normalized).run
      methods).PreservesInferOnly := by
  unfold scanMajorInductiveStep
  cases normalized with
  | all name bi domain body info =>
      generalize hhead : domain.collectSpine.1 = head
      cases head with
      | const id levels headInfo =>
          simp only [hhead]
          refine bindTcM_preservesInferOnly
            (TcM.PreservesInferOnly.tryGetConst id) ?_
          intro found
          cases found with
          | some declaration =>
              cases declaration with
              | indc => exact TcM.PreservesInferOnly.pure id
              | axio | defn | quot | ctor | recr =>
                  simp only [pure_bind]
                  refine bindTcM_preservesInferOnly
                    (TcM.PreservesInferOnly.pushLocal domain) ?_
                  intro _
                  exact hnext body
          | none =>
              simp only [pure_bind]
              refine bindTcM_preservesInferOnly
                (TcM.PreservesInferOnly.pushLocal domain) ?_
              intro _
              exact hnext body
      | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
          simp only [hhead, pure_bind]
          refine bindTcM_preservesInferOnly
            (TcM.PreservesInferOnly.pushLocal domain) ?_
          intro _
          exact hnext body
  | var | fvar | sort | const | app | lam | letE | prj | nat | str =>
      exact TcM.PreservesInferOnly.throw _

theorem scanMajorInductive_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly) :
    ∀ fuel source,
      ((scanMajorInductive fuel source).run methods).PreservesInferOnly
  | 0, source => by
      rw [scanMajorInductive]
      exact TcM.PreservesInferOnly.throw _
  | fuel + 1, source => by
      rw [scanMajorInductive]
      refine bind_preservesInferOnly
        (whnfRec_preservesInferOnly hmethods source) ?_
      intro normalized
      exact scanMajorInductiveStep_preservesInferOnly
        (scanMajorInductive fuel)
        (scanMajorInductive_preservesInferOnly hmethods fuel) normalized

theorem getMajorInductiveId_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (recTy : KExpr .anon) (skip : UInt64) :
    ((getMajorInductiveId recTy skip).run methods).PreservesInferOnly := by
  unfold getMajorInductiveId
  refine bindTcM_preservesInferOnly TcM.PreservesInferOnly.saveDepth ?_
  intro saved
  change (tryFinally
    ((do
      let ty ← peelMajorForalls skip.toNat recTy
      scanMajorInductive 9 ty).run methods)
    (TcM.restoreDepth (m := .anon) saved)).PreservesInferOnly
  apply TcM.PreservesInferOnly.tryFinally
  · refine bind_preservesInferOnly
      (peelMajorForalls_preservesInferOnly hmethods skip.toNat recTy) ?_
    intro ty
    exact scanMajorInductive_preservesInferOnly hmethods 9 ty
  · exact TcM.PreservesInferOnly.restoreDepth saved

end RecM

end Ix.Tc
