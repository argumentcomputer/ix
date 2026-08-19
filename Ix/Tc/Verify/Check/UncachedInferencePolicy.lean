import Ix.Tc.Verify.Check.UniverseInstantiationPolicy
import Ix.Tc.Verify.Check.FullInferenceProjections

/-!
# Operational policy for uncached inference

The production inference dispatcher temporarily mutates several checker
fields, opens local-context scopes, and delegates through the recursive
method table.  This module proves independently of semantic typing that one
uncached dispatcher layer preserves the caller's `inferOnly` policy on both
success and partial error.

The projection branch remains an explicit input because its helper contains
its own recursive WHNF and inference loops.  Closing that helper supplies the
last premise needed to feed this theorem into the already verified inference
cache shell.
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

theorem inferUncached_preservesInferOnly
    (methods : Methods .anon)
    (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly)
    (hprojection : ProjectionInference.PreservesInferOnlyAt methods)
    (inferOnly : Bool) (source : KExpr .anon) :
    ((inferUncached inferCall inferOnly source).run methods).PreservesInferOnly := by
  cases source with
  | var idx name info =>
      simpa [inferUncached] using TcM.PreservesInferOnly.lookupVar idx
  | fvar id name info =>
      unfold inferUncached
      simp only [ReaderT.run_bind]
      apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
      intro state
      split
      · exact TcM.PreservesInferOnly.pure _
      · exact TcM.PreservesInferOnly.throw _
  | sort u info =>
      simpa [inferUncached, TcM.intern] using
        (TcM.PreservesInferOnly.runIntern
          (internExprM (KExpr.mkSort (KUniv.mkSucc u))))
  | const id levels info =>
      unfold inferUncached
      simp only [ReaderT.run_bind, ReaderT.run_monadLift]
      apply TcM.PreservesInferOnly.bind
        (TcM.PreservesInferOnly.getConst id)
      intro concrete
      split
      · exact TcM.PreservesInferOnly.throw _
      · exact TcM.PreservesInferOnly.instantiateUnivParams
          concrete.ty levels
  | app f a info =>
      unfold inferUncached
      simp only [ReaderT.run_bind, ReaderT.run_monadLift, inferCall,
        isDefEqCall]
      apply TcM.PreservesInferOnly.bind (hmethods.infer f)
      intro fTy
      apply TcM.PreservesInferOnly.bind
        (ensureForallDirect_preservesInferOnly hwhnf)
      intro domCod
      rcases domCod with ⟨dom, cod⟩
      cases inferOnly with
      | true =>
          exact TcM.PreservesInferOnly.runIntern (subst cod a 0)
      | false =>
          apply TcM.PreservesInferOnly.bind (hmethods.infer a)
          intro aTy
          apply TcM.PreservesInferOnly.bind
            (TcM.PreservesInferOnly.isEagerReduce a)
          intro isEager
          cases isEager with
          | false =>
              simp only [Bool.false_eq_true, if_false, pure_bind]
              apply TcM.PreservesInferOnly.bind (hmethods.isDefEq aTy dom)
              intro equal
              cases equal with
              | false =>
                  simp only [Bool.not_false, if_true]
                  apply TcM.PreservesInferOnly.bind
                    TcM.PreservesInferOnly.get
                  intro state
                  exact TcM.PreservesInferOnly.throw (alpha := KExpr .anon)
                    (.appTypeMismatch aTy dom state.ctx.size)
              | true =>
                  simp only [Bool.not_true]
                  exact TcM.PreservesInferOnly.runIntern (subst cod a 0)
          | true =>
              simp only [if_true]
              show ((do
                modify fun state : TcState .anon =>
                  { state with eagerReduce := true }
                let equal ← isDefEqCall aTy dom
                modify fun state : TcState .anon =>
                  { state with eagerReduce := false }
                if !equal then
                  throw (TcError.appTypeMismatch aTy dom (← get).ctx.size)
                TcM.runIntern (subst cod a 0) : RecM .anon (KExpr .anon)).run
                  methods).PreservesInferOnly
              simp only [ReaderT.run_bind, ReaderT.run_monadLift,
                isDefEqCall]
              apply TcM.PreservesInferOnly.bind
                (TcM.PreservesInferOnly.modify
                  (f := fun state : TcState .anon =>
                    { state with eagerReduce := true }) (fun _ => rfl))
              intro _
              apply TcM.PreservesInferOnly.bind (hmethods.isDefEq aTy dom)
              intro equal
              apply TcM.PreservesInferOnly.bind
                (TcM.PreservesInferOnly.modify
                  (f := fun state : TcState .anon =>
                    { state with eagerReduce := false }) (fun _ => rfl))
              intro _
              cases equal with
              | false =>
                  simp only [Bool.not_false, if_true]
                  apply TcM.PreservesInferOnly.bind
                    TcM.PreservesInferOnly.get
                  intro state
                  exact TcM.PreservesInferOnly.throw (alpha := KExpr .anon)
                    (.appTypeMismatch aTy dom state.ctx.size)
              | true =>
                  simp only [Bool.not_true, pure_bind]
                  exact TcM.PreservesInferOnly.runIntern (subst cod a 0)
  | lam name bi ty body info =>
      unfold inferUncached
      simp only [inferCall]
      cases inferOnly with
      | true =>
          simp only [Bool.not_true, pure_bind]
          apply withLctxScope_preservesInferOnly
          simp only [ReaderT.run_bind, ReaderT.run_monadLift]
          apply TcM.PreservesInferOnly.bind
            (TcM.PreservesInferOnly.openBinder name bi ty body)
          intro opened
          rcases opened with ⟨bodyOpen, fvId⟩
          apply TcM.PreservesInferOnly.bind (hmethods.infer bodyOpen)
          intro bodyTy
          apply TcM.PreservesInferOnly.bind
            (TcM.PreservesInferOnly.runIntern (cheapBetaReduce bodyTy))
          intro reduced
          apply TcM.PreservesInferOnly.bind
            (TcM.PreservesInferOnly.runIntern
              (abstractFVars reduced #[fvId]))
          intro abstracted
          exact TcM.PreservesInferOnly.runIntern
            (internExprM (.mkAll anonN anonBi ty abstracted))
      | false =>
          simp only [Bool.not_false, if_true]
          apply TcM.PreservesInferOnly.bind (hmethods.infer ty)
          intro tyTy
          apply TcM.PreservesInferOnly.bind
            (ensureSortDirect_preservesInferOnly hwhnf)
          intro _
          apply withLctxScope_preservesInferOnly
          simp only [ReaderT.run_bind, ReaderT.run_monadLift]
          apply TcM.PreservesInferOnly.bind
            (TcM.PreservesInferOnly.openBinder name bi ty body)
          intro opened
          rcases opened with ⟨bodyOpen, fvId⟩
          apply TcM.PreservesInferOnly.bind (hmethods.infer bodyOpen)
          intro bodyTy
          apply TcM.PreservesInferOnly.bind
            (TcM.PreservesInferOnly.runIntern (cheapBetaReduce bodyTy))
          intro reduced
          apply TcM.PreservesInferOnly.bind
            (TcM.PreservesInferOnly.runIntern
              (abstractFVars reduced #[fvId]))
          intro abstracted
          exact TcM.PreservesInferOnly.runIntern
            (internExprM (.mkAll anonN anonBi ty abstracted))
  | all name bi ty body info =>
      unfold inferUncached
      simp only [ReaderT.run_bind, ReaderT.run_monadLift, inferCall]
      apply TcM.PreservesInferOnly.bind (hmethods.infer ty)
      intro tyTy
      apply TcM.PreservesInferOnly.bind
        (ensureSortDirect_preservesInferOnly hwhnf)
      intro domainLevel
      apply withLctxScope_preservesInferOnly
      simp only [ReaderT.run_bind, ReaderT.run_monadLift]
      apply TcM.PreservesInferOnly.bind
        (TcM.PreservesInferOnly.openBinder name bi ty body)
      intro opened
      rcases opened with ⟨bodyOpen, _⟩
      apply TcM.PreservesInferOnly.bind (hmethods.infer bodyOpen)
      intro bodyTy
      apply TcM.PreservesInferOnly.bind
        (ensureSortDirect_preservesInferOnly hwhnf)
      intro bodyLevel
      exact TcM.PreservesInferOnly.runIntern
        (internExprM (.mkSort (.mkIMax domainLevel bodyLevel)))
  | letE name ty value body nondep info =>
      unfold inferUncached
      simp only [inferCall, isDefEqCall]
      cases inferOnly with
      | true =>
          simp only [Bool.not_true, pure_bind]
          apply withLctxScope_preservesInferOnly
          simp only [ReaderT.run_bind, ReaderT.run_monadLift]
          apply TcM.PreservesInferOnly.bind
            (TcM.PreservesInferOnly.openLet name ty value body)
          intro opened
          rcases opened with ⟨bodyOpen, fvId⟩
          apply TcM.PreservesInferOnly.bind (hmethods.infer bodyOpen)
          intro bodyTy
          apply TcM.PreservesInferOnly.bind
            (TcM.PreservesInferOnly.runIntern
              (abstractFVars bodyTy #[fvId]))
          intro abstracted
          apply TcM.PreservesInferOnly.bind
            (TcM.PreservesInferOnly.runIntern
              (subst abstracted value 0))
          intro substituted
          exact TcM.PreservesInferOnly.runIntern
            (cheapBetaReduce substituted)
      | false =>
          simp only [Bool.not_false, if_true]
          apply TcM.PreservesInferOnly.bind (hmethods.infer ty)
          intro tyTy
          apply TcM.PreservesInferOnly.bind
            (ensureSortDirect_preservesInferOnly hwhnf)
          intro _
          apply TcM.PreservesInferOnly.bind (hmethods.infer value)
          intro valueTy
          apply TcM.PreservesInferOnly.bind (hmethods.isDefEq valueTy ty)
          intro equal
          cases equal with
          | false =>
              simp only [Bool.not_false, if_true]
              exact TcM.PreservesInferOnly.throw (alpha := KExpr .anon)
                .declTypeMismatch
          | true =>
              simp only [Bool.not_true, pure_bind]
              apply withLctxScope_preservesInferOnly
              simp only [ReaderT.run_bind, ReaderT.run_monadLift]
              apply TcM.PreservesInferOnly.bind
                (TcM.PreservesInferOnly.openLet name ty value body)
              intro opened
              rcases opened with ⟨bodyOpen, fvId⟩
              apply TcM.PreservesInferOnly.bind (hmethods.infer bodyOpen)
              intro bodyTy
              apply TcM.PreservesInferOnly.bind
                (TcM.PreservesInferOnly.runIntern
                  (abstractFVars bodyTy #[fvId]))
              intro abstracted
              apply TcM.PreservesInferOnly.bind
                (TcM.PreservesInferOnly.runIntern
                  (subst abstracted value 0))
              intro substituted
              exact TcM.PreservesInferOnly.runIntern
                (cheapBetaReduce substituted)
  | prj id field value info =>
      unfold inferUncached
      simp only [ReaderT.run_bind, ReaderT.run_monadLift, inferCall]
      apply TcM.PreservesInferOnly.bind (hmethods.infer value)
      intro valueTy
      exact hprojection id field value valueTy
  | nat value blob info =>
      unfold inferUncached
      simp only [ReaderT.run_bind, ReaderT.run_monadLift]
      apply TcM.PreservesInferOnly.bind
        (prims_preservesInferOnly methods)
      intro primitives
      exact TcM.PreservesInferOnly.runIntern
        (internExprM (.mkConst primitives.nat #[]))
  | str value blob info =>
      unfold inferUncached
      simp only [ReaderT.run_bind, ReaderT.run_monadLift]
      apply TcM.PreservesInferOnly.bind
        (prims_preservesInferOnly methods)
      intro primitives
      exact TcM.PreservesInferOnly.runIntern
        (internExprM (.mkConst primitives.string #[]))

end RecM

end Ix.Tc
