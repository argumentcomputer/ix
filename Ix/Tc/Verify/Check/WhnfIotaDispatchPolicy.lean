import Ix.Tc.Verify.Check.WhnfIotaSynthesisPolicy

/-!
# Operational inference-policy frame for complete iota dispatch

This module assembles ordinary constructor iota, struct eta, K synthesis,
Nat-offset cleanup, Nat and String literal expansion, and policy-selected
major normalization.  Its public theorem covers every branch of production
`tryIotaWithFlags`, completing the concrete iota helper obligation used by
the WHNF reducer frame.
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

theorem natToConstructor_preservesInferOnly
    {methods : Methods .anon} (value : Nat) :
    ((natToConstructor value).run methods).PreservesInferOnly := by
  unfold natToConstructor
  refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
  intro p
  split <;> exact TcM.PreservesInferOnly.pure _

theorem tryIotaCtorOrStructEta_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (recId : KId .anon) (recr : IotaInfo .anon)
    (recUs : Array (KUniv .anon)) (spine : Array (KExpr .anon))
    (majorWhnf : KExpr .anon) (transient : Bool) :
    ((tryIotaCtorOrStructEta recId recr recUs spine majorWhnf transient).run
      methods).PreservesInferOnly := by
  unfold tryIotaCtorOrStructEta
  rcases hspine : majorWhnf.collectSpine with ⟨ctorHead, ctorArgs⟩
  cases ctorHead with
  | const ctorId ctorUs ctorInfo =>
      refine bindTcM_preservesInferOnly
        (TcM.PreservesInferOnly.tryGetConst ctorId) ?_
      intro declaration
      cases declaration with
      | none =>
          simp only [pure_bind]
          exact tryStructEtaIota_preservesInferOnly hmethods recId recr recUs
            spine
      | some declaration =>
          cases declaration with
          | ctor name levelParams isUnsafe lvls induct cidx params fields ty =>
              simp only [KConst.iotaCtorInfo?, pure_bind]
              simpa only [ReaderT.run_bind, ReaderT.run_pure, bind_pure] using
                (tryApplyIotaCtor_preservesInferOnly recr recUs spine
                  ctorArgs cidx.toNat fields.toNat transient)
          | axio | defn | quot | indc | recr =>
              simp only [KConst.iotaCtorInfo?, pure_bind]
              exact tryStructEtaIota_preservesInferOnly hmethods recId recr
                recUs spine
  | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
      simp only [pure_bind]
      exact tryStructEtaIota_preservesInferOnly hmethods recId recr recUs spine

attribute [local irreducible] tryIotaCtorOrStructEta
  strLitToConstructor

theorem tryIotaAfterCleanup_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (flags : WhnfFlags) (recId : KId .anon) (recr : IotaInfo .anon)
    (recUs : Array (KUniv .anon)) (spine : Array (KExpr .anon))
    (majorWhnf : KExpr .anon) (majorWasNatLit : Bool) :
    ((tryIotaAfterCleanup flags recId recr recUs spine majorWhnf
      majorWasNatLit).run methods).PreservesInferOnly := by
  unfold tryIotaAfterCleanup
  cases majorWhnf with
  | str value blob info =>
      refine bind_preservesInferOnly
        (strLitToConstructor_preservesInferOnly value) ?_
      intro strCtor
      cases hcheap : flags.cheapRec with
      | true =>
          simp only [if_true]
          refine bind_preservesInferOnly
            (whnfCoreFlagsRec_preservesInferOnly hmethods strCtor flags) ?_
          intro normalized
          exact tryIotaCtorOrStructEta_preservesInferOnly hmethods recId recr
            recUs spine normalized majorWasNatLit
      | false =>
          simp only [Bool.false_eq_true, if_false]
          refine bind_preservesInferOnly
            (whnfRec_preservesInferOnly hmethods strCtor) ?_
          intro normalized
          exact tryIotaCtorOrStructEta_preservesInferOnly hmethods recId recr
            recUs spine normalized majorWasNatLit
  | var | fvar | sort | const | app | lam | all | letE | prj | nat =>
      simp only [pure_bind]
      exact tryIotaCtorOrStructEta_preservesInferOnly hmethods recId recr recUs
        spine _ majorWasNatLit

attribute [local irreducible] tryIotaAfterCleanup

theorem tryIotaAfterMajorWhnf_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (flags : WhnfFlags) (recId : KId .anon) (recr : IotaInfo .anon)
    (recUs : Array (KUniv .anon)) (spine : Array (KExpr .anon))
    (majorWhnf0 : KExpr .anon) :
    ((tryIotaAfterMajorWhnf flags recId recr recUs spine majorWhnf0).run
      methods).PreservesInferOnly := by
  unfold tryIotaAfterMajorWhnf
  cases majorWhnf0 with
  | nat value blob info =>
      refine bind_preservesInferOnly
        (natToConstructor_preservesInferOnly value) ?_
      intro majorWhnf
      simp only [pure_bind]
      refine bind_preservesInferOnly
        (cleanupNatOffsetMajor_preservesInferOnly majorWhnf) ?_
      intro cleaned
      cases cleaned with
      | none =>
          exact tryIotaAfterCleanup_preservesInferOnly hmethods flags recId
            recr recUs spine majorWhnf true
      | some cleaned =>
          exact tryIotaAfterCleanup_preservesInferOnly hmethods flags recId
            recr recUs spine cleaned true
  | var | fvar | sort | const | app | lam | all | letE | prj | str =>
      simp only [pure_bind]
      refine bind_preservesInferOnly
        (cleanupNatOffsetMajor_preservesInferOnly _) ?_
      intro cleaned
      cases cleaned with
      | none =>
          exact tryIotaAfterCleanup_preservesInferOnly hmethods flags recId
            recr recUs spine _ false
      | some cleaned =>
          exact tryIotaAfterCleanup_preservesInferOnly hmethods flags recId
            recr recUs spine cleaned false

attribute [local irreducible] tryIotaAfterMajorWhnf synthCtorWhenK

private theorem tryIotaMajor_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (flags : WhnfFlags) (recId : KId .anon) (recr : IotaInfo .anon)
    (recUs : Array (KUniv .anon)) (spine : Array (KExpr .anon))
    (major : KExpr .anon) :
    ((do
      let major := (← cleanupNatOffsetMajor major).getD major
      let majorWhnf0 ← if flags.cheapRec then
          whnfCoreFlagsRec major flags
        else whnfRec major
      tryIotaAfterMajorWhnf flags recId recr recUs spine majorWhnf0 :
      RecM .anon (Option (KExpr .anon))).run methods).PreservesInferOnly := by
  refine bind_preservesInferOnly
    (cleanupNatOffsetMajor_preservesInferOnly major) ?_
  intro cleaned
  let normalizedMajor := cleaned.getD major
  cases hcheap : flags.cheapRec with
  | true =>
      simp only [if_true]
      refine bind_preservesInferOnly
        (whnfCoreFlagsRec_preservesInferOnly hmethods normalizedMajor flags) ?_
      intro majorWhnf0
      exact tryIotaAfterMajorWhnf_preservesInferOnly hmethods flags recId recr
        recUs spine majorWhnf0
  | false =>
      simp only [Bool.false_eq_true, if_false]
      refine bind_preservesInferOnly
        (whnfRec_preservesInferOnly hmethods normalizedMajor) ?_
      intro majorWhnf0
      exact tryIotaAfterMajorWhnf_preservesInferOnly hmethods flags recId recr
        recUs spine majorWhnf0

private theorem tryIotaSelected_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (flags : WhnfFlags) (recId : KId .anon) (recr : IotaInfo .anon)
    (recUs : Array (KUniv .anon)) (spine : Array (KExpr .anon)) :
    ((do
      if spine.size ≤ recr.majorIdx then
        return none
      let major := spine[recr.majorIdx]!
      let major ← if recr.k then
          match (← synthCtorWhenK major recId recr recUs).selectMajor major with
          | some selected => pure selected
          | none => return none
        else pure major
      let major := (← cleanupNatOffsetMajor major).getD major
      let majorWhnf0 ← if flags.cheapRec then
          whnfCoreFlagsRec major flags
        else whnfRec major
      tryIotaAfterMajorWhnf flags recId recr recUs spine majorWhnf0 :
      RecM .anon (Option (KExpr .anon))).run methods).PreservesInferOnly := by
  by_cases hmajor : spine.size ≤ recr.majorIdx
  · simp only [hmajor, if_pos]
    exact TcM.PreservesInferOnly.pure none
  · simp only [hmajor, if_false, pure_bind]
    let major := spine[recr.majorIdx]!
    cases hk : recr.k with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        exact tryIotaMajor_preservesInferOnly hmethods flags recId recr recUs
          spine major
    | true =>
        simp only [if_true]
        refine bind_preservesInferOnly
          (synthCtorWhenK_preservesInferOnly hmethods major recId recr recUs) ?_
        intro synthesized
        cases synthesized with
        | synthesized ctor =>
            exact tryIotaMajor_preservesInferOnly hmethods flags recId recr recUs
              spine ctor
        | definitiveReject =>
            exact TcM.PreservesInferOnly.pure none
        | inconclusive =>
            exact tryIotaMajor_preservesInferOnly hmethods flags recId recr recUs
              spine major

theorem tryIotaWithFlags_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (source : KExpr .anon) (flags : WhnfFlags) :
    ((tryIotaWithFlags source flags).run methods).PreservesInferOnly := by
  unfold tryIotaWithFlags
  rcases hspine : source.collectSpine with ⟨head, spine⟩
  cases head with
  | const recId recUs info =>
      refine bindTcM_preservesInferOnly
        (TcM.PreservesInferOnly.tryGetConst recId) ?_
      intro declaration
      cases declaration with
      | none => exact TcM.PreservesInferOnly.pure none
      | some declaration =>
          simp only []
          cases hinfo : declaration.iotaInfo? with
          | none =>
              simp only []
              exact TcM.PreservesInferOnly.pure none
          | some recr =>
              simp only []
              by_cases hmajor : spine.size ≤ recr.majorIdx
              · simp only [hmajor, if_pos]
                exact TcM.PreservesInferOnly.pure none
              · simp only [hmajor, if_false, pure_bind]
                let major := spine[recr.majorIdx]!
                cases hk : recr.k with
                | false =>
                    simp only [Bool.false_eq_true, if_false]
                    exact tryIotaMajor_preservesInferOnly hmethods flags recId
                      recr recUs spine major
                | true =>
                    simp only [if_true]
                    refine bind_preservesInferOnly
                      (synthCtorWhenK_preservesInferOnly hmethods major recId
                        recr recUs) ?_
                    intro synthesized
                    cases synthesized with
                    | synthesized ctor =>
                        exact tryIotaMajor_preservesInferOnly hmethods flags
                          recId recr recUs spine ctor
                    | definitiveReject =>
                        exact TcM.PreservesInferOnly.pure none
                    | inconclusive =>
                        exact tryIotaMajor_preservesInferOnly hmethods flags
                          recId recr recUs spine major
  | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
      exact TcM.PreservesInferOnly.pure none

end RecM
end Ix.Tc
