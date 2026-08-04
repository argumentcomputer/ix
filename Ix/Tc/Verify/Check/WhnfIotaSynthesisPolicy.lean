import Ix.Tc.Verify.Check.WhnfIotaRecursionPolicy

/-!
# Operational inference-policy frame for struct eta and K synthesis

This module verifies both iota fallbacks that synthesize constructor-shaped
terms: struct eta for non-recursive one-constructor inductives and K-like
nullary-constructor synthesis.  It covers scoped type scans, optional
inference and WHNF probes, universe instantiation, projection rebuilding,
DefEq validation, and synthesis statistics on acceptance and rejection.
-/

namespace Ix.Tc
namespace RecM


theorem isStructLike_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (id : KId .anon) :
    ((isStructLike id).run methods).PreservesInferOnly := by
  unfold isStructLike
  refine bindTcM_preservesInferOnly
    (TcM.PreservesInferOnly.tryGetConst id) ?_
  intro declaration
  cases declaration with
  | none => exact TcM.PreservesInferOnly.pure false
  | some declaration =>
      cases declaration with
      | indc name levelParams lvls params indices isUnsafe block memberIdx ty
          ctors leanAll =>
          by_cases hinvalid : indices != 0 || ctors.size != 1
          · simp only [hinvalid, if_pos]
            exact TcM.PreservesInferOnly.pure false
          · simp only [hinvalid, pure_bind]
            refine bind_preservesInferOnly
              (computedIsRec_preservesInferOnly hmethods id) ?_
            intro recursive
            exact TcM.PreservesInferOnly.pure (!recursive)
      | axio | defn | quot | ctor | recr =>
          exact TcM.PreservesInferOnly.pure false

theorem finishStructEtaFields_preservesInferOnly
    {methods : Methods .anon} (indId : KId .anon)
    (major : KExpr .anon) : ∀ fuel field result,
    ((finishStructEtaFields indId major fuel field result).run
      methods).PreservesInferOnly
  | 0, field, result => by
      rw [finishStructEtaFields]
      exact TcM.PreservesInferOnly.pure result
  | fuel + 1, field, result => by
      rw [finishStructEtaFields]
      refine bindIntern_preservesInferOnly
        (.mkPrj indId field.toUInt64 major) ?_
      intro proj
      refine bindIntern_preservesInferOnly (.mkApp result proj) ?_
      intro next
      exact finishStructEtaFields_preservesInferOnly indId major fuel
        (field + 1) next

theorem finishStructEtaResult_preservesInferOnly
    {methods : Methods .anon} (indId : KId .anon)
    (major rhs : KExpr .anon) (fields : UInt64)
    (prefixArgs trailingArgs : Array (KExpr .anon)) :
    ((finishStructEtaResult indId major rhs fields prefixArgs trailingArgs).run
      methods).PreservesInferOnly := by
  unfold finishStructEtaResult
  refine bind_preservesInferOnly
    (finishAppResult_preservesInferOnly rhs prefixArgs 0) ?_
  intro prefixResult
  refine bind_preservesInferOnly
    (finishStructEtaFields_preservesInferOnly indId major fields.toNat 0
      prefixResult) ?_
  intro fieldResult
  exact finishAppResult_preservesInferOnly fieldResult trailingArgs 0

attribute [local irreducible] finishStructEtaResult

theorem finishStructEtaAfterSort_preservesInferOnly
    {methods : Methods .anon} (recUs : Array (KUniv .anon))
    (spine : Array (KExpr .anon)) (recr : IotaInfo .anon)
    (rule : RecRule .anon) (indId : KId .anon)
    (major majorSortW : KExpr .anon) :
    ((finishStructEtaAfterSort recUs spine recr rule indId major majorSortW).run
      methods).PreservesInferOnly := by
  unfold finishStructEtaAfterSort
  by_cases hrejected : structEtaSortRejected majorSortW
  · simp only [hrejected, if_pos]
    exact TcM.PreservesInferOnly.pure none
  · simp only [hrejected]
    let pmmEnd := recr.params + recr.motives + recr.minors
    have htail :
        ((do
          let rhs ← TcM.instantiateUnivParams rule.rhs recUs
          let result ← finishStructEtaResult indId major rhs rule.fields
            (spine.extract 0 (min pmmEnd spine.size))
            (spine.extract (recr.majorIdx + 1) spine.size)
          return some result : RecM .anon (Option (KExpr .anon))).run
          methods).PreservesInferOnly := by
      refine bindTcM_preservesInferOnly
        (TcM.PreservesInferOnly.instantiateUnivParams rule.rhs recUs) ?_
      intro rhs
      refine bind_preservesInferOnly
        (finishStructEtaResult_preservesInferOnly indId major rhs rule.fields
          (spine.extract 0 (min pmmEnd spine.size))
          (spine.extract (recr.majorIdx + 1) spine.size)) ?_
      intro result
      exact TcM.PreservesInferOnly.pure (some result)
    simpa only [pure_bind] using htail

theorem tryStructEtaAfterInductive_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (recUs : Array (KUniv .anon)) (spine : Array (KExpr .anon))
    (recr : IotaInfo .anon) (rule : RecRule .anon) (indId : KId .anon) :
    ((tryStructEtaAfterInductive recUs spine recr rule indId).run
      methods).PreservesInferOnly := by
  unfold tryStructEtaAfterInductive
  refine bind_preservesInferOnly (isStructLike_preservesInferOnly hmethods indId) ?_
  intro structLike
  cases structLike with
  | false =>
      simp only [Bool.not_false, if_true]
      exact TcM.PreservesInferOnly.pure none
  | true =>
      simp only [Bool.not_true, pure_bind]
      let major := spine[recr.majorIdx]!
      refine bind_preservesInferOnly
        (tryOptional_preservesInferOnly
          (inferOnlyRec_preservesInferOnly hmethods major)) ?_
      intro majorTyResult
      cases majorTyResult with
      | none => exact TcM.PreservesInferOnly.pure none
      | some majorTy =>
          simp only []
          refine bind_preservesInferOnly
            (tryOptional_preservesInferOnly
              (inferOnlyRec_preservesInferOnly hmethods majorTy)) ?_
          intro majorSortResult
          cases majorSortResult with
          | none => exact TcM.PreservesInferOnly.pure none
          | some majorSort =>
              simp only []
              refine bind_preservesInferOnly
                (tryOptional_preservesInferOnly
                  (whnfRec_preservesInferOnly hmethods majorSort)) ?_
              intro majorSortWResult
              cases majorSortWResult with
              | none => exact TcM.PreservesInferOnly.pure none
              | some majorSortW =>
                  exact finishStructEtaAfterSort_preservesInferOnly recUs
                    spine recr rule indId major majorSortW

attribute [local irreducible] tryStructEtaAfterInductive

theorem tryStructEtaIota_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (recId : KId .anon) (recr : IotaInfo .anon)
    (recUs : Array (KUniv .anon)) (spine : Array (KExpr .anon)) :
    ((tryStructEtaIota recId recr recUs spine).run
      methods).PreservesInferOnly := by
  unfold tryStructEtaIota
  by_cases hrules : recr.rules.size != 1
  · simp only [hrules, if_pos]
    exact TcM.PreservesInferOnly.pure none
  · simp only [hrules, Bool.false_eq_true, if_false, pure_bind]
    by_cases hlevels : recUs.size.toUInt64 != recr.lvls
    · simp only [hlevels, if_pos]
      exact TcM.PreservesInferOnly.pure none
    · simp only [hlevels, Bool.false_eq_true, if_false]
      let rule := recr.rules[0]!
      refine bindTcM_preservesInferOnly
        (TcM.PreservesInferOnly.tryGetConst recId) ?_
      intro declaration
      cases declaration with
      | none => exact TcM.PreservesInferOnly.pure none
      | some declaration =>
          let recTy := declaration.ty
          let skip :=
            (recr.params + recr.motives + recr.minors +
              recr.indices).toUInt64
          have hscan :
              ((do
                let recTy ← TcM.instantiateUnivParams recTy recUs
                getMajorInductiveId recTy skip : RecM .anon (KId .anon)).run
                methods).PreservesInferOnly := by
            refine bindTcM_preservesInferOnly
              (TcM.PreservesInferOnly.instantiateUnivParams recTy recUs) ?_
            intro instantiated
            exact getMajorInductiveId_preservesInferOnly hmethods
              instantiated skip
          refine bind_preservesInferOnly
            (tryOptional_preservesInferOnly hscan) ?_
          intro indResult
          cases indResult with
          | none => exact TcM.PreservesInferOnly.pure none
          | some indId =>
              exact tryStructEtaAfterInductive_preservesInferOnly hmethods
                recUs spine recr rule indId

theorem verifyKSynthCandidate_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (majorTyW : KExpr .anon) (ctorId : KId .anon)
    (tyUs : Array (KUniv .anon)) (tyArgs : Array (KExpr .anon))
    (params : Nat) :
    ((verifyKSynthCandidate majorTyW ctorId tyUs tyArgs params).run
      methods).PreservesInferOnly := by
  unfold verifyKSynthCandidate
  refine bindIntern_preservesInferOnly (.mkConst ctorId tyUs) ?_
  intro ctorHead
  refine bind_preservesInferOnly
    (finishAppResult_preservesInferOnly ctorHead
      (tyArgs.extract 0 (min params tyArgs.size)) 0) ?_
  intro ctorApp
  refine bind_preservesInferOnly
    (tryOptional_preservesInferOnly
      (inferOnlyRec_preservesInferOnly hmethods ctorApp)) ?_
  intro ctorTyResult
  cases ctorTyResult with
  | none => exact TcM.PreservesInferOnly.pure none
  | some ctorTy =>
      simp only []
      refine bindTcM_preservesInferOnly
        (TcM.PreservesInferOnly.bumpStats
          (fun state : TcState .anon => { state with
            kSynthAttempts := state.kSynthAttempts + 1 })
          (fun _ => rfl)) ?_
      intro _
      refine bind_preservesInferOnly
        (callIsDefEq_preservesInferOnly hmethods majorTyW ctorTy) ?_
      intro equal
      cases equal with
      | true =>
          simp only [Bool.not_true, pure_bind]
          exact TcM.PreservesInferOnly.pure (some ctorApp)
      | false =>
          simp only [Bool.not_false, if_true]
          refine bindTcM_preservesInferOnly
            (TcM.PreservesInferOnly.bumpStats
              (fun state : TcState .anon => { state with
                kSynthRejects := state.kSynthRejects + 1 })
              (fun _ => rfl)) ?_
          intro _
          exact TcM.PreservesInferOnly.pure none

attribute [local irreducible] verifyKSynthCandidate

theorem selectKSynthCandidate_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (majorTyW : KExpr .anon) (tyHeadId : KId .anon)
    (tyUs : Array (KUniv .anon)) (tyArgs : Array (KExpr .anon))
    (indId : KId .anon) (params : Nat) :
    ((selectKSynthCandidate majorTyW tyHeadId tyUs tyArgs indId params).run
      methods).PreservesInferOnly := by
  unfold selectKSynthCandidate
  by_cases hmismatch : tyHeadId.addr != indId.addr
  · simp only [hmismatch, if_pos]
    exact TcM.PreservesInferOnly.pure none
  · simp only [hmismatch, Bool.false_eq_true, if_false, pure_bind]
    refine bindTcM_preservesInferOnly
      (TcM.PreservesInferOnly.tryGetConst indId) ?_
    intro declaration
    cases declaration with
    | none => exact TcM.PreservesInferOnly.pure none
    | some declaration =>
        cases declaration with
        | indc name levelParams lvls indParams indices isUnsafe block memberIdx
            ty ctors leanAll =>
            simp only []
            cases hctor : ctors[0]? with
            | none =>
                simp only []
                exact TcM.PreservesInferOnly.pure none
            | some ctorId =>
                simp only []
                exact verifyKSynthCandidate_preservesInferOnly hmethods
                  majorTyW ctorId tyUs tyArgs params
        | axio | defn | quot | ctor | recr =>
            simp only []
            exact TcM.PreservesInferOnly.pure none

attribute [local irreducible] selectKSynthCandidate

theorem synthCtorWhenK_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (major : KExpr .anon) (recId : KId .anon) (recr : IotaInfo .anon)
    (recUs : Array (KUniv .anon)) :
    ((synthCtorWhenK major recId recr recUs).run
      methods).PreservesInferOnly := by
  unfold synthCtorWhenK
  by_cases hlevels : recUs.size.toUInt64 != recr.lvls
  · simp only [hlevels, if_pos]
    exact TcM.PreservesInferOnly.pure none
  · simp only [hlevels, Bool.false_eq_true, if_false, pure_bind]
    refine bind_preservesInferOnly
      (tryOptional_preservesInferOnly
        (inferOnlyRec_preservesInferOnly hmethods major)) ?_
    intro majorTyResult
    cases majorTyResult with
    | none => exact TcM.PreservesInferOnly.pure none
    | some majorTy =>
        simp only []
        refine bind_preservesInferOnly
          (tryOptional_preservesInferOnly
            (whnfRec_preservesInferOnly hmethods majorTy)) ?_
        intro majorTyWResult
        cases majorTyWResult with
        | none => exact TcM.PreservesInferOnly.pure none
        | some majorTyW =>
            simp only []
            rcases hspine : majorTyW.collectSpine with ⟨tyHead, tyArgs⟩
            cases tyHead with
            | const tyHeadId tyUs tyInfo =>
                refine bindTcM_preservesInferOnly
                  (TcM.PreservesInferOnly.tryGetConst recId) ?_
                intro declaration
                cases declaration with
                | none => exact TcM.PreservesInferOnly.pure none
                | some declaration =>
                    let recTy := declaration.ty
                    let skip :=
                      (recr.params + recr.motives + recr.minors +
                        recr.indices).toUInt64
                    have hscan :
                        ((do
                          let recTy ← TcM.instantiateUnivParams recTy recUs
                          getMajorInductiveId recTy skip :
                          RecM .anon (KId .anon)).run
                          methods).PreservesInferOnly := by
                      refine bindTcM_preservesInferOnly
                        (TcM.PreservesInferOnly.instantiateUnivParams recTy
                          recUs) ?_
                      intro instantiated
                      exact getMajorInductiveId_preservesInferOnly hmethods
                        instantiated skip
                    refine bind_preservesInferOnly
                      (tryOptional_preservesInferOnly hscan) ?_
                    intro indResult
                    cases indResult with
                    | none => exact TcM.PreservesInferOnly.pure none
                    | some indId =>
                        exact selectKSynthCandidate_preservesInferOnly hmethods
                          majorTyW tyHeadId tyUs tyArgs indId recr.params
            | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
                exact TcM.PreservesInferOnly.pure none

end RecM
end Ix.Tc
