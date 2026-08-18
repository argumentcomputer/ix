import Ix.Tc.Verify.Whnf.Iota.StringLiteral

/-!
# Successful K-like constructor synthesis

ConstructorDispatch--StringLiteral cover iota once the major reaches ordinary constructor dispatch,
but their outer prefixes deliberately assume `recr.k = false`.  This slice
opens the positive K branch.  It records every fallible production action in
`synthCtorWhenK`, including the caught inference/WHNF/type-scan stages, the
constructor rebuild, statistics boundary, and final def-equality gate, then
lifts a successful synthesis through the actual iota prefix.

The trace is execution-indexed.  It does not infer success merely from the K
flag: malformed or untrusted catalog entries may legitimately make any of the
caught stages return `none`, and callback errors may retain partial state.
-/

namespace Ix.Tc

open Lean4Lean (VDefEq VExpr)

namespace RecM

/-- A successful optional probe preserves its exact value and post-state. -/
theorem tryOptional_success
    {methods : Methods .anon} {x : RecM .anon α}
    {s sf : TcState .anon} {a : α}
    (h : x.run methods s = .ok a sf) :
    (tryOptional x).run methods s = .ok (some a) sf := by
  unfold tryOptional try?
  change EStateM.tryCatch
    (EStateM.bind (x.run methods) (fun a s => .ok (some a) s)) _ s = _
  unfold EStateM.bind EStateM.tryCatch
  simp only [h]

/-- A caught optional-probe error becomes absence while retaining the
error-side state, as required by the Rust `&mut` execution model. -/
theorem tryOptional_error
    {methods : Methods .anon} {x : RecM .anon α}
    {s sf : TcState .anon} {err : TcError .anon}
    (h : x.run methods s = .error err sf) :
    (tryOptional x).run methods s = .ok none sf := by
  unfold tryOptional try?
  change EStateM.tryCatch
    (EStateM.bind (x.run methods) (fun a s => .ok (some a) s)) _ s = _
  unfold EStateM.bind EStateM.tryCatch
  simp only [h]
  rfl

/-- Exact successful execution of the candidate-build transaction after
catalog selection has identified the first constructor. -/
structure VerifyKSynthCandidateSuccessTrace
    (methods : Methods .anon) (majorTyW : KExpr .anon)
    (ctorId : KId .anon) (tyUs : Array (KUniv .anon))
    (tyArgs : Array (KExpr .anon)) (params : Nat)
    (s : TcState .anon) (ctorApp : KExpr .anon) (sf : TcState .anon) : Type where
  ctorHead : KExpr .anon
  ctorTy : KExpr .anon
  sCtorHead : TcState .anon
  sCtorApp : TcState .anon
  sCtorTy : TcState .anon
  sAttempt : TcState .anon
  ctorHeadIntern :
    TcM.intern (KExpr.mkConst ctorId tyUs) s = .ok ctorHead sCtorHead
  ctorApps :
    (finishAppResult ctorHead
      (tyArgs.extract 0 (min params tyArgs.size)) 0).run methods sCtorHead =
        .ok ctorApp sCtorApp
  ctorInfer :
    (tryOptional (inferOnlyRec ctorApp)).run methods sCtorApp =
      .ok (some ctorTy) sCtorTy
  attemptStats :
    TcM.bumpStats
      (fun st => { st with kSynthAttempts := st.kSynthAttempts + 1 })
      sCtorTy = .ok () sAttempt
  typeDefEq :
    (callIsDefEq majorTyW ctorTy).run methods sAttempt = .ok true sf

namespace VerifyKSynthCandidateSuccessTrace

theorem eval
    (h : VerifyKSynthCandidateSuccessTrace methods majorTyW ctorId tyUs
      tyArgs params s ctorApp sf) :
    (verifyKSynthCandidate majorTyW ctorId tyUs tyArgs params).run methods s =
      .ok (some ctorApp) sf := by
  unfold verifyKSynthCandidate
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.intern (KExpr.mkConst ctorId tyUs)) _ s = _
  unfold EStateM.bind
  rw [h.ctorHeadIntern]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run
      (finishAppResult h.ctorHead
        (tyArgs.extract 0 (min params tyArgs.size)) 0) methods) _
      h.sCtorHead = _
  unfold EStateM.bind
  rw [h.ctorApps]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryOptional (inferOnlyRec ctorApp)) methods) _ h.sCtorApp = _
  unfold EStateM.bind
  rw [h.ctorInfer]
  simp only
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind
    (TcM.bumpStats
      (fun st => { st with kSynthAttempts := st.kSynthAttempts + 1 })) _
      h.sCtorTy = _
  unfold EStateM.bind
  rw [h.attemptStats]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (callIsDefEq majorTyW h.ctorTy) methods) _ h.sAttempt = _
  unfold EStateM.bind
  rw [h.typeDefEq]
  rfl

end VerifyKSynthCandidateSuccessTrace

/-- The final DefEq rejection is a successful `none`, not an exception, and
the rejection counter is sequenced after the attempt counter. -/
structure VerifyKSynthCandidateRejectTrace
    (methods : Methods .anon) (majorTyW : KExpr .anon)
    (ctorId : KId .anon) (tyUs : Array (KUniv .anon))
    (tyArgs : Array (KExpr .anon)) (params : Nat)
    (s sf : TcState .anon) : Type where
  ctorHead : KExpr .anon
  ctorApp : KExpr .anon
  ctorTy : KExpr .anon
  sCtorHead : TcState .anon
  sCtorApp : TcState .anon
  sCtorTy : TcState .anon
  sAttempt : TcState .anon
  sDefEq : TcState .anon
  ctorHeadIntern :
    TcM.intern (KExpr.mkConst ctorId tyUs) s = .ok ctorHead sCtorHead
  ctorApps :
    (finishAppResult ctorHead
      (tyArgs.extract 0 (min params tyArgs.size)) 0).run methods sCtorHead =
        .ok ctorApp sCtorApp
  ctorInfer :
    (tryOptional (inferOnlyRec ctorApp)).run methods sCtorApp =
      .ok (some ctorTy) sCtorTy
  attemptStats :
    TcM.bumpStats
      (fun st => { st with kSynthAttempts := st.kSynthAttempts + 1 })
      sCtorTy = .ok () sAttempt
  typeDefEq :
    (callIsDefEq majorTyW ctorTy).run methods sAttempt = .ok false sDefEq
  rejectStats :
    TcM.bumpStats
      (fun st => { st with kSynthRejects := st.kSynthRejects + 1 })
      sDefEq = .ok () sf

namespace VerifyKSynthCandidateRejectTrace

theorem eval
    (h : VerifyKSynthCandidateRejectTrace methods majorTyW ctorId tyUs
      tyArgs params s sf) :
    (verifyKSynthCandidate majorTyW ctorId tyUs tyArgs params).run methods s =
      .ok none sf := by
  unfold verifyKSynthCandidate
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.intern (KExpr.mkConst ctorId tyUs)) _ s = _
  unfold EStateM.bind
  rw [h.ctorHeadIntern]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run
      (finishAppResult h.ctorHead
        (tyArgs.extract 0 (min params tyArgs.size)) 0) methods) _
      h.sCtorHead = _
  unfold EStateM.bind
  rw [h.ctorApps]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryOptional (inferOnlyRec h.ctorApp)) methods) _
      h.sCtorApp = _
  unfold EStateM.bind
  rw [h.ctorInfer]
  simp only
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind
    (TcM.bumpStats
      (fun st => { st with kSynthAttempts := st.kSynthAttempts + 1 })) _
      h.sCtorTy = _
  unfold EStateM.bind
  rw [h.attemptStats]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (callIsDefEq majorTyW h.ctorTy) methods) _ h.sAttempt = _
  unfold EStateM.bind
  rw [h.typeDefEq]
  simp only [Bool.not_false, if_true]
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind
    (TcM.bumpStats
      (fun st => { st with kSynthRejects := st.kSynthRejects + 1 })) _
      h.sDefEq = _
  unfold EStateM.bind
  rw [h.rejectStats]
  rfl

end VerifyKSynthCandidateRejectTrace

/-- Exact successful execution of `synthCtorWhenK`.  Keeping the states
between callbacks explicit prevents swallowed errors or diagnostic-state
changes from being mistaken for pure lookups. -/
structure SynthCtorWhenKSuccessTrace
    (methods : Methods .anon) (major : KExpr .anon) (recId : KId .anon)
    (recr : IotaInfo .anon) (recUs : Array (KUniv .anon))
    (s : TcState .anon)
    (ctorApp : KExpr .anon) (sf : TcState .anon) : Type where
  majorTy : KExpr .anon
  majorTyW : KExpr .anon
  tyHeadId : KId .anon
  tyUs : Array (KUniv .anon)
  tyHeadInfo : ExprInfo .anon
  tyArgs : Array (KExpr .anon)
  recursor : KConst .anon
  recursorTy : KExpr .anon
  indId : KId .anon
  ctorId : KId .anon
  indLvls : UInt64
  indParams : UInt64
  indIndices : UInt64
  indUnsafe : Bool
  indBlock : KId .anon
  indMemberIdx : UInt64
  indTy : KExpr .anon
  ctors : Array (KId .anon)
  sMajorTy : TcState .anon
  sMajorTyW : TcState .anon
  sRecursor : TcState .anon
  sInductive : TcState .anon
  sIndLookup : TcState .anon
  levelArity : recUs.size.toUInt64 = recr.lvls
  majorInfer :
    (tryOptional (inferOnlyRec major)).run methods s =
      .ok (some majorTy) sMajorTy
  majorWhnf :
    (tryOptional (whnfRec majorTy)).run methods sMajorTy =
      .ok (some majorTyW) sMajorTyW
  majorSpine :
    majorTyW.collectSpine = (.const tyHeadId tyUs tyHeadInfo, tyArgs)
  recursorLookup :
    TcM.tryGetConst recId sMajorTyW = .ok (some recursor) sRecursor
  recursorType : recursor.ty = recursorTy
  majorInductive :
    (tryOptional (do
      let recursorTy ← liftM (TcM.instantiateUnivParams recursorTy recUs)
      getMajorInductiveId recursorTy
        (recr.params + recr.motives + recr.minors +
          recr.indices).toUInt64)).run methods sRecursor =
        .ok (some indId) sInductive
  sameInductive : tyHeadId.addr = indId.addr
  inductiveLookup :
    TcM.tryGetConst indId sInductive =
      .ok (some (.indc () () indLvls indParams indIndices indUnsafe
        indBlock indMemberIdx indTy ctors ())) sIndLookup
  firstCtor : ctors[0]? = some ctorId
  candidate :
    (verifyKSynthCandidate majorTyW ctorId tyUs tyArgs recr.params).run
      methods sIndLookup = .ok (some ctorApp) sf

namespace SynthCtorWhenKSuccessTrace

/-- A successful trace evaluates the production helper exactly. -/
theorem eval
    (h : SynthCtorWhenKSuccessTrace methods major recId recr recUs s ctorApp
      sf) :
    (synthCtorWhenK major recId recr recUs).run methods s =
      .ok (some ctorApp) sf := by
  unfold synthCtorWhenK
  have hlevels : (recUs.size.toUInt64 != recr.lvls) = false := by
    simp [h.levelArity]
  rw [hlevels]
  simp only [Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryOptional (inferOnlyRec major)) methods) _ s = _
  unfold EStateM.bind
  rw [h.majorInfer]
  simp only
  change EStateM.bind
    (ReaderT.run (tryOptional (whnfRec h.majorTy)) methods) _ h.sMajorTy = _
  unfold EStateM.bind
  rw [h.majorWhnf]
  simp only
  rw [h.majorSpine]
  simp only
  change EStateM.bind (TcM.tryGetConst recId) _ h.sMajorTyW = _
  unfold EStateM.bind
  rw [h.recursorLookup]
  simp only
  rw [h.recursorType]
  simp only [pure_bind]
  change EStateM.bind
    (ReaderT.run
      (tryOptional (do
        let recursorTy ←
          liftM (TcM.instantiateUnivParams h.recursorTy recUs)
        getMajorInductiveId recursorTy
          (recr.params + recr.motives + recr.minors +
            recr.indices).toUInt64))
      methods) _ h.sRecursor = _
  unfold EStateM.bind
  rw [h.majorInductive]
  simp only
  unfold selectKSynthCandidate
  rw [h.sameInductive]
  have haddrNe : (h.indId.addr != h.indId.addr) = false := by simp
  rw [haddrNe]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  change EStateM.bind (TcM.tryGetConst h.indId) _ h.sInductive = _
  unfold EStateM.bind
  rw [h.inductiveLookup]
  simp only [h.firstCtor]
  exact h.candidate

end SynthCtorWhenKSuccessTrace

/-- Exact K-enabled prefix through synthesis (successful or fallback), initial
cleanup, the policy-selected major callback, and post-WHNF processing.  The
explicit `selected` equation makes `.getD major` observable when synthesis
returns `none`. -/
theorem tryIotaWithFlags_kPrefix
    {methods : Methods .anon} {source : KExpr .anon} {flags : WhnfFlags}
    {s sLookup sSynth sCleanup sWhnf sf : TcState .anon}
    {recId : KId .anon} {recUs : Array (KUniv .anon)}
    {headInfo : ExprInfo .anon} {spine : Array (KExpr .anon)}
    {recursor : KConst .anon} {recr : IotaInfo .anon}
    {major selected majorWhnf result : KExpr .anon}
    {synthResult : Option (KExpr .anon)}
    (hsource : source.collectSpine = (.const recId recUs headInfo, spine))
    (hlookup : TcM.tryGetConst recId s = .ok (some recursor) sLookup)
    (hinfo : recursor.iotaInfo? = some recr)
    (hmajorBound : recr.majorIdx < spine.size)
    (hmajor : spine[recr.majorIdx]! = major)
    (hk : recr.k = true)
    (hsynth : (synthCtorWhenK major recId recr recUs).run methods sLookup =
      .ok synthResult sSynth)
    (hselected : synthResult.getD major = selected)
    (hcleanup : (cleanupNatOffsetMajor selected).run methods sSynth =
      .ok none sCleanup)
    (hwhnf :
      (if flags.cheapRec then
          (whnfCoreFlagsRec selected flags).run methods sCleanup
        else (whnfRec selected).run methods sCleanup) =
        .ok majorWhnf sWhnf)
    (hafter :
      (tryIotaAfterMajorWhnf flags recId recr recUs spine majorWhnf).run
        methods sWhnf = .ok (some result) sf) :
    (tryIotaWithFlags source flags).run methods s = .ok (some result) sf := by
  unfold tryIotaWithFlags
  rw [hsource, ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.tryGetConst recId) _ s = _
  unfold EStateM.bind
  rw [hlookup]
  simp only
  rw [hinfo]
  simp only
  rw [if_neg (Nat.not_le.mpr hmajorBound)]
  rw [hmajor, hk]
  simp only [↓reduceIte]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (synthCtorWhenK major recId recr recUs) methods) _ sLookup = _
  unfold EStateM.bind
  rw [hsynth]
  simp only
  rw [hselected]
  simp only [pure_bind]
  change EStateM.bind
    (ReaderT.run (cleanupNatOffsetMajor selected) methods) _ sSynth = _
  unfold EStateM.bind
  rw [hcleanup]
  simp only [Option.getD]
  cases hcheap : flags.cheapRec
  · simp only [hcheap, Bool.false_eq_true, ↓reduceIte] at hwhnf ⊢
    change EStateM.bind _ _ sCleanup = _
    unfold EStateM.bind
    change whnfRec selected methods sCleanup = .ok majorWhnf sWhnf at hwhnf
    rw [hwhnf]
    exact hafter
  · simp only [hcheap, ↓reduceIte] at hwhnf ⊢
    change EStateM.bind _ _ sCleanup = _
    unfold EStateM.bind
    change whnfCoreFlagsRec selected flags methods sCleanup =
      .ok majorWhnf sWhnf at hwhnf
    rw [hwhnf]
    exact hafter

/-- A caught K-synthesis miss keeps the original major and continues through
the same cleanup/WHNF/postprocessing path.  Partial state retained by the
caught probe is represented by `sSynth`. -/
theorem tryIotaWithFlags_kFallback
    {methods : Methods .anon} {source : KExpr .anon} {flags : WhnfFlags}
    {s sLookup sSynth sCleanup sWhnf sf : TcState .anon}
    {recId : KId .anon} {recUs : Array (KUniv .anon)}
    {headInfo : ExprInfo .anon} {spine : Array (KExpr .anon)}
    {recursor : KConst .anon} {recr : IotaInfo .anon}
    {major majorWhnf result : KExpr .anon}
    (hsource : source.collectSpine = (.const recId recUs headInfo, spine))
    (hlookup : TcM.tryGetConst recId s = .ok (some recursor) sLookup)
    (hinfo : recursor.iotaInfo? = some recr)
    (hmajorBound : recr.majorIdx < spine.size)
    (hmajor : spine[recr.majorIdx]! = major)
    (hk : recr.k = true)
    (hsynth : (synthCtorWhenK major recId recr recUs).run methods sLookup =
      .ok none sSynth)
    (hcleanup : (cleanupNatOffsetMajor major).run methods sSynth =
      .ok none sCleanup)
    (hwhnf :
      (if flags.cheapRec then
          (whnfCoreFlagsRec major flags).run methods sCleanup
        else (whnfRec major).run methods sCleanup) =
        .ok majorWhnf sWhnf)
    (hafter :
      (tryIotaAfterMajorWhnf flags recId recr recUs spine majorWhnf).run
        methods sWhnf = .ok (some result) sf) :
    (tryIotaWithFlags source flags).run methods s = .ok (some result) sf :=
  tryIotaWithFlags_kPrefix hsource hlookup hinfo hmajorBound hmajor hk
    hsynth rfl hcleanup hwhnf hafter

/-- Complete successful K-synthesis branch ending in ordinary constructor
dispatch. -/
theorem tryIotaWithFlags_kCtor
    {methods : Methods .anon} {source : KExpr .anon} {flags : WhnfFlags}
    {s sLookup sSynth sCleanup sWhnf sCleanupWhnf sCtor sf : TcState .anon}
    {recId : KId .anon} {recUs : Array (KUniv .anon)}
    {headInfo : ExprInfo .anon} {spine : Array (KExpr .anon)}
    {recursor : KConst .anon} {recr : IotaInfo .anon}
    {major synthesized majorWhnf : KExpr .anon}
    {ctorId : KId .anon} {ctorUs : Array (KUniv .anon)}
    {ctorHeadInfo : ExprInfo .anon} {ctorArgs : Array (KExpr .anon)}
    {ctor : KConst .anon} {cidx ctorFields : Nat}
    {result : KExpr .anon}
    (hsource : source.collectSpine = (.const recId recUs headInfo, spine))
    (hlookup : TcM.tryGetConst recId s = .ok (some recursor) sLookup)
    (hinfo : recursor.iotaInfo? = some recr)
    (hmajorBound : recr.majorIdx < spine.size)
    (hmajor : spine[recr.majorIdx]! = major)
    (hk : recr.k = true)
    (hsynth : (synthCtorWhenK major recId recr recUs).run methods sLookup =
      .ok (some synthesized) sSynth)
    (hcleanup : (cleanupNatOffsetMajor synthesized).run methods sSynth =
      .ok none sCleanup)
    (hwhnf :
      (if flags.cheapRec then
          (whnfCoreFlagsRec synthesized flags).run methods sCleanup
        else (whnfRec synthesized).run methods sCleanup) =
        .ok majorWhnf sWhnf)
    (hmajorShape : IotaCtorMajor majorWhnf)
    (hcleanupWhnf : (cleanupNatOffsetMajor majorWhnf).run methods sWhnf =
      .ok none sCleanupWhnf)
    (hctorSpine : majorWhnf.collectSpine =
      (.const ctorId ctorUs ctorHeadInfo, ctorArgs))
    (hctorLookup : TcM.tryGetConst ctorId sCleanupWhnf =
      .ok (some ctor) sCtor)
    (hctorInfo : ctor.iotaCtorInfo? = some (cidx, ctorFields))
    (hdispatch :
      (tryApplyIotaCtor recr recUs spine ctorArgs cidx ctorFields false).run
        methods sCtor = .ok (some result) sf) :
    (tryIotaWithFlags source flags).run methods s = .ok (some result) sf := by
  have hctor := tryIotaCtorOrStructEta_regular (recId := recId)
    hctorSpine hctorLookup hctorInfo hdispatch
  have hafter := tryIotaAfterMajorWhnf_regular (flags := flags)
    hmajorShape hcleanupWhnf hctor
  exact tryIotaWithFlags_kPrefix hsource hlookup hinfo hmajorBound hmajor hk
    hsynth rfl hcleanup hwhnf hafter

/-- Headline ConstructorSynthesis contract: successful K synthesis enters the same checked
ordinary-constructor rule semantics as a syntactic constructor major.  The
mutable callback prefix exposes its invariant and intern-only frame, exactly
as in ConstructorDispatch's non-K branch. -/
theorem tryIotaWithFlags_kCtor_checkedAcceptance_empty
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {methods : Methods .anon} {source : KExpr .anon} {flags : WhnfFlags}
    {s sLookup sSynth sCleanup sWhnf sCleanupWhnf sCtor sf : TcState .anon}
    {recId : KId .anon} {recUs : Array (KUniv .anon)}
    {headInfo : ExprInfo .anon} {spine : Array (KExpr .anon)}
    {recursor : KConst .anon} {recr : IotaInfo .anon}
    {major synthesized majorWhnf : KExpr .anon}
    {ctorId : KId .anon} {ctorUs : Array (KUniv .anon)}
    {ctorHeadInfo : ExprInfo .anon} {ctorArgs : Array (KExpr .anon)}
    {ctor : KConst .anon} {cidx ctorFields : Nat}
    {rule : RecRule .anon} {defeq : VDefEq} {startV : VExpr}
    {final : KExpr .anon} {finalV : VExpr}
    (h : ApplyIotaCtorTrace layer semantics trProj world support 0 []
      methods recr recUs spine ctorArgs cidx ctorFields false rule startV
      sCtor final finalV sf)
    (hcollect : source.collectSpine = (.const recId recUs headInfo, spine))
    (hlookup : TcM.tryGetConst recId s = .ok (some recursor) sLookup)
    (hinfo : recursor.iotaInfo? = some recr)
    (hmajorBound : recr.majorIdx < spine.size)
    (hmajor : spine[recr.majorIdx]! = major)
    (hk : recr.k = true)
    (hsynth : (synthCtorWhenK major recId recr recUs).run methods sLookup =
      .ok (some synthesized) sSynth)
    (hcleanup : (cleanupNatOffsetMajor synthesized).run methods sSynth =
      .ok none sCleanup)
    (hwhnf :
      (if flags.cheapRec then
          (whnfCoreFlagsRec synthesized flags).run methods sCleanup
        else (whnfRec synthesized).run methods sCleanup) =
        .ok majorWhnf sWhnf)
    (hmajorShape : IotaCtorMajor majorWhnf)
    (hcleanupWhnf : (cleanupNatOffsetMajor majorWhnf).run methods sWhnf =
      .ok none sCleanupWhnf)
    (hctorSpine : majorWhnf.collectSpine =
      (.const ctorId ctorUs ctorHeadInfo, ctorArgs))
    (hctorLookup : TcM.tryGetConst ctorId sCleanupWhnf =
      .ok (some ctor) sCtor)
    (hctorInfo : ctor.iotaCtorInfo? = some (cidx, ctorFields))
    (hprefixFrame : InternUpdateFrame s sCtor)
    (hdispatchI : WhnfStateInv layer semantics trProj world support 0 []
      sCtor)
    (hregistered : RegisteredRecursorRuleRhsRel world.venv world.nameOf
      trProj recId recursor rule defeq)
    (theory : WhnfTheory trProj world 0)
    (hempty : recUs.isEmpty = true)
    (harity : defeq.uvars = 0)
    (hruleSupport : support rule.rhs)
    (hstartV : startV = defeq.rhs)
    {pattern : RecursorRulePattern}
    (hpattern : RawRecursorRulePatternRel world.venv world.catalog
      world.nameOf recId recursor rule pattern)
    (hdispatchAligned : IotaCtorDispatchAligned cidx ctorFields pattern)
    {sourceV sourceType : VExpr}
    (hsourceTr : TrKExprS world.venv 0 world.nameOf trProj [] source sourceV)
    (hsourceType : world.venv.HasType 0 [] sourceV sourceType)
    {levels : List Lean4Lean.VLevel}
    {captures : (RecursorIotaPattern pattern.recursorName pattern.majorIdx
      pattern.constructorName
      (pattern.constructorParams.toNat +
        pattern.constructorFields.toNat)).Path → VExpr}
    (hmatch : Lean4Lean.Pattern.Matches
      (RecursorIotaPattern pattern.recursorName pattern.majorIdx
        pattern.constructorName
        (pattern.constructorParams.toNat +
          pattern.constructorFields.toNat))
      sourceV levels captures)
    (hchecks : pattern.checks.OK
      (world.venv.IsDefEqU 0 []) levels captures)
    (hrhsAligned : IotaRhsApplicationAligned pattern levels captures finalV) :
    (tryIotaWithFlags source flags).run methods s = .ok (some final) sf ∧
      WhnfStateInv layer semantics trProj world support 0 [] sf ∧
      InternUpdateFrame s sf ∧
      support final ∧
      WhnfMeaning trProj world 0 [] source final := by
  have hpatternDispatch :
      ApplyIotaCtorTrace layer semantics trProj world support 0 [] methods
        recr recUs spine ctorArgs pattern.ruleIndex
          pattern.constructorFields.toNat false rule startV sCtor final finalV
          sf := by
    simpa only [hdispatchAligned.ruleIndex, hdispatchAligned.fields] using h
  have hchecked := hpatternDispatch.checkedAcceptance_empty hregistered
    theory hempty harity hdispatchI hruleSupport hstartV hpattern hsourceTr
    hsourceType hmatch hchecks hrhsAligned
  obtain ⟨_, hfinalI, hdispatchFrame, hfinalSupport, hmeaning⟩ := hchecked
  have hrun := tryIotaWithFlags_kCtor hcollect hlookup hinfo hmajorBound
    hmajor hk hsynth hcleanup hwhnf hmajorShape hcleanupWhnf hctorSpine
    hctorLookup hctorInfo h.eval
  exact ⟨hrun, hfinalI, hprefixFrame.trans hdispatchFrame,
    hfinalSupport, hmeaning⟩

end RecM

end Ix.Tc
