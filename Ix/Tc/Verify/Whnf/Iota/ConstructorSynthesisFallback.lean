import Ix.Tc.Verify.Whnf.Iota.ConstructorSynthesis

/-!
# Exhaustive K-synthesis fallback branches

ConstructorSynthesis proves successful constructor synthesis and counted DefEq rejection.
This slice closes the complementary control-flow surface: every silent
fallback before candidate verification, the caught candidate-inference
error, and propagation of the final DefEq callback error.  Intermediate
states remain explicit because all three caught probes deliberately retain
their error-side mutations.

The post-scan catalog branches are stated against the named
`selectKSynthCandidate` production seam.  This separates genuinely reachable
malformed-inductive cases (for example an empty constructor array) from the
defensive repeated-lookup cases without assuming catalog immutability.
-/

namespace Ix.Tc

namespace RecM

/-- The structural side condition used by the non-constant type-head exit. -/
def KSynthNonConstHead : KExpr .anon → Prop
  | .const .. => False
  | _ => True

/-- The structural side condition used by the defensive non-inductive
catalog exit. -/
def KSynthNonInductive : KConst .anon → Prop
  | .indc .. => False
  | _ => True

/-- Candidate construction silently rejects a caught inference miss before
either statistics counter or DefEq is touched. -/
theorem verifyKSynthCandidate_inferMiss
    {methods : Methods .anon} {majorTyW : KExpr .anon}
    {ctorId : KId .anon} {tyUs : Array (KUniv .anon)}
    {tyArgs : Array (KExpr .anon)} {params : Nat}
    {s sCtorHead sCtorApp sf : TcState .anon}
    {ctorHead ctorApp : KExpr .anon}
    (hhead : TcM.intern (KExpr.mkConst ctorId tyUs) s =
      .ok ctorHead sCtorHead)
    (happs :
      (finishAppResult ctorHead
        (tyArgs.extract 0 (min params tyArgs.size)) 0).run methods sCtorHead =
          .ok ctorApp sCtorApp)
    (hinfer : (tryOptional (inferOnlyRec ctorApp)).run methods sCtorApp =
      .ok none sf) :
    (verifyKSynthCandidate majorTyW ctorId tyUs tyArgs params).run methods s =
      .ok .inconclusive sf := by
  unfold verifyKSynthCandidate
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.intern (KExpr.mkConst ctorId tyUs)) _ s = _
  unfold EStateM.bind
  rw [hhead]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run
      (finishAppResult ctorHead
        (tyArgs.extract 0 (min params tyArgs.size)) 0) methods) _
      sCtorHead = _
  unfold EStateM.bind
  rw [happs]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryOptional (inferOnlyRec ctorApp)) methods) _ sCtorApp = _
  unfold EStateM.bind
  rw [hinfer]
  rfl

/-- Raw candidate-inference errors are caught as absence while preserving
the exact error-side state. -/
theorem verifyKSynthCandidate_inferError
    {methods : Methods .anon} {majorTyW : KExpr .anon}
    {ctorId : KId .anon} {tyUs : Array (KUniv .anon)}
    {tyArgs : Array (KExpr .anon)} {params : Nat}
    {s sCtorHead sCtorApp sf : TcState .anon}
    {ctorHead ctorApp : KExpr .anon} {err : TcError .anon}
    (hhead : TcM.intern (KExpr.mkConst ctorId tyUs) s =
      .ok ctorHead sCtorHead)
    (happs :
      (finishAppResult ctorHead
        (tyArgs.extract 0 (min params tyArgs.size)) 0).run methods sCtorHead =
          .ok ctorApp sCtorApp)
    (hinfer : (inferOnlyRec ctorApp).run methods sCtorApp = .error err sf) :
    (verifyKSynthCandidate majorTyW ctorId tyUs tyArgs params).run methods s =
      .ok .inconclusive sf :=
  verifyKSynthCandidate_inferMiss hhead happs (tryOptional_error hinfer)

/-- Unlike the three optional probes, the final DefEq callback is not caught:
its error and post-error state propagate exactly. -/
theorem verifyKSynthCandidate_defEqError
    {methods : Methods .anon} {majorTyW : KExpr .anon}
    {ctorId : KId .anon} {tyUs : Array (KUniv .anon)}
    {tyArgs : Array (KExpr .anon)} {params : Nat}
    {s sCtorHead sCtorApp sCtorTy sAttempt sf : TcState .anon}
    {ctorHead ctorApp ctorTy : KExpr .anon} {err : TcError .anon}
    (hhead : TcM.intern (KExpr.mkConst ctorId tyUs) s =
      .ok ctorHead sCtorHead)
    (happs :
      (finishAppResult ctorHead
        (tyArgs.extract 0 (min params tyArgs.size)) 0).run methods sCtorHead =
          .ok ctorApp sCtorApp)
    (hinfer : (tryOptional (inferOnlyRec ctorApp)).run methods sCtorApp =
      .ok (some ctorTy) sCtorTy)
    (hattempt : TcM.bumpStats
      (fun st => { st with kSynthAttempts := st.kSynthAttempts + 1 })
      sCtorTy = .ok () sAttempt)
    (hdefeq : (callIsDefEq majorTyW ctorTy).run methods sAttempt =
      .error err sf) :
    (verifyKSynthCandidate majorTyW ctorId tyUs tyArgs params).run methods s =
      .error err sf := by
  unfold verifyKSynthCandidate
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.intern (KExpr.mkConst ctorId tyUs)) _ s = _
  unfold EStateM.bind
  rw [hhead]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run
      (finishAppResult ctorHead
        (tyArgs.extract 0 (min params tyArgs.size)) 0) methods) _
      sCtorHead = _
  unfold EStateM.bind
  rw [happs]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryOptional (inferOnlyRec ctorApp)) methods) _ sCtorApp = _
  unfold EStateM.bind
  rw [hinfer]
  simp only
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind
    (TcM.bumpStats
      (fun st => { st with kSynthAttempts := st.kSynthAttempts + 1 })) _
      sCtorTy = _
  unfold EStateM.bind
  rw [hattempt]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (callIsDefEq majorTyW ctorTy) methods) _ sAttempt = _
  unfold EStateM.bind
  rw [hdefeq]

/-- The normalized major type names a different inductive. -/
theorem selectKSynthCandidate_mismatch
    {methods : Methods .anon} {majorTyW : KExpr .anon}
    {tyHeadId indId : KId .anon} {tyUs : Array (KUniv .anon)}
    {tyArgs : Array (KExpr .anon)} {params : Nat} {s : TcState .anon}
    (hmismatch : (tyHeadId.addr != indId.addr) = true) :
    (selectKSynthCandidate majorTyW tyHeadId tyUs tyArgs indId params).run
      methods s = .ok .inconclusive s := by
  unfold selectKSynthCandidate
  rw [hmismatch]
  rfl

/-- The repeated defensive inductive lookup is absent. -/
theorem selectKSynthCandidate_missing
    {methods : Methods .anon} {majorTyW : KExpr .anon}
    {tyHeadId indId : KId .anon} {tyUs : Array (KUniv .anon)}
    {tyArgs : Array (KExpr .anon)} {params : Nat} {s sf : TcState .anon}
    (hsame : (tyHeadId.addr != indId.addr) = false)
    (hlookup : TcM.tryGetConst indId s = .ok none sf) :
    (selectKSynthCandidate majorTyW tyHeadId tyUs tyArgs indId params).run
      methods s = .ok .inconclusive sf := by
  unfold selectKSynthCandidate
  rw [hsame]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  change EStateM.bind (TcM.tryGetConst indId) _ s = _
  unfold EStateM.bind
  rw [hlookup]
  rfl

/-- The repeated lookup returns a loaded constant of a non-inductive shape. -/
theorem selectKSynthCandidate_nonInductive
    {methods : Methods .anon} {majorTyW : KExpr .anon}
    {tyHeadId indId : KId .anon} {tyUs : Array (KUniv .anon)}
    {tyArgs : Array (KExpr .anon)} {params : Nat} {s sf : TcState .anon}
    {entry : KConst .anon}
    (hsame : (tyHeadId.addr != indId.addr) = false)
    (hlookup : TcM.tryGetConst indId s = .ok (some entry) sf)
    (hshape : KSynthNonInductive entry) :
    (selectKSynthCandidate majorTyW tyHeadId tyUs tyArgs indId params).run
      methods s = .ok .inconclusive sf := by
  unfold selectKSynthCandidate
  rw [hsame]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  change EStateM.bind (TcM.tryGetConst indId) _ s = _
  unfold EStateM.bind
  rw [hlookup]
  cases entry <;> simp [KSynthNonInductive] at hshape
  all_goals rfl

/-- An inductive with no first constructor is a successful silent miss. -/
theorem selectKSynthCandidate_empty
    {methods : Methods .anon} {majorTyW : KExpr .anon}
    {tyHeadId indId block : KId .anon} {tyUs : Array (KUniv .anon)}
    {tyArgs : Array (KExpr .anon)} {params : Nat} {s sf : TcState .anon}
    {lvls indParams indices : UInt64} {isUnsafe : Bool}
    {memberIdx : UInt64} {indTy : KExpr .anon}
    (hsame : (tyHeadId.addr != indId.addr) = false)
    (hlookup : TcM.tryGetConst indId s =
      .ok (some (.indc () () lvls indParams indices isUnsafe block memberIdx
        indTy #[] ())) sf) :
    (selectKSynthCandidate majorTyW tyHeadId tyUs tyArgs indId params).run
      methods s = .ok .inconclusive sf := by
  unfold selectKSynthCandidate
  rw [hsame]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  change EStateM.bind (TcM.tryGetConst indId) _ s = _
  unfold EStateM.bind
  rw [hlookup]
  rfl

/-- A selected first constructor forwards any successful candidate result. -/
theorem selectKSynthCandidate_selected
    {methods : Methods .anon} {majorTyW : KExpr .anon}
    {tyHeadId indId block ctorId : KId .anon}
    {tyUs : Array (KUniv .anon)} {tyArgs : Array (KExpr .anon)}
    {params : Nat} {s sLookup sf : TcState .anon}
    {lvls indParams indices : UInt64} {isUnsafe : Bool}
    {memberIdx : UInt64} {indTy : KExpr .anon}
    {ctors : Array (KId .anon)} {result : KSynthOutcome .anon}
    (hsame : (tyHeadId.addr != indId.addr) = false)
    (hlookup : TcM.tryGetConst indId s =
      .ok (some (.indc () () lvls indParams indices isUnsafe block memberIdx
        indTy ctors ())) sLookup)
    (hfirst : ctors[0]? = some ctorId)
    (hcandidate :
      (verifyKSynthCandidate majorTyW ctorId tyUs tyArgs params).run methods
        sLookup = .ok result sf) :
    (selectKSynthCandidate majorTyW tyHeadId tyUs tyArgs indId params).run
      methods s = .ok result sf := by
  unfold selectKSynthCandidate
  rw [hsame]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  change EStateM.bind (TcM.tryGetConst indId) _ s = _
  unfold EStateM.bind
  rw [hlookup]
  simp only [hfirst]
  exact hcandidate

/-- A selected candidate's uncaught error propagates through the selector. -/
theorem selectKSynthCandidate_selectedError
    {methods : Methods .anon} {majorTyW : KExpr .anon}
    {tyHeadId indId block ctorId : KId .anon}
    {tyUs : Array (KUniv .anon)} {tyArgs : Array (KExpr .anon)}
    {params : Nat} {s sLookup sf : TcState .anon}
    {lvls indParams indices : UInt64} {isUnsafe : Bool}
    {memberIdx : UInt64} {indTy : KExpr .anon}
    {ctors : Array (KId .anon)} {err : TcError .anon}
    (hsame : (tyHeadId.addr != indId.addr) = false)
    (hlookup : TcM.tryGetConst indId s =
      .ok (some (.indc () () lvls indParams indices isUnsafe block memberIdx
        indTy ctors ())) sLookup)
    (hfirst : ctors[0]? = some ctorId)
    (hcandidate :
      (verifyKSynthCandidate majorTyW ctorId tyUs tyArgs params).run methods
        sLookup = .error err sf) :
    (selectKSynthCandidate majorTyW tyHeadId tyUs tyArgs indId params).run
      methods s = .error err sf := by
  unfold selectKSynthCandidate
  rw [hsame]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  change EStateM.bind (TcM.tryGetConst indId) _ s = _
  unfold EStateM.bind
  rw [hlookup]
  simp only [hfirst]
  exact hcandidate

/-- The first caught probe can fail before any other K-synthesis action. -/
theorem synthCtorWhenK_levelMismatch
    {methods : Methods .anon} {major : KExpr .anon} {recId : KId .anon}
    {recr : IotaInfo .anon} {recUs : Array (KUniv .anon)}
    {s : TcState .anon}
    (hlevels : (recUs.size.toUInt64 != recr.lvls) = true) :
    (synthCtorWhenK major recId recr recUs).run methods s =
      .ok .inconclusive s := by
  unfold synthCtorWhenK
  rw [hlevels]
  rfl

/-- Once universe arity is valid, the first caught probe can fail before any
other K-synthesis action. -/
theorem synthCtorWhenK_majorInferMiss
    {methods : Methods .anon} {major : KExpr .anon} {recId : KId .anon}
    {recr : IotaInfo .anon} {recUs : Array (KUniv .anon)}
    {s sf : TcState .anon}
    (hlevels : recUs.size.toUInt64 = recr.lvls)
    (hinfer : (tryOptional (inferOnlyRec major)).run methods s = .ok none sf) :
    (synthCtorWhenK major recId recr recUs).run methods s =
      .ok .inconclusive sf := by
  unfold synthCtorWhenK
  have hlevelsNe : (recUs.size.toUInt64 != recr.lvls) = false := by
    simp [hlevels]
  rw [hlevelsNe]
  simp only [Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryOptional (inferOnlyRec major)) methods) _ s = _
  unfold EStateM.bind
  rw [hinfer]
  rfl

theorem synthCtorWhenK_majorInferError
    {methods : Methods .anon} {major : KExpr .anon} {recId : KId .anon}
    {recr : IotaInfo .anon} {recUs : Array (KUniv .anon)}
    {s sf : TcState .anon} {err : TcError .anon}
    (hlevels : recUs.size.toUInt64 = recr.lvls)
    (hinfer : (inferOnlyRec major).run methods s = .error err sf) :
    (synthCtorWhenK major recId recr recUs).run methods s =
      .ok .inconclusive sf :=
  synthCtorWhenK_majorInferMiss hlevels (tryOptional_error hinfer)

/-- Major-type WHNF failure is caught after retaining the inference state. -/
theorem synthCtorWhenK_majorWhnfMiss
    {methods : Methods .anon} {major majorTy : KExpr .anon}
    {recId : KId .anon} {recr : IotaInfo .anon}
    {recUs : Array (KUniv .anon)}
    {s sInfer sf : TcState .anon}
    (hlevels : recUs.size.toUInt64 = recr.lvls)
    (hinfer : (tryOptional (inferOnlyRec major)).run methods s =
      .ok (some majorTy) sInfer)
    (hwhnf : (tryOptional (whnfRec majorTy)).run methods sInfer =
      .ok none sf) :
    (synthCtorWhenK major recId recr recUs).run methods s =
      .ok .inconclusive sf := by
  unfold synthCtorWhenK
  have hlevelsNe : (recUs.size.toUInt64 != recr.lvls) = false := by
    simp [hlevels]
  rw [hlevelsNe]
  simp only [Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryOptional (inferOnlyRec major)) methods) _ s = _
  unfold EStateM.bind
  rw [hinfer]
  simp only
  change EStateM.bind
    (ReaderT.run (tryOptional (whnfRec majorTy)) methods) _ sInfer = _
  unfold EStateM.bind
  rw [hwhnf]
  rfl

theorem synthCtorWhenK_majorWhnfError
    {methods : Methods .anon} {major majorTy : KExpr .anon}
    {recId : KId .anon} {recr : IotaInfo .anon}
    {recUs : Array (KUniv .anon)}
    {s sInfer sf : TcState .anon} {err : TcError .anon}
    (hlevels : recUs.size.toUInt64 = recr.lvls)
    (hinfer : (tryOptional (inferOnlyRec major)).run methods s =
      .ok (some majorTy) sInfer)
    (hwhnf : (whnfRec majorTy).run methods sInfer = .error err sf) :
    (synthCtorWhenK major recId recr recUs).run methods s =
      .ok .inconclusive sf :=
  synthCtorWhenK_majorWhnfMiss hlevels hinfer (tryOptional_error hwhnf)

/-- A normalized major type whose spine head is not a constant stops before
the recursor catalog is consulted. -/
theorem synthCtorWhenK_nonConstHead
    {methods : Methods .anon} {major majorTy majorTyW tyHead : KExpr .anon}
    {tyArgs : Array (KExpr .anon)} {recId : KId .anon}
    {recr : IotaInfo .anon} {recUs : Array (KUniv .anon)}
    {s sInfer sf : TcState .anon}
    (hlevels : recUs.size.toUInt64 = recr.lvls)
    (hinfer : (tryOptional (inferOnlyRec major)).run methods s =
      .ok (some majorTy) sInfer)
    (hwhnf : (tryOptional (whnfRec majorTy)).run methods sInfer =
      .ok (some majorTyW) sf)
    (hspine : majorTyW.collectSpine = (tyHead, tyArgs))
    (hshape : KSynthNonConstHead tyHead) :
    (synthCtorWhenK major recId recr recUs).run methods s =
      .ok .inconclusive sf := by
  unfold synthCtorWhenK
  have hlevelsNe : (recUs.size.toUInt64 != recr.lvls) = false := by
    simp [hlevels]
  rw [hlevelsNe]
  simp only [Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryOptional (inferOnlyRec major)) methods) _ s = _
  unfold EStateM.bind
  rw [hinfer]
  simp only
  change EStateM.bind
    (ReaderT.run (tryOptional (whnfRec majorTy)) methods) _ sInfer = _
  unfold EStateM.bind
  rw [hwhnf]
  simp only
  rw [hspine]
  cases tyHead <;> simp [KSynthNonConstHead] at hshape ⊢ <;> rfl

/-- A constant-headed major type with an absent recursor catalog entry. -/
theorem synthCtorWhenK_recursorMissing
    {methods : Methods .anon} {major majorTy majorTyW : KExpr .anon}
    {tyHeadId recId : KId .anon} {tyUs : Array (KUniv .anon)}
    {tyHeadInfo : ExprInfo .anon} {tyArgs : Array (KExpr .anon)}
    {recr : IotaInfo .anon} {recUs : Array (KUniv .anon)}
    {s sInfer sWhnf sf : TcState .anon}
    (hlevels : recUs.size.toUInt64 = recr.lvls)
    (hinfer : (tryOptional (inferOnlyRec major)).run methods s =
      .ok (some majorTy) sInfer)
    (hwhnf : (tryOptional (whnfRec majorTy)).run methods sInfer =
      .ok (some majorTyW) sWhnf)
    (hspine : majorTyW.collectSpine =
      (.const tyHeadId tyUs tyHeadInfo, tyArgs))
    (hlookup : TcM.tryGetConst recId sWhnf = .ok none sf) :
    (synthCtorWhenK major recId recr recUs).run methods s =
      .ok .inconclusive sf := by
  unfold synthCtorWhenK
  have hlevelsNe : (recUs.size.toUInt64 != recr.lvls) = false := by
    simp [hlevels]
  rw [hlevelsNe]
  simp only [Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryOptional (inferOnlyRec major)) methods) _ s = _
  unfold EStateM.bind
  rw [hinfer]
  simp only
  change EStateM.bind
    (ReaderT.run (tryOptional (whnfRec majorTy)) methods) _ sInfer = _
  unfold EStateM.bind
  rw [hwhnf]
  simp only
  rw [hspine]
  simp only
  change EStateM.bind (TcM.tryGetConst recId) _ sWhnf = _
  unfold EStateM.bind
  rw [hlookup]
  rfl

/-- A failed bounded major-inductive scan is caught after recursor lookup. -/
theorem synthCtorWhenK_majorInductiveMiss
    {methods : Methods .anon} {major majorTy majorTyW recTy : KExpr .anon}
    {tyHeadId recId : KId .anon} {tyUs : Array (KUniv .anon)}
    {tyHeadInfo : ExprInfo .anon} {tyArgs : Array (KExpr .anon)}
    {recursor : KConst .anon} {recr : IotaInfo .anon}
    {recUs : Array (KUniv .anon)}
    {s sInfer sWhnf sRec sf : TcState .anon}
    (hlevels : recUs.size.toUInt64 = recr.lvls)
    (hinfer : (tryOptional (inferOnlyRec major)).run methods s =
      .ok (some majorTy) sInfer)
    (hwhnf : (tryOptional (whnfRec majorTy)).run methods sInfer =
      .ok (some majorTyW) sWhnf)
    (hspine : majorTyW.collectSpine =
      (.const tyHeadId tyUs tyHeadInfo, tyArgs))
    (hlookup : TcM.tryGetConst recId sWhnf = .ok (some recursor) sRec)
    (hrecTy : recursor.ty = recTy)
    (hscan :
      (tryOptional (do
        let recTy ← liftM (TcM.instantiateUnivParams recTy recUs)
        getMajorInductiveId recTy
          (recr.params + recr.motives + recr.minors +
            recr.indices).toUInt64)).run methods sRec = .ok none sf) :
    (synthCtorWhenK major recId recr recUs).run methods s =
      .ok .inconclusive sf := by
  unfold synthCtorWhenK
  have hlevelsNe : (recUs.size.toUInt64 != recr.lvls) = false := by
    simp [hlevels]
  rw [hlevelsNe]
  simp only [Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryOptional (inferOnlyRec major)) methods) _ s = _
  unfold EStateM.bind
  rw [hinfer]
  simp only
  change EStateM.bind
    (ReaderT.run (tryOptional (whnfRec majorTy)) methods) _ sInfer = _
  unfold EStateM.bind
  rw [hwhnf]
  simp only
  rw [hspine]
  simp only
  change EStateM.bind (TcM.tryGetConst recId) _ sWhnf = _
  unfold EStateM.bind
  rw [hlookup]
  simp only
  rw [hrecTy]
  simp only [pure_bind]
  change EStateM.bind
    (ReaderT.run
      (tryOptional (do
        let recTy ← liftM (TcM.instantiateUnivParams recTy recUs)
        getMajorInductiveId recTy
          (recr.params + recr.motives + recr.minors +
            recr.indices).toUInt64))
      methods) _ sRec = _
  unfold EStateM.bind
  rw [hscan]
  rfl

theorem synthCtorWhenK_majorInductiveError
    {methods : Methods .anon} {major majorTy majorTyW recTy : KExpr .anon}
    {tyHeadId recId : KId .anon} {tyUs : Array (KUniv .anon)}
    {tyHeadInfo : ExprInfo .anon} {tyArgs : Array (KExpr .anon)}
    {recursor : KConst .anon} {recr : IotaInfo .anon}
    {recUs : Array (KUniv .anon)}
    {s sInfer sWhnf sRec sf : TcState .anon} {err : TcError .anon}
    (hlevels : recUs.size.toUInt64 = recr.lvls)
    (hinfer : (tryOptional (inferOnlyRec major)).run methods s =
      .ok (some majorTy) sInfer)
    (hwhnf : (tryOptional (whnfRec majorTy)).run methods sInfer =
      .ok (some majorTyW) sWhnf)
    (hspine : majorTyW.collectSpine =
      (.const tyHeadId tyUs tyHeadInfo, tyArgs))
    (hlookup : TcM.tryGetConst recId sWhnf = .ok (some recursor) sRec)
    (hrecTy : recursor.ty = recTy)
    (hscan :
      (do
        let recTy ← liftM (TcM.instantiateUnivParams recTy recUs)
        getMajorInductiveId recTy
          (recr.params + recr.motives + recr.minors +
            recr.indices).toUInt64).run methods sRec = .error err sf) :
    (synthCtorWhenK major recId recr recUs).run methods s =
      .ok .inconclusive sf :=
  synthCtorWhenK_majorInductiveMiss hlevels hinfer hwhnf hspine hlookup hrecTy
    (tryOptional_error hscan)

/-- Exact successful prefix through the bounded recursor scan.  The selector
result remains abstract so each post-scan branch can be lifted without
replaying the prefix proof. -/
structure SynthCtorWhenKSelectionTrace
    (methods : Methods .anon) (major : KExpr .anon) (recId : KId .anon)
    (recr : IotaInfo .anon) (recUs : Array (KUniv .anon))
    (s : TcState .anon) : Type where
  majorTy : KExpr .anon
  majorTyW : KExpr .anon
  tyHeadId : KId .anon
  tyUs : Array (KUniv .anon)
  tyHeadInfo : ExprInfo .anon
  tyArgs : Array (KExpr .anon)
  recursor : KConst .anon
  recTy : KExpr .anon
  indId : KId .anon
  sInfer : TcState .anon
  sWhnf : TcState .anon
  sRec : TcState .anon
  sScan : TcState .anon
  levelArity : recUs.size.toUInt64 = recr.lvls
  majorInfer : (tryOptional (inferOnlyRec major)).run methods s =
    .ok (some majorTy) sInfer
  majorWhnf : (tryOptional (whnfRec majorTy)).run methods sInfer =
    .ok (some majorTyW) sWhnf
  majorSpine : majorTyW.collectSpine =
    (.const tyHeadId tyUs tyHeadInfo, tyArgs)
  recursorLookup : TcM.tryGetConst recId sWhnf = .ok (some recursor) sRec
  recursorType : recursor.ty = recTy
  majorInductive :
    (tryOptional (do
      let recTy ← liftM (TcM.instantiateUnivParams recTy recUs)
      getMajorInductiveId recTy
        (recr.params + recr.motives + recr.minors +
          recr.indices).toUInt64)).run methods sRec = .ok (some indId) sScan

namespace SynthCtorWhenKSelectionTrace

theorem eval
    (h : SynthCtorWhenKSelectionTrace methods major recId recr recUs s)
    {outcome : EStateM.Result (TcError .anon) (TcState .anon)
      (KSynthOutcome .anon)}
    (hselect :
      (selectKSynthCandidate h.majorTyW h.tyHeadId h.tyUs h.tyArgs h.indId
        recr.params).run methods h.sScan = outcome) :
    (synthCtorWhenK major recId recr recUs).run methods s = outcome := by
  unfold synthCtorWhenK
  have hlevelsNe : (recUs.size.toUInt64 != recr.lvls) = false := by
    simp [h.levelArity]
  rw [hlevelsNe]
  simp only [Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryOptional (inferOnlyRec major)) methods) _ s = _
  unfold EStateM.bind
  rw [h.majorInfer]
  simp only
  change EStateM.bind
    (ReaderT.run (tryOptional (whnfRec h.majorTy)) methods) _ h.sInfer = _
  unfold EStateM.bind
  rw [h.majorWhnf]
  simp only
  rw [h.majorSpine]
  simp only
  change EStateM.bind (TcM.tryGetConst recId) _ h.sWhnf = _
  unfold EStateM.bind
  rw [h.recursorLookup]
  simp only
  rw [h.recursorType]
  simp only [pure_bind]
  change EStateM.bind
    (ReaderT.run
      (tryOptional (do
        let recTy ← liftM (TcM.instantiateUnivParams h.recTy recUs)
        getMajorInductiveId recTy
          (recr.params + recr.motives + recr.minors +
            recr.indices).toUInt64))
      methods) _ h.sRec = _
  unfold EStateM.bind
  rw [h.majorInductive]
  exact hselect

theorem mismatch
    (h : SynthCtorWhenKSelectionTrace methods major recId recr recUs s)
    (hmismatch : (h.tyHeadId.addr != h.indId.addr) = true) :
    (synthCtorWhenK major recId recr recUs).run methods s =
      .ok .inconclusive h.sScan :=
  h.eval (selectKSynthCandidate_mismatch hmismatch)

theorem missing
    (h : SynthCtorWhenKSelectionTrace methods major recId recr recUs s)
    {sf : TcState .anon}
    (hsame : (h.tyHeadId.addr != h.indId.addr) = false)
    (hlookup : TcM.tryGetConst h.indId h.sScan = .ok none sf) :
    (synthCtorWhenK major recId recr recUs).run methods s =
      .ok .inconclusive sf :=
  h.eval (selectKSynthCandidate_missing hsame hlookup)

theorem nonInductive
    (h : SynthCtorWhenKSelectionTrace methods major recId recr recUs s)
    {sf : TcState .anon} {entry : KConst .anon}
    (hsame : (h.tyHeadId.addr != h.indId.addr) = false)
    (hlookup : TcM.tryGetConst h.indId h.sScan = .ok (some entry) sf)
    (hshape : KSynthNonInductive entry) :
    (synthCtorWhenK major recId recr recUs).run methods s =
      .ok .inconclusive sf :=
  h.eval (selectKSynthCandidate_nonInductive hsame hlookup hshape)

theorem empty
    (h : SynthCtorWhenKSelectionTrace methods major recId recr recUs s)
    {sf : TcState .anon} {block : KId .anon}
    {lvls indParams indices : UInt64} {isUnsafe : Bool}
    {memberIdx : UInt64} {indTy : KExpr .anon}
    (hsame : (h.tyHeadId.addr != h.indId.addr) = false)
    (hlookup : TcM.tryGetConst h.indId h.sScan =
      .ok (some (.indc () () lvls indParams indices isUnsafe block memberIdx
        indTy #[] ())) sf) :
    (synthCtorWhenK major recId recr recUs).run methods s =
      .ok .inconclusive sf :=
  h.eval (selectKSynthCandidate_empty hsame hlookup)

theorem selected
    (h : SynthCtorWhenKSelectionTrace methods major recId recr recUs s)
    {sLookup sf : TcState .anon} {block ctorId : KId .anon}
    {lvls indParams indices : UInt64} {isUnsafe : Bool}
    {memberIdx : UInt64} {indTy : KExpr .anon}
    {ctors : Array (KId .anon)} {result : KSynthOutcome .anon}
    (hsame : (h.tyHeadId.addr != h.indId.addr) = false)
    (hlookup : TcM.tryGetConst h.indId h.sScan =
      .ok (some (.indc () () lvls indParams indices isUnsafe block memberIdx
        indTy ctors ())) sLookup)
    (hfirst : ctors[0]? = some ctorId)
    (hcandidate :
      (verifyKSynthCandidate h.majorTyW ctorId h.tyUs h.tyArgs recr.params).run
        methods sLookup = .ok result sf) :
    (synthCtorWhenK major recId recr recUs).run methods s = .ok result sf :=
  h.eval (selectKSynthCandidate_selected hsame hlookup hfirst hcandidate)

theorem selectedError
    (h : SynthCtorWhenKSelectionTrace methods major recId recr recUs s)
    {sLookup sf : TcState .anon} {block ctorId : KId .anon}
    {lvls indParams indices : UInt64} {isUnsafe : Bool}
    {memberIdx : UInt64} {indTy : KExpr .anon}
    {ctors : Array (KId .anon)} {err : TcError .anon}
    (hsame : (h.tyHeadId.addr != h.indId.addr) = false)
    (hlookup : TcM.tryGetConst h.indId h.sScan =
      .ok (some (.indc () () lvls indParams indices isUnsafe block memberIdx
        indTy ctors ())) sLookup)
    (hfirst : ctors[0]? = some ctorId)
    (hcandidate :
      (verifyKSynthCandidate h.majorTyW ctorId h.tyUs h.tyArgs recr.params).run
        methods sLookup = .error err sf) :
    (synthCtorWhenK major recId recr recUs).run methods s = .error err sf :=
  h.eval (selectKSynthCandidate_selectedError hsame hlookup hfirst hcandidate)

end SynthCtorWhenKSelectionTrace

end RecM

end Ix.Tc
