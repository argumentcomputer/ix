import Ix.Tc.Verify.Whnf.Iota.ConstructorSynthesisFallback

/-!
# Struct-eta iota control-flow closure

The ordinary-constructor, Nat/String-literal, and K-synthesis routes all
enter `tryIotaCtorOrStructEta` through a constructor hit.  This slice covers
the complementary fallthrough into `tryStructEtaIota`.  It names the exact
post-scan probe trace, proves every caught probe miss/error with its retained
state, exposes the H3 Prop guard, and records ordinary error propagation from
universe instantiation and rebuilding.

Semantic justification of a successful rebuilt rule remains indexed by an
explicit `WhnfMeaning` premise: the operational fact that an inductive looks
structure-like does not itself manufacture the registered Theory recursor
equation or projection interpretation.
-/

namespace Ix.Tc

namespace RecM

/-- Sorts in `Prop` are the sole rejected post-probe shape. -/
def StructEtaSortAdmissible (e : KExpr .anon) : Prop :=
  structEtaSortRejected e = false

/-- The defensive classifier lookup did not return an inductive declaration. -/
def StructEtaNonInductive : KConst .anon → Prop
  | .indc .. => False
  | _ => True

/-- Heads that bypass constructor catalog lookup and fall directly into the
struct-eta dispatcher. -/
def StructEtaDispatchNonConst : KExpr .anon → Prop
  | .const .. => False
  | _ => True

/-- An absent classifier entry is state-retaining failure, not an error. -/
theorem isStructLike_missing
    {methods : Methods .anon} {id : KId .anon} {s sf : TcState .anon}
    (hlookup : TcM.tryGetConst id s = .ok none sf) :
    (isStructLike id).run methods s = .ok false sf := by
  unfold isStructLike
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.tryGetConst id) _ s = _
  unfold EStateM.bind
  rw [hlookup]
  rfl

/-- A loaded non-inductive entry is rejected before the recursion probe. -/
theorem isStructLike_nonInductive
    {methods : Methods .anon} {id : KId .anon} {s sf : TcState .anon}
    {entry : KConst .anon}
    (hlookup : TcM.tryGetConst id s = .ok (some entry) sf)
    (hshape : StructEtaNonInductive entry) :
    (isStructLike id).run methods s = .ok false sf := by
  unfold isStructLike
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.tryGetConst id) _ s = _
  unfold EStateM.bind
  rw [hlookup]
  cases entry <;> simp [StructEtaNonInductive] at hshape ⊢

/-- Lookup errors are not swallowed by structure classification. -/
theorem isStructLike_lookupError
    {methods : Methods .anon} {id : KId .anon} {s sf : TcState .anon}
    {err : TcError .anon}
    (hlookup : TcM.tryGetConst id s = .error err sf) :
    (isStructLike id).run methods s = .error err sf := by
  unfold isStructLike
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.tryGetConst id) _ s = _
  unfold EStateM.bind
  rw [hlookup]

/-- Nonzero indices or a constructor count other than one reject the
inductive without consulting `computedIsRec`. -/
theorem isStructLike_badShape
    {methods : Methods .anon} {id block : KId .anon}
    {s sf : TcState .anon} {lvls params indices : UInt64}
    {isUnsafe : Bool} {memberIdx : UInt64} {ty : KExpr .anon}
    {ctors : Array (KId .anon)}
    (hlookup : TcM.tryGetConst id s =
      .ok (some (.indc () () lvls params indices isUnsafe block memberIdx ty
        ctors ())) sf)
    (hbad : (indices != 0 || ctors.size != 1) = true) :
    (isStructLike id).run methods s = .ok false sf := by
  unfold isStructLike
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.tryGetConst id) _ s = _
  unfold EStateM.bind
  rw [hlookup]
  simp only
  rw [hbad]
  rfl

/-- A shape-qualified inductive forwards the exact recursion result and its
post-state, negating only the returned Boolean. -/
theorem isStructLike_shapeQualified
    {methods : Methods .anon} {id block : KId .anon}
    {s sLookup sf : TcState .anon} {lvls params indices : UInt64}
    {isUnsafe recursive : Bool} {memberIdx : UInt64} {ty : KExpr .anon}
    {ctors : Array (KId .anon)}
    (hlookup : TcM.tryGetConst id s =
      .ok (some (.indc () () lvls params indices isUnsafe block memberIdx ty
        ctors ())) sLookup)
    (hshape : (indices != 0 || ctors.size != 1) = false)
    (hrec : (computedIsRec id).run methods sLookup = .ok recursive sf) :
    (isStructLike id).run methods s = .ok (!recursive) sf := by
  unfold isStructLike
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.tryGetConst id) _ s = _
  unfold EStateM.bind
  rw [hlookup]
  simp only
  rw [hshape]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (computedIsRec id) methods) _ sLookup = _
  unfold EStateM.bind
  rw [hrec]
  rfl

/-- Recursion-computation errors propagate after the qualified lookup. -/
theorem isStructLike_recError
    {methods : Methods .anon} {id block : KId .anon}
    {s sLookup sf : TcState .anon} {lvls params indices : UInt64}
    {isUnsafe : Bool} {memberIdx : UInt64} {ty : KExpr .anon}
    {ctors : Array (KId .anon)} {err : TcError .anon}
    (hlookup : TcM.tryGetConst id s =
      .ok (some (.indc () () lvls params indices isUnsafe block memberIdx ty
        ctors ())) sLookup)
    (hshape : (indices != 0 || ctors.size != 1) = false)
    (hrec : (computedIsRec id).run methods sLookup = .error err sf) :
    (isStructLike id).run methods s = .error err sf := by
  unfold isStructLike
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.tryGetConst id) _ s = _
  unfold EStateM.bind
  rw [hlookup]
  simp only
  rw [hshape]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (computedIsRec id) methods) _ sLookup = _
  unfold EStateM.bind
  rw [hrec]

/-- Zero prefix, fields, and trailing arguments leave the instantiated rule
unchanged and do not touch checker state. -/
theorem finishStructEtaResult_empty
    (methods : Methods .anon) (s : TcState .anon)
    (indId : KId .anon) (major rhs : KExpr .anon) :
    (finishStructEtaResult indId major rhs 0 #[] #[]).run methods s =
      .ok rhs s := by
  simp [finishStructEtaResult, finishAppResult, finishStructEtaFields]

/-- Direct expression interning cannot raise a checker error, independently
of collision behavior. -/
theorem structEtaIntern_total (e : KExpr .anon) (s : TcState .anon) :
    ∃ result sf, TcM.intern e s = .ok result sf := by
  let pair := internExprM e s.env.intern
  exact ⟨pair.1, { s with env := { s.env with intern := pair.2 } }, rfl⟩

/-- Every field segment terminates successfully.  This is deliberately only
an operational theorem: collision freedom is still required to identify the
returned nodes with the requested projections and applications. -/
theorem finishStructEtaFields_total
    (methods : Methods .anon) (s : TcState .anon)
    (indId : KId .anon) (major result : KExpr .anon)
    (fuel field : Nat) :
    ∃ final sf,
      (finishStructEtaFields indId major fuel field result).run methods s =
        .ok final sf := by
  induction fuel generalizing field result s with
  | zero => exact ⟨result, s, rfl⟩
  | succ fuel ih =>
      obtain ⟨proj, sProj, hproj⟩ := structEtaIntern_total
        (KExpr.mkPrj indId field.toUInt64 major) s
      obtain ⟨applied, sApp, happ⟩ := structEtaIntern_total
        (KExpr.mkApp result proj) sProj
      obtain ⟨final, sf, htail⟩ :=
        ih (s := sApp) (field := field + 1) (result := applied)
      refine ⟨final, sf, ?_⟩
      unfold finishStructEtaFields
      rw [ReaderT.run_bind, ReaderT.run_monadLift]
      change EStateM.bind
        (TcM.intern (KExpr.mkPrj indId field.toUInt64 major)) _ s = _
      unfold EStateM.bind
      rw [hproj]
      simp only
      rw [ReaderT.run_bind, ReaderT.run_monadLift]
      change EStateM.bind (TcM.intern (KExpr.mkApp result proj)) _ sProj = _
      unfold EStateM.bind
      rw [happ]
      exact htail

/-- Exact composition equation for the prefix, field, and trailing rebuild
segments. -/
theorem finishStructEtaResult_of_segments
    {methods : Methods .anon} {s sPrefix sFields sf : TcState .anon}
    {indId : KId .anon} {major rhs prefixResult fieldsResult final :
      KExpr .anon}
    {fields : UInt64}
    {prefixArgs trailingArgs : Array (KExpr .anon)}
    (hprefix : (finishAppResult rhs prefixArgs 0).run methods s =
      .ok prefixResult sPrefix)
    (hfields :
      (finishStructEtaFields indId major fields.toNat 0 prefixResult).run
        methods sPrefix = .ok fieldsResult sFields)
    (htrailing : (finishAppResult fieldsResult trailingArgs 0).run methods
      sFields = .ok final sf) :
    (finishStructEtaResult indId major rhs fields prefixArgs trailingArgs).run
      methods s = .ok final sf := by
  unfold finishStructEtaResult
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (finishAppResult rhs prefixArgs 0) methods)
    _ s = _
  unfold EStateM.bind
  rw [hprefix]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run
      (finishStructEtaFields indId major fields.toNat 0 prefixResult) methods)
      _ sPrefix = _
  unfold EStateM.bind
  rw [hfields]
  exact htrailing

/-- The complete three-segment rebuild cannot fail. -/
theorem finishStructEtaResult_total
    (methods : Methods .anon) (s : TcState .anon)
    (indId : KId .anon) (major rhs : KExpr .anon) (fields : UInt64)
    (prefixArgs trailingArgs : Array (KExpr .anon)) :
    ∃ final sf,
      (finishStructEtaResult indId major rhs fields prefixArgs trailingArgs).run
        methods s = .ok final sf := by
  obtain ⟨prefixResult, sPrefix, hprefix⟩ :=
    finishAppResult_total (methods := methods) (s := s) rhs prefixArgs 0
  obtain ⟨fieldsResult, sFields, hfields⟩ :=
    finishStructEtaFields_total methods sPrefix indId major prefixResult
      fields.toNat 0
  obtain ⟨final, sf, htrailing⟩ :=
    finishAppResult_total (methods := methods) (s := sFields) fieldsResult
      trailingArgs 0
  exact ⟨final, sf,
    finishStructEtaResult_of_segments hprefix hfields htrailing⟩

/-- Consequently, no projection/application rebuilding error is reachable.
Any struct-eta error after the H3 guard must have arisen during universe
instantiation. -/
theorem finishStructEtaResult_ne_error
    (methods : Methods .anon) (s : TcState .anon)
    (indId : KId .anon) (major rhs : KExpr .anon) (fields : UInt64)
    (prefixArgs trailingArgs : Array (KExpr .anon))
    (err : TcError .anon) (sf : TcState .anon) :
    (finishStructEtaResult indId major rhs fields prefixArgs trailingArgs).run
      methods s ≠ .error err sf := by
  intro herror
  obtain ⟨final, sFinal, hsuccess⟩ :=
    finishStructEtaResult_total methods s indId major rhs fields prefixArgs
      trailingArgs
  rw [hsuccess] at herror
  contradiction

/-- The H3 guard rejects a Prop-valued major before universe instantiation or
any result interning. -/
theorem finishStructEtaAfterSort_prop
    {methods : Methods .anon} {s : TcState .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {recr : IotaInfo .anon} {rule : RecRule .anon} {indId : KId .anon}
    {major : KExpr .anon} {u : KUniv .anon} {info : ExprInfo .anon}
    (hzero : u.isZero = true) :
    (finishStructEtaAfterSort recUs spine recr rule indId major
      (.sort u info)).run methods s = .ok none s := by
  simp [finishStructEtaAfterSort, structEtaSortRejected, hzero]

/-- Any admissible sort/non-sort shape forwards successful universe
instantiation and rebuilding with their exact intermediate states. -/
theorem finishStructEtaAfterSort_success
    {methods : Methods .anon} {s sInst sf : TcState .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {recr : IotaInfo .anon} {rule : RecRule .anon} {indId : KId .anon}
    {major majorSortW rhs result : KExpr .anon}
    (hadmissible : StructEtaSortAdmissible majorSortW)
    (hinst : TcM.instantiateUnivParams rule.rhs recUs s = .ok rhs sInst)
    (hfinish :
      (finishStructEtaResult indId major rhs rule.fields
        (spine.extract 0
          (min (recr.params + recr.motives + recr.minors) spine.size))
        (spine.extract (recr.majorIdx + 1) spine.size)).run methods sInst =
          .ok result sf) :
    (finishStructEtaAfterSort recUs spine recr rule indId major
      majorSortW).run methods s = .ok (some result) sf := by
  unfold StructEtaSortAdmissible at hadmissible
  unfold finishStructEtaAfterSort
  rw [hadmissible]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.instantiateUnivParams rule.rhs recUs) _ s = _
  unfold EStateM.bind
  rw [hinst]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run
      (finishStructEtaResult indId major rhs rule.fields
        (spine.extract 0
          (min (recr.params + recr.motives + recr.minors) spine.size))
        (spine.extract (recr.majorIdx + 1) spine.size)) methods) _ sInst = _
  unfold EStateM.bind
  rw [hfinish]
  rfl

/-- Universe-instantiation errors are not caught by struct eta. -/
theorem finishStructEtaAfterSort_instantiateError
    {methods : Methods .anon} {s sf : TcState .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {recr : IotaInfo .anon} {rule : RecRule .anon} {indId : KId .anon}
    {major majorSortW : KExpr .anon} {err : TcError .anon}
    (hadmissible : StructEtaSortAdmissible majorSortW)
    (hinst : TcM.instantiateUnivParams rule.rhs recUs s = .error err sf) :
    (finishStructEtaAfterSort recUs spine recr rule indId major
      majorSortW).run methods s = .error err sf := by
  unfold StructEtaSortAdmissible at hadmissible
  unfold finishStructEtaAfterSort
  rw [hadmissible]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.instantiateUnivParams rule.rhs recUs) _ s = _
  unfold EStateM.bind
  rw [hinst]

/-- Generic forwarding equation for a hypothetical rebuilding error.  The
premise is eliminated by `finishStructEtaResult_ne_error`; the theorem is
retained only as a compositional equation for clients that case-split before
using totality. -/
theorem finishStructEtaAfterSort_finishError
    {methods : Methods .anon} {s sInst sf : TcState .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {recr : IotaInfo .anon} {rule : RecRule .anon} {indId : KId .anon}
    {major majorSortW rhs : KExpr .anon} {err : TcError .anon}
    (hadmissible : StructEtaSortAdmissible majorSortW)
    (hinst : TcM.instantiateUnivParams rule.rhs recUs s = .ok rhs sInst)
    (hfinish :
      (finishStructEtaResult indId major rhs rule.fields
        (spine.extract 0
          (min (recr.params + recr.motives + recr.minors) spine.size))
        (spine.extract (recr.majorIdx + 1) spine.size)).run methods sInst =
          .error err sf) :
    (finishStructEtaAfterSort recUs spine recr rule indId major
      majorSortW).run methods s = .error err sf := by
  unfold StructEtaSortAdmissible at hadmissible
  unfold finishStructEtaAfterSort
  rw [hadmissible]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.instantiateUnivParams rule.rhs recUs) _ s = _
  unfold EStateM.bind
  rw [hinst]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run
      (finishStructEtaResult indId major rhs rule.fields
        (spine.extract 0
          (min (recr.params + recr.motives + recr.minors) spine.size))
        (spine.extract (recr.majorIdx + 1) spine.size)) methods) _ sInst = _
  unfold EStateM.bind
  rw [hfinish]

/-- A failed structure classification is a silent miss with the classifier's
post-state. -/
theorem tryStructEtaAfterInductive_notStruct
    {methods : Methods .anon} {s sf : TcState .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {recr : IotaInfo .anon} {rule : RecRule .anon} {indId : KId .anon}
    (hstruct : (isStructLike indId).run methods s = .ok false sf) :
    (tryStructEtaAfterInductive recUs spine recr rule indId).run methods s =
      .ok none sf := by
  unfold tryStructEtaAfterInductive
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (isStructLike indId) methods) _ s = _
  unfold EStateM.bind
  rw [hstruct]
  rfl

/-- Classification errors are not among struct eta's caught probes. -/
theorem tryStructEtaAfterInductive_structError
    {methods : Methods .anon} {s sf : TcState .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {recr : IotaInfo .anon} {rule : RecRule .anon} {indId : KId .anon}
    {err : TcError .anon}
    (hstruct : (isStructLike indId).run methods s = .error err sf) :
    (tryStructEtaAfterInductive recUs spine recr rule indId).run methods s =
      .error err sf := by
  unfold tryStructEtaAfterInductive
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (isStructLike indId) methods) _ s = _
  unfold EStateM.bind
  rw [hstruct]

/-- The first inference probe can silently miss after a successful structure
classification. -/
theorem tryStructEtaAfterInductive_majorInferMiss
    {methods : Methods .anon} {s sStruct sf : TcState .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {recr : IotaInfo .anon} {rule : RecRule .anon} {indId : KId .anon}
    (hstruct : (isStructLike indId).run methods s = .ok true sStruct)
    (hinfer : (tryOptional (inferOnlyRec spine[recr.majorIdx]!)).run
      methods sStruct = .ok none sf) :
    (tryStructEtaAfterInductive recUs spine recr rule indId).run methods s =
      .ok none sf := by
  unfold tryStructEtaAfterInductive
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (isStructLike indId) methods) _ s = _
  unfold EStateM.bind
  rw [hstruct]
  simp only [Bool.not_true, Bool.false_eq_true, if_false, pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryOptional (inferOnlyRec spine[recr.majorIdx]!)) methods) _
      sStruct = _
  unfold EStateM.bind
  rw [hinfer]
  rfl

theorem tryStructEtaAfterInductive_majorInferError
    {methods : Methods .anon} {s sStruct sf : TcState .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {recr : IotaInfo .anon} {rule : RecRule .anon} {indId : KId .anon}
    {err : TcError .anon}
    (hstruct : (isStructLike indId).run methods s = .ok true sStruct)
    (hinfer : (inferOnlyRec spine[recr.majorIdx]!).run methods sStruct =
      .error err sf) :
    (tryStructEtaAfterInductive recUs spine recr rule indId).run methods s =
      .ok none sf :=
  tryStructEtaAfterInductive_majorInferMiss hstruct
    (tryOptional_error hinfer)

/-- The second inference probe can silently miss after retaining both prior
post-states. -/
theorem tryStructEtaAfterInductive_sortInferMiss
    {methods : Methods .anon} {s sStruct sMajorTy sf : TcState .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {recr : IotaInfo .anon} {rule : RecRule .anon} {indId : KId .anon}
    {majorTy : KExpr .anon}
    (hstruct : (isStructLike indId).run methods s = .ok true sStruct)
    (hmajor : (tryOptional (inferOnlyRec spine[recr.majorIdx]!)).run
      methods sStruct = .ok (some majorTy) sMajorTy)
    (hsort : (tryOptional (inferOnlyRec majorTy)).run methods sMajorTy =
      .ok none sf) :
    (tryStructEtaAfterInductive recUs spine recr rule indId).run methods s =
      .ok none sf := by
  unfold tryStructEtaAfterInductive
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (isStructLike indId) methods) _ s = _
  unfold EStateM.bind
  rw [hstruct]
  simp only [Bool.not_true, Bool.false_eq_true, if_false, pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryOptional (inferOnlyRec spine[recr.majorIdx]!)) methods) _
      sStruct = _
  unfold EStateM.bind
  rw [hmajor]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryOptional (inferOnlyRec majorTy)) methods) _ sMajorTy = _
  unfold EStateM.bind
  rw [hsort]
  rfl

theorem tryStructEtaAfterInductive_sortInferError
    {methods : Methods .anon} {s sStruct sMajorTy sf : TcState .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {recr : IotaInfo .anon} {rule : RecRule .anon} {indId : KId .anon}
    {majorTy : KExpr .anon} {err : TcError .anon}
    (hstruct : (isStructLike indId).run methods s = .ok true sStruct)
    (hmajor : (tryOptional (inferOnlyRec spine[recr.majorIdx]!)).run
      methods sStruct = .ok (some majorTy) sMajorTy)
    (hsort : (inferOnlyRec majorTy).run methods sMajorTy = .error err sf) :
    (tryStructEtaAfterInductive recUs spine recr rule indId).run methods s =
      .ok none sf :=
  tryStructEtaAfterInductive_sortInferMiss hstruct hmajor
    (tryOptional_error hsort)

/-- The final WHNF probe can silently miss after both successful inference
callbacks. -/
theorem tryStructEtaAfterInductive_sortWhnfMiss
    {methods : Methods .anon}
    {s sStruct sMajorTy sMajorSort sf : TcState .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {recr : IotaInfo .anon} {rule : RecRule .anon} {indId : KId .anon}
    {majorTy majorSort : KExpr .anon}
    (hstruct : (isStructLike indId).run methods s = .ok true sStruct)
    (hmajor : (tryOptional (inferOnlyRec spine[recr.majorIdx]!)).run
      methods sStruct = .ok (some majorTy) sMajorTy)
    (hsort : (tryOptional (inferOnlyRec majorTy)).run methods sMajorTy =
      .ok (some majorSort) sMajorSort)
    (hwhnf : (tryOptional (whnfRec majorSort)).run methods sMajorSort =
      .ok none sf) :
    (tryStructEtaAfterInductive recUs spine recr rule indId).run methods s =
      .ok none sf := by
  unfold tryStructEtaAfterInductive
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (isStructLike indId) methods) _ s = _
  unfold EStateM.bind
  rw [hstruct]
  simp only [Bool.not_true, Bool.false_eq_true, if_false, pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryOptional (inferOnlyRec spine[recr.majorIdx]!)) methods) _
      sStruct = _
  unfold EStateM.bind
  rw [hmajor]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryOptional (inferOnlyRec majorTy)) methods) _ sMajorTy = _
  unfold EStateM.bind
  rw [hsort]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryOptional (whnfRec majorSort)) methods) _ sMajorSort = _
  unfold EStateM.bind
  rw [hwhnf]
  rfl

theorem tryStructEtaAfterInductive_sortWhnfError
    {methods : Methods .anon}
    {s sStruct sMajorTy sMajorSort sf : TcState .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {recr : IotaInfo .anon} {rule : RecRule .anon} {indId : KId .anon}
    {majorTy majorSort : KExpr .anon} {err : TcError .anon}
    (hstruct : (isStructLike indId).run methods s = .ok true sStruct)
    (hmajor : (tryOptional (inferOnlyRec spine[recr.majorIdx]!)).run
      methods sStruct = .ok (some majorTy) sMajorTy)
    (hsort : (tryOptional (inferOnlyRec majorTy)).run methods sMajorTy =
      .ok (some majorSort) sMajorSort)
    (hwhnf : (whnfRec majorSort).run methods sMajorSort = .error err sf) :
    (tryStructEtaAfterInductive recUs spine recr rule indId).run methods s =
      .ok none sf :=
  tryStructEtaAfterInductive_sortWhnfMiss hstruct hmajor hsort
    (tryOptional_error hwhnf)

/-- Exact successful probe prefix through classification, both inference
callbacks, and sort WHNF. -/
structure StructEtaProbeTrace
    (methods : Methods .anon) (recUs : Array (KUniv .anon))
    (spine : Array (KExpr .anon)) (recr : IotaInfo .anon)
    (rule : RecRule .anon) (indId : KId .anon) (s : TcState .anon) : Type where
  majorTy : KExpr .anon
  majorSort : KExpr .anon
  majorSortW : KExpr .anon
  sStruct : TcState .anon
  sMajorTy : TcState .anon
  sMajorSort : TcState .anon
  sMajorSortW : TcState .anon
  structLike : (isStructLike indId).run methods s = .ok true sStruct
  majorInfer :
    (tryOptional (inferOnlyRec spine[recr.majorIdx]!)).run methods sStruct =
      .ok (some majorTy) sMajorTy
  sortInfer : (tryOptional (inferOnlyRec majorTy)).run methods sMajorTy =
    .ok (some majorSort) sMajorSort
  sortWhnf : (tryOptional (whnfRec majorSort)).run methods sMajorSort =
    .ok (some majorSortW) sMajorSortW

namespace StructEtaProbeTrace

/-- Any post-probe outcome is forwarded exactly. -/
theorem eval
    (h : StructEtaProbeTrace methods recUs spine recr rule indId s)
    {outcome : EStateM.Result (TcError .anon) (TcState .anon)
      (Option (KExpr .anon))}
    (hfinish :
      (finishStructEtaAfterSort recUs spine recr rule indId
        spine[recr.majorIdx]! h.majorSortW).run methods h.sMajorSortW =
          outcome) :
    (tryStructEtaAfterInductive recUs spine recr rule indId).run methods s =
      outcome := by
  unfold tryStructEtaAfterInductive
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (isStructLike indId) methods) _ s = _
  unfold EStateM.bind
  rw [h.structLike]
  simp only [Bool.not_true, Bool.false_eq_true, if_false, pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryOptional (inferOnlyRec spine[recr.majorIdx]!)) methods) _
      h.sStruct = _
  unfold EStateM.bind
  rw [h.majorInfer]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryOptional (inferOnlyRec h.majorTy)) methods) _
      h.sMajorTy = _
  unfold EStateM.bind
  rw [h.sortInfer]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryOptional (whnfRec h.majorSort)) methods) _
      h.sMajorSort = _
  unfold EStateM.bind
  rw [h.sortWhnf]
  exact hfinish

theorem prop
    (h : StructEtaProbeTrace methods recUs spine recr rule indId s)
    {u : KUniv .anon} {info : ExprInfo .anon}
    (hsort : h.majorSortW = .sort u info) (hzero : u.isZero = true) :
    (tryStructEtaAfterInductive recUs spine recr rule indId).run methods s =
      .ok none h.sMajorSortW := by
  apply h.eval
  rw [hsort]
  exact finishStructEtaAfterSort_prop hzero

theorem success
    (h : StructEtaProbeTrace methods recUs spine recr rule indId s)
    {sInst sf : TcState .anon} {rhs result : KExpr .anon}
    (hadmissible : StructEtaSortAdmissible h.majorSortW)
    (hinst : TcM.instantiateUnivParams rule.rhs recUs h.sMajorSortW =
      .ok rhs sInst)
    (hbuild :
      (finishStructEtaResult indId spine[recr.majorIdx]! rhs rule.fields
        (spine.extract 0
          (min (recr.params + recr.motives + recr.minors) spine.size))
        (spine.extract (recr.majorIdx + 1) spine.size)).run methods sInst =
          .ok result sf) :
    (tryStructEtaAfterInductive recUs spine recr rule indId).run methods s =
      .ok (some result) sf :=
  h.eval (finishStructEtaAfterSort_success hadmissible hinst hbuild)

theorem finishError
    (h : StructEtaProbeTrace methods recUs spine recr rule indId s)
    {sInst sf : TcState .anon} {rhs : KExpr .anon} {err : TcError .anon}
    (hadmissible : StructEtaSortAdmissible h.majorSortW)
    (hinst : TcM.instantiateUnivParams rule.rhs recUs h.sMajorSortW =
      .ok rhs sInst)
    (hbuild :
      (finishStructEtaResult indId spine[recr.majorIdx]! rhs rule.fields
        (spine.extract 0
          (min (recr.params + recr.motives + recr.minors) spine.size))
        (spine.extract (recr.majorIdx + 1) spine.size)).run methods sInst =
          .error err sf) :
    (tryStructEtaAfterInductive recUs spine recr rule indId).run methods s =
      .error err sf :=
  h.eval (finishStructEtaAfterSort_finishError hadmissible hinst hbuild)

end StructEtaProbeTrace

/-- Rule-count rejection happens before any catalog access. -/
theorem tryStructEtaIota_ruleCount
    {methods : Methods .anon} {s : TcState .anon} {recId : KId .anon}
    {recr : IotaInfo .anon} {recUs : Array (KUniv .anon)}
    {spine : Array (KExpr .anon)}
    (hcount : (recr.rules.size != 1) = true) :
    (tryStructEtaIota recId recr recUs spine).run methods s = .ok none s := by
  unfold tryStructEtaIota
  rw [hcount]
  rfl

/-- With one selected rule, a malformed recursor universe application is
rejected before the repeated catalog lookup or type scan. -/
theorem tryStructEtaIota_levelMismatch
    {methods : Methods .anon} {s : TcState .anon} {recId : KId .anon}
    {recr : IotaInfo .anon} {recUs : Array (KUniv .anon)}
    {spine : Array (KExpr .anon)}
    (hcount : (recr.rules.size != 1) = false)
    (hlevels : (recUs.size.toUInt64 != recr.lvls) = true) :
    (tryStructEtaIota recId recr recUs spine).run methods s = .ok none s := by
  unfold tryStructEtaIota
  rw [hcount]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  rw [hlevels]
  rfl

/-- An absent recursor during the defensive repeated lookup is a silent miss. -/
theorem tryStructEtaIota_recursorMissing
    {methods : Methods .anon} {s sf : TcState .anon} {recId : KId .anon}
    {recr : IotaInfo .anon} {recUs : Array (KUniv .anon)}
    {spine : Array (KExpr .anon)}
    (hcount : (recr.rules.size != 1) = false)
    (hlevels : recUs.size.toUInt64 = recr.lvls)
    (hlookup : TcM.tryGetConst recId s = .ok none sf) :
    (tryStructEtaIota recId recr recUs spine).run methods s = .ok none sf := by
  unfold tryStructEtaIota
  rw [hcount]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  have hlevelsNe : (recUs.size.toUInt64 != recr.lvls) = false := by
    simp [hlevels]
  rw [hlevelsNe]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  change EStateM.bind (TcM.tryGetConst recId) _ s = _
  unfold EStateM.bind
  rw [hlookup]
  rfl

/-- Recursor lookup errors remain errors. -/
theorem tryStructEtaIota_recursorError
    {methods : Methods .anon} {s sf : TcState .anon} {recId : KId .anon}
    {recr : IotaInfo .anon} {recUs : Array (KUniv .anon)}
    {spine : Array (KExpr .anon)} {err : TcError .anon}
    (hcount : (recr.rules.size != 1) = false)
    (hlevels : recUs.size.toUInt64 = recr.lvls)
    (hlookup : TcM.tryGetConst recId s = .error err sf) :
    (tryStructEtaIota recId recr recUs spine).run methods s =
      .error err sf := by
  unfold tryStructEtaIota
  rw [hcount]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  have hlevelsNe : (recUs.size.toUInt64 != recr.lvls) = false := by
    simp [hlevels]
  rw [hlevelsNe]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  change EStateM.bind (TcM.tryGetConst recId) _ s = _
  unfold EStateM.bind
  rw [hlookup]

/-- Failure of the bounded major-inductive scan is caught after the repeated
recursor lookup, retaining the scan's post-state. -/
theorem tryStructEtaIota_majorInductiveMiss
    {methods : Methods .anon} {s sRec sf : TcState .anon}
    {recId : KId .anon} {recr : IotaInfo .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {rule : RecRule .anon} {recursor : KConst .anon}
    {recTy : KExpr .anon}
    (hcount : (recr.rules.size != 1) = false)
    (hlevels : recUs.size.toUInt64 = recr.lvls)
    (hrule : recr.rules[0]! = rule)
    (hlookup : TcM.tryGetConst recId s = .ok (some recursor) sRec)
    (hrecTy : recursor.ty = recTy)
    (hscan :
      (tryOptional (do
        let recTy ← liftM (TcM.instantiateUnivParams recTy recUs)
        getMajorInductiveId recTy
          (recr.params + recr.motives + recr.minors +
            recr.indices).toUInt64)).run methods sRec = .ok none sf) :
    (tryStructEtaIota recId recr recUs spine).run methods s = .ok none sf := by
  unfold tryStructEtaIota
  rw [hcount]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  have hlevelsNe : (recUs.size.toUInt64 != recr.lvls) = false := by
    simp [hlevels]
  rw [hlevelsNe]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  rw [hrule]
  change EStateM.bind (TcM.tryGetConst recId) _ s = _
  unfold EStateM.bind
  rw [hlookup]
  simp only
  rw [hrecTy]
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

theorem tryStructEtaIota_majorInductiveError
    {methods : Methods .anon} {s sRec sf : TcState .anon}
    {recId : KId .anon} {recr : IotaInfo .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {rule : RecRule .anon} {recursor : KConst .anon}
    {recTy : KExpr .anon} {err : TcError .anon}
    (hcount : (recr.rules.size != 1) = false)
    (hlevels : recUs.size.toUInt64 = recr.lvls)
    (hrule : recr.rules[0]! = rule)
    (hlookup : TcM.tryGetConst recId s = .ok (some recursor) sRec)
    (hrecTy : recursor.ty = recTy)
    (hscan :
      (do
        let recTy ← liftM (TcM.instantiateUnivParams recTy recUs)
        getMajorInductiveId recTy
          (recr.params + recr.motives + recr.minors +
            recr.indices).toUInt64).run methods sRec = .error err sf) :
    (tryStructEtaIota recId recr recUs spine).run methods s = .ok none sf :=
  tryStructEtaIota_majorInductiveMiss hcount hlevels hrule hlookup hrecTy
    (tryOptional_error hscan)

/-- Exact selected prefix through the single rule, repeated recursor lookup,
and caught inductive scan. -/
structure StructEtaSelectionTrace
    (methods : Methods .anon) (recId : KId .anon) (recr : IotaInfo .anon)
    (recUs : Array (KUniv .anon)) (spine : Array (KExpr .anon))
    (s : TcState .anon) : Type where
  rule : RecRule .anon
  recursor : KConst .anon
  recTy : KExpr .anon
  indId : KId .anon
  sRec : TcState .anon
  sScan : TcState .anon
  ruleCount : (recr.rules.size != 1) = false
  levelArity : recUs.size.toUInt64 = recr.lvls
  selectedRule : recr.rules[0]! = rule
  recursorLookup : TcM.tryGetConst recId s = .ok (some recursor) sRec
  recursorType : recursor.ty = recTy
  majorInductive :
    (tryOptional (do
      let recTy ← liftM (TcM.instantiateUnivParams recTy recUs)
      getMajorInductiveId recTy
        (recr.params + recr.motives + recr.minors +
          recr.indices).toUInt64)).run methods sRec = .ok (some indId) sScan

namespace StructEtaSelectionTrace

theorem eval
    (h : StructEtaSelectionTrace methods recId recr recUs spine s)
    {outcome : EStateM.Result (TcError .anon) (TcState .anon)
      (Option (KExpr .anon))}
    (hafter :
      (tryStructEtaAfterInductive recUs spine recr h.rule h.indId).run
        methods h.sScan = outcome) :
    (tryStructEtaIota recId recr recUs spine).run methods s = outcome := by
  unfold tryStructEtaIota
  rw [h.ruleCount]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  have hlevelsNe : (recUs.size.toUInt64 != recr.lvls) = false := by
    simp [h.levelArity]
  rw [hlevelsNe]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  rw [h.selectedRule]
  change EStateM.bind (TcM.tryGetConst recId) _ s = _
  unfold EStateM.bind
  rw [h.recursorLookup]
  simp only
  rw [h.recursorType]
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
  exact hafter

end StructEtaSelectionTrace

/-- Complete successful path through single-rule selection, the bounded
inductive scan, all three caught probes, universe instantiation, and the
three rebuilding segments. -/
structure StructEtaIotaSuccessTrace
    (methods : Methods .anon) (recId : KId .anon) (recr : IotaInfo .anon)
    (recUs : Array (KUniv .anon)) (spine : Array (KExpr .anon))
    (s : TcState .anon) (result : KExpr .anon) (sf : TcState .anon) : Type where
  selection : StructEtaSelectionTrace methods recId recr recUs spine s
  probes : StructEtaProbeTrace methods recUs spine recr selection.rule
    selection.indId selection.sScan
  rhs : KExpr .anon
  sInst : TcState .anon
  admissible : StructEtaSortAdmissible probes.majorSortW
  instantiation :
    TcM.instantiateUnivParams selection.rule.rhs recUs probes.sMajorSortW =
      .ok rhs sInst
  rebuild :
    (finishStructEtaResult selection.indId spine[recr.majorIdx]! rhs
      selection.rule.fields
      (spine.extract 0
        (min (recr.params + recr.motives + recr.minors) spine.size))
      (spine.extract (recr.majorIdx + 1) spine.size)).run methods sInst =
        .ok result sf

namespace StructEtaIotaSuccessTrace

/-- The complete trace is an exact execution of production
`tryStructEtaIota`. -/
theorem eval
    (h : StructEtaIotaSuccessTrace methods recId recr recUs spine s result
      sf) :
    (tryStructEtaIota recId recr recUs spine).run methods s =
      .ok (some result) sf :=
  h.selection.eval
    (h.probes.success h.admissible h.instantiation h.rebuild)

/-- K1 acceptance at the honest semantic boundary.  The operational trace is
constructed here; state preservation, finite support, and Theory meaning are
explicit premises because structure-likeness alone does not supply the
registered struct-eta equation or projection interpretation. -/
theorem acceptance
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx}
    (h : StructEtaIotaSuccessTrace methods recId recr recUs spine s result
      sf)
    {source : KExpr .anon}
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta sf)
    (hframe : InternUpdateFrame s sf)
    (hsupport : support result)
    (hmeaning : WhnfMeaning trProj world uvars Delta source result) :
    (tryStructEtaIota recId recr recUs spine).run methods s =
        .ok (some result) sf ∧
      WhnfStateInv layer semantics trProj world support uvars Delta sf ∧
      InternUpdateFrame s sf ∧
      support result ∧
      WhnfMeaning trProj world uvars Delta source result :=
  ⟨h.eval, hI, hframe, hsupport, hmeaning⟩

end StructEtaIotaSuccessTrace

/-! ### Final constructor/struct-eta dispatch -/

/-- A non-constant normalized head reaches struct eta without touching the
constant catalog. -/
theorem tryIotaCtorOrStructEta_nonConst
    {methods : Methods .anon} {s : TcState .anon}
    {recId : KId .anon} {recr : IotaInfo .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {majorWhnf ctorHead : KExpr .anon} {ctorArgs : Array (KExpr .anon)}
    {transient : Bool}
    {outcome : EStateM.Result (TcError .anon) (TcState .anon)
      (Option (KExpr .anon))}
    (hspine : majorWhnf.collectSpine = (ctorHead, ctorArgs))
    (hshape : StructEtaDispatchNonConst ctorHead)
    (heta : (tryStructEtaIota recId recr recUs spine).run methods s =
      outcome) :
    (tryIotaCtorOrStructEta recId recr recUs spine majorWhnf transient).run
      methods s = outcome := by
  unfold tryIotaCtorOrStructEta
  rw [hspine]
  cases ctorHead <;> simp [StructEtaDispatchNonConst] at hshape ⊢
  all_goals exact heta

/-- An absent constant-head entry retains the lookup state and falls through
to struct eta. -/
theorem tryIotaCtorOrStructEta_missing
    {methods : Methods .anon} {s sLookup : TcState .anon}
    {recId ctorId : KId .anon} {recr : IotaInfo .anon}
    {recUs ctorUs : Array (KUniv .anon)}
    {spine ctorArgs : Array (KExpr .anon)}
    {majorWhnf : KExpr .anon} {ctorInfo : ExprInfo .anon}
    {transient : Bool}
    {outcome : EStateM.Result (TcError .anon) (TcState .anon)
      (Option (KExpr .anon))}
    (hspine : majorWhnf.collectSpine =
      (.const ctorId ctorUs ctorInfo, ctorArgs))
    (hlookup : TcM.tryGetConst ctorId s = .ok none sLookup)
    (heta : (tryStructEtaIota recId recr recUs spine).run methods sLookup =
      outcome) :
    (tryIotaCtorOrStructEta recId recr recUs spine majorWhnf transient).run
      methods s = outcome := by
  unfold tryIotaCtorOrStructEta
  rw [hspine, ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.tryGetConst ctorId) _ s = _
  unfold EStateM.bind
  rw [hlookup]
  simpa only [pure_bind] using heta

/-- A loaded constant without constructor iota metadata takes the same
fallthrough, starting from the lookup's exact post-state. -/
theorem tryIotaCtorOrStructEta_notConstructor
    {methods : Methods .anon} {s sLookup : TcState .anon}
    {recId ctorId : KId .anon} {recr : IotaInfo .anon}
    {recUs ctorUs : Array (KUniv .anon)}
    {spine ctorArgs : Array (KExpr .anon)}
    {majorWhnf : KExpr .anon} {ctorInfo : ExprInfo .anon}
    {entry : KConst .anon} {transient : Bool}
    {outcome : EStateM.Result (TcError .anon) (TcState .anon)
      (Option (KExpr .anon))}
    (hspine : majorWhnf.collectSpine =
      (.const ctorId ctorUs ctorInfo, ctorArgs))
    (hlookup : TcM.tryGetConst ctorId s = .ok (some entry) sLookup)
    (hinfo : entry.iotaCtorInfo? = none)
    (heta : (tryStructEtaIota recId recr recUs spine).run methods sLookup =
      outcome) :
    (tryIotaCtorOrStructEta recId recr recUs spine majorWhnf transient).run
      methods s = outcome := by
  unfold tryIotaCtorOrStructEta
  rw [hspine, ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.tryGetConst ctorId) _ s = _
  unfold EStateM.bind
  rw [hlookup]
  simp only [hinfo, pure_bind]
  exact heta

/-- Constant-head lookup errors propagate before either dispatcher runs. -/
theorem tryIotaCtorOrStructEta_lookupError
    {methods : Methods .anon} {s sf : TcState .anon}
    {recId ctorId : KId .anon} {recr : IotaInfo .anon}
    {recUs ctorUs : Array (KUniv .anon)}
    {spine ctorArgs : Array (KExpr .anon)}
    {majorWhnf : KExpr .anon} {ctorInfo : ExprInfo .anon}
    {transient : Bool} {err : TcError .anon}
    (hspine : majorWhnf.collectSpine =
      (.const ctorId ctorUs ctorInfo, ctorArgs))
    (hlookup : TcM.tryGetConst ctorId s = .error err sf) :
    (tryIotaCtorOrStructEta recId recr recUs spine majorWhnf transient).run
      methods s = .error err sf := by
  unfold tryIotaCtorOrStructEta
  rw [hspine, ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.tryGetConst ctorId) _ s = _
  unfold EStateM.bind
  rw [hlookup]

/-- A constructor metadata hit forwards either success or error from ordinary
iota, and never enters struct eta. -/
theorem tryIotaCtorOrStructEta_constructor
    {methods : Methods .anon} {s sLookup : TcState .anon}
    {recId ctorId : KId .anon} {recr : IotaInfo .anon}
    {recUs ctorUs : Array (KUniv .anon)}
    {spine ctorArgs : Array (KExpr .anon)}
    {majorWhnf : KExpr .anon} {ctorInfo : ExprInfo .anon}
    {entry : KConst .anon} {transient : Bool} {cidx ctorFields : Nat}
    {outcome : EStateM.Result (TcError .anon) (TcState .anon)
      (Option (KExpr .anon))}
    (hspine : majorWhnf.collectSpine =
      (.const ctorId ctorUs ctorInfo, ctorArgs))
    (hlookup : TcM.tryGetConst ctorId s = .ok (some entry) sLookup)
    (hinfo : entry.iotaCtorInfo? = some (cidx, ctorFields))
    (hdispatch :
      (tryApplyIotaCtor recr recUs spine ctorArgs cidx ctorFields transient).run
        methods sLookup = outcome) :
    (tryIotaCtorOrStructEta recId recr recUs spine majorWhnf transient).run
      methods s = outcome := by
  unfold tryIotaCtorOrStructEta
  rw [hspine, ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.tryGetConst ctorId) _ s = _
  unfold EStateM.bind
  rw [hlookup]
  simp only [hinfo, pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run
      (tryApplyIotaCtor recr recUs spine ctorArgs cidx ctorFields transient)
      methods) _ sLookup = _
  unfold EStateM.bind
  rw [hdispatch]
  cases outcome <;> rfl

end RecM

end Ix.Tc
