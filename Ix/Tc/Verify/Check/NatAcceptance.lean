import Ix.Tc.Verify.NatFixture
import Ix.Tc.Verify.Check.PublicStandalone

/-!
# Concrete standalone-check acceptance over the ambient Nat world

This fixture connects the exact production `TcM.checkConst` execution to the
semantic pending-declaration boundary.  A valid axiom succeeds and promotes
the ghost world; an intrinsically malformed axiom is then rejected with exact
public rollback.  Both verdicts use the same concrete catalog entries and
checker states as their semantic witnesses.

The valid path deliberately preloads one semantically justified inference
cache entry.  This makes the production execution reducible in Lean without
evaluating the Blake3 FFI and keeps the witness about checker control flow,
cache use, reset, validation, acceptance, and rollback rather than about a
mock implementation.
-/

namespace Ix.Tc.AmbientNat

def acceptanceEnv : KEnv .anon :=
  { loadedEnv with inferCache :=
      loadedEnv.inferCache.insert (natRef.addr, emptyCtxAddr) natType }

def initialState : TcState .anon :=
  { state Primitives.ofAnonAddrs with
    env := acceptanceEnv
    fuelBudget := 0
    recFuel := 0 }

def resetState : TcState .anon :=
  { initialState with
    ctx := #[]
    letVals := #[]
    numLetBindings := 0
    ctxId := emptyCtxAddr
    ctxIdStack := #[]
    equivManager := {}
    inferOnly := false
    inNativeReduce := false
    cheapRecursionDepth := 0
    eagerReduce := false
    defEqDepth := 0
    defEqPeak := 0
    dispatchDepth := 0
    recFuel := initialState.fuelBudget
    ctxAddrCache := {}
    lctx := {} }

/-- Finite syntax used by the concrete public-check lifecycle.  It contains
the checked Nat reference, the cached inferred sort, and both universe
subterms needed to interpret that sort. -/
def acceptanceSupport : RunSupport where
  expr := fun source => source = natRef ∨ source = natType
  exprFinite :=
    FiniteSupport.union (FiniteSupport.singleton natRef)
      (FiniteSupport.singleton natType)
  univ := fun level => level = zeroLevel ∨ level = oneLevel
  univFinite :=
    FiniteSupport.union (FiniteSupport.singleton zeroLevel)
      (FiniteSupport.singleton oneLevel)

/-- Cache semantics used only to state the six-field contract for the exact
finite table selected by this fixture. -/
def acceptanceKeys : WhnfContextKeys := WhnfContextKeys.closed 0

def acceptanceSemantics : CacheSemantics :=
  kernelCacheSemantics acceptanceKeys RawProjRel.none

theorem selectedMethods :
    methodsN initialState.recFuel.toNat = (methodsOut : Methods .anon) := by
  rfl

theorem selectedMethods_wf :
    Methods.WFAt .noAccel acceptanceSemantics RawProjRel.none worldNat
      acceptanceSupport 0 (methodsN initialState.recFuel.toNat) := by
  rw [selectedMethods]
  exact Methods.methodsOut_wfAt .noAccel acceptanceSemantics RawProjRel.none
    worldNat acceptanceSupport 0

theorem acceptanceSupport_collisionFree : acceptanceSupport.CollisionFree := by
  constructor
  · intro left hleft right hright haddr
    rcases hleft with rfl | rfl <;> rcases hright with rfl | rfl
    · rfl
    · exact False.elim (zeroAddress_ne_natAddress (by
        simpa [natRef, natType, info] using haddr))
    · exact False.elim (zeroAddress_ne_natAddress (by
        simpa [natRef, natType, info] using haddr.symm))
    · rfl
  · intro left hleft right hright haddr
    rcases hleft with rfl | rfl <;> rcases hright with rfl | rfl
    · rfl
    · exact False.elim (zeroAddress_ne_natAddress (by
        simpa [zeroLevel, oneLevel] using haddr.symm))
    · exact False.elim (zeroAddress_ne_natAddress (by
        simpa [zeroLevel, oneLevel] using haddr))
    · rfl

theorem initial_reset : TcM.reset initialState = .ok () resetState := by
  rfl

theorem initialState_wf :
    TcStateWF RawProjRel.none initialState worldNat := by
  refine ⟨trustedCatalogRelNat, ?_, ?_⟩
  · intro id concrete hloaded
    apply loadedAgrees
    simpa [KEnv.get?, initialState, acceptanceEnv] using hloaded
  · exact InternTable.WF.empty

theorem resetState_wf :
    TcStateWF RawProjRel.none resetState worldGood := by
  refine ⟨trustedCatalogRelGood, ?_, ?_⟩
  · intro id concrete hloaded
    apply loadedAgrees
    simpa [KEnv.get?, resetState, initialState, acceptanceEnv] using hloaded
  · exact InternTable.WF.empty

theorem goodPromotion :
    Promotes worldNat (fun target => target = goodId) worldGood := by
  refine ⟨nat_le_good, ?_⟩
  intro target htarget
  subst target
  exact good_trusted

theorem loadedEnv_good : loadedEnv.get? goodId = some goodConcrete := by
  simp only [loadedEnv, KEnv.get?, KEnv.insert,
    Std.HashMap.getElem?_insert]
  split
  · next h => exact False.elim (badId_ne_goodId (eq_of_beq h))
  · rfl

theorem reset_loaded_good :
    resetState.env.get? goodId = some goodConcrete := by
  simpa [resetState, initialState, acceptanceEnv] using loadedEnv_good

theorem reset_loaded_nat :
    resetState.env.get? natId = some natConcrete := by
  change loadedEnv.get? natId = some natConcrete
  exact loadedEnv_nat

theorem reset_try_get_good :
    TcM.tryGetConst goodId resetState =
      .ok (some goodConcrete) resetState := by
  unfold TcM.tryGetConst
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ resetState = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) resetState =
    .ok resetState resetState from rfl]
  simp only
  rw [reset_loaded_good]
  rfl

theorem reset_get_good :
    TcM.getConst goodId resetState = .ok goodConcrete resetState := by
  unfold TcM.getConst
  change EStateM.bind (TcM.tryGetConst goodId) _ resetState = _
  unfold EStateM.bind
  rw [reset_try_get_good]
  rfl

theorem reset_try_get_nat :
    TcM.tryGetConst natId resetState =
      .ok (some natConcrete) resetState := by
  unfold TcM.tryGetConst
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ resetState = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) resetState =
    .ok resetState resetState from rfl]
  simp only
  rw [reset_loaded_nat]
  rfl

theorem reset_get_nat :
    TcM.getConst natId resetState = .ok natConcrete resetState := by
  unfold TcM.getConst
  change EStateM.bind (TcM.tryGetConst natId) _ resetState = _
  unfold EStateM.bind
  rw [reset_try_get_nat]
  rfl

theorem reset_infer_key :
    TcM.inferKey natRef resetState =
      .ok (natRef.addr, emptyCtxAddr) resetState := by
  simpa [TcM.inferKey_eq_whnfKey] using
    (TcM.whnfKey_closed (s := resetState) (source := natRef) (by rfl))

theorem reset_infer_hit :
    resetState.env.inferCache[(natRef.addr, emptyCtxAddr)]? =
      some natType := by
  simp [resetState, initialState, acceptanceEnv]

theorem reset_infer :
    (RecM.infer natRef).run methodsOut resetState =
      .ok natType resetState := by
  exact RecM.inferWith_fullHit reset_infer_key reset_infer_hit

theorem oneLevel_wf : oneLevel.toVLevel.WF 0 := by
  change True
  trivial

theorem natType_translation :
    TrKExpr worldNat.venv 0 worldNat.nameOf RawProjRel.none [] natType
      (.sort oneLevel.toVLevel) := by
  refine ⟨.sort oneLevel.toVLevel, ?_, ?_⟩
  · simpa [natType] using
      (TrKExprS.sort (env := worldNat.venv) (nameOf := worldNat.nameOf)
        (trProj := RawProjRel.none) (Δ := []) oneLevel_wf)
  · exact Lean4Lean.VEnv.IsDefEqU.refl
      ⟨_, Lean4Lean.VEnv.HasType.sort oneLevel_wf⟩

theorem natReference_type :
    worldNat.venv.HasType 0 [] (.const natName [])
      (.sort oneLevel.toVLevel) := by
  simpa [worldNat, natConstant, oneLevel, zeroLevel] using
    (Lean4Lean.VEnv.HasType.const (env := natEnv) (U := 0) (Γ := [])
      (ci := natConstant) (ls := []) natEnv_nat (by simp) rfl)

theorem oneLevel_view :
    SortView worldNat acceptanceSupport 0 [] (.sort oneLevel.toVLevel) oneLevel := by
  refine ⟨?_, ?_, oneLevel_wf, ?_⟩
  · simp [oneLevel, zeroLevel, KUniv.size, UInt64.size]
  · intro level hlevel
    cases hlevel with
    | refl => exact Or.inr rfl
    | succ hchild =>
        cases hchild
        exact Or.inl rfl
  · exact Lean4Lean.VEnv.IsDefEqU.refl
      ⟨_, Lean4Lean.VEnv.HasType.sort oneLevel_wf⟩

theorem goodTypeEvidence :
    TypeCheckEvidence RawProjRel.none worldNat acceptanceSupport 0 []
      goodConstant.type := by
  refine ⟨natType, .sort oneLevel.toVLevel, natType_translation, ?_,
    oneLevel, oneLevel_view⟩
  simpa [goodConstant] using natReference_type

theorem goodCheckEvidence :
    StandaloneCheckEvidence RawProjRel.none worldNat acceptanceSupport goodDecl := by
  exact .axiom goodTypeEvidence

theorem goodIngress :
    PreDeclRel worldNat.venv worldNat.nameOf RawProjRel.none goodId
      goodConcrete goodDecl := by
  unfold goodConcrete goodDecl goodConstant
  apply PreDeclRel.axiom
  · exact nameOf_good
  · exact PreTrKExprS.const nameOf_nat natEnv_nat (by simp) rfl

theorem goodCheckResult :
    StandaloneCheckResult RawProjRel.none worldNat acceptanceSupport goodId
      goodConcrete goodDecl :=
  ⟨goodIngress, goodCheckEvidence⟩

theorem reset_validation :
    (RecM.validateConstWellScoped goodConcrete).run methodsOut resetState =
      .ok () resetState := by
  unfold goodConcrete RecM.validateConstWellScoped
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.validateExprWellScoped natRef 0 0).run methodsOut) _
      resetState = _
  have hvalidate :
      (RecM.validateExprWellScoped natRef 0 0).run methodsOut resetState =
        .ok () resetState := by
    unfold RecM.validateExprWellScoped
    rw [RecM.validateExprWellScoped.go.eq_def]
    simp only [Std.HashSet.contains_empty, Bool.false_eq_true, if_false,
      natRef]
    rw [ReaderT.run_bind]
    change EStateM.bind (TcM.getConst natId) _ resetState = _
    unfold EStateM.bind
    rw [reset_get_nat]
    simp [natConcrete]
    change (pure () : RecM .anon Unit).run methodsOut resetState = _
    rfl
  unfold EStateM.bind
  rw [hvalidate]
  rfl

theorem natRef_validationCoverage :
    natRef.ValidationCoverage acceptanceSupport := by
  constructor
  · intro candidate hcandidate
    cases hcandidate
    exact Or.inl rfl
  · intro level hlevel
    unfold natRef at hlevel
    cases hlevel with
    | const hmem _ => simp at hmem

theorem goodValidationResources :
    StandaloneValidationResources acceptanceSupport goodConcrete := by
  exact .axiom natRef_validationCoverage (by
    change 1 < UInt64.size
    decide)

theorem goodScope : StandaloneScope goodConcrete :=
  RecM.validateConstWellScoped_sound goodValidationResources
    acceptanceSupport_collisionFree reset_validation

theorem reset_member :
    (RecM.checkConstMember goodId goodConcrete).run methodsOut resetState =
      .ok () resetState := by
  unfold RecM.checkConstMember
  simp only [goodConcrete, Mode.F.hasDups, Bool.false_eq_true, if_false,
    ReaderT.run_bind]
  change EStateM.bind
    ((RecM.validateConstWellScoped goodConcrete).run methodsOut) _
      resetState = _
  unfold EStateM.bind
  rw [reset_validation]
  change EStateM.bind ((RecM.infer natRef).run methodsOut) _
    resetState = _
  unfold EStateM.bind
  rw [reset_infer]
  simp [RecM.ensureSortDirect, natType]

theorem initial_fresh_member :
    (RecM.checkConstMemberFresh goodId).run methodsOut initialState =
      .ok () resetState := by
  unfold RecM.checkConstMemberFresh
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind TcM.reset _ initialState = _
  unfold EStateM.bind
  rw [initial_reset]
  change EStateM.bind (TcM.getConst goodId) _ resetState = _
  unfold EStateM.bind
  rw [reset_get_good]
  exact reset_member

theorem initial_loaded_good :
    initialState.env.get? goodId = some goodConcrete := by
  simpa [initialState, acceptanceEnv] using loadedEnv_good

theorem initial_try_get_good :
    TcM.tryGetConst goodId initialState = .ok (some goodConcrete) initialState := by
  unfold TcM.tryGetConst
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ initialState = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) initialState =
    .ok initialState initialState from rfl]
  simp only
  rw [initial_loaded_good]
  rfl

theorem initial_get_good :
    TcM.getConst goodId initialState = .ok goodConcrete initialState := by
  unfold TcM.getConst
  change EStateM.bind (TcM.tryGetConst goodId) _ initialState = _
  unfold EStateM.bind
  rw [initial_try_get_good]
  rfl

theorem initial_route_good :
    (RecM.coordinatedBlockFor goodConcrete).run methodsOut initialState =
      .ok none initialState := by
  rfl

theorem initial_good_body :
    (RecM.checkConst goodId).run methodsOut initialState =
      .ok () resetState := by
  unfold RecM.checkConst
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.getConst goodId) _ initialState = _
  unfold EStateM.bind
  rw [initial_get_good]
  change EStateM.bind
    ((RecM.coordinatedBlockFor goodConcrete).run methodsOut) _ initialState = _
  unfold EStateM.bind
  rw [initial_route_good]
  exact initial_fresh_member

theorem initial_good_public :
    TcM.checkConst goodId initialState = .ok () resetState := by
  apply TcM.isolateCheckErrors_ok
  simpa [TcM.runRec, initialState] using initial_good_body

theorem loadedEnv_bad :
    loadedEnv.get? IllTypedPending.targetId =
      some IllTypedPending.concrete := by
  simp [loadedEnv, KEnv.get?, KEnv.insert]

theorem reset_loaded_bad :
    resetState.env.get? IllTypedPending.targetId =
      some IllTypedPending.concrete := by
  change loadedEnv.get? IllTypedPending.targetId =
    some IllTypedPending.concrete
  exact loadedEnv_bad

theorem reset_try_get_bad :
    TcM.tryGetConst IllTypedPending.targetId resetState =
      .ok (some IllTypedPending.concrete) resetState := by
  unfold TcM.tryGetConst
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ resetState = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) resetState =
    .ok resetState resetState from rfl]
  simp only
  rw [reset_loaded_bad]
  rfl

theorem reset_get_bad :
    TcM.getConst IllTypedPending.targetId resetState =
      .ok IllTypedPending.concrete resetState := by
  unfold TcM.getConst
  change EStateM.bind (TcM.tryGetConst IllTypedPending.targetId) _
    resetState = _
  unfold EStateM.bind
  rw [reset_try_get_bad]
  rfl

theorem reset_bad_validation :
    (RecM.validateConstWellScoped IllTypedPending.concrete).run methodsOut
      resetState =
        .error (.univParamOutOfRange 0 0) resetState := by
  unfold IllTypedPending.concrete RecM.validateConstWellScoped
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.validateExprWellScoped IllTypedPending.badType 0 0).run methodsOut)
      _ resetState = _
  have hvalidate :
      (RecM.validateExprWellScoped IllTypedPending.badType 0 0).run
          methodsOut resetState =
        .error (.univParamOutOfRange 0 0) resetState := by
    unfold RecM.validateExprWellScoped
    rw [RecM.validateExprWellScoped.go.eq_def]
    simp only [Std.HashSet.contains_empty, Bool.false_eq_true, if_false,
      IllTypedPending.badType]
    rw [ReaderT.run_bind]
    change EStateM.bind
      ((RecM.validateUnivParamsSeen IllTypedPending.badLevel 0 ∅).run
        methodsOut) _ resetState = _
    have huniv :
        (RecM.validateUnivParamsSeen IllTypedPending.badLevel 0 ∅).run
            methodsOut resetState =
          .error (.univParamOutOfRange 0 0) resetState := by
      unfold RecM.validateUnivParamsSeen
      rw [RecM.validateUnivParamsSeen.go.eq_def]
      simp [IllTypedPending.badLevel]
      rfl
    unfold EStateM.bind
    rw [huniv]
  unfold EStateM.bind
  rw [hvalidate]

theorem reset_bad_member :
    (RecM.checkConstMember IllTypedPending.targetId
        IllTypedPending.concrete).run methodsOut resetState =
      .error (.univParamOutOfRange 0 0) resetState := by
  unfold RecM.checkConstMember
  simp only [IllTypedPending.concrete, Mode.F.hasDups,
    Bool.false_eq_true, if_false, ReaderT.run_bind]
  change EStateM.bind
    ((RecM.validateConstWellScoped IllTypedPending.concrete).run methodsOut) _
      resetState = _
  unfold EStateM.bind
  rw [reset_bad_validation]

theorem reset_reset : TcM.reset resetState = .ok () resetState := by
  rfl

theorem reset_bad_fresh :
    (RecM.checkConstMemberFresh IllTypedPending.targetId).run methodsOut
      resetState =
        .error (.univParamOutOfRange 0 0) resetState := by
  unfold RecM.checkConstMemberFresh
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind TcM.reset _ resetState = _
  unfold EStateM.bind
  rw [reset_reset]
  change EStateM.bind (TcM.getConst IllTypedPending.targetId) _
    resetState = _
  unfold EStateM.bind
  rw [reset_get_bad]
  exact reset_bad_member

theorem reset_bad_route :
    (RecM.coordinatedBlockFor IllTypedPending.concrete).run methodsOut
      resetState = .ok none resetState := by
  rfl

theorem reset_bad_body :
    (RecM.checkConst IllTypedPending.targetId).run methodsOut resetState =
      .error (.univParamOutOfRange 0 0) resetState := by
  unfold RecM.checkConst
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.getConst IllTypedPending.targetId) _
    resetState = _
  unfold EStateM.bind
  rw [reset_get_bad]
  change EStateM.bind
    ((RecM.coordinatedBlockFor IllTypedPending.concrete).run methodsOut) _
      resetState = _
  unfold EStateM.bind
  rw [reset_bad_route]
  exact reset_bad_fresh

theorem reset_bad_public :
    TcM.checkConst IllTypedPending.targetId resetState =
      .error (.univParamOutOfRange 0 0) resetState := by
  have hbody : TcM.runRec (RecM.checkConst IllTypedPending.targetId)
      resetState =
        .error (.univParamOutOfRange 0 0) resetState := by
    simpa [TcM.runRec, resetState] using reset_bad_body
  have hrestore :
      resetState.restoreCheckCachesOnError resetState = resetState := by
    simp [TcState.restoreCheckCachesOnError,
      KEnv.restoreCheckCachesOnError,
      KEnv.restoreBlockCheckResultsOnError,
      resetState, initialState, acceptanceEnv, loadedEnv, KEnv.insert]
    rw [Std.HashMap.fold_eq_foldl_toList]
    rw [Std.HashMap.toList_empty]
    rfl
  simpa [TcM.checkConst, hrestore] using
    (TcM.isolateCheckErrors_error hbody)

theorem goodAccepted : StandaloneAccepted worldNat.venv goodDecl :=
  goodCheckResult.accepted

/-- One theorem joins the semantic pending boundary, finite validator and
collision resources, exact production execution, ghost promotion, and an
intrinsically invalid follow-up rejection.  The invalid run returns the same
state, so the theorem also exposes the public rollback result. -/
structure PublicCheckLifecycle : Prop where
  supportCollision : acceptanceSupport.CollisionFree
  methodSelection :
    methodsN initialState.recFuel.toNat = (methodsOut : Methods .anon)
  methodContract :
    Methods.WFAt .noAccel acceptanceSemantics RawProjRel.none worldNat
      acceptanceSupport 0 (methodsN initialState.recFuel.toNat)
  validationResources :
    StandaloneValidationResources acceptanceSupport goodConcrete
  initialWF : TcStateWF RawProjRel.none initialState worldNat
  validPending : PendingDecl RawProjRel.none worldNat goodId goodDecl
  validValidation :
    (RecM.validateConstWellScoped goodConcrete).run methodsOut resetState =
      .ok () resetState
  semanticCacheEntry :
    resetState.env.inferCache[(natRef.addr, emptyCtxAddr)]? = some natType
  inferenceExecution :
    (RecM.infer natRef).run methodsOut resetState = .ok natType resetState
  validResult : StandaloneCheckResult RawProjRel.none worldNat acceptanceSupport
    goodId goodConcrete goodDecl
  validExecution : TcM.checkConst goodId initialState = .ok () resetState
  promotion : Promotes worldNat (fun target => target = goodId) worldGood
  promotedWF : TcStateWF RawProjRel.none resetState worldGood
  trustedResult : TrustedDecl RawProjRel.none worldGood goodId goodDecl
  invalidPending : PendingDecl RawProjRel.none worldGood
    IllTypedPending.targetId IllTypedPending.theoryDecl
  invalidSemantic :
    ¬∃ env', Lean4Lean.VDecl.WF worldGood.venv
      IllTypedPending.theoryDecl env'
  invalidExecution :
    TcM.checkConst IllTypedPending.targetId resetState =
      .error (.univParamOutOfRange 0 0) resetState

theorem publicCheckLifecycle : PublicCheckLifecycle where
  supportCollision := acceptanceSupport_collisionFree
  methodSelection := selectedMethods
  methodContract := selectedMethods_wf
  validationResources := goodValidationResources
  initialWF := initialState_wf
  validPending := goodPending
  validValidation := reset_validation
  semanticCacheEntry := reset_infer_hit
  inferenceExecution := reset_infer
  validResult := goodCheckResult
  validExecution := initial_good_public
  promotion := goodPromotion
  promotedWF := resetState_wf
  trustedResult := goodTrustedDecl
  invalidPending := badPending
  invalidSemantic := badDecl_not_wf
  invalidExecution := reset_bad_public

def goodSucceeded : Bool :=
  match TcM.checkConst goodId initialState with
  | .ok () _ => true
  | .error _ _ => false

example : goodSucceeded = true := by
  simp [goodSucceeded, initial_good_public]

end Ix.Tc.AmbientNat
