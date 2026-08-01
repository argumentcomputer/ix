import Ix.Tc.Verify.Check.PositiveFuelSort
import Ix.Tc.Verify.Check.PublicStandalone

/-!
# Executed positive-fuel checker over a finite suffix model

This fixture checks one eagerly loaded, pending sort axiom with recursion fuel
one.  The production suffix model is the constructive singleton model for
closed eager states; the method schedule admits exactly the one sort
inference performed by the checker.
-/

namespace Ix.Tc.PositiveFuelSort.Checker

open PositiveFuelSort

def targetAddress : Address :=
  ⟨⟨Array.replicate 32 (37 : UInt8)⟩⟩

def targetId : KId .anon := ⟨targetAddress, ()⟩
def targetName : Lean.Name := `Ix.Tc.Verify.positiveFuelSortAxiom

def catalog : Catalog := fun id =>
  if id == targetId then some concreteAxiom else none

@[simp] theorem catalog_target : catalog targetId = some concreteAxiom := by
  simp [catalog]

def world : VerifyWorld where
  catalog := catalog
  trusted := fun _ => False
  venv := .empty
  nameOf := fun addr =>
    if addr == targetAddress then some targetName else none
  venvWF := ⟨[], .empty⟩
  trustedCatalogued := fun {_} h => False.elim h

@[simp] theorem world_nameOf_target :
    world.nameOf targetId.addr = some targetName := by
  simp [world, targetId]

def declaration : Lean4Lean.VDecl :=
  .axiom { name := targetName, uvars := 0, type := .sort .zero }

theorem rawDeclaration :
    RawDeclRel world.venv world.nameOf RawProjRel.none targetId
      concreteAxiom declaration := by
  apply RawDeclRel.axiom world_nameOf_target
  exact .sort

theorem pending :
    PendingDecl RawProjRel.none world targetId declaration := by
  refine ⟨concreteAxiom, catalog_target, rawDeclaration, ?_, ?_, ?_⟩
  · exact fun h => h
  · intro id href
    change source.References id at href
    obtain ⟨u, info, hsource⟩ := supported_is_sort source_supported
    rw [hsource] at href
    simp [KExpr.References] at href
  · intro name hname
    change Lean4Lean.VEnv.empty.constants name = none
    rfl

def env : KEnv .anon :=
  ({} : KEnv .anon).insert targetId concreteAxiom

/-- Positive recursion fuel is preserved by the per-constant reset because
the fixture's fuel budget is also one. -/
def initialState : TcState .anon :=
  { TcState.ofEnvAnon env with
    noAccel := true
    recFuel := 1
    fuelBudget := 1 }

theorem initialState_closed : ClosedContextState initialState := by
  constructor <;> rfl

theorem initialState_reset :
    TcM.reset initialState = .ok () initialState := by
  rfl

theorem trustedCatalog : TrustedCatalogRel RawProjRel.none world :=
  TrustedCatalogLog.empty

theorem loadedAgreement : LoadedAgrees world.catalog env := by
  apply LoadedAgrees.insert (LoadedAgrees.empty world.catalog)
  exact catalog_target

theorem initialState_core :
    TcStateWF RawProjRel.none initialState world :=
  ⟨trustedCatalog, loadedAgreement, InternTable.WF.empty⟩

def model : ScopedKernelSuffixModel RawProjRel.none world :=
  ClosedContextDigest.model RawProjRel.none world 0

theorem initialState_kernel :
    KernelStateWF (kernelCacheSemantics model.keys RawProjRel.none)
      RawProjRel.none world support initialState := by
  apply KernelStateWF.of_no_cache_entries initialState_core
  · constructor
    · intro candidate hcandidate
      obtain ⟨addr, haddr⟩ := hcandidate
      simp [initialState, env, KEnv.insert, TcState.ofEnvAnon] at haddr
    · intro candidate hcandidate
      obtain ⟨addr, haddr⟩ := hcandidate
      simp [initialState, env, KEnv.insert, TcState.ofEnvAnon] at haddr
  · rfl
  · intro entry hentry
    cases hentry <;>
      simp [initialState, env, KEnv.insert, TcState.ofEnvAnon] at *

theorem initialState_baseInv :
    WhnfStateInv .noAccel
      (kernelCacheSemantics model.keys RawProjRel.none)
      RawProjRel.none world support model.keys.uvars [] initialState := by
  refine ⟨initialState_kernel, ?_, rfl,
    Primitives.ofAnonAddrs_canonical⟩
  apply CtxRecon.empty <;> rfl

theorem initialState_inv :
    ScopedWhnfStateInv model .noAccel
      (kernelCacheSemantics model.keys RawProjRel.none)
      support [] initialState :=
  ⟨initialState_baseInv,
    ClosedContextDigest.model_stateInScope initialState_closed⟩

theorem sourceTranslation :
    TrKExprS world.venv model.keys.uvars world.nameOf RawProjRel.none []
      source (.sort .zero) := by
  unfold source sourceUniv
  exact .sort (by trivial)

def theory : WhnfTheory RawProjRel.none world model.keys.uvars where
  literalWF := by
    intro literal hliteral
    cases literal <;>
      simp [world, Lean4Lean.VEnv.ContainsLits,
        Lean4Lean.VEnv.contains, Lean4Lean.VEnv.empty] at hliteral
  projections := RawProjRel.none_ok world.venv model.keys.uvars

theorem trustedReferences : RecM.TrustedReferences world support := by
  intro candidate id hcandidate href
  obtain ⟨u, info, hsort⟩ := supported_is_sort hcandidate
  subst candidate
  simp [KExpr.References] at href

theorem schedule (separation : AddressSeparation) :
    Methods.ScopedCallScheduleAt model .noAccel
      (kernelCacheSemantics model.keys RawProjRel.none) support
      (Methods.ScopedSortSchedule.calls source) 2 :=
  Methods.ScopedSortSchedule.two (support_collisionFree separation)
    source_supported result_supported theory trustedReferences

theorem methodContract (separation : AddressSeparation) :
    Methods.ScopedWFAtOn model .noAccel
      (kernelCacheSemantics model.keys RawProjRel.none) support
      (.singletonInfer source)
      (Methods.next (Ix.Tc.methodsN (m := .anon) 1)) := by
  simpa [Methods.ScopedSortSchedule.calls] using
    (schedule separation).nextSelected

theorem fullInference (separation : AddressSeparation) :
    Methods.ScopedFullInferenceWFAtOn model support
      (.singletonInfer source)
      (Methods.next (Ix.Tc.methodsN (m := .anon) 1)) :=
  Methods.ScopedFullInferenceWFAtOn.ofSingletonSort
    (methodContract separation)
    (Methods.next_preservesInferOnly _
      (Methods.methodsN_concrete_preservesInferOnly 1))

def pipelines (separation : AddressSeparation) :
    ScopedStandalonePipelineResources model support
      (.singletonInfer source) (Ix.Tc.methodsN (m := .anon) 1) :=
  ScopedStandalonePipelineResources.singletonSortAxiom
    (fullInference separation) sortResources supported_is_sort

theorem pipelines_cover (separation : AddressSeparation) :
    (pipelines separation).Covers concreteAxiom :=
  .axiom rfl

theorem validationCoverage : source.ValidationCoverage support := by
  constructor
  · intro candidate hcandidate
    cases hcandidate
    exact source_supported
  · intro level hlevel
    cases hlevel with
    | sort hreach =>
        cases hreach
        exact Or.inl rfl

theorem validationResources :
    StandaloneValidationResources support concreteAxiom :=
  .axiom validationCoverage (by
    change 1 < UInt64.size
    decide)

/-! ## Exact production execution -/

def methods : Methods .anon := Ix.Tc.methodsN 1

theorem initial_loaded :
    initialState.env.get? targetId = some concreteAxiom := by
  simp [initialState, env, KEnv.get?, KEnv.insert, TcState.ofEnvAnon]

theorem initial_tryGet :
    TcM.tryGetConst targetId initialState =
      .ok (some concreteAxiom) initialState := by
  unfold TcM.tryGetConst
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ initialState = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) initialState =
    .ok initialState initialState from rfl]
  simp only
  rw [initial_loaded]
  rfl

theorem initial_get :
    TcM.getConst targetId initialState =
      .ok concreteAxiom initialState := by
  unfold TcM.getConst
  change EStateM.bind (TcM.tryGetConst targetId) _ initialState = _
  unfold EStateM.bind
  rw [initial_tryGet]
  rfl

theorem validation_execution :
    (RecM.validateConstWellScoped concreteAxiom).run methods initialState =
      .ok () initialState := by
  unfold concreteAxiom RecM.validateConstWellScoped
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.validateExprWellScoped source 0 0).run methods) _ initialState = _
  have hvalidate :
      (RecM.validateExprWellScoped source 0 0).run methods initialState =
        .ok () initialState := by
    unfold RecM.validateExprWellScoped
    rw [RecM.validateExprWellScoped.go.eq_def]
    simp only [Std.HashSet.contains_empty, Bool.false_eq_true, if_false]
    have hsource : source = .sort sourceUniv source.info := by rfl
    rw [hsource]
    rw [ReaderT.run_bind]
    change EStateM.bind
      ((RecM.validateUnivParamsSeen sourceUniv 0 ∅).run methods) _
        initialState = _
    let seen : Std.HashSet Address :=
      ({} : Std.HashSet Address).insert sourceUniv.addr
    have huniv :
        (RecM.validateUnivParamsSeen sourceUniv 0 ∅).run methods initialState =
          .ok seen initialState := by
      unfold sourceUniv KUniv.mkZero RecM.validateUnivParamsSeen
      rw [RecM.validateUnivParamsSeen.go.eq_def]
      simp only [Std.HashSet.contains_empty, Bool.false_eq_true, if_false]
      rw [RecM.validateUnivParamsSeen.go.eq_def]
      rfl
    unfold EStateM.bind
    rw [huniv]
    simp only
    rw [RecM.validateExprWellScoped.go.eq_def]
    rfl
  unfold EStateM.bind
  rw [hvalidate]
  rfl

def inferKey : Address × Address := (source.addr, emptyCtxAddr)

theorem initial_inferKey :
    TcM.inferKey source initialState = .ok inferKey initialState := by
  simpa [inferKey, TcM.inferKey_eq_whnfKey] using
    (TcM.whnfKey_closed (s := initialState) (source := source) (by rfl))

theorem initial_inferMiss :
    initialState.env.inferCache[inferKey]? = none := by
  simp [initialState, env, inferKey, KEnv.insert, TcState.ofEnvAnon]

theorem publicInference_wf (separation : AddressSeparation) :
    TcM.WF
      (ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys RawProjRel.none) support [])
      initialState (TcM.infer source)
      (fun inferred _ => support inferred ∧
        InferPost RawProjRel.none world model.keys.uvars []
          (.sort .zero) inferred) := by
  simpa [source, result, resultUniv] using
    (TcM.infer.sort_scoped_wf_fuel_one
      (initial := initialState) (model := model)
      (u := sourceUniv) (info := source.info)
      (Delta := []) (sourceV := .sort .zero)
      (by rfl) (support_collisionFree separation) source_supported
      result_supported theory trustedReferences sourceTranslation)

/-- Exact operational witness for the positive-fuel inference used by the
axiom checker.  It interns the successor sort and records the cache entry,
so this is not a pre-seeded-cache witness.  This execution fact deliberately
does not depend on the semantic typing postcondition. -/
theorem inference_run (separation : AddressSeparation) :
    ∃ after,
      (RecM.infer source).run methods initialState = .ok result after := by
  obtain ⟨afterIntern, hintern, _hbaseAfter, _hframe⟩ :=
    TcM.intern_whnf_eval (support_collisionFree separation)
      result_supported initialState_baseInv
  have hbody :
      (RecM.inferUncached RecM.inferCall false source).run methods
          initialState = .ok result afterIntern := by
    simpa [methods, source, result, resultUniv] using hintern
  have hshell := RecM.inferWith_fullMiss_success
    (inferRec := RecM.inferCall) (methods := methods)
    (source := source) (ty := result) (key := inferKey)
    (s := initialState) (sKey := initialState) (sBody := afterIntern)
    (by rfl) initial_inferKey initial_inferMiss hbody
  let after : TcState .anon :=
    { afterIntern with env := { afterIntern.env with
        inferCache := afterIntern.env.inferCache.insert inferKey result } }
  have hrun :
      (RecM.infer source).run methods initialState = .ok result after := by
    simpa [RecM.infer, after] using hshell
  exact ⟨after, hrun⟩

/-- Exact positive-fuel inference together with its verified semantic
postcondition.  The execution component is factored through `inference_run`
so request-trace certificates need not inherit the typing proof's axioms. -/
theorem inference_execution (separation : AddressSeparation) :
    ∃ after,
      (RecM.infer source).run methods initialState = .ok result after ∧
      ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys RawProjRel.none) support [] after ∧
      support result ∧
      InferPost RawProjRel.none world model.keys.uvars []
        (.sort .zero) result := by
  obtain ⟨after, hrun⟩ := inference_run separation
  have hpublic : TcM.infer source initialState = .ok result after := by
    simpa [TcM.infer, TcM.runRec, initialState, methods] using hrun
  have hverified := (publicInference_wf separation) initialState_inv
  rw [hpublic] at hverified
  exact ⟨after, hrun, hverified.1, hverified.2⟩

theorem member_execution (separation : AddressSeparation) :
    ∃ after,
      (RecM.checkConstMember targetId concreteAxiom).run methods initialState =
        .ok () after ∧
      ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys RawProjRel.none) support [] after := by
  obtain ⟨after, hinfer, hafter, _⟩ := inference_execution separation
  have hrun :
      (RecM.checkConstMember targetId concreteAxiom).run methods initialState =
        .ok () after := by
    unfold RecM.checkConstMember
    simp only [concreteAxiom, Mode.F.hasDups, Bool.false_eq_true, if_false,
      ReaderT.run_bind]
    change EStateM.bind
      ((RecM.validateConstWellScoped concreteAxiom).run methods) _
        initialState = _
    unfold EStateM.bind
    rw [validation_execution]
    change EStateM.bind ((RecM.infer source).run methods) _ initialState = _
    unfold EStateM.bind
    rw [hinfer]
    have hresult : result = .sort resultUniv result.info := by rfl
    rw [hresult]
    rfl
  exact ⟨after, hrun, hafter⟩

theorem fresh_execution (separation : AddressSeparation) :
    ∃ after,
      (RecM.checkConstMemberFresh targetId).run methods initialState =
        .ok () after ∧
      ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys RawProjRel.none) support [] after := by
  obtain ⟨after, hmember, hafter⟩ := member_execution separation
  have hrun :
      (RecM.checkConstMemberFresh targetId).run methods initialState =
        .ok () after := by
    unfold RecM.checkConstMemberFresh
    simp only [ReaderT.run_bind, ReaderT.run_monadLift]
    change EStateM.bind TcM.reset _ initialState = _
    unfold EStateM.bind
    rw [initialState_reset]
    change EStateM.bind (TcM.getConst targetId) _ initialState = _
    unfold EStateM.bind
    rw [initial_get]
    exact hmember
  exact ⟨after, hrun, hafter⟩

theorem route_execution :
    (RecM.coordinatedBlockFor concreteAxiom).run methods initialState =
      .ok none initialState := by
  rfl

theorem body_execution (separation : AddressSeparation) :
    ∃ after,
      (RecM.checkConst targetId).run methods initialState = .ok () after ∧
      ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys RawProjRel.none) support [] after := by
  obtain ⟨after, hfresh, hafter⟩ := fresh_execution separation
  have hrun :
      (RecM.checkConst targetId).run methods initialState = .ok () after := by
    unfold RecM.checkConst
    simp only [ReaderT.run_bind, ReaderT.run_monadLift]
    change EStateM.bind (TcM.getConst targetId) _ initialState = _
    unfold EStateM.bind
    rw [initial_get]
    change EStateM.bind
      ((RecM.coordinatedBlockFor concreteAxiom).run methods) _ initialState = _
    unfold EStateM.bind
    rw [route_execution]
    exact hfresh
  exact ⟨after, hrun, hafter⟩

theorem public_execution (separation : AddressSeparation) :
    ∃ after,
      TcM.checkConst targetId initialState = .ok () after ∧
      ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys RawProjRel.none) support [] after := by
  obtain ⟨after, hbody, hafter⟩ := body_execution separation
  have hrun : TcM.checkConst targetId initialState = .ok () after := by
    apply TcM.isolateCheckErrors_ok
    simpa [TcM.runRec, initialState, methods] using hbody
  exact ⟨after, hrun, hafter⟩

theorem sourcePreTranslation :
    PreTrKExprS world.venv model.keys.uvars world.nameOf RawProjRel.none []
      source (.sort .zero) := by
  unfold source sourceUniv
  exact .sort (by trivial)

theorem declarationIngress :
    PreDeclRel world.venv world.nameOf RawProjRel.none targetId
      concreteAxiom declaration := by
  apply PreDeclRel.axiom world_nameOf_target
  exact sourcePreTranslation

/-- The executed positive-fuel checker run produces semantic acceptance and
promotes the pending axiom into a trusted world while retaining membership
in the finite suffix-state domain. -/
theorem checked_and_promoted (separation : AddressSeparation) :
    ∃ after,
      TcM.checkConst targetId initialState = .ok () after ∧
      StandaloneCheckResult RawProjRel.none world support targetId
        concreteAxiom declaration ∧
      ∃ world',
        Promotes world (fun target => target = targetId) world' ∧
        WhnfStateInv .noAccel
          (kernelCacheSemantics model.keys RawProjRel.none) RawProjRel.none
          world' support model.keys.uvars [] after ∧
        model.StateInScope after ∧
        TrustedDecl RawProjRel.none world' targetId declaration := by
  obtain ⟨after, hmember, _hafter⟩ := member_execution separation
  have hfresh :
      (RecM.checkConstMemberFresh targetId).run methods initialState =
        .ok () after := by
    unfold RecM.checkConstMemberFresh
    simp only [ReaderT.run_bind, ReaderT.run_monadLift]
    change EStateM.bind TcM.reset _ initialState = _
    unfold EStateM.bind
    rw [initialState_reset]
    change EStateM.bind (TcM.getConst targetId) _ initialState = _
    unfold EStateM.bind
    rw [initial_get]
    exact hmember
  have hbody :
      (RecM.checkConst targetId).run methods initialState = .ok () after := by
    unfold RecM.checkConst
    simp only [ReaderT.run_bind, ReaderT.run_monadLift]
    change EStateM.bind (TcM.getConst targetId) _ initialState = _
    unfold EStateM.bind
    rw [initial_get]
    change EStateM.bind
      ((RecM.coordinatedBlockFor concreteAxiom).run methods) _ initialState = _
    unfold EStateM.bind
    rw [route_execution]
    exact hfresh
  have hevidence := RecM.checkConstMember_scoped_sound
    (pipelines separation) (methodContract separation)
    (Methods.next_preservesInferOnly methods
      (Methods.methodsN_concrete_preservesInferOnly 1))
    declarationIngress (pipelines_cover separation) validationResources
    (by rfl) (by rfl) initialState_inv
    ClosedContextDigest.model_lazyFaultPreserves hmember
  obtain ⟨world', hpromotes, hcore, htrusted⟩ :=
    PendingDecl.promoteOfAccepted hevidence.1.1.1.core pending
      hevidence.2.accepted
  have hpublic : TcM.checkConst targetId initialState = .ok () after := by
    apply TcM.isolateCheckErrors_ok
    simpa [TcM.runRec, initialState, methods] using hbody
  exact ⟨after, hpublic, ⟨declarationIngress, hevidence.2⟩,
    world', hpromotes,
    hevidence.1.1.rebaseWorld hpromotes.1 hcore,
    hevidence.1.2, htrusted⟩

end Ix.Tc.PositiveFuelSort.Checker
