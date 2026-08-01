import Ix.Tc.Verify.Check.ScopedPositiveFuelAxiom

/-!
# Execution certificate for the scoped positive-fuel checker

This module ties the finite request list to the actual public checker
program.  The successful sort inference performs exactly one audited intern
operation; reset, validation, lookup, routing, and cache insertion are
certified silent steps.
-/

namespace Ix.Tc.PositiveFuelSort.Checker

theorem tryGetConst_requests_of_loaded
    {state : TcState .anon} {id : KId .anon} {constant : KConst .anon}
    (hloaded : state.env.get? id = some constant) :
    ExecutionRequests (TcM.tryGetConst id) state [] := by
  unfold TcM.tryGetConst
  apply ExecutionRequests.bind (ExecutionRequests.get state)
  intro current after hget
  cases hget
  rw [hloaded]
  exact .pure state (some constant)

theorem getConst_requests_of_loaded
    {state : TcState .anon} {id : KId .anon} {constant : KConst .anon}
    (hloaded : state.env.get? id = some constant) :
    ExecutionRequests (TcM.getConst id) state [] := by
  unfold TcM.getConst
  apply ExecutionRequests.bind
    (tryGetConst_requests_of_loaded hloaded)
  intro found after hrun
  have hrun' : TcM.tryGetConst id state = .ok (some constant) state := by
    unfold TcM.tryGetConst
    change EStateM.bind (get : TcM .anon (TcState .anon)) _ state = _
    unfold EStateM.bind
    rw [show (get : TcM .anon (TcState .anon)) state =
      .ok state state from rfl]
    simp only
    rw [hloaded]
    rfl
  rw [hrun'] at hrun
  cases hrun
  exact .pure state constant

theorem reset_requests :
    ExecutionRequests TcM.reset initialState [] := by
  unfold TcM.reset
  exact ExecutionRequests.modify initialState _ rfl

theorem validation_function :
    (RecM.validateConstWellScoped concreteAxiom).run methods =
      (pure () : TcM .anon Unit) := by
  funext state
  unfold concreteAxiom RecM.validateConstWellScoped
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.validateExprWellScoped source 0 0).run methods) _ state = _
  have hvalidate :
      (RecM.validateExprWellScoped source 0 0).run methods state =
        .ok () state := by
    unfold RecM.validateExprWellScoped
    rw [RecM.validateExprWellScoped.go.eq_def]
    simp only [Std.HashSet.contains_empty, Bool.false_eq_true, if_false]
    have hsource : source = .sort sourceUniv source.info := by rfl
    rw [hsource]
    rw [ReaderT.run_bind]
    change EStateM.bind
      ((RecM.validateUnivParamsSeen sourceUniv 0 ∅).run methods) _ state = _
    let seen : Std.HashSet Address :=
      ({} : Std.HashSet Address).insert sourceUniv.addr
    have huniv :
        (RecM.validateUnivParamsSeen sourceUniv 0 ∅).run methods state =
          .ok seen state := by
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

theorem validation_requests :
    ExecutionRequests
      ((RecM.validateConstWellScoped concreteAxiom).run methods)
      initialState [] :=
  .of_eq validation_function (.pure initialState ())

theorem inferKey_function :
    TcM.inferKey source =
      (pure inferKey : TcM .anon (Address × Address)) := by
  funext state
  unfold TcM.inferKey TcM.ctxAddrForLbr
  change EStateM.bind (get : TcM .anon (TcState .anon))
    (fun _ => pure inferKey) state = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) state =
    .ok state state from rfl]

theorem inferKey_requests :
    ExecutionRequests (TcM.inferKey source) initialState [] :=
  .of_eq inferKey_function (.pure initialState inferKey)

theorem cacheInferResult_requests (state : TcState .anon)
    (inferred : KExpr .anon) :
    ExecutionRequests
      ((RecM.cacheInferResult false inferKey inferred).run methods)
      state [] := by
  unfold RecM.cacheInferResult
  simp only [Bool.not_false, if_true]
  exact ExecutionRequests.modify state _ rfl

theorem inferUncached_function :
    (RecM.inferUncached RecM.inferCall false source).run methods =
      TcM.intern result := by
  funext state
  have hsource : source = .sort sourceUniv source.info := by rfl
  rw [hsource]
  unfold RecM.inferUncached
  rfl

theorem inferUncached_requests (state : TcState .anon) :
    ExecutionRequests
      ((RecM.inferUncached RecM.inferCall false source).run methods)
      state [.internExpr result] :=
  .of_eq inferUncached_function (.internExpr state result)

theorem inference_requests :
    ExecutionRequests ((RecM.infer source).run methods) initialState
      [.internExpr result] := by
  unfold RecM.infer RecM.inferWith
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  apply ExecutionRequests.bind (ExecutionRequests.get initialState)
  intro current after hget
  cases hget
  apply ExecutionRequests.bind inferKey_requests
  intro key after hkey
  rw [initial_inferKey] at hkey
  cases hkey
  apply ExecutionRequests.bind (ExecutionRequests.get initialState)
  intro current after hget
  cases hget
  rw [initial_inferMiss]
  simp only
  rw [ReaderT.run_bind, ReaderT.run_pure, pure_bind]
  have hinferOnly : initialState.inferOnly = false := by rfl
  rw [hinferOnly]
  simp only [Bool.false_eq_true, if_false, ReaderT.run_pure, pure_bind,
    ReaderT.run_bind]
  apply ExecutionRequests.bind (inferUncached_requests initialState)
  intro inferred after _hinfer
  apply ExecutionRequests.bind
    (cacheInferResult_requests after inferred)
  intro _ afterCache _hcache
  exact .pure afterCache inferred

theorem ensureSort_function :
    (RecM.ensureSortDirect result).run methods =
      (pure resultUniv : TcM .anon (KUniv .anon)) := by
  funext state
  unfold RecM.ensureSortDirect result
  rfl

theorem ensureSort_requests (state : TcState .anon) :
    ExecutionRequests ((RecM.ensureSortDirect result).run methods)
      state [] :=
  .of_eq ensureSort_function (.pure state resultUniv)

theorem member_requests (separation : AddressSeparation) :
    ExecutionRequests
      ((RecM.checkConstMember targetId concreteAxiom).run methods)
      initialState [.internExpr result] := by
  obtain ⟨afterInfer, hinfer⟩ := inference_run separation
  unfold RecM.checkConstMember
  simp only [concreteAxiom, Mode.F.hasDups, Bool.false_eq_true, if_false,
    ReaderT.run_bind]
  apply ExecutionRequests.bind validation_requests
  intro _ afterValidation hvalidation
  rw [validation_execution] at hvalidation
  cases hvalidation
  apply ExecutionRequests.bind inference_requests
  intro inferred after hrun
  rw [hinfer] at hrun
  cases hrun
  have hresult : result = .sort resultUniv result.info := by rfl
  rw [hresult]
  apply ExecutionRequests.bind (ensureSort_requests afterInfer)
  intro _ afterSort hsort
  have hsortRun :
      (RecM.ensureSortDirect result).run methods afterInfer =
        .ok resultUniv afterInfer := by
    rw [ensureSort_function]
    rfl
  rw [hsortRun] at hsort
  cases hsort
  exact .pure afterInfer ()

theorem fresh_requests (separation : AddressSeparation) :
    ExecutionRequests
      ((RecM.checkConstMemberFresh targetId).run methods)
      initialState [.internExpr result] := by
  unfold RecM.checkConstMemberFresh
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  apply ExecutionRequests.bind reset_requests
  intro _ afterReset hreset
  rw [initialState_reset] at hreset
  cases hreset
  apply ExecutionRequests.bind
    (getConst_requests_of_loaded initial_loaded)
  intro constant afterGet hget
  rw [initial_get] at hget
  cases hget
  exact member_requests separation

theorem route_function :
    (RecM.coordinatedBlockFor concreteAxiom).run methods =
      (pure none : TcM .anon (Option (KId .anon))) := by
  funext state
  rfl

theorem route_requests (state : TcState .anon) :
    ExecutionRequests
      ((RecM.coordinatedBlockFor concreteAxiom).run methods) state [] :=
  .of_eq route_function (.pure state none)

theorem body_requests (separation : AddressSeparation) :
    ExecutionRequests ((RecM.checkConst targetId).run methods)
      initialState [.internExpr result] := by
  unfold RecM.checkConst
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  apply ExecutionRequests.bind
    (getConst_requests_of_loaded initial_loaded)
  intro constant afterGet hget
  rw [initial_get] at hget
  cases hget
  apply ExecutionRequests.bind (route_requests initialState)
  intro route afterRoute hroute
  have hrouteRun :
      (RecM.coordinatedBlockFor concreteAxiom).run methods initialState =
        .ok none initialState := by
    rw [route_function]
    rfl
  rw [hrouteRun] at hroute
  cases hroute
  exact fresh_requests separation

/-- The exact public checker trace.  The successful run performs one and
only one audited interning request: construction of `Sort 1` while
inferring the pending `Sort 0` axiom's type. -/
theorem public_requests (separation : AddressSeparation) :
    ExecutionRequests (TcM.checkConst targetId) initialState
      [.internExpr result] := by
  unfold TcM.checkConst
  apply ExecutionRequests.isolateCheckErrors
  apply ExecutionRequests.runRec
  simpa [initialState, methods] using body_requests separation

def requests : List WalkerRequest := [.internExpr result]

theorem result_constructed : KExpr.Constructed result := by
  unfold result
  exact .sort

theorem request_coverage :
    CheckConstSupport initialState.env.intern requests support := by
  constructor
  · constructor
    · intro candidate hcandidate
      obtain ⟨addr, haddr⟩ := hcandidate
      simp [initialState, env, KEnv.insert, TcState.ofEnvAnon] at haddr
    · intro candidate hcandidate
      obtain ⟨addr, haddr⟩ := hcandidate
      simp [initialState, env, KEnv.insert, TcState.ofEnvAnon] at haddr
  · intro request hrequest
    simp [requests] at hrequest
    subst request
    constructor
    · intro candidate hcandidate
      change candidate = result at hcandidate
      subst candidate
      exact result_supported
    · intro candidate hcandidate
      exact False.elim hcandidate

theorem request_bounds : ResourceBounds requests := by
  constructor
  intro request hrequest
  simp [requests] at hrequest
  subst request
  exact result_constructed

theorem runAssumptions (separation : AddressSeparation) :
    RunAssumptions initialState (TcM.checkConst targetId) requests support :=
  ⟨by simpa [requests] using public_requests separation,
    support_collisionFree separation, request_coverage, request_bounds⟩

/-- The complete K2S public-run package for a real fuel-one checker
execution.  Its method-call schedule and its suffix-state domain are both
finite, but deliberately separate: the call domain contains the source
sort, while the run support also contains the constructed successor sort. -/
def publicContext (separation : AddressSeparation) :
    ScopedRecursiveMethodRunContext initialState (TcM.checkConst targetId)
      requests RawProjRel.none world support where
  run := runAssumptions separation
  model := model
  calls := Methods.ScopedSortSchedule.calls source
  schedule := by
    simpa [initialState] using schedule separation

end Ix.Tc.PositiveFuelSort.Checker
