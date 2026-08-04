import Ix.Tc.Verify.Check.ProjectionInferencePolicy

/-!
# Operational inference-policy frame for WHNF drivers

The recursive method knot needs an outcome-sensitive guarantee that WHNF
preserves the caller's `TcState.inferOnly` bit.  This module proves the
production driver shells directly: bounded iteration, syntactic fast paths,
instrumentation, fuel charging, cache selection, hits, misses, and writes.

The reducer internals remain explicit premises in
`WhnfReductionPolicyAt`.  Later modules discharge those premises over the
individual structural, no-delta, and full-WHNF helper seams; this file ensures
that no additional policy obligation is hidden in the outer drivers.
-/

namespace Ix.Tc

namespace RecM


theorem runBounded_preservesInferOnly
    {methods : Methods .anon}
    {step : sigma → RecM .anon (BoundedStep sigma alpha)}
    (hstep : ∀ state, ((step state).run methods).PreservesInferOnly) :
    ∀ fuel state,
      ((runBounded step fuel state).run methods).PreservesInferOnly
  | 0, state => by
      exact TcM.PreservesInferOnly.throw _
  | fuel + 1, state => by
      rw [runBounded, ReaderT.run_bind]
      apply TcM.PreservesInferOnly.bind (hstep state)
      intro action
      cases action with
      | next state => exact runBounded_preservesInferOnly hstep fuel state
      | done result => exact TcM.PreservesInferOnly.pure result

/-- Operational contracts for the production seams inside the three WHNF
drivers.  The outer bounded loops, cache routing, instrumentation, and leaf
dispatch are proved below rather than included as assumptions. -/
structure WhnfNoDeltaPolicyAt (methods : Methods .anon) : Prop where
  transient : ∀ source,
    ((isTransientNatLiteralWork source).run methods).PreservesInferOnly
  coreStep : ∀ source flags,
    ((whnfCoreWithFlagsStep source flags).run methods).PreservesInferOnly
  noDeltaReducers : ∀ flags mode source,
    ((whnfNoDeltaReducersStep flags mode source).run methods).PreservesInferOnly
structure WhnfReductionPolicyAt (methods : Methods .anon) : Prop extends
    WhnfNoDeltaPolicyAt methods where
  fullStep : ∀ mode state,
    ((whnfWithNatSuccModeStep mode state).run methods).PreservesInferOnly

theorem whnfCoreWithFlagsUncached_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfNoDeltaPolicyAt methods)
    (source : KExpr .anon) (flags : WhnfFlags) :
    ((whnfCoreWithFlagsUncached source flags).run methods).PreservesInferOnly := by
  unfold whnfCoreWithFlagsUncached
  exact runBounded_preservesInferOnly
    (fun current => policy.coreStep current flags) _ source

private theorem whnfCoreFullCacheMiss_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfNoDeltaPolicyAt methods)
    (source : KExpr .anon) (flags : WhnfFlags)
    (key : Address × Address) :
    ((do
      let result ← whnfCoreWithFlagsUncached source flags
      modify fun state : TcState .anon => { state with env := { state.env with
        whnfCoreCache := state.env.whnfCoreCache.insert key result } }
      pure result).run methods).PreservesInferOnly := by
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind
    (whnfCoreWithFlagsUncached_preservesInferOnly policy source flags)
  intro result
  show ((do
    modify fun state : TcState .anon => { state with env := { state.env with
      whnfCoreCache := state.env.whnfCoreCache.insert key result } }
    pure result : RecM .anon (KExpr .anon)).run methods).PreservesInferOnly
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind
    (TcM.PreservesInferOnly.modify
      (f := fun state : TcState .anon => { state with env := { state.env with
        whnfCoreCache := state.env.whnfCoreCache.insert key result } })
      (fun _ => rfl))
  intro _
  exact TcM.PreservesInferOnly.pure result

private theorem whnfCoreCheapCacheMiss_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfNoDeltaPolicyAt methods)
    (source : KExpr .anon) (flags : WhnfFlags)
    (key : Address × Address) :
    ((do
      let result ← whnfCoreWithFlagsUncached source flags
      modify fun state : TcState .anon => { state with env := { state.env with
        whnfCoreCheapCache := state.env.whnfCoreCheapCache.insert key result } }
      pure result).run methods).PreservesInferOnly := by
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind
    (whnfCoreWithFlagsUncached_preservesInferOnly policy source flags)
  intro result
  show ((do
    modify fun state : TcState .anon => { state with env := { state.env with
      whnfCoreCheapCache := state.env.whnfCoreCheapCache.insert key result } }
    pure result : RecM .anon (KExpr .anon)).run methods).PreservesInferOnly
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind
    (TcM.PreservesInferOnly.modify
      (f := fun state : TcState .anon => { state with env := { state.env with
        whnfCoreCheapCache := state.env.whnfCoreCheapCache.insert key result } })
      (fun _ => rfl))
  intro _
  exact TcM.PreservesInferOnly.pure result

theorem whnfCoreWithFlagsNonLeaf_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfNoDeltaPolicyAt methods)
    (source : KExpr .anon) (flags : WhnfFlags) :
    ((whnfCoreWithFlagsNonLeaf source flags).run methods).PreservesInferOnly := by
  unfold whnfCoreWithFlagsNonLeaf
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  apply TcM.PreservesInferOnly.bind (TcM.PreservesInferOnly.whnfKey source)
  intro key
  apply TcM.PreservesInferOnly.bind (policy.transient source)
  intro transient
  cases hfull : flags.isFull with
  | false =>
      cases transient with
      | true =>
          simp
          exact whnfCoreWithFlagsUncached_preservesInferOnly policy source flags
      | false =>
          simp
          apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
          intro state
          split
          · exact TcM.PreservesInferOnly.pure _
          · exact whnfCoreCheapCacheMiss_preservesInferOnly policy source
              flags key
  | true =>
      cases transient with
      | true =>
          simp
          exact whnfCoreWithFlagsUncached_preservesInferOnly policy source flags
      | false =>
          simp
          apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
          intro state
          split
          · exact TcM.PreservesInferOnly.pure _
          · exact whnfCoreFullCacheMiss_preservesInferOnly policy source
              flags key

theorem whnfCoreWithFlags_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfNoDeltaPolicyAt methods)
    (source : KExpr .anon) (flags : WhnfFlags) :
    ((whnfCoreWithFlags source flags).run methods).PreservesInferOnly := by
  cases source with
  | var idx name info =>
      unfold whnfCoreWithFlags
      simp only [ReaderT.run_bind, ReaderT.run_monadLift]
      apply TcM.PreservesInferOnly.bind
        (TcM.PreservesInferOnly.isLetVar idx)
      intro isLet
      cases isLet with
      | false =>
          simp only [Bool.not_false, if_true]
          exact TcM.PreservesInferOnly.pure _
      | true =>
          simp only [Bool.not_true, pure_bind]
          exact whnfCoreWithFlagsNonLeaf_preservesInferOnly policy _ flags
  | fvar id name info =>
      simpa only [whnfCoreWithFlags, pure_bind] using
        whnfCoreWithFlagsNonLeaf_preservesInferOnly policy _ flags
  | app f a info =>
      simpa only [whnfCoreWithFlags, pure_bind] using
        whnfCoreWithFlagsNonLeaf_preservesInferOnly policy _ flags
  | letE name ty value body nondep info =>
      simpa only [whnfCoreWithFlags, pure_bind] using
        whnfCoreWithFlagsNonLeaf_preservesInferOnly policy _ flags
  | prj id field value info =>
      simpa only [whnfCoreWithFlags, pure_bind] using
        whnfCoreWithFlagsNonLeaf_preservesInferOnly policy _ flags
  | sort u info => exact TcM.PreservesInferOnly.pure _
  | const id levels info => exact TcM.PreservesInferOnly.pure _
  | lam name bi ty body info => exact TcM.PreservesInferOnly.pure _
  | all name bi ty body info => exact TcM.PreservesInferOnly.pure _
  | nat value blob info => exact TcM.PreservesInferOnly.pure _
  | str value blob info => exact TcM.PreservesInferOnly.pure _

theorem whnfCore_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfNoDeltaPolicyAt methods)
    (source : KExpr .anon) :
    ((whnfCore source).run methods).PreservesInferOnly := by
  simpa only [whnfCore] using
    whnfCoreWithFlags_preservesInferOnly policy source .FULL

theorem whnfNoDeltaImplStep_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfNoDeltaPolicyAt methods)
    (flags : WhnfFlags) (mode : NatSuccMode) (source : KExpr .anon) :
    ((whnfNoDeltaImplStep flags mode source).run methods).PreservesInferOnly := by
  unfold whnfNoDeltaImplStep
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind
    (whnfCoreWithFlags_preservesInferOnly policy source flags)
  intro reduced
  exact policy.noDeltaReducers flags mode reduced

theorem whnfNoDeltaImplUncached_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfNoDeltaPolicyAt methods)
    (source : KExpr .anon) (flags : WhnfFlags) (mode : NatSuccMode) :
    ((whnfNoDeltaImplUncached source flags mode).run methods).PreservesInferOnly := by
  unfold whnfNoDeltaImplUncached
  exact runBounded_preservesInferOnly
    (fun current => whnfNoDeltaImplStep_preservesInferOnly policy flags mode
      current) _ source

private theorem whnfNoDeltaNoWriteMiss_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfNoDeltaPolicyAt methods)
    (source : KExpr .anon) (flags : WhnfFlags) (mode : NatSuccMode) :
    ((do
      let result ← whnfNoDeltaImplUncached source flags mode
      let _ ← (get : RecM .anon (TcState .anon))
      pure result).run methods).PreservesInferOnly := by
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind
    (whnfNoDeltaImplUncached_preservesInferOnly policy source flags mode)
  intro result
  apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
  intro _
  exact TcM.PreservesInferOnly.pure result

private theorem whnfNoDeltaFullWriteMiss_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfNoDeltaPolicyAt methods)
    (source : KExpr .anon) (flags : WhnfFlags) (mode : NatSuccMode)
    (key : Address × Address) :
    ((do
      let result ← whnfNoDeltaImplUncached source flags mode
      let state ← (get : RecM .anon (TcState .anon))
      if state.inNativeReduce = false then
        (fun _ => result) <$> modify fun current : TcState .anon =>
          { current with env := { current.env with
            whnfNoDeltaCache :=
              current.env.whnfNoDeltaCache.insert key result } }
      else
        pure result).run methods).PreservesInferOnly := by
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind
    (whnfNoDeltaImplUncached_preservesInferOnly policy source flags mode)
  intro result
  apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
  intro state
  cases state.inNativeReduce with
  | false =>
      simp
      exact TcM.PreservesInferOnly.map
        (TcM.PreservesInferOnly.modify
          (f := fun state : TcState .anon => { state with env := { state.env with
            whnfNoDeltaCache :=
              state.env.whnfNoDeltaCache.insert key result } })
          (fun _ => rfl))
        (fun _ => result)
  | true =>
      simp
      exact TcM.PreservesInferOnly.pure result

private theorem whnfNoDeltaCheapWriteMiss_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfNoDeltaPolicyAt methods)
    (source : KExpr .anon) (flags : WhnfFlags) (mode : NatSuccMode)
    (key : Address × Address) :
    ((do
      let result ← whnfNoDeltaImplUncached source flags mode
      let state ← (get : RecM .anon (TcState .anon))
      if state.inNativeReduce = false then
        (fun _ => result) <$> modify fun current : TcState .anon =>
          { current with env := { current.env with
            whnfNoDeltaCheapCache :=
              current.env.whnfNoDeltaCheapCache.insert key result } }
      else
        pure result).run methods).PreservesInferOnly := by
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind
    (whnfNoDeltaImplUncached_preservesInferOnly policy source flags mode)
  intro result
  apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
  intro state
  cases state.inNativeReduce with
  | false =>
      simp
      exact TcM.PreservesInferOnly.map
        (TcM.PreservesInferOnly.modify
          (f := fun state : TcState .anon => { state with env := { state.env with
            whnfNoDeltaCheapCache :=
              state.env.whnfNoDeltaCheapCache.insert key result } })
          (fun _ => rfl))
        (fun _ => result)
  | true =>
      simp
      exact TcM.PreservesInferOnly.pure result

theorem whnfNoDeltaImplNonLeaf_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfNoDeltaPolicyAt methods)
    (source : KExpr .anon) (flags : WhnfFlags) (mode : NatSuccMode) :
    ((whnfNoDeltaImplNonLeaf source flags mode).run methods).PreservesInferOnly := by
  unfold whnfNoDeltaImplNonLeaf
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  apply TcM.PreservesInferOnly.bind (TcM.PreservesInferOnly.whnfKey source)
  intro key
  apply TcM.PreservesInferOnly.bind (policy.transient source)
  intro transient
  cases huse : (mode == .collapse) with
  | false =>
      simp
      exact whnfNoDeltaNoWriteMiss_preservesInferOnly policy source flags mode
  | true =>
      cases transient with
      | true =>
          simp
          exact whnfNoDeltaNoWriteMiss_preservesInferOnly policy source flags mode
      | false =>
          cases hfull : flags.isFull with
          | false =>
              simp
              apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
              intro state
              split
              · exact TcM.PreservesInferOnly.pure _
              · exact whnfNoDeltaCheapWriteMiss_preservesInferOnly policy
                  source flags mode key
          | true =>
              simp
              apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
              intro state
              split
              · exact TcM.PreservesInferOnly.pure _
              · exact whnfNoDeltaFullWriteMiss_preservesInferOnly policy
                  source flags mode key

theorem whnfNoDeltaImpl_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfNoDeltaPolicyAt methods)
    (source : KExpr .anon) (flags : WhnfFlags) (mode : NatSuccMode) :
    ((whnfNoDeltaImpl source flags mode).run methods).PreservesInferOnly := by
  cases source with
  | var idx name info =>
      unfold whnfNoDeltaImpl
      simp only [ReaderT.run_bind, ReaderT.run_monadLift]
      apply TcM.PreservesInferOnly.bind
        (TcM.PreservesInferOnly.isLetVar idx)
      intro isLet
      cases isLet with
      | false =>
          simp only [Bool.not_false, if_true]
          exact TcM.PreservesInferOnly.pure _
      | true =>
          simp only [Bool.not_true, pure_bind]
          exact whnfNoDeltaImplNonLeaf_preservesInferOnly policy _ flags mode
  | fvar id name info =>
      simpa only [whnfNoDeltaImpl, pure_bind] using
        whnfNoDeltaImplNonLeaf_preservesInferOnly policy _ flags mode
  | const id levels info =>
      simpa only [whnfNoDeltaImpl, pure_bind] using
        whnfNoDeltaImplNonLeaf_preservesInferOnly policy _ flags mode
  | app f a info =>
      simpa only [whnfNoDeltaImpl, pure_bind] using
        whnfNoDeltaImplNonLeaf_preservesInferOnly policy _ flags mode
  | letE name ty value body nondep info =>
      simpa only [whnfNoDeltaImpl, pure_bind] using
        whnfNoDeltaImplNonLeaf_preservesInferOnly policy _ flags mode
  | prj id field value info =>
      simpa only [whnfNoDeltaImpl, pure_bind] using
        whnfNoDeltaImplNonLeaf_preservesInferOnly policy _ flags mode
  | sort u info => exact TcM.PreservesInferOnly.pure _
  | lam name bi ty body info => exact TcM.PreservesInferOnly.pure _
  | all name bi ty body info => exact TcM.PreservesInferOnly.pure _
  | nat value blob info => exact TcM.PreservesInferOnly.pure _
  | str value blob info => exact TcM.PreservesInferOnly.pure _

theorem whnfNoDelta_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfNoDeltaPolicyAt methods)
    (source : KExpr .anon) :
    ((whnfNoDelta source).run methods).PreservesInferOnly := by
  simpa only [whnfNoDelta] using
    whnfNoDeltaImpl_preservesInferOnly policy source .FULL .collapse

theorem whnfWithNatSuccModeUncached_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfReductionPolicyAt methods)
    (source : KExpr .anon) (mode : NatSuccMode) :
    ((whnfWithNatSuccModeUncached source mode).run methods).PreservesInferOnly := by
  unfold whnfWithNatSuccModeUncached
  exact runBounded_preservesInferOnly
    (fun state => policy.fullStep mode state) _ (source, {})

theorem whnfWithNatSuccModePrefix_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) :
    ((whnfWithNatSuccModePrefix source).run methods).PreservesInferOnly := by
  unfold whnfWithNatSuccModePrefix
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  apply TcM.PreservesInferOnly.bind
    (TcM.PreservesInferOnly.stepTrace "whnf+" fun _ => TcM.addr8 source.addr)
  intro _
  exact TcM.PreservesInferOnly.bumpStats
    (fun state : TcState .anon => { state with
      whnfCalls := state.whnfCalls + 1 })
    (fun _ => rfl)

theorem whnfWithNatSuccModeMissCharge_preservesInferOnly
    {methods : Methods .anon} :
    ((whnfWithNatSuccModeMissCharge (m := .anon)).run methods).PreservesInferOnly := by
  unfold whnfWithNatSuccModeMissCharge
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  apply TcM.PreservesInferOnly.bind
    (TcM.PreservesInferOnly.bumpStats
      (fun state : TcState .anon => { state with
        whnfMisses := state.whnfMisses + 1 })
      (fun _ => rfl))
  intro _
  exact TcM.PreservesInferOnly.tick

private theorem whnfNoWriteMiss_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfReductionPolicyAt methods)
    (source : KExpr .anon) (mode : NatSuccMode) :
    ((do
      let result ← whnfWithNatSuccModeUncached source mode
      let _ ← (get : RecM .anon (TcState .anon))
      pure result).run methods).PreservesInferOnly := by
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind
    (whnfWithNatSuccModeUncached_preservesInferOnly policy source mode)
  intro result
  apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
  intro _
  exact TcM.PreservesInferOnly.pure result

private theorem whnfWriteMiss_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfReductionPolicyAt methods)
    (source : KExpr .anon) (mode : NatSuccMode)
    (key : Address × Address) :
    ((do
      let result ← whnfWithNatSuccModeUncached source mode
      let state ← (get : RecM .anon (TcState .anon))
      if state.inNativeReduce = false then
        (fun _ => result) <$> modify fun current : TcState .anon =>
          { current with env := { current.env with
            whnfCache := current.env.whnfCache.insert key result } }
      else
        pure result).run methods).PreservesInferOnly := by
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind
    (whnfWithNatSuccModeUncached_preservesInferOnly policy source mode)
  intro result
  apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
  intro state
  cases state.inNativeReduce with
  | false =>
      simp
      exact TcM.PreservesInferOnly.map
        (TcM.PreservesInferOnly.modify
          (f := fun state : TcState .anon => { state with env := { state.env with
            whnfCache := state.env.whnfCache.insert key result } })
          (fun _ => rfl))
        (fun _ => result)
  | true =>
      simp
      exact TcM.PreservesInferOnly.pure result

theorem whnfWithNatSuccModeNonLeaf_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfReductionPolicyAt methods)
    (source : KExpr .anon) (mode : NatSuccMode) :
    ((whnfWithNatSuccModeNonLeaf source mode).run methods).PreservesInferOnly := by
  unfold whnfWithNatSuccModeNonLeaf
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  apply TcM.PreservesInferOnly.bind
    (whnfWithNatSuccModePrefix_preservesInferOnly source)
  intro _
  apply TcM.PreservesInferOnly.bind (TcM.PreservesInferOnly.whnfKey source)
  intro key
  apply TcM.PreservesInferOnly.bind (policy.transient source)
  intro transient
  cases huse : (mode == .collapse) with
  | false =>
      simp
      apply TcM.PreservesInferOnly.bind
        whnfWithNatSuccModeMissCharge_preservesInferOnly
      intro _
      exact whnfNoWriteMiss_preservesInferOnly policy source mode
  | true =>
      cases transient with
      | true =>
          simp
          apply TcM.PreservesInferOnly.bind
            whnfWithNatSuccModeMissCharge_preservesInferOnly
          intro _
          exact whnfNoWriteMiss_preservesInferOnly policy source mode
      | false =>
          simp
          apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
          intro state
          split
          · exact TcM.PreservesInferOnly.pure _
          · apply TcM.PreservesInferOnly.bind
              whnfWithNatSuccModeMissCharge_preservesInferOnly
            intro _
            exact whnfWriteMiss_preservesInferOnly policy source mode key

theorem whnfWithNatSuccMode_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfReductionPolicyAt methods)
    (source : KExpr .anon) (mode : NatSuccMode) :
    ((whnfWithNatSuccMode source mode).run methods).PreservesInferOnly := by
  cases source with
  | var idx name info =>
      unfold whnfWithNatSuccMode
      simp only [ReaderT.run_bind, ReaderT.run_monadLift]
      apply TcM.PreservesInferOnly.bind
        (TcM.PreservesInferOnly.isLetVar idx)
      intro isLet
      cases isLet with
      | false =>
          simp only [Bool.not_false, if_true]
          exact TcM.PreservesInferOnly.pure _
      | true =>
          simp only [Bool.not_true, pure_bind]
          exact whnfWithNatSuccModeNonLeaf_preservesInferOnly policy _ mode
  | fvar id name info =>
      simpa only [whnfWithNatSuccMode, pure_bind] using
        whnfWithNatSuccModeNonLeaf_preservesInferOnly policy _ mode
  | const id levels info =>
      simpa only [whnfWithNatSuccMode, pure_bind] using
        whnfWithNatSuccModeNonLeaf_preservesInferOnly policy _ mode
  | app f a info =>
      simpa only [whnfWithNatSuccMode, pure_bind] using
        whnfWithNatSuccModeNonLeaf_preservesInferOnly policy _ mode
  | letE name ty value body nondep info =>
      simpa only [whnfWithNatSuccMode, pure_bind] using
        whnfWithNatSuccModeNonLeaf_preservesInferOnly policy _ mode
  | prj id field value info =>
      simpa only [whnfWithNatSuccMode, pure_bind] using
        whnfWithNatSuccModeNonLeaf_preservesInferOnly policy _ mode
  | sort u info => exact TcM.PreservesInferOnly.pure _
  | lam name bi ty body info => exact TcM.PreservesInferOnly.pure _
  | all name bi ty body info => exact TcM.PreservesInferOnly.pure _
  | nat value blob info => exact TcM.PreservesInferOnly.pure _
  | str value blob info => exact TcM.PreservesInferOnly.pure _

theorem whnf_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfReductionPolicyAt methods)
    (source : KExpr .anon) :
    ((whnf source).run methods).PreservesInferOnly := by
  simpa only [whnf] using
    whnfWithNatSuccMode_preservesInferOnly policy source .collapse

end RecM

end Ix.Tc
