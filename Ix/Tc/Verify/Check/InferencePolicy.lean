import Ix.Tc.Verify.Knot
import Ix.Tc.Verify.Infer.Applications
import Ix.Tc.Verify.Whnf.StructEta.CallbackPrefix
import Ix.Tc.Verify.Whnf.StructEta.RecursionClassifier

/-!
# Inference-policy frames

Full inference is selected by the mutable `TcState.inferOnly` bit.  The
ordinary K1/K2 semantic contracts intentionally ignore operational flags, so
they cannot by themselves justify that a recursive callback which starts in
full mode returns in full mode.

This module gives that missing fact a small, outcome-sensitive vocabulary.
`TcM.PreservesInferOnly` constrains both successful and partial-error states.
The method-table record and finite-knot lemmas isolate the remaining proof:
show that one unfolded production layer preserves the flag whenever its
smaller callbacks do.  No semantic typing claim is bundled into this
operational frame.
-/

namespace Ix.Tc

/-- An action restores the caller's inference policy on both outcomes. -/
def TcM.PreservesInferOnly (x : TcM .anon alpha) : Prop :=
  ∀ before,
    match x before with
    | .ok _ after => after.inferOnly = before.inferOnly
    | .error _ after => after.inferOnly = before.inferOnly

namespace TcM.PreservesInferOnly

/-- Turn a policy-indexed Hoare frame into the global operational frame used
by the concrete method table. -/
theorem ofWF {x : TcM .anon alpha}
    (h : ∀ before, TcM.WF
      (fun after => after.inferOnly = before.inferOnly) before x
      (fun _ _ => True)) : x.PreservesInferOnly := by
  intro before
  have hpost := h before rfl
  cases hrun : x before <;> rw [hrun] at hpost <;> exact hpost.1

theorem ok {x : TcM .anon alpha} (hx : x.PreservesInferOnly)
    {before after : TcState .anon} {value : alpha}
    (hrun : x before = .ok value after) :
    after.inferOnly = before.inferOnly := by
  simpa [hrun] using hx before

theorem error {x : TcM .anon alpha} (hx : x.PreservesInferOnly)
    {before after : TcState .anon} {err : TcError .anon}
    (hrun : x before = .error err after) :
    after.inferOnly = before.inferOnly := by
  simpa [hrun] using hx before

theorem pure (value : alpha) :
    (pure value : TcM .anon alpha).PreservesInferOnly := by
  intro before
  rfl

theorem throw (err : TcError .anon) :
    (throw err : TcM .anon alpha).PreservesInferOnly := by
  intro before
  rfl

theorem get :
    (get : TcM .anon (TcState .anon)).PreservesInferOnly := by
  intro before
  rfl

theorem modifyGet
    {f : TcState .anon → alpha × TcState .anon}
    (hf : ∀ state, (f state).2.inferOnly = state.inferOnly) :
    (modifyGet f : TcM .anon alpha).PreservesInferOnly := by
  intro before
  exact hf before

theorem modify {f : TcState .anon → TcState .anon}
    (hf : ∀ state, (f state).inferOnly = state.inferOnly) :
    (modify f : TcM .anon PUnit).PreservesInferOnly := by
  exact modifyGet fun state => hf state

theorem bind {x : TcM .anon alpha} {f : alpha → TcM .anon beta}
    (hx : x.PreservesInferOnly)
    (hf : ∀ value, (f value).PreservesInferOnly) :
    (x >>= f).PreservesInferOnly := by
  intro before
  show (match EStateM.bind x f before with
    | .ok _ after => after.inferOnly = before.inferOnly
    | .error _ after => after.inferOnly = before.inferOnly)
  unfold EStateM.bind
  cases hrun : x before with
  | ok value middle =>
      have hfirst := hx.ok hrun
      cases hnext : f value middle with
      | ok result after =>
          simpa only [hnext] using (hf value).ok hnext |>.trans hfirst
      | error err after =>
          simpa only [hnext] using (hf value).error hnext |>.trans hfirst
  | error err after =>
      simpa only [hrun] using hx.error hrun

theorem tryCatch {x : TcM .anon alpha}
    {handler : TcError .anon → TcM .anon alpha}
    (hx : x.PreservesInferOnly)
    (hh : ∀ err, (handler err).PreservesInferOnly) :
    (tryCatch x handler).PreservesInferOnly := by
  intro before
  show (match (EStateM.tryCatch x handler : TcM .anon alpha) before with
    | .ok _ after => after.inferOnly = before.inferOnly
    | .error _ after => after.inferOnly = before.inferOnly)
  unfold EStateM.tryCatch
  cases hrun : x before with
  | ok value after =>
      simpa only [hrun] using hx.ok hrun
  | error err middle =>
      have hfirst := hx.error hrun
      have hrestore : EStateM.Backtrackable.restore middle
          (EStateM.Backtrackable.save before) = middle := rfl
      simp only [hrestore]
      cases hhandler : handler err middle with
      | ok value after =>
          simpa only [hhandler] using (hh err).ok hhandler |>.trans hfirst
      | error nextErr after =>
          simpa only [hhandler] using (hh err).error hhandler |>.trans hfirst

private theorem tryFinally_eq
    (x : TcM .anon alpha) (finalizer : TcM .anon beta)
    (before : TcState .anon) :
    tryFinally x finalizer before =
      match x before with
      | .ok value middle =>
          match finalizer middle with
          | .ok _ after => .ok value after
          | .error err after => .error err after
      | .error err middle =>
          match finalizer middle with
          | .ok _ after => .error err after
          | .error cleanupErr after => .error cleanupErr after := by
  unfold tryFinally
  change EStateM.map (fun value : alpha × beta => value.1)
    (tryFinally' x (fun _ => finalizer)) before = _
  unfold EStateM.map MonadFinally.tryFinally' EStateM.instMonadFinally
  cases hrun : x before <;>
    simp only [hrun] <;>
    cases hcleanup : finalizer _ <;>
    rfl

/-- `finally` composes two ordinary frames.  In particular, this covers
local-context scopes whose cleanup truncates only `lctx`. -/
theorem tryFinally {x : TcM .anon alpha} {finalizer : TcM .anon beta}
    (hx : x.PreservesInferOnly)
    (hfinalizer : finalizer.PreservesInferOnly) :
    (tryFinally x finalizer).PreservesInferOnly := by
  intro before
  rw [tryFinally_eq]
  cases hrun : x before with
  | ok value middle =>
      have hfirst := hx.ok hrun
      cases hfinal : finalizer middle with
      | ok _ after =>
          simpa only [hfinal] using hfinalizer.ok hfinal |>.trans hfirst
      | error err after =>
          simpa only [hfinal] using hfinalizer.error hfinal |>.trans hfirst
  | error err middle =>
      have hfirst := hx.error hrun
      cases hfinal : finalizer middle with
      | ok _ after =>
          simpa only [hfinal] using hfinalizer.ok hfinal |>.trans hfirst
      | error cleanupErr after =>
          simpa only [hfinal] using hfinalizer.error hfinal |>.trans hfirst

/-- Intern-table computations update only `env.intern`. -/
theorem runIntern (x : InternM .anon alpha) :
    (TcM.runIntern x).PreservesInferOnly := by
  intro before
  cases hrun : x before.env.intern
  rfl

end TcM.PreservesInferOnly

namespace TcM.LazyFaultPreserves

/-- Lazy ingress changes only the environment and faulted-address set, so it
preserves any fixed value of the inference-policy bit independently of the
driver hook's success or failure. -/
theorem inferOnly (policy : Bool) :
    TcM.LazyFaultPreserves (fun state => state.inferOnly = policy) := by
  intro state fault addr hlazy hpolicy
  cases hrun : fault addr state.env <;>
    simp [TcM.lazyIngressPost, hpolicy]

end TcM.LazyFaultPreserves

namespace TcM.PreservesInferOnly

/-- The installed lazy hook cannot alter checker fields outside `env`. -/
theorem lazyIngressAddr (addr : Address) :
    (TcM.lazyIngressAddr (m := .anon) addr).PreservesInferOnly := by
  apply ofWF
  intro before
  exact TcM.lazyIngressAddr_wf
    (TcM.LazyFaultPreserves.inferOnly before.inferOnly) addr before

/-- Optional constant lookup preserves the policy through eager hits, lazy
ingress, retry, post-fault misses, and hook errors. -/
theorem tryGetConst (id : KId .anon) :
    (TcM.tryGetConst id).PreservesInferOnly := by
  apply ofWF
  intro before
  exact TcM.tryGetConst_wf
    (TcM.LazyFaultPreserves.inferOnly before.inferOnly) id before

/-- Required lookup only converts the final optional miss to an error. -/
theorem getConst (id : KId .anon) :
    (TcM.getConst id).PreservesInferOnly := by
  unfold TcM.getConst
  apply bind (tryGetConst id)
  intro found
  cases found with
  | none => exact throw _
  | some concrete => exact pure concrete

/-- Block lookup has the same operational lazy-ingress frame. -/
theorem tryGetBlock (id : KId .anon) :
    (TcM.tryGetBlock id).PreservesInferOnly := by
  apply ofWF
  intro before
  exact TcM.tryGetBlock_wf
    (TcM.LazyFaultPreserves.inferOnly before.inferOnly) id before

/-- Fuel consumption and exhaustion do not change inference policy. -/
theorem tick : (TcM.tick (m := .anon)).PreservesInferOnly := by
  apply ofWF
  intro before
  apply TcM.WF.mono
    (TcM.tick.wf (I := fun after =>
      after.inferOnly = before.inferOnly) (fun _ hpolicy => hpolicy))
  · intros; trivial
  · intros; trivial

/-- Environment-only mutation preserves inference policy. -/
theorem modifyEnv (f : KEnv .anon → KEnv .anon) :
    (TcM.modifyEnv f).PreservesInferOnly := by
  exact modify (f := fun state => { state with env := f state.env })
    (fun _ => rfl)

/-- Unique-ownership equivalence-manager mutation changes no policy field. -/
theorem withEquiv (f : EquivManager → alpha × EquivManager) :
    (TcM.withEquiv (m := .anon) f).PreservesInferOnly := by
  unfold TcM.withEquiv
  apply bind (modifyGet (fun _ => rfl))
  intro manager
  cases hresult : f manager with
  | mk value next =>
      apply bind (modify
        (f := fun state => { state with equivManager := next })
        (fun _ => rfl))
      intro _
      exact pure value

/-- Optional tracing reads state but has no checker-state effect. -/
theorem stepTrace (tag : String) (payload : Unit → String) :
    (TcM.stepTrace (m := .anon) tag payload).PreservesInferOnly := by
  unfold TcM.stepTrace
  apply bind get
  intro state
  split <;> exact pure _

/-- A statistics update preserves policy whenever its supplied record update
does. -/
theorem bumpStats (f : TcState .anon → TcState .anon)
    (hf : ∀ state, (f state).inferOnly = state.inferOnly) :
    (TcM.bumpStats f).PreservesInferOnly := by
  unfold TcM.bumpStats
  apply bind get
  intro state
  split
  · exact modify hf
  · exact pure _

/-- Legacy variable lookup either throws, reads, or updates only the intern
table. -/
theorem lookupVar (idx : UInt64) :
    (TcM.lookupVar (m := .anon) idx).PreservesInferOnly := by
  unfold TcM.lookupVar
  apply bind get
  intro state
  simp only
  split
  · exact throw _
  · exact runIntern _

/-- Legacy let lookup is read-only apart from interning the lifted value. -/
theorem lookupLetVal (idx : UInt64) :
    (TcM.lookupLetVal (m := .anon) idx).PreservesInferOnly := by
  unfold TcM.lookupLetVal
  apply bind get
  intro state
  simp only
  split
  · exact pure _
  · split
    · exact pure _
    · simp only [pure_bind]
      apply bind (runIntern _)
      intro result
      exact pure (some result)

/-- The let-variable classifier is state-pure. -/
theorem isLetVar (idx : UInt64) :
    (TcM.isLetVar (m := .anon) idx).PreservesInferOnly := by
  unfold TcM.isLetVar
  apply bind get
  intro state
  simp only
  split <;> exact pure _

/-- The eager-reduction marker classifier is state-pure. -/
theorem isEagerReduce (source : KExpr .anon) :
    (TcM.isEagerReduce source).PreservesInferOnly := by
  apply ofWF
  intro before
  apply TcM.WF.mono (TcM.isEagerReduce_wf source before)
  · intros; trivial
  · intros; trivial

/-- Suffix-key memoization may update only `ctxAddrCache`, so inference-key
construction preserves the policy bit on every outcome. -/
theorem ctxAddrForLbr (lbr : UInt64) :
    (TcM.ctxAddrForLbr (m := .anon) lbr).PreservesInferOnly := by
  intro before
  have hrun := TcM.ctxAddrForLbr_wf
    (I := fun after : TcState .anon =>
      after.inferOnly = before.inferOnly)
    (fun {prior next : TcState .anon} hmiddle hframe => by
      have hsame : next.inferOnly = prior.inferOnly := by
        simpa [ContextKeyFrame] using congrArg TcState.inferOnly hframe
      exact hsame.trans hmiddle)
    lbr before rfl
  cases hexec : TcM.ctxAddrForLbr lbr before with
  | ok value after =>
      rw [hexec] at hrun
      exact hrun.1
  | error err after =>
      rw [hexec] at hrun
      exact hrun.1

/-- WHNF key construction only extends the suffix-key memo table. -/
theorem whnfKey (source : KExpr .anon) :
    (TcM.whnfKey source).PreservesInferOnly := by
  unfold TcM.whnfKey
  apply bind (ctxAddrForLbr source.lbr)
  intro key
  exact pure (source.addr, key)

/-- DefEq context-key construction is the same suffix memo operation. -/
theorem defEqCtxKey (left right : KExpr .anon) :
    (TcM.defEqCtxKey left right).PreservesInferOnly := by
  exact ctxAddrForLbr _

theorem inferKey (source : KExpr .anon) :
    (TcM.inferKey source).PreservesInferOnly := by
  unfold TcM.inferKey
  apply bind (ctxAddrForLbr source.lbr)
  intro _
  exact pure _

theorem freshFVarId :
    (TcM.freshFVarId (m := .anon)).PreservesInferOnly := by
  intro before
  by_cases hroom : before.env.nextFVarId.toNat + 1 < UInt64.size
  · rw [TcM.freshFVarId]
    simp only [if_pos hroom]
  · rw [TcM.freshFVarId]
    simp only [if_neg hroom]

/-- Binder opening changes the fvar counter, intern table, and local-context
stack, but never the inference policy. -/
theorem openBinder
    (name : Mode.anon.F Name) (bi : Mode.anon.F Lean.BinderInfo)
    (type body : KExpr .anon) :
    (TcM.openBinder name bi type body).PreservesInferOnly := by
  unfold TcM.openBinder
  apply bind freshFVarId
  intro fv
  apply bind (runIntern _)
  intro fvExpr
  apply bind (modify
    (f := fun state =>
      { state with lctx := state.lctx.push fv (.cdecl name bi type) })
    fun _ => rfl)
  intro _
  apply bind (runIntern (instantiateRev body #[fvExpr]))
  intro bodyOpen
  exact pure (bodyOpen, fv)

/-- Let opening has the same policy frame as lambda/forall opening. -/
theorem openLet
    (name : Mode.anon.F Name) (type value body : KExpr .anon) :
    (TcM.openLet name type value body).PreservesInferOnly := by
  unfold TcM.openLet
  apply bind freshFVarId
  intro fv
  apply bind (runIntern _)
  intro fvExpr
  apply bind (modify
    (f := fun state =>
      { state with lctx := state.lctx.push fv (.ldecl name type value) })
    fun _ => rfl)
  intro _
  apply bind (runIntern (instantiateRev body #[fvExpr]))
  intro bodyOpen
  exact pure (bodyOpen, fv)

/-- The production infer-only scope may run an arbitrary callback after
forcing the bit to `true`; its finalizer restores the caller's exact bit on
both outcomes. -/
theorem withInferOnly (x : TcM .anon alpha) :
    (TcM.withInferOnly x).PreservesInferOnly := by
  intro before
  rw [TcM.withInferOnly_eq]
  cases x {before with inferOnly := true} <;> rfl

/-- Combine an existing semantic Hoare proof with an independent policy
frame.  This is the adapter used by K3 callback contexts. -/
theorem strengthenWF
    {I : TcState .anon → Prop} {before : TcState .anon}
    {x : TcM .anon alpha} {Q : alpha → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (hsemantic : TcM.WF I before x Q E)
    (hpolicy : x.PreservesInferOnly) :
    TcM.WF I before x
      (fun value after => Q value after ∧
        after.inferOnly = before.inferOnly)
      (fun err after => E err after ∧
        after.inferOnly = before.inferOnly) := by
  intro hI
  have hpost := hsemantic hI
  cases hrun : x before with
  | ok value after =>
      rw [hrun] at hpost
      exact ⟨hpost.1, hpost.2, hpolicy.ok hrun⟩
  | error err after =>
      rw [hrun] at hpost
      exact ⟨hpost.1, hpost.2, hpolicy.error hrun⟩

/-- Specialize `strengthenWF` to a known policy value and put the policy fact
first, matching the callback records used by full inference. -/
theorem strengthenWFValue
    {I : TcState .anon → Prop} {before : TcState .anon}
    {x : TcM .anon alpha} {Q : alpha → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop} {policy : Bool}
    (hsemantic : TcM.WF I before x Q E)
    (hframe : x.PreservesInferOnly)
    (hbefore : before.inferOnly = policy) :
    TcM.WF I before x
      (fun value after => after.inferOnly = policy ∧ Q value after)
      (fun err after => after.inferOnly = policy ∧ E err after) := by
  exact TcM.WF.mono (strengthenWF hsemantic hframe)
    (fun _ _ post => ⟨post.2.trans hbefore, post.1⟩)
    (fun _ _ post => ⟨post.2.trans hbefore, post.1⟩)

end TcM.PreservesInferOnly

namespace RecM

/-- Writing either inference-cache partition changes only `env`; the policy
selected at `inferWith` entry remains untouched. -/
theorem cacheInferResult_preservesInferOnly
    (inferOnly : Bool) (key : Address × Address) (ty : KExpr .anon)
    (methods : Methods .anon) :
    ((cacheInferResult inferOnly key ty).run methods).PreservesInferOnly := by
  cases inferOnly <;> intro before <;> rfl

/-- The cache-miss tail composes uncached inference with the policy-selected
cache write. -/
private theorem inferMissTail_preservesInferOnly
    (methods : Methods .anon)
    (huncached : ∀ inferOnly source,
      ((inferUncached inferCall inferOnly source).run methods).PreservesInferOnly)
    (inferOnly : Bool) (source : KExpr .anon)
    (key : Address × Address) :
    ((do
      let ty ← inferUncached inferCall inferOnly source
      cacheInferResult inferOnly key ty
      pure ty).run methods).PreservesInferOnly := by
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind (huncached inferOnly source)
  intro ty
  apply TcM.PreservesInferOnly.bind
    (cacheInferResult_preservesInferOnly inferOnly key ty methods)
  intro _
  exact TcM.PreservesInferOnly.pure ty

/-- The production inference cache shell preserves the caller's exact policy
provided its uncached dispatcher does.  Both full and infer-only cache hits,
both misses, key memoization, and the selected cache write are covered. -/
theorem inferWith_preservesInferOnly
    (methods : Methods .anon)
    (huncached : ∀ inferOnly source,
      ((inferUncached inferCall inferOnly source).run methods).PreservesInferOnly)
    (source : KExpr .anon) :
    ((inferWith inferCall source).run methods).PreservesInferOnly := by
  unfold inferWith
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
  intro before
  apply TcM.PreservesInferOnly.bind
    (TcM.PreservesInferOnly.inferKey source)
  intro key
  apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
  intro afterKey
  split
  · exact TcM.PreservesInferOnly.pure _
  · cases hpolicy : before.inferOnly with
    | false =>
        simpa only [Bool.false_eq_true, if_false, pure_bind] using
          inferMissTail_preservesInferOnly methods huncached false source key
    | true =>
        simp only [if_true, pure_bind, ReaderT.run_bind]
        apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
        intro afterFullMiss
        split
        · exact TcM.PreservesInferOnly.pure _
        · exact inferMissTail_preservesInferOnly methods huncached true
            source key

/-- `RecM.infer` is the production cache shell with `inferCall`. -/
theorem infer_preservesInferOnly
    (methods : Methods .anon)
    (huncached : ∀ inferOnly source,
      ((inferUncached inferCall inferOnly source).run methods).PreservesInferOnly)
    (source : KExpr .anon) :
    ((infer source).run methods).PreservesInferOnly := by
  simpa [infer] using inferWith_preservesInferOnly methods huncached source

/-- Local-context cleanup changes only `lctx`; the body frame therefore
survives both normal return and exceptional cleanup. -/
theorem withLctxScope_preservesInferOnly
    {methods : Methods .anon} {x : RecM .anon alpha}
    (hx : (x.run methods).PreservesInferOnly) :
    ((withLctxScope x).run methods).PreservesInferOnly := by
  unfold withLctxScope
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
  intro savedState
  change (tryFinally (x.run methods)
    (modify (fun state : TcState .anon =>
      { state with lctx := state.lctx.truncate savedState.lctx.size }) :
      TcM .anon PUnit)).PreservesInferOnly
  apply TcM.PreservesInferOnly.tryFinally hx
  exact TcM.PreservesInferOnly.modify fun _ => rfl

/-- The WHNF fallback used by Pi exposure preserves the policy whenever the
concrete WHNF layer over the same smaller table does. -/
theorem ensureForallWhnf_preservesInferOnly
    {methods : Methods .anon} {input : KExpr .anon}
    (hwhnf : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly) :
    ((ensureForallWhnf input).run methods).PreservesInferOnly := by
  simp only [ensureForallWhnf, ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind (hwhnf input)
  intro reduced
  cases reduced <;> simp only <;>
    first
    | exact TcM.PreservesInferOnly.pure _
    | exact TcM.PreservesInferOnly.throw _

/-- The syntactic Pi fast path is state-pure; every other constructor uses
the framed WHNF fallback above. -/
theorem ensureForallDirect_preservesInferOnly
    {methods : Methods .anon} {input : KExpr .anon}
    (hwhnf : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly) :
    ((ensureForallDirect input).run methods).PreservesInferOnly := by
  cases input <;> simp only [ensureForallDirect, pure_bind]
  all_goals
    first
    | exact TcM.PreservesInferOnly.pure _
    | exact ensureForallWhnf_preservesInferOnly hwhnf

/-- Sort exposure has the same operational policy shape as Pi exposure. -/
theorem ensureSortWhnf_preservesInferOnly
    {methods : Methods .anon} {input : KExpr .anon}
    (hwhnf : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly) :
    ((ensureSortWhnf input).run methods).PreservesInferOnly := by
  simp only [ensureSortWhnf, ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind (hwhnf input)
  intro reduced
  cases reduced <;> simp only <;>
    first
    | exact TcM.PreservesInferOnly.pure _
    | exact TcM.PreservesInferOnly.throw _

/-- The syntactic sort fast path is state-pure; every other constructor uses
the framed WHNF fallback above. -/
theorem ensureSortDirect_preservesInferOnly
    {methods : Methods .anon} {input : KExpr .anon}
    (hwhnf : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly) :
    ((ensureSortDirect input).run methods).PreservesInferOnly := by
  cases input <;> simp only [ensureSortDirect, pure_bind]
  all_goals
    first
    | exact TcM.PreservesInferOnly.pure _
    | exact ensureSortWhnf_preservesInferOnly hwhnf

end RecM

namespace Methods

/-- Outcome-sensitive policy frames for all six recursive back-edges. -/
structure PreservesInferOnly (methods : Methods .anon) : Prop where
  whnf : ∀ source, (methods.whnf source).PreservesInferOnly
  whnfCore : ∀ source, (methods.whnfCore source).PreservesInferOnly
  whnfMode : ∀ source mode,
    (methods.whnfMode source mode).PreservesInferOnly
  whnfCoreFlags : ∀ source flags,
    (methods.whnfCoreFlags source flags).PreservesInferOnly
  infer : ∀ source, (methods.infer source).PreservesInferOnly
  isDefEq : ∀ left right,
    (methods.isDefEq left right).PreservesInferOnly

/-- One-layer closure obligation for the operational policy frame. -/
def InferOnlyClosed : Prop :=
  ∀ methods, methods.PreservesInferOnly →
    (Methods.next methods).PreservesInferOnly

/-- The exhausted table throws without changing state. -/
theorem methodsOut_preservesInferOnly :
    (methodsOut : Methods .anon).PreservesInferOnly := by
  constructor <;> intros <;> exact TcM.PreservesInferOnly.throw _

/-- A proof for one unfolded layer closes every finite production
approximation selected by `TcM.runRec`. -/
theorem methodsN_preservesInferOnly
    (hclosed : InferOnlyClosed) (n : Nat) :
    (methodsN (m := .anon) n).PreservesInferOnly := by
  induction n with
  | zero => exact methodsOut_preservesInferOnly
  | succ n ih =>
      simpa [Methods.methodsN_succ, Nat.succ_eq_add_one] using
        hclosed (methodsN n) ih

/-- The ordinary K2 DefEq contract plus its independent operational frame is
exactly the strong DefEq callback required by K3 full inference. -/
theorem PreservesInferOnly.isDefEq_full_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {s : TcState .anon} {left right : KExpr .anon}
    {leftV rightV : Lean4Lean.VExpr}
    (hsemantic : Methods.WFAt layer semantics trProj world support uvars
      methods)
    (hframe : methods.PreservesInferOnly)
    (hbefore : s.inferOnly = false)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (methods.isDefEq left right)
      (fun answer after =>
        after.inferOnly = false ∧
          (answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV))
      (fun _ after => after.inferOnly = false) := by
  apply TcM.WF.mono
    (TcM.PreservesInferOnly.strengthenWFValue
      (hsemantic.isDefEq hleftSupport hrightSupport hleft hright)
      (hframe.isDefEq left right) hbefore)
  · intro _ _ post
    exact post
  · intro _ _ post
    exact post.1

end Methods

end Ix.Tc
