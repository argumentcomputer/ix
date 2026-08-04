import Ix.Tc.Verify.DefEq

/-!
# Finite suffix model for closed checker states

Closed public inputs take the real `ctxAddrForLbr` fast path for every loose
bound-variable radius.  Their normalized semantic suffix input is therefore
just the reconciled ghost context, which is `[]`; the finite digest scope is
a singleton and its collision theorem is constructive.

This is a production instantiation, not a mock key oracle: `execution` is
proved from `TcM.ctxAddrForLbr_empty`, and the model's state predicate fixes
the concrete fields needed to derive the empty reconciliation.
-/

namespace Ix.Tc

/-- Concrete eager checker states with no legacy/opened local bindings and
no driver-owned lazy-ingress hook. -/
structure ClosedContextState (s : TcState .anon) : Prop where
  ctx : s.ctx = #[]
  letVals : s.letVals = #[]
  numLetBindings : s.numLetBindings = 0
  lctx : s.lctx = {}
  lazyFault : s.lazyFault = none

namespace ClosedContextState

/-- A suffix memo update cannot open a local context. -/
theorem contextKeyFrame {before after : TcState .anon}
    (hbefore : ClosedContextState before)
    (hframe : ContextKeyFrame before after) :
    ClosedContextState after := by
  rw [hframe]
  exact {
    ctx := hbefore.ctx
    letVals := hbefore.letVals
    numLetBindings := hbefore.numLetBindings
    lctx := hbefore.lctx
    lazyFault := hbefore.lazyFault }

/-- Digest-neutral cache/intern updates retain closedness. -/
theorem contextDigestFrame {before after : TcState .anon}
    (hbefore : ClosedContextState before)
    (hframe : ContextDigestFrame before after) :
    ClosedContextState after where
  ctx := hframe.ctx.trans hbefore.ctx
  letVals := hframe.letVals.trans hbefore.letVals
  numLetBindings := hframe.numLetBindings.trans hbefore.numLetBindings
  lctx := hframe.lctx.trans hbefore.lctx
  lazyFault := hframe.lazyFault.trans hbefore.lazyFault

/-- Reconciliation from a concretely closed state has exactly the empty
semantic local context. -/
theorem delta_eq_nil
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {s : TcState .anon} {Delta : KVLCtx}
    (hclosed : ClosedContextState s)
    (hctx : CtxRecon env uvars nameOf trProj s Delta) :
    Delta = [] := by
  have hrecon := hctx.recon
  rw [hclosed.ctx, hclosed.letVals, hclosed.lctx] at hrecon
  cases hrecon
  rfl

end ClosedContextState

namespace ClosedContextDigest

/-- Exact normalized input for the closed-context production path.  The
radius is intentionally erased: with no legacy frames every request denotes
the same empty semantic suffix. -/
def spec (trProj : RawProjRel) (world : VerifyWorld) (uvars : Nat) :
    ContextDigestSpec trProj world uvars where
  Input := KVLCtx
  inputOf := fun _ Delta => Delta
  digest := fun _ => emptyCtxAddr
  StateValid := ClosedContextState
  memoValid := by
    intro s hclosed lbr cached hactive hlookup
    simp [hclosed.ctx] at hactive
  preserves := by
    intro before after lbr ctxAddr hclosed hrun
    exact hclosed.contextKeyFrame (TcM.ctxAddrForLbr_frame hrun)
  framePreserves := by
    intro before after hclosed hframe
    exact hclosed.contextDigestFrame hframe
  execution := by
    intro before after lbr ctxAddr Delta hclosed hctx hrun
    have hempty : before.ctx.isEmpty = true := by
      simp [hclosed.ctx]
    have heval := TcM.ctxAddrForLbr_empty hempty lbr
    rw [heval] at hrun
    injection hrun

/-- The one normalized context input reachable from a closed state. -/
def scope {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat} :
    ContextDigestScope (spec trProj world uvars) where
  entries := [[]]

/-- A singleton composite-input scope is collision-free independently of the
expression/universe address assumptions. -/
theorem scope_collisionFree
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat} :
    (scope (trProj := trProj) (world := world) (uvars := uvars)).CollisionFree := by
  intro left right hleft hright hdigest
  simp [ContextDigestScope.Contains, scope] at hleft hright
  subst left
  subst right
  rfl

/-- Every possible suffix-key request from a closed reconciled state lands in
the singleton normalized-input scope. -/
theorem scope_captures
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {s : TcState .anon} (hclosed : ClosedContextState s) :
    (scope (trProj := trProj) (world := world) (uvars := uvars)).Captures s := by
  intro after lbr ctxAddr Delta hctx hrun
  have hDelta : Delta = [] := hclosed.delta_eq_nil hctx
  subst Delta
  simp only [ContextDigestScope.Contains, scope, spec]
  exact List.mem_cons_self

/-- Equality of normalized closed-context inputs is literal context equality,
so every semantic judgment transports by substitution. -/
def suffixSemantics
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat} :
    ContextSuffixSemantics (spec trProj world uvars) where
  whnf hinput hmeaning := by
    cases hinput
    exact hmeaning
  infer hinput hmeaning := by
    cases hinput
    exact hmeaning
  defEq hinput hmeaning := by
    cases hinput
    exact hmeaning
  isProp hinput hmeaning := by
    cases hinput
    exact hmeaning

/-- The concrete finite model used by closed positive-fuel executions. -/
def model (trProj : RawProjRel) (world : VerifyWorld) (uvars : Nat) :
    ScopedKernelSuffixModel trProj world :=
  ScopedKernelSuffixModel.finiteOperational (spec trProj world uvars)
    scope scope_collisionFree suffixSemantics

/-- Closedness supplies both parts of the finite model's state-domain
witness: production-state validity and singleton input capture. -/
theorem model_stateInScope
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {s : TcState .anon} (hclosed : ClosedContextState s) :
    (model trProj world uvars).StateInScope s :=
  ⟨hclosed, scope_captures hclosed⟩

/-- Membership in the concrete closed-state domain rules out lazy ingress. -/
theorem model_noLazy
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {s : TcState .anon}
    (hscope : (model trProj world uvars).StateInScope s) :
    s.lazyFault = none :=
  hscope.1.lazyFault

/-- The concrete closed model satisfies the driver's lazy-ingress contract
constructively: an in-scope state cannot contain a hook. -/
theorem model_lazyFaultPreserves
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {layer : WhnfLayer} {support : RunSupport} {Delta : KVLCtx} :
    TcM.LazyFaultPreserves
      (ScopedWhnfStateInv (model trProj world uvars) layer
        (kernelCacheSemantics (model trProj world uvars).keys trProj)
        support Delta) :=
  TcM.LazyFaultPreserves.of_none fun hI => model_noLazy hI.2

/-- Production reset writes exactly the closed-context fields required by
the singleton suffix model, so it returns every in-scope input to the same
finite state domain. -/
theorem model_resetPreservesScope
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat} :
    (model trProj world uvars).ResetPreservesScope := by
  intro before after hbefore hrun
  have hnoLazy := model_noLazy hbefore
  have hclosed : ClosedContextState after := by
    unfold TcM.reset at hrun
    injection hrun with hafter
    subst after
    constructor <;> try rfl
    exact hnoLazy
  exact model_stateInScope hclosed

end ClosedContextDigest

end Ix.Tc
