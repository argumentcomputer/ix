import Ix.Tc.Verify.Whnf.Projection.StringExpansion
import Ix.Tc.Ingress

/-!
# Concrete anonymous lazy-ingress refinement

`RuntimeContracts` proves the generic state-on-error plumbing for an arbitrary callback
stored in `TcState.lazyFault`.  Its type cannot establish that the callback
agrees with the immutable catalog, preserves finite intern support, or leaves
semantic caches untouched.

This slice names that missing driver boundary for the actual
`ingressAnonAddrShallow` function.  The refinement is deliberately
outcome-exhaustive: `ok false` (absent input), `ok true` (successful ingress),
and `error` (with its partial environment) all carry the same environment
frame.  A separate installed-hook premise identifies the otherwise arbitrary
function stored in `TcState`.
-/

namespace Ix.Tc

/-- Exact environment facts needed after one lazy-ingress callback.

Constants and blocks may grow and the intern table may grow.  The new loaded
map must still agree with the immutable catalog; intern coherence and the
run's finite support must be re-established.  Semantic caches may not acquire
new entries, and the fvar mint counter must remain fixed so the current local
context stays reconciled. -/
structure LazyIngressEnvFrame (world : VerifyWorld) (support : RunSupport)
    (before after : KEnv .anon) : Prop where
  loaded : LoadedAgrees world.catalog after
  intern : after.intern.WF
  internSupport : support.CoversIntern after.intern
  cacheBack : ∀ {entry}, after.HasCacheEntry entry →
    before.HasCacheEntry entry
  nextFVarId : after.nextFVarId = before.nextFVarId

namespace LazyIngressEnvFrame

/-- No environment change is a valid ingress frame. -/
theorem refl
    {world : VerifyWorld} {support : RunSupport} {env : KEnv .anon}
    (hloaded : LoadedAgrees world.catalog env)
    (hintern : env.intern.WF)
    (hcover : support.CoversIntern env.intern) :
    LazyIngressEnvFrame world support env env where
  loaded := hloaded
  intern := hintern
  internSupport := hcover
  cacheBack := fun h => h
  nextFVarId := rfl

/-- The environment frame preserves the complete fixed-world kernel
invariant.  In particular, cache validity is inherited only after proving
that every post-ingress physical entry was already present before ingress. -/
theorem kernelStateWF
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {before after : KEnv .anon}
    (frame : LazyIngressEnvFrame world support before after)
    {s : TcState .anon}
    (h : KernelStateWF semantics trProj world support s)
    (hbefore : s.env = before) :
    KernelStateWF semantics trProj world support {s with env := after} := by
  subst before
  exact {
    core := {
      trustedCatalog := h.core.trustedCatalog
      loaded := frame.loaded
      intern := frame.intern
    }
    internSupport := frame.internSupport
    caches := fun {_} hentry => h.caches (frame.cacheBack hentry)
    equivalences := h.equivalences
  }

/-- Changing the ingress-owned environment fields leaves the dual concrete
context reconciled.  Only `nextFVarId` is observed by `CtxRecon`. -/
theorem ctxRecon
    {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {trProj : RawProjRel} {Delta : KVLCtx}
    {s : TcState .anon} {after : KEnv .anon} {addr : Address}
    (frame : LazyIngressEnvFrame world support s.env after)
    (h : CtxRecon world.venv uvars world.nameOf trProj s Delta) :
    CtxRecon world.venv uvars world.nameOf trProj
      (TcM.lazyIngressPost s addr after) Delta := by
  refine {
    size_eq := ?_
    recon := ?_
    lwf := ?_
    incr := ?_
    fresh := ?_
    lets := ?_
  }
  · simpa [TcM.lazyIngressPost] using h.size_eq
  · simpa [TcM.lazyIngressPost] using h.recon
  · simpa [TcM.lazyIngressPost] using h.lwf
  · simpa [TcM.lazyIngressPost] using h.incr
  · intro p hp
    have hold := h.fresh p (by
      simpa [TcM.lazyIngressPost] using hp)
    simpa [TcM.lazyIngressPost, frame.nextFVarId] using hold
  · simpa [TcM.lazyIngressPost] using h.lets

/-- One callback outcome preserves the entire K1 invariant, including the
address mark retained by production on both success and failure. -/
theorem whnfStateInv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx}
    {s : TcState .anon} {after : KEnv .anon} {addr : Address}
    (frame : LazyIngressEnvFrame world support s.env after)
    (h : WhnfStateInv layer semantics trProj world support uvars Delta s) :
    WhnfStateInv layer semantics trProj world support uvars Delta
      (TcM.lazyIngressPost s addr after) := by
  refine ⟨?_, frame.ctxRecon h.2.1, ?_⟩
  · exact {
      core := {
        trustedCatalog := h.1.core.trustedCatalog
        loaded := frame.loaded
        intern := frame.intern
      }
      internSupport := frame.internSupport
      caches := fun {_} hentry => h.1.caches (frame.cacheBack hentry)
      equivalences := by
        simpa [TcM.lazyIngressPost] using h.1.equivalences
    }
  · cases layer <;>
      simpa [TcM.lazyIngressPost, WhnfLayer.StateOK] using h.2.2

end LazyIngressEnvFrame

/-- A verified top-level miss is production's exact absent-address outcome:
no conversion, interning, block registration, or partial mutation occurs. -/
theorem ingressAnonAddrShallow_absent
    (ixonEnv : Ixon.Env) (addr : Address) (verify : Bool)
    (before : KEnv .anon)
    (hget : getConstVerified ixonEnv addr verify = .ok none) :
    ingressAnonAddrShallow ixonEnv addr verify before = .ok false before := by
  unfold ingressAnonAddrShallow
  simp [IngressM.liftExcept, hget]
  rfl

/-- Driver-facing refinement of the actual anonymous shallow-ingress
transaction.

This is an input/environment relation, not an axiom and not a consequence of
the callback's function type.  A proof may be constructed from Ixon
materialization/catalog agreement and a finite support census for every node
interned while converting the selected constant or mutual block. -/
structure AnonIngressRefinement (ixonEnv : Ixon.Env) (verify : Bool)
    (world : VerifyWorld) (support : RunSupport) : Prop where
  outcome : ∀ {before : KEnv .anon} {addr : Address},
    LoadedAgrees world.catalog before →
    before.intern.WF →
    support.CoversIntern before.intern →
    match ingressAnonAddrShallow ixonEnv addr verify before with
    | .ok _ after => LazyIngressEnvFrame world support before after
    | .error _ after => LazyIngressEnvFrame world support before after

namespace AnonIngressRefinement

theorem ok
    {ixonEnv : Ixon.Env} {verify : Bool}
    {world : VerifyWorld} {support : RunSupport}
    (refinement : AnonIngressRefinement ixonEnv verify world support)
    {before after : KEnv .anon} {addr : Address} {found : Bool}
    (hloaded : LoadedAgrees world.catalog before)
    (hintern : before.intern.WF)
    (hcover : support.CoversIntern before.intern)
    (hrun : ingressAnonAddrShallow ixonEnv addr verify before =
      .ok found after) :
    LazyIngressEnvFrame world support before after := by
  have h := refinement.outcome (addr := addr) hloaded hintern hcover
  rw [hrun] at h
  exact h

/-- The absent-address result is an explicit specialization of the successful
outcome, rather than being conflated with an ingress error. -/
theorem absent
    {ixonEnv : Ixon.Env} {verify : Bool}
    {world : VerifyWorld} {support : RunSupport}
    (refinement : AnonIngressRefinement ixonEnv verify world support)
    {before after : KEnv .anon} {addr : Address}
    (hloaded : LoadedAgrees world.catalog before)
    (hintern : before.intern.WF)
    (hcover : support.CoversIntern before.intern)
    (hrun : ingressAnonAddrShallow ixonEnv addr verify before =
      .ok false after) :
    LazyIngressEnvFrame world support before after :=
  refinement.ok hloaded hintern hcover hrun

/-- Construct the absent-address frame directly from the verified Ixon miss,
without appealing to the general ingress refinement. -/
theorem absentOfVerifiedMiss
    {ixonEnv : Ixon.Env} {verify : Bool}
    {world : VerifyWorld} {support : RunSupport}
    {before : KEnv .anon} {addr : Address}
    (hloaded : LoadedAgrees world.catalog before)
    (hintern : before.intern.WF)
    (hcover : support.CoversIntern before.intern)
    (hget : getConstVerified ixonEnv addr verify = .ok none) :
    ingressAnonAddrShallow ixonEnv addr verify before = .ok false before ∧
      LazyIngressEnvFrame world support before before :=
  ⟨ingressAnonAddrShallow_absent ixonEnv addr verify before hget,
    LazyIngressEnvFrame.refl hloaded hintern hcover⟩

/-- An ingress error carries the callback's partial post-environment.  The
same frame is required there; no rollback is assumed. -/
theorem error
    {ixonEnv : Ixon.Env} {verify : Bool}
    {world : VerifyWorld} {support : RunSupport}
    (refinement : AnonIngressRefinement ixonEnv verify world support)
    {before after : KEnv .anon} {addr : Address} {err : IngressErr}
    (hloaded : LoadedAgrees world.catalog before)
    (hintern : before.intern.WF)
    (hcover : support.CoversIntern before.intern)
    (hrun : ingressAnonAddrShallow ixonEnv addr verify before =
      .error err after) :
    LazyIngressEnvFrame world support before after := by
  have h := refinement.outcome (addr := addr) hloaded hintern hcover
  rw [hrun] at h
  exact h

/-- Instantiate the generic hook contract from `RuntimeContracts` with the
actual anonymous shallow-ingress function.  `hinstalled` is essential:
`WhnfStateInv` does not otherwise constrain the arbitrary function stored in
`lazyFault`. -/
theorem lazyFaultPreserves
    {ixonEnv : Ixon.Env} {verify : Bool}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx}
    (refinement : AnonIngressRefinement ixonEnv verify world support)
    (hinstalled : ∀ {s : TcState .anon}
        {fault : Address → EStateM String (KEnv .anon) Bool},
      WhnfStateInv layer semantics trProj world support uvars Delta s →
      s.lazyFault = some fault →
      fault = fun addr => ingressAnonAddrShallow ixonEnv addr verify) :
    TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta) := by
  intro s fault addr hlazy hI
  have hfault := hinstalled hI hlazy
  subst fault
  change
    match ingressAnonAddrShallow ixonEnv addr verify s.env with
    | .ok _ after =>
        WhnfStateInv layer semantics trProj world support uvars Delta
          (TcM.lazyIngressPost s addr after)
    | .error _ after =>
        WhnfStateInv layer semantics trProj world support uvars Delta
          (TcM.lazyIngressPost s addr after)
  cases hrun :
      ingressAnonAddrShallow ixonEnv addr verify s.env with
  | ok found after =>
      have frame := refinement.ok hI.1.core.loaded hI.1.core.intern
        hI.1.internSupport hrun
      simpa using frame.whnfStateInv hI
  | error err after =>
      have frame := refinement.error hI.1.core.loaded hI.1.core.intern
        hI.1.internSupport hrun
      simpa using frame.whnfStateInv hI

end AnonIngressRefinement

/-- A driver-owned installation of the concrete anonymous shallow-ingress
hook.  Packaging the Ixon environment and verification mode existentially
keeps reducer contexts independent of those runtime parameters while ruling
out an arbitrary function of the same `lazyFault` type. -/
structure AnonLazyIngressContext (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) : Type where
  ixonEnv : Ixon.Env
  verify : Bool
  refinement : AnonIngressRefinement ixonEnv verify world support
  installed : ∀ {uvars : Nat} {Delta : KVLCtx}
      {s : TcState .anon}
      {fault : Address → EStateM String (KEnv .anon) Bool},
    WhnfStateInv layer semantics trProj world support uvars Delta s →
    s.lazyFault = some fault →
    fault = fun addr => ingressAnonAddrShallow ixonEnv addr verify

namespace AnonLazyIngressContext

/-- The installed production hook preserves the complete fixed-world
invariant for every universe count and local context used by the driver. -/
theorem preserves
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    (context : AnonLazyIngressContext layer semantics trProj world support)
    {uvars : Nat} {Delta : KVLCtx} :
    TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta) :=
  context.refinement.lazyFaultPreserves
    (context.installed (uvars := uvars) (Delta := Delta))

end AnonLazyIngressContext

namespace RecM.ProjectionHelper

/-- The concrete `.noAccel` projection helper for an anonymous driver hook.
The String-constructor transaction is supplied by StringExpansion's finite plans; this
slice supplies the exact shallow-ingress callback on every state where a hook
is installed. -/
theorem noAccelOfAnonIngress
    {ixonEnv : Ixon.Env} {verify : Bool}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (hinputs : WhnfCoreInputSupport support)
    (refinement : AnonIngressRefinement ixonEnv verify world support)
    (hinstalled : ∀ {uvars : Nat} {Delta : KVLCtx}
        {s : TcState .anon}
        {fault : Address → EStateM String (KEnv .anon) Bool},
      WhnfStateInv .noAccel semantics trProj world support uvars Delta s →
      s.lazyFault = some fault →
      fault = fun addr => ingressAnonAddrShallow ixonEnv addr verify)
    (strings : ProjectionStringPlanContext trProj world support) :
    ProjectionHelper.WF .noAccel semantics trProj world support :=
  ProjectionHelper.noAccelOfStringPlans hinputs
    (fun uvars Delta =>
      refinement.lazyFaultPreserves
        (hinstalled (uvars := uvars) (Delta := Delta)))
    strings

end RecM.ProjectionHelper

end Ix.Tc
