import Ix.Tc.Verify.Whnf.Delta.OptionalReduction
import Ix.Tc.Verify.Knot

/-!
# Four-field fixed-universe WHNF closure

The structural, no-delta, full-WHNF, and trusted-delta reducers now expose
fixed-universe contracts.  This module assembles those contracts into the
four K1 fields of one unfolded production method-table layer.

The context retains the exact construction boundary:

* no-delta contexts are supplied for every caller local context;
* the compact symbolic-Nat guard carries its exact optional-reduction
  contract;
* one trusted delta context is shared by those callers;
* arbitrary-flag structural contexts are supplied for the fourth public
  method field.

In particular, the full reducer is constructed with
`FullWhnfStepContext.ofTrustedDelta`; callers cannot replace delta unfolding
with a free successful-reduction oracle.  The `tryNatOffsetStuck` stage added
after the original K1 driver proof remains an explicit closure obligation
until its callbacks and intern operations are decomposed into finite
run-scoped inputs.

## K1 acceptance boundary

`K1ClosureContext.closedAt` below is the K1 closure result: it supplies exactly
the four fixed-universe WHNF fields of `Methods.next`.  It deliberately does
not tie the complete six-method production knot.  That later step also needs
K2's `infer` and `isDefEq` fields before `Methods.ClosedAt.of_parts`,
`Methods.methodsN_wfAt`, and the public runner can be used.

The universally quantified caller context is not assumed well formed merely
to construct `K1ClosureContext`.  Each reducer instead recovers that fact from
the `CtxRecon` component of the runtime invariant at its point of use.  The
concrete successful, absent, stuck, and partial-error executions in
`NatFixture` separately keep the branch contracts inhabited; they are not a
substitute for K2's two missing recursive fields.
-/

namespace Ix.Tc

/-- The final K1 cache composition at the universe count encoded by `keys`:
WHNF expression entries outside, universe-sensitive delta bodies underneath,
and the caller's remaining cache families as the base. -/
def k1CacheSemantics (keys : WhnfContextKeys) (trProj : RawProjRel)
    (fallback : CacheSemantics) : CacheSemantics :=
  whnfCacheSemantics keys trProj
    (unfoldCacheSemantics keys.uvars trProj fallback)

namespace RecM

/-- Complete input family needed to prove the four K1 method-table fields at
one universe count. -/
structure K1ClosureContext
    {alpha : Type} (initial : TcState .anon) (program : TcM .anon alpha)
    (requests : List WalkerRequest) (keys : WhnfContextKeys)
    (fallback : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) : Type where
  noDelta : ∀ Delta : KVLCtx,
    NoDeltaDriverContext initial program requests keys
      (unfoldCacheSemantics keys.uvars trProj fallback)
      trProj world support Delta .FULL
  /-- Exact closure obligation for the compact symbolic-Nat stage introduced
  after the original K1 driver proof. -/
  natOffsetStuck : OptionalReduction.WFAt .noAccel
    (k1CacheSemantics keys trProj fallback) trProj world support
    keys.uvars tryNatOffsetStuck
  delta :
    TrustedDeltaContext initial program requests keys fallback trProj world
      support
  structuralFlags : ∀ (Delta : KVLCtx) (flags : WhnfFlags),
    StructuralCoreContext initial program requests keys
      (unfoldCacheSemantics keys.uvars trProj fallback)
      trProj world support Delta flags

namespace K1ClosureContext

/-- Assemble K1's four fixed-universe fields for one smaller, already
well-formed method table. -/
theorem layer
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {keys : WhnfContextKeys}
    {fallback : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (context : K1ClosureContext initial program requests keys fallback trProj
      world support)
    (methods : Methods .anon)
    (hmethods : Methods.WFAt .noAccel
      (k1CacheSemantics keys trProj fallback)
      trProj world support keys.uvars methods) :
    Methods.WhnfLayerWFAt .noAccel
      (k1CacheSemantics keys trProj fallback)
      trProj world support keys.uvars methods := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Delta s source sourceV hsourceSupport hsource
    let full :=
      FullWhnfStepContext.ofTrustedDelta
        (context.noDelta Delta) context.natOffsetStuck context.delta
    exact
      (FullWhnfStepContext.publicWhnf_wf full hsourceSupport hsource)
        methods hmethods
  · intro Delta s source sourceV hsourceSupport hsource
    let full :=
      FullWhnfStepContext.ofTrustedDelta
        (context.noDelta Delta) context.natOffsetStuck context.delta
    exact
      (FullWhnfStepContext.publicCore_wf full hsourceSupport hsource)
        methods hmethods
  · intro Delta s source sourceV mode hsourceSupport hsource
    let full :=
      FullWhnfStepContext.ofTrustedDelta
        (context.noDelta Delta) context.natOffsetStuck context.delta
    exact
      (FullWhnfStepContext.publicMode_wf full mode hsourceSupport hsource)
        methods hmethods
  · intro Delta s source sourceV flags hsourceSupport hsource
    exact
      (StructuralCoreContext.publicFlags_wf
        (context.structuralFlags Delta flags) hsourceSupport hsource)
        methods hmethods

/-- K1's headline fixed-universe closure result: any semantically valid
smaller method table proves all four WHNF fields of the next production
layer. -/
theorem closedAt
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {keys : WhnfContextKeys}
    {fallback : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (context : K1ClosureContext initial program requests keys fallback trProj
      world support) :
    Methods.WhnfClosedAt .noAccel
      (k1CacheSemantics keys trProj fallback)
      trProj world support keys.uvars := by
  intro methods hmethods
  exact context.layer methods hmethods

end K1ClosureContext
end RecM
end Ix.Tc
