import Ix.Tc.Verify.Check.CheckConstExecution

/-!
# Semantic assembly for production `checkConst`

This module joins the real top-level dispatcher to exact coordinated-block
admission.  The success theorem is exhaustive: a routed call yields semantic
block acceptance; an unrouted call is returned as the standalone branch
already covered by K3.

The body certifier is relative to the remaining checker-specific semantic
source: K3 supplies singleton definitions, while E2 supplies inductive and
recursor oracles.  Before invoking it, this module proves that the body's
second block lookup and classifier selected the same ordered members and kind
as the route.  Thus the certifier cannot be applied to a TOCTOU-substituted
block.
-/

namespace Ix.Tc

/-- Stable kernel state plus E0's physical/ghost block-table agreement. -/
structure CoordinatedKernelStateWF (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (state : TcState .anon) : Prop where
  kernel : KernelStateWF semantics trProj world support state
  blocks : LoadedBlocksAgrees world.blocks state.env

namespace CoordinatedKernelStateWF

theorem blockState
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {state : TcState .anon}
    (h : CoordinatedKernelStateWF semantics trProj world support state) :
    BlockStateWF trProj state world :=
  ⟨h.kernel.core, h.blocks⟩

end CoordinatedKernelStateWF

/-- Exhaustive semantic disposition of a successful production call.  The
standalone constructor is intentionally operational: its semantic result is
the existing K3 theorem, with declaration-specific premises. -/
inductive CheckConstSuccessDisposition
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (methods : Methods .anon)
    (id : KId .anon) (before after : TcState .anon) : Prop
  | coordinated {concrete : KConst .anon} {loaded routed : TcState .anon}
      {block : KId .anon} {members : Array (KId .anon)}
      {kind : CheckBlockKind} :
      TcM.getConst id before = .ok concrete loaded →
      (RecM.coordinatedBlockFor concrete).run methods loaded =
        .ok (some block) routed →
      ExactCheckBlock world block members kind →
      id ∈ members →
      CoordinatedBlockAccepted semantics trProj world support methods block id
        routed after →
      CheckConstSuccessDisposition semantics trProj world support methods id
        before after
  | standalone {concrete : KConst .anon} {loaded routed : TcState .anon} :
      TcM.getConst id before = .ok concrete loaded →
      (RecM.coordinatedBlockFor concrete).run methods loaded =
        .ok none routed →
      (RecM.checkConstMemberFresh id).run methods routed = .ok () after →
      CheckConstSuccessDisposition semantics trProj world support methods id
        before after

namespace CheckConstSuccessDisposition

/-- In the coordinated case, the requested declaration itself is trusted in
the admitted world.  The standalone case is excluded explicitly rather than
silently treating member checking as block admission. -/
theorem coordinated_trusted
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {methods : Methods .anon}
    {id : KId .anon} {before after : TcState .anon}
    (h : CheckConstSuccessDisposition semantics trProj world support methods
      id before after)
    (hcoordinated : ∀ {concrete : KConst .anon} {loaded routed : TcState .anon},
      TcM.getConst id before = .ok concrete loaded →
      (RecM.coordinatedBlockFor concrete).run methods loaded =
        .ok none routed → False) :
    ∃ admittedWorld, world ≤ admittedWorld ∧ admittedWorld.trusted id := by
  cases h with
  | @coordinated concrete loaded routed block members kind hget hroute hexact
      hmember haccepted =>
      obtain ⟨admittedWorld, hle, hblock⟩ := haccepted.accepted
      exact ⟨admittedWorld, hle,
        (hexact.rebaseWorld hle).trusted hblock hmember⟩
  | @standalone concrete loaded routed hget hroute hmember =>
      exact False.elim (hcoordinated hget hroute)

end CheckConstSuccessDisposition

namespace RecM

/-- Assemble the real `checkConst` success path.  `certify` is invoked only
after the route's exact block has been matched against the body's actual
lookup and classification. -/
theorem checkConst_success_disposition
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {methods : Methods .anon}
    {id : KId .anon} {before after : TcState .anon}
    (hbefore : CoordinatedKernelStateWF semantics trProj world support before)
    (hexactCatalog : ExactCoordinatedCatalog world)
    (hfault : TcM.LazyFaultPreserves
      (CoordinatedKernelStateWF semantics trProj world support))
    (hfaultBlock : TcM.LazyFaultPreserves
      (fun state => BlockStateWF trProj state world))
    (certify : ∀ {block : KId .anon}
      {members : Array (KId .anon)} {kind : CheckBlockKind}
      {routed bodyAfter : TcState .anon},
      ExactCheckBlock world block members kind →
      id ∈ members →
      ExactBlockBodySuccessTrace methods block id members kind routed
        bodyAfter →
      CertifiedBlockBodySuccess semantics trProj world support methods block
        id members kind routed bodyAfter)
    (hrun : (checkConst id).run methods before = .ok () after) :
    CheckConstSuccessDisposition semantics trProj world support methods id
      before after := by
  cases checkConst_success_trace hrun with
  | coordinated concrete loaded block routed hget hroute hcoordinated =>
      have hgetPost := TcM.getConst_loaded_wf hfault id before hbefore
      rw [hget] at hgetPost
      have hcatalog : world.catalog id = some concrete :=
        hgetPost.1.kernel.core.loaded hgetPost.2
      have hroutePost := coordinatedBlockFor_some_preserves hfault hgetPost.1
        hroute
      obtain ⟨members, kind, hexact, hmember⟩ :=
        coordinatedBlockFor_some_exact hcatalog hexactCatalog
          hgetPost.1.blockState hfaultBlock hroute
      have haccepted := checkCoordinatedBlock_accepted hroutePost.kernel
        (fun {actualMembers} {actualKind} {bodyAfter} trace => by
          cases trace with
          | run bodyLoaded classified hlookup hclassification hclassified =>
              have hlookupPost := TcM.tryGetBlock_wf hfault block routed
                hroutePost
              rw [hlookup] at hlookupPost
              have hphysical := TcM.tryGetBlock_success_loaded hlookup
              have hworldActual := hlookupPost.1.blocks hphysical
              have hmembers : actualMembers = members :=
                Option.some.inj (hworldActual.symm.trans hexact.blockLookup)
              subst actualMembers
              have hkind := classifyBlock_success_exact
                (I := CoordinatedKernelStateWF semantics trProj world support)
                (fun hI => hI.kernel.core.loaded) hfault hexact
                hlookupPost.1 hclassification
              cases hkind.2
              exact certify hexact hmember
                (.run bodyLoaded classified hlookup hclassification hclassified))
        hcoordinated
      exact .coordinated hget hroute hexact hmember haccepted
  | standalone concrete loaded routed hget hroute hmember =>
      exact .standalone hget hroute hmember

end RecM

end Ix.Tc
