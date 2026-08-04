import Ix.Tc.Verify.Check.PublicBlocks
import Ix.Tc.Verify.Check.PublicStandalone
import Ix.Tc.Verify.Driver.Serial

/-!
# Supported production-checker acceptance

This module is the concrete adapter between the per-call K3/E0 theorems and
E1's serial checked-set composition.  It intentionally does not contain an
opaque `checkConst succeeded, therefore the declaration is sound` callback.
Instead, every reusable successful call must expose:

* one finite, run-scoped recursive-method context;
* the exact physical/world cache and block-table invariants for that call;
* agreement between the source work item and the block selected by the
  production router;
* declaration-local K3 resources for an observed standalone route; and
* either constructive scoped singleton-definition evidence or an explicit
  E2 oracle-backed resource for every fresh coordinated body;
* certificate-backed replay resources for coordinated blocks whose semantic
  entries are already installed in the current Theory environment.

The composition theorems below turn those resources into `CheckSuccessSound`,
which `Driver.Serial` then composes into `SubjectWF`.
The source-to-kernel route agreement remains an explicit representation
premise until the later ingress/refinement phase discharges it generically.
-/

namespace Ix.Tc

namespace AnonWorkItem

/-- Exact relation between a production work item and the result observed
from `coordinatedBlockFor`.  A standalone source entry may be checked either
through K3 (axioms) or through its singleton coordinated block
(definitions/recursors).  A Muts work item must route to its advertised
envelope address. -/
def SelectedBlockMatches (item : AnonWorkItem) :
    Option (KId .anon) → Prop
  | selected => match item with
    | .standalone _ => True
    | .block blockAddr _ _ =>
        selected = some (⟨blockAddr, ()⟩ : KId .anon)

end AnonWorkItem

/-! ## Standalone K3 resources -/

/-- The declaration-local premises needed when the actual production router
selects K3's standalone path.  None of these fields assumes a declaration-WF
transition or target trust; `PendingDecl` explicitly asserts the opposite. -/
structure SupportedStandaloneResources
    {initial : TcState .anon} {id : KId .anon}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (context : ScopedRecursiveMethodRunContext initial (TcM.checkConst id)
      requests trProj world support)
    (concrete : KConst .anon) : Type where
  pipelines : ScopedStandalonePipelineResources context.model support
    (context.calls (initial.recFuel.toNat + 1))
    (Ix.Tc.methodsN (m := .anon) initial.recFuel.toNat)
  decl : Lean4Lean.VDecl
  projection : trProj.SubstCompatible
  literals : ∀ literal, world.venv.ContainsLits literal
  pending : PendingDecl trProj world id decl
  catalog : world.catalog id = some concrete
  validation : StandaloneValidationResources support concrete
  covered : pipelines.Covers concrete
  collision : support.CollisionFree
  uvars : context.model.keys.uvars = concrete.lvls.toNat
  resetScope : context.model.ResetPreservesScope
  route : StandaloneRoute
    (ScopedWhnfStateInv context.model .noAccel
      (kernelCacheSemantics context.model.keys trProj) support [])
    (Ix.Tc.methodsN (m := .anon) initial.recFuel.toNat) concrete

namespace SupportedStandaloneResources

/-- Apply K3 to the exact successful public call and retain only the world
extension and target-trust facts required by E1. -/
theorem promotes
    {initial after : TcState .anon} {id : KId .anon}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {context : ScopedRecursiveMethodRunContext initial (TcM.checkConst id)
      requests trProj world support}
    {concrete : KConst .anon}
    (resources : SupportedStandaloneResources context concrete)
    (hI : ScopedWhnfStateInv context.model .noAccel
      (kernelCacheSemantics context.model.keys trProj) support [] initial)
    (hfault : TcM.LazyFaultPreserves
      (ScopedWhnfStateInv context.model .noAccel
        (kernelCacheSemantics context.model.keys trProj) support []))
    (hrun : TcM.checkConst id initial = .ok () after) :
    ∃ world', world ≤ world' ∧ world'.trusted id := by
  have hresult := TcM.checkConst.wf context resources.pipelines
    resources.projection resources.literals resources.pending
    resources.catalog resources.validation resources.covered
    resources.collision resources.uvars resources.resetScope resources.route
    hI hfault hrun
  obtain ⟨world', hpromotes, _hpost, _hscope, _htrusted⟩ := hresult.2
  exact ⟨world', hpromotes.1, hpromotes.2 rfl⟩

end SupportedStandaloneResources

/-! ## Coordinated-body resources -/

/-- Exhaustive body evidence supported by the E3-S adapter.

The first constructor is constructive K3 evidence for the only definition
block shape currently modeled atomically by Lean4Lean: one definition.  The
second constructor keeps the E2 inductive/recursor oracle visible.  In
particular there is no constructor containing a prebuilt
`CertifiedBlockBodySuccess`. -/
inductive SupportedBlockBodyResources
    {initial : TcState .anon} {id : KId .anon}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (context : ScopedRecursiveMethodRunContext initial (TcM.checkConst id)
      requests trProj world support) :
    (block requested : KId .anon) → Array (KId .anon) → CheckBlockKind →
      TcState .anon → TcState .anon → Prop
  | singletonDefinition
      {block requested member : KId .anon} {concrete : KConst .anon}
      {decl : Lean4Lean.VDecl} {before after : TcState .anon}
      (pipelines : ScopedStandalonePipelineResources context.model support
        (context.calls (initial.recFuel.toNat + 1))
        (Ix.Tc.methodsN (m := .anon) initial.recFuel.toNat))
      (projection : trProj.SubstCompatible)
      (literals : ∀ literal, world.venv.ContainsLits literal)
      (pending : PendingDecl trProj world member decl)
      (catalog : world.catalog member = some concrete)
      (validation : StandaloneValidationResources support concrete)
      (covered : pipelines.Covers concrete)
      (collision : support.CollisionFree)
      (uvars : context.model.keys.uvars = concrete.lvls.toNat)
      (resetScope : context.model.ResetPreservesScope)
      (initialInv : ScopedWhnfStateInv context.model .noAccel
        (kernelCacheSemantics context.model.keys trProj) support [] before)
      (lazyFault : TcM.LazyFaultPreserves
        (ScopedWhnfStateInv context.model .noAccel
          (kernelCacheSemantics context.model.keys trProj) support []))
      (blocksAfter : LoadedBlocksAgrees world.blocks after.env) :
      SupportedBlockBodyResources context block requested #[member] .defn
        before after
  | oracleBacked
      {block requested : KId .anon} {members : Array (KId .anon)}
      {kind : CheckBlockKind} {before after : TcState .anon}
      (resources : OracleBackedBlockResources
        (kernelCacheSemantics context.model.keys trProj) trProj world support
        members kind after) :
      SupportedBlockBodyResources context block requested members kind before
        after

namespace SupportedBlockBodyResources

/-- Turn one transparent supported-body constructor into the exact E0 body
certificate for the observed trace. -/
theorem certify
    {initial : TcState .anon} {id : KId .anon}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {context : ScopedRecursiveMethodRunContext initial (TcM.checkConst id)
      requests trProj world support}
    {block requested : KId .anon} {members : Array (KId .anon)}
    {kind : CheckBlockKind} {before after : TcState .anon}
    (resources : SupportedBlockBodyResources context block requested members
      kind before after)
    (hexact : ExactCheckBlock world block members kind)
    (trace : RecM.ExactBlockBodySuccessTrace
      (Ix.Tc.methodsN (m := .anon) initial.recFuel.toNat)
      block requested members kind before after) :
    CertifiedBlockBodySuccess
      (kernelCacheSemantics context.model.keys trProj) trProj world support
      (Ix.Tc.methodsN (m := .anon) initial.recFuel.toNat)
      block requested members kind before after := by
  cases resources with
  | singletonDefinition pipelines projection literals pending catalog
      validation covered collision uvars resetScope initialInv lazyFault
      blocksAfter =>
      let methods := Ix.Tc.methodsN (m := .anon) initial.recFuel.toNat
      have hmethods : Methods.ScopedWFAtOn context.model .noAccel
          (kernelCacheSemantics context.model.keys trProj) support
          (context.calls (initial.recFuel.toNat + 1))
          (Methods.next methods) := by
        simpa [methods] using context.schedule.nextSelected
      have hpolicy : (Methods.next methods).PreservesInferOnly :=
        Methods.next_preservesInferOnly methods
          (Methods.methodsN_concrete_preservesInferOnly
            initial.recFuel.toNat)
      simpa [methods] using RecM.certifySingletonDefinitionScoped pipelines
        hmethods hpolicy projection literals pending catalog validation
        covered collision uvars resetScope hexact trace initialInv lazyFault
        blocksAfter
  | oracleBacked oracle =>
      exact RecM.certifyOracleBackedBlock trace hexact oracle

end SupportedBlockBodyResources

/-! ## Certificate-backed coordinated-block replay -/

namespace CheckBlockKind

/-- Kinds which E3-S may replay from already-installed semantic entries.
Definitions remain on the constructive K3 route; this adapter is only for
inductive-family and generated-recursor blocks. -/
def CertificateBacked : CheckBlockKind → Prop
  | .inductive' | .recursor => True
  | .defn => False

end CheckBlockKind

/-- A coordinated block whose complete semantic entries are already installed
in `world.venv`.

This is the reusable E3-S form of E2's fixed semantic certificates. Unlike an
`ExistingSemanticBlockCertificate`, it deliberately has no freshness premise:
checked-set composition may replay a block in a monotone world which already
trusts a proper subset of its exact members. Admission is therefore the
idempotent union of the exact member array with the current trusted set.

The resource cannot certify definitions, cannot choose a future Theory
environment, and cannot select a residual member predicate. Every member must
instead carry the same declaration/rule/pattern provenance consumed by trusted
catalog lookups in the current environment. -/
structure CertificateBackedBlockResources (world : VerifyWorld)
    (blockAddr primary : Address) (targets : Array Address) : Type where
  trProj : RawProjRel
  members : Array (KId .anon)
  kind : CheckBlockKind
  certificateBacked : kind.CertificateBacked
  exactBlock : ExactCheckBlock world (⟨blockAddr, ()⟩ : KId .anon)
    members kind
  workCatalog : (AnonWorkItem.block blockAddr primary targets)
    |>.MatchesBlockCatalog world.blocks
  entry : ∀ {id}, id ∈ members →
    TrustedCatalogEntry trProj world.catalog world.nameOf world.venv id

namespace CertificateBackedBlockResources

/-- Trust the exact certified member array while leaving the installed Theory
environment and every immutable representation component unchanged. -/
def admittedWorld
    {world : VerifyWorld} {blockAddr primary : Address}
    {targets : Array Address}
    (resources : CertificateBackedBlockResources world blockAddr primary
      targets) : VerifyWorld where
  catalog := world.catalog
  blocks := world.blocks
  trusted := fun id => id ∈ resources.members ∨ world.trusted id
  venv := world.venv
  nameOf := world.nameOf
  venvWF := world.venvWF
  trustedCatalogued := by
    intro id htrusted
    change id ∈ resources.members ∨ world.trusted id at htrusted
    rcases htrusted with hmember | hold
    · obtain ⟨concrete, _, _, hcatalog, _, _⟩ :=
        (resources.entry hmember).lookup
      exact ⟨concrete, hcatalog⟩
    · exact world.trustedCatalogued hold

/-- The replay trust delta is exactly the fixed physical member array. -/
@[simp] theorem admittedWorld_trusted_iff
    {world : VerifyWorld} {blockAddr primary : Address}
    {targets : Array Address}
    (resources : CertificateBackedBlockResources world blockAddr primary
      targets) (id : KId .anon) :
    resources.admittedWorld.trusted id ↔
      id ∈ resources.members ∨ world.trusted id :=
  Iff.rfl

/-- An unrelated declaration cannot ride along with certificate replay. -/
theorem newlyTrustedMember
    {world : VerifyWorld} {blockAddr primary : Address}
    {targets : Array Address}
    (resources : CertificateBackedBlockResources world blockAddr primary
      targets) {id : KId .anon}
    (hafter : resources.admittedWorld.trusted id)
    (hbefore : ¬world.trusted id) : id ∈ resources.members := by
  rcases (resources.admittedWorld_trusted_iff id).1 hafter with
    hmember | hold
  · exact hmember
  · exact False.elim (hbefore hold)

/-- Certificate replay is a monotone, environment-preserving world
extension. -/
theorem le_admittedWorld
    {world : VerifyWorld} {blockAddr primary : Address}
    {targets : Array Address}
    (resources : CertificateBackedBlockResources world blockAddr primary
      targets) :
    world ≤ resources.admittedWorld :=
  ⟨rfl, rfl, rfl, fun {_} hold => Or.inr hold, Lean4Lean.VEnv.LE.rfl⟩

/-- Reindex installed semantic entries across an arbitrary monotone current
world. This is the reusable bridge used by E1 after prior work items have
possibly trusted a proper subset of this block. -/
def rebaseWorld
    {before current : VerifyWorld} {blockAddr primary : Address}
    {targets : Array Address}
    (resources : CertificateBackedBlockResources before blockAddr primary
      targets) (hle : before ≤ current) :
    CertificateBackedBlockResources current blockAddr primary targets where
  trProj := resources.trProj
  members := resources.members
  kind := resources.kind
  certificateBacked := resources.certificateBacked
  exactBlock := resources.exactBlock.rebaseWorld hle
  workCatalog := by
    simpa only [← hle.blocks] using resources.workCatalog
  entry := by
    intro id hmember
    simpa only [← hle.catalog, ← hle.nameOf] using
      TrustedCatalogEntry.mono hle.venv (resources.entry hmember)

/-- Replay admits the full exact block and recovers the complete work-item
predicate. Already trusted members are retained by the old-trust disjunct;
missing members enter through their fixed certificate entries. -/
theorem accepts
    {world : VerifyWorld} {blockAddr primary : Address}
    {targets : Array Address}
    (resources : CertificateBackedBlockResources world blockAddr primary
      targets) :
    ∃ admittedWorld, world ≤ admittedWorld ∧
      WorkItemAccepted admittedWorld
        (.block blockAddr primary targets) := by
  let admittedWorld := resources.admittedWorld
  have hle : world ≤ admittedWorld := resources.le_admittedWorld
  have htrusted : ∀ id, id ∈ resources.members →
      admittedWorld.trusted id := by
    intro id hmember
    exact Or.inl hmember
  have haccepted : admittedWorld.AcceptedBlock
      (⟨blockAddr, ()⟩ : KId .anon) := by
    refine ⟨resources.members, ?_, resources.exactBlock.nonempty,
      htrusted⟩
    exact resources.exactBlock.blockLookup
  refine ⟨admittedWorld, hle, haccepted, ?_⟩
  obtain ⟨workMembers, hworkBlock, _hnonempty, _hprimary, htargets⟩ :=
    resources.workCatalog.block_targets
  have hmembers : workMembers = resources.members :=
    Option.some.inj
      (hworkBlock.symm.trans resources.exactBlock.blockLookup)
  subst workMembers
  intro addr haddr
  rw [htargets] at haddr
  obtain ⟨member, hmember, hmemberAddr⟩ := Array.mem_map.mp haddr
  have hmemberTrusted := htrusted member hmember
  have hid : (⟨member.addr, ()⟩ : KId .anon) = member := by
    cases member with
    | mk memberAddr memberName => cases memberName; rfl
  rw [← hmemberAddr, hid]
  exact hmemberTrusted

end CertificateBackedBlockResources

/-! ## One reusable production call -/

/-- Complete non-semantic resources for reinterpreting one successful serial
checker call in a particular current ghost world.  The world may differ from
the runtime serial order: cache provenance therefore has to be re-established
for this exact `initial` state, rather than inferred from a result bit.

`routeMatches` is the explicit Ixon-to-kernel representation seam.  It says
only which physical block the observed production router selected; it grants
no typing or trust fact. -/
structure SupportedCheckRun (world : VerifyWorld) (item : AnonWorkItem)
    (initial : TcState .anon) : Type where
  requests : List WalkerRequest
  trProj : RawProjRel
  support : RunSupport
  context : ScopedRecursiveMethodRunContext initial
    (TcM.checkConst (⟨item.primary, ()⟩ : KId .anon)) requests trProj world
    support
  initialInv : ScopedWhnfStateInv context.model .noAccel
    (kernelCacheSemantics context.model.keys trProj) support [] initial
  loadedBlocks : LoadedBlocksAgrees world.blocks initial.env
  scopedLazyFault : TcM.LazyFaultPreserves
    (ScopedWhnfStateInv context.model .noAccel
      (kernelCacheSemantics context.model.keys trProj) support [])
  coordinatedLazyFault : TcM.LazyFaultPreserves
    (CoordinatedKernelStateWF
      (kernelCacheSemantics context.model.keys trProj) trProj world support)
  blockLazyFault : TcM.LazyFaultPreserves
    (fun state => BlockStateWF trProj state world)
  exactCatalog : ExactCoordinatedCatalog world
  workCatalog : item.MatchesBlockCatalog world.blocks
  routeMatches : ∀ {concrete : KConst .anon} {loaded routed : TcState .anon}
      {selected : Option (KId .anon)},
    TcM.getConst (⟨item.primary, ()⟩ : KId .anon) initial =
        .ok concrete loaded →
    (RecM.coordinatedBlockFor concrete).run
        (Ix.Tc.methodsN (m := .anon) initial.recFuel.toNat) loaded =
        .ok selected routed →
    item.SelectedBlockMatches selected
  standalone : ∀ {concrete : KConst .anon} {loaded routed : TcState .anon},
    TcM.getConst (⟨item.primary, ()⟩ : KId .anon) initial =
        .ok concrete loaded →
    (RecM.coordinatedBlockFor concrete).run
        (Ix.Tc.methodsN (m := .anon) initial.recFuel.toNat) loaded =
        .ok none routed →
    SupportedStandaloneResources context concrete
  blockBody : ∀ {block : KId .anon} {members : Array (KId .anon)}
      {kind : CheckBlockKind} {routed bodyAfter : TcState .anon},
    ExactCheckBlock world block members kind →
    (⟨item.primary, ()⟩ : KId .anon) ∈ members →
    RecM.ExactBlockBodySuccessTrace
      (Ix.Tc.methodsN (m := .anon) initial.recFuel.toNat)
      block (⟨item.primary, ()⟩ : KId .anon) members kind routed
        bodyAfter →
    SupportedBlockBodyResources context block
      (⟨item.primary, ()⟩ : KId .anon) members kind routed bodyAfter

namespace SupportedCheckRun

/-- K3/E0 assembly for one actual successful production call. -/
theorem accepts
    {world : VerifyWorld} {item : AnonWorkItem}
    {initial after : TcState .anon}
    (resources : SupportedCheckRun world item initial)
    (hrun : TcM.checkConst (⟨item.primary, ()⟩ : KId .anon) initial =
      .ok () after) :
    ∃ admittedWorld, world ≤ admittedWorld ∧
      WorkItemAccepted admittedWorld item := by
  have hcoordinated : CoordinatedKernelStateWF
      (kernelCacheSemantics resources.context.model.keys resources.trProj)
      resources.trProj world resources.support initial :=
    ⟨resources.initialInv.1.1, resources.loadedBlocks⟩
  have hdisposition := TcM.checkConst.blockDisposition hcoordinated
    resources.exactCatalog resources.coordinatedLazyFault
    resources.blockLazyFault
    (fun hexact hmember trace =>
      (resources.blockBody hexact hmember trace).certify hexact trace)
    hrun
  cases item with
  | standalone addr =>
      cases hdisposition with
      | @coordinated concrete loaded routed block members kind hget hroute
          hexact hmember haccepted =>
          obtain ⟨admittedWorld, hle, hblock⟩ := haccepted.accepted
          exact ⟨admittedWorld, hle,
            (hexact.rebaseWorld hle).trusted hblock hmember⟩
      | @standalone concrete loaded routed hget hroute hmember =>
          have hresources := resources.standalone hget hroute
          obtain ⟨admittedWorld, hle, htrusted⟩ :=
            hresources.promotes resources.initialInv
              resources.scopedLazyFault hrun
          exact ⟨admittedWorld, hle, htrusted⟩
  | block blockAddr primary targets =>
      cases hdisposition with
      | @coordinated concrete loaded routed block members kind hget hroute
          hexact hmember haccepted =>
          have hselected := resources.routeMatches hget hroute
          change (some block : Option (KId .anon)) =
            some (⟨blockAddr, ()⟩ : KId .anon) at hselected
          have hblockEq : block = (⟨blockAddr, ()⟩ : KId .anon) :=
            Option.some.inj hselected
          subst block
          obtain ⟨workMembers, hworkBlock, _hnonempty, _hprimary,
              htargets⟩ := resources.workCatalog.block_targets
          have hmembers : workMembers = members :=
            Option.some.inj (hworkBlock.symm.trans hexact.blockLookup)
          subst workMembers
          obtain ⟨admittedWorld, hle, hblock⟩ := haccepted.accepted
          refine ⟨admittedWorld, hle, hblock, ?_⟩
          intro addr haddr
          rw [htargets] at haddr
          obtain ⟨member, hmemberArray, hmemberAddr⟩ :=
            Array.mem_map.mp haddr
          have htrusted :=
            (hexact.rebaseWorld hle).trusted hblock hmemberArray
          have hid : (⟨member.addr, ()⟩ : KId .anon) = member := by
            cases member with
            | mk memberAddr memberName => cases memberName; rfl
          rw [← hmemberAddr, hid]
          exact htrusted
      | @standalone concrete loaded routed hget hroute hmember =>
          have hselected := resources.routeMatches hget hroute
          change (none : Option (KId .anon)) =
            some (⟨blockAddr, ()⟩ : KId .anon) at hselected
          contradiction

end SupportedCheckRun

/-! ## Reusable fragment and E1 composition -/

/-- Exhaustive semantic resources accepted by the supported-fragment
adapter. `operational` is the full K3/E0 state-and-cache route.
`certificateBackedBlock` is the narrower E2 replay route for
inductive/recursor blocks whose complete semantic entries are already
installed; it does not manufacture a standalone recursive-method context or
an oracle-selected future world. -/
inductive SupportedCheckEvidence (world : VerifyWorld) :
    AnonWorkItem → TcState .anon → Type
  | operational {item initial} :
      SupportedCheckRun world item initial →
      SupportedCheckEvidence world item initial
  | certificateBackedBlock {blockAddr primary targets initial} :
      CertificateBackedBlockResources world blockAddr primary targets →
      SupportedCheckEvidence world (.block blockAddr primary targets) initial

namespace SupportedCheckEvidence

theorem accepts
    {world : VerifyWorld} {item : AnonWorkItem}
    {initial after : TcState .anon}
    (evidence : SupportedCheckEvidence world item initial)
    (hrun : TcM.checkConst (⟨item.primary, ()⟩ : KId .anon) initial =
      .ok () after) :
    ∃ admittedWorld, world ≤ admittedWorld ∧
      WorkItemAccepted admittedWorld item := by
  cases evidence with
  | operational resources => exact resources.accepts hrun
  | certificateBackedBlock resources => exact resources.accepts

end SupportedCheckEvidence

/-! ## Oracle-free certificate-backed fragments -/

/-- Exact all-block evidence used when every row in a fragment is backed by
already-installed semantic entries. Keeping this narrow evidence separate
from `SupportedCheckEvidence` gives all-block consumers a dependency path
which cannot reach the operational oracle-backed E0 branch. -/
inductive CertificateBackedCheckEvidence (world : VerifyWorld) :
    AnonWorkItem → Type
  | block {blockAddr primary targets} :
      CertificateBackedBlockResources world blockAddr primary targets →
      CertificateBackedCheckEvidence world
        (.block blockAddr primary targets)

namespace CertificateBackedCheckEvidence

/-- Interpret an exact certificate-backed row without consulting the runtime
result as semantic authority. The successful result remains a gate in the
surrounding `CheckSuccessSound` interface. -/
theorem accepts
    {world : VerifyWorld} {item : AnonWorkItem}
    (evidence : CertificateBackedCheckEvidence world item) :
    ∃ admittedWorld, world ≤ admittedWorld ∧
      WorkItemAccepted admittedWorld item := by
  cases evidence with
  | block resources => exact resources.accepts

end CertificateBackedCheckEvidence

/-- A precisely scoped all-block fragment provider. Resources are requested
only for a still-pending row at an arbitrary monotone current world, exactly as
in `SupportedCheckFragment`, but the evidence surface admits only fixed
certificate-backed blocks. -/
structure CertificateBackedCheckFragment (baseline : VerifyWorld)
    (catalog : DependencyCatalog) (work : Array AnonWorkItem) : Type where
  resources : ∀ item, item ∈ work →
    ∀ {before : AnonCheckLoopState} {checker : TcState .anon},
      (TcM.checkConst
        (⟨item.primary, ()⟩ : KId .anon)).run before.checker =
          .ok () checker →
      ∀ current, baseline ≤ current →
        (∀ {target}, catalog.dependsOn item.root target →
          catalog.blockOf target ≠ item.root →
          current.AcceptsAddress target) →
        ¬WorkItemAccepted current item →
        CertificateBackedCheckEvidence current item

namespace CertificateBackedCheckFragment

/-- The oracle-free all-block adapter demanded by E1. -/
theorem checkSuccessSound
    {baseline : VerifyWorld} {catalog : DependencyCatalog}
    {work : Array AnonWorkItem}
    (fragment : CertificateBackedCheckFragment baseline catalog work) :
    CheckSuccessSound baseline catalog work := by
  intro item hitem before checker hrun current hcurrent hdeps
  by_cases haccepted : WorkItemAccepted current item
  · exact ⟨current, VerifyWorld.LE.rfl, haccepted⟩
  · have resources := fragment.resources item hitem hrun current hcurrent
      hdeps haccepted
    exact resources.accepts

end CertificateBackedCheckFragment

/-- A precisely scoped fragment provider.  Resources are requested only when
the item is not already accepted in `current`; this keeps the pending/fresh
K3 premise honest while allowing E1 to reuse the rule at arbitrary monotone
world extensions.  The provider may use the accepted external dependencies
to establish the run's cache and declaration premises, but cannot assume its
own `WorkItemAccepted` conclusion. -/
structure SupportedCheckFragment (baseline : VerifyWorld)
    (catalog : DependencyCatalog) (work : Array AnonWorkItem) : Type where
  resources : ∀ item, item ∈ work →
    ∀ {before : AnonCheckLoopState} {checker : TcState .anon},
      (TcM.checkConst
        (⟨item.primary, ()⟩ : KId .anon)).run before.checker =
          .ok () checker →
      ∀ current, baseline ≤ current →
        (∀ {target}, catalog.dependsOn item.root target →
          catalog.blockOf target ≠ item.root →
          current.AcceptsAddress target) →
        ¬WorkItemAccepted current item →
        SupportedCheckEvidence current item before.checker

namespace SupportedCheckFragment

/-- The concrete K3/E0 adapter demanded by E1. -/
theorem checkSuccessSound
    {baseline : VerifyWorld} {catalog : DependencyCatalog}
    {work : Array AnonWorkItem}
    (fragment : SupportedCheckFragment baseline catalog work) :
    CheckSuccessSound baseline catalog work := by
  intro item hitem before checker hrun current hcurrent hdeps
  by_cases haccepted : WorkItemAccepted current item
  · exact ⟨current, VerifyWorld.LE.rfl, haccepted⟩
  · have resources := fragment.resources item hitem hrun current hcurrent
      hdeps haccepted
    exact resources.accepts hrun

end SupportedCheckFragment

namespace AnonWorkEnvWF

/-- E3-S composition specialized to an all-block certificate-backed fragment.
This route keeps the public serial success gate and E1 schedule unchanged while
excluding the operational oracle-backed body branch from its dependency
closure. -/
theorem checkEnvAnon_certificateBacked_subjectWF
    {env : Ixon.Env} (h : AnonWorkEnvWF env)
    (hblock : IxonEnv.BlockOfIdempotent env)
    {baseline : VerifyWorld} {assumptions : FiniteAddressSet}
    (hdeps : DepsClosed (IxonEnv.dependencyCatalog env hblock)
      (expectedAnonWork env) h.subjects assumptions)
    (hwf : WellFoundedBlocks (IxonEnv.dependencyCatalog env hblock)
      (expectedAnonWork env) h.subjects)
    (hassumptions : AssumptionsWF baseline assumptions)
    (hdisjoint : h.subjects.Disjoint assumptions)
    (fragment : CertificateBackedCheckFragment baseline
      (IxonEnv.dependencyCatalog env hblock) (expectedAnonWork env))
    (cfg : CheckCfg) {results : Array CheckResult}
    (hrun : checkEnvAnon env cfg = .ok results)
    (hresults : AllCheckResultsSucceeded results) :
    SubjectWF baseline (IxonEnv.dependencyCatalog env hblock)
      (expectedAnonWork env) h.subjects assumptions := by
  exact h.checkEnvAnon_subjectWF hblock hdeps hwf hassumptions hdisjoint
    fragment.checkSuccessSound cfg hrun hresults

/-- E3-S supported-fragment composition theorem. Successful `checkEnvAnon`
rows imply `SubjectWF` for the exact enumerated work/subject sets and the explicit
assumption set, provided every still-pending successful call belongs to the
transparent supported fragment above. -/
theorem checkEnvAnon_supported_subjectWF
    {env : Ixon.Env} (h : AnonWorkEnvWF env)
    (hblock : IxonEnv.BlockOfIdempotent env)
    {baseline : VerifyWorld} {assumptions : FiniteAddressSet}
    (hdeps : DepsClosed (IxonEnv.dependencyCatalog env hblock)
      (expectedAnonWork env) h.subjects assumptions)
    (hwf : WellFoundedBlocks (IxonEnv.dependencyCatalog env hblock)
      (expectedAnonWork env) h.subjects)
    (hassumptions : AssumptionsWF baseline assumptions)
    (hdisjoint : h.subjects.Disjoint assumptions)
    (fragment : SupportedCheckFragment baseline
      (IxonEnv.dependencyCatalog env hblock) (expectedAnonWork env))
    (cfg : CheckCfg) {results : Array CheckResult}
    (hrun : checkEnvAnon env cfg = .ok results)
    (hresults : AllCheckResultsSucceeded results) :
    SubjectWF baseline (IxonEnv.dependencyCatalog env hblock)
      (expectedAnonWork env) h.subjects assumptions := by
  exact h.checkEnvAnon_subjectWF hblock hdeps hwf hassumptions hdisjoint
    fragment.checkSuccessSound cfg hrun hresults

end AnonWorkEnvWF

end Ix.Tc
