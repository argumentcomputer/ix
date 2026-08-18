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
  E2 oracle-backed resource for every fresh coordinated body.

The final theorem below turns those operational resources into
`CheckSuccessSound`, which `Driver.Serial` then composes into `SubjectWF`.
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

/-! ## Certificate-backed coordinated blocks -/

/-- A coordinated block whose semantic meaning is supplied directly by an
explicit E2 oracle rather than by K3's standalone recursive-method proof.

The oracle contains exactly the exact physical members which are not already
trusted in `world`. This residual form is important for reusable checked-set
composition: an arbitrary monotone current world may already contain a
proper subset, while a replayed successful block must still establish the
whole `WorkItemAccepted` fact without re-certifying an existing member.

This resource is intentionally unavailable for definitions. Its semantic
authority is the named `InductiveOracle` boundary, and its member equation
prevents either an unrelated declaration or an already-trusted declaration
from appearing in the new trust delta. -/
structure ResidualOracleBlockResources (world : VerifyWorld)
    (blockAddr primary : Address) (targets : Array Address) : Type where
  trProj : RawProjRel
  members : Array (KId .anon)
  kind : CheckBlockKind
  oracleBacked : kind.OracleBacked
  exactBlock : ExactCheckBlock world (⟨blockAddr, ()⟩ : KId .anon)
    members kind
  workCatalog : (AnonWorkItem.block blockAddr primary targets)
    |>.MatchesBlockCatalog world.blocks
  oracle : InductiveOracle trProj world.catalog world.nameOf world.trusted
    world.venv
  memberIff : ∀ id,
    oracle.members id ↔ id ∈ members ∧ ¬world.trusted id

namespace ResidualOracleBlockResources

/-- If the exact work item is not accepted, at least one semantic template
member is still untrusted. This is the non-vacuity bridge used before
`InductiveOracle.restageMissing`; unlike an all-members freshness premise it
also handles safe partial/replay worlds. -/
theorem missing_of_not_accepted
    {world : VerifyWorld} {blockAddr primary : Address}
    {targets : Array Address} {members : Array (KId .anon)}
    {kind : CheckBlockKind} {member : KId .anon → Prop}
    (exactBlock : ExactCheckBlock world
      (⟨blockAddr, ()⟩ : KId .anon) members kind)
    (workCatalog : (AnonWorkItem.block blockAddr primary targets)
      |>.MatchesBlockCatalog world.blocks)
    (memberIff : ∀ id, member id ↔ id ∈ members)
    (hnot : ¬WorkItemAccepted world
      (.block blockAddr primary targets)) :
    ∃ id, member id ∧ ¬world.trusted id := by
  by_contra hmissing
  have htrusted : ∀ id, id ∈ members → world.trusted id := by
    intro id hid
    by_contra huntrusted
    exact hmissing ⟨id, (memberIff id).2 hid, huntrusted⟩
  have haccepted : world.AcceptedBlock
      (⟨blockAddr, ()⟩ : KId .anon) :=
    ⟨members, exactBlock.blockLookup, exactBlock.nonempty, htrusted⟩
  apply hnot
  refine ⟨haccepted, ?_⟩
  obtain ⟨workMembers, hworkBlock, _hnonempty, _hprimary, htargets⟩ :=
    workCatalog.block_targets
  have hmembers : workMembers = members :=
    Option.some.inj (hworkBlock.symm.trans exactBlock.blockLookup)
  subst workMembers
  intro addr haddr
  rw [htargets] at haddr
  obtain ⟨id, hid, haddr⟩ := Array.mem_map.mp haddr
  have htrustedId := htrusted id hid
  have hkId : (⟨id.addr, ()⟩ : KId .anon) = id := by
    cases id with
    | mk idAddr idName => cases idName; rfl
  rw [← haddr, hkId]
  exact htrustedId

/-- Admit precisely the residual oracle members and recover the complete
atomic work-item predicate. Existing exact members are retained through the
old-trust side of `TrustBlock`; missing exact members enter through the
oracle side. -/
theorem accepts
    {world : VerifyWorld} {blockAddr primary : Address}
    {targets : Array Address}
    (resources : ResidualOracleBlockResources world blockAddr primary
      targets) :
    ∃ admittedWorld, world ≤ admittedWorld ∧
      WorkItemAccepted admittedWorld
        (.block blockAddr primary targets) := by
  let admittedWorld := world.admitOracle resources.oracle
  have hle : world ≤ admittedWorld :=
    world.le_admitOracle resources.oracle
  have htrusted : ∀ id, id ∈ resources.members →
      admittedWorld.trusted id := by
    intro id hmember
    by_cases hold : world.trusted id
    · exact resources.oracle.trust_old hold
    · exact resources.oracle.trust_member
        ((resources.memberIff id).2 ⟨hmember, hold⟩)
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

end ResidualOracleBlockResources

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
`certificateBackedBlock` is the narrower E2 route for inductive/recursor
blocks whose exact raw representation already has an explicit oracle; it
does not manufacture a standalone recursive-method context. -/
inductive SupportedCheckEvidence (world : VerifyWorld) :
    AnonWorkItem → TcState .anon → Type
  | operational {item initial} :
      SupportedCheckRun world item initial →
      SupportedCheckEvidence world item initial
  | certificateBackedBlock {blockAddr primary targets initial} :
      ResidualOracleBlockResources world blockAddr primary targets →
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
