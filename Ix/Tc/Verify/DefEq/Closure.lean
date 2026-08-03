import Ix.Tc.Verify.DefEq.CacheShell
import Ix.Tc.Verify.DefEq.FinalWhnf.Closure
import Ix.Tc.Verify.DefEq.LazyDeltaClosure

/-!
# Complete definitional-equality closure

This module assembles the verified recursive DefEq tiers, the public cache
shell, and the exact `isDefEq` field of one unfolded method-table layer.  The
resource record deliberately reuses witnesses owned by its lower closure
records: projection delta owns the shared Theory/collision/structural facts,
while final WHNF owns the direct reducer and primitive-expansion facts.
-/

namespace Ix.Tc

namespace CacheEntry

/-- If every direct declaration reference in the finite run support is
trusted, then either DefEq cache partition may safely mention any pair of
supported source addresses.  The key itself carries no authority: its direct
roots are recovered through `SourceReferences`. -/
theorem defEqReferencesAuthorized
    {world : VerifyWorld} {support : RunSupport}
    (htrusted : RecM.TrustedReferences world support)
    {kind : DefEqCacheKind} {key : Address × Address × Address}
    {answer : Bool} :
    (CacheEntry.defEq kind key answer).ReferencesAuthorized
      (CacheAuthority.stable world) support := by
  intro id href
  apply Or.inl
  change CacheEntry.SourceReferences support key.1 id ∨
    CacheEntry.SourceReferences support key.2.1 id at href
  rcases href with ⟨source, hsource, _haddr, hreference⟩ |
      ⟨source, hsource, _haddr, hreference⟩
  · exact htrusted hsource hreference
  · exact htrusted hsource hreference

end CacheEntry

namespace RecM

/-- Concrete resources for the entire recursive and public DefEq method.
No field assumes soundness of `isDefEqInner`, `isDefEqWhnf`, or `isDefEq`
itself. -/
structure DefEqClosureResources
    {trProj : RawProjRel} {world : VerifyWorld} (support : RunSupport)
    (proposition : PropositionClassifierContext trProj world support)
    (eligible : KId .anon → Prop) where
  finalWhnf : FinalWhnfClosureResources support proposition eligible
  iteration : LazyDeltaIterationResources support proposition.model
  projectionDelta : ProjectionDeltaClosureResources
    (kernelCacheSemantics proposition.model.keys trProj) trProj world support
    proposition.model.keys.uvars
  structural : StructuralCongruenceResources support
  application : TryDefEqApp.WFAt .noAccel
    (kernelCacheSemantics proposition.model.keys trProj) trProj world support
    proposition.model.keys.uvars
  bool : BoolTruePrimitiveContext world
  cheap : DefEqCheapReductionContext .noAccel
    (kernelCacheSemantics proposition.model.keys trProj) trProj world support
    proposition.model.keys.uvars

namespace DefEqClosureResources

/-- Supply the stopped lazy-delta continuation from concrete projection,
structural, application-spine, and final-WHNF closures. -/
def stopped
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {proposition : PropositionClassifierContext trProj world support}
    {eligible : KId .anon → Prop}
    (resources : DefEqClosureResources support proposition eligible) :
    StoppedContinuationClosureResources
      (kernelCacheSemantics proposition.model.keys trProj) trProj world support
      proposition.model.keys.uvars where
  projectionDelta := resources.projectionDelta
  structural := resources.structural
  application := resources.application
  finalWhnf := resources.finalWhnf.finalWhnf

/-- Assemble one complete bounded lazy-delta resource from its verified
iteration and stopped continuation. -/
def lazyDelta
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {proposition : PropositionClassifierContext trProj world support}
    {eligible : KId .anon → Prop}
    (resources : DefEqClosureResources support proposition eligible) :
    LazyDeltaClosureResources support proposition.model where
  iteration := resources.iteration
  stopped := resources.stopped

/-- Close the complete recursive `isDefEqInner` program in production tier
order. -/
theorem inner
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {proposition : PropositionClassifierContext trProj world support}
    {eligible : KId .anon → Prop}
    (resources : DefEqClosureResources support proposition eligible) :
    DefEqInner.WF .noAccel trProj world support proposition.model := by
  unfold DefEqInner.WF
  exact DefEqAfterStringExpansion.closesInner
    resources.projectionDelta.theory
    resources.projectionDelta.collision
    resources.projectionDelta.sorts
    resources.projectionDelta.quick
    resources.bool
    resources.finalWhnf.string
    resources.finalWhnf.canonical
    resources.finalWhnf.directWhnf
    (DefEqAfterProofIrrelevance.closesAfterStringExpansion
      resources.projectionDelta.theory
      resources.projectionDelta.collision
      resources.projectionDelta.sorts
      resources.projectionDelta.quick
      resources.cheap
      (isPropType_wf proposition)
      (DefEqAfterProofIrrelevance.ofKernelResources resources.lazyDelta))

/-- Close the complete public `isDefEq` entry point, including both result
cache partitions and guarded equivalence-root fallbacks. -/
theorem entryPoint
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {proposition : PropositionClassifierContext trProj world support}
    {eligible : KId .anon → Prop}
    (resources : DefEqClosureResources support proposition eligible) :
    ∀ {Delta state a b aV bV},
      support a → support b →
      TrKExprS world.venv proposition.model.keys.uvars world.nameOf trProj
        Delta a aV →
      TrKExprS world.venv proposition.model.keys.uvars world.nameOf trProj
        Delta b bV →
      RecM.WF .noAccel
        (kernelCacheSemantics proposition.model.keys trProj) trProj world
        support proposition.model.keys.uvars Delta state (isDefEq a b)
        (fun answer _ => answer = true →
          world.venv.IsDefEqU proposition.model.keys.uvars Delta.toCtx aV
            bV) := by
  intro Delta state a b aV bV haSupport hbSupport ha hb
  exact isDefEq_wf proposition.model resources.projectionDelta.theory
    resources.projectionDelta.collision resources.inner
    haSupport hbSupport ha hb
    (fun _ctxAddr _kind _answer =>
      CacheEntry.defEqReferencesAuthorized
        resources.iteration.trustedReferences)

/-- The `isDefEq` field of one unfolded production method-table layer.  All
recursive calls are discharged solely by the smaller table's `Methods.WFAt`
hypothesis. -/
theorem nextDefEq_wf
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {proposition : PropositionClassifierContext trProj world support}
    {eligible : KId .anon → Prop}
    (resources : DefEqClosureResources support proposition eligible)
    (methods : Methods .anon)
    (hmethods : Methods.WFAt .noAccel
      (kernelCacheSemantics proposition.model.keys trProj) trProj world support
      proposition.model.keys.uvars methods) :
    ∀ {Delta state a b aV bV},
      support a → support b →
      TrKExprS world.venv proposition.model.keys.uvars world.nameOf trProj
        Delta a aV →
      TrKExprS world.venv proposition.model.keys.uvars world.nameOf trProj
        Delta b bV →
      TcM.WF
        (WhnfStateInv .noAccel
          (kernelCacheSemantics proposition.model.keys trProj) trProj world
          support proposition.model.keys.uvars Delta) state
        ((RecM.isDefEq a b).run methods)
        (fun answer _ => answer = true →
          world.venv.IsDefEqU proposition.model.keys.uvars Delta.toCtx aV
            bV) := by
  intro Delta state a b aV bV haSupport hbSupport ha hb
  exact (resources.entryPoint haSupport hbSupport ha hb) methods hmethods

end DefEqClosureResources

end RecM

end Ix.Tc
