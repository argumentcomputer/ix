import Ix.Tc.Verify.Check.BlockOracle
import Ix.Tc.Verify.Inductive.IngressExecution
import Ix.Tc.Verify.Inductive.SingletonIngress
import Ix.Tc.Verify.Inductive.SingletonOracle

/-!
# Certificate-backed singleton family blocks

E0 fixes the exact physical block, classifier, execution trace, and active
post-state.  `SingletonFamilyCatalogLink` fixes the same member array and
constructs its semantic oracle from the E2a transaction.  This module joins
those independently audited indices, so a successful production family block
does not need an additional ambient inductive oracle.

The recursor remains a separate physical Ix block; the second adapter below
certifies that block with the enumeration oracle built from its registered
generated equations.
-/

namespace Ix.Tc

namespace SingletonFamilyCatalogLink

/-- The exact family/constructor link supplies all oracle-backed resources
for an E0 inductive-block trace. -/
def blockResources
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {source : Lean4Lean.VInductDecl} {theoryAfter : Lean4Lean.VEnv}
    {tx : CertifiedGenerationTransaction source world.venv theoryAfter}
    (link : SingletonFamilyCatalogLink trProj world.catalog world.nameOf
      world.trusted tx)
    {after : TcState .anon}
    (activePost : ActiveBlockStateWF semantics trProj world support
      link.members after) :
    OracleBackedBlockResources semantics trProj world support link.members
      .inductive' after where
  oracleBacked := by trivial
  activePost := activePost
  oracle := link.oracle
  memberIff := link.oracle_members_iff

end SingletonFamilyCatalogLink

namespace SingletonRecursorCatalogLink

/-- The enumeration link supplies all oracle-backed resources for the exact
one-member production recursor block. -/
def blockResources
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {source : Lean4Lean.VInductDecl} {theoryAfter : Lean4Lean.VEnv}
    {tx : CertifiedGenerationTransaction source world.venv theoryAfter}
    {family : SingletonFamilyCatalogLink trProj world.catalog world.nameOf
      world.trusted tx}
    (link : SingletonRecursorCatalogLink trProj world.catalog world.nameOf
      world.trusted tx family)
    (shape : CertifiedSingletonGeneration.IsEnumeration
      tx.certificate.generation)
    {after : TcState .anon}
    (activePost : ActiveBlockStateWF semantics trProj world support
      link.members after) :
    OracleBackedBlockResources semantics trProj world support link.members
      .recursor after where
  oracleBacked := by trivial
  activePost := activePost
  oracle := link.oracle shape
  memberIff := link.oracle_members_iff shape

end SingletonRecursorCatalogLink

namespace RecM

/-- Certify one actual successful singleton family/constructor block by
combining E0's exact trace with E2a/E2b's exact catalog link. -/
theorem certifySingletonFamilyBlock
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {methods : Methods .anon}
    {source : Lean4Lean.VInductDecl} {theoryAfter : Lean4Lean.VEnv}
    {tx : CertifiedGenerationTransaction source world.venv theoryAfter}
    (link : SingletonFamilyCatalogLink trProj world.catalog world.nameOf
      world.trusted tx)
    {block requested : KId .anon} {before after : TcState .anon}
    (trace : ExactBlockBodySuccessTrace methods block requested link.members
      .inductive' before after)
    (hexact : ExactCheckBlock world block link.members .inductive')
    (activePost : ActiveBlockStateWF semantics trProj world support
      link.members after) :
    CertifiedBlockBodySuccess semantics trProj world support methods block
      requested link.members .inductive' before after :=
  certifyOracleBackedBlock trace hexact (link.blockResources activePost)

/-- Certify one actual successful singleton enumeration recursor block by
combining E0's exact trace with E2a/E2b's generated-rule correspondence. -/
theorem certifySingletonRecursorBlock
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {methods : Methods .anon}
    {source : Lean4Lean.VInductDecl} {theoryAfter : Lean4Lean.VEnv}
    {tx : CertifiedGenerationTransaction source world.venv theoryAfter}
    {family : SingletonFamilyCatalogLink trProj world.catalog world.nameOf
      world.trusted tx}
    (link : SingletonRecursorCatalogLink trProj world.catalog world.nameOf
      world.trusted tx family)
    (shape : CertifiedSingletonGeneration.IsEnumeration
      tx.certificate.generation)
    {block requested : KId .anon} {before after : TcState .anon}
    (trace : ExactBlockBodySuccessTrace methods block requested link.members
      .recursor before after)
    (hexact : ExactCheckBlock world block link.members .recursor)
    (activePost : ActiveBlockStateWF semantics trProj world support
      link.members after) :
    CertifiedBlockBodySuccess semantics trProj world support methods block
      requested link.members .recursor before after :=
  certifyOracleBackedBlock trace hexact
    (link.blockResources shape activePost)

/-! ## Atomic post-admission adapters -/

/-- Certify a family body whose generated memo entries are validated in the
exact world produced by admitting the family oracle. The pre-world trusted
log justifies the admission; no reduction cache is required to be meaningful
before the family exists semantically. -/
theorem certifySingletonFamilyBlockPostAdmission
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {methods : Methods .anon}
    {source : Lean4Lean.VInductDecl} {theoryAfter : Lean4Lean.VEnv}
    {tx : CertifiedGenerationTransaction source world.venv theoryAfter}
    (link : SingletonFamilyCatalogLink trProj world.catalog world.nameOf
      world.trusted tx)
    {block requested : KId .anon} {before after : TcState .anon}
    (trace : ExactBlockBodySuccessTrace methods block requested link.members
      .inductive' before after)
    (hexact : ExactCheckBlock world block link.members .inductive')
    (trustedCatalog : TrustedCatalogRel trProj world)
    (post : KernelStateWF semantics trProj
      (world.admitOracle link.oracle) support after) :
    CertifiedAdmittedBlockBodySuccess semantics trProj world
      (world.admitOracle link.oracle) support methods block requested
      link.members .inductive' before after :=
  certifyOracleBackedAdmittedBlock trace hexact (by trivial) link.oracle
    link.oracle_members_iff trustedCatalog post

/-- Post-admission counterpart for the enumeration recursor block. -/
theorem certifySingletonRecursorBlockPostAdmission
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {methods : Methods .anon}
    {source : Lean4Lean.VInductDecl} {theoryAfter : Lean4Lean.VEnv}
    {tx : CertifiedGenerationTransaction source world.venv theoryAfter}
    {family : SingletonFamilyCatalogLink trProj world.catalog world.nameOf
      world.trusted tx}
    (link : SingletonRecursorCatalogLink trProj world.catalog world.nameOf
      world.trusted tx family)
    (shape : CertifiedSingletonGeneration.IsEnumeration
      tx.certificate.generation)
    {block requested : KId .anon} {before after : TcState .anon}
    (trace : ExactBlockBodySuccessTrace methods block requested link.members
      .recursor before after)
    (hexact : ExactCheckBlock world block link.members .recursor)
    (trustedCatalog : TrustedCatalogRel trProj world)
    (post : KernelStateWF semantics trProj
      (world.admitOracle (link.oracle shape)) support after) :
    CertifiedAdmittedBlockBodySuccess semantics trProj world
      (world.admitOracle (link.oracle shape)) support methods block requested
      link.members .recursor before after :=
  certifyOracleBackedAdmittedBlock trace hexact (by trivial)
    (link.oracle shape) (link.oracle_members_iff shape) trustedCatalog post

/-! ## Loaded-ingress adapters -/

/-- Certify an actual successful family/constructor block from the entries
loaded in its production post-state.  `LoadedAgrees` transports those entries
to the immutable catalog, while the trusted log and certified generation
trace prove that none of the linked addresses was already admitted. -/
theorem certifySingletonFamilyIngressBlock
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {methods : Methods .anon}
    {source : Lean4Lean.VInductDecl} {theoryAfter : Lean4Lean.VEnv}
    {tx : CertifiedGenerationTransaction source world.venv theoryAfter}
    {block requested : KId .anon} {before after : TcState .anon}
    (view : SingletonFamilyIngressView trProj after.env world.nameOf tx)
    (trace : ExactBlockBodySuccessTrace methods block requested view.members
      .inductive' before after)
    (hexact : ExactCheckBlock world block view.members .inductive')
    (activePost : ActiveBlockStateWF semantics trProj world support
      view.members after) :
    CertifiedBlockBodySuccess semantics trProj world support methods block
      requested view.members .inductive' before after := by
  let link := view.toCatalogLink activePost.blockState.core.loaded
    activePost.blockState.core.trustedCatalog
  exact certifySingletonFamilyBlock link trace hexact activePost

/-- Certify an actual successful singleton recursor block from the recursor
entry loaded in its production post-state.  The preceding family link fixes
the constructor order used by both the Ix rule array and Lean4Lean's
generated equations. -/
theorem certifySingletonRecursorIngressBlock
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {methods : Methods .anon}
    {source : Lean4Lean.VInductDecl} {theoryAfter : Lean4Lean.VEnv}
    {tx : CertifiedGenerationTransaction source world.venv theoryAfter}
    {family : SingletonFamilyCatalogLink trProj world.catalog world.nameOf
      world.trusted tx}
    {block requested : KId .anon} {before after : TcState .anon}
    (view : SingletonRecursorIngressView trProj after.env world.nameOf tx
      family)
    (shape : CertifiedSingletonGeneration.IsEnumeration
      tx.certificate.generation)
    (trace : ExactBlockBodySuccessTrace methods block requested view.members
      .recursor before after)
    (hexact : ExactCheckBlock world block view.members .recursor)
    (activePost : ActiveBlockStateWF semantics trProj world support
      view.members after) :
    CertifiedBlockBodySuccess semantics trProj world support methods block
      requested view.members .recursor before after := by
  let link := view.toCatalogLink activePost.blockState.core.loaded
    activePost.blockState.core.trustedCatalog
  exact certifySingletonRecursorBlock link shape trace hexact activePost

/-! ## Complete production-ingress/checker joins -/

/-- Join one actual anonymous family-block ingress execution to one actual
successful production checker-body execution.  The semantic catalog link is
constructed internally from the conversion interpretation, publication
trace, loaded-catalog invariant, trusted log, and E2a transaction. -/
theorem certifySingletonFamilyIngressExecution
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {methods : Methods .anon}
    {source : Lean4Lean.VInductDecl} {theoryAfter : Lean4Lean.VEnv}
    {tx : CertifiedGenerationTransaction source world.venv theoryAfter}
    {ixonEnv : Ixon.Env} {blockConstant : Ixon.Constant}
    {blockAddr : Address} {ingressBefore ingressAfter : AnonEnv}
    {ingressResult : AnonBlockIngressTrace}
    (interpretation : SingletonFamilyIngressInterpretation trProj
      world.nameOf ingressResult tx)
    (ingress : AnonBlockIngressSuccessTrace ixonEnv blockConstant blockAddr
      ingressBefore ingressAfter ingressResult)
    (loadedIngress : LoadedAgrees world.catalog ingressAfter)
    {block requested : KId .anon} {before after : TcState .anon}
    (trace : ExactBlockBodySuccessTrace methods block requested
      (ingressResult.allEntries.map (·.1)) .inductive' before after)
    (hexact : ExactCheckBlock world block
      (ingressResult.allEntries.map (·.1)) .inductive')
    (activePost : ActiveBlockStateWF semantics trProj world support
      (ingressResult.allEntries.map (·.1)) after) :
    CertifiedBlockBodySuccess semantics trProj world support methods block
      requested (ingressResult.allEntries.map (·.1)) .inductive' before
      after := by
  let link := interpretation.toCatalogLink ingress loadedIngress
    activePost.blockState.core.trustedCatalog
  have hmembers : link.members = ingressResult.allEntries.map (·.1) :=
    interpretation.toCatalogLink_members ingress loadedIngress
      activePost.blockState.core.trustedCatalog
  rw [← hmembers] at trace hexact activePost ⊢
  exact certifySingletonFamilyBlock link trace hexact activePost

/-- Join one actual anonymous recursor-block ingress execution to one actual
successful production recursor checker-body execution.  Positional generated
equation and iota-pattern facts remain derived from the E2a certificate and
the supported enumeration shape. -/
theorem certifySingletonRecursorIngressExecution
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {methods : Methods .anon}
    {source : Lean4Lean.VInductDecl} {theoryAfter : Lean4Lean.VEnv}
    {tx : CertifiedGenerationTransaction source world.venv theoryAfter}
    {family : SingletonFamilyCatalogLink trProj world.catalog world.nameOf
      world.trusted tx}
    {ixonEnv : Ixon.Env} {blockConstant : Ixon.Constant}
    {blockAddr : Address} {ingressBefore ingressAfter : AnonEnv}
    {ingressResult : AnonBlockIngressTrace}
    (interpretation : SingletonRecursorIngressInterpretation trProj
      world.nameOf ingressResult tx family)
    (ingress : AnonBlockIngressSuccessTrace ixonEnv blockConstant blockAddr
      ingressBefore ingressAfter ingressResult)
    (loadedIngress : LoadedAgrees world.catalog ingressAfter)
    (shape : CertifiedSingletonGeneration.IsEnumeration
      tx.certificate.generation)
    {block requested : KId .anon} {before after : TcState .anon}
    (trace : ExactBlockBodySuccessTrace methods block requested
      (ingressResult.allEntries.map (·.1)) .recursor before after)
    (hexact : ExactCheckBlock world block
      (ingressResult.allEntries.map (·.1)) .recursor)
    (activePost : ActiveBlockStateWF semantics trProj world support
      (ingressResult.allEntries.map (·.1)) after) :
    CertifiedBlockBodySuccess semantics trProj world support methods block
      requested (ingressResult.allEntries.map (·.1)) .recursor before
      after := by
  let link := interpretation.toCatalogLink ingress loadedIngress
    activePost.blockState.core.trustedCatalog
  have hmembers : link.members = ingressResult.allEntries.map (·.1) := by
    change #[interpretation.recursorId] = _
    exact interpretation.entryIds.symm
  rw [← hmembers] at trace hexact activePost ⊢
  exact certifySingletonRecursorBlock link shape trace hexact activePost

end RecM

end Ix.Tc
