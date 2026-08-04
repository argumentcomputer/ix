import Ix.Tc.Verify.Check.BlockTransaction
import Ix.Tc.Verify.Inductive.Certificate

/-!
# Oracle-backed inductive and recursor blocks

E0 proves the transaction and cache ordering around production block checks.
The semantic meaning of a successful inductive/recursor body remains the
explicit E2b boundary: E2b must connect the actual Ix validators and generated
recursor patterns to an `InductiveOracle`.  The Lean4Lean
`CertifiedGenerationTransaction` supplies the Theory-owned portion of that
future construction, but cannot determine Ix addresses, member arrays, or
checker execution on its own.

This module packages exactly that remaining boundary and ties it to the real
classified-body trace.  It introduces no unindexed “block succeeded” axiom.
-/

namespace Ix.Tc

/-- The E2b resources which remain after E0 has fixed the exact physical
array and production classifier kind.  The post-state uses temporary block
authority; it cannot be exposed as a stable success until the oracle's exact
member set is atomically admitted. -/
structure OracleBackedBlockResources
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport)
    (members : Array (KId .anon)) (kind : CheckBlockKind)
    (after : TcState .anon) where
  oracleBacked : kind.OracleBacked
  activePost : ActiveBlockStateWF semantics trProj world support members after
  oracle : InductiveOracle trProj world.catalog world.nameOf world.trusted
    world.venv
  memberIff : ∀ id, oracle.members id ↔ id ∈ members

namespace RecM

/-- Package an actual successful inductive/recursor body for E0.  The trace,
exact block, active post-state, and oracle all share the same `members` and
`kind` indices. -/
theorem certifyOracleBackedBlock
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {methods : Methods .anon}
    {block requested : KId .anon} {members : Array (KId .anon)}
    {kind : CheckBlockKind} {before after : TcState .anon}
    (trace : ExactBlockBodySuccessTrace methods block requested members kind
      before after)
    (hexact : ExactCheckBlock world block members kind)
    (resources : OracleBackedBlockResources semantics trProj world support
      members kind after) :
    CertifiedBlockBodySuccess semantics trProj world support methods block
      requested members kind before after :=
  { trace := trace
    exactBlock := hexact
    activePost := resources.activePost
    evidence := .oracleBacked resources.oracleBacked resources.oracle
      resources.memberIff }

/-- Package an actual successful inductive/recursor body when its memoized
post-state is validated only after the exact oracle admission. This is the
appropriate atomic proof shape for production blocks whose generated
reduction entries mention members of the block itself. -/
theorem certifyOracleBackedAdmittedBlock
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {methods : Methods .anon}
    {block requested : KId .anon} {members : Array (KId .anon)}
    {kind : CheckBlockKind} {before after : TcState .anon}
    (trace : ExactBlockBodySuccessTrace methods block requested members kind
      before after)
    (hexact : ExactCheckBlock world block members kind)
    (horacleBacked : kind.OracleBacked)
    (oracle : InductiveOracle trProj world.catalog world.nameOf world.trusted
      world.venv)
    (memberIff : ∀ id, oracle.members id ↔ id ∈ members)
    (trustedCatalog : TrustedCatalogRel trProj world)
    (post : KernelStateWF semantics trProj (world.admitOracle oracle) support
      after) :
    CertifiedAdmittedBlockBodySuccess semantics trProj world
      (world.admitOracle oracle) support methods block requested members kind
      before after := by
  let certificate : OracleBlockCertificate trProj world block members kind :=
    { oracleBacked := horacleBacked
      exactBlock := hexact
      oracle := oracle
      memberIff := memberIff }
  exact
    { trace := trace
      admission := certificate.admit trustedCatalog
      post := post }

end RecM

end Ix.Tc
