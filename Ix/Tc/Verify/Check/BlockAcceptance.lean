import Ix.Tc.Verify.Check.Acceptance
import Ix.Tc.Verify.Check.BlockCache

/-!
# Atomic coordinated-block acceptance

The production checker validates a coordinated block before publishing one
cached success verdict.  The corresponding ghost transition must therefore
be exact: every immutable member is admitted, no unrelated declaration is
admitted, and the successful cache entry is installed only after temporary
member authority has become stable trust.

Inductive-family and recursor blocks are admitted here relative to the
explicit `InductiveOracle`.  That oracle already describes one Theory-level
block transaction; E2 must derive it from the production inductive checker.
Definition admission is local, but Lean4Lean currently has no mutual-
definition `VDecl`, so the constructive definition theorem below is
deliberately restricted to production's singleton definition blocks.  A
multi-definition block is not silently decomposed into independent claims.
-/

namespace Ix.Tc

/-- Exact promotion specialized to the ordered member array of one physical
block.  Array order remains available through `ExactCheckBlock`; the trust
delta uses extensional membership. -/
abbrev ExactBlockPromotion (before : VerifyWorld)
    (members : Array (KId .anon)) (after : VerifyWorld) : Prop :=
  ExactPromotion before (fun id => id ∈ members) after

/-- The stable semantic result of one atomic coordinated-block transaction.
The immutable identity is stated in the pre-world, while `promotion` fixes
the complete trust delta and `trustedCatalog` records the actual Theory
event log for the post-world. -/
structure AtomicBlockAdmission (trProj : RawProjRel)
    (before after : VerifyWorld) (block : KId .anon)
    (members : Array (KId .anon)) (kind : CheckBlockKind) : Prop where
  exactBlock : ExactCheckBlock before block members kind
  promotion : ExactBlockPromotion before members after
  trustedCatalog : TrustedCatalogRel trProj after

namespace AtomicBlockAdmission

/-- Exact block identity survives the ghost transaction. -/
theorem exactAfter {trProj : RawProjRel} {before after : VerifyWorld}
    {block : KId .anon} {members : Array (KId .anon)}
    {kind : CheckBlockKind}
    (h : AtomicBlockAdmission trProj before after block members kind) :
    ExactCheckBlock after block members kind := by
  refine ⟨?_, h.exactBlock.nonempty, ?_⟩
  · change after.blocks block = some members
    rw [← h.promotion.le.blocks]
    exact h.exactBlock.blockLookup
  · intro id
    change id ∈ members ↔
      after.catalog.CoordinatedMember block kind id
    rw [← h.promotion.le.catalog]
    exact h.exactBlock.memberIff id

/-- Every member is trusted in the post-world.  Consequently no proper
subset can be published as an atomic success. -/
theorem memberTrusted {trProj : RawProjRel}
    {before after : VerifyWorld} {block id : KId .anon}
    {members : Array (KId .anon)} {kind : CheckBlockKind}
    (h : AtomicBlockAdmission trProj before after block members kind)
    (hid : id ∈ members) : after.trusted id :=
  (h.promotion.trusted_iff id).2 (.inl hid)

/-- The atomic transaction establishes the stable meaning required by a
successful physical block-cache entry. -/
theorem accepted {trProj : RawProjRel} {before after : VerifyWorld}
    {block : KId .anon} {members : Array (KId .anon)}
    {kind : CheckBlockKind}
    (h : AtomicBlockAdmission trProj before after block members kind) :
    after.AcceptedBlock block :=
  ⟨members, h.exactAfter.blockLookup, h.exactBlock.nonempty,
    fun _ hid => h.memberTrusted hid⟩

/-- An identifier newly trusted by this transition must be an exact physical
member; unrelated catalog entries cannot ride along with block acceptance. -/
theorem newlyTrustedMember {trProj : RawProjRel}
    {before after : VerifyWorld} {block id : KId .anon}
    {members : Array (KId .anon)} {kind : CheckBlockKind}
    (h : AtomicBlockAdmission trProj before after block members kind)
    (hafter : after.trusted id) (hbefore : ¬before.trusted id) :
    id ∈ members :=
  h.promotion.newlyTrusted hafter hbefore

/-- Close the active block-cache phase only after the exact semantic
transaction.  This composes atomic admission with the cache ordering theorem
instead of allowing cache success to justify its own acceptance. -/
theorem closeCacheSuccess
    {semantics : CacheSemantics} {support : RunSupport}
    {trProj : RawProjRel} {before after : VerifyWorld}
    {env : KEnv .anon} {block : KId .anon}
    {members : Array (KId .anon)} {kind : CheckBlockKind}
    (h : AtomicBlockAdmission trProj before after block members kind)
    (hcaches : CacheInvariant semantics
      (CacheAuthority.coordinatedBlock before members) support env) :
    CacheInvariant semantics (CacheAuthority.stable after) support
      { env with blockCheckResults :=
          env.blockCheckResults.insert block (.ok ()) } :=
  CacheInvariant.closeExactBlockSuccess hcaches h.promotion.le h.exactAfter
    h.accepted

end AtomicBlockAdmission

/-! ## Oracle-backed inductive and recursor blocks -/

namespace CheckBlockKind

/-- Kinds whose semantic block transaction is represented by the current
ambient inductive oracle.  Definitions use the standalone declaration
transition; quotients never enter coordinated routing. -/
def OracleBacked : CheckBlockKind → Prop
  | .inductive' | .recursor => True
  | .defn => False

end CheckBlockKind

/-- An oracle tied extensionally to one exact immutable member array.  The
kind restriction prevents this ambient inductive boundary from being reused
as a definition checker. -/
structure OracleBlockCertificate (trProj : RawProjRel)
    (world : VerifyWorld) (block : KId .anon)
    (members : Array (KId .anon)) (kind : CheckBlockKind) where
  oracleBacked : kind.OracleBacked
  exactBlock : ExactCheckBlock world block members kind
  oracle : InductiveOracle trProj world.catalog world.nameOf world.trusted
    world.venv
  memberIff : ∀ id, oracle.members id ↔ id ∈ members

namespace VerifyWorld

/-- Materialize the one ambient Theory transaction carried by an inductive
oracle while preserving all immutable ghost inputs. -/
def admitOracle {trProj : RawProjRel} (world : VerifyWorld)
    (oracle : InductiveOracle trProj world.catalog world.nameOf world.trusted
      world.venv) : VerifyWorld where
  catalog := world.catalog
  blocks := world.blocks
  trusted := oracle.TrustBlock
  venv := oracle.after
  nameOf := world.nameOf
  venvWF := oracle.blockWF
  trustedCatalogued := by
    intro id htrusted
    change oracle.members id ∨ world.trusted id at htrusted
    rcases htrusted with hmember | hold
    · exact oracle.catalogued hmember
    · exact world.trustedCatalogued hold

/-- Oracle admission is a monotone world extension. -/
theorem le_admitOracle {trProj : RawProjRel} (world : VerifyWorld)
    (oracle : InductiveOracle trProj world.catalog world.nameOf world.trusted
      world.venv) : world ≤ world.admitOracle oracle :=
  ⟨rfl, rfl, rfl, fun {_} hold => oracle.trust_old hold, oracle.envLE⟩

end VerifyWorld

namespace OracleBlockCertificate

/-- Oracle freshness covers every exact immutable member. -/
theorem fresh {trProj : RawProjRel} {world : VerifyWorld}
    {block : KId .anon} {members : Array (KId .anon)}
    {kind : CheckBlockKind}
    (certificate : OracleBlockCertificate trProj world block members kind)
    {id : KId .anon} (hid : id ∈ members) : ¬world.trusted id :=
  certificate.oracle.fresh ((certificate.memberIff id).2 hid)

/-- Commit an oracle-backed block as one exact ghost transaction and one
trusted-log event.  This theorem is intentionally semantic: E2 supplies the
future operational proof that a production inductive/recursor block success
constructs this certificate. -/
theorem admit {trProj : RawProjRel} {world : VerifyWorld}
    {block : KId .anon} {members : Array (KId .anon)}
    {kind : CheckBlockKind}
    (certificate : OracleBlockCertificate trProj world block members kind)
    (hrel : TrustedCatalogRel trProj world) :
    AtomicBlockAdmission trProj world
      (world.admitOracle certificate.oracle) block members kind := by
  refine ⟨certificate.exactBlock, ?_, ?_⟩
  · refine ⟨world.le_admitOracle certificate.oracle, ?_⟩
    intro id
    change (certificate.oracle.members id ∨ world.trusted id) ↔
      id ∈ members ∨ world.trusted id
    rw [certificate.memberIff id]
  · exact TrustedCatalogLog.ambient certificate.oracle hrel

/-- Rebase the concrete/world invariant after the ghost-only atomic oracle
transaction.  The concrete environment, including its exact block array,
does not change. -/
theorem admitState {trProj : RawProjRel} {world : VerifyWorld}
    {block : KId .anon} {members : Array (KId .anon)}
    {kind : CheckBlockKind} {state : TcState .anon}
    (certificate : OracleBlockCertificate trProj world block members kind)
    (hstate : BlockStateWF trProj state world) :
    let after := world.admitOracle certificate.oracle
    AtomicBlockAdmission trProj world after block members kind ∧
      BlockStateWF trProj state after := by
  let admission := certificate.admit hstate.core.trustedCatalog
  refine ⟨admission, ?_⟩
  apply hstate.rebaseWorld admission.promotion.le
  exact
    { trustedCatalog := admission.trustedCatalog
      loaded := (LoadedAgrees.world_iff admission.promotion.le).mp
        hstate.core.loaded
      intern := hstate.core.intern }

end OracleBlockCertificate

/-! ## Constructive singleton-definition admission -/

/-- The currently supported definition-block semantic certificate.  Its
singleton shape is explicit: treating a multi-definition block as a sequence
of standalone declarations would be unsound for mutual references until the
Theory exposes a matching atomic declaration form. -/
structure SingletonDefinitionCertificate (trProj : RawProjRel)
    (world : VerifyWorld) (block id : KId .anon)
    (decl : Lean4Lean.VDecl) : Prop where
  exactBlock : ExactCheckBlock world block #[id] .defn
  pending : PendingDecl trProj world id decl
  accepted : StandaloneAccepted world.venv decl

namespace SingletonDefinitionCertificate

/-- Construct the singleton definition's exact one-declaration Theory
transition.  Every accepted member (the singleton) is trusted, and the exact
promotion theorem rules out unrelated trust growth. -/
theorem admit {trProj : RawProjRel} {world : VerifyWorld}
    {block id : KId .anon} {decl : Lean4Lean.VDecl}
    {state : TcState .anon}
    (certificate : SingletonDefinitionCertificate trProj world block id decl)
    (hstate : BlockStateWF trProj state world) :
    ∃ after,
      AtomicBlockAdmission trProj world after block #[id] .defn ∧
      BlockStateWF trProj state after ∧
      TrustedDecl trProj after id decl := by
  obtain ⟨concrete, hcatalog, hraw, huntrusted, hclosed, hfresh⟩ :=
    certificate.pending
  obtain ⟨venv', hwf⟩ := hraw.wfOfAccepted hfresh certificate.accepted
  have hpending : PendingDecl trProj world id decl :=
    ⟨concrete, hcatalog, hraw, huntrusted, hclosed, hfresh⟩
  obtain ⟨after, hpromotion, hrel, hdecl⟩ :=
    TrustedCatalogRel.promoteExact hstate.core.trustedCatalog hpending hwf
  have hblockPromotion : ExactBlockPromotion world #[id] after := by
    refine ⟨hpromotion.le, ?_⟩
    intro target
    simpa using hpromotion.trusted_iff target
  let admission : AtomicBlockAdmission trProj world after block #[id] .defn :=
    ⟨certificate.exactBlock, hblockPromotion, hrel⟩
  refine ⟨after, admission, ?_, hdecl⟩
  apply hstate.rebaseWorld admission.promotion.le
  exact
    { trustedCatalog := hrel
      loaded := (LoadedAgrees.world_iff admission.promotion.le).mp
        hstate.core.loaded
      intern := hstate.core.intern }

end SingletonDefinitionCertificate

end Ix.Tc
