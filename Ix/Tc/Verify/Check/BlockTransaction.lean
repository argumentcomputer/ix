import Ix.Tc.Verify.Check.BlockExecution

/-!
# Atomic coordinated-block transactions

This module joins the operational trace of `checkCoordinatedBlock` to the
semantic admission model.  The join is indexed by the exact physical member
array and by the `CheckBlockKind` returned by production classification, so
neither an unrelated array nor a different checker branch can justify a
successful verdict.

There are exactly two currently supported semantic sources:

* a singleton definition, whose successful K3 result supplies ordinary
  declaration acceptance; and
* an inductive or recursor block, relative to the explicit inductive oracle
  which E2 must construct from the corresponding production checker.

Lean4Lean does not yet expose an atomic mutual-definition declaration, so no
constructor below decomposes a multi-definition production block into a
sequence of stronger semantic claims.
-/

namespace Ix.Tc

/-- The complete checker invariant while one exact coordinated block is
active.  Only structural block caches may use the additional member
authority; all reduction, inference, and definitional-equality entries remain
subject to the restrictions in `CacheEntry.ReferencesAuthorized`. -/
structure ActiveBlockStateWF (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (members : Array (KId .anon)) (state : TcState .anon) : Prop where
  blockState : BlockStateWF trProj state world
  internSupport : support.CoversIntern state.env.intern
  caches : CacheInvariant semantics
    (CacheAuthority.coordinatedBlock world members) support state.env
  equivalences : EquivManager.WF
    (semantics.Equiv (CacheAuthority.coordinatedBlock world members) support)
    state.equivManager

namespace ActiveBlockStateWF

/-- Enter temporary block authority from an ordinary stable kernel state.
The additional authority does not validate any new cache entry; it only
weakens the authority relation under which already-valid entries are viewed.
Exact loaded-block agreement is supplied separately because the legacy K1/K2
kernel invariant intentionally tracks constants but not block arrays. -/
theorem ofKernel
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {members : Array (KId .anon)} {state : TcState .anon}
    (h : KernelStateWF semantics trProj world support state)
    (hblocks : LoadedBlocksAgrees world.blocks state.env) :
    ActiveBlockStateWF semantics trProj world support members state := by
  have hauthority : CacheAuthority.stable world ≤
      CacheAuthority.coordinatedBlock world members := by
    refine ⟨VerifyWorld.LE.rfl, ?_⟩
    intro id hauthorized
    rcases hauthorized with htrusted | hactive
    · exact .inl htrusted
    · exact False.elim hactive
  exact
    { blockState := ⟨h.core, hblocks⟩
      internSupport := h.internSupport
      caches := h.caches.mono hauthority
      equivalences := EquivManager.WF.mono
        (fun hrel => semantics.equivMono hauthority hrel) h.equivalences }

/-- Once the exact block has been admitted, eliminate temporary member
authority and publish the successful physical verdict.  The result is the
ordinary stable kernel invariant in the admitted world. -/
theorem closeSuccess
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {beforeWorld afterWorld : VerifyWorld} {support : RunSupport}
    {members : Array (KId .anon)} {block : KId .anon}
    {kind : CheckBlockKind} {state : TcState .anon}
    (h : ActiveBlockStateWF semantics trProj beforeWorld support members state)
    (hadmission : AtomicBlockAdmission trProj beforeWorld afterWorld block
      members kind)
    (hstate : BlockStateWF trProj state afterWorld) :
    KernelStateWF semantics trProj afterWorld support
      (state.withBlockCheckResult block (.ok ())) := by
  have hauthority : CacheAuthority.coordinatedBlock beforeWorld members ≤
      CacheAuthority.stable afterWorld :=
    CacheAuthority.coordinatedBlock_le_stable hadmission.promotion.le
      hadmission.exactAfter.blockLookup hadmission.accepted
  refine ⟨(BlockStateWF.withBlockCheckResult hstate block (.ok ())).core,
    ?_, ?_, ?_⟩
  · simpa [TcState.withBlockCheckResult] using h.internSupport
  · simpa [TcState.withBlockCheckResult] using
      hadmission.closeCacheSuccess h.caches
  · have hequiv := EquivManager.WF.mono
        (fun hrel => semantics.equivMono hauthority hrel) h.equivalences
    simpa [TcState.withBlockCheckResult] using hequiv

end ActiveBlockStateWF

/-! ## Semantic evidence tied to one classified array -/

/-- Semantic evidence admitted by E0.  Its indices are the production array
and classified kind; this rules out pairing an operational trace with a
certificate for a different block shape.

The singleton-definition constructor retains the actual K3 checker result,
not merely an assumed `VDecl.WF`.  The oracle-backed constructor is limited
definitionally to inductive/recursor kinds and remains the named E2 boundary.
-/
inductive BlockAdmissionEvidence (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (block : KId .anon) :
    Array (KId .anon) → CheckBlockKind → Prop
  | singletonDefinition {id : KId .anon} {concrete : KConst .anon}
      {decl : Lean4Lean.VDecl} :
      PendingDecl trProj world id decl →
      StandaloneCheckResult trProj world support id concrete decl →
      BlockAdmissionEvidence trProj world support block #[id] .defn
  | oracleBacked {members : Array (KId .anon)}
      {kind : CheckBlockKind} :
      kind.OracleBacked →
      (oracle : InductiveOracle trProj world.catalog world.nameOf
        world.trusted world.venv) →
      (∀ id, oracle.members id ↔ id ∈ members) →
      BlockAdmissionEvidence trProj world support block members kind

namespace BlockAdmissionEvidence

/-- Turn supported semantic evidence into one exact ghost admission.  No
concrete mutation occurs here; the post-state relation is obtained by
rebasing the same concrete state across the proved world extension. -/
theorem admit
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {block : KId .anon} {members : Array (KId .anon)}
    {kind : CheckBlockKind} {state : TcState .anon}
    (evidence : BlockAdmissionEvidence trProj world support block members kind)
    (hexact : ExactCheckBlock world block members kind)
    (hstate : BlockStateWF trProj state world) :
    ∃ after,
      AtomicBlockAdmission trProj world after block members kind ∧
      BlockStateWF trProj state after := by
  cases evidence with
  | singletonDefinition hpending checked =>
      let certificate : SingletonDefinitionCertificate trProj world block _ _ :=
        { exactBlock := hexact
          pending := hpending
          accepted := checked.accepted }
      obtain ⟨after, hadmission, hafter, _⟩ := certificate.admit hstate
      exact ⟨after, hadmission, hafter⟩
  | @oracleBacked members kind horacleBacked oracle hmembers =>
      let certificate : OracleBlockCertificate trProj world block members kind :=
        { oracleBacked := horacleBacked
          exactBlock := hexact
          oracle := oracle
          memberIff := hmembers }
      have h := certificate.admitState hstate
      exact ⟨world.admitOracle oracle, h.1, h.2⟩

end BlockAdmissionEvidence

/-- A successful fresh body together with the exact operational and semantic
resources needed to commit it.  `trace` is the real production lookup,
classification, and classified-branch run; it is not an abstract callback
result. -/
structure CertifiedBlockBodySuccess
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (methods : Methods .anon)
    (block requested : KId .anon) (members : Array (KId .anon))
    (kind : CheckBlockKind) (before after : TcState .anon) : Prop where
  trace : RecM.ExactBlockBodySuccessTrace methods block requested members kind
    before after
  exactBlock : ExactCheckBlock world block members kind
  activePost : ActiveBlockStateWF semantics trProj world support members after
  evidence : BlockAdmissionEvidence trProj world support block members kind

namespace CertifiedBlockBodySuccess

/-- Commit a certified fresh body, preserving the exact production trace and
closing in a stable state only after semantic admission. -/
theorem commit
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {methods : Methods .anon}
    {block requested : KId .anon} {members : Array (KId .anon)}
    {kind : CheckBlockKind} {before after : TcState .anon}
    (certificate : CertifiedBlockBodySuccess semantics trProj world support
      methods block requested members kind before after) :
    ∃ admittedWorld,
      AtomicBlockAdmission trProj world admittedWorld block members kind ∧
      KernelStateWF semantics trProj admittedWorld support
        (after.withBlockCheckResult block (.ok ())) := by
  obtain ⟨admittedWorld, hadmission, hstate⟩ :=
    certificate.evidence.admit certificate.exactBlock
      certificate.activePost.blockState
  exact ⟨admittedWorld, hadmission,
    certificate.activePost.closeSuccess hadmission hstate⟩

end CertifiedBlockBodySuccess

/-! ## Post-admission cache validation

An inductive checker may construct reduction and inference memo entries whose
results mention declarations in the block being checked. Those entries are
not sound in the pre-admission world, and production does not expose the
intermediate body state to another check: semantic admission and publication
of the block verdict form one atomic close.

`CertifiedAdmittedBlockBodySuccess` is the corresponding proof shape. It
retains the exact production body trace, but validates the complete physical
post-state directly in the exact admitted world. This avoids the false
requirement that newly generated reduction entries already be meaningful
before their family has entered the Theory environment. -/

/-- An exact successful body together with its exact semantic admission and
the complete post-state invariant in that admitted world. -/
structure CertifiedAdmittedBlockBodySuccess
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world admittedWorld : VerifyWorld) (support : RunSupport)
    (methods : Methods .anon) (block requested : KId .anon)
    (members : Array (KId .anon)) (kind : CheckBlockKind)
    (before after : TcState .anon) : Prop where
  trace : RecM.ExactBlockBodySuccessTrace methods block requested members kind
    before after
  admission : AtomicBlockAdmission trProj world admittedWorld block members
    kind
  post : KernelStateWF semantics trProj admittedWorld support after

namespace CertifiedAdmittedBlockBodySuccess

/-- Publish the successful physical verdict after the post-state has already
been validated in the exact admitted world. -/
theorem commit
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world admittedWorld : VerifyWorld} {support : RunSupport}
    {methods : Methods .anon} {block requested : KId .anon}
    {members : Array (KId .anon)} {kind : CheckBlockKind}
    {before after : TcState .anon}
    (certificate : CertifiedAdmittedBlockBodySuccess semantics trProj world
      admittedWorld support methods block requested members kind before
      after) :
    KernelStateWF semantics trProj admittedWorld support
      (after.withBlockCheckResult block (.ok ())) := by
  refine ⟨certificate.post.core.of_consts_eq rfl ?_, ?_, ?_, ?_⟩
  · simpa [TcState.withBlockCheckResult] using certificate.post.core.intern
  · simpa [TcState.withBlockCheckResult] using certificate.post.internSupport
  · simpa [TcState.withBlockCheckResult] using
      certificate.post.caches.insertBlockSuccess
        certificate.admission.accepted
  · simpa [TcState.withBlockCheckResult] using certificate.post.equivalences

end CertifiedAdmittedBlockBodySuccess

/-! ## Stable result publication -/

namespace KernelStateWF

/-- Publishing a failed block verdict preserves the exact semantic world.
An error result has unconditional cache provenance and carries no declaration
acceptance claim. -/
theorem withBlockError
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {state : TcState .anon}
    (h : KernelStateWF semantics trProj world support state)
    (block : KId .anon) (err : TcError .anon) :
    KernelStateWF semantics trProj world support
      (state.withBlockCheckResult block (.error err)) := by
  refine ⟨h.core.of_consts_eq rfl h.core.intern, ?_, ?_, ?_⟩
  · simpa [TcState.withBlockCheckResult] using h.internSupport
  · simpa [TcState.withBlockCheckResult] using
      h.caches.insertBlockError (block := block) (err := err)
  · simpa [TcState.withBlockCheckResult] using h.equivalences

end KernelStateWF

/-- Exhaustive semantic result of a successful production coordinated call.
A cache hit reuses an already accepted block in the same world.  A fresh run
contains the exact body certificate and one atomic world admission. -/
inductive CoordinatedBlockAccepted
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (methods : Methods .anon)
    (block requested : KId .anon) (before after : TcState .anon) : Prop
  | replay :
      before.env.blockCheckResults[block]? = some (.ok ()) →
      after = before →
      world.AcceptedBlock block →
      KernelStateWF semantics trProj world support after →
      CoordinatedBlockAccepted semantics trProj world support methods block
        requested before after
  | fresh {members : Array (KId .anon)} {kind : CheckBlockKind}
      {bodyAfter : TcState .anon} {admittedWorld : VerifyWorld} :
      before.env.blockCheckResults[block]? = none →
      CertifiedBlockBodySuccess semantics trProj world support methods block
        requested members kind before bodyAfter →
      AtomicBlockAdmission trProj world admittedWorld block members kind →
      after = bodyAfter.withBlockCheckResult block (.ok ()) →
      KernelStateWF semantics trProj admittedWorld support after →
      CoordinatedBlockAccepted semantics trProj world support methods block
        requested before after

namespace CoordinatedBlockAccepted

/-- Every successful path ends with an accepted exact block: by cache
provenance on replay, or by the fresh atomic admission. -/
theorem accepted
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {methods : Methods .anon}
    {block requested : KId .anon} {before after : TcState .anon}
    (h : CoordinatedBlockAccepted semantics trProj world support methods block
      requested before after) :
    ∃ admittedWorld, world ≤ admittedWorld ∧
      admittedWorld.AcceptedBlock block := by
  cases h with
  | replay _ _ haccepted _ =>
      exact ⟨world, VerifyWorld.LE.rfl, haccepted⟩
  | fresh _ _ hadmission _ _ =>
      exact ⟨_, hadmission.promotion.le, hadmission.accepted⟩

end CoordinatedBlockAccepted

namespace RecM

/-- Production success is all-or-nothing relative to a verifier for the
fresh classified body.  The verifier receives the exact trace extracted
from this very run; in particular it cannot certify a different kind or
member array. -/
theorem checkCoordinatedBlock_accepted
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {methods : Methods .anon}
    {block requested : KId .anon} {before after : TcState .anon}
    (hbefore : KernelStateWF semantics trProj world support before)
    (certify : ∀ {members : Array (KId .anon)}
      {kind : CheckBlockKind} {bodyAfter : TcState .anon},
      ExactBlockBodySuccessTrace methods block requested members kind before
        bodyAfter →
      CertifiedBlockBodySuccess semantics trProj world support methods block
        requested members kind before bodyAfter)
    (hrun : (checkCoordinatedBlock block requested).run methods before =
      .ok () after) :
    CoordinatedBlockAccepted semantics trProj world support methods block
      requested before after := by
  cases checkCoordinatedBlock_success_trace hrun with
  | cached hhit hafter =>
      subst after
      exact .replay hhit rfl
        (hbefore.caches.acceptedBlock_of_success_hit hhit) hbefore
  | @fresh bodyAfter hmiss hbody hafter =>
      obtain ⟨members, kind, htrace⟩ := checkBlockBody_success_trace hbody
      let certificate := certify htrace
      obtain ⟨admittedWorld, hadmission, hfinal⟩ := certificate.commit
      exact .fresh hmiss certificate hadmission hafter
        (hafter ▸ hfinal)

end RecM

/-- Exhaustive semantic result of a failing coordinated call.  Both cases
retain the same verification world; the fresh case records the actual body
failure and publishes only an error cache entry. -/
inductive CoordinatedBlockRejected
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (methods : Methods .anon)
    (block requested : KId .anon) (before : TcState .anon)
    (err : TcError .anon) (after : TcState .anon) : Prop
  | replay :
      before.env.blockCheckResults[block]? = some (.error err) →
      after = before →
      KernelStateWF semantics trProj world support after →
      CoordinatedBlockRejected semantics trProj world support methods block
        requested before err after
  | fresh {failed : TcState .anon} :
      before.env.blockCheckResults[block]? = none →
      (RecM.captureBlockCheckResult block requested).run methods before =
        .ok (.error err) failed →
      (RecM.checkBlockBody block requested).run methods before =
        .error err failed →
      after = failed.withBlockCheckResult block (.error err) →
      KernelStateWF semantics trProj world support after →
      CoordinatedBlockRejected semantics trProj world support methods block
        requested before err after

namespace RecM

/-- Production failure cannot perform semantic admission.  A verifier for
the exact partial-error state is sufficient to re-establish the stable
invariant after the unconditional error-only cache insertion; the world in
the conclusion is definitionally the original world. -/
theorem checkCoordinatedBlock_rejected
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {methods : Methods .anon}
    {block requested : KId .anon} {before after : TcState .anon}
    {err : TcError .anon}
    (hbefore : KernelStateWF semantics trProj world support before)
    (errorFrame : ∀ {failed : TcState .anon} {caught : TcError .anon},
      (checkBlockBody block requested).run methods before =
        .error caught failed →
      KernelStateWF semantics trProj world support failed)
    (hrun : (checkCoordinatedBlock block requested).run methods before =
      .error err after) :
    CoordinatedBlockRejected semantics trProj world support methods block
      requested before err after := by
  cases checkCoordinatedBlock_error_trace hrun with
  | cached hhit hafter =>
      subst after
      exact .replay hhit rfl hbefore
  | @fresh failed hmiss hcapture hbody hafter =>
      have hfailed := errorFrame hbody
      have hfinal := hfailed.withBlockError block err
      exact .fresh hmiss hcapture hbody hafter (hafter ▸ hfinal)

end RecM

end Ix.Tc
