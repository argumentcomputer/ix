import Ix.Tc.Verify.DefEq

/-!
# Certified semantics for inductive structural caches

The K1/K2 semantic stack deliberately gives no meaning to the three caches
owned only by inductive checking: generated recursors, the major-set to block
index, and the peer-agreement marker.  Rejecting those entries makes every
stable post-inductive state uninhabitable, while accepting them without a
contract would let a warm structural cache bypass the checks that created it.

This module supplies the missing contract.  Every structural entry is tied to
one exact immutable block whose members are trusted or belong to the current
atomic authority.  Generated entries and major keys must additionally name
authorized declarations.  Canonical type and rule semantics remain a
consumer obligation: the production recursor-member checker validates those
artifacts exhaustively before accepting a stored recursor.
-/

namespace Ix.Tc

namespace CacheAuthority

/-- An immutable block is usable while all of its exact members are already
trusted or are members of the current atomic transaction. -/
def AuthorizesBlock (authority : CacheAuthority) (block : KId .anon) : Prop :=
  ∃ members : Array (KId .anon),
    authority.world.blocks block = some members ∧
      members.size > 0 ∧
      ∀ id ∈ members,
        authority.world.trusted id ∨ authority.active id

/-- Exact block authority is monotone under trusted-world growth and active
transaction authority transport. -/
theorem AuthorizesBlock.mono {before after : CacheAuthority}
    (hle : before ≤ after) {block : KId .anon}
    (h : before.AuthorizesBlock block) :
    after.AuthorizesBlock block := by
  obtain ⟨members, hblock, hnonempty, hall⟩ := h
  refine ⟨members, ?_, hnonempty, ?_⟩
  · simpa only [← hle.world.blocks] using hblock
  · intro id hid
    exact hle.authorized (hall id hid)

/-- A fully admitted block is authorized at the stable boundary. -/
theorem authorizesBlock_of_accepted {world : VerifyWorld}
    {block : KId .anon} (h : world.AcceptedBlock block) :
    (CacheAuthority.stable world).AuthorizesBlock block := by
  obtain ⟨members, hblock, hnonempty, hall⟩ := h
  exact ⟨members, hblock, hnonempty, fun id hid => .inl (hall id hid)⟩

end CacheAuthority

/-- Semantic ownership of the three inductive-only cache families.  The
fallback retains the complete K1/K2 and block-result meanings. -/
def StructuralInductiveCacheValid (fallback : CacheSemantics)
    (authority : CacheAuthority) (support : RunSupport) : CacheEntry → Prop
  | .recursor block generated =>
      authority.AuthorizesBlock block ∧
        ∀ entry ∈ generated,
          ∃ id : KId .anon,
            (authority.world.trusted id ∨ authority.active id) ∧
              id.addr = entry.indAddr
  | .recMajors majors block =>
      authority.AuthorizesBlock block ∧
        ∀ id ∈ majors,
          authority.world.trusted id ∨ authority.active id
  | .blockPeer block => authority.AuthorizesBlock block
  | entry => fallback.Valid authority support entry

namespace StructuralInductiveCacheValid

/-- Structural validity survives the same authority growth as the generic
cache invariant. -/
theorem mono {fallback : CacheSemantics}
    {before after : CacheAuthority} {support : RunSupport}
    {entry : CacheEntry} (hle : before ≤ after)
    (h : StructuralInductiveCacheValid fallback before support entry) :
    StructuralInductiveCacheValid fallback after support entry := by
  cases entry with
  | recursor block generated =>
      refine ⟨CacheAuthority.AuthorizesBlock.mono hle h.1, ?_⟩
      intro cached hcached
      obtain ⟨id, hauthorized, haddr⟩ := h.2 cached hcached
      exact ⟨id, hle.authorized hauthorized, haddr⟩
  | recMajors majors block =>
      refine ⟨CacheAuthority.AuthorizesBlock.mono hle h.1, ?_⟩
      intro id hid
      exact hle.authorized (h.2 id hid)
  | blockPeer block =>
      exact CacheAuthority.AuthorizesBlock.mono hle h
  | expr | defEq | defEqFailure | unfold | natSuccStuck | isProp | isRec |
      blockResult =>
      exact fallback.mono hle h

end StructuralInductiveCacheValid

/-- Overlay the inductive structural-cache contract on any existing
semantic fallback. -/
def structuralInductiveCacheSemantics
    (fallback : CacheSemantics) : CacheSemantics where
  Valid := StructuralInductiveCacheValid fallback
  mono := StructuralInductiveCacheValid.mono
  Equiv := fallback.Equiv
  equivEquivalence := fallback.equivEquivalence
  equivMono := fallback.equivMono
  blockError := by
    intro authority support block err
    exact fallback.blockError authority support block err
  blockSuccess := by
    intro authority support block h
    exact fallback.blockSuccess authority support block h
  blockSuccessSound := by
    intro authority support block h
    exact fallback.blockSuccessSound authority support block h

/-- The production K1/K2 stack with a non-vacuous meaning for every
inductive structural cache family. -/
def kernelCacheSemanticsWithInductives
    (keys : WhnfContextKeys) (trProj : RawProjRel) : CacheSemantics :=
  k1CacheSemantics keys trProj <|
    inferCacheSemantics keys trProj <|
      defEqCacheSemantics keys trProj <|
        isPropCacheSemantics keys trProj <|
          isRecCacheSemantics <|
            structuralInductiveCacheSemantics CacheSemantics.blockErrorsOnly

namespace CacheProvenance

/-- Build provenance for one authorized generated-recursor batch.  Expression
support and direct dependency authorization stay explicit because the batch
stores executable types and rule right-hand sides. -/
theorem structuralRecursor
    {fallback : CacheSemantics} {authority : CacheAuthority}
    {support : RunSupport} {block : KId .anon}
    {generated : Array (GeneratedRecursor .anon)}
    (hblock : authority.AuthorizesBlock block)
    (hgenerated : ∀ entry ∈ generated,
      ∃ id : KId .anon,
        (authority.world.trusted id ∨ authority.active id) ∧
          id.addr = entry.indAddr)
    (hsupported : (CacheEntry.recursor block generated).SupportedBy support)
    (hreferences : ∀ ⦃id⦄,
      (CacheEntry.recursor block generated).References support id →
        authority.world.trusted id ∨ authority.active id) :
    CacheProvenance (structuralInductiveCacheSemantics fallback)
      authority support (.recursor block generated) := by
  refine ⟨hsupported, ?_, ⟨hblock, hgenerated⟩⟩
  intro id href
  rcases hreferences href with htrusted | hactive
  · exact .inl htrusted
  · exact .inr ⟨trivial, hactive⟩

/-- Build provenance for one authorized major-set index. -/
theorem structuralRecMajors
    {fallback : CacheSemantics} {authority : CacheAuthority}
    {support : RunSupport} {majors : Array (KId .anon)}
    {block : KId .anon}
    (hblock : authority.AuthorizesBlock block)
    (hmajors : ∀ id ∈ majors,
      authority.world.trusted id ∨ authority.active id) :
    CacheProvenance (structuralInductiveCacheSemantics fallback)
      authority support (.recMajors majors block) := by
  refine ⟨trivial, ?_, ⟨hblock, hmajors⟩⟩
  intro id hid
  rcases hmajors id hid with htrusted | hactive
  · exact .inl htrusted
  · exact .inr ⟨trivial, hactive⟩

/-- Build provenance for the marker written only after exact block peer
agreement has succeeded.  The marker has no expression payload or direct
declaration roots; its semantic payload is the authorized exact block. -/
theorem structuralBlockPeer
    {fallback : CacheSemantics} {authority : CacheAuthority}
    {support : RunSupport} {block : KId .anon}
    (hblock : authority.AuthorizesBlock block) :
    CacheProvenance (structuralInductiveCacheSemantics fallback)
      authority support (.blockPeer block) := by
  refine ⟨trivial, ?_, hblock⟩
  intro id href
  exact False.elim href

end CacheProvenance

namespace CacheInvariant

/-- Insert or replace one provenance-certified generated-recursor batch. -/
theorem insertRecursor {semantics : CacheSemantics}
    {authority : CacheAuthority} {support : RunSupport}
    {env : KEnv .anon} {block : KId .anon}
    {generated : Array (GeneratedRecursor .anon)}
    (hbefore : CacheInvariant semantics authority support env)
    (hnew : CacheProvenance semantics authority support
      (.recursor block generated)) :
    CacheInvariant semantics authority support
      { env with recursorCache := env.recursorCache.insert block generated } := by
  apply update hbefore hnew
  intro entry hentry
  cases hentry with
  | whnf hget => exact .inr (.whnf hget)
  | whnfNoDelta hget => exact .inr (.whnfNoDelta hget)
  | whnfNoDeltaCheap hget => exact .inr (.whnfNoDeltaCheap hget)
  | whnfCore hget => exact .inr (.whnfCore hget)
  | whnfCoreCheap hget => exact .inr (.whnfCoreCheap hget)
  | infer hget => exact .inr (.infer hget)
  | inferOnly hget => exact .inr (.inferOnly hget)
  | defEq hget => exact .inr (.defEq hget)
  | defEqCheap hget => exact .inr (.defEqCheap hget)
  | defEqFailure hmem => exact .inr (.defEqFailure hmem)
  | unfold hget => exact .inr (.unfold hget)
  | natSuccStuck hmem => exact .inr (.natSuccStuck hmem)
  | isProp hget => exact .inr (.isProp hget)
  | isRec hget => exact .inr (.isRec hget)
  | @recursor foundBlock foundGenerated hget =>
      rw [Std.HashMap.getElem?_insert] at hget
      split at hget
      · next heq =>
        cases hget
        have hblock : block = foundBlock := eq_of_beq heq
        subst foundBlock
        exact .inl rfl
      · exact .inr (.recursor hget)
  | recMajors hget => exact .inr (.recMajors hget)
  | blockPeer hmem => exact .inr (.blockPeer hmem)
  | blockResult hget => exact .inr (.blockResult hget)

/-- Insert or replace one provenance-certified major-set index. -/
theorem insertRecMajors {semantics : CacheSemantics}
    {authority : CacheAuthority} {support : RunSupport}
    {env : KEnv .anon} {majors : Array (KId .anon)}
    {block : KId .anon}
    (hbefore : CacheInvariant semantics authority support env)
    (hnew : CacheProvenance semantics authority support
      (.recMajors majors block)) :
    CacheInvariant semantics authority support
      { env with recMajorsCache := env.recMajorsCache.insert majors block } := by
  apply update hbefore hnew
  intro entry hentry
  cases hentry with
  | whnf hget => exact .inr (.whnf hget)
  | whnfNoDelta hget => exact .inr (.whnfNoDelta hget)
  | whnfNoDeltaCheap hget => exact .inr (.whnfNoDeltaCheap hget)
  | whnfCore hget => exact .inr (.whnfCore hget)
  | whnfCoreCheap hget => exact .inr (.whnfCoreCheap hget)
  | infer hget => exact .inr (.infer hget)
  | inferOnly hget => exact .inr (.inferOnly hget)
  | defEq hget => exact .inr (.defEq hget)
  | defEqCheap hget => exact .inr (.defEqCheap hget)
  | defEqFailure hmem => exact .inr (.defEqFailure hmem)
  | unfold hget => exact .inr (.unfold hget)
  | natSuccStuck hmem => exact .inr (.natSuccStuck hmem)
  | isProp hget => exact .inr (.isProp hget)
  | isRec hget => exact .inr (.isRec hget)
  | recursor hget => exact .inr (.recursor hget)
  | @recMajors foundMajors foundBlock hget =>
      rw [Std.HashMap.getElem?_insert] at hget
      split at hget
      · next heq =>
        cases hget
        have hmajors : majors = foundMajors := eq_of_beq heq
        subst foundMajors
        exact .inl rfl
      · exact .inr (.recMajors hget)
  | blockPeer hmem => exact .inr (.blockPeer hmem)
  | blockResult hget => exact .inr (.blockResult hget)

/-- Insert one provenance-certified peer-agreement marker. -/
theorem insertBlockPeer {semantics : CacheSemantics}
    {authority : CacheAuthority} {support : RunSupport}
    {env : KEnv .anon} {block : KId .anon}
    (hbefore : CacheInvariant semantics authority support env)
    (hnew : CacheProvenance semantics authority support (.blockPeer block)) :
    CacheInvariant semantics authority support
      { env with
        blockPeerAgreementCache := env.blockPeerAgreementCache.insert block } := by
  apply update hbefore hnew
  intro entry hentry
  cases hentry with
  | whnf hget => exact .inr (.whnf hget)
  | whnfNoDelta hget => exact .inr (.whnfNoDelta hget)
  | whnfNoDeltaCheap hget => exact .inr (.whnfNoDeltaCheap hget)
  | whnfCore hget => exact .inr (.whnfCore hget)
  | whnfCoreCheap hget => exact .inr (.whnfCoreCheap hget)
  | infer hget => exact .inr (.infer hget)
  | inferOnly hget => exact .inr (.inferOnly hget)
  | defEq hget => exact .inr (.defEq hget)
  | defEqCheap hget => exact .inr (.defEqCheap hget)
  | defEqFailure hmem => exact .inr (.defEqFailure hmem)
  | unfold hget => exact .inr (.unfold hget)
  | natSuccStuck hmem => exact .inr (.natSuccStuck hmem)
  | isProp hget => exact .inr (.isProp hget)
  | isRec hget => exact .inr (.isRec hget)
  | recursor hget => exact .inr (.recursor hget)
  | recMajors hget => exact .inr (.recMajors hget)
  | @blockPeer foundBlock hmem =>
      rw [Std.HashSet.contains_insert, Bool.or_eq_true] at hmem
      rcases hmem with hsame | hold
      · have hblock : block = foundBlock := eq_of_beq hsame
        subst foundBlock
        exact .inl rfl
      · exact .inr (.blockPeer hold)
  | blockResult hget => exact .inr (.blockResult hget)

end CacheInvariant

namespace ScopedWhnfStateInv

/-- Replacing one generated-recursor batch through the production cache field
preserves the complete scoped checker invariant once the installed batch has
explicit cache provenance.  The write is invisible to context reconstruction
and to the composite suffix digest; no semantic meaning is inferred merely
from the physical cache insertion. -/
theorem insertRecursor
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {Delta : KVLCtx}
    {state : TcState .anon} {block : KId .anon}
    {generated : Array (GeneratedRecursor .anon)}
    (hnew : CacheProvenance semantics (CacheAuthority.stable world) support
      (.recursor block generated))
    (h : ScopedWhnfStateInv model layer semantics support Delta state) :
    ScopedWhnfStateInv model layer semantics support Delta
      { state with env := { state.env with
        recursorCache := state.env.recursorCache.insert block generated } } := by
  refine ⟨?_, model.preservesFrame h.2 ?_⟩
  · rcases h.1 with ⟨hkernel, hctx, hlayer⟩
    refine ⟨?_, ?_, ?_⟩
    · exact {
        core := hkernel.core.of_consts_eq rfl (by
          simpa using hkernel.core.intern)
        internSupport := by
          simpa using hkernel.internSupport
        caches := CacheInvariant.insertRecursor hkernel.caches hnew
        equivalences := by
          simpa using hkernel.equivalences }
    · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
    · cases layer <;> exact hlayer
  · constructor <;> rfl

end ScopedWhnfStateInv

end Ix.Tc
