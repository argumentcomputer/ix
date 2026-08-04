import Ix.Tc.Driver
import Ix.Tc.Verify.State

/-!
# Coordinated checker-block identity

`checkConst` uses three representations of a block which must not be allowed
to drift apart:

* `KEnv.blocks` is the concrete ordered member array used by the checker;
* `VerifyWorld.blocks` is its immutable ghost identity, needed to interpret a
  stable `blockCheckResults[block] = .ok ()` hit; and
* `AnonWorkItem.block` exposes the block address, primary address, target
  addresses, and the larger `provenTargets` set used by the driver.

This module defines their exact agreement without assigning typing authority
to any of them.  In particular, a catalogued member is still untrusted until
the atomic acceptance theorem admits the complete array.
-/

namespace Ix.Tc

/-! ## Concrete/world block agreement -/

/-- E0's representation invariant.  The existing `TcStateWF` continues to
separate loaded constants from semantic trust; this layer adds the one-way
agreement for lazily loaded block arrays. -/
structure BlockStateWF (trProj : RawProjRel) (s : TcState .anon)
    (world : VerifyWorld) : Prop where
  core : TcStateWF trProj s world
  loadedBlocks : LoadedBlocksAgrees world.blocks s.env

namespace BlockStateWF

/-- A concrete block lookup exposes the exact immutable ordered array. -/
theorem blockLookup {trProj : RawProjRel} {s : TcState .anon}
    {world : VerifyWorld} (h : BlockStateWF trProj s world)
    {block : KId .anon} {members : Array (KId .anon)}
    (hget : s.env.blocks[block]? = some members) :
    world.blocks block = some members :=
  h.loadedBlocks hget

/-- Operational bookkeeping changes preserve the block invariant when the
whole environment is unchanged. -/
theorem of_env_eq {trProj : RawProjRel} {before after : TcState .anon}
    {world : VerifyWorld} (h : BlockStateWF trProj before world)
    (henv : after.env = before.env) :
    BlockStateWF trProj after world := by
  refine ⟨h.core.of_env_eq henv, ?_⟩
  rw [henv]
  exact h.loadedBlocks

/-- Ghost promotion preserves block identity because `VerifyWorld.LE` fixes
the immutable block catalog. -/
theorem rebaseWorld {trProj : RawProjRel} {s : TcState .anon}
    {before after : VerifyWorld} (h : BlockStateWF trProj s before)
    (hle : before ≤ after) (hcore : TcStateWF trProj s after) :
    BlockStateWF trProj s after :=
  ⟨hcore, (LoadedBlocksAgrees.world_iff hle).mp h.loadedBlocks⟩

end BlockStateWF

/-! ## Exact semantic ownership of members -/

namespace KConst

/-- A definition declaration records this coordinated owner block. -/
def IsDefinitionMemberOf (block : KId .anon) : KConst .anon → Prop
  | .defn (block := owner) .. => owner = block
  | _ => False

/-- A recursor declaration records this coordinated owner block. -/
def IsRecursorMemberOf (block : KId .anon) : KConst .anon → Prop
  | .recr (block := owner) .. => owner = block
  | _ => False

/-- Inductive-like ownership follows production's routing exactly.  An
inductive records its block directly; a constructor inherits the block from
the exact parent inductive committed by the catalog. -/
def IsInductiveMemberOf (catalog : Catalog) (block : KId .anon) :
    KConst .anon → Prop
  | .indc (block := owner) .. => owner = block
  | .ctor (induct := parent) .. =>
      ∃ parentConst, catalog parent = some parentConst ∧
        match parentConst with
        | .indc (block := owner) .. => owner = block
        | _ => False
  | _ => False

/-- Exact declaration shape represented by a production `CheckBlockKind`. -/
def IsMemberOfKind (catalog : Catalog) (block : KId .anon) :
    CheckBlockKind → KConst .anon → Prop
  | .defn => IsDefinitionMemberOf block
  | .inductive' => IsInductiveMemberOf catalog block
  | .recursor => IsRecursorMemberOf block

end KConst

namespace Catalog

/-- `id` is the exact catalog declaration owned by `block` under `kind`.
This is deliberately stronger than merely having the right constructor tag. -/
def CoordinatedMember (catalog : Catalog) (block : KId .anon)
    (kind : CheckBlockKind) (id : KId .anon) : Prop :=
  ∃ concrete, catalog id = some concrete ∧
    concrete.IsMemberOfKind catalog block kind

namespace CoordinatedMember

theorem catalogued {catalog : Catalog} {block : KId .anon}
    {kind : CheckBlockKind} {id : KId .anon}
    (h : catalog.CoordinatedMember block kind id) :
    Catalog.Contains catalog id := by
  obtain ⟨concrete, hcatalog, _⟩ := h
  exact ⟨concrete, hcatalog⟩

end CoordinatedMember

end Catalog

/-- One immutable block entry is exact for a coordinated checker kind: it is
nonempty, and array membership is equivalent to catalog ownership.  The
ordered array itself remains available, so later ingress/driver proofs can
also establish positional claims rather than only set coverage. -/
structure ExactCheckBlock (world : VerifyWorld) (block : KId .anon)
    (members : Array (KId .anon)) (kind : CheckBlockKind) : Prop where
  blockLookup : world.blocks block = some members
  nonempty : members.size > 0
  memberIff : ∀ id, id ∈ members ↔
    world.catalog.CoordinatedMember block kind id

namespace ExactCheckBlock

/-- Exact block identity is stable under semantic world extension: both the
catalog and ordered block table are immutable components of `VerifyWorld`. -/
theorem rebaseWorld {before after : VerifyWorld} {block : KId .anon}
    {members : Array (KId .anon)} {kind : CheckBlockKind}
    (h : ExactCheckBlock before block members kind) (hle : before ≤ after) :
    ExactCheckBlock after block members kind := by
  refine ⟨?_, h.nonempty, ?_⟩
  · rw [← hle.blocks]
    exact h.blockLookup
  · intro id
    rw [← hle.catalog]
    exact h.memberIff id

theorem member {world : VerifyWorld} {block id : KId .anon}
    {members : Array (KId .anon)} {kind : CheckBlockKind}
    (h : ExactCheckBlock world block members kind)
    (hmember : world.catalog.CoordinatedMember block kind id) :
    id ∈ members :=
  (h.memberIff id).2 hmember

theorem coordinated {world : VerifyWorld} {block id : KId .anon}
    {members : Array (KId .anon)} {kind : CheckBlockKind}
    (h : ExactCheckBlock world block members kind) (hmember : id ∈ members) :
    world.catalog.CoordinatedMember block kind id :=
  (h.memberIff id).1 hmember

/-- Once the exact block is accepted, every exact member is trusted. -/
theorem trusted {world : VerifyWorld} {block id : KId .anon}
    {members : Array (KId .anon)} {kind : CheckBlockKind}
    (hexact : ExactCheckBlock world block members kind)
    (haccepted : world.AcceptedBlock block) (hid : id ∈ members) :
    world.trusted id :=
  VerifyWorld.AcceptedBlock.trusted haccepted hexact.blockLookup hid

/-- Acceptance covers every catalog declaration owned by this exact block;
no proper subset of its member array can satisfy the conclusion. -/
theorem coordinated_trusted {world : VerifyWorld} {block id : KId .anon}
    {members : Array (KId .anon)} {kind : CheckBlockKind}
    (hexact : ExactCheckBlock world block members kind)
    (haccepted : world.AcceptedBlock block)
    (hid : world.catalog.CoordinatedMember block kind id) :
    world.trusted id :=
  hexact.trusted haccepted (hexact.member hid)

end ExactCheckBlock

/-- Global coherence required of E0's immutable inputs: every catalogued
declaration which records coordinated ownership has one exact block entry of
the same kind.  The premise does not trust or type the declaration. -/
def ExactCoordinatedCatalog (world : VerifyWorld) : Prop :=
  ∀ {id concrete block kind}, world.catalog id = some concrete →
    concrete.IsMemberOfKind world.catalog block kind →
      ∃ members, ExactCheckBlock world block members kind

namespace ExactCoordinatedCatalog

/-- Resolve a catalogued owner to its exact array and requested membership. -/
theorem resolve {world : VerifyWorld} (h : ExactCoordinatedCatalog world)
    {id concrete block kind}
    (hcatalog : world.catalog id = some concrete)
    (hshape : concrete.IsMemberOfKind world.catalog block kind) :
    ∃ members, ExactCheckBlock world block members kind ∧ id ∈ members := by
  obtain ⟨members, hexact⟩ := h hcatalog hshape
  exact ⟨members, hexact,
    hexact.member ⟨concrete, hcatalog, hshape⟩⟩

end ExactCoordinatedCatalog

/-! ## Driver primary/target identity -/

namespace AnonWorkItem

/-- Exact agreement between one anonymous driver item and the immutable block
catalog.  A Muts item exposes all flattened `KEnv.blocks` members as targets;
its first member is the primary.  `provenTargets` additionally includes the
original Muts address, which is not necessarily a `KConst` declaration id.

Standalone ingress also registers a singleton physical block, although
axioms and quotients intentionally bypass block coordination in `checkConst`. -/
def MatchesBlockCatalog (blocks : BlockCatalog) : AnonWorkItem → Prop
  | .standalone addr =>
      let id : KId .anon := ⟨addr, ()⟩
      blocks id = some #[id]
  | .block blockAddr primary targets =>
      let block : KId .anon := ⟨blockAddr, ()⟩
      ∃ first rest,
        blocks block = some (#[first] ++ rest) ∧
          primary = first.addr ∧
          targets = (#[first] ++ rest).map (·.addr)

namespace MatchesBlockCatalog

/-- A block item's primary is one of its exact target addresses. -/
theorem primary_mem_targets {blocks : BlockCatalog} {item : AnonWorkItem}
    (h : item.MatchesBlockCatalog blocks) :
    item.primary ∈ item.targets := by
  cases item with
  | standalone addr => simp [AnonWorkItem.primary, AnonWorkItem.targets]
  | block blockAddr primary targets =>
      obtain ⟨first, rest, hblock, hprimary, htargets⟩ := h
      subst primary
      subst targets
      simp [AnonWorkItem.primary, AnonWorkItem.targets]

/-- For a block item, `targets` is exactly the address image of the immutable
ordered member array. -/
theorem block_targets {blocks : BlockCatalog} {blockAddr primary : Address}
    {targets : Array Address}
    (h : (AnonWorkItem.block blockAddr primary targets).MatchesBlockCatalog
      blocks) :
    ∃ members, blocks (⟨blockAddr, ()⟩ : KId .anon) = some members ∧
      members.size > 0 ∧ primary = members[0]!.addr ∧
      targets = members.map (·.addr) := by
  obtain ⟨first, rest, hblock, hprimary, htargets⟩ := h
  refine ⟨#[first] ++ rest, hblock, ?_, ?_, htargets⟩
  · rw [Array.size_append]
    have hone : (#[first] : Array (KId .anon)).size = 1 := by rfl
    rw [hone]
    omega
  · have hzero : (#[first] ++ rest)[0]! = first := by
      rw [getElem!_pos (#[first] ++ rest) 0 (by simp; omega)]
      exact Array.getElem_append_left (by simp)
    rw [hzero]
    exact hprimary

/-- `provenTargets` is the exact target array plus the original Muts block
address.  This is the extra coverage later consumed by E1; it is not smuggled
into the member array or treated as a trusted declaration. -/
theorem block_provenTargets {blocks : BlockCatalog}
    {blockAddr primary : Address} {targets : Array Address}
    (_h : (AnonWorkItem.block blockAddr primary targets).MatchesBlockCatalog
      blocks) :
    (AnonWorkItem.block blockAddr primary targets).provenTargets =
      #[blockAddr] ++ targets := by
  rfl

/-- Standalone work proves exactly its one target. -/
theorem standalone_provenTargets {blocks : BlockCatalog} {addr : Address}
    (_h : (AnonWorkItem.standalone addr).MatchesBlockCatalog blocks) :
    (AnonWorkItem.standalone addr).provenTargets = #[addr] := by
  rfl

end MatchesBlockCatalog

end AnonWorkItem

end Ix.Tc
