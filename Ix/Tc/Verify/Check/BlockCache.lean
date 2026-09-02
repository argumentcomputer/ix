import Ix.Tc.Verify.Check.BlockIdentity

/-!
# Coordinated block-cache closure

During an atomic block check, structural block caches may refer to members
which are not trusted yet.  A successful close must first promote the complete
exact member array, then rebase those active entries to stable authority, and
only then insert `blockCheckResults[block] = .ok ()`.

The inverse theorem is equally important: replaying a physical cached success
recovers acceptance of the exact immutable block and therefore cannot certify
a proper subset or treat the block address as a declaration.
-/

namespace Ix.Tc

namespace CacheAuthority

/-- Temporary authority for exactly the members of one atomic block. -/
def coordinatedBlock (world : VerifyWorld)
    (members : Array (KId .anon)) : CacheAuthority where
  world := world
  active := fun id => id ∈ members

/-- Entering an atomic block only adds temporary member authority; it does
not change the trusted world. -/
theorem stable_le_coordinatedBlock {world : VerifyWorld}
    {members : Array (KId .anon)} :
    stable world ≤ coordinatedBlock world members := by
  refine ⟨VerifyWorld.LE.rfl, ?_⟩
  intro id hauthorized
  rcases hauthorized with htrusted | hactive
  · exact .inl htrusted
  · exact False.elim hactive

/-- Once the exact block has been accepted in a larger world, every temporary
member authority becomes ordinary stable trust. -/
theorem coordinatedBlock_le_stable
    {before after : VerifyWorld} {block : KId .anon}
    {members : Array (KId .anon)}
    (hle : before ≤ after) (hblock : after.blocks block = some members)
    (haccepted : after.AcceptedBlock block) :
    coordinatedBlock before members ≤ stable after := by
  refine ⟨hle, ?_⟩
  intro id hauthorized
  rcases hauthorized with htrusted | hmember
  · exact .inl (hle.trusted htrusted)
  · exact .inl (VerifyWorld.AcceptedBlock.trusted
      haccepted hblock hmember)

end CacheAuthority

namespace CacheInvariant

/-- Close the successful atomic-cache phase in the required order: all exact
members are already trusted in `after`, active authority is eliminated, and
the successful block verdict is inserted under stable authority. -/
theorem closeBlockSuccess
    {semantics : CacheSemantics} {support : RunSupport}
    {before after : VerifyWorld} {env : KEnv .anon}
    {block : KId .anon} {members : Array (KId .anon)}
    (hcaches : CacheInvariant semantics
      (CacheAuthority.coordinatedBlock before members) support env)
    (hle : before ≤ after) (hblock : after.blocks block = some members)
    (haccepted : after.AcceptedBlock block) :
    CacheInvariant semantics (CacheAuthority.stable after) support
      { env with blockCheckResults :=
          env.blockCheckResults.insert block (.ok ()) } := by
  have hauthority : CacheAuthority.coordinatedBlock before members ≤
      CacheAuthority.stable after :=
    CacheAuthority.coordinatedBlock_le_stable hle hblock haccepted
  exact (hcaches.mono hauthority).insertBlockSuccess haccepted

/-- Exact-block specialization of `closeBlockSuccess`. -/
theorem closeExactBlockSuccess
    {semantics : CacheSemantics} {support : RunSupport}
    {before after : VerifyWorld} {env : KEnv .anon}
    {block : KId .anon} {members : Array (KId .anon)}
    {kind : CheckBlockKind}
    (hcaches : CacheInvariant semantics
      (CacheAuthority.coordinatedBlock before members) support env)
    (hle : before ≤ after)
    (hexact : ExactCheckBlock after block members kind)
    (haccepted : after.AcceptedBlock block) :
    CacheInvariant semantics (CacheAuthority.stable after) support
      { env with blockCheckResults :=
          env.blockCheckResults.insert block (.ok ()) } :=
  closeBlockSuccess hcaches hle hexact.blockLookup haccepted

/-- A stable physical success hit covers every catalog declaration owned by
the exact block.  This is the member-level replay theorem used by E0. -/
theorem replayCoordinatedMember
    {semantics : CacheSemantics} {support : RunSupport}
    {world : VerifyWorld} {env : KEnv .anon}
    {block id : KId .anon} {members : Array (KId .anon)}
    {kind : CheckBlockKind}
    (hcaches : CacheInvariant semantics (CacheAuthority.stable world)
      support env)
    (hexact : ExactCheckBlock world block members kind)
    (hhit : env.blockCheckResults[block]? = some (.ok ()))
    (hid : world.catalog.CoordinatedMember block kind id) :
    world.trusted id := by
  have haccepted := hcaches.acceptedBlock_of_success_hit hhit
  exact hexact.coordinated_trusted haccepted hid

/-- Adversarial corollary: if even one exact member is untrusted, no valid
stable success verdict for that block can exist. -/
theorem rejectsSuccessWithUntrustedMember
    {semantics : CacheSemantics} {support : RunSupport}
    {world : VerifyWorld} {block id : KId .anon}
    {members : Array (KId .anon)} {kind : CheckBlockKind}
    (hexact : ExactCheckBlock world block members kind)
    (hid : id ∈ members) (huntrusted : ¬world.trusted id) :
    ¬semantics.Valid (CacheAuthority.stable world) support
      (.blockResult block (.ok ())) := by
  intro hvalid
  have haccepted := semantics.blockSuccessSound
    (CacheAuthority.stable world) support block hvalid
  exact huntrusted (hexact.trusted haccepted hid)

end CacheInvariant

end Ix.Tc
