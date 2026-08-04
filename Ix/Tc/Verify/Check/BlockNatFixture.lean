import Ix.Tc.Verify.Check.PublicBlocks
import Ix.Tc.Verify.NatFixture

/-!
# Concrete Nat block fixture for E0

The existing ambient-Nat oracle is instantiated here against an exact
physical block table.  This fixture exercises the semantic transaction and
the adversarial cache rule without pretending that E2 has already connected
the production inductive checker to the oracle.
-/

namespace Ix.Tc.AmbientNat.E0

/-- Ordered production member array for the Nat family. -/
def blockMembers : Array (KId .anon) := #[natId, zeroId, succId]

/-- A physical block table containing exactly the Nat family under its
recorded owner key. -/
def blockTable : BlockCatalog := fun block =>
  if block == natId then some blockMembers else none

/-- Pre-admission world: the Nat declarations are immutable inputs but none
is trusted yet. -/
def baseWorld : VerifyWorld where
  catalog := catalog
  blocks := blockTable
  trusted := fun _ => False
  venv := .empty
  nameOf := nameOf
  venvWF := ⟨[], .empty⟩
  trustedCatalogued := fun {_} h => False.elim h

@[simp] theorem blockMembers_iff (id : KId .anon) :
    id ∈ blockMembers ↔ AmbientNat.members id := by
  simp [blockMembers, AmbientNat.members]

/-- For the inductive classifier kind, the full ambient catalog owns exactly
the three Nat-family declarations.  Other fixture entries are standalone or
recursor-shaped and cannot enter this block. -/
theorem coordinated_iff (id : KId .anon) :
    catalog.CoordinatedMember natId .inductive' id ↔
      AmbientNat.members id := by
  constructor
  · rintro ⟨concrete, hcatalog, hshape⟩
    unfold catalog at hcatalog
    split at hcatalog
    · exact Or.inl (eq_of_beq (by assumption))
    · split at hcatalog
      · exact Or.inr (Or.inl (eq_of_beq (by assumption)))
      · split at hcatalog
        · exact Or.inr (Or.inr (eq_of_beq (by assumption)))
        · split at hcatalog
          · have : concrete = goodConcrete := Option.some.inj hcatalog.symm
            subst concrete
            simp [goodConcrete, KConst.IsMemberOfKind,
              KConst.IsInductiveMemberOf] at hshape
          · split at hcatalog
            · have : concrete = IllTypedPending.concrete :=
                Option.some.inj hcatalog.symm
              subst concrete
              simp [IllTypedPending.concrete, KConst.IsMemberOfKind,
                KConst.IsInductiveMemberOf] at hshape
            · split at hcatalog
              · have : concrete = iotaConcrete :=
                  Option.some.inj hcatalog.symm
                subst concrete
                simp [iotaConcrete, KConst.IsMemberOfKind,
                  KConst.IsInductiveMemberOf] at hshape
              · cases hcatalog
  · intro hmember
    rcases hmember with rfl | rfl | rfl
    · exact ⟨natConcrete, catalog_nat, by rfl⟩
    · exact ⟨zeroConcrete, catalog_zero, by
        refine ⟨natConcrete, catalog_nat, ?_⟩
        rfl⟩
    · exact ⟨succConcrete, catalog_succ, by
        refine ⟨natConcrete, catalog_nat, ?_⟩
        rfl⟩

/-- Exact immutable identity of the concrete Nat block. -/
theorem exactBlock :
    ExactCheckBlock baseWorld natId blockMembers .inductive' := by
  refine ⟨?_, by decide, ?_⟩
  · rfl
  · intro id
    exact (blockMembers_iff id).trans (coordinated_iff id).symm

/-- The ambient Nat oracle specialized definitionally to the pre-admission
world. -/
def blockOracle : InductiveOracle RawProjRel.none baseWorld.catalog
    baseWorld.nameOf baseWorld.trusted baseWorld.venv :=
  AmbientNat.oracle

/-- Concrete oracle-backed certificate for the exact Nat member array. -/
def certificate : OracleBlockCertificate RawProjRel.none baseWorld natId
    blockMembers .inductive' where
  oracleBacked := trivial
  exactBlock := exactBlock
  oracle := blockOracle
  memberIff := fun id => by
    change AmbientNat.members id ↔ id ∈ blockMembers
    exact (blockMembers_iff id).symm

/-- The fixture performs one exact atomic Theory admission: all three Nat
members become trusted together and no unrelated catalog entry does. -/
theorem atomicAdmission :
    AtomicBlockAdmission RawProjRel.none baseWorld
      (baseWorld.admitOracle blockOracle) natId blockMembers .inductive' :=
  certificate.admit TrustedCatalogLog.empty

/-- Before admission, a stable successful block-cache entry is semantically
invalid because an exact member is still untrusted. -/
theorem rejectsPrematureSuccess
    (semantics : CacheSemantics) (support : RunSupport) :
    ¬semantics.Valid (CacheAuthority.stable baseWorld) support
      (.blockResult natId (.ok ())) :=
  CacheInvariant.rejectsSuccessWithUntrustedMember exactBlock
    (id := zeroId) (by simp [blockMembers]) (fun h => h)

end Ix.Tc.AmbientNat.E0
