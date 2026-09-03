import Ix.Tc.Verify.Check.SingletonInductive
import Ix.Tc.Verify.Inductive.IndexedRecursiveFixture

/-!
# Production acceptance of the indexed-recursive fixture

The dependency family is checked first.  The production `IndexedVec` family
checker then derives its canonical generated recursor, and the separately
ingressed recursor block is compared against that cached result.  Every run
starts from the exact final anonymous ingress state retained by the fixture.
-/

namespace Ix.Tc.IndexedRecursiveFixture

open Lean4Lean
open Lean4Lean.InductiveReplayFixtures
open IndexedRecursiveCertificateFixture

local instance acceptanceAnonKIdDecidableEq : DecidableEq (KId .anon) :=
  fun left right =>
    if h : left == right then
      .isTrue (eq_of_beq h)
    else
      .isFalse fun equality => h (by cases equality; exact beq_self_eq_true left)

def natBlockId : KId .anon := ⟨natBlockAddress, ()⟩
def familyBlockId : KId .anon := ⟨familyBlockAddress, ()⟩
def recursorBlockId : KId .anon := ⟨recursorBlockAddress, ()⟩

/- Keep the physical member arrays consumed by the production checkers as
plain ingress data.  Projecting these arrays from the semantic catalog links
would make an otherwise operational checker trace depend transitively on the
links' `InductiveOracle`-indexed types. -/
def natMembers : Array (KId .anon) := #[natId, zeroId, succId]
def familyMembers : Array (KId .anon) := #[familyId, nilId, consId]
def recursorMembers : Array (KId .anon) := #[recursorId]

theorem natMembers_eq : natMembers = #[natId, zeroId, succId] := rfl
theorem familyMembers_eq : familyMembers = #[familyId, nilId, consId] := rfl
theorem recursorMembers_eq : recursorMembers = #[recursorId] := rfl

def checkerFuel : UInt64 := 1024
def checkerMethods : Methods .anon := methodsN checkerFuel.toNat

def checkerInitial : TcState .anon :=
  { TcState.ofEnvAnon recursorIngressAfter with
    recFuel := checkerFuel
    fuelBudget := checkerFuel }

private theorem natBlockLoadedNative :
    checkerInitial.env.getBlock? natBlockId = some natMembers := by
  native_decide
theorem natBlockLoaded :
    checkerInitial.env.getBlock? natBlockId = some natMembers :=
  natBlockLoadedNative

private theorem familyBlockLoadedNative :
    checkerInitial.env.getBlock? familyBlockId = some familyMembers := by
  native_decide
theorem familyBlockLoaded :
    checkerInitial.env.getBlock? familyBlockId = some familyMembers :=
  familyBlockLoadedNative

private theorem recursorBlockLoadedNative :
    checkerInitial.env.getBlock? recursorBlockId = some recursorMembers := by
  native_decide
theorem recursorBlockLoaded :
    checkerInitial.env.getBlock? recursorBlockId = some recursorMembers :=
  recursorBlockLoadedNative

/-! ## Dependency and target checker runs -/

def natKernelOutcome :=
  (RecM.checkInductiveBlock natBlockId natMembers).run checkerMethods
    checkerInitial

def natKernelAfter : TcState .anon :=
  match natKernelOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def natKernelSucceeded : Bool :=
  match natKernelOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem natKernelSucceededNative : natKernelSucceeded = true := by
  native_decide
theorem natKernelSucceeded_eq : natKernelSucceeded = true :=
  natKernelSucceededNative

theorem natKernelRun :
    (RecM.checkInductiveBlock natBlockId natMembers).run checkerMethods
      checkerInitial = .ok () natKernelAfter := by
  have success := natKernelSucceeded_eq
  unfold natKernelSucceeded at success
  unfold natKernelAfter
  generalize houtcome : natKernelOutcome = outcome at success ⊢
  cases outcome <;> simp_all [natKernelOutcome]

def familyKernelOutcome :=
  (RecM.checkInductiveBlock familyBlockId familyMembers).run checkerMethods
    natKernelAfter

def familyKernelAfter : TcState .anon :=
  match familyKernelOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def familyKernelSucceeded : Bool :=
  match familyKernelOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem familyKernelSucceededNative :
    familyKernelSucceeded = true := by
  native_decide
theorem familyKernelSucceeded_eq : familyKernelSucceeded = true :=
  familyKernelSucceededNative

theorem familyKernelRun :
    (RecM.checkInductiveBlock familyBlockId familyMembers).run checkerMethods
      natKernelAfter = .ok () familyKernelAfter := by
  have success := familyKernelSucceeded_eq
  unfold familyKernelSucceeded at success
  unfold familyKernelAfter
  generalize houtcome : familyKernelOutcome = outcome at success ⊢
  cases outcome <;> simp_all [familyKernelOutcome]

def recursorKernelOutcome :=
  (RecM.checkRecursorBlock recursorBlockId recursorMembers).run checkerMethods
    familyKernelAfter

def recursorKernelAfter : TcState .anon :=
  match recursorKernelOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def recursorKernelSucceeded : Bool :=
  match recursorKernelOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem recursorKernelSucceededNative :
    recursorKernelSucceeded = true := by
  native_decide
theorem recursorKernelSucceeded_eq : recursorKernelSucceeded = true :=
  recursorKernelSucceededNative

theorem recursorKernelRun :
    (RecM.checkRecursorBlock recursorBlockId recursorMembers).run
      checkerMethods familyKernelAfter = .ok () recursorKernelAfter := by
  have success := recursorKernelSucceeded_eq
  unfold recursorKernelSucceeded at success
  unfold recursorKernelAfter
  generalize houtcome : recursorKernelOutcome = outcome at success ⊢
  cases outcome <;> simp_all [recursorKernelOutcome]

/-! ## Exact physical ownership -/

/-- Direct ownership is the field stored by an inductive declaration.  A
constructor's ownership is resolved through its catalogued parent below. -/
private def IsDirectInductiveOwner (block : KId .anon) : KConst .anon → Prop
  | .indc (block := owner) .. => owner = block
  | _ => False

local instance directInductiveOwnerDecidable (block : KId .anon)
    (concrete : KConst .anon) :
    Decidable (IsDirectInductiveOwner block concrete) := by
  cases concrete <;> simp only [IsDirectInductiveOwner] <;> infer_instance

local instance recursorOwnerDecidable (block : KId .anon)
    (concrete : KConst .anon) :
    Decidable (concrete.IsRecursorMemberOf block) := by
  cases concrete <;>
    simp only [KConst.IsRecursorMemberOf] <;> infer_instance

private theorem directInductiveOwner_inductiveMemberOf
    {catalog : Catalog} {block : KId .anon} {concrete : KConst .anon}
    (howner : IsDirectInductiveOwner block concrete) :
    concrete.IsInductiveMemberOf catalog block := by
  cases concrete <;>
    simp_all [IsDirectInductiveOwner, KConst.IsInductiveMemberOf]

private theorem certifiedConstructor_inductiveMemberOf
    {source : Lean4Lean.VInductDecl} {familyId block : KId .anon}
    {index : Nat} {sourceConstructor : Lean4Lean.VConstVal}
    {concrete familyConcrete : KConst .anon} {catalog : Catalog}
    (hshape : concrete.IsCertifiedSingletonConstructor source familyId index
      sourceConstructor)
    (hcatalog : catalog familyId = some familyConcrete)
    (hfamilyOwner : IsDirectInductiveOwner block familyConcrete) :
    concrete.IsInductiveMemberOf catalog block := by
  cases concrete <;>
    simp_all [KConst.IsCertifiedSingletonConstructor,
      KConst.IsInductiveMemberOf, IsDirectInductiveOwner]
  exact hfamilyOwner

private theorem certifiedConstructor_not_inductiveMemberOf
    {source : Lean4Lean.VInductDecl} {familyId block : KId .anon}
    {index : Nat} {sourceConstructor : Lean4Lean.VConstVal}
    {concrete familyConcrete : KConst .anon} {catalog : Catalog}
    (hshape : concrete.IsCertifiedSingletonConstructor source familyId index
      sourceConstructor)
    (hcatalog : catalog familyId = some familyConcrete)
    (hnotOwner : ¬IsDirectInductiveOwner block familyConcrete) :
    ¬concrete.IsInductiveMemberOf catalog block := by
  intro howner
  cases concrete with
  | ctor name levelParams isUnsafe levels induct cidx params fields ty =>
      simp only [KConst.IsCertifiedSingletonConstructor] at hshape
      simp only [KConst.IsInductiveMemberOf] at howner
      obtain ⟨parentConcrete, hparentCatalog, hparentOwner⟩ := howner
      rw [hshape.2.1, hcatalog] at hparentCatalog
      have hparent : parentConcrete = familyConcrete :=
        (Option.some.inj hparentCatalog).symm
      subst parentConcrete
      exact hnotOwner hparentOwner
  | _ =>
      simp [KConst.IsCertifiedSingletonConstructor] at hshape

private theorem certifiedFamily_not_inductiveMemberOf
    {source : Lean4Lean.VInductDecl} {generation : source.GenerationChecked}
    {constructorIds : Array (KId .anon)} {concrete : KConst .anon}
    {catalog : Catalog} {block : KId .anon}
    (hshape : concrete.IsCertifiedSingletonFamily source generation
      constructorIds)
    (hnotOwner : ¬IsDirectInductiveOwner block concrete) :
    ¬concrete.IsInductiveMemberOf catalog block := by
  intro howner
  cases concrete <;>
    simp_all [KConst.IsCertifiedSingletonFamily,
      KConst.IsInductiveMemberOf, IsDirectInductiveOwner]

private theorem certifiedRecursor_not_inductiveMemberOf
    {source : Lean4Lean.VInductDecl} {generation : source.GenerationChecked}
    {constructorIds : Array (KId .anon)} {concrete : KConst .anon}
    {catalog : Catalog} {block : KId .anon}
    (hshape : concrete.IsCertifiedSingletonRecursor source generation
      constructorIds) :
    ¬concrete.IsInductiveMemberOf catalog block := by
  intro howner
  cases concrete <;>
    simp_all [KConst.IsCertifiedSingletonRecursor,
      KConst.IsInductiveMemberOf]

private theorem certifiedFamily_not_recursorMemberOf
    {source : Lean4Lean.VInductDecl} {generation : source.GenerationChecked}
    {constructorIds : Array (KId .anon)} {concrete : KConst .anon}
    {block : KId .anon}
    (hshape : concrete.IsCertifiedSingletonFamily source generation
      constructorIds) :
    ¬concrete.IsRecursorMemberOf block := by
  intro howner
  cases concrete <;>
    simp_all [KConst.IsCertifiedSingletonFamily,
      KConst.IsRecursorMemberOf]

private theorem certifiedConstructor_not_recursorMemberOf
    {source : Lean4Lean.VInductDecl} {familyId : KId .anon}
    {index : Nat} {sourceConstructor : Lean4Lean.VConstVal}
    {concrete : KConst .anon} {block : KId .anon}
    (hshape : concrete.IsCertifiedSingletonConstructor source familyId index
      sourceConstructor) :
    ¬concrete.IsRecursorMemberOf block := by
  intro howner
  cases concrete <;>
    simp_all [KConst.IsCertifiedSingletonConstructor,
      KConst.IsRecursorMemberOf]

private theorem familyDirectOwnerNative :
    IsDirectInductiveOwner familyBlockId familyConcrete := by
  native_decide
theorem familyDirectOwner :
    IsDirectInductiveOwner familyBlockId familyConcrete :=
  familyDirectOwnerNative

private theorem natNotFamilyDirectOwnerNative :
    ¬IsDirectInductiveOwner familyBlockId natConcrete := by
  native_decide
theorem natNotFamilyDirectOwner :
    ¬IsDirectInductiveOwner familyBlockId natConcrete :=
  natNotFamilyDirectOwnerNative

theorem familyOwner :
    familyConcrete.IsInductiveMemberOf catalog familyBlockId :=
  directInductiveOwner_inductiveMemberOf familyDirectOwner

theorem nilOwner :
    nilConcrete.IsInductiveMemberOf catalog familyBlockId :=
  certifiedConstructor_inductiveMemberOf nilShape catalog_family
    familyDirectOwner

theorem consOwner :
    consConcrete.IsInductiveMemberOf catalog familyBlockId :=
  certifiedConstructor_inductiveMemberOf consShape catalog_family
    familyDirectOwner

theorem natNotFamilyOwner :
    ¬natConcrete.IsInductiveMemberOf catalog familyBlockId :=
  certifiedFamily_not_inductiveMemberOf natFamilyShape
    natNotFamilyDirectOwner

theorem zeroNotFamilyOwner :
    ¬zeroConcrete.IsInductiveMemberOf catalog familyBlockId :=
  certifiedConstructor_not_inductiveMemberOf zeroShape catalog_nat
    natNotFamilyDirectOwner

theorem succNotFamilyOwner :
    ¬succConcrete.IsInductiveMemberOf catalog familyBlockId :=
  certifiedConstructor_not_inductiveMemberOf succShape catalog_nat
    natNotFamilyDirectOwner

theorem recursorNotFamilyOwner :
    ¬recursorConcrete.IsInductiveMemberOf catalog familyBlockId :=
  certifiedRecursor_not_inductiveMemberOf recursorShape

private theorem recursorOwnerNative :
    recursorConcrete.IsRecursorMemberOf recursorBlockId := by
  native_decide
theorem recursorOwner :
    recursorConcrete.IsRecursorMemberOf recursorBlockId :=
  recursorOwnerNative

theorem familyNotRecursorOwner :
    ¬familyConcrete.IsRecursorMemberOf recursorBlockId :=
  certifiedFamily_not_recursorMemberOf familyShape

theorem nilNotRecursorOwner :
    ¬nilConcrete.IsRecursorMemberOf recursorBlockId :=
  certifiedConstructor_not_recursorMemberOf nilShape

theorem consNotRecursorOwner :
    ¬consConcrete.IsRecursorMemberOf recursorBlockId :=
  certifiedConstructor_not_recursorMemberOf consShape

theorem natNotRecursorOwner :
    ¬natConcrete.IsRecursorMemberOf recursorBlockId :=
  certifiedFamily_not_recursorMemberOf natFamilyShape

theorem zeroNotRecursorOwner :
    ¬zeroConcrete.IsRecursorMemberOf recursorBlockId :=
  certifiedConstructor_not_recursorMemberOf zeroShape

theorem succNotRecursorOwner :
    ¬succConcrete.IsRecursorMemberOf recursorBlockId :=
  certifiedConstructor_not_recursorMemberOf succShape

/-- Every successful lookup in the fixture's explicit semantic catalog is
one of its seven declaration entries. -/
theorem catalog_entry_cases {id : KId .anon} {concrete : KConst .anon}
    (hcatalog : catalog id = some concrete) :
    (id = familyId ∧ concrete = familyConcrete) ∨
      (id = nilId ∧ concrete = nilConcrete) ∨
      (id = consId ∧ concrete = consConcrete) ∨
      (id = recursorId ∧ concrete = recursorConcrete) ∨
      (id = natId ∧ concrete = natConcrete) ∨
      (id = zeroId ∧ concrete = zeroConcrete) ∨
      (id = succId ∧ concrete = succConcrete) := by
  unfold catalog at hcatalog
  split at hcatalog
  · left
    exact ⟨eq_of_beq (by assumption), (Option.some.inj hcatalog).symm⟩
  · split at hcatalog
    · right; left
      exact ⟨eq_of_beq (by assumption), (Option.some.inj hcatalog).symm⟩
    · split at hcatalog
      · right; right; left
        exact ⟨eq_of_beq (by assumption),
          (Option.some.inj hcatalog).symm⟩
      · split at hcatalog
        · right; right; right; left
          exact ⟨eq_of_beq (by assumption),
            (Option.some.inj hcatalog).symm⟩
        · split at hcatalog
          · right; right; right; right; left
            exact ⟨eq_of_beq (by assumption),
              (Option.some.inj hcatalog).symm⟩
          · split at hcatalog
            · right; right; right; right; right; left
              exact ⟨eq_of_beq (by assumption),
                (Option.some.inj hcatalog).symm⟩
            · split at hcatalog
              · right; right; right; right; right; right
                exact ⟨eq_of_beq (by assumption),
                  (Option.some.inj hcatalog).symm⟩
              · contradiction

theorem familyCoordinated_iff (id : KId .anon) :
    id ∈ familyMembers ↔
      catalog.CoordinatedMember familyBlockId .inductive' id := by
  constructor
  · intro hmember
    simp [familyMembers_eq] at hmember
    rcases hmember with rfl | rfl | rfl
    · exact ⟨familyConcrete, catalog_family, familyOwner⟩
    · exact ⟨nilConcrete, catalog_nil, nilOwner⟩
    · exact ⟨consConcrete, catalog_cons, consOwner⟩
  · rintro ⟨concrete, hcatalog, howner⟩
    rcases catalog_entry_cases hcatalog with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [familyMembers_eq]
    · simp [familyMembers_eq]
    · simp [familyMembers_eq]
    · exact False.elim (recursorNotFamilyOwner howner)
    · exact False.elim (natNotFamilyOwner howner)
    · exact False.elim (zeroNotFamilyOwner howner)
    · exact False.elim (succNotFamilyOwner howner)

theorem recursorCoordinated_iff (id : KId .anon) :
    id ∈ recursorMembers ↔
      catalog.CoordinatedMember recursorBlockId .recursor id := by
  constructor
  · intro hmember
    rw [recursorMembers_eq] at hmember
    have hid : id = recursorId := by simpa using hmember
    subst id
    exact ⟨recursorConcrete, catalog_recursor, recursorOwner⟩
  · rintro ⟨concrete, hcatalog, howner⟩
    rcases catalog_entry_cases hcatalog with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact False.elim (familyNotRecursorOwner howner)
    · exact False.elim (nilNotRecursorOwner howner)
    · exact False.elim (consNotRecursorOwner howner)
    · simp [recursorMembers_eq]
    · exact False.elim (natNotRecursorOwner howner)
    · exact False.elim (zeroNotRecursorOwner howner)
    · exact False.elim (succNotRecursorOwner howner)

theorem world_family_block :
    world.blocks familyBlockId = some familyMembers := by
  change recursorIngressAfter.getBlock? familyBlockId = some familyMembers
  simpa [checkerInitial, TcState.ofEnvAnon] using familyBlockLoaded

theorem world_recursor_block :
    world.blocks recursorBlockId = some recursorMembers := by
  change recursorIngressAfter.getBlock? recursorBlockId = some recursorMembers
  simpa [checkerInitial, TcState.ofEnvAnon] using recursorBlockLoaded

def exactFamilyBlock :
    ExactCheckBlock world familyBlockId familyMembers .inductive' where
  blockLookup := world_family_block
  nonempty := by rw [familyMembers_eq]; decide
  memberIff := fun id => familyCoordinated_iff id

def exactRecursorBlock :
    ExactCheckBlock world recursorBlockId recursorMembers .recursor where
  blockLookup := world_recursor_block
  nonempty := by rw [recursorMembers_eq]; decide
  memberIff := fun id => recursorCoordinated_iff id

/-! ## Semantic admission of the checked blocks -/

/-- The catalog link's semantic member order is the exact physical family
block order consumed by the production checker. -/
theorem familyLink_members_eq : familyLink.members = familyMembers := by
  rfl

/-- Complete consumer-facing provenance for an exact physical member of the
certified `IndexedVec` family transaction. -/
private def familySemanticEntry {id : KId .anon}
    (hmember : id ∈ familyMembers) :
    TrustedCatalogEntry RawProjRel.none world.catalog world.nameOf
      indexedVecFinalEnv id := by
  have hlinked : id ∈ familyLink.members := by
    rw [familyLink_members_eq]
    exact hmember
  obtain ⟨concrete, name, ci, hcatalog, hraw, hlookup, hwf⟩ :=
    familyLink.translateMember hlinked
  exact .ambient hcatalog hraw hlookup hwf
    (by
      intro rule hrule
      exact False.elim
        (familyLink.noRecursorRule hlinked hcatalog rule hrule))
    (by
      intro ruleIndex rule hrule
      exact False.elim
        (familyLink.noRecursorRuleAt hlinked hcatalog
          ruleIndex rule hrule))

def familyBlockCertificate :
    SemanticBlockTransitionCertificate RawProjRel.none world familyBlockId
      familyMembers .inductive' indexedVecFinalEnv where
  exactBlock := exactFamilyBlock
  fresh := by
    intro id hmember
    have hlinked : id ∈ familyLink.members := by
      rw [familyLink_members_eq]
      exact hmember
    exact familyLink.fresh id hlinked
  envLE := transaction.facts.envLE
  afterWF := transaction.facts.afterWF
  entry := fun {_} hmember => familySemanticEntry hmember

def familyAcceptedWorld : VerifyWorld :=
  familyBlockCertificate.admittedWorld

theorem familyAtomicAdmission :
    AtomicBlockAdmission RawProjRel.none world familyAcceptedWorld
      familyBlockId familyMembers .inductive' :=
  familyBlockCertificate.admit trustedCatalog

theorem familyBlockAccepted :
    familyAcceptedWorld.AcceptedBlock familyBlockId :=
  familyAtomicAdmission.accepted

/-- The exact indexed-recursive recursor transaction, including the
dependent equality checks and recursive `cons` equation. -/
def recursorBlockOracle : InductiveOracle RawProjRel.none world.catalog
    world.nameOf world.trusted world.venv :=
  IndexedRecursivePattern.oracle recursorLink

def recursorAcceptedWorld : VerifyWorld :=
  world.admitOracle recursorBlockOracle

def recursorBlockCertificate : OracleBlockCertificate RawProjRel.none world
    recursorBlockId recursorMembers .recursor where
  oracleBacked := trivial
  exactBlock := exactRecursorBlock
  oracle := recursorBlockOracle
  memberIff := fun id =>
    IndexedRecursivePattern.oracle_members_iff recursorLink id

theorem recursorAtomicAdmission :
    AtomicBlockAdmission RawProjRel.none world recursorAcceptedWorld
      recursorBlockId recursorMembers .recursor :=
  recursorBlockCertificate.admit trustedCatalog

theorem recursorBlockAccepted :
    recursorAcceptedWorld.AcceptedBlock recursorBlockId :=
  recursorAtomicAdmission.accepted

/-! ## Adversarial recursor metadata -/

/-- Change only the stored index arity.  The type and rules still have the
canonical IndexedVec shape, so accepting this declaration would demonstrate
that the production comparison was coherence-only instead of exhaustive. -/
def corruptRecursorIndexArity : KConst .anon → KConst .anon
  | .recr name levelParams k isUnsafe lvls params indices motives minors block
      memberIdx ty rules leanAll =>
    .recr name levelParams k isUnsafe lvls params (indices + 1) motives minors
      block memberIdx ty rules leanAll
  | concrete => concrete

def malformedRecursorConcrete : KConst .anon :=
  corruptRecursorIndexArity recursorConcrete

/-- Retain the generated recursor cache produced by the successful family
check, but replace the separately ingressed recursor declaration with the
single-field adversarial mutation. -/
def malformedRecursorInitial : TcState .anon :=
  { familyKernelAfter with
    env := familyKernelAfter.env.insert recursorId malformedRecursorConcrete }

def malformedRecursorOutcome :=
  (RecM.checkRecursorBlock recursorBlockId recursorMembers).run
    checkerMethods malformedRecursorInitial

def malformedRecursorRejected : Bool :=
  match malformedRecursorOutcome with
  | .ok _ _ => false
  | .error _ _ => true

private theorem malformedRecursorRejectedNative :
    malformedRecursorRejected = true := by
  native_decide

/-- The actual production recursor checker rejects the declaration whose
index-arity metadata disagrees with the recursor generated from the certified
family block. -/
theorem malformedRecursorRun :
    ∃ error after,
      (RecM.checkRecursorBlock recursorBlockId recursorMembers).run
        checkerMethods malformedRecursorInitial = .error error after := by
  have rejection := malformedRecursorRejectedNative
  unfold malformedRecursorRejected at rejection
  generalize houtcome : malformedRecursorOutcome = outcome at rejection
  cases outcome with
  | ok value after => simp at rejection
  | error error after =>
      refine ⟨error, after, ?_⟩
      simpa [malformedRecursorOutcome] using houtcome

/-! ## End-to-end executable witness -/

/-- One premise-free statement joins the three dependency-ordered production
ingress runs, all three checker branches, the exact family/recursor block
identities, their semantic admissions, and the metadata attack rejection. -/
structure EndToEndAcceptance : Prop where
  natIngress : natIngressOutcome = .ok natIngressResult natIngressAfter
  familyIngress : familyIngressOutcome =
    .ok familyIngressResult familyIngressAfter
  recursorIngress : recursorIngressOutcome =
    .ok recursorIngressResult recursorIngressAfter
  natKernel :
    (RecM.checkInductiveBlock natBlockId natMembers).run checkerMethods
      checkerInitial = .ok () natKernelAfter
  familyKernel :
    (RecM.checkInductiveBlock familyBlockId familyMembers).run checkerMethods
      natKernelAfter = .ok () familyKernelAfter
  recursorKernel :
    (RecM.checkRecursorBlock recursorBlockId recursorMembers).run
      checkerMethods familyKernelAfter = .ok () recursorKernelAfter
  exactFamily :
    ExactCheckBlock world familyBlockId familyMembers .inductive'
  exactRecursor :
    ExactCheckBlock world recursorBlockId recursorMembers .recursor
  admittedFamily :
    AtomicBlockAdmission RawProjRel.none world familyAcceptedWorld
      familyBlockId familyMembers .inductive'
  admittedRecursor :
    AtomicBlockAdmission RawProjRel.none world recursorAcceptedWorld
      recursorBlockId recursorMembers .recursor
  rejectsMalformedRecursor :
    ∃ error after,
      (RecM.checkRecursorBlock recursorBlockId recursorMembers).run
        checkerMethods malformedRecursorInitial = .error error after

theorem endToEndAcceptance : EndToEndAcceptance where
  natIngress := natIngressRun
  familyIngress := familyIngressRun
  recursorIngress := recursorIngressRun
  natKernel := natKernelRun
  familyKernel := familyKernelRun
  recursorKernel := recursorKernelRun
  exactFamily := exactFamilyBlock
  exactRecursor := exactRecursorBlock
  admittedFamily := familyAtomicAdmission
  admittedRecursor := recursorAtomicAdmission
  rejectsMalformedRecursor := malformedRecursorRun

end Ix.Tc.IndexedRecursiveFixture
