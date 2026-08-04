import Ix.Tc.Verify.Inductive.EnumerationFixture
import Ix.Tc.Verify.Inductive.OneFamilyAdmission

/-!
# Concrete singleton-enumeration checker acceptance

This module runs the production coordinated-block body over the Boolean
ingress fixture.  The family block is checked first so that production
constructs its canonical recursor cache; the separate recursor block is then
checked against that exact generated result.
-/

namespace Ix.Tc

namespace BooleanEnumerationFixture

local instance acceptanceAnonKIdDecidableEq : DecidableEq (KId .anon) :=
  fun left right =>
    if h : left == right then
      .isTrue (eq_of_beq h)
    else
      .isFalse fun equality => h (by cases equality; exact beq_self_eq_true left)

/-- Physical owner keys, distinct from the projected declaration ids stored
as block members. -/
def familyBlockId : KId .anon := ⟨familyBlockAddress, ()⟩
def recursorBlockId : KId .anon := ⟨recursorBlockAddress, ()⟩

def familyMembers : Array (KId .anon) := familyLink.members
def recursorMembers : Array (KId .anon) := recursorLink.members

theorem familyMembers_eq : familyMembers = #[familyId, falseId, trueId] := by
  rfl

theorem recursorMembers_eq : recursorMembers = #[recursorId] := by
  rfl

/-- A finite production method table large enough for both concrete runs.
The value is fixture data, not a semantic assumption: both success equations
below are checked by native evaluation. -/
def checkerFuel : UInt64 := 256

def checkerMethods : Methods .anon := methodsN checkerFuel.toNat

def checkerInitial : TcState .anon :=
  { TcState.ofEnvAnon recursorIngressAfter with
    recFuel := checkerFuel
    fuelBudget := checkerFuel }

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

/-! ## Family production run -/

def familyBodyOutcome :=
  (RecM.checkBlockBody familyBlockId familyId).run checkerMethods
    checkerInitial

def familyBodyAfter : TcState .anon :=
  match familyBodyOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def familyBodySucceeded : Bool :=
  match familyBodyOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem familyBodySucceededNative : familyBodySucceeded = true := by
  native_decide

theorem familyBodySucceeded_eq : familyBodySucceeded = true :=
  familyBodySucceededNative

theorem familyBodyRun :
    (RecM.checkBlockBody familyBlockId familyId).run checkerMethods
      checkerInitial = .ok () familyBodyAfter := by
  have success := familyBodySucceeded_eq
  unfold familyBodySucceeded at success
  unfold familyBodyAfter
  generalize houtcome : familyBodyOutcome = outcome at success ⊢
  cases outcome <;> simp_all [familyBodyOutcome]

def familyClassificationOutcome :=
  (RecM.classifyBlock familyMembers).run checkerMethods checkerInitial

def familyClassifiedAfter : TcState .anon :=
  match familyClassificationOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def familyClassificationSucceeded : Bool :=
  match familyClassificationOutcome with
  | .ok .inductive' _ => true
  | .ok _ _ => false
  | .error _ _ => false

private theorem familyClassificationSucceededNative :
    familyClassificationSucceeded = true := by
  native_decide

theorem familyClassificationSucceeded_eq :
    familyClassificationSucceeded = true :=
  familyClassificationSucceededNative

theorem familyClassificationRun :
    familyClassificationOutcome =
      .ok .inductive' familyClassifiedAfter := by
  have success := familyClassificationSucceeded_eq
  unfold familyClassificationSucceeded at success
  unfold familyClassifiedAfter
  generalize houtcome : familyClassificationOutcome = outcome at success ⊢
  cases outcome with
  | error => simp at success
  | ok kind after =>
      cases kind <;> simp_all

/-- Exact production lookup, classification, and inductive branch trace. -/
def familyBodyTrace : RecM.ExactBlockBodySuccessTrace checkerMethods
    familyBlockId familyId familyMembers .inductive' checkerInitial
      familyBodyAfter := by
  obtain ⟨actualMembers, actualKind, trace⟩ :=
    RecM.checkBlockBody_success_trace familyBodyRun
  cases trace with
  | run loaded classified hlookup hclass hcheck =>
      have expectedLookup := TcM.tryGetBlock_of_loaded familyBlockLoaded
      have hlookupEq :=
        EStateM.Result.ok.inj (hlookup.symm.trans expectedLookup)
      have hmembers : actualMembers = familyMembers :=
        Option.some.inj hlookupEq.1
      have hloaded : loaded = checkerInitial := hlookupEq.2
      subst actualMembers
      subst loaded
      have hclassEq := EStateM.Result.ok.inj
        (hclass.symm.trans familyClassificationRun)
      have hkind : actualKind = .inductive' := hclassEq.1
      have hclassified : classified = familyClassifiedAfter := hclassEq.2
      subst actualKind
      subst classified
      exact .run checkerInitial familyClassifiedAfter expectedLookup
        familyClassificationRun hcheck

/-- The production inductive checker itself succeeds on the same physical
family array, independently of the surrounding classification wrapper. -/
def familyKernelOutcome :=
  (RecM.checkInductiveBlock familyBlockId familyMembers).run checkerMethods
    checkerInitial

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
      checkerInitial = .ok () familyKernelAfter := by
  have success := familyKernelSucceeded_eq
  unfold familyKernelSucceeded at success
  unfold familyKernelAfter
  generalize houtcome : familyKernelOutcome = outcome at success ⊢
  cases outcome <;> simp_all [familyKernelOutcome]

/-! ## Recursor production run -/

private theorem recursorBlockLoadedAfterFamilyNative :
    familyBodyAfter.env.getBlock? recursorBlockId = some recursorMembers := by
  native_decide

theorem recursorBlockLoadedAfterFamily :
    familyBodyAfter.env.getBlock? recursorBlockId = some recursorMembers :=
  recursorBlockLoadedAfterFamilyNative

def recursorBodyOutcome :=
  (RecM.checkBlockBody recursorBlockId recursorId).run checkerMethods
    familyBodyAfter

def recursorBodyAfter : TcState .anon :=
  match recursorBodyOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def recursorBodySucceeded : Bool :=
  match recursorBodyOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem recursorBodySucceededNative :
    recursorBodySucceeded = true := by
  native_decide

theorem recursorBodySucceeded_eq : recursorBodySucceeded = true :=
  recursorBodySucceededNative

theorem recursorBodyRun :
    (RecM.checkBlockBody recursorBlockId recursorId).run checkerMethods
      familyBodyAfter = .ok () recursorBodyAfter := by
  have success := recursorBodySucceeded_eq
  unfold recursorBodySucceeded at success
  unfold recursorBodyAfter
  generalize houtcome : recursorBodyOutcome = outcome at success ⊢
  cases outcome <;> simp_all [recursorBodyOutcome]

def recursorClassificationOutcome :=
  (RecM.classifyBlock recursorMembers).run checkerMethods familyBodyAfter

def recursorClassifiedAfter : TcState .anon :=
  match recursorClassificationOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def recursorClassificationSucceeded : Bool :=
  match recursorClassificationOutcome with
  | .ok .recursor _ => true
  | .ok _ _ => false
  | .error _ _ => false

private theorem recursorClassificationSucceededNative :
    recursorClassificationSucceeded = true := by
  native_decide

theorem recursorClassificationSucceeded_eq :
    recursorClassificationSucceeded = true :=
  recursorClassificationSucceededNative

theorem recursorClassificationRun :
    recursorClassificationOutcome =
      .ok .recursor recursorClassifiedAfter := by
  have success := recursorClassificationSucceeded_eq
  unfold recursorClassificationSucceeded at success
  unfold recursorClassifiedAfter
  generalize houtcome : recursorClassificationOutcome = outcome
    at success ⊢
  cases outcome with
  | error => simp at success
  | ok kind after =>
      cases kind <;> simp_all

/-- Exact production lookup, classification, and recursor branch trace. -/
def recursorBodyTrace : RecM.ExactBlockBodySuccessTrace checkerMethods
    recursorBlockId recursorId recursorMembers .recursor familyBodyAfter
      recursorBodyAfter := by
  obtain ⟨actualMembers, actualKind, trace⟩ :=
    RecM.checkBlockBody_success_trace recursorBodyRun
  cases trace with
  | run loaded classified hlookup hclass hcheck =>
      have expectedLookup :=
        TcM.tryGetBlock_of_loaded recursorBlockLoadedAfterFamily
      have hlookupEq :=
        EStateM.Result.ok.inj (hlookup.symm.trans expectedLookup)
      have hmembers : actualMembers = recursorMembers :=
        Option.some.inj hlookupEq.1
      have hloaded : loaded = familyBodyAfter := hlookupEq.2
      subst actualMembers
      subst loaded
      have hclassEq := EStateM.Result.ok.inj
        (hclass.symm.trans recursorClassificationRun)
      have hkind : actualKind = .recursor := hclassEq.1
      have hclassified : classified = recursorClassifiedAfter := hclassEq.2
      subst actualKind
      subst classified
      exact .run familyBodyAfter recursorClassifiedAfter expectedLookup
        recursorClassificationRun hcheck

/-- The production recursor checker succeeds after the family run has
populated the canonical generated-recursor cache it consumes. -/
def recursorKernelOutcome :=
  (RecM.checkRecursorBlock recursorBlockId recursorMembers).run checkerMethods
    familyBodyAfter

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
      checkerMethods familyBodyAfter = .ok () recursorKernelAfter := by
  have success := recursorKernelSucceeded_eq
  unfold recursorKernelSucceeded at success
  unfold recursorKernelAfter
  generalize houtcome : recursorKernelOutcome = outcome at success ⊢
  cases outcome <;> simp_all [recursorKernelOutcome]

/-! ## Exact immutable block ownership -/

/-- Direct physical ownership of the family declaration.  Constructors use
the catalogued parent relation below, so this discriminator intentionally
covers only the `.indc` case. -/
private def IsDirectInductiveOwner (block : KId .anon) :
    KConst .anon → Prop
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

private theorem familyDirectOwnerNative :
    IsDirectInductiveOwner familyBlockId familyConcrete := by
  native_decide

theorem familyDirectOwner :
    IsDirectInductiveOwner familyBlockId familyConcrete :=
  familyDirectOwnerNative

private theorem directInductiveOwner_inductiveMemberOf
    {catalog : Catalog} {block : KId .anon} {concrete : KConst .anon}
    (howner : IsDirectInductiveOwner block concrete) :
    concrete.IsInductiveMemberOf catalog block := by
  cases concrete <;>
    simp_all [IsDirectInductiveOwner, KConst.IsInductiveMemberOf]

theorem familyOwner :
    familyConcrete.IsInductiveMemberOf catalog familyBlockId :=
  directInductiveOwner_inductiveMemberOf familyDirectOwner

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

theorem falseOwner :
    falseConcrete.IsInductiveMemberOf catalog familyBlockId :=
  certifiedConstructor_inductiveMemberOf falseShape catalog_family
    familyDirectOwner

theorem trueOwner :
    trueConcrete.IsInductiveMemberOf catalog familyBlockId :=
  certifiedConstructor_inductiveMemberOf trueShape catalog_family
    familyDirectOwner

private theorem recursorOwnerNative :
    recursorConcrete.IsRecursorMemberOf recursorBlockId := by
  native_decide

theorem recursorOwner :
    recursorConcrete.IsRecursorMemberOf recursorBlockId :=
  recursorOwnerNative

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

theorem recursorNotFamilyOwner :
    ¬recursorConcrete.IsInductiveMemberOf catalog familyBlockId :=
  certifiedRecursor_not_inductiveMemberOf recursorShape

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

theorem familyNotRecursorOwner :
    ¬familyConcrete.IsRecursorMemberOf recursorBlockId :=
  certifiedFamily_not_recursorMemberOf familyShape

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

theorem falseNotRecursorOwner :
    ¬falseConcrete.IsRecursorMemberOf recursorBlockId :=
  certifiedConstructor_not_recursorMemberOf falseShape

theorem trueNotRecursorOwner :
    ¬trueConcrete.IsRecursorMemberOf recursorBlockId :=
  certifiedConstructor_not_recursorMemberOf trueShape

/-- Every successful lookup in the fixture's explicit semantic catalog is
one of its four declaration entries. -/
theorem catalog_entry_cases {id : KId .anon} {concrete : KConst .anon}
    (hcatalog : catalog id = some concrete) :
    (id = familyId ∧ concrete = familyConcrete) ∨
      (id = falseId ∧ concrete = falseConcrete) ∨
      (id = trueId ∧ concrete = trueConcrete) ∨
      (id = recursorId ∧ concrete = recursorConcrete) := by
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
        · right; right; right
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
    · exact ⟨falseConcrete, catalog_false, falseOwner⟩
    · exact ⟨trueConcrete, catalog_true, trueOwner⟩
  · rintro ⟨concrete, hcatalog, howner⟩
    rcases catalog_entry_cases hcatalog with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [familyMembers_eq]
    · simp [familyMembers_eq]
    · simp [familyMembers_eq]
    · exact False.elim (recursorNotFamilyOwner howner)

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
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact False.elim (familyNotRecursorOwner howner)
    · exact False.elim (falseNotRecursorOwner howner)
    · exact False.elim (trueNotRecursorOwner howner)
    · simp [recursorMembers_eq]

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

/-! ## Explicit family transition -/

theorem familyLink_members_eq : familyLink.members = familyMembers := by
  rfl

/-- Complete post-generation provenance for one exact family-block member.
Family and constructor constants have no recursor rules, so their rule and
pattern obligations close from their certified concrete shapes. -/
private def familySemanticEntry {id : KId .anon}
    (hmember : id ∈ familyMembers) :
    TrustedCatalogEntry RawProjRel.none world.catalog world.nameOf theoryAfter
      id := by
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
        (familyLink.noRecursorRuleAt hlinked hcatalog ruleIndex rule hrule))

/-- The exact Boolean family block advances the explicitly named Theory
environment produced by its checked generation transaction. -/
def familyBlockCertificate :
    SemanticBlockTransitionCertificate RawProjRel.none world familyBlockId
      familyMembers .inductive' theoryAfter where
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

/-- The intermediate world after exactly the family and its constructors are
trusted and the certified generation environment is installed. -/
def familyAcceptedWorld : VerifyWorld :=
  familyBlockCertificate.admittedWorld

theorem familyAtomicAdmission :
    AtomicBlockAdmission RawProjRel.none world familyAcceptedWorld
      familyBlockId familyMembers .inductive' :=
  familyBlockCertificate.admit trustedCatalog

/-! ## Existing generated-recursor transition -/

/-- Complete provenance for the generated Boolean recursor in the Theory
environment installed by the family transaction.  Both concrete rules are
linked to their registered generated equations and exact enumeration iota
patterns. -/
private def recursorSemanticEntryBase :
    TrustedCatalogEntry RawProjRel.none world.catalog world.nameOf theoryAfter
      recursorId := by
  obtain ⟨hraw, hlookup, hwf⟩ := recursorLink.translateRecursor
  refine .ambient catalog_recursor hraw hlookup hwf ?_ ?_
  · intro rule hrule
    exact recursorLink.registeredRule hrule
  · intro ruleIndex rule hrule
    exact recursorLink.enumerationPatternRel enumerationShape hrule

def familyRecursorSemanticEntry :
    TrustedCatalogEntry RawProjRel.none familyAcceptedWorld.catalog
      familyAcceptedWorld.nameOf familyAcceptedWorld.venv recursorId := by
  change TrustedCatalogEntry RawProjRel.none world.catalog world.nameOf
    theoryAfter recursorId
  exact recursorSemanticEntryBase

theorem familyAcceptedWorld_recursor_fresh :
    ¬familyAcceptedWorld.trusted recursorId := by
  intro htrusted
  change recursorId ∈ familyMembers ∨ world.trusted recursorId at htrusted
  rcases htrusted with hfamily | hold
  · have hcoordinated := (familyCoordinated_iff recursorId).1 hfamily
    obtain ⟨concrete, hcatalog, howner⟩ := hcoordinated
    rw [catalog_recursor] at hcatalog
    cases hcatalog
    exact recursorNotFamilyOwner howner
  · exact recursorLink.fresh hold

def exactRecursorBlockAfterFamily :
    ExactCheckBlock familyAcceptedWorld recursorBlockId recursorMembers
      .recursor :=
  exactRecursorBlock.rebaseWorld familyAtomicAdmission.promotion.le

/-- The separately stored recursor block consumes semantic entries already
installed by the family transition; it does not choose another future Theory
environment. -/
def recursorBlockCertificate :
    ExistingSemanticBlockCertificate RawProjRel.none familyAcceptedWorld
      recursorBlockId recursorMembers .recursor where
  exactBlock := exactRecursorBlockAfterFamily
  fresh := by
    intro id hmember
    have hid : id = recursorId := by
      simpa [recursorMembers_eq] using hmember
    subst id
    exact familyAcceptedWorld_recursor_fresh
  entry := by
    intro id hmember
    have hid : id = recursorId := by
      simpa [recursorMembers_eq] using hmember
    subst id
    exact familyRecursorSemanticEntry

/-- The Boolean family/constructor block and generated-recursor block form
one explicit two-stage semantic transaction. -/
def oneFamilyCertificate :
    OneFamilyRecursorCertificate RawProjRel.none world familyBlockId
      familyMembers recursorBlockId recursorMembers theoryAfter where
  family := familyBlockCertificate
  recursor := recursorBlockCertificate

/-- The final world after both exact physical blocks are trusted. -/
def recursorAcceptedWorld : VerifyWorld :=
  oneFamilyCertificate.admittedWorld

theorem recursorAtomicAdmission :
    AtomicBlockAdmission RawProjRel.none familyAcceptedWorld recursorAcceptedWorld
      recursorBlockId recursorMembers .recursor :=
  oneFamilyCertificate.recursorAdmission trustedCatalog

theorem oneFamilyAtomicClosure : oneFamilyCertificate.AtomicClosure :=
  oneFamilyCertificate.atomicClosure trustedCatalog

theorem familyBlockAccepted :
    recursorAcceptedWorld.AcceptedBlock familyBlockId :=
  oneFamilyAtomicClosure.familyAccepted

theorem recursorBlockAccepted :
    recursorAcceptedWorld.AcceptedBlock recursorBlockId :=
  oneFamilyAtomicClosure.recursorAccepted

/-! ## End-to-end executable witness -/

/-- The supported Boolean fragment in one proposition.  It starts with the two
actual anonymous-ingress calls, runs the production coordinated checker and
its concrete inductive/recursor branches, and ends in exact stable block
acceptance in one composed explicit semantic world.  There is no reflection,
oracle-selected future world, or arbitrary-regeneration premise in this
witness. -/
structure EndToEndAcceptance : Prop where
  familyIngress : familyIngressOutcome =
    .ok familyIngressResult familyIngressAfter
  recursorIngress : recursorIngressOutcome =
    .ok recursorIngressResult recursorIngressAfter
  familyBody :
    (RecM.checkBlockBody familyBlockId familyId).run checkerMethods
      checkerInitial = .ok () familyBodyAfter
  recursorBody :
    (RecM.checkBlockBody recursorBlockId recursorId).run checkerMethods
      familyBodyAfter = .ok () recursorBodyAfter
  familyTrace : RecM.ExactBlockBodySuccessTrace checkerMethods
    familyBlockId familyId familyMembers .inductive' checkerInitial
      familyBodyAfter
  recursorTrace : RecM.ExactBlockBodySuccessTrace checkerMethods
    recursorBlockId recursorId recursorMembers .recursor familyBodyAfter
      recursorBodyAfter
  familyKernel :
    (RecM.checkInductiveBlock familyBlockId familyMembers).run checkerMethods
      checkerInitial = .ok () familyKernelAfter
  recursorKernel :
    (RecM.checkRecursorBlock recursorBlockId recursorMembers).run
      checkerMethods familyBodyAfter = .ok () recursorKernelAfter
  exactFamily :
    ExactCheckBlock world familyBlockId familyMembers .inductive'
  exactRecursor :
    ExactCheckBlock world recursorBlockId recursorMembers .recursor
  familyAdmission :
    AtomicBlockAdmission RawProjRel.none world familyAcceptedWorld
      familyBlockId familyMembers .inductive'
  recursorAdmission :
    AtomicBlockAdmission RawProjRel.none familyAcceptedWorld
      recursorAcceptedWorld recursorBlockId recursorMembers .recursor
  oneFamily : oneFamilyCertificate.AtomicClosure
  acceptedFamily : recursorAcceptedWorld.AcceptedBlock familyBlockId
  acceptedRecursor : recursorAcceptedWorld.AcceptedBlock recursorBlockId

theorem endToEndAcceptance : EndToEndAcceptance where
  familyIngress := familyIngressRun
  recursorIngress := recursorIngressRun
  familyBody := familyBodyRun
  recursorBody := recursorBodyRun
  familyTrace := familyBodyTrace
  recursorTrace := recursorBodyTrace
  familyKernel := familyKernelRun
  recursorKernel := recursorKernelRun
  exactFamily := exactFamilyBlock
  exactRecursor := exactRecursorBlock
  familyAdmission := familyAtomicAdmission
  recursorAdmission := recursorAtomicAdmission
  oneFamily := oneFamilyAtomicClosure
  acceptedFamily := familyBlockAccepted
  acceptedRecursor := recursorBlockAccepted

end BooleanEnumerationFixture

end Ix.Tc
