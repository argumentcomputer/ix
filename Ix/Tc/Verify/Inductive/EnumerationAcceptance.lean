import Ix.Tc.Verify.Inductive.EnumerationFixture

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

/-! ## Semantic admission of the checked blocks -/

/-- The family transaction exposed by the exact Ix/source catalog link. -/
def familyBlockOracle : InductiveOracle RawProjRel.none world.catalog
    world.nameOf world.trusted world.venv :=
  familyLink.oracle

/-- The stable world obtained by admitting exactly the checked family array. -/
def familyAcceptedWorld : VerifyWorld :=
  world.admitOracle familyBlockOracle

/-- The production family array and the semantic family transaction have
exactly the same members. -/
def familyBlockCertificate : OracleBlockCertificate RawProjRel.none world
    familyBlockId familyMembers .inductive' where
  oracleBacked := trivial
  exactBlock := exactFamilyBlock
  oracle := familyBlockOracle
  memberIff := fun id => familyLink.oracle_members_iff id

theorem familyAtomicAdmission :
    AtomicBlockAdmission RawProjRel.none world familyAcceptedWorld
      familyBlockId familyMembers .inductive' :=
  familyBlockCertificate.admit trustedCatalog

theorem familyBlockAccepted :
    familyAcceptedWorld.AcceptedBlock familyBlockId :=
  familyAtomicAdmission.accepted

/-- The recursor transaction exposed by the exact Ix/source catalog link,
including both generated Boolean reduction equations. -/
def recursorBlockOracle : InductiveOracle RawProjRel.none world.catalog
    world.nameOf world.trusted world.venv :=
  recursorLink.oracle enumerationShape

/-- The stable world obtained by admitting exactly the checked recursor
array.  It is stated separately from `familyAcceptedWorld`: both physical
blocks interpret the same certified Lean4Lean generation transaction, while
their trust deltas are intentionally their distinct exact member arrays. -/
def recursorAcceptedWorld : VerifyWorld :=
  world.admitOracle recursorBlockOracle

def recursorBlockCertificate : OracleBlockCertificate RawProjRel.none world
    recursorBlockId recursorMembers .recursor where
  oracleBacked := trivial
  exactBlock := exactRecursorBlock
  oracle := recursorBlockOracle
  memberIff := fun id => recursorLink.oracle_members_iff enumerationShape id

theorem recursorAtomicAdmission :
    AtomicBlockAdmission RawProjRel.none world recursorAcceptedWorld
      recursorBlockId recursorMembers .recursor :=
  recursorBlockCertificate.admit trustedCatalog

theorem recursorBlockAccepted :
    recursorAcceptedWorld.AcceptedBlock recursorBlockId :=
  recursorAtomicAdmission.accepted

/-! ## End-to-end executable witness -/

/-- The supported E2b fragment in one proposition.  It starts with the two
actual anonymous-ingress calls, runs the production coordinated checker and
its concrete inductive/recursor branches, and ends in exact stable block
acceptance derived from the same catalog links.  There is no reflection or
arbitrary-regeneration premise in this witness. -/
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
  acceptedFamily : familyAcceptedWorld.AcceptedBlock familyBlockId
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
  acceptedFamily := familyBlockAccepted
  acceptedRecursor := recursorBlockAccepted

end BooleanEnumerationFixture

end Ix.Tc
