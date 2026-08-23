import Ix.Tc.Verify.Driver.SupportedAcceptance
import Ix.Tc.Verify.Inductive.EnumerationAcceptance

/-!
# Certificate-backed Boolean driver acceptance

This module connects the concrete E2 Boolean generation certificate to the
E3-S production-driver adapter.  The runtime checker call remains a required
gate, but semantic authority for these two coordinated blocks comes from the
fixed family transition and existing-recursor certificates.  In particular,
the proof does not reinterpret the runtime cache order as a topological
semantic schedule: the recursor work item is physically enumerated first,
while its successful checker call also validates and caches the family block.

The staged baseline below has the constructively generated Boolean Theory
environment and an empty trust predicate.  Its `VEnv.WF` field is derived
from `CertifiedGenerationTransaction`; it is not an assumed target-world
well-formedness premise.  The certificates' per-member semantic entries are
then transported to each monotone current world and replayed idempotently;
neither row constructs or admits an `InductiveOracle`.
-/

namespace Ix.Tc

namespace BooleanEnumerationFixture

local instance booleanAddressDecidableEq : DecidableEq Address :=
  fun left right =>
    if h : left == right then
      .isTrue (eq_of_beq h)
    else
      .isFalse fun equality => h (by
        cases equality
        exact beq_self_eq_true left)

/- Executable equality is used only to discharge closed native facts about
the finite serialized fixture.  These instances compare the actual inductive
data; no address-hash injectivity principle is involved. -/
deriving instance DecidableEq for Ixon.Univ
deriving instance DecidableEq for Ixon.Expr
deriving instance DecidableEq for Ixon.Definition
deriving instance DecidableEq for Ixon.RecursorRule
deriving instance DecidableEq for Ixon.Recursor
deriving instance DecidableEq for Ixon.Axiom
deriving instance DecidableEq for Ixon.Quotient
deriving instance DecidableEq for Ixon.Constructor
deriving instance DecidableEq for Ixon.Inductive
deriving instance DecidableEq for Ixon.InductiveProj
deriving instance DecidableEq for Ixon.ConstructorProj
deriving instance DecidableEq for Ixon.RecursorProj
deriving instance DecidableEq for Ixon.DefinitionProj
deriving instance DecidableEq for Ixon.MutConst
deriving instance DecidableEq for Ixon.ConstantInfo
deriving instance DecidableEq for Ixon.Constant
deriving instance DecidableEq for Ixon.LazyConstant
deriving instance DecidableEq for AnonWorkItem
deriving instance DecidableEq for CheckResult

/-- The E2-certified Theory result, with no concrete Ix declaration trusted
yet.  Catalog, block table, names, and the empty trust predicate are inherited
unchanged from the concrete ingress fixture. -/
def stagedWorld : VerifyWorld :=
  { world with
    venv := theoryAfter
    venvWF := transaction.facts.afterWF }

theorem world_le_staged : world ≤ stagedWorld where
  catalog := rfl
  blocks := rfl
  nameOf := rfl
  trusted := fun h => h
  venv := transaction.facts.envLE

/-- The two work rows emitted by production enumeration, in their actual
address order. -/
def recursorItem : AnonWorkItem :=
  .block recursorBlockAddress recursorId.addr #[recursorId.addr]

def familyItem : AnonWorkItem :=
  .block familyBlockAddress familyId.addr
    #[familyId.addr, falseId.addr, trueId.addr]

def booleanWork : Array AnonWorkItem := #[recursorItem, familyItem]

private theorem buildAnonWorkNative :
    buildAnonWork recursorIxonEnv = .ok booleanWork := by
  native_decide

theorem buildAnonWork_eq :
    buildAnonWork recursorIxonEnv = .ok booleanWork :=
  buildAnonWorkNative

/-! ## Serialized source integrity -/

def familyProjectionConstant : Ixon.Constant :=
  ⟨.iPrj ⟨0, familyBlockAddress⟩, #[], #[], #[]⟩

def falseProjectionConstant : Ixon.Constant :=
  ⟨.cPrj ⟨0, 0, familyBlockAddress⟩, #[], #[], #[]⟩

def trueProjectionConstant : Ixon.Constant :=
  ⟨.cPrj ⟨0, 1, familyBlockAddress⟩, #[], #[], #[]⟩

def recursorProjectionConstant : Ixon.Constant :=
  ⟨.rPrj ⟨0, recursorBlockAddress⟩, #[], #[], #[]⟩

private theorem sourceAddressesNative :
    orderedAnonConstAddrs recursorIxonEnv =
      #[recursorId.addr, recursorBlockAddress, trueId.addr,
        familyBlockAddress, falseId.addr, familyId.addr] := by
  native_decide

theorem sourceAddresses :
    orderedAnonConstAddrs recursorIxonEnv =
      #[recursorId.addr, recursorBlockAddress, trueId.addr,
        familyBlockAddress, falseId.addr, familyId.addr] :=
  sourceAddressesNative

private theorem sourceKeysNative :
    recursorIxonEnv.consts.keys =
      [recursorBlockAddress, falseId.addr, recursorId.addr,
        trueId.addr, familyBlockAddress, familyId.addr] := by
  native_decide

private theorem sourceAddressesNodupNative :
    (#[recursorId.addr, recursorBlockAddress, trueId.addr,
      familyBlockAddress, falseId.addr, familyId.addr] : Array Address).toList.Nodup := by
  native_decide

private theorem recursorTargetsNonemptyNative :
    (anonBlockTargets recursorBlockAddress #[.recr recursorIxon]).size > 0 := by
  native_decide

private theorem familyTargetsNonemptyNative :
    (anonBlockTargets familyBlockAddress #[.indc familyIxon]).size > 0 := by
  native_decide

/-- The unsorted map-key view has the same finite source domain.  This form
is used to classify arbitrary successful lookups, independently of the
ordering implementation used by `buildAnonWork`. -/
theorem sourceKeys :
    recursorIxonEnv.consts.keys =
      [recursorBlockAddress, falseId.addr, recursorId.addr,
        trueId.addr, familyBlockAddress, familyId.addr] :=
  sourceKeysNative

private theorem familyBlockEntry :
    ExactAnonEntry recursorIxonEnv familyBlockAddress
      familyBlockConstant := by
  refine ⟨by native_decide,
    Ixon.LazyConstant.ofConstant familyBlockConstant,
    by native_decide, rfl, by native_decide⟩

private theorem recursorBlockEntry :
    ExactAnonEntry recursorIxonEnv recursorBlockAddress
      recursorBlockConstant := by
  refine ⟨by native_decide,
    Ixon.LazyConstant.ofConstant recursorBlockConstant,
    by native_decide, rfl, by native_decide⟩

private theorem familyProjectionEntry :
    ExactAnonEntry recursorIxonEnv familyId.addr
      familyProjectionConstant := by
  refine ⟨by native_decide,
    Ixon.LazyConstant.ofConstant familyProjectionConstant,
    by native_decide, rfl, by native_decide⟩

private theorem falseProjectionEntry :
    ExactAnonEntry recursorIxonEnv falseId.addr
      falseProjectionConstant := by
  refine ⟨by native_decide,
    Ixon.LazyConstant.ofConstant falseProjectionConstant,
    by native_decide, rfl, by native_decide⟩

private theorem trueProjectionEntry :
    ExactAnonEntry recursorIxonEnv trueId.addr
      trueProjectionConstant := by
  refine ⟨by native_decide,
    Ixon.LazyConstant.ofConstant trueProjectionConstant,
    by native_decide, rfl, by native_decide⟩

private theorem recursorProjectionEntry :
    ExactAnonEntry recursorIxonEnv recursorId.addr
      recursorProjectionConstant := by
  refine ⟨by native_decide,
    Ixon.LazyConstant.ofConstant recursorProjectionConstant,
    by native_decide, rfl, by native_decide⟩

/-- Every materialized source entry in the finite Boolean environment is one
of the two block envelopes or one of their four generated projections. -/
private theorem sourceEntryCases {addr : Address} {constant : Ixon.Constant}
    (hentry : ExactAnonEntry recursorIxonEnv addr constant) :
    (addr = recursorBlockAddress ∧ constant = recursorBlockConstant) ∨
    (addr = trueId.addr ∧ constant = trueProjectionConstant) ∨
    (addr = familyBlockAddress ∧ constant = familyBlockConstant) ∨
    (addr = recursorId.addr ∧ constant = recursorProjectionConstant) ∨
    (addr = falseId.addr ∧ constant = falseProjectionConstant) ∨
    (addr = familyId.addr ∧ constant = familyProjectionConstant) := by
  have haddr := hentry.1
  rw [sourceAddresses] at haddr
  simp at haddr
  rcases haddr with haddr | haddr | haddr | haddr | haddr | haddr
  · subst addr
    exact .inr (.inr (.inr (.inl ⟨rfl,
      ExactAnonEntry.constant_unique hentry recursorProjectionEntry⟩)))
  · subst addr
    exact .inl ⟨rfl,
      ExactAnonEntry.constant_unique hentry recursorBlockEntry⟩
  · subst addr
    exact .inr (.inl ⟨rfl,
      ExactAnonEntry.constant_unique hentry trueProjectionEntry⟩)
  · subst addr
    exact .inr (.inr (.inl ⟨rfl,
      ExactAnonEntry.constant_unique hentry familyBlockEntry⟩))
  · subst addr
    exact .inr (.inr (.inr (.inr (.inl ⟨rfl,
      ExactAnonEntry.constant_unique hentry falseProjectionEntry⟩))))
  · subst addr
    exact .inr (.inr (.inr (.inr (.inr ⟨rfl,
      ExactAnonEntry.constant_unique hentry familyProjectionEntry⟩))))

/-- The concrete serialized Boolean environment satisfies the exact source
integrity contract used by production work enumeration. -/
def sourceWF : AnonWorkEnvWF recursorIxonEnv where
  keysNodup := by
    rw [sourceAddresses]
    exact sourceAddressesNodupNative
  entry := by
    intro addr haddr
    rw [sourceAddresses] at haddr
    simp at haddr
    rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨recursorProjectionConstant, recursorProjectionEntry⟩
    · exact ⟨recursorBlockConstant, recursorBlockEntry⟩
    · exact ⟨trueProjectionConstant, trueProjectionEntry⟩
    · exact ⟨familyBlockConstant, familyBlockEntry⟩
    · exact ⟨falseProjectionConstant, falseProjectionEntry⟩
    · exact ⟨familyProjectionConstant, familyProjectionEntry⟩
  blocksNonempty := by
    intro addr constant members hentry hinfo
    rcases sourceEntryCases hentry with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hinfo
      exact recursorTargetsNonemptyNative
    · simp [trueProjectionConstant] at hinfo
    · cases hinfo
      exact familyTargetsNonemptyNative
    · simp [recursorProjectionConstant] at hinfo
    · simp [falseProjectionConstant] at hinfo
    · simp [familyProjectionConstant] at hinfo
  projectionComplete := by
    intro block constant members target hentry hinfo htarget
    rcases sourceEntryCases hentry with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hinfo
      simp [anonBlockTargets, anonMemberTargets, recursorIxon] at htarget
      subst target
      exact ⟨recursorProjectionConstant, recursorProjectionEntry, rfl⟩
    · simp [trueProjectionConstant] at hinfo
    · cases hinfo
      simp [anonBlockTargets, anonMemberTargets, familyIxon] at htarget
      rcases htarget with htarget | ⟨index, hbound, htarget⟩
      · subst target
        exact ⟨familyProjectionConstant, familyProjectionEntry, rfl⟩
      · have hindex : index = 0 ∨ index = 1 := by omega
        rcases hindex with rfl | rfl
        · subst target
          exact ⟨falseProjectionConstant, falseProjectionEntry, rfl⟩
        · subst target
          exact ⟨trueProjectionConstant, trueProjectionEntry, rfl⟩
    · simp [recursorProjectionConstant] at hinfo
    · simp [falseProjectionConstant] at hinfo
    · simp [familyProjectionConstant] at hinfo
  projectionOwned := by
    intro addr constant owner hentry howner
    rcases sourceEntryCases hentry with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [recursorBlockConstant, projectionOwner?] at howner
    · simp [trueProjectionConstant, projectionOwner?] at howner
      subst owner
      exact ⟨familyBlockConstant, #[.indc familyIxon], familyBlockEntry,
        rfl, by
          simp [anonBlockTargets, anonMemberTargets, familyIxon, trueId]
          right
          exact ⟨1, by omega, rfl⟩⟩
    · simp [familyBlockConstant, projectionOwner?] at howner
    · simp [recursorProjectionConstant, projectionOwner?] at howner
      subst owner
      exact ⟨recursorBlockConstant, #[.recr recursorIxon],
        recursorBlockEntry, rfl, by
          simp [anonBlockTargets, anonMemberTargets, recursorIxon,
            recursorId]⟩
    · simp [falseProjectionConstant, projectionOwner?] at howner
      subst owner
      exact ⟨familyBlockConstant, #[.indc familyIxon], familyBlockEntry,
        rfl, by
          simp [anonBlockTargets, anonMemberTargets, familyIxon, falseId]
          right
          exact ⟨0, by omega, rfl⟩⟩
    · simp [familyProjectionConstant, projectionOwner?] at howner
      subst owner
      exact ⟨familyBlockConstant, #[.indc familyIxon], familyBlockEntry,
        rfl, by
          simp [anonBlockTargets, anonMemberTargets, familyIxon, familyId]⟩

theorem expectedAnonWork_eq :
    expectedAnonWork recursorIxonEnv = booleanWork := by
  exact Except.ok.inj
    (sourceWF.buildAnonWork_eq_expected.symm.trans buildAnonWork_eq)

/-- Every generated projection collapses directly to a non-projection block
envelope, while both envelopes are fixed points.  Successful lookups are
first reduced to the exact finite source-key domain; unknown addresses are
fixed points by definition. -/
def blockOfIdempotent : IxonEnv.BlockOfIdempotent recursorIxonEnv := by
  intro addr
  cases hlookup : recursorIxonEnv.getConst? addr with
  | none =>
      simp [blockOfAddr, hlookup]
  | some constant =>
      have hraw : ∃ lazy,
          recursorIxonEnv.consts.get? addr = some lazy := by
        have hbind :
            (recursorIxonEnv.consts.get? addr).bind
                Ixon.LazyConstant.get? = some constant := by
          simpa only [Ixon.Env.getConst?] using hlookup
        rw [Option.bind_eq_some_iff] at hbind
        obtain ⟨lazy, hstored, _⟩ := hbind
        exact ⟨lazy, hstored⟩
      obtain ⟨lazy, hraw⟩ := hraw
      have hmem : addr ∈ recursorIxonEnv.consts :=
        (Std.HashMap.getElem?_eq_some_iff.mp hraw).choose
      have hkey : addr ∈ recursorIxonEnv.consts.keys :=
        Std.HashMap.mem_keys.mpr hmem
      rw [sourceKeys] at hkey
      simp at hkey
      rcases hkey with rfl | rfl | rfl | rfl | rfl | rfl
      · simp [blockOfAddr, recursorBlockEntry.getConst,
          recursorBlockConstant]
      · simp [blockOfAddr, falseProjectionEntry.getConst,
          familyBlockEntry.getConst, falseProjectionConstant,
          familyBlockConstant]
      · simp [blockOfAddr, recursorProjectionEntry.getConst,
          recursorBlockEntry.getConst, recursorProjectionConstant,
          recursorBlockConstant]
      · simp [blockOfAddr, trueProjectionEntry.getConst,
          familyBlockEntry.getConst, trueProjectionConstant,
          familyBlockConstant]
      · simp [blockOfAddr, familyBlockEntry.getConst,
          familyBlockConstant]
      · simp [blockOfAddr, familyProjectionEntry.getConst,
          familyBlockEntry.getConst, familyProjectionConstant,
          familyBlockConstant]

/-- Exact collapsed dependency catalog used by the Boolean driver theorem. -/
def dependencyGraph : DependencyCatalog :=
  IxonEnv.dependencyCatalog recursorIxonEnv blockOfIdempotent

/-- The closed Boolean fixture has no external declaration assumptions. -/
def noAssumptions : FiniteAddressSet := ⟨[], by simp⟩

/-- Exact physical block identity, rebased to the staged semantic baseline. -/
def stagedExactFamily :
    ExactCheckBlock stagedWorld familyBlockId familyMembers .inductive' :=
  exactFamilyBlock.rebaseWorld world_le_staged

def stagedExactRecursor :
    ExactCheckBlock stagedWorld recursorBlockId recursorMembers .recursor :=
  exactRecursorBlock.rebaseWorld world_le_staged

theorem familyWorkCatalog :
    familyItem.MatchesBlockCatalog stagedWorld.blocks := by
  refine ⟨familyId, #[falseId, trueId], ?_, rfl, ?_⟩
  · exact stagedExactFamily.blockLookup
  · simp

theorem recursorWorkCatalog :
    recursorItem.MatchesBlockCatalog stagedWorld.blocks := by
  refine ⟨recursorId, #[], ?_, rfl, ?_⟩
  · exact stagedExactRecursor.blockLookup
  · simp

/-! ## Closed dependency graph -/

theorem family_no_dependencies {target : Address} :
    ¬dependencyGraph.dependsOn familyBlockAddress target := by
  rintro ⟨constant, hget, hsemantic⟩
  have hconstant : constant = familyBlockConstant :=
    Option.some.inj (hget.symm.trans familyBlockEntry.getConst)
  subst constant
  have hmem := hsemantic.target_mem_refs
  simp [familyBlockConstant] at hmem

theorem recursor_dependency_target {target : Address}
    (hdependency : dependencyGraph.dependsOn recursorBlockAddress target) :
    target = familyId.addr ∨ target = falseId.addr ∨
      target = trueId.addr := by
  obtain ⟨constant, hget, hsemantic⟩ := hdependency
  have hconstant : constant = recursorBlockConstant :=
    Option.some.inj (hget.symm.trans recursorBlockEntry.getConst)
  subst constant
  simpa [recursorBlockConstant] using hsemantic.target_mem_refs

theorem depsClosed :
    DepsClosed dependencyGraph (expectedAnonWork recursorIxonEnv)
      sourceWF.subjects noAssumptions := by
  intro item hitem target hdependency
  rw [expectedAnonWork_eq] at hitem
  have hcases : item = recursorItem ∨ item = familyItem := by
    simpa [booleanWork] using hitem
  rcases hcases with rfl | rfl
  · left
    change dependencyGraph.dependsOn recursorBlockAddress target at hdependency
    rcases recursor_dependency_target hdependency with
      rfl | rfl | rfl <;>
      simp [AnonWorkEnvWF.subjects, sourceAddresses]
  · change dependencyGraph.dependsOn familyBlockAddress target at hdependency
    exact (family_no_dependencies hdependency).elim

theorem assumptionsWF : AssumptionsWF stagedWorld noAssumptions := by
  intro addr haddr
  simp [noAssumptions] at haddr

theorem subjects_disjoint_assumptions :
    sourceWF.subjects.Disjoint noAssumptions := by
  intro addr _ haddr
  simp [noAssumptions] at haddr

/-- A semantic schedule may differ from the physical serial enumeration.
The family is admitted first because every recursor reference collapses into
that family block; the production driver still executes recursor-first. -/
def wellFounded :
    WellFoundedBlocks dependencyGraph (expectedAnonWork recursorIxonEnv)
      sourceWF.subjects where
  schedule := [familyItem, recursorItem]
  permutation := by
    rw [expectedAnonWork_eq]
    exact List.Perm.swap recursorItem familyItem []
  topological := by
    apply TopologicalFrom.cons
    · intro target hdependency _
      change dependencyGraph.dependsOn familyBlockAddress target at hdependency
      exact (family_no_dependencies hdependency).elim
    · apply TopologicalFrom.cons
      · intro target hdependency _
        change dependencyGraph.dependsOn recursorBlockAddress target at hdependency
        right
        refine ⟨familyItem, by simp, ?_⟩
        rcases recursor_dependency_target hdependency with
          rfl | rfl | rfl <;>
          simp [familyItem, AnonWorkItem.Covers,
            AnonWorkItem.provenTargets]
      · exact .nil _
  rank := fun addr => if addr = recursorBlockAddress then 1 else 0
  decreases := by
    intro item target hitem hdependency _ houtside
    rw [expectedAnonWork_eq] at hitem
    have hcases : item = recursorItem ∨ item = familyItem := by
      simpa [booleanWork] using hitem
    rcases hcases with rfl | rfl
    · change dependencyGraph.blockOf target ≠ recursorBlockAddress at houtside
      change (if dependencyGraph.blockOf target = recursorBlockAddress then 1 else 0) <
        (if recursorBlockAddress = recursorBlockAddress then 1 else 0)
      simp [houtside]
    · change dependencyGraph.dependsOn familyBlockAddress target at hdependency
      exact (family_no_dependencies hdependency).elim

/-! ## Fixed certificate resources -/

/-- The family transition's exact per-member provenance, viewed in the staged
driver world where its generated Theory environment is already installed but
no concrete Ix member is trusted yet. -/
def stagedFamilyResources :
    CertificateBackedBlockResources stagedWorld familyBlockAddress
      familyId.addr #[familyId.addr, falseId.addr, trueId.addr] where
  trProj := RawProjRel.none
  members := familyMembers
  kind := .inductive'
  certificateBacked := trivial
  exactBlock := stagedExactFamily
  workCatalog := familyWorkCatalog
  entry := by
    intro id hmember
    change TrustedCatalogEntry RawProjRel.none world.catalog world.nameOf
      theoryAfter id
    exact familyBlockCertificate.entry hmember

/-- The separately certified generated recursor already has its complete type,
registered-rule, and positional iota-pattern provenance in the same staged
Theory environment. -/
def stagedRecursorResources :
    CertificateBackedBlockResources stagedWorld recursorBlockAddress
      recursorId.addr #[recursorId.addr] where
  trProj := RawProjRel.none
  members := recursorMembers
  kind := .recursor
  certificateBacked := trivial
  exactBlock := stagedExactRecursor
  workCatalog := recursorWorkCatalog
  entry := by
    intro id hmember
    have hid : id = recursorId := by
      simpa [recursorMembers_eq] using hmember
    subst id
    change TrustedCatalogEntry RawProjRel.none world.catalog world.nameOf
      theoryAfter recursorId
    exact familyRecursorSemanticEntry

/-- Transport the fixed family certificate to an arbitrary monotone E1 world.
No freshness premise is needed: replay unions all exact members
idempotently. -/
def familyCertificateResources
    (current : VerifyWorld) (hle : stagedWorld ≤ current) :
    CertificateBackedBlockResources current familyBlockAddress familyId.addr
      #[familyId.addr, falseId.addr, trueId.addr] :=
  stagedFamilyResources.rebaseWorld hle

/-- Transport the fixed generated-recursor certificate to an arbitrary
monotone E1 world. -/
def recursorCertificateResources
    (current : VerifyWorld) (hle : stagedWorld ≤ current) :
    CertificateBackedBlockResources current recursorBlockAddress recursorId.addr
      #[recursorId.addr] :=
  stagedRecursorResources.rebaseWorld hle

/-! ## Supported production calls -/

/-- Every still-pending successful call in the concrete two-row work set has
certificate-backed evidence at its *current* semantic world.  The actual
successful `checkConst` equation remains in the provider interface and hence
in `CheckSuccessSound`; it is deliberately not used as a substitute for the
E2 semantic certificate. -/
def supportedFragment :
    CertificateBackedCheckFragment stagedWorld dependencyGraph booleanWork where
  resources := by
    intro item hitem before checker hrun current hle hdeps hnot
    have hcases : item = recursorItem ∨ item = familyItem := by
      simpa [booleanWork] using hitem
    by_cases hrecursor : item = recursorItem
    · subst item
      exact .block (recursorCertificateResources current hle)
    · have hfamily : item = familyItem := hcases.resolve_left hrecursor
      subst item
      exact .block (familyCertificateResources current hle)

def supportedExpectedFragment :
    CertificateBackedCheckFragment stagedWorld dependencyGraph
      (expectedAnonWork recursorIxonEnv) := by
  rw [expectedAnonWork_eq]
  exact supportedFragment

/-! ## Actual production-driver acceptance -/

/-- Hash verification is enabled: the release witness executes the same
address validation path as the public anonymous-environment checker.  A
one-item clearing interval also exercises the production cache-reset branch
between the recursor and family rows. -/
def checkCfg : CheckCfg :=
  { verifyHashes := true, clearEvery := 1 }

def successfulResults : Array CheckResult :=
  #[⟨recursorId.addr, none⟩, ⟨familyId.addr, none⟩,
    ⟨falseId.addr, none⟩, ⟨trueId.addr, none⟩]

private theorem checkEnvAnonNative :
    checkEnvAnon recursorIxonEnv checkCfg = .ok successfulResults := by
  native_decide

/-- Exact result of the real production driver on the certified Boolean
environment. -/
theorem checkEnvAnon_eq :
    checkEnvAnon recursorIxonEnv checkCfg = .ok successfulResults :=
  checkEnvAnonNative

theorem allResultsSucceeded :
    AllCheckResultsSucceeded successfulResults := by
  intro result hresult
  simp [successfulResults] at hresult
  rcases hresult with rfl | rfl | rfl | rfl <;> rfl

/-- Whole-driver E3-S witness for a real environment containing an inductive
family and its generated recursor.  The theorem consumes the actual
`checkEnvAnon` success, the exact finite source domain, the collapsed
dependency schedule, and fixed E2 semantic entries for both coordinated
blocks. Its dependency path contains no oracle-selected world materialization. -/
theorem subjectWF :
    SubjectWF stagedWorld dependencyGraph
      (expectedAnonWork recursorIxonEnv) sourceWF.subjects
      noAssumptions := by
  exact sourceWF.checkEnvAnon_certificateBacked_subjectWF blockOfIdempotent
    depsClosed wellFounded assumptionsWF subjects_disjoint_assumptions
    supportedExpectedFragment checkCfg checkEnvAnon_eq allResultsSucceeded

end BooleanEnumerationFixture

end Ix.Tc
