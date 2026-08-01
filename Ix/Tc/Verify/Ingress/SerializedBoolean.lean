import Ix.Tc.Verify.Driver.BooleanAcceptance
import Ix.Tc.Verify.Ingress.AnonStructural
import Ix.Tc.Verify.Ingress.Representation

/-!
# Serialized Boolean acceptance

This is the first complete T0 vertical slice.  It serializes the certified
Boolean Ixon environment, decodes the resulting bytes with the pure reference
decoder, erases anonymous-irrelevant metadata, and reconnects the decoded
source to the existing E3-S semantic world.
-/

namespace Ix.Tc
namespace BooleanSerialized

open BooleanEnumerationFixture

local instance addressDecidableEq : DecidableEq Address :=
  AnonStructural.addressDecidableEq

local instance idDecidableEq : DecidableEq (KId .anon) :=
  AnonStructural.idDecidableEq

local instance constDecidableEq : DecidableEq (KConst .anon) :=
  AnonStructural.constDecidableEq

/-! ## Pure byte round-trip -/

def encoded : Except String ByteArray := Ixon.serEnv recursorIxonEnv

def bytes : ByteArray :=
  match encoded with
  | .ok bytes => bytes
  | .error _ => ByteArray.empty

def encodeSucceeded : Bool :=
  match encoded with
  | .ok _ => true
  | .error _ => false

private theorem encodeSucceededNative : encodeSucceeded = true := by
  native_decide

theorem encode_eq : encoded = .ok bytes := by
  have success := encodeSucceededNative
  unfold encodeSucceeded at success
  unfold bytes
  generalize hencoded : encoded = result at success ⊢
  cases result <;> simp_all

def decoded : Ixon.Env :=
  match Ixon.deEnv bytes with
  | .ok env => env
  | .error _ => {}

def decodeSucceeded : Bool :=
  match Ixon.deEnv bytes with
  | .ok _ => true
  | .error _ => false

private theorem decodeSucceededNative : decodeSucceeded = true := by
  native_decide

theorem decode_eq : Ixon.deEnv bytes = .ok decoded := by
  have success := decodeSucceededNative
  unfold decodeSucceeded at success
  unfold decoded
  generalize hdecoded : Ixon.deEnv bytes = result at success ⊢
  cases result <;> simp_all

/-- The exact environment consumed by anonymous checking. -/
def env : Ixon.Env := IxonEnv.eraseAnonMetadata decoded

/-! ## Exact decoded source entries -/

private theorem sourceAddressesNative :
    orderedAnonConstAddrs env =
      #[recursorBlockAddress, trueId.addr, familyBlockAddress,
        recursorId.addr, falseId.addr, familyId.addr] := by
  native_decide

theorem sourceAddresses :
    orderedAnonConstAddrs env =
      #[recursorBlockAddress, trueId.addr, familyBlockAddress,
        recursorId.addr, falseId.addr, familyId.addr] :=
  sourceAddressesNative

private theorem sourceKeysNative :
    env.consts.keys =
      [recursorBlockAddress, falseId.addr, recursorId.addr,
        trueId.addr, familyBlockAddress, familyId.addr] := by
  native_decide

theorem sourceKeys :
    env.consts.keys =
      [recursorBlockAddress, falseId.addr, recursorId.addr,
        trueId.addr, familyBlockAddress, familyId.addr] :=
  sourceKeysNative

private theorem sourceAddressesNodupNative :
    (#[recursorBlockAddress, trueId.addr, familyBlockAddress,
      recursorId.addr, falseId.addr, familyId.addr] : Array Address).toList.Nodup := by
  native_decide

private theorem recursorBlockLookupNative :
    env.consts.get? recursorBlockAddress = some
      (Ixon.LazyConstant.ofConstant recursorBlockConstant) := by
  native_decide

private theorem familyBlockLookupNative :
    env.consts.get? familyBlockAddress = some
      (Ixon.LazyConstant.ofConstant familyBlockConstant) := by
  native_decide

private theorem recursorProjectionLookupNative :
    env.consts.get? recursorId.addr = some
      (Ixon.LazyConstant.ofConstant recursorProjectionConstant) := by
  native_decide

private theorem familyProjectionLookupNative :
    env.consts.get? familyId.addr = some
      (Ixon.LazyConstant.ofConstant familyProjectionConstant) := by
  native_decide

private theorem falseProjectionLookupNative :
    env.consts.get? falseId.addr = some
      (Ixon.LazyConstant.ofConstant falseProjectionConstant) := by
  native_decide

private theorem trueProjectionLookupNative :
    env.consts.get? trueId.addr = some
      (Ixon.LazyConstant.ofConstant trueProjectionConstant) := by
  native_decide

private theorem recursorBlockHashNative :
    Address.blake3
      (Ixon.LazyConstant.ofConstant recursorBlockConstant).rawBytes =
      recursorBlockAddress := by
  native_decide

private theorem familyBlockHashNative :
    Address.blake3
      (Ixon.LazyConstant.ofConstant familyBlockConstant).rawBytes =
      familyBlockAddress := by
  native_decide

private theorem recursorProjectionHashNative :
    Address.blake3
      (Ixon.LazyConstant.ofConstant recursorProjectionConstant).rawBytes =
      recursorId.addr := by
  native_decide

private theorem familyProjectionHashNative :
    Address.blake3
      (Ixon.LazyConstant.ofConstant familyProjectionConstant).rawBytes =
      familyId.addr := by
  native_decide

private theorem falseProjectionHashNative :
    Address.blake3
      (Ixon.LazyConstant.ofConstant falseProjectionConstant).rawBytes =
      falseId.addr := by
  native_decide

private theorem trueProjectionHashNative :
    Address.blake3
      (Ixon.LazyConstant.ofConstant trueProjectionConstant).rawBytes =
      trueId.addr := by
  native_decide

private theorem familyBlockEntry :
    ExactAnonEntry env familyBlockAddress familyBlockConstant := by
  refine ⟨by native_decide,
    Ixon.LazyConstant.ofConstant familyBlockConstant,
    familyBlockLookupNative, rfl, by native_decide⟩

private theorem recursorBlockEntry :
    ExactAnonEntry env recursorBlockAddress recursorBlockConstant := by
  refine ⟨by native_decide,
    Ixon.LazyConstant.ofConstant recursorBlockConstant,
    recursorBlockLookupNative, rfl, by native_decide⟩

private theorem familyProjectionEntry :
    ExactAnonEntry env familyId.addr familyProjectionConstant := by
  refine ⟨by native_decide,
    Ixon.LazyConstant.ofConstant familyProjectionConstant,
    familyProjectionLookupNative, rfl, by native_decide⟩

private theorem falseProjectionEntry :
    ExactAnonEntry env falseId.addr falseProjectionConstant := by
  refine ⟨by native_decide,
    Ixon.LazyConstant.ofConstant falseProjectionConstant,
    falseProjectionLookupNative, rfl, by native_decide⟩

private theorem trueProjectionEntry :
    ExactAnonEntry env trueId.addr trueProjectionConstant := by
  refine ⟨by native_decide,
    Ixon.LazyConstant.ofConstant trueProjectionConstant,
    trueProjectionLookupNative, rfl, by native_decide⟩

private theorem recursorProjectionEntry :
    ExactAnonEntry env recursorId.addr recursorProjectionConstant := by
  refine ⟨by native_decide,
    Ixon.LazyConstant.ofConstant recursorProjectionConstant,
    recursorProjectionLookupNative, rfl, by native_decide⟩

private theorem sourceEntryCases {addr : Address} {constant : Ixon.Constant}
    (hentry : ExactAnonEntry env addr constant) :
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
    exact .inl ⟨rfl,
      ExactAnonEntry.constant_unique hentry recursorBlockEntry⟩
  · subst addr
    exact .inr (.inl ⟨rfl,
      ExactAnonEntry.constant_unique hentry trueProjectionEntry⟩)
  · subst addr
    exact .inr (.inr (.inl ⟨rfl,
      ExactAnonEntry.constant_unique hentry familyBlockEntry⟩))
  · subst addr
    exact .inr (.inr (.inr (.inl ⟨rfl,
      ExactAnonEntry.constant_unique hentry recursorProjectionEntry⟩)))
  · subst addr
    exact .inr (.inr (.inr (.inr (.inl ⟨rfl,
      ExactAnonEntry.constant_unique hentry falseProjectionEntry⟩))))
  · subst addr
    exact .inr (.inr (.inr (.inr (.inr ⟨rfl,
      ExactAnonEntry.constant_unique hentry familyProjectionEntry⟩))))

private theorem recursorTargetsNonemptyNative :
    (anonBlockTargets recursorBlockAddress #[.recr recursorIxon]).size > 0 := by
  native_decide

private theorem familyTargetsNonemptyNative :
    (anonBlockTargets familyBlockAddress #[.indc familyIxon]).size > 0 := by
  native_decide

/-- The decoded environment satisfies the same exact work-enumeration
contract as the pre-serialization source. -/
def sourceWF : AnonWorkEnvWF env where
  keysNodup := by
    rw [sourceAddresses]
    exact sourceAddressesNodupNative
  entry := by
    intro addr haddr
    rw [sourceAddresses] at haddr
    simp at haddr
    rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨recursorBlockConstant, recursorBlockEntry⟩
    · exact ⟨trueProjectionConstant, trueProjectionEntry⟩
    · exact ⟨familyBlockConstant, familyBlockEntry⟩
    · exact ⟨recursorProjectionConstant, recursorProjectionEntry⟩
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

private theorem constAddresses : IxonEnv.ConstAddressIntegrity env := by
  intro addr lazy hlookup
  have hmem : addr ∈ env.consts :=
    (Std.HashMap.getElem?_eq_some_iff.mp hlookup).choose
  have hkey : addr ∈ env.consts.keys := Std.HashMap.mem_keys.mpr hmem
  rw [sourceKeys] at hkey
  simp at hkey
  rcases hkey with rfl | rfl | rfl | rfl | rfl | rfl
  · have hlazy := Option.some.inj
      (hlookup.symm.trans recursorBlockLookupNative)
    subst lazy
    exact recursorBlockHashNative
  · have hlazy := Option.some.inj
      (hlookup.symm.trans falseProjectionLookupNative)
    subst lazy
    exact falseProjectionHashNative
  · have hlazy := Option.some.inj
      (hlookup.symm.trans recursorProjectionLookupNative)
    subst lazy
    exact recursorProjectionHashNative
  · have hlazy := Option.some.inj
      (hlookup.symm.trans trueProjectionLookupNative)
    subst lazy
    exact trueProjectionHashNative
  · have hlazy := Option.some.inj
      (hlookup.symm.trans familyBlockLookupNative)
    subst lazy
    exact familyBlockHashNative
  · have hlazy := Option.some.inj
      (hlookup.symm.trans familyProjectionLookupNative)
    subst lazy
    exact familyProjectionHashNative

private theorem constMaterialization :
    IxonEnv.ConstMaterializationIntegrity env := by
  intro addr lazy hlookup
  have hmem : addr ∈ env.consts :=
    (Std.HashMap.getElem?_eq_some_iff.mp hlookup).choose
  have hkey : addr ∈ env.consts.keys := Std.HashMap.mem_keys.mpr hmem
  rw [sourceKeys] at hkey
  simp at hkey
  rcases hkey with rfl | rfl | rfl | rfl | rfl | rfl
  · have hlazy := Option.some.inj
      (hlookup.symm.trans recursorBlockLookupNative)
    subst lazy
    exact ⟨recursorBlockConstant, rfl⟩
  · have hlazy := Option.some.inj
      (hlookup.symm.trans falseProjectionLookupNative)
    subst lazy
    exact ⟨falseProjectionConstant, rfl⟩
  · have hlazy := Option.some.inj
      (hlookup.symm.trans recursorProjectionLookupNative)
    subst lazy
    exact ⟨recursorProjectionConstant, rfl⟩
  · have hlazy := Option.some.inj
      (hlookup.symm.trans trueProjectionLookupNative)
    subst lazy
    exact ⟨trueProjectionConstant, rfl⟩
  · have hlazy := Option.some.inj
      (hlookup.symm.trans familyBlockLookupNative)
    subst lazy
    exact ⟨familyBlockConstant, rfl⟩
  · have hlazy := Option.some.inj
      (hlookup.symm.trans familyProjectionLookupNative)
    subst lazy
    exact ⟨familyProjectionConstant, rfl⟩

private theorem blobKeysNative : env.blobs.keys = [] := by
  native_decide

private theorem blobAddresses : IxonEnv.BlobAddressIntegrity env := by
  intro addr value hlookup
  have hmem : addr ∈ env.blobs :=
    (Std.HashMap.getElem?_eq_some_iff.mp hlookup).choose
  have hkey : addr ∈ env.blobs.keys := Std.HashMap.mem_keys.mpr hmem
  rw [blobKeysNative] at hkey
  simp at hkey

/-! ## Collapsed block identity -/

def blockOfIdempotent : IxonEnv.BlockOfIdempotent env := by
  intro addr
  cases hlookup : env.getConst? addr with
  | none =>
      simp [blockOfAddr, hlookup]
  | some constant =>
      have hraw : ∃ lazy, env.consts.get? addr = some lazy := by
        have hbind :
            (env.consts.get? addr).bind Ixon.LazyConstant.get? =
              some constant := by
          simpa only [Ixon.Env.getConst?] using hlookup
        rw [Option.bind_eq_some_iff] at hbind
        obtain ⟨lazy, hstored, _⟩ := hbind
        exact ⟨lazy, hstored⟩
      obtain ⟨lazy, hraw⟩ := hraw
      have hmem : addr ∈ env.consts :=
        (Std.HashMap.getElem?_eq_some_iff.mp hraw).choose
      have hkey : addr ∈ env.consts.keys :=
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

/-- Hash, materialization, blob, projection, and collapsed-block integrity of
the decoded anonymous environment. -/
def representationWF : IxonEnv.RepresentationWF env where
  constAddresses := constAddresses
  constMaterialization := constMaterialization
  blobAddresses := blobAddresses
  source := sourceWF
  blockOfIdempotent := blockOfIdempotent

def input : IxonEnv.SerializedAnonInput bytes env where
  source := recursorIxonEnv
  encode := encode_eq
  decoded := decoded
  decode := decode_eq
  erased := rfl
  representation := representationWF

/-! ## Eager catalog correspondence -/

private theorem buildAnonWorkNative :
    buildAnonWork env = .ok booleanWork := by
  native_decide

theorem expectedAnonWork_eq :
    expectedAnonWork env = booleanWork := by
  exact Except.ok.inj
    (sourceWF.buildAnonWork_eq_expected.symm.trans buildAnonWorkNative)

def eagerOutcome := (ingressAll env true).run ({} : AnonEnv)

def eagerSucceeded : Bool :=
  match eagerOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem eagerSucceededNative : eagerSucceeded = true := by
  native_decide

def eagerWork : Array AnonWorkItem :=
  match eagerOutcome with
  | .ok work _ => work
  | .error _ _ => #[]

def eagerAfter : AnonEnv :=
  match eagerOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem eagerWorkNative : eagerWork = booleanWork := by
  native_decide

theorem eagerRun : eagerOutcome = .ok booleanWork eagerAfter := by
  have success := eagerSucceededNative
  have workEq := eagerWorkNative
  unfold eagerSucceeded at success
  unfold eagerWork at workEq
  unfold eagerAfter
  generalize houtcome : eagerOutcome = result at success workEq ⊢
  cases result <;> simp_all

def isCataloguedId (id : KId .anon) : Bool :=
  id == familyId || id == falseId || id == trueId || id == recursorId

private theorem isCataloguedId_iff (id : KId .anon) :
    isCataloguedId id = true ↔
      id = familyId ∨ id = falseId ∨ id = trueId ∨ id = recursorId := by
  simp [isCataloguedId, beq_iff_eq, or_assoc]

private theorem eagerKeysClassifiedNative :
    eagerAfter.consts.keys.all isCataloguedId = true := by
  native_decide

private theorem eagerKeyCases {id : KId .anon}
    (hmem : id ∈ eagerAfter.consts.keys) :
    id = familyId ∨ id = falseId ∨ id = trueId ∨ id = recursorId := by
  have hall := eagerKeysClassifiedNative
  rw [List.all_eq_true] at hall
  exact (isCataloguedId_iff id).mp (hall id hmem)

private theorem eagerFamilyNative :
    eagerAfter.get? familyId = some familyConcrete := by
  native_decide

private theorem eagerFalseNative :
    eagerAfter.get? falseId = some falseConcrete := by
  native_decide

private theorem eagerTrueNative :
    eagerAfter.get? trueId = some trueConcrete := by
  native_decide

private theorem eagerRecursorNative :
    eagerAfter.get? recursorId = some recursorConcrete := by
  native_decide

theorem eagerConstants :
    LoadedAgrees stagedWorld.catalog eagerAfter := by
  intro id constant hget
  have hmap : eagerAfter.consts[id]? = some constant := by
    simpa only [KEnv.get?] using hget
  have hmem : id ∈ eagerAfter.consts :=
    (Std.HashMap.getElem?_eq_some_iff.mp hmap).choose
  have hkey : id ∈ eagerAfter.consts.keys := Std.HashMap.mem_keys.mpr hmem
  rcases eagerKeyCases hkey with rfl | rfl | rfl | rfl
  · have hc := Option.some.inj (hget.symm.trans eagerFamilyNative)
    subst constant
    simpa [stagedWorld] using catalog_family
  · have hc := Option.some.inj (hget.symm.trans eagerFalseNative)
    subst constant
    simpa [stagedWorld] using catalog_false
  · have hc := Option.some.inj (hget.symm.trans eagerTrueNative)
    subst constant
    simpa [stagedWorld] using catalog_true
  · have hc := Option.some.inj (hget.symm.trans eagerRecursorNative)
    subst constant
    simpa [stagedWorld] using catalog_recursor

def isCataloguedBlock (id : KId .anon) : Bool :=
  id == familyBlockId || id == recursorBlockId

private theorem isCataloguedBlock_iff (id : KId .anon) :
    isCataloguedBlock id = true ↔
      id = familyBlockId ∨ id = recursorBlockId := by
  simp [isCataloguedBlock, beq_iff_eq]

private theorem eagerBlockKeysClassifiedNative :
    eagerAfter.blocks.keys.all isCataloguedBlock = true := by
  native_decide

private theorem eagerBlockKeyCases {id : KId .anon}
    (hmem : id ∈ eagerAfter.blocks.keys) :
    id = familyBlockId ∨ id = recursorBlockId := by
  have hall := eagerBlockKeysClassifiedNative
  rw [List.all_eq_true] at hall
  exact (isCataloguedBlock_iff id).mp
    (hall id hmem)

private theorem eagerFamilyBlockNative :
    eagerAfter.getBlock? familyBlockId = some familyMembers := by
  native_decide

private theorem eagerRecursorBlockNative :
    eagerAfter.getBlock? recursorBlockId = some recursorMembers := by
  native_decide

theorem eagerBlocks : LoadedBlocksAgrees stagedWorld.blocks eagerAfter := by
  intro id members hget
  have hmem : id ∈ eagerAfter.blocks :=
    (Std.HashMap.getElem?_eq_some_iff.mp hget).choose
  have hkey : id ∈ eagerAfter.blocks.keys := Std.HashMap.mem_keys.mpr hmem
  rcases eagerBlockKeyCases hkey with rfl | rfl
  · have hm := Option.some.inj (hget.symm.trans eagerFamilyBlockNative)
    subst members
    simpa [stagedWorld] using world_family_block
  · have hm := Option.some.inj (hget.symm.trans eagerRecursorBlockNative)
    subst members
    simpa [stagedWorld] using world_recursor_block

def eagerAgreement :
    EagerCatalogAgreement env stagedWorld (expectedAnonWork env) where
  after := eagerAfter
  run := by
    rw [expectedAnonWork_eq]
    exact eagerRun
  constants := eagerConstants
  blocks := eagerBlocks

/-! ## Cold lazy-ingress catalog correspondence -/

def lazyFamilyOutcome :=
  ingressAnonAddrShallow env familyId.addr true ({} : AnonEnv)

def lazyFamilyAfter : AnonEnv :=
  match lazyFamilyOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def lazyFamilySucceeded : Bool :=
  match lazyFamilyOutcome with
  | .ok found _ => found
  | .error _ _ => false

private theorem lazyFamilySucceededNative :
    lazyFamilySucceeded = true := by
  native_decide

theorem lazyFamilyRun :
    lazyFamilyOutcome = .ok true lazyFamilyAfter := by
  have success := lazyFamilySucceededNative
  unfold lazyFamilySucceeded at success
  unfold lazyFamilyAfter
  generalize houtcome : lazyFamilyOutcome = result at success ⊢
  cases result <;> simp_all

def isFamilyId (id : KId .anon) : Bool :=
  id == familyId || id == falseId || id == trueId

private theorem isFamilyId_iff (id : KId .anon) :
    isFamilyId id = true ↔
      id = familyId ∨ id = falseId ∨ id = trueId := by
  simp [isFamilyId, beq_iff_eq, or_assoc]

private theorem lazyFamilyKeysClassifiedNative :
    lazyFamilyAfter.consts.keys.all isFamilyId = true := by
  native_decide

private theorem lazyFamilyKeyCases {id : KId .anon}
    (hmem : id ∈ lazyFamilyAfter.consts.keys) :
    id = familyId ∨ id = falseId ∨ id = trueId := by
  have hall := lazyFamilyKeysClassifiedNative
  rw [List.all_eq_true] at hall
  exact (isFamilyId_iff id).mp (hall id hmem)

private theorem lazyFamilyLoadedNative :
    lazyFamilyAfter.get? familyId = some familyConcrete := by
  native_decide

private theorem lazyFalseLoadedNative :
    lazyFamilyAfter.get? falseId = some falseConcrete := by
  native_decide

private theorem lazyTrueLoadedNative :
    lazyFamilyAfter.get? trueId = some trueConcrete := by
  native_decide

theorem lazyFamilyConstants :
    LoadedAgrees stagedWorld.catalog lazyFamilyAfter := by
  intro id constant hget
  have hmap : lazyFamilyAfter.consts[id]? = some constant := by
    simpa only [KEnv.get?] using hget
  have hmem : id ∈ lazyFamilyAfter.consts :=
    (Std.HashMap.getElem?_eq_some_iff.mp hmap).choose
  have hkey : id ∈ lazyFamilyAfter.consts.keys :=
    Std.HashMap.mem_keys.mpr hmem
  rcases lazyFamilyKeyCases hkey with rfl | rfl | rfl
  · have hc := Option.some.inj (hget.symm.trans lazyFamilyLoadedNative)
    subst constant
    simpa [stagedWorld] using catalog_family
  · have hc := Option.some.inj (hget.symm.trans lazyFalseLoadedNative)
    subst constant
    simpa [stagedWorld] using catalog_false
  · have hc := Option.some.inj (hget.symm.trans lazyTrueLoadedNative)
    subst constant
    simpa [stagedWorld] using catalog_true

private theorem lazyFamilyBlockKeysNative :
    lazyFamilyAfter.blocks.keys.all (fun id => id == familyBlockId) = true := by
  native_decide

private theorem lazyFamilyBlockNative :
    lazyFamilyAfter.getBlock? familyBlockId = some familyMembers := by
  native_decide

theorem lazyFamilyBlocks :
    LoadedBlocksAgrees stagedWorld.blocks lazyFamilyAfter := by
  intro id members hget
  have hmem : id ∈ lazyFamilyAfter.blocks :=
    (Std.HashMap.getElem?_eq_some_iff.mp hget).choose
  have hkey : id ∈ lazyFamilyAfter.blocks.keys :=
    Std.HashMap.mem_keys.mpr hmem
  have hall := lazyFamilyBlockKeysNative
  rw [List.all_eq_true] at hall
  have hid : id = familyBlockId := eq_of_beq (hall id hkey)
  subst id
  have hm := Option.some.inj (hget.symm.trans lazyFamilyBlockNative)
  subst members
  simpa [stagedWorld] using world_family_block

def lazyFamilyStep :
    LazyCatalogStep env stagedWorld ({} : AnonEnv) familyId.addr where
  after := lazyFamilyAfter
  found := true
  run := lazyFamilyRun
  constants := lazyFamilyConstants
  blocks := lazyFamilyBlocks

def lazyRecursorOutcome :=
  ingressAnonAddrShallow env recursorId.addr true lazyFamilyAfter

def lazyRecursorAfter : AnonEnv :=
  match lazyRecursorOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def lazyRecursorSucceeded : Bool :=
  match lazyRecursorOutcome with
  | .ok found _ => found
  | .error _ _ => false

private theorem lazyRecursorSucceededNative :
    lazyRecursorSucceeded = true := by
  native_decide

theorem lazyRecursorRun :
    lazyRecursorOutcome = .ok true lazyRecursorAfter := by
  have success := lazyRecursorSucceededNative
  unfold lazyRecursorSucceeded at success
  unfold lazyRecursorAfter
  generalize houtcome : lazyRecursorOutcome = result at success ⊢
  cases result <;> simp_all

private theorem lazyRecursorKeysClassifiedNative :
    lazyRecursorAfter.consts.keys.all isCataloguedId = true := by
  native_decide

private theorem lazyRecursorKeyCases {id : KId .anon}
    (hmem : id ∈ lazyRecursorAfter.consts.keys) :
    id = familyId ∨ id = falseId ∨ id = trueId ∨ id = recursorId := by
  have hall := lazyRecursorKeysClassifiedNative
  rw [List.all_eq_true] at hall
  exact (isCataloguedId_iff id).mp (hall id hmem)

private theorem lazyFinalFamilyNative :
    lazyRecursorAfter.get? familyId = some familyConcrete := by
  native_decide

private theorem lazyFinalFalseNative :
    lazyRecursorAfter.get? falseId = some falseConcrete := by
  native_decide

private theorem lazyFinalTrueNative :
    lazyRecursorAfter.get? trueId = some trueConcrete := by
  native_decide

private theorem lazyFinalRecursorNative :
    lazyRecursorAfter.get? recursorId = some recursorConcrete := by
  native_decide

theorem lazyFinalConstants :
    LoadedAgrees stagedWorld.catalog lazyRecursorAfter := by
  intro id constant hget
  have hmap : lazyRecursorAfter.consts[id]? = some constant := by
    simpa only [KEnv.get?] using hget
  have hmem : id ∈ lazyRecursorAfter.consts :=
    (Std.HashMap.getElem?_eq_some_iff.mp hmap).choose
  have hkey : id ∈ lazyRecursorAfter.consts.keys :=
    Std.HashMap.mem_keys.mpr hmem
  rcases lazyRecursorKeyCases hkey with rfl | rfl | rfl | rfl
  · have hc := Option.some.inj (hget.symm.trans lazyFinalFamilyNative)
    subst constant
    simpa [stagedWorld] using catalog_family
  · have hc := Option.some.inj (hget.symm.trans lazyFinalFalseNative)
    subst constant
    simpa [stagedWorld] using catalog_false
  · have hc := Option.some.inj (hget.symm.trans lazyFinalTrueNative)
    subst constant
    simpa [stagedWorld] using catalog_true
  · have hc := Option.some.inj (hget.symm.trans lazyFinalRecursorNative)
    subst constant
    simpa [stagedWorld] using catalog_recursor

private theorem lazyFinalBlockKeysClassifiedNative :
    lazyRecursorAfter.blocks.keys.all isCataloguedBlock = true := by
  native_decide

private theorem lazyFinalFamilyBlockNative :
    lazyRecursorAfter.getBlock? familyBlockId = some familyMembers := by
  native_decide

private theorem lazyFinalRecursorBlockNative :
    lazyRecursorAfter.getBlock? recursorBlockId = some recursorMembers := by
  native_decide

theorem lazyFinalBlocks :
    LoadedBlocksAgrees stagedWorld.blocks lazyRecursorAfter := by
  intro id members hget
  have hmem : id ∈ lazyRecursorAfter.blocks :=
    (Std.HashMap.getElem?_eq_some_iff.mp hget).choose
  have hkey : id ∈ lazyRecursorAfter.blocks.keys :=
    Std.HashMap.mem_keys.mpr hmem
  have hall := lazyFinalBlockKeysClassifiedNative
  rw [List.all_eq_true] at hall
  rcases (isCataloguedBlock_iff id).mp (hall id hkey) with rfl | rfl
  · have hm := Option.some.inj
      (hget.symm.trans lazyFinalFamilyBlockNative)
    subst members
    simpa [stagedWorld] using world_family_block
  · have hm := Option.some.inj
      (hget.symm.trans lazyFinalRecursorBlockNative)
    subst members
    simpa [stagedWorld] using world_recursor_block

def lazyRecursorStep :
    LazyCatalogStep env stagedWorld lazyFamilyAfter recursorId.addr where
  after := lazyRecursorAfter
  found := true
  run := lazyRecursorRun
  constants := lazyFinalConstants
  blocks := lazyFinalBlocks

def lazyRequests : List Address := [familyId.addr, recursorId.addr]

def lazyTrace :
    LazyCatalogTrace env stagedWorld ({} : AnonEnv) lazyRequests
      lazyRecursorAfter := by
  exact .cons lazyFamilyStep (.cons lazyRecursorStep (.nil _))

/-! ## Serialized dependency binding -/

private theorem originalRecursorBlockLookupNative :
    recursorIxonEnv.getConst? recursorBlockAddress =
      some recursorBlockConstant := by
  native_decide

private theorem originalRecursorProjectionLookupNative :
    recursorIxonEnv.getConst? recursorId.addr =
      some recursorProjectionConstant := by
  native_decide

private theorem originalFalseProjectionLookupNative :
    recursorIxonEnv.getConst? falseId.addr =
      some falseProjectionConstant := by
  native_decide

private theorem originalTrueProjectionLookupNative :
    recursorIxonEnv.getConst? trueId.addr =
      some trueProjectionConstant := by
  native_decide

private theorem originalFamilyBlockLookupNative :
    recursorIxonEnv.getConst? familyBlockAddress =
      some familyBlockConstant := by
  native_decide

private theorem originalFamilyProjectionLookupNative :
    recursorIxonEnv.getConst? familyId.addr =
      some familyProjectionConstant := by
  native_decide

/-- Successful lookups in the in-memory source used by E3-S have the exact
same materialized value after serialization and pure decoding.  The finite
key classification avoids any appeal to injectivity of content hashes. -/
private theorem decodedGetConst_of_original {addr : Address}
    {constant : Ixon.Constant}
    (hget : recursorIxonEnv.getConst? addr = some constant) :
    env.getConst? addr = some constant := by
  have hraw : ∃ lazy, recursorIxonEnv.consts.get? addr = some lazy := by
    have hbind :
        (recursorIxonEnv.consts.get? addr).bind
            Ixon.LazyConstant.get? = some constant := by
      simpa only [Ixon.Env.getConst?] using hget
    rw [Option.bind_eq_some_iff] at hbind
    obtain ⟨lazy, hstored, _⟩ := hbind
    exact ⟨lazy, hstored⟩
  obtain ⟨lazy, hraw⟩ := hraw
  have hmem : addr ∈ recursorIxonEnv.consts :=
    (Std.HashMap.getElem?_eq_some_iff.mp hraw).choose
  have hkey : addr ∈ recursorIxonEnv.consts.keys :=
    Std.HashMap.mem_keys.mpr hmem
  rw [BooleanEnumerationFixture.sourceKeys] at hkey
  simp at hkey
  rcases hkey with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc := Option.some.inj
      (hget.symm.trans originalRecursorBlockLookupNative)
    subst constant
    exact recursorBlockEntry.getConst
  · have hc := Option.some.inj
      (hget.symm.trans originalRecursorProjectionLookupNative)
    subst constant
    exact recursorProjectionEntry.getConst
  · have hc := Option.some.inj
      (hget.symm.trans originalFalseProjectionLookupNative)
    subst constant
    exact falseProjectionEntry.getConst
  · have hc := Option.some.inj
      (hget.symm.trans originalTrueProjectionLookupNative)
    subst constant
    exact trueProjectionEntry.getConst
  · have hc := Option.some.inj
      (hget.symm.trans originalFamilyBlockLookupNative)
    subst constant
    exact familyBlockEntry.getConst
  · have hc := Option.some.inj
      (hget.symm.trans originalFamilyProjectionLookupNative)
    subst constant
    exact familyProjectionEntry.getConst

/-- Every dependency used by the E3-S Boolean proof is a reference stored in
the corresponding constant recovered from the decoded byte array. -/
theorem dependencyBound :
    SerializedDependencyBound env dependencyGraph := by
  intro source target hdependency
  obtain ⟨constant, hget, hsemantic⟩ := hdependency
  exact ⟨constant, decodedGetConst_of_original hget,
    hsemantic.target_mem_refs⟩

/-! ## Semantic and production-driver transport -/

private theorem finiteAddressSet_eq_of_entries_eq
    {left right : FiniteAddressSet}
    (h : left.entries = right.entries) : left = right := by
  cases left
  cases right
  cases h
  rfl

theorem subjects_eq :
    sourceWF.subjects = BooleanEnumerationFixture.sourceWF.subjects := by
  apply finiteAddressSet_eq_of_entries_eq
  change (orderedAnonConstAddrs env).toList =
    (orderedAnonConstAddrs recursorIxonEnv).toList
  rw [sourceAddresses, BooleanEnumerationFixture.sourceAddresses]

theorem semanticSubjectWF :
    SubjectWF stagedWorld dependencyGraph (expectedAnonWork env)
      sourceWF.subjects noAssumptions := by
  rw [expectedAnonWork_eq, subjects_eq,
    ← BooleanEnumerationFixture.expectedAnonWork_eq]
  exact BooleanEnumerationFixture.subjectWF

private theorem checkEnvAnonNative :
    checkEnvAnon env checkCfg = .ok successfulResults := by
  native_decide

theorem checkEnvAnon_eq :
    checkEnvAnon env checkCfg = .ok successfulResults :=
  checkEnvAnonNative

/-! ## Public T0 certificate -/

def certificate :
    SerializedSubjectCertificate bytes stagedWorld dependencyGraph
      noAssumptions lazyRequests where
  env := env
  input := input
  eager := eagerAgreement
  lazyAfter := lazyRecursorAfter
  lazy := lazyTrace
  lazyConstants := lazyFinalConstants
  lazyBlocks := lazyFinalBlocks
  dependencyBound := dependencyBound
  cfg := checkCfg
  results := successfulResults
  driver := checkEnvAnon_eq
  resultsSucceeded := allResultsSucceeded
  semantic := semanticSubjectWF

/-- T0-S: the serialized Boolean environment passes pure decoding, integrity
checks, exact eager and cold-lazy ingress, production checking, dependency
binding, and the existing semantic acceptance theorem. -/
theorem subjectWF :
    SerializedSubjectWF bytes stagedWorld dependencyGraph noAssumptions
      lazyRequests :=
  ⟨certificate⟩

end BooleanSerialized
end Ix.Tc
