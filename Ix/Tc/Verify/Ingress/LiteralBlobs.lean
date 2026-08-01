import Ix.Tc.Verify.Ingress.AnonStructural
import Ix.Tc.Verify.Ingress.Representation

/-!
# Serialized literal/blob ingress

This T0 fixture makes the blob side of the serialized representation
contract non-vacuous.  A Nat literal and a String literal are stored in one
Ixon environment, serialized, decoded with the pure reference decoder, and
ingressed through the production anonymous lazy-fault path.  Separate
malformed environments demonstrate that the decoder rejects a constant or a
blob stored under an address that does not commit to its bytes.
-/

namespace Ix.Tc
namespace SerializedLiteralBlobs

local instance addressDecidableEq : DecidableEq Address :=
  AnonStructural.addressDecidableEq

local instance idDecidableEq : DecidableEq (KId .anon) :=
  AnonStructural.idDecidableEq

local instance constDecidableEq : DecidableEq (KConst .anon) :=
  AnonStructural.constDecidableEq

/- Executable equality is confined to this finite Ixon fixture and compares
the actual inductive fields. -/
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

/-! ## Source environment -/

def natBytes : ByteArray := ⟨(42 : Nat).toBytesLE⟩
def stringBytes : ByteArray := "hi".toUTF8

def natBlobAddress : Address := Address.blake3 natBytes
def stringBlobAddress : Address := Address.blake3 stringBytes

def natConstant : Ixon.Constant :=
  ⟨.defn ⟨.defn, .safe, 0, .sort 0, .nat 0⟩,
    #[], #[natBlobAddress], #[.zero]⟩

def stringConstant : Ixon.Constant :=
  ⟨.defn ⟨.defn, .safe, 0, .sort 0, .str 0⟩,
    #[], #[stringBlobAddress], #[.zero]⟩

def natAddress : Address := Address.blake3 (Ixon.serConstant natConstant)
def stringAddress : Address :=
  Address.blake3 (Ixon.serConstant stringConstant)

def sourceEnv : Ixon.Env :=
  let base : Ixon.Env := {}
  let blobs := base.blobs.insert natBlobAddress natBytes
  let blobs := blobs.insert stringBlobAddress stringBytes
  let withBlobs : Ixon.Env := { base with blobs := blobs }
  (withBlobs.storeConst natAddress natConstant).storeConst
    stringAddress stringConstant

/-! ## Pure byte round-trip -/

def encoded : Except String ByteArray := Ixon.serEnv sourceEnv

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

def env : Ixon.Env := IxonEnv.eraseAnonMetadata decoded

/-! ## Exact decoded entries -/

private theorem natLookupNative :
    env.consts.get? natAddress =
      some (Ixon.LazyConstant.ofConstant natConstant) := by
  native_decide

private theorem stringLookupNative :
    env.consts.get? stringAddress =
      some (Ixon.LazyConstant.ofConstant stringConstant) := by
  native_decide

private theorem natBlobLookupNative :
    env.getBlob? natBlobAddress = some natBytes := by
  native_decide

private theorem stringBlobLookupNative :
    env.getBlob? stringBlobAddress = some stringBytes := by
  native_decide

private theorem natHashNative :
    Address.blake3 (Ixon.LazyConstant.ofConstant natConstant).rawBytes =
      natAddress := by
  native_decide

private theorem stringHashNative :
    Address.blake3 (Ixon.LazyConstant.ofConstant stringConstant).rawBytes =
      stringAddress := by
  native_decide

private theorem natBlobHashNative :
    Address.blake3 natBytes = natBlobAddress := by
  native_decide

private theorem stringBlobHashNative :
    Address.blake3 stringBytes = stringBlobAddress := by
  native_decide

private theorem natEntry : ExactAnonEntry env natAddress natConstant := by
  refine ⟨by native_decide, Ixon.LazyConstant.ofConstant natConstant,
    natLookupNative, rfl, by native_decide⟩

private theorem stringEntry :
    ExactAnonEntry env stringAddress stringConstant := by
  refine ⟨by native_decide, Ixon.LazyConstant.ofConstant stringConstant,
    stringLookupNative, rfl, by native_decide⟩

def isLiteralAddress (addr : Address) : Bool :=
  addr == natAddress || addr == stringAddress

private theorem isLiteralAddress_iff (addr : Address) :
    isLiteralAddress addr = true ↔
      addr = natAddress ∨ addr = stringAddress := by
  simp [isLiteralAddress, beq_iff_eq]

private theorem sourceAddressesClassifiedNative :
    (orderedAnonConstAddrs env).toList.all isLiteralAddress = true := by
  native_decide

private theorem sourceAddressCases {addr : Address}
    (haddr : addr ∈ orderedAnonConstAddrs env) :
    addr = natAddress ∨ addr = stringAddress := by
  have hall := sourceAddressesClassifiedNative
  rw [List.all_eq_true] at hall
  exact (isLiteralAddress_iff addr).mp (hall addr (by simpa using haddr))

private theorem sourceKeysClassifiedNative :
    env.consts.keys.all isLiteralAddress = true := by
  native_decide

private theorem sourceAddressesNodupNative :
    (orderedAnonConstAddrs env).toList.Nodup := by
  native_decide

private theorem sourceKeyCases {addr : Address}
    (haddr : addr ∈ env.consts.keys) :
    addr = natAddress ∨ addr = stringAddress := by
  have hall := sourceKeysClassifiedNative
  rw [List.all_eq_true] at hall
  exact (isLiteralAddress_iff addr).mp (hall addr haddr)

private theorem sourceEntryCases {addr : Address}
    {constant : Ixon.Constant} (hentry : ExactAnonEntry env addr constant) :
    (addr = natAddress ∧ constant = natConstant) ∨
      (addr = stringAddress ∧ constant = stringConstant) := by
  rcases sourceAddressCases hentry.1 with rfl | rfl
  · exact .inl ⟨rfl, ExactAnonEntry.constant_unique hentry natEntry⟩
  · exact .inr ⟨rfl, ExactAnonEntry.constant_unique hentry stringEntry⟩

def sourceWF : AnonWorkEnvWF env where
  keysNodup := sourceAddressesNodupNative
  entry := by
    intro addr haddr
    rcases sourceAddressCases haddr with rfl | rfl
    · exact ⟨natConstant, natEntry⟩
    · exact ⟨stringConstant, stringEntry⟩
  blocksNonempty := by
    intro addr constant members hentry hinfo
    rcases sourceEntryCases hentry with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [natConstant] at hinfo
    · simp [stringConstant] at hinfo
  projectionComplete := by
    intro block constant members target hentry hinfo _
    rcases sourceEntryCases hentry with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [natConstant] at hinfo
    · simp [stringConstant] at hinfo
  projectionOwned := by
    intro addr constant owner hentry howner
    rcases sourceEntryCases hentry with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [natConstant, projectionOwner?] at howner
    · simp [stringConstant, projectionOwner?] at howner

private theorem constAddresses : IxonEnv.ConstAddressIntegrity env := by
  intro addr lazy hlookup
  have hmem : addr ∈ env.consts :=
    (Std.HashMap.getElem?_eq_some_iff.mp hlookup).choose
  have hkey : addr ∈ env.consts.keys := Std.HashMap.mem_keys.mpr hmem
  rcases sourceKeyCases hkey with rfl | rfl
  · have hlazy := Option.some.inj (hlookup.symm.trans natLookupNative)
    subst lazy
    exact natHashNative
  · have hlazy := Option.some.inj (hlookup.symm.trans stringLookupNative)
    subst lazy
    exact stringHashNative

private theorem constMaterialization :
    IxonEnv.ConstMaterializationIntegrity env := by
  intro addr lazy hlookup
  have hmem : addr ∈ env.consts :=
    (Std.HashMap.getElem?_eq_some_iff.mp hlookup).choose
  have hkey : addr ∈ env.consts.keys := Std.HashMap.mem_keys.mpr hmem
  rcases sourceKeyCases hkey with rfl | rfl
  · have hlazy := Option.some.inj (hlookup.symm.trans natLookupNative)
    subst lazy
    exact ⟨natConstant, rfl⟩
  · have hlazy := Option.some.inj (hlookup.symm.trans stringLookupNative)
    subst lazy
    exact ⟨stringConstant, rfl⟩

def isLiteralBlobAddress (addr : Address) : Bool :=
  addr == natBlobAddress || addr == stringBlobAddress

private theorem isLiteralBlobAddress_iff (addr : Address) :
    isLiteralBlobAddress addr = true ↔
      addr = natBlobAddress ∨ addr = stringBlobAddress := by
  simp [isLiteralBlobAddress, beq_iff_eq]

private theorem blobKeysClassifiedNative :
    env.blobs.keys.all isLiteralBlobAddress = true := by
  native_decide

private theorem blobAddresses : IxonEnv.BlobAddressIntegrity env := by
  intro addr value hlookup
  have hmem : addr ∈ env.blobs :=
    (Std.HashMap.getElem?_eq_some_iff.mp hlookup).choose
  have hkey : addr ∈ env.blobs.keys := Std.HashMap.mem_keys.mpr hmem
  have hall := blobKeysClassifiedNative
  rw [List.all_eq_true] at hall
  rcases (isLiteralBlobAddress_iff addr).mp (hall addr hkey) with rfl | rfl
  · have hvalue := Option.some.inj
      (hlookup.symm.trans natBlobLookupNative)
    subst value
    exact natBlobHashNative
  · have hvalue := Option.some.inj
      (hlookup.symm.trans stringBlobLookupNative)
    subst value
    exact stringBlobHashNative

def blockOfIdempotent : IxonEnv.BlockOfIdempotent env := by
  intro addr
  cases hlookup : env.getConst? addr with
  | none => simp [blockOfAddr, hlookup]
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
      rcases sourceKeyCases hkey with rfl | rfl
      · simp [blockOfAddr, natEntry.getConst, natConstant]
      · simp [blockOfAddr, stringEntry.getConst, stringConstant]

def representationWF : IxonEnv.RepresentationWF env where
  constAddresses := constAddresses
  constMaterialization := constMaterialization
  blobAddresses := blobAddresses
  source := sourceWF
  blockOfIdempotent := blockOfIdempotent

def input : IxonEnv.SerializedAnonInput bytes env where
  source := sourceEnv
  encode := encode_eq
  decoded := decoded
  decode := decode_eq
  erased := rfl
  representation := representationWF

/-! ## Exact literal ingress -/

def natId : KId .anon := ⟨natAddress, ()⟩
def stringId : KId .anon := ⟨stringAddress, ()⟩

def sortZero : KExpr .anon := KExpr.mkSort KUniv.mkZero

def natExpected : KConst .anon :=
  .defn () () .defn .safe (.regular 0) 0 sortZero
    (KExpr.mkNat 42 natBlobAddress) () natId

def stringExpected : KConst .anon :=
  .defn () () .defn .safe (.regular 0) 0 sortZero
    (KExpr.mkStr "hi" stringBlobAddress) () stringId

def natOutcome :=
  ingressAnonAddrShallow env natAddress true ({} : AnonEnv)

def natAfter : AnonEnv :=
  match natOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def natSucceeded : Bool :=
  match natOutcome with
  | .ok found _ => found
  | .error _ _ => false

private theorem natSucceededNative : natSucceeded = true := by
  native_decide

theorem natRun : natOutcome = .ok true natAfter := by
  have success := natSucceededNative
  unfold natSucceeded at success
  unfold natAfter
  generalize houtcome : natOutcome = result at success ⊢
  cases result <;> simp_all

private theorem natLoadedNative :
    natAfter.get? natId = some natExpected := by
  native_decide

def stringOutcome :=
  ingressAnonAddrShallow env stringAddress true ({} : AnonEnv)

def stringAfter : AnonEnv :=
  match stringOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def stringSucceeded : Bool :=
  match stringOutcome with
  | .ok found _ => found
  | .error _ _ => false

private theorem stringSucceededNative : stringSucceeded = true := by
  native_decide

theorem stringRun : stringOutcome = .ok true stringAfter := by
  have success := stringSucceededNative
  unfold stringSucceeded at success
  unfold stringAfter
  generalize houtcome : stringOutcome = result at success ⊢
  cases result <;> simp_all

private theorem stringLoadedNative :
    stringAfter.get? stringId = some stringExpected := by
  native_decide

structure LiteralBlobRoundTrip where
  input : IxonEnv.SerializedAnonInput bytes env
  natBlob : env.getBlob? natBlobAddress = some natBytes
  natBlobAddressed : Address.blake3 natBytes = natBlobAddress
  stringBlob : env.getBlob? stringBlobAddress = some stringBytes
  stringBlobAddressed : Address.blake3 stringBytes = stringBlobAddress
  natAfter : AnonEnv
  natRun : natOutcome = .ok true natAfter
  natLoaded : natAfter.get? natId = some natExpected
  stringAfter : AnonEnv
  stringRun : stringOutcome = .ok true stringAfter
  stringLoaded : stringAfter.get? stringId = some stringExpected

def literalCertificate : LiteralBlobRoundTrip where
  input := input
  natBlob := natBlobLookupNative
  natBlobAddressed := natBlobHashNative
  stringBlob := stringBlobLookupNative
  stringBlobAddressed := stringBlobHashNative
  natAfter := natAfter
  natRun := natRun
  natLoaded := natLoadedNative
  stringAfter := stringAfter
  stringRun := stringRun
  stringLoaded := stringLoadedNative

/-- Non-vacuous T0 literal/blob round-trip through serialized bytes and the
actual anonymous ingress implementation. -/
theorem literalRoundTrip : Nonempty LiteralBlobRoundTrip :=
  ⟨literalCertificate⟩

/-! ## Adversarial address-integrity fixtures -/

def wrongConstantAddress : Address :=
  Address.blake3 "not-the-constant-body".toUTF8

def malformedConstantEnv : Ixon.Env :=
  let consts := sourceEnv.consts.insert wrongConstantAddress
    (Ixon.LazyConstant.ofConstant natConstant)
  { sourceEnv with consts := consts }

private theorem malformedConstantRejectedNative :
    IxonEnv.serializationRejected malformedConstantEnv = true := by
  native_decide

/-- The reference decoder rejects constant bytes stored under a mismatching
content address. -/
theorem malformedConstantRejected :
    IxonEnv.SerializedDecodeRejected malformedConstantEnv :=
  IxonEnv.serializedDecodeRejected_of_true
    malformedConstantRejectedNative

def wrongBlobAddress : Address :=
  Address.blake3 "not-the-blob-body".toUTF8

def malformedBlobEnv : Ixon.Env :=
  let blobs := sourceEnv.blobs.insert wrongBlobAddress natBytes
  { sourceEnv with blobs := blobs }

private theorem malformedBlobRejectedNative :
    IxonEnv.serializationRejected malformedBlobEnv = true := by
  native_decide

/-- The reference decoder rejects blob bytes stored under a mismatching
content address. -/
theorem malformedBlobRejected :
    IxonEnv.SerializedDecodeRejected malformedBlobEnv :=
  IxonEnv.serializedDecodeRejected_of_true malformedBlobRejectedNative

end SerializedLiteralBlobs
end Ix.Tc
