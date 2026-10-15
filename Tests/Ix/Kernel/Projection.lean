import Ix.Ixon.Authenticated.Theorems
import Ix.Address
import IxC.Fixtures.ByteAdmission

/-! Projection reconstruction (keys under the entry's hash, exact records,
the request bound and conflicts) and the certified entry with projection
omission at BLAKE3, `Ixon.Authenticated.checkBytesProjection`, on fixtures
re-keyed to their BLAKE3 addresses (`Tests.Ix.Kernel.Authentic.rekey`). -/

open Ix.Kernel Tests.Ix.Kernel.IxonFixtures Tests.Ix.Kernel.Codec Tests.Ix.Kernel.Authentic

namespace Tests.Ix.Kernel.Projection

/-- The default role table's section, committed under its BLAKE3 hash
(`Ix.Kernel.Admission.defaultBinding`). -/
def blake3Binding : Ix.Kernel.Admission.Binding :=
  match Ix.Kernel.Admission.defaultBinding with
  | .ok b => b
  | .error _ => ⟨default, .empty⟩

/-- The specification hash, pure BLAKE3. -/
def spec : ByteArray → Address := Address.blake3Pure

def variants (owner : Address) (index ctor : UInt64) : List Ixon.Constant :=
  [⟨.dPrj ⟨index, owner⟩, #[], #[], #[]⟩,
   ⟨.iPrj ⟨index, owner⟩, #[], #[], #[]⟩,
   ⟨.rPrj ⟨index, owner⟩, #[], #[], #[]⟩,
   ⟨.cPrj ⟨index, ctor, owner⟩, #[], #[], #[]⟩]

-- These use the production Rust BLAKE3 backend, independently of the pure
-- implementation the theorems are about. Every variant and compact-tag
-- boundary must produce the same address and a lossless complete record.
#guard wordBoundaries.all fun index =>
  (variants (address 12) index (18446744073709551615 - index)).all fun record =>
    Ixon.Projection.address spec record == Address.blake3 (Ixon.serConstant record) &&
      Ixon.Authenticated.projectionAddress record == Ixon.Projection.address spec record &&
      exactConstant record
#guard ((variants (address 12) 0 0).map (Ixon.Projection.address spec)).eraseDups.length = 4

def entry (record : Ixon.Constant) : Address × Ixon.Constant :=
  (Ixon.Projection.address spec record, record)

def blockInput : List (Address × Ixon.Constant) := [(address 12, variedBlock)]

def generated : List (Address × Ixon.Constant) := [
  entry ⟨.rPrj ⟨2, address 12⟩, #[], #[], #[]⟩,
  entry ⟨.cPrj ⟨1, 0, address 12⟩, #[], #[], #[]⟩,
  entry ⟨.iPrj ⟨1, address 12⟩, #[], #[], #[]⟩,
  entry ⟨.dPrj ⟨0, address 12⟩, #[], #[], #[]⟩]

def reconstructs (input expected : List (Address × Ixon.Constant)) (limit : Nat) : Bool :=
  match Ixon.Authenticated.reconstruct limit input with
  | .ok output => output == expected
  | .error _ => false

def reconstructionError (input : List (Address × Ixon.Constant)) (limit : Nat := 16) :
    Option Ixon.Projection.Error :=
  match Ixon.Authenticated.reconstruct limit input with
  | .ok _ => none
  | .error error => some error

#guard reconstructs [] [] 0
#guard reconstructs [(address 1, identity)] [(address 1, identity)] 0
#guard reconstructs blockInput (generated ++ blockInput) 4
#guard reconstructs (generated ++ blockInput) (generated ++ blockInput) 4
#guard reconstructionError blockInput 3 = some .limit
#guard reconstructionError (generated ++ blockInput) 3 = some .limit
#guard Ixon.Projection.primaries (generated ++ blockInput) == blockInput

def definitionProjection : Ixon.Constant := ⟨.dPrj ⟨0, address 12⟩, #[], #[], #[]⟩
def definitionAddress : Address := Ixon.Projection.address spec definitionProjection

-- A supplied conflicting payload is never overwritten or ignored, even
-- if it differs only by a side table unused by the projection's fields.
#guard reconstructionError (blockInput ++ [(definitionAddress, identity)]) = some (.conflict definitionAddress)
#guard reconstructionError (blockInput ++ [(definitionAddress,
  { definitionProjection with refs := #[address 1] })]) = some (.conflict definitionAddress)
#guard reconstructionError [(⟨⟨Array.replicate 31 0⟩⟩, variedBlock)] =
  some (.ownerWidth ⟨⟨Array.replicate 31 0⟩⟩)
#guard reconstructionError [(⟨⟨#[]⟩⟩, variedBlock)] 0 = some .limit
#guard match Ixon.Projection.reconstructLoop spec 1
    [⟨.definition, .member (address 12) UInt64.size⟩] [] with
  | .error (.projection (.malformed reason)) => reason == "projection index exceeds UInt64"
  | _ => false

/-- A constructor-free family in `Type 1` and its large eliminator, stored
separately (in `Prop` the family would be `False`'s block, byte for byte,
and so the prelude's under its content address, with its recursor and
projection records). -/
def family : Ixon.Constant :=
  ⟨.muts #[.indc ⟨false, 0, 0, 0, .sort 0, #[]⟩], #[], #[], #[.succ (.succ .zero)]⟩

/-- The family, its projection record and its recursor (which names the
projection), under their BLAKE3 keys. -/
def separated : Rekeyed :=
  rekey spec [(address 3, family), (address 6, falseRecursorRecord), (address 4, falseProjection)]

/-- The records without their projection records. -/
def withoutProjections (r : Rekeyed) : List (Address × Ixon.Constant) :=
  r.records.filter fun (_, c) => !Ingress.isProjection c.info

/-- The family and its recursor; the recursor refers to the computed family
projection, which is deliberately absent from input. -/
def separatedInput : List (Address × Ixon.Constant) := withoutProjections separated

def encode (input : List (Address × Ixon.Constant)) : Ix.Kernel.Admission.Records :=
  input.map fun (key, record) => (key, Ixon.serConstant record)

/-- The entry on records already under their keys. -/
def checkAt (input : List (Address × Ixon.Constant)) (limit : Nat := 16)
    (bounds : Ix.Kernel.Admission.Limits := ByteAdmission.limits) :
    Except Ixon.Projection.CheckError (Ix.Kernel.Env .anon) :=
  Ixon.Authenticated.checkBytesProjection blake3Binding limit bounds (encode input) []

/-- The entry on a fixture re-keyed under BLAKE3. -/
def check (input : List (Address × Ixon.Constant)) (limit : Nat := 16)
    (bounds : Ix.Kernel.Admission.Limits := ByteAdmission.limits) :
    Except Ixon.Projection.CheckError (Ix.Kernel.Env .anon) :=
  checkAt (rekey spec input).records limit bounds

def accepts (input : List (Address × Ixon.Constant)) (limit : Nat := 16) : Bool :=
  (check input limit).isOk

#guard separatedInput.length == 2
#guard (checkAt separatedInput).isOk
#guard !(Ixon.Authenticated.checkBytes blake3Binding ByteAdmission.limits (encode separatedInput) []).isOk
#guard accepts [(address 3, falseBlock)]
#guard accepts [(address 1, identity), (address 2, aliasIdentity)] 0
#guard (checkAt separated.records).isOk
#guard !(checkAt separatedInput 0).isOk
-- A family stored without its recursor declines at the reader; the request
-- bound and the batch limits apply first.
#guard match check [(address 3, family)] with
  | .error e@(.checker _) => e.outcome == .declined
  | _ => false
#guard match checkAt separatedInput 0 with
  | .error e@(.reconstruction .limit) => e.outcome == .declined
  | _ => false
#guard match check [] 0 { ByteAdmission.limits with maxRecords := 0 } with
  | .ok _ => true
  | _ => false
#guard match Ixon.Authenticated.checkBytesProjection blake3Binding 0 { ByteAdmission.limits with maxRecords := 0 }
    [(address 1, ⟨#[]⟩)] [] with
  | .error e@(.reconstruction (.admission (.limit .records))) => e.outcome == .declined
  | _ => false

-- The classification of every reconstruction failure (`Error.outcome`):
-- the request bound and a writer failure other than a malformed projection
-- decline; a malformed projection, an owner key of the wrong width and a
-- conflicting record reject; the byte stage as `Admission.ByteError.outcome`.
#guard (Ixon.Projection.Error.limit).outcome == .declined
#guard (Ixon.Projection.Error.ownerWidth (address 1)).outcome == .rejected
#guard (Ixon.Projection.Error.projection (.malformed "")).outcome == .rejected
#guard (Ixon.Projection.Error.projection .exhausted).outcome == .declined
#guard (Ixon.Projection.Error.projection (.unresolved "")).outcome == .declined
#guard (Ixon.Projection.Error.conflict (address 1)).outcome == .rejected
#guard (Ixon.Projection.Error.admission (.duplicate .blobs 1 (address 1))).outcome == .rejected
#guard (Ixon.Projection.Error.admission (.mismatch .records 0 (address 1))).outcome == .rejected
#guard (Ixon.Projection.Error.admission (.limit .records)).outcome == .declined

def wrongConstructorIndex : Ixon.Constant :=
  ⟨.muts #[.indc ⟨false, 0, 0, 0, .sort 0,
    #[⟨false, 0, 1, 0, 0, .recur 0 #[]⟩]⟩], #[], #[], #[.zero]⟩

-- The reconstructed constructor projection does not match the block's
-- metadata: the reader finds it malformed, which rejects.
#guard match check [(address 20, wrongConstructorIndex)] with
  | .error e@(.checker _) => e.outcome == .rejected
  | _ => false

example (V : Type) [Ix.Kernel.SetTheory V] {env : Ix.Kernel.Env .anon}
    (h : Ixon.Authenticated.checkBytesProjection blake3Binding 16 ByteAdmission.limits (encode separatedInput) [] = .ok env) :
    Nonempty (Ix.Kernel.Model V env) :=
  Ixon.Authenticated.checkBytesProjection_has_model V h

example {hash : ByteArray → Address} {binding : Ix.Kernel.Admission.Binding} {maxProjections : Nat}
    {records : Ix.Kernel.Admission.Records} {blobs : Ingress.Blobs} {env : Ix.Kernel.Env .anon}
    (h : Ixon.Projection.checkBytes hash binding maxProjections ByteAdmission.limits records blobs = .ok env) :
    ∃ output, (∀ entry ∈ output, entry.1 = hash (Ixon.serConstant entry.2)) ∧
      Ix.Kernel.Admission.checkConstantsAt hash binding output blobs = .ok env :=
  (Ixon.Projection.checkBytes_authentic h).2

end Tests.Ix.Kernel.Projection
