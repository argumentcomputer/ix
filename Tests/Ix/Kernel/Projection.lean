import Ix.Ixon.Projection.Theorems
import Ix.Address
import IxC.Fixtures.ByteAdmission

/-! Projection reconstruction (pure BLAKE3 keys, exact records, the request
bound and conflicts) and the certified entry with projection omission,
`Ixon.Projection.checkBytes`. -/

open Ix.Kernel Tests.Ix.Kernel.IxonFixtures Tests.Ix.Kernel.Codec

namespace Tests.Ix.Kernel.Projection

def variants (owner : Address) (index ctor : UInt64) : List Ixon.Constant :=
  [⟨.dPrj ⟨index, owner⟩, #[], #[], #[]⟩,
   ⟨.iPrj ⟨index, owner⟩, #[], #[], #[]⟩,
   ⟨.rPrj ⟨index, owner⟩, #[], #[], #[]⟩,
   ⟨.cPrj ⟨index, ctor, owner⟩, #[], #[], #[]⟩]

-- These use the production Rust BLAKE3 backend, independently of the pure
-- reconstruction implementation. Every variant and compact-tag boundary
-- must produce the same address and a lossless complete record.
#guard wordBoundaries.all fun index =>
  (variants (address 12) index (18446744073709551615 - index)).all fun record =>
    Ixon.Projection.address record == Address.blake3 (Ixon.serConstant record) &&
      exactConstant record
#guard ((variants (address 12) 0 0).map Ixon.Projection.address).eraseDups.length = 4

def entry (record : Ixon.Constant) : Address × Ixon.Constant :=
  (Ixon.Projection.address record, record)

def blockInput : List (Address × Ixon.Constant) := [(address 12, variedBlock)]

def generated : List (Address × Ixon.Constant) := [
  entry ⟨.rPrj ⟨2, address 12⟩, #[], #[], #[]⟩,
  entry ⟨.cPrj ⟨1, 0, address 12⟩, #[], #[], #[]⟩,
  entry ⟨.iPrj ⟨1, address 12⟩, #[], #[], #[]⟩,
  entry ⟨.dPrj ⟨0, address 12⟩, #[], #[], #[]⟩]

def reconstructs (input expected : List (Address × Ixon.Constant)) (limit : Nat) : Bool :=
  match Ixon.Projection.reconstruct limit input with
  | .ok output => output == expected
  | .error _ => false

def reconstructionError (input : List (Address × Ixon.Constant)) (limit : Nat := 16) :
    Option Ixon.Projection.Error :=
  match Ixon.Projection.reconstruct limit input with
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
def definitionAddress : Address := Ixon.Projection.address definitionProjection

-- A supplied conflicting payload is never overwritten or ignored, even
-- if it differs only by a side table unused by the projection's fields.
#guard reconstructionError (blockInput ++ [(definitionAddress, identity)]) = some (.conflict definitionAddress)
#guard reconstructionError (blockInput ++ [(definitionAddress,
  { definitionProjection with refs := #[address 1] })]) = some (.conflict definitionAddress)
#guard reconstructionError [(⟨⟨Array.replicate 31 0⟩⟩, variedBlock)] =
  some (.ownerWidth ⟨⟨Array.replicate 31 0⟩⟩)
#guard reconstructionError [(⟨⟨#[]⟩⟩, variedBlock)] 0 = some .limit
#guard match Ixon.Projection.reconstructLoop 1
    [⟨.definition, .member (address 12) UInt64.size⟩] [] with
  | .error (.projection (.malformed reason)) => reason == "projection index exceeds UInt64"
  | _ => false

-- The family and recursor are physically separate. The recursor refers to
-- the computed family projection, which is deliberately absent from input.
def separatedInput : List (Address × Ixon.Constant) := [
  (address 3, falseFamily),
  (address 6, { falseRecursorRecord with refs := #[Ixon.Projection.address falseProjection] })]

def encode (input : List (Address × Ixon.Constant)) : Ix.Kernel.Admission.Records :=
  input.map fun (key, record) => (key, Ixon.serConstant record)

def check (input : List (Address × Ixon.Constant)) (limit : Nat := 16)
    (bounds : Ix.Kernel.Admission.Limits := ByteAdmission.limits) :
    Except Ixon.Projection.CheckError Ix.Kernel.Env :=
  Ixon.Projection.checkBytes limit bounds (encode input) []

def accepts (input : List (Address × Ixon.Constant)) (limit : Nat := 16) : Bool :=
  (check input limit).isOk

#guard accepts separatedInput
#guard !(Ix.Kernel.Admission.checkBytes ByteAdmission.limits (encode separatedInput) []).isOk
#guard accepts [(address 3, falseBlock)]
#guard accepts [(address 1, identity), (address 2, aliasIdentity)] 0
#guard accepts (entry falseProjection :: separatedInput)
#guard !(accepts separatedInput 0)
-- A family stored without its recursor declines at the reader; the request
-- bound and the batch limits apply first.
#guard match check [(address 3, falseFamily)] with
  | .error e@(.checker _) => e.outcome == .declined
  | _ => false
#guard match check separatedInput 0 with
  | .error e@(.reconstruction .limit) => e.outcome == .declined
  | _ => false
#guard match check [] 0 { ByteAdmission.limits with maxRecords := 0 } with
  | .ok _ => true
  | _ => false
#guard match Ixon.Projection.checkBytes 0 { ByteAdmission.limits with maxRecords := 0 }
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
#guard (Ixon.Projection.Error.admission (.limit .records)).outcome == .declined

def wrongConstructorIndex : Ixon.Constant :=
  ⟨.muts #[.indc ⟨false, 0, 0, 0, .sort 0,
    #[⟨false, 0, 1, 0, 0, .recur 0 #[]⟩]⟩], #[], #[], #[.zero]⟩

-- The reconstructed constructor projection does not match the block's
-- metadata: the reader finds it malformed, which rejects.
#guard match check [(address 20, wrongConstructorIndex)] with
  | .error e@(.checker _) => e.outcome == .rejected
  | _ => false

example (V : Type) [Ix.Kernel.SetTheory V] {env : Ix.Kernel.Env}
    (h : Ixon.Projection.checkBytes 16 ByteAdmission.limits (encode separatedInput) [] = .ok env) :
    Nonempty (Ix.Kernel.Model V env) :=
  Ixon.Projection.checkBytes_has_model V h

end Tests.Ix.Kernel.Projection
