/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.ProjectionProofs
import Ix.Address
import Tests.Ix.Kernel.ByteAdmission

open Ix.Kernel Tests.Ix.Kernel.Ingress Tests.Ix.Kernel.Egress Tests.Ix.Kernel.Codec

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
    Ix.Ixon.Projection.address record == Address.blake3 (Ixon.serConstant record) &&
      exactConstant record
#guard ((variants (address 12) 0 0).map Ix.Ixon.Projection.address).eraseDups.length = 4

def entry (record : Ixon.Constant) : Address × Ixon.Constant :=
  (Ix.Ixon.Projection.address record, record)

def blockInput : Ingress.Constants := [(address 12, variedBlock)]

def generated : Ingress.Constants := [
  entry ⟨.rPrj ⟨2, address 12⟩, #[], #[], #[]⟩,
  entry ⟨.cPrj ⟨1, 0, address 12⟩, #[], #[], #[]⟩,
  entry ⟨.iPrj ⟨1, address 12⟩, #[], #[], #[]⟩,
  entry ⟨.dPrj ⟨0, address 12⟩, #[], #[], #[]⟩]

def reconstructs (input expected : Ingress.Constants) (limit : Nat) : Bool :=
  match Ix.Ixon.Projection.reconstruct limit input with
  | .ok output => output == expected
  | .error _ => false

def reconstructionError (input : Ingress.Constants) (limit : Nat := 16) :
    Option Ix.Ixon.Projection.Error :=
  match Ix.Ixon.Projection.reconstruct limit input with
  | .ok _ => none
  | .error error => some error

#guard reconstructs [] [] 0
#guard reconstructs [(address 1, identity)] [(address 1, identity)] 0
#guard reconstructs blockInput (generated ++ blockInput) 4
#guard reconstructs (generated ++ blockInput) (generated ++ blockInput) 4
#guard reconstructionError blockInput 3 = some .limit
#guard reconstructionError (generated ++ blockInput) 3 = some .limit
#guard Ix.Ixon.Projection.primaries (generated ++ blockInput) == blockInput

def definitionProjection : Ixon.Constant := ⟨.dPrj ⟨0, address 12⟩, #[], #[], #[]⟩
def definitionAddress : Address := Ix.Ixon.Projection.address definitionProjection

-- A supplied conflicting payload is never overwritten or ignored, even
-- if it differs only by a side table unused by the projection's fields.
#guard reconstructionError (blockInput ++ [(definitionAddress, identity)]) = some (.conflict definitionAddress)
#guard reconstructionError (blockInput ++ [(definitionAddress,
  { definitionProjection with refs := #[address 1] })]) = some (.conflict definitionAddress)
#guard reconstructionError [(⟨⟨Array.replicate 31 0⟩⟩, variedBlock)] =
  some (.ownerWidth ⟨⟨Array.replicate 31 0⟩⟩)
#guard reconstructionError [(⟨⟨#[]⟩⟩, variedBlock)] 0 = some .limit
#guard match Ix.Ixon.Projection.reconstructLoop 1
    [⟨.definition, .member (address 12) UInt64.size⟩] [] with
  | .error (.projection (.malformed reason)) => reason == "projection index exceeds UInt64"
  | _ => false

-- The family and recursor are physically separate. The recursor refers to
-- the computed family projection, which is deliberately absent from input.
def separatedInput : Ingress.Constants := [
  (address 3, falseFamily),
  (address 6, { falseRecursorRecord with refs := #[Ix.Ixon.Projection.address falseProjection] })]

def encode (input : Ingress.Constants) : Ix.Ixon.Admission.Records :=
  input.map fun (key, record) => (key, Ixon.serConstant record)

def accepts (input : Ingress.Constants) (limit : Nat := 16) : Bool :=
  (Ix.Ixon.Projection.checkBytesIntrinsic.{1} limit ByteAdmission.limits {} (encode input) []).isOk

#guard accepts separatedInput
#guard !(Ix.Ixon.Admission.checkBytesIntrinsic.{1} ByteAdmission.limits {} (encode separatedInput) []).isOk
#guard accepts [(address 3, falseBlock)]
#guard accepts [(address 3, falseFamily)]
#guard accepts [(address 1, identity), (address 2, aliasIdentity)] 0
#guard accepts (entry falseProjection :: separatedInput)
#guard !(accepts separatedInput 0)
#guard match Ix.Ixon.Projection.checkBytesIntrinsic.{1} 16 ByteAdmission.limits ⟨0⟩
    (encode separatedInput) [] with
  | .error (.admission (.kernel (.declined _))) => true
  | _ => false
#guard match Ix.Ixon.Projection.checkBytesIntrinsic.{1} 0
    { ByteAdmission.limits with maxRecords := 0 } {} [(address 1, ⟨#[]⟩)] [] with
  | .error (.admission (.limit .records)) => true
  | _ => false

def wrongConstructorIndex : Ixon.Constant :=
  ⟨.muts #[.indc ⟨false, 0, 0, 0, .sort 0,
    #[⟨false, 0, 1, 0, 0, .recur 0 #[]⟩]⟩], #[], #[], #[.zero]⟩

#guard match Ix.Ixon.Projection.checkBytesIntrinsic.{1} 16 ByteAdmission.limits {}
    (encode [(address 20, wrongConstructorIndex)]) [] with
  | .error (.admission (.kernel (.rejected _))) => true
  | _ => false

example (V : Type 1) [Model.SetTheory V] {env : Env Address}
    (h : Ix.Ixon.Projection.checkBytesIntrinsic.{1} 16 ByteAdmission.limits {}
      (encode separatedInput) [] = .ok env) : Nonempty (Model V env) :=
  Ix.Ixon.Projection.checkBytesIntrinsic_has_model V h

end Tests.Ix.Kernel.Projection
