/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.Ixon

namespace Ix.Certified

open Ix.Theory Ix.Theory.Certified
open Ix.Theory.Model Ix.Theory.Model.SetTheory

universe v

/-- These external constant addresses are part of the selected public profile,
not fields supplied by an annotation or typing witness. -/
structure Profile where
  falseType : Address
  falseElim : Address
  natType : Option Address := none
  deriving DecidableEq

abbrev ConstantBlobs := List (Address × ByteArray)

abbrev DecodedObject (address : Address) (bytes : ByteArray) :=
  { value : Ixon.Constant //
    address.hash.size = 32 ∧ Address.blake3 bytes = address ∧
    Ixon.runGetExact Ixon.getConstant bytes = .ok value ∧ Ixon.serConstant value = bytes }

/-- Check canonical re-encoding after a single parse. Keeping the parser's
result as a separate argument makes the cache reflection equation explicit. -/
def canonicalObject? (address : Address) (bytes : ByteArray)
    (auth : address.hash.size = 32 ∧ Address.blake3 bytes = address)
    (result : Except String Ixon.Constant)
    (parsed : Ixon.runGetExact Ixon.getConstant bytes = result) : Option (DecodedObject address bytes) :=
  match result, parsed with
  | .error _, _ => none
  | .ok source, hp =>
    if hc : Ixon.serConstant source = bytes then some ⟨source, auth.1, auth.2, hp, hc⟩ else none

/-- The accepted byte domain consists of complete canonical Ixon constants.
The returned proof records authentication, exact consumption, and re-encoding
of the same bytes. It grants no typing or semantic acceptance by itself. -/
def decodeObject? (address : Address) (bytes : ByteArray) : Option (DecodedObject address bytes) :=
  if h : address.hash.size = 32 ∧ Address.blake3 bytes = address then
    canonicalObject? address bytes h (Ixon.runGetExact Ixon.getConstant bytes) rfl
  else none

def decodeObjects? (blobs : ConstantBlobs) : Option Objects :=
  blobs.mapM fun (address, bytes) => do
    let source ← decodeObject? address bytes
    return (address, source.val)

/-- Natural blobs use Ix's unsigned little-endian encoding, with authentication
and canonical re-encoding checked before any literal is read. -/
def decodeNatural? (address : Address) (bytes : ByteArray) :
    Option { value : Nat //
      address.hash.size = 32 ∧ Address.blake3 bytes = address ∧
      Nat.fromBytesLE bytes.data = value ∧ ByteArray.mk value.toBytesLE = bytes } :=
  if h : address.hash.size = 32 ∧ Address.blake3 bytes = address then
    let value := Nat.fromBytesLE bytes.data
    if hc : ByteArray.mk value.toBytesLE = bytes then some ⟨value, h.1, h.2, rfl, hc⟩ else none
  else none

def decodeNaturals? (blobs : ConstantBlobs) : Option Naturals :=
  blobs.mapM fun (address, bytes) => do
    let value ← decodeNatural? address bytes
    return (address, value.val)

def readSignature? (profile : Profile) (objects : Objects) :
    Option (PrimitiveSignature Address) := do
  let falseType ← resolveReference? objects profile.falseType
  let falseElim ← resolveReference? objects profile.falseElim
  let natType ← match profile.natType with
    | none => some none
    | some address => (resolveReference? objects address).map some
  if h : falseType ≠ falseElim then
    return ⟨falseType, falseElim, h, natType⟩
  else none

structure PreparedInput where
  signature : PrimitiveSignature Address
  input : ProofInput Address

def prepare? (fuel : Nat) (profile : Profile) (target : Address) (blobs : ConstantBlobs)
    (literalBlobs : ConstantBlobs := []) : Option PreparedInput := do
  if !((blobs ++ literalBlobs).map Prod.fst).Nodup then none else do
  let naturals ← decodeNaturals? literalBlobs
  let objects ← decodeObjects? blobs
  let signature ← readSignature? profile objects
  let input ← readProofInput? fuel objects target naturals
  return ⟨signature, input⟩

/-- The actual serialized-input gate invokes the mathematical validator after
authentication and decoding. The byte/statement preservation and compiled
execution theorems remain separate obligations. -/
def acceptsSerialized (fuel : Nat) (profile : Profile) (target : Address)
    (blobs : ConstantBlobs) (witness : ProofWitness Address)
    (literalBlobs : ConstantBlobs := []) : Bool :=
  match prepare? fuel profile target blobs literalBlobs with
  | none => false
  | some prepared =>
    acceptsCertified.{0,v} fuel prepared.signature prepared.input witness

theorem acceptsSerialized_prepared {fuel : Nat} {profile : Profile} {target : Address}
    {blobs literalBlobs : ConstantBlobs} {witness : ProofWitness Address}
    (h : acceptsSerialized.{v} fuel profile target blobs witness literalBlobs = true) :
    ∃ prepared, prepare? fuel profile target blobs literalBlobs = some prepared ∧
      acceptsCertified.{0,v} fuel prepared.signature prepared.input witness = true := by
  unfold acceptsSerialized at h
  cases hp : prepare? fuel profile target blobs literalBlobs with
  | none => simp [hp] at h
  | some prepared => exact ⟨prepared, rfl, by simpa only [hp] using h⟩

/-- A successful serialized host check constructs the model of its decoded
input. Relating that input to a public cryptographic proposition is C6/C8. -/
theorem accepted_serialized_has_model {fuel : Nat} {profile : Profile} {target : Address}
    {blobs literalBlobs : ConstantBlobs} {witness : ProofWitness Address}
    (h : acceptsSerialized.{v} fuel profile target blobs witness literalBlobs = true)
    (V : Type v) [SetTheory V] (levels : List Nat) (env : Nat → V) :
    ∃ prepared, prepare? fuel profile target blobs literalBlobs = some prepared ∧
      ∃ result : CheckedProof.{0,v} prepared.signature prepared.input,
        checkProofCertified fuel prepared.signature prepared.input witness = some result ∧
        ∃ constants : Assignment Address V,
          prepared.signature.Compatible result.environment.entries constants ∧
          WellDenoted constants levels env result.proof.val ∧
          WellDenoted constants levels env result.proposition.val ∧
          interp constants levels env result.proof.val ∈ˢ
            interp constants levels env result.proposition.val := by
  obtain ⟨prepared, hp, ha⟩ := acceptsSerialized_prepared h
  exact ⟨prepared, hp, accepted_has_model ha V levels env⟩

/-- This checks the decoded target statement against the profile's exact
empty proposition. It performs no theorem or semantic witness search. -/
def isFalseStatement (fuel : Nat) (profile : Profile) (target : Address)
    (blobs : ConstantBlobs) (literalBlobs : ConstantBlobs := []) : Bool :=
  match prepare? fuel profile target blobs literalBlobs with
  | none => false
  | some prepared => decide (prepared.input.proposition = prepared.signature.falseExpr)

theorem no_serialized_proof_of_False {fuel : Nat} {profile : Profile} {target : Address}
    {blobs literalBlobs : ConstantBlobs} {witness : ProofWitness Address}
    (V : Type v) [SetTheory V]
    (hf : isFalseStatement fuel profile target blobs literalBlobs = true)
    (h : acceptsSerialized.{v} fuel profile target blobs witness literalBlobs = true) : False := by
  obtain ⟨prepared, hp, ha⟩ := acceptsSerialized_prepared h
  have he : prepared.input.proposition = prepared.signature.falseExpr := by
    simpa only [isFalseStatement, hp, decide_eq_true_eq] using hf
  exact no_proof_of_False V he ha

end Ix.Certified
