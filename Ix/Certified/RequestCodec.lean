/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.Command
import Ix.Certified.ClaimCommand

/-! Ixon serialization for the typed certified requests. Request frames carry
their own version and distinguish source requests from claim requests. Public
envelopes keep their existing Ixon representation and content addresses.
The public decoders consume the complete input and require canonical bytes.
-/

namespace Ix.Certified

namespace RequestCodec

open Ixon

def magic : ByteArray := "IX-CERTIFIED-REQUEST".toUTF8 ++ ⟨#[0]⟩

/-- Bound transport decoding before allocating collections or parsing claims. -/
def maxBytes : Nat := 1 <<< 20

def putHeader (kind : UInt8) : PutM Unit := do
  putBytes magic
  putTag0 ⟨1⟩
  putU8 kind

def getHeader (kind : UInt8) : GetM Unit := do
  if (← getBytes magic.size) != magic then throw "invalid certified request magic"
  if (← getTag0).size != 1 then throw "unsupported certified request version"
  if (← getU8) != kind then throw "incorrect certified request kind"

def putList (putValue : α → PutM Unit) (values : List α) : PutM Unit := do
  putTag0 ⟨values.length.toUInt64⟩
  values.forM putValue

/-- Every item used by this codec consumes at least one byte. Check the count
against the remaining input before allocating the collection. -/
def getList (getValue : GetM α) : GetM (List α) := do
  let count := (← getTag0).size.toNat
  let state ← get
  if count > state.bytes.size - state.idx then throw "certified request list exceeds remaining input"
  let mut values := []
  for _ in [:count] do values := (← getValue) :: values
  return values.reverse

def putOption (putValue : α → PutM Unit) : Option α → PutM Unit
  | none => putU8 0
  | some value => do putU8 1; putValue value

def getOption (getValue : GetM α) : GetM (Option α) := do
  match ← getU8 with
  | 0 => return none
  | 1 => return some (← getValue)
  | _ => throw "invalid certified request option tag"

def putBlob (bytes : ByteArray) : PutM Unit := do
  putTag0 ⟨bytes.size.toUInt64⟩
  putBytes bytes

def getBlob : GetM ByteArray := do
  getBytes (← getTag0).size.toNat

def putProfile (profile : Profile) : PutM Unit := do
  Serialize.put profile.falseType
  Serialize.put profile.falseElim
  putOption Serialize.put profile.natType

def getProfile : GetM Profile :=
  return ⟨← Serialize.get, ← Serialize.get, ← getOption Serialize.get⟩

def putSelection (selection : InputSelection) : PutM Unit := do
  putList Serialize.put selection.objects
  putList Serialize.put selection.naturals

def getSelection : GetM InputSelection :=
  return ⟨← getList Serialize.get, ← getList Serialize.get⟩

def putModelProof (hint : ModelProofHint) : PutM Unit := do
  Serialize.put hint.equality
  Serialize.put hint.reflexivity
  Serialize.put hint.eliminator
  Serialize.put hint.proof

def getModelProof : GetM ModelProofHint :=
  return ⟨← Serialize.get, ← Serialize.get, ← Serialize.get, ← Serialize.get⟩

def putModelRules (hint : ModelRuleHints) : PutM Unit := do
  Serialize.put hint.owner
  putList (putOption putModelProof) hint.proofs

def getModelRules : GetM ModelRuleHints :=
  return ⟨← Serialize.get, ← getList (getOption getModelProof)⟩

def putModel (hint : ModelHint) : PutM Unit := do
  Serialize.put hint.source
  putList Serialize.put hint.recursors
  putList Serialize.put hint.targets
  putList putModelRules hint.proofs

def getModel : GetM ModelHint :=
  return ⟨← Serialize.get, ← getList Serialize.get, ← getList Serialize.get,
    ← getList getModelRules⟩

def putSourceRequest (request : Command.Request) : PutM Unit := do
  putHeader 0
  putProfile request.profile
  Serialize.put request.target
  putList Serialize.put request.subjects
  putSelection request.selection
  putList putModel request.models

def getSourceRequest : GetM Command.Request := do
  getHeader 0
  return ⟨← getProfile, ← Serialize.get, ← getList Serialize.get,
    ← getSelection, ← getList getModel⟩

def putLeaf (hint : LeafHint) : PutM Unit := do
  Ix.Claim.put hint.claim
  putOption putBlob hint.subjects
  putOption putBlob hint.frontierTree

def getLeaf : GetM LeafHint :=
  return ⟨← Ix.Claim.get, ← getOption getBlob, ← getOption getBlob⟩

def putLogical (hint : LogicalHint) : PutM Unit := do
  putSelection hint.selection
  putList putLeaf hint.leaves
  putOption putBlob hint.subjects
  putOption putBlob hint.members
  putOption putBlob hint.frontierTree
  putOption putBlob hint.axiomTree
  putList putModel hint.models

def getLogical : GetM LogicalHint :=
  return ⟨← getSelection, ← getList getLeaf, ← getOption getBlob,
    ← getOption getBlob, ← getOption getBlob, ← getOption getBlob,
    ← getList getModel⟩

def putHint : ClaimCommand.Hint → PutM Unit
  | .logical hint => do putU8 0; putLogical hint
  | .contains tree => do putU8 1; putBlob tree
  | .reveal witness => do
    putU8 2
    Serialize.put witness.opening.secret
    Serialize.put witness.opening.payload

def getHint : GetM ClaimCommand.Hint := do
  match ← getU8 with
  | 0 => return .logical (← getLogical)
  | 1 => return .contains (← getBlob)
  | 2 => return .reveal ⟨⟨← Serialize.get, ← Serialize.get⟩⟩
  | _ => throw "invalid certified claim hint tag"

def putClaimRequest (request : ClaimCommand.Request) : PutM Unit := do
  putHeader 1
  Serialize.put request.address
  putHint request.hint

def getClaimRequest : GetM ClaimCommand.Request := do
  getHeader 1
  return ⟨← Serialize.get, ← getHint⟩

def decode (getValue : GetM α) (putValue : α → PutM Unit) (bytes : ByteArray) : Except String α := do
  if bytes.size > maxBytes then throw "certified input exceeds the 1 MiB transport limit"
  let value ← runGetExact getValue bytes
  if runPut (putValue value) != bytes then throw "noncanonical certified input bytes"
  return value

end RequestCodec

instance : Ixon.Serialize Command.Request where
  put := RequestCodec.putSourceRequest
  get := RequestCodec.getSourceRequest

instance : Ixon.Serialize ClaimCommand.Request where
  put := RequestCodec.putClaimRequest
  get := RequestCodec.getClaimRequest

instance : Ixon.Serialize Envelope where
  put := putEnvelope
  get := getEnvelope

def Command.Request.toIxon (request : Command.Request) : ByteArray := Ixon.ser request

def Command.Request.ofIxon (bytes : ByteArray) : Except String Command.Request :=
  RequestCodec.decode RequestCodec.getSourceRequest RequestCodec.putSourceRequest bytes

def ClaimCommand.Request.toIxon (request : ClaimCommand.Request) : ByteArray := Ixon.ser request

def ClaimCommand.Request.ofIxon (bytes : ByteArray) : Except String ClaimCommand.Request :=
  RequestCodec.decode RequestCodec.getClaimRequest RequestCodec.putClaimRequest bytes

def Envelope.toIxon (envelope : Envelope) : ByteArray := envelopeBytes envelope

def Envelope.ofIxon (bytes : ByteArray) : Except String Envelope :=
  RequestCodec.decode getEnvelope putEnvelope bytes

end Ix.Certified
