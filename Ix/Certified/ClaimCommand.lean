/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.ClaimSuggest
import Ix.Kernel.CertifiedClaims

/-! Typed checking for the versioned public claim protocol. Public bytes and
their expected address are inputs; requests supply untrusted search hints.
The JSON reader supports legacy requests. Command-line input formats are in
`Ix.Certified.CLI`. Each successful run ends in the certified TcM claim checker. -/

namespace Ix.Certified.ClaimCommand

universe v

inductive Hint where
  | logical (hint : LogicalHint)
  | contains (tree : ByteArray)
  | reveal (witness : RevealWitness)

structure Request where
  address : Address
  hint : Hint

def readAddress (value : String) : Except String Address :=
  match Address.fromString value with
  | none => .error "expected a 32-byte hexadecimal address"
  | some address => .ok address

def readHex (value : String) : Except String ByteArray :=
  match bytesOfHex value with
  | none => .error "expected an even-length hexadecimal byte string"
  | some bytes => .ok bytes

def readOptionalHex (json : Lean.Json) (field : String) : Except String (Option ByteArray) := do
  (← json.getObjValAs? (Option String) field).mapM readHex

def readLeaf (json : Lean.Json) : Except String LeafHint := do
  let bytes ← readHex (← json.getObjValAs? String "claim")
  let claim ← Ixon.runGetExact Ix.Claim.get bytes
  if Ix.Claim.ser claim != bytes then throw "noncanonical leaf claim bytes"
  return ⟨claim, ← readOptionalHex json "subjects", ← readOptionalHex json "frontier"⟩

def readLogicalHint (json : Lean.Json) : Except String LogicalHint := do
  let objects ← (← json.getObjValAs? (List String) "objects").mapM readAddress
  let naturals ← (← json.getObjValAs? (List String) "naturals").mapM readAddress
  let leaves ← (← json.getObjValAs? (List Lean.Json) "leaves").mapM readLeaf
  return ⟨⟨objects, naturals⟩, leaves, ← readOptionalHex json "subjects",
    ← readOptionalHex json "members", ← readOptionalHex json "frontier", ← readOptionalHex json "axioms",
    ← ModelHint.readOptional json⟩

def readRequest (json : Lean.Json) : Except String Request := do
  let address ← readAddress (← json.getObjValAs? String "address")
  let kind ← json.getObjValAs? String "kind"
  let hint : Hint ← if kind = "logical" then do pure (Hint.logical (← readLogicalHint json))
    else if kind = "contains" then do pure (Hint.contains (← readHex (← json.getObjValAs? String "tree")))
    else if kind = "reveal" then do
      let secret ← readAddress (← json.getObjValAs? String "secret")
      let payload ← readAddress (← json.getObjValAs? String "payload")
      pure (Hint.reveal ⟨⟨secret, payload⟩⟩)
    else throw "kind must be logical, contains or reveal"
  return ⟨address, hint⟩

def suggestWitness? (fuel : Nat) (source : Ixon.Env) (bytes : ByteArray) (request : Request) :
    Option ClaimWitness := do
  let reading ← readEnvelope? fuel request.address bytes
  match request.hint with
  | .logical hint => return .logical (← suggestLogical? fuel source reading.envelope hint)
  | .contains tree => return .contains tree
  | .reveal witness => return .reveal witness

def run (fuel : Nat) (source : Ixon.Env) (bytes : ByteArray) (request : Request) : Except String Unit := do
  let some witness := suggestWitness? fuel source bytes request
    | throw "certified envelope or witness search declined"
  if Kernel.acceptsCertifiedClaim.{v} fuel source request.address bytes witness then return ()
  else throw "certified claim validation rejected the witness"

theorem run_success {fuel : Nat} {source : Ixon.Env} {bytes : ByteArray} {request : Request}
    (h : run.{v} fuel source bytes request = .ok ()) :
    ∃ witness, Kernel.acceptsCertifiedClaim.{v} fuel source request.address bytes witness = true := by
  cases hw : suggestWitness? fuel source bytes request with
  | none => simp [run, hw] at h
  | some witness =>
    by_cases ha : Kernel.acceptsCertifiedClaim.{v} fuel source request.address bytes witness = true
    · exact ⟨witness, ha⟩
    · simp [run, hw, ha] at h

theorem run_meaning {fuel : Nat} {source : Ixon.Env} {bytes : ByteArray} {request : Request}
    (h : run.{v} fuel source bytes request = .ok ()) :
    ∃ receipt : ClaimReceipt.{v} source fuel request.address bytes,
      Address.blake3 bytes = request.address ∧ envelopeBytes receipt.reading.envelope = bytes ∧
      SemanticClaimMeaning.{v} source fuel receipt.reading.envelope := by
  obtain ⟨witness, hw⟩ := run_success h
  obtain ⟨receipt, _, ha, hb, hm⟩ := Kernel.accepted_tc_claim_meaning hw
  exact ⟨receipt, ha, hb, hm⟩

end Ix.Certified.ClaimCommand
