/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.Trees
import Ix.Claim

/-! Versioned public claims for the certified source checker. This envelope
binds the original Ix claim, primitive addresses, modeled logical policy and
axiom-use root. The thin-frontier convention is distinct from the legacy
whole-environment convention. A backend still has to bind its actual program
and permitted keys to this source program version. -/

namespace Ix.Certified

structure Protocol where
  format : UInt64 := 1
  codec : UInt64 := 1
  checker : UInt64 := 1
  policy : UInt64 := 1
  aggregation : UInt64 := 1
  deriving DecidableEq

/-- Checker version 2 includes checked model companions for mutual and
nested declarations. Older checker identities do not select this program. -/
def Protocol.current : Protocol := { checker := 2 }

structure Envelope where
  protocol : Protocol
  profile : Profile
  claim : Ix.Claim
  logicalAxioms : Option Address

def envelopeMagic : ByteArray := "IX-CERTIFIED-CLAIM".toUTF8 ++ ⟨#[0]⟩

def putEnvelope (envelope : Envelope) : Ixon.PutM Unit := do
  Ixon.putBytes envelopeMagic
  Ixon.putTag0 ⟨envelope.protocol.format⟩
  Ixon.putTag0 ⟨envelope.protocol.codec⟩
  Ixon.putTag0 ⟨envelope.protocol.checker⟩
  Ixon.putTag0 ⟨envelope.protocol.policy⟩
  Ixon.putTag0 ⟨envelope.protocol.aggregation⟩
  Ixon.Serialize.put envelope.profile.falseType
  Ixon.Serialize.put envelope.profile.falseElim
  Ix.Claim.putOptAddr envelope.profile.natType
  Ix.Claim.put envelope.claim
  Ix.Claim.putOptAddr envelope.logicalAxioms

def envelopeBytes (envelope : Envelope) : ByteArray := Ixon.runPut (putEnvelope envelope)

def getEnvelope : Ixon.GetM Envelope := do
  if (← Ixon.getBytes envelopeMagic.size) != envelopeMagic then throw "invalid certified claim magic"
  let format := (← Ixon.getTag0).size
  let codec := (← Ixon.getTag0).size
  let checker := (← Ixon.getTag0).size
  let policy := (← Ixon.getTag0).size
  let aggregation := (← Ixon.getTag0).size
  let falseType ← Ixon.Serialize.get
  let falseElim ← Ixon.Serialize.get
  let natType ← Ix.Claim.getOptAddr
  let claim ← Ix.Claim.get
  let logicalAxioms ← Ix.Claim.getOptAddr
  return ⟨⟨format, codec, checker, policy, aggregation⟩, ⟨falseType, falseElim, natType⟩, claim, logicalAxioms⟩

structure EnvelopeReading (address : Address) (bytes : ByteArray) where
  envelope : Envelope
  addressSize : address.hash.size = 32
  authenticated : Address.blake3 bytes = address
  parsing : Ixon.runGetExact getEnvelope bytes = .ok envelope
  canonical : envelopeBytes envelope = bytes
  supported : envelope.protocol = Protocol.current

def readEnvelope? (fuel : Nat) (address : Address) (bytes : ByteArray) :
    Option (EnvelopeReading address bytes) :=
  if bytes.size > fuel then none else
  if ha : address.hash.size = 32 ∧ Address.blake3 bytes = address then
    match hp : Ixon.runGetExact getEnvelope bytes with
    | .error _ => none
    | .ok envelope =>
      if hc : envelopeBytes envelope = bytes then
        if hs : envelope.protocol = Protocol.current then some ⟨envelope, ha.1, ha.2, hp, hc, hs⟩
        else none
      else none
  else none

/-- Exact parsing fixes the complete public claim and profile. Semantic or
expression equality is never used to recover the authenticated bytes. -/
theorem EnvelopeReading.unique {a b : EnvelopeReading address bytes} : a.envelope = b.envelope :=
  Except.ok.inj (a.parsing.symm.trans b.parsing)

end Ix.Certified
