/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified
import Ix.Certified.ClaimAccept

namespace Ix.Kernel

open Ix.Certified

universe v

namespace TcM

def checkClaimCertified (fuel : Nat) (source : Ixon.Env) (address : Address) (bytes : ByteArray)
    (witness : ClaimWitness) (cache : InputCache) :
    TcM m (ClaimReceipt.{v} source fuel address bytes × InputCache) := fun state =>
  match checkClaimBytes? fuel source address bytes witness cache with
  | none => .error (.other "certified claim, source, policy or witness check failed") state
  | some result => .ok result state

theorem checkClaimCertified_success {fuel : Nat} {source : Ixon.Env} {address : Address} {bytes : ByteArray}
    {witness : ClaimWitness} {cache nextCache : InputCache}
    {before after : TcState m} {receipt : ClaimReceipt.{v} source fuel address bytes}
    (h : (checkClaimCertified fuel source address bytes witness cache).run before =
      .ok (receipt, nextCache) after) :
    checkClaimBytes? fuel source address bytes witness cache = some (receipt, nextCache) ∧
      after = before := by
  unfold checkClaimCertified EStateM.run at h
  cases hc : checkClaimBytes? fuel source address bytes witness cache with
  | none => simp [hc] at h
  | some result =>
    simp only [hc, EStateM.Result.ok.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

end TcM

def certifiedClaimStep (fuel : Nat) (source : Ixon.Env) (address : Address) (bytes : ByteArray)
    (witness : ClaimWitness) :
    EStateM (TcError .anon) CertifiedState (ClaimReceipt.{v} source fuel address bytes) := fun state =>
  match (TcM.checkClaimCertified fuel source address bytes witness state.inputCache).run state.checker with
  | .error error _ => .error error state
  | .ok (receipt, cache) checker => .ok receipt ⟨checker, cache⟩

theorem certifiedClaimStep_failure {fuel : Nat} {source : Ixon.Env} {address : Address} {bytes : ByteArray}
    {witness : ClaimWitness} {before after : CertifiedState} {error : TcError .anon}
    (h : (certifiedClaimStep.{v} fuel source address bytes witness).run before = .error error after) :
    after = before := by
  unfold certifiedClaimStep EStateM.run at h
  dsimp only at h
  split at h
  · exact (EStateM.Result.error.inj h).2.symm
  · cases h

theorem certifiedClaimStep_success {fuel : Nat} {source : Ixon.Env} {address : Address} {bytes : ByteArray}
    {witness : ClaimWitness} {before after : CertifiedState} {receipt : ClaimReceipt.{v} source fuel address bytes}
    (h : (certifiedClaimStep fuel source address bytes witness).run before = .ok receipt after) :
    checkClaimBytes? fuel source address bytes witness before.inputCache = some (receipt, after.inputCache) ∧
      after.checker = before.checker := by
  unfold certifiedClaimStep EStateM.run at h
  dsimp only at h
  split at h
  · cases h
  · rename_i pair checker he
    rcases pair with ⟨result, cache⟩
    cases h
    exact TcM.checkClaimCertified_success he

def runCertifiedClaim (fuel : Nat) (source : Ixon.Env) (address : Address) (bytes : ByteArray)
    (witness : ClaimWitness) : Option (ClaimReceipt.{v} source fuel address bytes) :=
  match (certifiedClaimStep fuel source address bytes witness).run initialCertifiedState with
  | .error _ _ => none
  | .ok receipt _ => some receipt

def acceptsCertifiedClaim (fuel : Nat) (source : Ixon.Env) (address : Address) (bytes : ByteArray)
    (witness : ClaimWitness) : Bool := (runCertifiedClaim.{v} fuel source address bytes witness).isSome

/-- The actual TcM entry point constructs the meaning of the original claim
from empty initialization. Warm callers have the same receipt theorem and
full rollback; neither logical judgments nor policy decisions are cached. -/
theorem accepted_tc_claim_meaning {fuel : Nat} {source : Ixon.Env} {address : Address} {bytes : ByteArray}
    {witness : ClaimWitness} (h : acceptsCertifiedClaim.{v} fuel source address bytes witness = true) :
    ∃ receipt : ClaimReceipt.{v} source fuel address bytes,
      runCertifiedClaim fuel source address bytes witness = some receipt ∧
      Address.blake3 bytes = address ∧ envelopeBytes receipt.reading.envelope = bytes ∧
      SemanticClaimMeaning.{v} source fuel receipt.reading.envelope := by
  unfold acceptsCertifiedClaim at h
  cases hr : runCertifiedClaim.{v} fuel source address bytes witness with
  | none => simp [hr] at h
  | some receipt => exact ⟨receipt, rfl, receipt.reading.authenticated, receipt.reading.canonical, receipt.meaning⟩

end Ix.Kernel
