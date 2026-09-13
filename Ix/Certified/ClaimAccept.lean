/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.Reveal

namespace Ix.Certified

open Ix.Theory Ix.Theory.Certified Ix.Theory.Model Ix.Theory.Model.SetTheory

universe v

def LogicalKind : Ix.Claim → Prop
  | .check .. | .checkEnv .. | .catalog .. => True
  | _ => False

theorem LogicalReceipt.kind (receipt : LogicalReceipt.{v} source fuel envelope witness) :
    LogicalKind envelope.claim := by
  have h := receipt.checked.content.meaning
  cases hc : envelope.claim <;> simp_all [LogicalKind]

/-- Meaning of the exact source declarations selected by the public claim.
The annotated readings remain tied to their original type fields and tables. -/
def SubjectsInterpreted (receipt : LogicalReceipt.{v} source fuel envelope witness)
    (V : Type v) [SetTheory V] (constants : Assignment Address V) : Prop :=
  ∀ ref ∈ receipt.checked.subjects, ∃ entry,
    SourceDeclarationReading source receipt.snapshot.decodedObjects receipt.snapshot.decodedNaturals ref entry ∧
    ∀ levels, levels.length = entry.universes → ∀ env,
      WellDenoted constants levels env entry.type ∧
      constants ref levels ∈ˢ interp constants levels env entry.type

def LogicalMeaning (source : Ixon.Env) (fuel : Nat) (envelope : Envelope) : Prop :=
  ∃ witness : LogicalWitness, ∃ receipt : LogicalReceipt.{v} source fuel envelope witness,
    SignatureReading envelope.profile receipt.snapshot.decodedObjects receipt.checked.signature ∧
    (∀ ref ∈ receipt.checked.frontierRefs, ∃ entry,
      receipt.checked.batch.receipt.frontier.interface.entries ref = some entry ∧
      SourceDeclarationReading source receipt.snapshot.decodedObjects receipt.snapshot.decodedNaturals ref entry) ∧
    (∀ ref ∈ receipt.checked.axiomRefs, ∃ entry,
      Standard.EntrySource receipt.checked.store ref entry ∨ Quotient.EntrySource receipt.checked.store ref entry) ∧
    (∀ (V : Type v) [SetTheory V] (constants : Assignment Address V),
      receipt.checked.signature.Compatible receipt.checked.batch.receipt.frontier.interface.entries constants →
      ∃ constants' : Assignment Address V,
        receipt.checked.signature.Compatible receipt.checked.batch.receipt.checked.result.entries constants' ∧
        Assignment.AgreesOn receipt.checked.batch.receipt.frontier.interface.entries constants constants' ∧
        SubjectsInterpreted receipt V constants') ∧
    (claimFrontier envelope.claim = none → ∀ (V : Type v) [SetTheory V],
      ∃ constants : Assignment Address V,
        receipt.checked.signature.Compatible receipt.checked.batch.receipt.checked.result.entries constants ∧
        SubjectsInterpreted receipt V constants)

theorem LogicalReceipt.meaning (receipt : LogicalReceipt.{v} source fuel envelope witness) :
    LogicalMeaning.{v} source fuel envelope :=
  ⟨witness, receipt, readSignature_sound receipt.checked.signatureReading,
    fun _ h => receipt.checked.original_frontier h,
    fun _ h => receipt.checked.logical_policy h,
    fun V _ constants hM => receipt.subject_meaning V constants hM,
    fun closed V _ => receipt.closed_subject_meaning closed V⟩

/-- One contract for the versioned claim protocol. Structural membership and
revelation remain structural. Evaluation is excluded until a separate
execution/result interpretation has been proved and bound to the profile. -/
def SemanticClaimMeaning (source : Ixon.Env) (fuel : Nat) (envelope : Envelope) : Prop :=
  envelope.protocol = Protocol.current ∧
    match envelope.claim with
    | .check .. | .checkEnv .. | .catalog .. => LogicalMeaning.{v} source fuel envelope
    | .contains root target => envelope.logicalAxioms = none ∧ TreeMembership root target
    | .reveal commitment info => envelope.logicalAxioms = none ∧ RevealMeaning source commitment info
    | .eval .. => False

inductive ClaimWitness where
  | logical (witness : LogicalWitness)
  | contains (tree : ByteArray)
  | reveal (witness : RevealWitness)

inductive ClaimAction (source : Ixon.Env) (fuel : Nat) (envelope : Envelope) where
  | logical {witness : LogicalWitness} (receipt : LogicalReceipt.{v} source fuel envelope witness)
  | contains {root target : Address} {bytes : ByteArray}
      (claim : envelope.claim = .contains root target)
      (noAxioms : envelope.logicalAxioms = none) (opening : TreeOpening fuel root bytes)
      (member : target ∈ treeLeaves opening.tree)
  | reveal {commitment : Address} {info : Ix.RevealConstantInfo} {witness : RevealWitness}
      (claim : envelope.claim = .reveal commitment info)
      (noAxioms : envelope.logicalAxioms = none) (receipt : RevealReceipt source commitment info witness)

structure ClaimReceipt (source : Ixon.Env) (fuel : Nat) (address : Address) (bytes : ByteArray) where
  reading : EnvelopeReading address bytes
  action : ClaimAction.{v} source fuel reading.envelope

def checkClaimAction? (fuel : Nat) (source : Ixon.Env) (envelope : Envelope) (witness : ClaimWitness) :
    Read source (ClaimAction.{v} source fuel envelope) :=
  match hc : envelope.claim, witness with
  | .check .., .logical witness | .checkEnv .., .logical witness | .catalog .., .logical witness => do
    let receipt ← checkLogicalSource?.{v} fuel source envelope witness
    return .logical receipt
  | .contains root target, .contains bytes =>
    if ha : envelope.logicalAxioms = none then
      match readTree? fuel root bytes with
      | none => failure
      | some opening =>
        if hm : (treeLeaves opening.tree).contains target = true then
          pure (.contains hc ha opening (List.contains_iff_mem.mp hm)) else failure
    else failure
  | .reveal commitment info, .reveal witness =>
    if ha : envelope.logicalAxioms = none then do
      let receipt ← checkReveal? source commitment info witness
      return .reveal hc ha receipt
    else failure
  | _, _ => failure

/-- Public source acceptance starts with exact authenticated claim bytes.
Protocol and policy versions are checked before any dispatcher branch. -/
def checkClaimBytes? (fuel : Nat) (source : Ixon.Env) (address : Address) (bytes : ByteArray)
    (witness : ClaimWitness) : Read source (ClaimReceipt.{v} source fuel address bytes) :=
  match readEnvelope? fuel address bytes with
  | none => failure
  | some reading => do
    let action ← checkClaimAction?.{v} fuel source reading.envelope witness
    return ⟨reading, action⟩

def acceptsClaimBytes (fuel : Nat) (source : Ixon.Env) (address : Address) (bytes : ByteArray)
    (witness : ClaimWitness) : Bool :=
  (checkClaimBytes?.{v} fuel source address bytes witness {}).isSome

theorem ClaimReceipt.meaning (receipt : ClaimReceipt.{v} source fuel address bytes) :
    SemanticClaimMeaning.{v} source fuel receipt.reading.envelope := by
  refine ⟨receipt.reading.supported, ?_⟩
  cases receipt.action with
  | logical logical =>
    have kind := logical.kind
    have meaning := logical.meaning
    cases hc : receipt.reading.envelope.claim <;> simp_all [LogicalKind]
  | contains claim noAxioms opening member =>
    rw [claim]
    exact ⟨noAxioms, opening.membership member⟩
  | reveal claim noAxioms revealed =>
    rw [claim]
    exact ⟨noAxioms, revealed.meaning⟩

/-- Successful source checking yields the meaning of the exact authenticated
public envelope, including profile, statement, frontier and logical-use root. -/
theorem accepted_claim_meaning {fuel : Nat} {source : Ixon.Env} {address : Address} {bytes : ByteArray}
    {witness : ClaimWitness} (h : acceptsClaimBytes.{v} fuel source address bytes witness = true) :
    ∃ receipt : ClaimReceipt.{v} source fuel address bytes, ∃ cache,
      checkClaimBytes? fuel source address bytes witness {} = some (receipt, cache) ∧
      Address.blake3 bytes = address ∧ envelopeBytes receipt.reading.envelope = bytes ∧
      SemanticClaimMeaning.{v} source fuel receipt.reading.envelope := by
  unfold acceptsClaimBytes at h
  obtain ⟨⟨receipt, cache⟩, hc⟩ := Option.isSome_iff_exists.mp h
  exact ⟨receipt, cache, hc, receipt.reading.authenticated, receipt.reading.canonical, receipt.meaning⟩

theorem evaluation_not_semantic {source : Ixon.Env} {fuel : Nat} {envelope : Envelope}
    {input output : Address} {frontier : Option Address}
    (h : envelope.claim = .eval input output frontier) : ¬ SemanticClaimMeaning.{v} source fuel envelope := by
  simp [SemanticClaimMeaning, h]

theorem membership_not_leaf {fuel : Nat} {root target : Address} {bytes : Option ByteArray} :
    readSubjectView? fuel (.contains root target) bytes = none := by cases bytes <;> rfl

theorem revelation_not_leaf {fuel : Nat} {commitment : Address} {info : Ix.RevealConstantInfo}
    {bytes : Option ByteArray} : readSubjectView? fuel (.reveal commitment info) bytes = none := by
  cases bytes <;> rfl

end Ix.Certified
