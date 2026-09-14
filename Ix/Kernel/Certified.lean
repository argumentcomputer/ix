/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Monad
import Ix.Certified.Ingress

/-! The witness-assisted certified Ix.Kernel entry point. It reads the selected
closure from the actual lazy Ixon store and checks it against the modeled
policy. Its only reusable cache is the checked byte/decoder cache. Existing
inference flags, equivalence classes and judgment caches have no effect on
this entry point. Successful legacy checking does not create a receipt. -/

namespace Ix.Kernel

open Ix.Certified Ix.Theory Ix.Theory.Certified Ix.Theory.Model Ix.Theory.Model.SetTheory

universe v

namespace TcM

def checkCertified (fuel : Nat) (source : Ixon.Env) (profile : Profile) (target : Address)
    (selection : InputSelection) (witness : ProofWitness Address) (cache : InputCache) :
    TcM m (SourceReceipt.{v} source fuel profile target witness × InputCache) := fun state =>
  match checkSource? fuel source profile target selection witness cache with
  | none => .error (.other "certified source, profile, resource or witness check failed") state
  | some result => .ok result state

/-- A successful TcM execution reflects the independent full validator, and
cannot be influenced by pre-existing kernel judgment caches or flags. -/
theorem checkCertified_success {fuel : Nat} {source : Ixon.Env} {profile : Profile} {target : Address}
    {selection : InputSelection} {witness : ProofWitness Address} {cache nextCache : InputCache}
    {before after : TcState m} {receipt : SourceReceipt.{v} source fuel profile target witness}
    (h : (checkCertified fuel source profile target selection witness cache).run before =
      .ok (receipt, nextCache) after) :
    checkSource? fuel source profile target selection witness cache = some (receipt, nextCache) ∧
      after = before := by
  unfold checkCertified EStateM.run at h
  cases hc : checkSource? fuel source profile target selection witness cache with
  | none => simp [hc] at h
  | some result =>
    simp only [hc, EStateM.Result.ok.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- On failure the entire caller state is unchanged. No admission receipt or
partially populated cache escapes the failed source transaction. -/
theorem checkCertified_failure {fuel : Nat} {source : Ixon.Env} {profile : Profile} {target : Address}
    {selection : InputSelection} {witness : ProofWitness Address} {cache : InputCache}
    {before after : TcState m} {error : TcError m}
    (h : (checkCertified.{v} fuel source profile target selection witness cache).run before =
      .error error after) :
    checkSource?.{v} fuel source profile target selection witness cache = none ∧ after = before := by
  unfold checkCertified EStateM.run at h
  cases hc : checkSource?.{v} fuel source profile target selection witness cache with
  | none =>
    simp only [hc, EStateM.Result.error.injEq] at h
    exact ⟨rfl, h.2.symm⟩
  | some result => simp [hc] at h

end TcM

/-- Anonymous initialization constructs IDs directly. It does not evaluate
meta-mode display-name hashing, whose legacy implementation carries native
proof leaves. The certified primitive signature is checked separately. -/
def initialCertifiedPrimitives : Primitives .anon where
  nat := ⟨PrimAddrs.canonical.nat, ()⟩
  natZero := ⟨PrimAddrs.canonical.natZero, ()⟩
  natSucc := ⟨PrimAddrs.canonical.natSucc, ()⟩
  natAdd := ⟨PrimAddrs.canonical.natAdd, ()⟩
  natPred := ⟨PrimAddrs.canonical.natPred, ()⟩
  natSub := ⟨PrimAddrs.canonical.natSub, ()⟩
  natMul := ⟨PrimAddrs.canonical.natMul, ()⟩
  natPow := ⟨PrimAddrs.canonical.natPow, ()⟩
  natGcd := ⟨PrimAddrs.canonical.natGcd, ()⟩
  natMod := ⟨PrimAddrs.canonical.natMod, ()⟩
  natDiv := ⟨PrimAddrs.canonical.natDiv, ()⟩
  natBitwise := ⟨PrimAddrs.canonical.natBitwise, ()⟩
  natBeq := ⟨PrimAddrs.canonical.natBeq, ()⟩
  natBle := ⟨PrimAddrs.canonical.natBle, ()⟩
  natLand := ⟨PrimAddrs.canonical.natLand, ()⟩
  natLor := ⟨PrimAddrs.canonical.natLor, ()⟩
  natXor := ⟨PrimAddrs.canonical.natXor, ()⟩
  natShiftLeft := ⟨PrimAddrs.canonical.natShiftLeft, ()⟩
  natShiftRight := ⟨PrimAddrs.canonical.natShiftRight, ()⟩
  boolType := ⟨PrimAddrs.canonical.boolType, ()⟩
  boolTrue := ⟨PrimAddrs.canonical.boolTrue, ()⟩
  boolFalse := ⟨PrimAddrs.canonical.boolFalse, ()⟩
  string := ⟨PrimAddrs.canonical.string, ()⟩
  stringMk := ⟨PrimAddrs.canonical.stringMk, ()⟩
  charType := ⟨PrimAddrs.canonical.charType, ()⟩
  charMk := ⟨PrimAddrs.canonical.charMk, ()⟩
  charOfNat := ⟨PrimAddrs.canonical.charOfNat, ()⟩
  stringOfList := ⟨PrimAddrs.canonical.stringOfList, ()⟩
  stringToByteArray := ⟨PrimAddrs.canonical.stringToByteArray, ()⟩
  byteArrayEmpty := ⟨PrimAddrs.canonical.byteArrayEmpty, ()⟩
  list := ⟨PrimAddrs.canonical.list, ()⟩
  listNil := ⟨PrimAddrs.canonical.listNil, ()⟩
  listCons := ⟨PrimAddrs.canonical.listCons, ()⟩
  eq := ⟨PrimAddrs.canonical.eq, ()⟩
  eqRefl := ⟨PrimAddrs.canonical.eqRefl, ()⟩
  quotType := ⟨PrimAddrs.canonical.quotType, ()⟩
  quotCtor := ⟨PrimAddrs.canonical.quotCtor, ()⟩
  quotLift := ⟨PrimAddrs.canonical.quotLift, ()⟩
  quotInd := ⟨PrimAddrs.canonical.quotInd, ()⟩
  reduceBool := ⟨PrimAddrs.canonical.reduceBool, ()⟩
  reduceNat := ⟨PrimAddrs.canonical.reduceNat, ()⟩
  eagerReduce := ⟨PrimAddrs.canonical.eagerReduce, ()⟩
  systemPlatformNumBits := ⟨PrimAddrs.canonical.systemPlatformNumBits, ()⟩
  systemPlatformGetNumBits := ⟨PrimAddrs.canonical.systemPlatformGetNumBits, ()⟩
  subtypeVal := ⟨PrimAddrs.canonical.subtypeVal, ()⟩
  natDecLe := ⟨PrimAddrs.canonical.natDecLe, ()⟩
  natDecEq := ⟨PrimAddrs.canonical.natDecEq, ()⟩
  natDecLt := ⟨PrimAddrs.canonical.natDecLt, ()⟩
  decidableRec := ⟨PrimAddrs.canonical.decidableRec, ()⟩
  decidableIsTrue := ⟨PrimAddrs.canonical.decidableIsTrue, ()⟩
  decidableIsFalse := ⟨PrimAddrs.canonical.decidableIsFalse, ()⟩
  natLeOfBleEqTrue := ⟨PrimAddrs.canonical.natLeOfBleEqTrue, ()⟩
  natNotLeOfNotBleEqTrue := ⟨PrimAddrs.canonical.natNotLeOfNotBleEqTrue, ()⟩
  natEqOfBeqEqTrue := ⟨PrimAddrs.canonical.natEqOfBeqEqTrue, ()⟩
  natNeOfBeqEqFalse := ⟨PrimAddrs.canonical.natNeOfBeqEqFalse, ()⟩
  fin := ⟨PrimAddrs.canonical.fin, ()⟩
  boolNoConfusion := ⟨PrimAddrs.canonical.boolNoConfusion, ()⟩
  int := ⟨PrimAddrs.canonical.int, ()⟩
  intOfNat := ⟨PrimAddrs.canonical.intOfNat, ()⟩
  intNegSucc := ⟨PrimAddrs.canonical.intNegSucc, ()⟩
  intAdd := ⟨PrimAddrs.canonical.intAdd, ()⟩
  intSub := ⟨PrimAddrs.canonical.intSub, ()⟩
  intMul := ⟨PrimAddrs.canonical.intMul, ()⟩
  intNeg := ⟨PrimAddrs.canonical.intNeg, ()⟩
  intEmod := ⟨PrimAddrs.canonical.intEmod, ()⟩
  intEdiv := ⟨PrimAddrs.canonical.intEdiv, ()⟩
  intBmod := ⟨PrimAddrs.canonical.intBmod, ()⟩
  intBdiv := ⟨PrimAddrs.canonical.intBdiv, ()⟩
  intNatAbs := ⟨PrimAddrs.canonical.intNatAbs, ()⟩
  intPow := ⟨PrimAddrs.canonical.intPow, ()⟩
  intDecEq := ⟨PrimAddrs.canonical.intDecEq, ()⟩
  intDecLe := ⟨PrimAddrs.canonical.intDecLe, ()⟩
  intDecLt := ⟨PrimAddrs.canonical.intDecLt, ()⟩
  punit := ⟨PrimAddrs.canonical.punit, ()⟩
  natRec := ⟨PrimAddrs.canonical.natRec, ()⟩
  natCasesOn := ⟨PrimAddrs.canonical.natCasesOn, ()⟩
  bitVec := ⟨PrimAddrs.canonical.bitVec, ()⟩
  bitVecToNat := ⟨PrimAddrs.canonical.bitVecToNat, ()⟩
  bitVecOfNat := ⟨PrimAddrs.canonical.bitVecOfNat, ()⟩
  bitVecUlt := ⟨PrimAddrs.canonical.bitVecUlt, ()⟩
  decidableDecide := ⟨PrimAddrs.canonical.decidableDecide, ()⟩
  ltLt := ⟨PrimAddrs.canonical.ltLt, ()⟩
  ofNatOfNat := ⟨PrimAddrs.canonical.ofNatOfNat, ()⟩
  unit := ⟨PrimAddrs.canonical.unit, ()⟩
  punitSizeOf1 := ⟨PrimAddrs.canonical.punitSizeOf1, ()⟩
  sizeOfSizeOf := ⟨PrimAddrs.canonical.sizeOfSizeOf, ()⟩
  stringBack := ⟨PrimAddrs.canonical.stringBack, ()⟩
  stringLegacyBack := ⟨PrimAddrs.canonical.stringLegacyBack, ()⟩
  stringUtf8ByteSize := ⟨PrimAddrs.canonical.stringUtf8ByteSize, ()⟩
  stringAppend := ⟨PrimAddrs.canonical.stringAppend, ()⟩
  stringDecEq := ⟨PrimAddrs.canonical.stringDecEq, ()⟩

/-- State of the certified driver. Semantic judgments are never cached. -/
structure CertifiedState where
  checker : TcState .anon := TcState.new {} initialCertifiedPrimitives
  inputCache : InputCache := {}

/-- The public source program starts with empty kernel and byte caches. -/
def initialCertifiedState : CertifiedState := {}

def certifiedStep (fuel : Nat) (source : Ixon.Env) (profile : Profile) (target : Address)
    (selection : InputSelection) (witness : ProofWitness Address) :
    EStateM (TcError .anon) CertifiedState (SourceReceipt.{v} source fuel profile target witness) := fun state =>
  match (TcM.checkCertified fuel source profile target selection witness state.inputCache).run state.checker with
  | .error error _ => .error error state
  | .ok (receipt, cache) checker => .ok receipt ⟨checker, cache⟩

theorem certifiedStep_failure {fuel : Nat} {source : Ixon.Env} {profile : Profile} {target : Address}
    {selection : InputSelection} {witness : ProofWitness Address}
    {before after : CertifiedState} {error : TcError .anon}
    (h : (certifiedStep.{v} fuel source profile target selection witness).run before = .error error after) :
    after = before := by
  unfold certifiedStep EStateM.run at h
  dsimp only at h
  split at h
  · exact (EStateM.Result.error.inj h).2.symm
  · cases h

/-- All reused cache entries still match current bytes, and every request
reruns full scope, policy, dependency, formation and proof validation. -/
theorem certifiedStep_success {fuel : Nat} {source : Ixon.Env} {profile : Profile} {target : Address}
    {selection : InputSelection} {witness : ProofWitness Address}
    {before after : CertifiedState} {receipt : SourceReceipt.{v} source fuel profile target witness}
    (h : (certifiedStep fuel source profile target selection witness).run before = .ok receipt after) :
    checkSource? fuel source profile target selection witness before.inputCache =
      some (receipt, after.inputCache) ∧ after.checker = before.checker := by
  unfold certifiedStep EStateM.run at h
  dsimp only at h
  split at h
  · cases h
  · rename_i pair checker he
    rcases pair with ⟨result, cache⟩
    cases h
    exact TcM.checkCertified_success he

def runCertified (fuel : Nat) (source : Ixon.Env) (profile : Profile) (target : Address)
    (selection : InputSelection) (witness : ProofWitness Address) :
    Option (SourceReceipt.{v} source fuel profile target witness) :=
  match (certifiedStep fuel source profile target selection witness).run initialCertifiedState with
  | .error _ _ => none
  | .ok receipt _ => some receipt

def acceptsCertifiedSource (fuel : Nat) (source : Ixon.Env) (profile : Profile) (target : Address)
    (selection : InputSelection) (witness : ProofWitness Address) : Bool :=
  (runCertified.{v} fuel source profile target selection witness).isSome

/-- Source success constructs every model premise from actual byte reads and
validator execution. There is no initial semantic model or cache oracle. -/
theorem accepted_tc_has_model {fuel : Nat} {source : Ixon.Env} {profile : Profile} {target : Address}
    {selection : InputSelection} {witness : ProofWitness Address}
    (h : acceptsCertifiedSource.{v} fuel source profile target selection witness = true)
    (V : Type v) [SetTheory V] (levels : List Nat) (env : Nat → V) :
    ∃ receipt : SourceReceipt.{v} source fuel profile target witness,
      runCertified fuel source profile target selection witness = some receipt ∧
      (∀ address bytes, (address, bytes) ∈ receipt.snapshot.blobs → constantBytes? source address = some bytes) ∧
      (∀ address bytes, (address, bytes) ∈ receipt.snapshot.literalBlobs → source.getBlob? address = some bytes) ∧
      ∃ constants : Assignment Address V,
        receipt.prepared.signature.Compatible receipt.proof.environment.entries constants ∧
        WellDenoted constants levels env receipt.proof.proof.val ∧
        WellDenoted constants levels env receipt.proof.proposition.val ∧
        interp constants levels env receipt.proof.proof.val ∈ˢ
          interp constants levels env receipt.proof.proposition.val := by
  unfold acceptsCertifiedSource at h
  cases hr : runCertified.{v} fuel source profile target selection witness with
  | none => simp [hr] at h
  | some receipt =>
    exact ⟨receipt, rfl, fun _ _ he => receipt.snapshot.objects_from_source he,
      fun _ _ he => receipt.snapshot.naturals_from_source he, receipt.has_model V levels env⟩

theorem no_tc_proof_of_False (receipt : SourceReceipt.{v} source fuel profile target witness)
    (V : Type v) [SetTheory V]
    (h : receipt.prepared.input.proposition = receipt.prepared.signature.falseExpr) : False := by
  apply no_proof_of_False (fuel := fuel) (witness := witness) V h
  simp only [acceptsCertified, receipt.checked, Option.isSome_some]


namespace TcM

def checkStoreCertified (fuel : Nat) (source : Ixon.Env) (profile : Profile) (subjects : List Address)
    (selection : InputSelection) (witness : List (DeclarationWitness Address)) (cache : InputCache) :
    TcM m (StoreReceipt.{v} source fuel profile subjects witness × InputCache) := fun state =>
  match checkSourceStore? fuel source profile subjects selection witness cache with
  | none => .error (.other "certified declaration, profile, resource or witness check failed") state
  | some result => .ok result state

theorem checkStoreCertified_success {fuel : Nat} {source : Ixon.Env} {profile : Profile} {subjects : List Address}
    {selection : InputSelection} {witness : List (DeclarationWitness Address)} {cache nextCache : InputCache}
    {before after : TcState m} {receipt : StoreReceipt.{v} source fuel profile subjects witness}
    (h : (checkStoreCertified fuel source profile subjects selection witness cache).run before =
      .ok (receipt, nextCache) after) :
    checkSourceStore? fuel source profile subjects selection witness cache = some (receipt, nextCache) ∧
      after = before := by
  unfold checkStoreCertified EStateM.run at h
  cases hc : checkSourceStore? fuel source profile subjects selection witness cache with
  | none => simp [hc] at h
  | some result =>
    simp only [hc, EStateM.Result.ok.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

end TcM

def certifiedStoreStep (fuel : Nat) (source : Ixon.Env) (profile : Profile) (subjects : List Address)
    (selection : InputSelection) (witness : List (DeclarationWitness Address)) :
    EStateM (TcError .anon) CertifiedState (StoreReceipt.{v} source fuel profile subjects witness) := fun state =>
  match (TcM.checkStoreCertified fuel source profile subjects selection witness state.inputCache).run state.checker with
  | .error error _ => .error error state
  | .ok (receipt, cache) checker => .ok receipt ⟨checker, cache⟩

theorem certifiedStoreStep_failure {fuel : Nat} {source : Ixon.Env} {profile : Profile} {subjects : List Address}
    {selection : InputSelection} {witness : List (DeclarationWitness Address)}
    {before after : CertifiedState} {error : TcError .anon}
    (h : (certifiedStoreStep.{v} fuel source profile subjects selection witness).run before = .error error after) :
    after = before := by
  unfold certifiedStoreStep EStateM.run at h
  dsimp only at h
  split at h
  · exact (EStateM.Result.error.inj h).2.symm
  · cases h

theorem certifiedStoreStep_success {fuel : Nat} {source : Ixon.Env} {profile : Profile} {subjects : List Address}
    {selection : InputSelection} {witness : List (DeclarationWitness Address)}
    {before after : CertifiedState} {receipt : StoreReceipt.{v} source fuel profile subjects witness}
    (h : (certifiedStoreStep fuel source profile subjects selection witness).run before = .ok receipt after) :
    checkSourceStore? fuel source profile subjects selection witness before.inputCache =
      some (receipt, after.inputCache) ∧ after.checker = before.checker := by
  unfold certifiedStoreStep EStateM.run at h
  dsimp only at h
  split at h
  · cases h
  · rename_i pair checker he
    rcases pair with ⟨result, cache⟩
    cases h
    exact TcM.checkStoreCertified_success he

def runCertifiedStore (fuel : Nat) (source : Ixon.Env) (profile : Profile) (subjects : List Address)
    (selection : InputSelection) (witness : List (DeclarationWitness Address)) :
    Option (StoreReceipt.{v} source fuel profile subjects witness) :=
  match (certifiedStoreStep fuel source profile subjects selection witness).run initialCertifiedState with
  | .error _ _ => none
  | .ok receipt _ => some receipt

def acceptsCertifiedStoreSource (fuel : Nat) (source : Ixon.Env) (profile : Profile) (subjects : List Address)
    (selection : InputSelection) (witness : List (DeclarationWitness Address)) : Bool :=
  (runCertifiedStore.{v} fuel source profile subjects selection witness).isSome

/-- Complete declaration requests, including source blocks, construct a
single model realizing every requested member and constructor. -/
theorem accepted_tc_store_has_model {fuel : Nat} {source : Ixon.Env} {profile : Profile} {subjects : List Address}
    {selection : InputSelection} {witness : List (DeclarationWitness Address)}
    (h : acceptsCertifiedStoreSource.{v} fuel source profile subjects selection witness = true)
    (V : Type v) [SetTheory V] :
    ∃ receipt : StoreReceipt.{v} source fuel profile subjects witness,
      runCertifiedStore fuel source profile subjects selection witness = some receipt ∧
      (∀ address bytes, (address, bytes) ∈ receipt.snapshot.blobs → constantBytes? source address = some bytes) ∧
      (∀ address bytes, (address, bytes) ∈ receipt.snapshot.literalBlobs → source.getBlob? address = some bytes) ∧
      ∃ constants : Assignment Address V,
        receipt.prepared.signature.Compatible receipt.result.environment.entries constants ∧
        ∀ r ∈ receipt.prepared.targets, ∃ entry, receipt.result.environment.entries r = some entry ∧
          EntrySource receipt.prepared.signature receipt.prepared.store r entry ∧
          ∀ levels, levels.length = entry.universes → ∀ env : Nat → V,
            WellDenoted constants levels env entry.type ∧
            constants r levels ∈ˢ interp constants levels env entry.type := by
  unfold acceptsCertifiedStoreSource at h
  cases hr : runCertifiedStore.{v} fuel source profile subjects selection witness with
  | none => simp [hr] at h
  | some receipt =>
    exact ⟨receipt, rfl, fun _ _ he => receipt.snapshot.objects_from_source he,
      fun _ _ he => receipt.snapshot.naturals_from_source he, receipt.has_model V⟩

end Ix.Kernel
