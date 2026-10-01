/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Consistency
import Tests.Ix.Kernel.Codec

/-! Byte admission: the byte stage (batch limits, canonical decoding) of the
certified entry `Ix.Ixon.Admission.checkBytes`, and that entry's verdicts on
the shared Ixon record fixtures. The entry's reader and checker are tested
in `Tests.Ix.Kernel.ConLecheReader` and `Tests.Ix.Kernel.CertifiedEntry`.
Until L6 (plan v4) these fixtures also ran through the intrinsic kernel's
entry `checkBytesIntrinsic`, retired with that kernel. -/

open Tests.Ix.Kernel.IxonFixtures Tests.Ix.Kernel.Codec

namespace Tests.Ix.Kernel.ByteAdmission

open Ix.Ixon.Admission

def limits : Limits := ⟨256, 256, 1048576, 65536, 65536⟩

def encode (constants : List (Address × Ixon.Constant)) : Records :=
  constants.map fun (address, constant) => (address, Ixon.serConstant constant)

def roundtrip (constants : List (Address × Ixon.Constant)) : Bool :=
  match decodeRecords limits (encode constants) with
  | .ok decoded => decoded == constants
  | .error _ => false

def check (records : Records) (blobs : List (Address × ByteArray) := []) (bounds : Limits := limits) :
    Except Ix.Ixon.ConLecheAdmission.Error ConLeche.Env :=
  checkBytes bounds records blobs

def accepts (constants : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := []) : Bool :=
  (check (encode constants) blobs).isOk

def outcomeOf (constants : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := []) :
    Option Outcome :=
  match check (encode constants) blobs with
  | .ok _ => none
  | .error error => some (outcome error)

/-- The byte stage's verdict alone: `none` when the batch limits hold and
every record decodes canonically. -/
def failure (records : Records) (blobs : List (Address × ByteArray) := []) (bounds : Limits := limits) :
    Option Ix.Ixon.Admission.Error :=
  match preflight bounds records blobs, decodeRecords bounds records with
  | .error error, _ => some error
  | .ok _, .error error => some error
  | .ok _, .ok _ => none

/-- The certified entry reports the byte stage's failures unchanged. -/
def entryAgrees (records : Records) (blobs : List (Address × ByteArray) := []) (bounds : Limits := limits) : Bool :=
  match failure records blobs bounds, check records blobs bounds with
  | some (.limit resource), .error (.limit resource') => resource == resource'
  | some (.decode position address _), .error (.decode position' address' _) =>
    position == position' && address == address'
  | none, .error (.limit _) | none, .error (.decode ..) => false
  | none, _ => true
  | some _, _ => false

def decodeFailureAt (records : Records) (position : Nat) (address : Address)
    (bounds : Limits := limits) : Bool :=
  entryAgrees records [] bounds &&
  match failure records (bounds := bounds) with
  | some (.decode found key _) => found == position && key == address
  | _ => false

#guard roundtrip variants
#guard roundtrip falseStore
#guard roundtrip separatedFalse
#guard roundtrip [(address 1, sharedIdentity)]
#guard roundtrip [(address 1, identity), (address 2, aliasIdentity), (address 1, sharedIdentity)]
#guard accepts []
#guard accepts falseStore
#guard accepts separatedFalse
#guard accepts [(address 1, sharedIdentity)]
#guard accepts [(address 1, identity), (address 2, aliasIdentity)]
-- Ixon v3 admits single-use sharing entries and erases binder contracts.
#guard accepts [(address 1, singleUseSharing)]
#guard accepts [(address 1, { identity with info := .defn ⟨.defn, .safe, 1, idType,
    .lam .linear (.sort 0) (.leanLam (.var 0) (.var 0))⟩ })]

-- A duplicate record address is malformed (the reader rejects it); a
-- reference to a later record and a family stored without its recursor are
-- checker or reader verdicts, which decline at the Ix API (D-trust rows
-- 21-22; the intrinsic kernel rejected the first and admitted the second).
#guard outcomeOf [(address 1, identity), (address 1, identity)] = some .rejected
#guard outcomeOf [(address 2, aliasIdentity), (address 1, identity)] = some .declined
#guard outcomeOf [(address 3, falseFamily), (address 4, falseProjection)] = some .declined

-- Preflight rejects oversized batches before it reaches even the first
-- malformed payload; counts include zero-byte entries and projections. The
-- certified entry reports each failure unchanged.
def malformed : Records := [(address 1, ⟨#[]⟩)]
#guard failure malformed (bounds := { limits with maxRecords := 0 }) = some (.limit .records)
#guard failure malformed [(address 9, ⟨#[]⟩)]
    (bounds := { limits with maxBlobs := 0 }) = some (.limit .blobs)
#guard failure malformed [(address 9, ⟨#[1]⟩)]
    (bounds := { limits with maxTotalBytes := 0 }) = some (.limit .totalBytes)
#guard failure (encode falseStore) (bounds := { limits with maxRecords := 2 }) =
  some (.limit .records)
#guard (preflight ⟨0, 0, 0, 0, 0⟩ [] []).isOk
#guard failure [] [(address 9, ⟨#[]⟩), (address 10, ⟨#[]⟩)]
    (bounds := { limits with maxBlobs := 1 }) = some (.limit .blobs)
#guard entryAgrees malformed (bounds := { limits with maxRecords := 0 })
#guard entryAgrees malformed [(address 9, ⟨#[]⟩)] (bounds := { limits with maxBlobs := 0 })
#guard entryAgrees malformed [(address 9, ⟨#[1]⟩)] (bounds := { limits with maxTotalBytes := 0 })
#guard entryAgrees (encode falseStore) (bounds := { limits with maxRecords := 2 })
#guard entryAgrees [] [(address 9, ⟨#[]⟩), (address 10, ⟨#[]⟩)] (bounds := { limits with maxBlobs := 1 })

def one : Records := encode [(address 1, identity)]
def two : Records := encode [(address 1, identity), (address 2, aliasIdentity)]
def blob : List (Address × ByteArray) := [(address 9, ⟨#[1, 2, 3]⟩)]

#guard failure two (bounds := { limits with maxTotalBytes := payloadBytes two - 1 }) =
  some (.limit .totalBytes)
#guard failure two (bounds := { limits with maxTotalBytes := payloadBytes two }) = none
#guard failure one blob
    (bounds := { limits with maxTotalBytes := payloadBytes one + payloadBytes blob - 1 }) =
  some (.limit .totalBytes)
#guard failure one blob
    (bounds := { limits with maxTotalBytes := payloadBytes one + payloadBytes blob }) = none
#guard decodeFailureAt one 0 (address 1) { limits with maxRecordBytes := payloadBytes one - 1 }
#guard failure one (bounds := { limits with maxRecordBytes := payloadBytes one }) = none
#guard decodeFailureAt one 0 (address 1) { limits with maxRecordUnivNodes := 0 }
#guard failure one (bounds := { limits with maxRecordUnivNodes := 1 }) = none
#guard (check two (bounds := { limits with maxTotalBytes := payloadBytes two })).isOk
#guard (check one blob (bounds := { limits with maxTotalBytes := payloadBytes one + payloadBytes blob })).isOk
#guard entryAgrees two (bounds := { limits with maxTotalBytes := payloadBytes two - 1 })
#guard entryAgrees one blob
    (bounds := { limits with maxTotalBytes := payloadBytes one + payloadBytes blob - 1 })

-- Every proper prefix and every appended byte is rejected at its original
-- position; canonical spelling is checked before semantic admission.
#guard (List.range (Ixon.serConstant identity).size).all fun size =>
  decodeFailureAt [(address 1, (Ixon.serConstant identity).extract 0 size)] 0 (address 1)
#guard (List.range 256).all fun byte =>
  decodeFailureAt [(address 1, (Ixon.serConstant identity).push byte.toUInt8)] 0 (address 1)
#guard alternateSpellings.all fun bytes =>
  decodeFailureAt [(address 1, bytes)] 0 (address 1)
#guard decodeFailureAt (one ++ [(address 2, ⟨#[]⟩)]) 1 (address 2)
#guard decodeFailureAt (one ++ [(address 2, nonminimalSharingCount)]) 1 (address 2)
#guard decodeFailureAt [(address 1, recordUnivsPayload 1 successorBomb)] 0 (address 1)

example (V : Type) [ConLeche.SetTheory V] {env : ConLeche.Env}
    (h : checkBytes limits (encode separatedFalse) [] = .ok env) : Nonempty (ConLeche.Model V env) :=
  checkBytes_has_model V h

example {constants : List (Address × Ixon.Constant)} {records : Records}
    (h : Ix.Ixon.Verify.Admission.RecordsRead limits records constants) : records = encode constants :=
  h.encode

example {records : Records} {blobs : List (Address × ByteArray)} {env : ConLeche.Env}
    (h : checkBytes limits records blobs = .ok env) :
    ∃ constants, Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
      Ix.Ixon.Verify.Admission.resourceUnits constants ≤
        2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes :=
  checkBytes_resources h

end Tests.Ix.Kernel.ByteAdmission
