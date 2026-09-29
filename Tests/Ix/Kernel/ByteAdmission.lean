/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Verify.Admission
import Tests.Ix.Kernel.Codec

open Ix.Kernel Tests.Ix.Kernel.Ingress Tests.Ix.Kernel.Egress Tests.Ix.Kernel.Codec

namespace Tests.Ix.Kernel.ByteAdmission

open Ix.Ixon.Admission

def limits : Limits := ⟨256, 256, 1048576, 65536, 65536⟩

def encode (constants : Ingress.Constants) : Records :=
  constants.map fun (address, constant) => (address, Ixon.serConstant constant)

def roundtrip (constants : Ingress.Constants) : Bool :=
  match decodeRecords limits (encode constants) with
  | .ok decoded => decoded == constants
  | .error _ => false

def accepts (constants : Ingress.Constants) (blobs : Ingress.Blobs := []) : Bool :=
  (checkBytes.{1} limits {} (encode constants) blobs).isOk

def failure (records : Records) (blobs : Ingress.Blobs := []) (bounds : Limits := limits)
    (cfg : Config := {}) : Option Ix.Ixon.Admission.Error :=
  match checkBytes.{1} bounds cfg records blobs with
  | .ok _ => none
  | .error error => some error

def decodeFailureAt (records : Records) (position : Nat) (address : Address)
    (bounds : Limits := limits) : Bool :=
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
#guard accepts [(address 3, falseFamily), (address 4, falseProjection)]
#guard accepts [(address 1, sharedIdentity)]
#guard accepts [(address 1, identity), (address 2, aliasIdentity)]

#guard failure (encode [(address 1, identity), (address 1, identity)]) =
  some (.kernel (.rejected "duplicate constant address"))
#guard failure (encode [(address 1, identity)])
    [(address 9, ⟨#[]⟩), (address 9, ⟨#[1]⟩)] =
  some (.kernel (.rejected "duplicate blob address"))
#guard match failure (encode [(address 2, aliasIdentity), (address 1, identity)]) with
  | some (.kernel (.rejected _)) => true
  | _ => false
#guard match failure (encode [(address 1, identity)]) (cfg := ⟨0⟩) with
  | some (.kernel (.declined _)) => true
  | _ => false
#guard match failure (encode [(address 1, { identity with info := .defn ⟨.defn, .safe, 1, idType,
    .lam .linear (.sort 0) (.leanLam (.var 0) (.var 0))⟩ })]) with
  | some (.kernel (.declined _)) => true
  | _ => false

-- Preflight rejects oversized batches before it reaches even the first
-- malformed payload; counts include zero-byte entries and projections.
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

def one : Records := encode [(address 1, identity)]
def two : Records := encode [(address 1, identity), (address 2, aliasIdentity)]
def blob : Ingress.Blobs := [(address 9, ⟨#[1, 2, 3]⟩)]

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

example (V : Type 1) [Model.SetTheory V] {env : Env Address}
    (h : checkBytes.{1} limits {} (encode separatedFalse) [] = .ok env) : Nonempty (Model V env) :=
  Ix.Ixon.Verify.Admission.checkBytes_has_model V h

example {records : Records} {blobs : Ingress.Blobs} {env : Env Address}
    (h : checkBytes.{1} limits {} records blobs = .ok env) :
    (records.map Prod.fst).Nodup ∧ (blobs.map Prod.fst).Nodup :=
  Ix.Ixon.Verify.Admission.checkBytes_unique_keys h

example {constants : Ingress.Constants} {records : Records}
    (h : Ix.Ixon.Verify.Admission.RecordsRead limits records constants) : records = encode constants :=
  h.encode

end Tests.Ix.Kernel.ByteAdmission
