import Ix.Ixon.KernelConsistency
import Tests.Ix.Kernel.Codec

/-! Byte admission: the byte stage (batch limits, key uniqueness, canonical
decoding) of the
certified entry `Ix.Ixon.Admission.checkBytes`, and that entry's verdicts on
the shared Ixon record fixtures. The entry's reader and checker are tested
in `Tests.Ix.Kernel.Reader` and `Tests.Ix.Kernel.CertifiedEntry`. -/

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
    Except Ix.Ixon.Admission.Error Ix.Kernel.Env :=
  checkBytes bounds records blobs

def accepts (constants : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := []) : Bool :=
  (check (encode constants) blobs).isOk

def outcomeOf (constants : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := []) :
    Option Outcome :=
  match check (encode constants) blobs with
  | .ok _ => none
  | .error error => some error.outcome

/-- The byte stage's verdict alone: `none` when the batch limits hold, no
key repeats in its table, and every record decodes canonically. -/
def failure (records : Records) (blobs : List (Address × ByteArray) := []) (bounds : Limits := limits) :
    Option Ix.Ixon.Admission.ByteError :=
  match preflight bounds records blobs, uniqueKeys records blobs, decodeRecords bounds records with
  | .error error, _, _ => some error
  | .ok _, .error error, _ => some error
  | .ok _, .ok _, .error error => some error
  | .ok _, .ok _, .ok _ => none

/-- The certified entry reports the byte stage's failures unchanged. -/
def entryAgrees (records : Records) (blobs : List (Address × ByteArray) := []) (bounds : Limits := limits) : Bool :=
  match failure records blobs bounds, check records blobs bounds with
  | some (.limit resource), .error (.limit resource') => resource == resource'
  | some (.duplicate table position address), .error (.duplicate table' position' address') =>
    table == table' && position == position' && address == address'
  | some (.decode position address _), .error (.decode position' address' _) =>
    position == position' && address == address'
  | none, .error (.limit _) | none, .error (.duplicate ..) | none, .error (.decode ..) => false
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

-- A duplicate record or blob address is malformed (the byte stage rejects
-- it); a reference to a later record and a family stored without its
-- recursor are checker or reader verdicts, which decline at the Ix API
-- (`Ix.Ixon.Admission.Error.outcome`).
#guard outcomeOf [(address 1, identity), (address 1, identity)] = some .rejected
#guard outcomeOf [(address 1, identity)] [(address 9, ⟨#[1]⟩), (address 9, ⟨#[1]⟩)] = some .rejected
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

-- Key uniqueness runs after the batch limits and before decoding; the
-- position is the second occurrence's, and the payloads do not matter.
def twice : Records := encode [(address 1, identity), (address 1, identity)]
def blobTwice : List (Address × ByteArray) := [(address 9, ⟨#[1]⟩), (address 9, ⟨#[2]⟩)]
#guard failure twice = some (.duplicate .records 1 (address 1))
#guard failure (encode [(address 1, identity)]) blobTwice = some (.duplicate .blobs 1 (address 9))
#guard failure [(address 1, ⟨#[]⟩), (address 1, ⟨#[0xff]⟩)] = some (.duplicate .records 1 (address 1))
#guard failure twice blobTwice = some (.duplicate .records 1 (address 1))
#guard failure twice (bounds := { limits with maxRecords := 1 }) = some (.limit .records)
#guard entryAgrees twice
#guard entryAgrees (encode [(address 1, identity)]) blobTwice
#guard entryAgrees [(address 1, ⟨#[]⟩), (address 1, ⟨#[0xff]⟩)]
-- controls: distinct keys pass the stage, and a record key may also be a blob key
#guard failure (encode [(address 1, identity), (address 2, aliasIdentity)])
    [(address 9, ⟨#[1]⟩), (address 10, ⟨#[1]⟩)] = none
#guard accepts [(address 1, identity)] [(address 1, ⟨#[1]⟩)]
#guard (uniqueKeys [] []).isOk

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

example (V : Type) [Ix.Kernel.SetTheory V] {env : Ix.Kernel.Env}
    (h : checkBytes limits (encode separatedFalse) [] = .ok env) : Nonempty (Ix.Kernel.Model V env) :=
  checkBytes_has_model V h

example {constants : List (Address × Ixon.Constant)} {records : Records}
    (h : Ix.Ixon.Verify.Admission.RecordsRead limits records constants) : records = encode constants :=
  h.encode

example {records : Records} {blobs : List (Address × ByteArray)} {env : Ix.Kernel.Env}
    (h : checkBytes limits records blobs = .ok env) :
    (records.map Prod.fst).Nodup ∧ (blobs.map Prod.fst).Nodup := by
  obtain ⟨_, _, _, _, _, _, _, keys, _⟩ := checkBytes_reading h
  exact keys

example {records : Records} {blobs : List (Address × ByteArray)} {env : Ix.Kernel.Env}
    (h : checkBytes limits records blobs = .ok env) :
    ∃ constants, Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
      Ix.Ixon.Verify.Admission.resourceUnits constants ≤
        2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes :=
  checkBytes_resources h

end Tests.Ix.Kernel.ByteAdmission
