import IxC.Kernel.Admission.Theorems
import IxC.Fixtures.Codec
import IxC.Fixtures.Authentic

/-! Byte admission: the byte stage (batch limits, key uniqueness, address
authentication, canonical decoding) of the
certified entry `Ix.Kernel.Admission.checkBytes`, and that entry's verdicts on
the shared Ixon record fixtures, sealed under the kernel-side fixture hash
(`Tests.Ix.Kernel.Authentic.fixtureHash`). The entry's reader and checker
are tested in `Tests.Ix.Kernel.Reader` and `Tests.Ix.Kernel.CertifiedEntry`,
and authentication at BLAKE3 in `Tests.Ix.Kernel.Authentication`. -/

open Tests.Ix.Kernel.IxonFixtures Tests.Ix.Kernel.Codec Tests.Ix.Kernel.Authentic

namespace Tests.Ix.Kernel.ByteAdmission

open Ix.Kernel.Admission

def limits : Limits := ⟨256, 256, 1048576, 65536, 65536⟩

def encode (constants : List (Address × Ixon.Constant)) : Records :=
  constants.map fun (address, constant) => (address, Ixon.serConstant constant)

/-- A payload under its fixture-hash key. -/
def authentic (bytes : ByteArray) : Address × ByteArray := (fixtureHash bytes, bytes)

/-- A fixture's records under authentic keys. -/
def sealed (constants : List (Address × Ixon.Constant)) : Records := (rekey fixtureHash constants).encoded

def roundtrip (constants : List (Address × Ixon.Constant)) : Bool :=
  match decodeRecords limits (encode constants) with
  | .ok decoded => decoded == constants
  | .error _ => false

def check (records : Records) (blobs : List (Address × ByteArray) := []) (bounds : Limits := limits) :
    Except Ix.Kernel.Admission.Error Ix.Kernel.Env :=
  checkBytes fixtureHash bounds records blobs

/-- The entry's verdict on a fixture sealed under the fixture hash. -/
def accepts (constants : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := []) : Bool :=
  let s := rekey fixtureHash constants blobs
  (check s.encoded s.blobs).isOk

def outcomeOf (constants : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := []) :
    Option Outcome :=
  let s := rekey fixtureHash constants blobs
  match check s.encoded s.blobs with
  | .ok _ => none
  | .error error => some error.outcome

/-- The byte stage's verdict alone: `none` when the batch limits hold, no
key repeats in its table, every key is the hash of its bytes, and every
record decodes canonically. -/
def failure (records : Records) (blobs : List (Address × ByteArray) := []) (bounds : Limits := limits) :
    Option Ix.Kernel.Admission.ByteError :=
  match preflight bounds records blobs, uniqueKeys records blobs, authenticate fixtureHash records blobs,
      decodeRecords bounds records with
  | .error error, _, _, _ => some error
  | .ok _, .error error, _, _ => some error
  | .ok _, .ok _, .error error, _ => some error
  | .ok _, .ok _, .ok _, .error error => some error
  | .ok _, .ok _, .ok _, .ok _ => none

/-- The certified entry reports the byte stage's failures unchanged. -/
def entryAgrees (records : Records) (blobs : List (Address × ByteArray) := []) (bounds : Limits := limits) : Bool :=
  match failure records blobs bounds, check records blobs bounds with
  | some (.limit resource), .error (.limit resource') => resource == resource'
  | some (.duplicate table position address), .error (.duplicate table' position' address') =>
    table == table' && position == position' && address == address'
  | some (.mismatch table position address), .error (.mismatch table' position' address') =>
    table == table' && position == position' && address == address'
  | some (.decode position address _), .error (.decode position' address' _) =>
    position == position' && address == address'
  | none, .error (.limit _) | none, .error (.duplicate ..) | none, .error (.mismatch ..)
  | none, .error (.decode ..) => false
  | none, _ => true
  | some _, _ => false

def decodeFailureAt (records : Records) (position : Nat) (address : Address)
    (bounds : Limits := limits) : Bool :=
  entryAgrees records [] bounds &&
  match failure records (bounds := bounds) with
  | some (.decode found key _) => found == position && key == address
  | _ => false

/-- The record at `position` passes authentication and fails to decode
there. -/
def decodeFailureOf (records : Records) (position : Nat) (bounds : Limits := limits) : Bool :=
  match records[position]? with
  | some (address, _) => decodeFailureAt records position address bounds
  | none => false

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
-- The entry admits a sharing table that is not the canonical one (a slot
-- referenced once): Ixon v4 does not check the table's canonicity on read.
#guard accepts [(address 1, singleUseSharing)]
-- Typing is contract-blind: a `linear` λ checks against a `many` type.
#guard accepts [(address 1, { identity with info := .defn ⟨.defn, .safe, 1, idType,
    .lam .linear (.sort 0) (.leanLam (.var 0) (.var 0))⟩ })]

-- A duplicate record or blob address is malformed (the byte stage rejects
-- it); a reference to a later record and a family stored without its
-- recursor are checker or reader verdicts, which decline at the Ix API
-- (`Ix.Kernel.Admission.Error.outcome`).
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

-- Key uniqueness runs after the batch limits and before authentication and
-- decoding; the position is the second occurrence's, and the payloads do not
-- matter.
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
-- the same authentic record twice is a duplicate
#guard failure (sealed [(address 1, identity), (address 1, identity)]) =
  some (.duplicate .records 1 (fixtureHash (Ixon.serConstant identity)))
-- controls: distinct keys pass the stage, and a record key may also be a blob
-- key (a blob that holds a record's payload)
#guard failure (sealed [(address 1, identity), (address 2, aliasIdentity)])
    [authentic ⟨#[1]⟩, authentic ⟨#[2]⟩] = none
#guard accepts [(address 1, identity)] [(address 1, Ixon.serConstant identity)]
#guard (rekey fixtureHash [(address 1, identity)] [(address 1, Ixon.serConstant identity)]).encoded.map (·.1) ==
  (rekey fixtureHash [(address 1, identity)] [(address 1, Ixon.serConstant identity)]).blobs.map (·.1)
#guard (uniqueKeys [] []).isOk

-- Authentication runs after key uniqueness and before decoding: a record or
-- blob whose key is not the hash of its bytes, exactly as supplied, rejects
-- at its position. A record's payload is hashed as supplied, before it is
-- decoded, so a payload that would not decode reports the wrong key first.
#guard failure (encode [(address 1, identity)]) = some (.mismatch .records 0 (address 1))
#guard failure (sealed [(address 1, identity)] ++ encode [(address 2, aliasIdentity)]) =
  some (.mismatch .records 1 (address 2))
#guard failure (sealed [(address 1, identity)]) [authentic ⟨#[1]⟩, (address 9, ⟨#[2]⟩)] =
  some (.mismatch .blobs 1 (address 9))
#guard failure [(address 1, ⟨#[0xff]⟩)] = some (.mismatch .records 0 (address 1))
-- the key of another payload, and the key of the record's own payload with
-- a byte appended
#guard failure [(fixtureHash (Ixon.serConstant identity), Ixon.serConstant sharedIdentity)] =
  some (.mismatch .records 0 (fixtureHash (Ixon.serConstant identity)))
#guard failure [(fixtureHash (Ixon.serConstant identity), (Ixon.serConstant identity).push 0)] =
  some (.mismatch .records 0 (fixtureHash (Ixon.serConstant identity)))
#guard entryAgrees (encode [(address 1, identity)])
#guard entryAgrees (sealed [(address 1, identity)]) [authentic ⟨#[1]⟩, (address 9, ⟨#[2]⟩)]
#guard match check (encode [(address 1, identity)]) with
  | .error error => error.outcome == .rejected
  | .ok _ => false
#guard (authenticate fixtureHash [] []).isOk
#guard (authenticate fixtureHash (sealed falseStore) [authentic ⟨#[1]⟩]).isOk

def one : Records := sealed [(address 1, identity)]
def two : Records := sealed [(address 1, identity), (address 2, aliasIdentity)]
def blob : List (Address × ByteArray) := [authentic ⟨#[1, 2, 3]⟩]

#guard failure two (bounds := { limits with maxTotalBytes := payloadBytes two - 1 }) =
  some (.limit .totalBytes)
#guard failure two (bounds := { limits with maxTotalBytes := payloadBytes two }) = none
#guard failure one blob
    (bounds := { limits with maxTotalBytes := payloadBytes one + payloadBytes blob - 1 }) =
  some (.limit .totalBytes)
#guard failure one blob
    (bounds := { limits with maxTotalBytes := payloadBytes one + payloadBytes blob }) = none
#guard decodeFailureOf one 0 { limits with maxRecordBytes := payloadBytes one - 1 }
#guard failure one (bounds := { limits with maxRecordBytes := payloadBytes one }) = none
#guard decodeFailureOf one 0 { limits with maxRecordUnivNodes := 0 }
#guard failure one (bounds := { limits with maxRecordUnivNodes := 1 }) = none
#guard (check two (bounds := { limits with maxTotalBytes := payloadBytes two })).isOk
#guard (check one blob (bounds := { limits with maxTotalBytes := payloadBytes one + payloadBytes blob })).isOk
#guard entryAgrees two (bounds := { limits with maxTotalBytes := payloadBytes two - 1 })
#guard entryAgrees one blob
    (bounds := { limits with maxTotalBytes := payloadBytes one + payloadBytes blob - 1 })

-- Every proper prefix and every appended byte is rejected at its original
-- position; canonical spelling is checked before semantic admission.
#guard (List.range (Ixon.serConstant identity).size).all fun size =>
  decodeFailureOf [authentic ((Ixon.serConstant identity).extract 0 size)] 0
#guard (List.range 256).all fun byte =>
  decodeFailureOf [authentic ((Ixon.serConstant identity).push byte.toUInt8)] 0
#guard alternateSpellings.all fun bytes =>
  decodeFailureOf [authentic bytes] 0
#guard decodeFailureOf (one ++ [authentic ⟨#[]⟩]) 1
#guard decodeFailureOf (one ++ [authentic invalidSharingCount]) 1
#guard decodeFailureOf (one ++ [authentic (recordSharingCount [0xC3, 0x80, 0xBF, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF])])
  1
#guard decodeFailureOf [authentic (recordUnivsPayload 1 successorBomb)] 0

example (V : Type) [Ix.Kernel.SetTheory V] {env : Ix.Kernel.Env}
    (h : checkBytes fixtureHash limits (sealed separatedFalse) [] = .ok env) :
    Nonempty (Ix.Kernel.Model V env) :=
  checkBytes_has_model V h

example {constants : List (Address × Ixon.Constant)} {records : Records}
    (h : Ix.Kernel.Admission.RecordsRead limits records constants) : records = encode constants :=
  h.encode

example {hash : ByteArray → Address} {records : Records} {blobs : List (Address × ByteArray)}
    {env : Ix.Kernel.Env} (h : checkBytes hash limits records blobs = .ok env) :
    (records.map Prod.fst).Nodup ∧ (blobs.map Prod.fst).Nodup := by
  obtain ⟨_, _, _, _, _, _, _, keys, _⟩ := checkBytes_reading h
  exact keys

example {hash : ByteArray → Address} {records : Records} {blobs : List (Address × ByteArray)}
    {env : Ix.Kernel.Env} (h : checkBytes hash limits records blobs = .ok env) :
    (∀ entry ∈ records, entry.1 = hash entry.2) ∧ ∀ entry ∈ blobs, entry.1 = hash entry.2 :=
  checkBytes_authentic h

example {hash : ByteArray → Address} {records : Records} {blobs : List (Address × ByteArray)}
    {env : Ix.Kernel.Env} (h : checkBytes hash limits records blobs = .ok env) :
    ∃ constants, Ix.Kernel.Admission.RecordsRead limits records constants ∧
      ∀ entry ∈ constants, entry.1 = hash (Ixon.serConstant entry.2) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, constants, reading, hashed, _⟩ := checkBytes_reading h
  exact ⟨constants, reading, hashed⟩

example {hash : ByteArray → Address} {records : Records} {blobs : List (Address × ByteArray)}
    {env : Ix.Kernel.Env} (h : checkBytes hash limits records blobs = .ok env) :
    ∃ constants, Ix.Kernel.Admission.RecordsRead limits records constants ∧
      Ix.Kernel.Admission.resourceUnits constants ≤
        2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes :=
  checkBytes_resources h

end Tests.Ix.Kernel.ByteAdmission
