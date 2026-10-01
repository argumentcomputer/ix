/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Canonical
import Ix.Kernel.Ingress.Records
import Std.Data.HashSet.Basic

/-! # The byte stage of admission

Batch limits (`preflight`), key uniqueness (`uniqueKeys`) and canonical
per-record decoding (`decodeRecords`) of the certified entry
(`Ix.Ixon.Admission.checkBytes`, con-leche behind the Ixon reader), in that
order. Their composition is proved in `Ix.Ixon.Verify.Admission`.

The host supplies record order, address keys, and literal blobs. Addresses
are keys, not authenticated content hashes, but a batch may use each key
once per table: two records, or two blobs, under one address are malformed
input (a reject at the Ix API, `Ix.Ixon.Admission.outcome`), not a choice
for the reader to make. Blobs retain their exact supplied bytes. No host
decoder or verdict participates in this path.
-/

namespace Ix.Ixon.Admission

open Kernel

abbrev Records := List (Address × ByteArray)

/-- Explicit coverage limits. `maxTotalBytes` counts all constant and blob
payloads, excluding address keys and host transport framing. Universe nodes
are bounded across each record's entire universe table; the batch bound is
therefore at most `maxRecords * maxRecordUnivNodes`. These are input/expansion
limits, not heap or wall-clock bounds for the remaining readers or checker. -/
structure Limits where
  maxRecords : Nat
  maxBlobs : Nat
  maxTotalBytes : Nat
  maxRecordBytes : Nat
  maxRecordUnivNodes : Nat
  deriving Repr

inductive Resource where
  | records
  | blobs
  | totalBytes
  deriving Repr, DecidableEq

/-- The two keyed tables of a batch. -/
inductive Table where
  | records
  | blobs
  deriving Repr, DecidableEq

/-- Byte failures: a batch limit, a key used twice in one table, or a record
that does not decode canonically. Positions are zero-based and identify the
original input record or blob; a duplicate's is its second occurrence.
Checker failures are the entry's own (`Ix.Ixon.KernelAdmission.Error`). -/
inductive Error where
  | limit (resource : Resource)
  | duplicate (table : Table) (position : Nat) (address : Address)
  | decode (position : Nat) (address : Address) (reason : String)
  deriving Repr, DecidableEq

/-- Measure payloads only; admission uses the short-circuiting preflight
below instead of computing this unbounded sum before checking a limit. -/
def payloadBytes : Records → Nat
  | [] => 0
  | (_, bytes) :: rest => bytes.size + payloadBytes rest

/-- Reserve payload bytes and one entry before visiting the rest. A batch
cannot reset the total byte budget between constants or between constants
and blobs. No record decoding occurs during this preflight. -/
def consume (resource : Resource) : Nat → Nat → Records → Except Error Nat
  | _, remaining, [] => .ok remaining
  | 0, _, _ :: _ => .error (.limit resource)
  | count + 1, remaining, (_, bytes) :: rest =>
    if bytes.size ≤ remaining then consume resource count (remaining - bytes.size) rest
    else .error (.limit .totalBytes)

def preflight (limits : Limits) (records : Records) (blobs : Ingress.Blobs) :
    Except Error Unit := do
  let remaining ← consume .records limits.maxRecords limits.maxTotalBytes records
  let _ ← consume .blobs limits.maxBlobs remaining blobs
  return ()

/-- The first key of a table that repeats an earlier one (or one of `seen`),
with its position. -/
def firstDuplicate {α : Type} : Nat → Std.HashSet Address → List (Address × α) →
    Option (Nat × Address)
  | _, _, [] => none
  | position, seen, (address, _) :: rest =>
    if seen.contains address then some (position, address)
    else firstDuplicate (position + 1) (seen.insert address) rest

/-- Each record address and each blob address occurs once
(`Ix.Ixon.Verify.Admission.uniqueKeys_ok_iff`). The entries run it after
`preflight`, so its work is bounded by the batch limits, and before
decoding. -/
def uniqueKeys (records : Records) (blobs : Ingress.Blobs) : Except Error Unit :=
  match firstDuplicate 0 {} records with
  | some (position, address) => .error (.duplicate .records position address)
  | none =>
    match firstDuplicate 0 {} blobs with
    | some (position, address) => .error (.duplicate .blobs position address)
    | none => .ok ()

/-- Tail-recursive decoding retains all records, keys, and their order,
including projections and unused side tables. -/
def decodeLoop (limits : Limits) : Nat → Records → Ingress.Constants →
    Except Error Ingress.Constants
  | _, [], reversed => .ok reversed.reverse
  | position, (address, bytes) :: rest, reversed => do
    let constant ← (_root_.Ixon.Canonical.deConstant limits.maxRecordBytes
      limits.maxRecordUnivNodes bytes).mapError (.decode position address)
    decodeLoop limits (position + 1) rest ((address, constant) :: reversed)

/-- Decode canonical records with per-record byte/universe limits. The batch
preflight is part of `checkBytes`, not this independently useful operation. -/
def decodeRecords (limits : Limits) (records : Records) : Except Error Ingress.Constants :=
  decodeLoop limits 0 records []

