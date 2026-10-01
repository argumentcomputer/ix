/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Canonical
import Ix.Kernel.Ingress.Reading
import Ix.Kernel.Check

/-! # The byte stage of admission

Batch limits (`preflight`) and canonical per-record decoding
(`decodeRecords`), shared by the certified entry
(`Ix.Ixon.Admission.checkBytes`, con-leche behind the Ixon reader) and the
intrinsic reference entry (`Ix.Ixon.Admission.checkBytesIntrinsic`).
Their composition is proved in `Ix.Ixon.Verify.Admission`.

The host supplies record order, address keys, and literal blobs. Addresses
are keys, not authenticated content hashes. Blobs retain their exact supplied
bytes. No host decoder or verdict participates in this path.
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

/-- Keep byte failures separate from the kernel's rejected/declined outcomes.
The decoder position is zero-based and identifies the original input record. -/
inductive Error where
  | limit (resource : Resource)
  | decode (position : Nat) (address : Address) (reason : String)
  | kernel (error : Kernel.Error)
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

