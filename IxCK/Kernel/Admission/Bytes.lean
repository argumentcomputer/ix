module

public import IxCK.Ixon.Canonical
public import IxCK.Kernel.Admission.Depth
public import IxCK.Kernel.Ingress.Records
public import Std.Data.HashSet.Basic

/-! # The byte stage of admission

Batch limits (`preflight`), key uniqueness (`uniqueKeys`), address
authentication (`authenticate`) and canonical per-record decoding
(`decodeRecords`) of the certified entry (`Ix.Kernel.Admission.checkBytes`, the
verified checker behind the Ixon reader), in that order. Their composition is
proved in `Ix.Kernel.Admission.Bytes.Theorems`.

The host supplies record order, address keys, and literal blobs. A batch may
use each key once per table: two records, or two blobs, under one address are
malformed input (a reject at the Ix API, `Ix.Kernel.Admission.Error.outcome`),
not a choice for the reader to make. Each key must be the content hash of the
bytes stored under it, exactly as supplied: `authenticate` recomputes the
entry's `hash` parameter over every record payload and every blob and refuses
a mismatch (also a reject). The hash is a parameter because the kernel admits
no hasher (`Ix.Kernel.Audit.kernelImportAllowlist`); the root library
instantiates it at BLAKE3. Blobs retain their exact supplied bytes. No host
decoder or verdict participates in this path.
-/

@[expose] public section

namespace Ix.Kernel.Admission

abbrev Records := List (Address × ByteArray)

/-- Explicit coverage limits. `maxTotalBytes` counts all constant and blob
payloads, excluding address keys and host transport framing. Universe nodes
are bounded across each record's entire universe table; the batch bound is
therefore at most `maxRecords * maxRecordUnivNodes`. These are input/expansion
limits, not heap or wall-clock bounds for the remaining readers or checker.

A record over `maxRecordBytes`, or whose universe table expands past
`maxRecordUnivNodes`, is declined (`.limit .recordBytes`, `.limit .recordUnivNodes`;
`ByteError.asLimit`), as the batch limits are.

The last two fields have defaults. `maxDepth` bounds how deep a record's
expressions and universes nest, as stored (`scanDepths`, before decoding) and
with their shares expanded (`expandedDepths`, after decoding). `workers`
bounds the tasks phase B runs on (`Cached.checkPendingTasks`): `none` is one
task per 64 records, `some 0` the walk on the calling thread, `some w` at most
`w` tasks; it cannot change a verdict (`Cached.checkDecls_cfg`). A limit only
turns an answer into a decline, so an input accepted under some limits is
accepted under larger ones (`docs/kernel.md`, "Limits"). -/
structure Limits where
  maxRecords : Nat
  maxBlobs : Nat
  maxTotalBytes : Nat
  maxRecordBytes : Nat
  maxRecordUnivNodes : Nat
  maxDepth : Nat := 16384
  workers : Option Nat := none
  deriving Repr

/-- The native stack, in bytes, a host runs the entry on: 16 KiB per level of
`maxDepth`, and at least 256 MiB, which the typing core's recursion at its
fixed fuel (`checkFuel`, 100,000 levels, under 1 KiB each as measured) needs
with a margin. 256 MiB at the default. -/
def Limits.stackFor (l : Limits) : Nat := max (256 * 1024 * 1024) (16 * 1024 * l.maxDepth)

inductive Resource where
  | records
  | blobs
  | totalBytes
  /-- A record's payload over `maxRecordBytes` (the decoder's byte budget). -/
  | recordBytes
  /-- A record's universe table expands past `maxRecordUnivNodes` nodes. -/
  | recordUnivNodes
  /-- A record's expressions or universes nest deeper than `maxDepth`, as
  stored or with their shares expanded. -/
  | depth
  deriving Repr, DecidableEq

/-- The two keyed tables of a batch. -/
inductive Table where
  | records
  | blobs
  deriving Repr, DecidableEq

/-- Byte failures: a batch limit, a key used twice in one table, a key that
is not the hash of the bytes stored under it, or a record that does not
decode canonically. Positions are zero-based and identify the original input
record or blob; a duplicate's is its second occurrence. The entry's failures
(`Ix.Kernel.Admission.Error`) include them unchanged (`Error.ofBytes`). -/
inductive ByteError where
  | limit (resource : Resource)
  | duplicate (table : Table) (position : Nat) (address : Address)
  | mismatch (table : Table) (position : Nat) (address : Address)
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
def consume (resource : Resource) : Nat → Nat → Records → Except ByteError Nat
  | _, remaining, [] => .ok remaining
  | 0, _, _ :: _ => .error (.limit resource)
  | count + 1, remaining, (_, bytes) :: rest =>
    if bytes.size ≤ remaining then consume resource count (remaining - bytes.size) rest
    else .error (.limit .totalBytes)

def preflight (limits : Limits) (records : Records) (blobs : Ingress.Blobs) :
    Except ByteError Unit := do
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
(`Ix.Kernel.Admission.uniqueKeys_ok_iff`). The entries run it after
`preflight`, so its work is bounded by the batch limits, and before
decoding. -/
def uniqueKeys (records : Records) (blobs : Ingress.Blobs) : Except ByteError Unit :=
  match firstDuplicate 0 {} records with
  | some (position, address) => .error (.duplicate .records position address)
  | none =>
    match firstDuplicate 0 {} blobs with
    | some (position, address) => .error (.duplicate .blobs position address)
    | none => .ok ()

/-- The first entry of a table whose key is not `hash` of its bytes, with
its position. -/
def firstMismatch (hash : ByteArray → Address) : Nat → List (Address × ByteArray) →
    Option (Nat × Address)
  | _, [] => none
  | position, (address, bytes) :: rest =>
    if hash bytes == address then firstMismatch hash (position + 1) rest
    else some (position, address)

/-- Each record address and each blob address is `hash` of the bytes stored
under it, as supplied (`Ix.Kernel.Admission.authenticate_ok_iff`): a record's
payload is hashed before it is decoded, never re-encoded. The entries run it
after `preflight` and `uniqueKeys`, so the bytes it hashes are bounded by the
batch limits. -/
def authenticate (hash : ByteArray → Address) (records : Records) (blobs : Ingress.Blobs) :
    Except ByteError Unit :=
  match firstMismatch hash 0 records with
  | some (position, address) => .error (.mismatch .records position address)
  | none =>
    match firstMismatch hash 0 blobs with
    | some (position, address) => .error (.mismatch .blobs position address)
    | none => .ok ()

/-- Tail-recursive decoding retains all records, keys, and their order,
including projections and unused side tables. -/
def decodeLoop (limits : Limits) : Nat → Records → Ingress.Constants →
    Except ByteError Ingress.Constants
  | _, [], reversed => .ok reversed.reverse
  | position, (address, bytes) :: rest, reversed => do
    let constant ← (Ixon.Canonical.deConstant limits.maxRecordBytes
      limits.maxRecordUnivNodes bytes).mapError (.decode position address)
    decodeLoop limits (position + 1) rest ((address, constant) :: reversed)

/-- Decode canonical records with per-record byte/universe limits. The batch
preflight is part of `checkBytes`, not this independently useful operation. -/
def decodeRecords (limits : Limits) (records : Records) : Except ByteError Ingress.Constants :=
  decodeLoop limits 0 records []

/-- The decoder's messages for the two per-record limits (`Ixon.Bounded.deConstant`,
`Ixon.Bounded.getUnivFromTag`). -/
def recordBytesExhausted : String := "getConstantBounded: byte budget exhausted"
def univNodesExhausted : String := "getUnivBounded: expanded-node budget exhausted"

/-- **The per-record limits as declines**: `decodeRecords` reports a record over
`maxRecordBytes`, or a universe table that expands past `maxRecordUnivNodes`, as a decode error
carrying the decoder's message; `asLimit` reads those two messages as the limits they are
(`.limit .recordBytes`, `.limit .recordUnivNodes`) and leaves every other error as it is. -/
def ByteError.asLimit : ByteError → ByteError
  | .decode p a r =>
    if r == recordBytesExhausted then .limit .recordBytes
    else if r == univNodesExhausted then .limit .recordUnivNodes
    else .decode p a r
  | e => e

/-- A bound on how deep a record of these bytes can nest: an expression's levels grow by at most one
per byte it is written in (a spine or telescope of `n` steps is written in at least `n` more
bytes), and a universe's by at most the decoder's node budget, which it checks before it
builds a `succ` chain. When `maxDepth` is at least this, the scan cannot decline the record
and is skipped. -/
def storedDepthBound (limits : Limits) (bytes : ByteArray) : Nat :=
  bytes.size + limits.maxRecordUnivNodes + 1

/-- The scan declines a record: within the byte limit, able to reach the depth limit, and
nested past it. -/
def scanFails (limits : Limits) (bytes : ByteArray) : Bool :=
  bytes.size ≤ limits.maxRecordBytes && limits.maxDepth < storedDepthBound limits bytes &&
    !Depth.within limits.maxDepth bytes

/-- **The stored-nesting scan**: every record's expressions (shares as leaves)
and universes within `limits.maxDepth` (`Depth.within`), read from the bytes
before anything decodes them, so that the decoder's recursion is bounded. A
record over `maxRecordBytes` is left to the decoder, which refuses it, and so is a
record the limit cannot be reached in (`storedDepthBound`). -/
def scanDepths (limits : Limits) : Records → Except ByteError Unit
  | [] => .ok ()
  | (_, bytes) :: rest =>
    if scanFails limits bytes then .error (.limit .depth) else scanDepths limits rest

/-- A bound on how deep any record within the byte limit can nest with its shares expanded:
two decoded nodes per byte at most (an application or binder telescope of `n` steps is written
with `n + 1` expressions), and an acyclic path meets each node once. -/
def expandedDepthBound (limits : Limits) : Nat := 2 * limits.maxRecordBytes + 2

/-- The expanded check declines a decoded record: the limit below `expandedDepthBound` and a
path past it. -/
def expandedFails (limits : Limits) (constant : Ixon.Constant) : Bool :=
  !(expandedDepthBound limits ≤ limits.maxDepth ||
    Depth.expandedWithin limits.maxDepth (8 * limits.maxRecordBytes + 16) constant)

/-- **The expanded-depth check**: every decoded record's expressions within
`limits.maxDepth` with their shares expanded, as the reader builds them
(`Depth.expandedWithin`). Not walked when the limit is at least twice the record byte limit and
two (`expandedDepthBound`): a decoded record has at most two nodes per byte that wrote it, and a
path through its shares meets each stored node at most once, so none is that deep. -/
def expandedDepths (limits : Limits) : Ingress.Constants → Except ByteError Unit
  | [] => .ok ()
  | (_, constant) :: rest =>
    if expandedFails limits constant then .error (.limit .depth) else expandedDepths limits rest

/-- The scan as one test over the records (`scanFails`), in any order: what a parallel scan
computes (`Ix.RoleBinding.RecordDecoding.scanDepthsParallel_eq`). -/
theorem scanDepths_eq_all (limits : Limits) : ∀ records : Records,
    scanDepths limits records =
      if records.all (fun p => !scanFails limits p.2) then .ok () else .error (.limit .depth)
  | [] => rfl
  | (_, b) :: rest => by
    rw [scanDepths, scanDepths_eq_all limits rest, List.all_cons]
    show (if scanFails limits b = true then _ else _) =
      (if (!scanFails limits b && rest.all fun p => !scanFails limits p.2) = true then _ else _)
    cases scanFails limits b <;> rfl

/-- The expanded check as one test over the records (`expandedFails`). -/
theorem expandedDepths_eq_all (limits : Limits) : ∀ constants : Ingress.Constants,
    expandedDepths limits constants =
      if constants.all (fun p => !expandedFails limits p.2) then .ok () else .error (.limit .depth)
  | [] => rfl
  | (_, c) :: rest => by
    rw [expandedDepths, expandedDepths_eq_all limits rest, List.all_cons]
    show (if expandedFails limits c = true then _ else _) =
      (if (!expandedFails limits c && rest.all fun p => !expandedFails limits p.2) = true then _ else _)
    cases expandedFails limits c <;> rfl

/-- **Decoding within the depth limit**: the stored-nesting scan, canonical
decoding (`decodeRecords`, its per-record limits reported as such: `ByteError.asLimit`), the
expanded-depth check. The entries decode with
it; its result is `decodeRecords`'s (`decodeWithin_decodeRecords`), and it fails where
`decodeRecords` fails or with `.limit .depth` (`decodeWithin_error`). -/
def decodeWithin (limits : Limits) (records : Records) : Except ByteError Ingress.Constants := do
  scanDepths limits records
  let constants ← (decodeRecords limits records).mapError ByteError.asLimit
  expandedDepths limits constants
  pure constants

end Ix.Kernel.Admission

end
