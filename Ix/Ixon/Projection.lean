import IxC.Ixon.Codec
import IxC.Kernel.Admission
import IxC.Kernel.Egress.Projection

/-! Projection reconstruction outside the hash-free kernel.

Projection records are derived from physical mutual blocks, using the same
variant/member/constructor positions as production ingress. Their keys are
the content hash `hash` of the complete production serialization, the same
hash the entry authenticates the supplied records with; the root library
instantiates it at BLAKE3 (`Ixon.Authenticated`). Existing records are
retained exactly; a conflicting payload at a generated key is an error, so no
collision assumption is needed to extend the supplied store.
-/

namespace Ixon.Projection

open Ix.Kernel

structure Request where
  layout : Egress.ProjectionLayout
  reference : ConstRef Address
  deriving DecidableEq

/-- Member positions, followed by constructor positions for inductives.
Standalone definitions and recursors already use their primary address. -/
def memberRequests (owner : Address) (index : Nat) : Ixon.MutConst → List Request
  | .defn _ => [⟨.definition, .member owner index⟩]
  | .recr _ => [⟨.recursor, .member owner index⟩]
  | .indc source => ⟨.inductive, .member owner index⟩ ::
      source.ctors.toList.zipIdx.map (fun (_, ctor) => ⟨.constructor, .ctor owner index ctor⟩)

def requests (constants : Ingress.Constants) : List Request :=
  constants.flatMap fun (owner, source) =>
    match source.info with
    | .muts members => members.toList.zipIdx.flatMap fun (member, index) =>
        memberRequests owner index member
    | _ => []

def primaries (constants : Ingress.Constants) : Ingress.Constants :=
  constants.filter fun pair => !Ingress.isProjection pair.2.info

/-- A record's address: `hash` of its complete serialization, as for a
supplied record. -/
def address (hash : ByteArray → Address) (record : Ixon.Constant) : Address :=
  hash (Ixon.serConstant record)

/-- Compare only exact projection records, including their empty tables.
This avoids evaluating structural equality on unrelated declaration trees. -/
def matchesRecord (request : Request) (record : Ixon.Constant) : Bool :=
  match Egress.readProjection record with
  | .ok (layout, reference) => decide (layout = request.layout ∧ reference = request.reference)
  | .error _ => false

inductive Error where
  | limit
  | ownerWidth (owner : Address)
  | projection (reason : SearchFailure)
  | conflict (address : Address)
  | admission (reason : Admission.ByteError)
  deriving DecidableEq, Repr

/-- Reserve one request before writing or hashing it. Existing identical
records spend a request too. Newly derived projections precede the input;
the relative order and fields of primary declarations are preserved. -/
def reconstructLoop (hash : ByteArray → Address) :
    Nat → List Request → Ingress.Constants → Except Error Ingress.Constants
  | _, [], constants => .ok constants
  | 0, _ :: _, _ => .error .limit
  | remaining + 1, request :: rest, constants => do
    if request.reference.block.hash.size != 32 then
      throw (.ownerWidth request.reference.block)
    let record ← (Egress.writeProjection request.layout request.reference).mapError .projection
    let key := address hash record
    match Ingress.lookup constants key with
    | some existing =>
      if matchesRecord request existing then reconstructLoop hash remaining rest constants
      else throw (.conflict key)
    | none => reconstructLoop hash remaining rest ((key, record) :: constants)

/-- Reconstruct every member and constructor projection from the supplied
physical blocks, under `hash`. `maxProjections` bounds requests, including
reused records. The final kernel admission validates owners and constructor
metadata. -/
def reconstruct (hash : ByteArray → Address) (maxProjections : Nat) (constants : Ingress.Constants) :
    Except Error Ingress.Constants :=
  reconstructLoop hash maxProjections (requests constants) constants

/-- Failures of the certified entry: byte admission and reconstruction
(`Error`), or the checker (`Admission.Error`). -/
inductive CheckError where
  | reconstruction (error : Error)
  | checker (error : Admission.Error)

/-- How an Ix caller classifies a reconstruction failure, as
`Admission.Error.outcome` does the entry's (`docs/kernel.md`, "Outcomes"):
the request bound is a coverage bound and declines; an owner key that is
not a 32-byte hash, a projection the writer finds malformed and a supplied
record that conflicts with a derived one at its key reject; any other
writer failure declines; the byte stage as `Admission.ByteError.outcome`. -/
def Error.outcome : Error → Admission.Outcome
  | .limit => .declined
  | .ownerWidth _ => .rejected
  | .projection (.malformed _) => .rejected
  | .projection _ => .declined
  | .conflict _ => .rejected
  | .admission error => error.outcome

/-- The classification of a failure of `checkBytes` (call it as
`e.outcome`): reconstruction as `Error.outcome`, the checker as
`Admission.Error.outcome`. -/
def CheckError.outcome : CheckError → Admission.Outcome
  | .reconstruction error => error.outcome
  | .checker error => error.outcome

/-- **The certified entry with optional omission of projection records**:
canonical byte admission, projection reconstruction, then the
verified checker behind the Ixon reader under the role table's section
(`Admission.checkConstantsAt`: the table admitted under `hash`, then
`Admission.checkConstants`) on the expanded records. Input byte limits, key uniqueness and
authentication apply before reconstruction: every supplied record and blob
is stored under `hash` of its bytes, and every reconstructed projection under
`hash` of its serialization. The separate projection limit bounds generated
requests. -/
def checkBytes (hash : ByteArray → Address) (binding : Admission.Binding) (maxProjections : Nat)
    (limits : Admission.Limits) (records : Admission.Records) (blobs : Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except CheckError Ix.Kernel.Env := do
  (Admission.preflight limits records blobs).mapError (fun error => .reconstruction (.admission error))
  (Admission.uniqueKeys records blobs).mapError (fun error => .reconstruction (.admission error))
  (Admission.authenticate hash records blobs).mapError (fun error => .reconstruction (.admission error))
  let constants ← (Admission.decodeRecords limits records).mapError
    (fun error => .reconstruction (.admission error))
  let expanded ← (reconstruct hash maxProjections constants).mapError .reconstruction
  (Admission.checkConstantsAt hash binding expanded blobs hint).mapError .checker

end Ixon.Projection
