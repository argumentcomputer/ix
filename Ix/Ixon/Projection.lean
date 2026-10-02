import Ix.Address.Pure
import IxKernel.Ixon.Codec
import IxKernel.Kernel.Admission
import IxKernel.Kernel.Egress.Projection

/-! Pure projection reconstruction outside the hash-free kernel.

Projection records are derived from physical mutual blocks, using the same
variant/member/constructor positions as production ingress. Their keys are
the pure BLAKE3 hash of the complete production serialization. Existing
records are retained exactly; a conflicting payload at a generated key is
an error, so no collision assumption is needed to extend the supplied store.
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

/-- The address is a theorem-level computation, not a host hash result. -/
def address (record : Ixon.Constant) : Address :=
  Address.blake3Pure (Ixon.serConstant record)

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
def reconstructLoop : Nat → List Request → Ingress.Constants → Except Error Ingress.Constants
  | _, [], constants => .ok constants
  | 0, _ :: _, _ => .error .limit
  | remaining + 1, request :: rest, constants => do
    if request.reference.block.hash.size != 32 then
      throw (.ownerWidth request.reference.block)
    let record ← (Egress.writeProjection request.layout request.reference).mapError .projection
    let key := address record
    match Ingress.lookup constants key with
    | some existing =>
      if matchesRecord request existing then reconstructLoop remaining rest constants
      else throw (.conflict key)
    | none => reconstructLoop remaining rest ((key, record) :: constants)

/-- Reconstruct every member and constructor projection from the supplied
physical blocks. `maxProjections` bounds requests, including reused records.
The final kernel admission validates owners and constructor metadata. -/
def reconstruct (maxProjections : Nat) (constants : Ingress.Constants) :
    Except Error Ingress.Constants :=
  reconstructLoop maxProjections (requests constants) constants

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
verified checker behind the Ixon reader (`Admission.checkConstants`)
on the expanded records. Input byte limits and key uniqueness apply before
reconstruction; the separate projection limit bounds generated requests. Owner keys remain
supplied keys: only derived projection addresses are authenticated here. -/
def checkBytes (maxProjections : Nat) (limits : Admission.Limits) (records : Admission.Records)
    (blobs : Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except CheckError Ix.Kernel.Env := do
  (Admission.preflight limits records blobs).mapError (fun error => .reconstruction (.admission error))
  (Admission.uniqueKeys records blobs).mapError (fun error => .reconstruction (.admission error))
  let constants ← (Admission.decodeRecords limits records).mapError
    (fun error => .reconstruction (.admission error))
  let expanded ← (reconstruct maxProjections constants).mapError .reconstruction
  (Admission.checkConstants expanded blobs hint).mapError .checker

end Ixon.Projection
