/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Address.Pure
import Ix.Ixon.Codec
import Ix.Ixon.Admission
import Ix.Kernel.Egress.Projection

/-! Pure projection reconstruction outside the hash-free kernel.

Projection records are derived from physical mutual blocks, using the same
variant/member/constructor positions as production ingress. Their keys are
the pure BLAKE3 hash of the complete production serialization. Existing
records are retained exactly; a conflicting payload at a generated key is
an error, so no collision assumption is needed to extend the supplied store.
-/

namespace Ix.Ixon.Projection

open Kernel

structure Request where
  layout : Egress.ProjectionLayout
  reference : ConstRef Address
  deriving DecidableEq

/-- Member positions, followed by constructor positions for inductives.
Standalone definitions and recursors already use their primary address. -/
def memberRequests (owner : Address) (index : Nat) : _root_.Ixon.MutConst → List Request
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
def address (record : _root_.Ixon.Constant) : Address :=
  Address.blake3Pure (_root_.Ixon.serConstant record)

/-- Compare only exact projection records, including their empty tables.
This avoids evaluating structural equality on unrelated declaration trees. -/
def matchesRecord (request : Request) (record : _root_.Ixon.Constant) : Bool :=
  match Egress.readProjection record with
  | .ok (layout, reference) => decide (layout = request.layout ∧ reference = request.reference)
  | .error _ => false

inductive Error where
  | limit
  | ownerWidth (owner : Address)
  | projection (reason : SearchFailure)
  | conflict (address : Address)
  | admission (reason : Admission.Error)
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

universe v

/-- Canonical byte admission with optional omission of projection records.
Input byte limits apply before reconstruction; the separate projection limit
bounds generated requests. Owner keys remain supplied keys: only derived
projection addresses are authenticated here. -/
def checkBytes (maxProjections : Nat) (limits : Admission.Limits) (cfg : Config)
    (records : Admission.Records) (blobs : Ingress.Blobs)
    (family : Option (ConstRef Address) := none) : Except Error (Env Address) := do
  (Admission.preflight limits records blobs).mapError .admission
  let constants ← (Admission.decodeRecords limits records).mapError .admission
  let expanded ← reconstruct maxProjections constants
  (Kernel.checkEnv.{v} cfg expanded blobs family).mapError (fun error => .admission (.kernel error))

end Ix.Ixon.Projection
