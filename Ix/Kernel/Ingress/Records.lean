/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Types

/-! # The decoded-record store of the Ixon ingress

Decoded records (`Constants`) and literal blobs (`Blobs`) as the host supplies
them, keyed by address and in order, with the lookups the certified entries
use: first-match `lookup`, the projection test, the empty-table test of a
projection record, and the little-endian value of a natural-number blob.

These definitions were part of the intrinsic kernel's ingress
(`Ix/Kernel/Ingress/Reading.lean`), which L6 (plan v4) retired with that
kernel. They are kept unchanged, under their names, so that the certified
statements that mention them (`Ix.Ixon.Admission.checkBytes_*`,
`Ix.Ixon.Projection.*`, `Ix.Ixon.BlockOrder.*`) did not change. -/

namespace Ix.Kernel.Ingress

abbrev Constants := List (Address × Ixon.Constant)
abbrev Blobs := List (Address × ByteArray)

def isProjection : Ixon.ConstantInfo → Bool
  | .dPrj _ | .iPrj _ | .rPrj _ | .cPrj _ => true
  | _ => false

/-- First lookup in the supplied finite store. -/
def lookup (store : List (Address × α)) (address : Address) : Option α :=
  match store with
  | [] => none
  | (key, value) :: rest => if key = address then some value else lookup rest address

/-- Little-endian natural-number payload, including the empty encoding of zero.
Canonical byte spelling is a separate condition (the canonical decoder). -/
def natural (bytes : ByteArray) : Nat :=
  bytes.data.toList.foldr (fun byte rest => byte.toNat + 256 * rest) 0

/-- A projection constant carries no expression tables. -/
def emptyTables (source : Ixon.Constant) : Bool :=
  source.sharing.isEmpty && source.refs.isEmpty && source.univs.isEmpty

end Ix.Kernel.Ingress
