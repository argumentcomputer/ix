/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Admission.Bytes
import Ix.Ixon.ConLecheAdmission

/-! # Admission from ordered Ixon record bytes

The certified Ixon entry (plan v4, L5). This adapter lives outside the
checker: decoding and admission execute here; their composition with the
checker is proved in `Ix.Ixon.Consistency` (the public theorems) and
`Ix.Ixon.ConLecheConsistency` (the same theorems at every pin table and
prelude).

* `checkBytes` is the certified entry: batch limits and canonical decoding
  (`Ix.Ixon.Admission.Bytes`), then con-leche's verified checker behind the
  Ixon reader under the committed pin table and Ixon prelude
  (`Ix.Ixon.ConLecheAdmission.checkBytes`).
* The intrinsic kernel's byte admission (`checkBytesIntrinsic`, the
  certified entry through L4) was retired at L6 (plan v4) with the
  intrinsic kernel.

The host supplies record order, address keys, and literal blobs. Addresses
are keys, not authenticated content hashes. Blobs retain their exact supplied
bytes. No host decoder or verdict
participates in this path.
-/

namespace Ix.Ixon.Admission

open Kernel

/-- **The certified Ixon entry**: check exactly the declarations described by
the supplied canonical record bytes with con-leche's verified checker, after
the batch limits and canonical per-record decoding. `hint` is the host's
optional (untrusted) reducibility hint per constant. -/
def checkBytes (limits : Limits) (records : Records) (blobs : Ingress.Blobs)
    (hint : ConstRef Address → Option ConLeche.ReducibilityHint := fun _ => none) :
    Except ConLecheAdmission.Error ConLeche.Env :=
  ConLecheAdmission.checkBytes limits records blobs hint

/-- How an Ix caller classifies a failure of the certified entry (D-trust,
inventory section 3.7, rows 21-22; roadmap section 2, "Coverage and
rejection"): `reject` only where an independent check establishes that the
input is wrong (the batch limits are a coverage bound and decline; a
non-canonical record and a record the reader finds malformed reject); every
checker verdict declines, because con-leche reports fuel exhaustion as
`internal` and a failed conversion search as `invalid`, and neither is
evidence that the input is wrong. -/
inductive Outcome where
  | rejected
  | declined
  deriving Repr, DecidableEq

def outcome : ConLecheAdmission.Error → Outcome
  | .limit _ => .declined
  | .decode .. => .rejected
  | .prelude _ => .declined
  | .read _ (.malformed _) => .rejected
  | .read _ (.declined _) => .declined
  | .kernel _ _ => .declined

end Ix.Ixon.Admission
