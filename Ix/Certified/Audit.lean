/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.AuditSupport
import Ix.Certified.Bytes

/-!
The serialized host adapter has its own audit. This is not the pure model's
import boundary or an Aiur compiler/AIR soundness theorem. Foreign hashing and
its output contract remain explicit runtime dependencies.
-/

open Lean Lean.Elab Command

namespace Ix.Certified.Audit

def roots : Array Lean.Name := #[
  `Ix.Certified.decodeObject?, `Ix.Certified.decodeNatural?,
  `Ix.Certified.readSignature?, `Ix.Certified.prepare?,
  `Ix.Certified.acceptsSerialized_prepared,
  `Ix.Certified.accepted_serialized_has_model,
  `Ix.Certified.no_serialized_proof_of_False]

run_cmd AuditSupport.report "serialized" roots #[]

end Ix.Certified.Audit
