/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.AuditSupport
import Ix.Kernel.Certified
import Ix.Certified.Command

/-! This audit covers the actual TcM certified entry points, the decoder
cache and source receipts. It does not promote legacy TcM successes. -/

open Lean Lean.Elab Command

namespace Ix.Certified.TcAudit

def roots : Array Lean.Name := #[
  `Ix.Certified.constantBytes?, `Ix.Certified.decodeObject_complete,
  `Ix.Certified.decodeNatural_complete,
  `Ix.Certified.SourceSnapshot.prepare_eq, `Ix.Certified.SourceSnapshot.prepareStore_eq,
  `Ix.Certified.SourceSnapshot.objects_from_source, `Ix.Certified.SourceSnapshot.naturals_from_source,
  `Ix.Certified.SourceReceipt.serialized, `Ix.Certified.StoreReceipt.serialized,
  `Ix.Certified.accepted_serialized_store_has_model,
  `Ix.Kernel.TcM.checkCertified_success, `Ix.Kernel.TcM.checkCertified_failure,
  `Ix.Kernel.TcM.checkStoreCertified_success,
  `Ix.Kernel.certifiedStep_success, `Ix.Kernel.certifiedStep_failure,
  `Ix.Kernel.certifiedStoreStep_success, `Ix.Kernel.certifiedStoreStep_failure,
  `Ix.Kernel.initialCertifiedState, `Ix.Kernel.accepted_tc_has_model,
  `Ix.Kernel.accepted_tc_store_has_model, `Ix.Kernel.no_tc_proof_of_False,
  `Ix.Certified.Command.run_success]

def premises : Array Lean.Name := #[
  `Ix.Certified.InputCache.mk, `Ix.Certified.CachedObject.mk, `Ix.Certified.CachedNatural.mk,
  `Ix.Certified.DecodedObject, `Ix.Certified.DecodedNatural,
  `Ix.Certified.SourceObject.mk, `Ix.Certified.SourceNatural.mk,
  `Ix.Certified.SourceReceipt.mk, `Ix.Certified.StoreReceipt.mk,
  `Ix.Certified.InputSelection.mk, `Ix.Certified.subjectReferences?,
  `Ix.Kernel.CertifiedState.mk]

run_cmd AuditSupport.report "certified checker" roots premises

end Ix.Certified.TcAudit
