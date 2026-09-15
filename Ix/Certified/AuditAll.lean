/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.Audit
import Ix.Certified.TcAudit
import Ix.Certified.SourceAudit
import Ix.Certified.ClaimAudit
import Ix.Certified.ModeledAudit

/-! The union of the five historical adapter boundaries, without duplicate
root, premise or worker reports. Each component remains independently audited. -/

namespace Ix.Certified.AuditAll

def roots : Array Lean.Name := AuditSupport.distinct
  (Audit.roots ++ TcAudit.roots ++ SourceAudit.roots ++ ClaimAudit.roots ++ ModeledAudit.roots)

def premises : Array Lean.Name := AuditSupport.distinct
  (TcAudit.premises ++ SourceAudit.premises ++ ClaimAudit.premises ++ ModeledAudit.premises)

run_cmd AuditSupport.report "Certified host adapters" roots premises

end Ix.Certified.AuditAll
