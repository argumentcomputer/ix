/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.AuditSupport
import Ix.Certified.ClaimCommand
import Ix.Certified.Command

/-! Trust, runtime and premise inventory of the versioned semantic claim
checker, source command and actual TcM acceptance boundary. -/

open Lean Lean.Elab Command

namespace Ix.Certified.ModeledAudit

def roots : Array Lean.Name := #[
  `Ix.Theory.Certified.Modeled.check?_sound,
  `Ix.Theory.Certified.Modeled.checkEquation?_sound,
  `Ix.Theory.Certified.Modeled.assignment_realizes,
  `Ix.Theory.Certified.Modeled.assignment_agrees,
  `Ix.Theory.Certified.checkModeledExtension?,
  `Ix.Theory.Certificate.Modeled.witness?,
  `Ix.Theory.Certificate.sourceGroup?,
  `Ix.Theory.Certificate.proofWitness?,
  `Ix.Certified.modelCandidate?, `Ix.Certified.modelCandidates?,
  `Ix.Certified.ModelHint.readOptional, `Ix.Certified.ModelHint.read,
  `Ix.Certified.suggestSource?, `Ix.Certified.suggestStore?,
  `Ix.Certified.Command.readRequest, `Ix.Certified.Command.run_success,
  `Ix.Certified.suggestLogical?, `Ix.Certified.ClaimCommand.readRequest,
  `Ix.Certified.ClaimCommand.run_meaning,
  `Ix.Kernel.acceptsCertifiedSource, `Ix.Kernel.acceptsCertifiedStoreSource,
  `Ix.Kernel.accepted_tc_claim_meaning]

def premises : Array Lean.Name := #[
  `Ix.Certified.Protocol.current,
  `Ix.Certified.ModelHint.mk, `Ix.Certified.ModelRuleHints.mk,
  `Ix.Certified.ModelProofHint.mk,
  `Ix.Theory.Certificate.Modeled.Candidate.mk,
  `Ix.Theory.Certificate.Modeled.ProofHint.mk,
  `Ix.Theory.Certified.Modeled.Witness.mk,
  `Ix.Theory.Certified.Modeled.Checked.mk,
  `Ix.Theory.Certified.Modeled.SourceMatches,
  `Ix.Theory.Certified.Modeled.sourceRefs?,
  `Ix.Theory.Certified.Modeled.recursorSource?,
  `Ix.Theory.Certified.Modeled.majorSource?,
  `Ix.Theory.Certified.Modeled.ruleSource?,
  `Ix.Theory.Certified.Modeled.Companion.entry,
  `Ix.Theory.Certified.Modeled.CompanionChecked.mk,
  `Ix.Theory.Certified.Modeled.CheckedCompanions.mk,
  `Ix.Theory.Certified.Modeled.CheckedEquation.mk,
  `Ix.Theory.Certified.Modeled.checkEquation?]

run_cmd AuditSupport.report "modeled source" roots premises

end Ix.Certified.ModeledAudit
