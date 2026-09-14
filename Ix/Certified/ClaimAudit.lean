/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.AuditSupport
import Ix.Certified.ClaimCommand

/-! Trust, runtime and premise inventory of the versioned semantic claim
checker, source command and actual TcM acceptance boundary. -/

open Lean Lean.Elab Command

namespace Ix.Certified.ClaimAudit

def roots : Array Lean.Name := #[
  `Ix.Certified.TreeOpening.membership, `Ix.Certified.TreeOpening.unique,
  `Ix.Certified.treeLeaves_join, `Ix.Certified.EnvelopeReading.unique,
  `Ix.Certified.readEnvelope?, `Ix.Certified.readTree?,
  `Ix.Certified.LogicalChecking.original_subject, `Ix.Certified.LogicalChecking.original_frontier,
  `Ix.Certified.LogicalChecking.logical_policy, `Ix.Certified.LogicalChecking.closed_frontier,
  `Ix.Certified.LogicalReceipt.subject_meaning, `Ix.Certified.LogicalReceipt.closed_subject_meaning,
  `Ix.Certified.LogicalReceipt.no_False,
  `Ix.Certified.RevealReceipt.meaning, `Ix.Certified.ClaimReceipt.meaning,
  `Ix.Certified.accepted_claim_meaning, `Ix.Certified.evaluation_not_semantic,
  `Ix.Certified.membership_not_leaf, `Ix.Certified.revelation_not_leaf,
  `Ix.Kernel.TcM.checkClaimCertified_success,
  `Ix.Kernel.certifiedClaimStep_failure, `Ix.Kernel.certifiedClaimStep_success,
  `Ix.Kernel.accepted_tc_claim_meaning,
  `Ix.Certified.ClaimCommand.readRequest,
  `Ix.Certified.ClaimCommand.run_success, `Ix.Certified.ClaimCommand.run_meaning]

def premises : Array Lean.Name := #[
  `Ix.Certified.Protocol.current, `Ix.Certified.envelopeMagic,
  `Ix.Certified.putEnvelope, `Ix.Certified.getEnvelope,
  `Ix.Certified.EnvelopeReading.mk, `Ix.Certified.TreeOpening.mk,
  `Ix.Certified.OptionalTreeOpening.mk, `Ix.Certified.SubjectView.mk,
  `Ix.Certified.PreparedLeaf.mk, `Ix.Certified.ContentView.mk,
  `Ix.Certified.ownedReferences, `Ix.Certified.claimFrontier,
  `Ix.Certified.LogicalChecking.mk, `Ix.Certified.LogicalReceipt.mk,
  `Ix.Certified.SubjectsInterpreted, `Ix.Certified.LogicalMeaning,
  `Ix.Certified.RevealMatches, `Ix.Certified.ConstructorMatches,
  `Ix.Certified.ConstructorsMatch, `Ix.Certified.MutMatches,
  `Ix.Certified.ComponentsMatch, `Ix.Certified.RulesMatch,
  `Ix.Certified.RevealMeaning, `Ix.Certified.SemanticClaimMeaning]

run_cmd AuditSupport.report "claim meaning" roots premises

end Ix.Certified.ClaimAudit
