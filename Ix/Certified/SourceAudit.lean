/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.AuditSupport
import Ix.Certified.SourceMeaning

/-! The source audit freezes original expression/statement meaning and
its connection to the actual canonical source bytes. Claim composition and
backend execution are audited by their separate roots when connected. -/

open Lean Lean.Elab Command

namespace Ix.Certified.SourceAudit

def roots : Array Lean.Name := #[
  `Ix.Certified.resolveReference_iff, `Ix.Certified.readLevel_value,
  `Ix.Certified.readExpr_sound, `Ix.Certified.ExprReading.unique,
  `Ix.Certified.readExpr_fuel_independent,
  `Ix.Certified.readBlock_sourceHeader, `Ix.Certified.readStore_sourceHeader,
  `Ix.Certified.SourceSnapshot.object_bytes, `Ix.Certified.SourceSnapshot.natural_bytes,
  `Ix.Certified.readSignature_sound,
  `Ix.Certified.StoreReceipt.subject_meaning, `Ix.Certified.SourceReceipt.proposition_meaning,
  `Ix.Certified.StoreReceipt.subject_coverage]

def premises : Array Lean.Name := #[
  `Ix.Certified.MemberMeaning, `Ix.Certified.ReferenceTarget, `Ix.Certified.ReferenceMeaning,
  `Ix.Certified.LevelsReading.nil, `Ix.Certified.LevelsReading.cons,
  `Ix.Certified.ExprReading.var, `Ix.Certified.ExprReading.sort, `Ix.Certified.ExprReading.ref,
  `Ix.Certified.ExprReading.recur, `Ix.Certified.ExprReading.app, `Ix.Certified.ExprReading.lam,
  `Ix.Certified.ExprReading.all, `Ix.Certified.ExprReading.prj, `Ix.Certified.ExprReading.nat,
  `Ix.Certified.ExprReading.share, `Ix.Certified.rawHeader?,
  `Ix.Certified.ObjectBytes, `Ix.Certified.NaturalBytes,
  `Ix.Certified.SignatureReading, `Ix.Certified.SourceDeclarationReading, `Ix.Certified.SubjectReading]

run_cmd AuditSupport.report "source meaning" roots premises

end Ix.Certified.SourceAudit
