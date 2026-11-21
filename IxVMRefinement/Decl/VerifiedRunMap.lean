import IxVMRefinement.Decl.JudgeMap
import IxVMRefinement.Assembly.RoleFacts
import IxC.Kernel.Model.JudgeRules
import IxC.Kernel.Verify.Rules.Bridge
import IxC.Kernel.Verify.Level

/-! # Verified checker runs as rules-tier judgements -/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model

/-- Every primitive judgement of a verified kernel run has a rules-tier derivation at the
same environment and terms. This discharges the map used by the inductive run translations. -/
theorem verifiedRunMap (fuel : Nat) :
    JudgementsMap (runJ (md := .anon) .verified fuel) rulesJ where
  annot h := Assembly.annotateCore_to_annot h
  infer h := Rules.inferTypeCore_bridge h
  defeq h := Rules.isDefEqCore_bridge h
  sort h := Rules.whnf_bridge (Ix.Kernel.ensureSortCore_inv h)
  isZero h := by
    intro φ
    simpa only [Level.eval] using Level.isEquiv_sound h φ

end IxVM.Refinement.Decl
