import IxVMRefinement.Decl.LateNatCtorT
import IxVMRefinement.Decl.LateNatRecCheck

/-! # The stored-type load witness under a second keying

The native recursor comparison of a late recursor reads the member's constructor loads under
two keyings: the prefix keying for the recursor's type, and the rule keying for its rules. The
load witness on the stored constructor types (`NatCtorLoadT`) moves from the first to any
keying that keeps every key the first resolves (`NatCtorLoadT.rekey_mono`). The comparison
itself is `late_nat_rec_check_spec_of_tele` (`LateNatRecCheckTele.lean`). -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (Expr Level LevelParam ConstantVal ConstantInfo RecRule Declaration)

set_option linter.unusedVariables false

/-- The stored-type load witness at member `idx` under a keying that keeps every key the first
resolves, when the member's constructor projections resolve under the first. -/
theorem NatCtorLoadT.rekey_mono {κ₁ κ₂ : _root_.Address → KKey} {b₀ : Bytes.Address}
    {idx k : Nat} {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)}
    {x_block : SourceValue F} {cs : List (Call F)}
    (hload : NatCtorLoadT κ₁ b₀ idx k ctors_info x_block cs)
    (keep : ∀ x, κ₁ x ≠ unresolvedKey → κ₂ x = κ₁ x)
    (hCres : ∀ i, i < ctors_info.length → κ₁ (cprjAddr (ixAddr b₀) idx i) ≠ unresolvedKey) :
    NatCtorLoadT κ₂ b₀ idx k ctors_info x_block cs := by
  intro j hj p9 hp m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50 hs hb ev ld info hinfo
  obtain ⟨h1, h2, hlt, h3⟩ :=
    hload j hj p9 hp m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50 hs hb ev ld info hinfo
  exact ⟨h1.trans (keep _ (hCres j hj)).symm, h2, hlt, h3.rekey_mono keep⟩

end IxVM.Refinement.Decl
