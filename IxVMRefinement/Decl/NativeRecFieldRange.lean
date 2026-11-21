import IxVMRefinement.Decl.NativeRec
import IxVMRefinement.Callees.ProjAddr
import IxVMRefinement.Core.Certs
import IxVMRefinement.Assembly.GuardHeadRep

/-! # Two specifications at counts in the field's range, beside `Decl/NativeRec.lean`

`Decl/NativeRec.lean` holds the native recursor's generators at the counts an accepted run
gives (its section "The generators at counts in the field's range"). Two lemmas of the same
kind read functions specified elsewhere and stay here:

* `peel_n_foralls_tm_bounded`: `peel_n_foralls` on a `Tm` term, for any count below the
  field's modulus;
* `projection_addr_ctor_bounded`: the address of a constructor projection, at member and
  constructor indices below the modulus.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (ConstantInfo ConstantVal Declaration Expr Level LevelParam RecRule)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ## The loop counters -/

/-- `KernelCheck::peel_n_foralls` on a `Tm` expression strips `n` leading `∀`-binders, for any
count in the field's range. -/
theorem peel_n_foralls_tm_bounded {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (n : Nat) {k : Nat} {E : KExpr} {pe r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 18446744069414584321 →
      Tm κ d Γ h k E pe →
      ObsFn W "KernelCheck::peel_n_foralls" [pe, .field (n : F)] h r h' cs →
      h' = h ∧ ∃ bs body,
        E.stripPis n = some (bs, body) ∧ bs.length = n ∧ Tm κ d Γ h (k + n) body r
  | 0, k, E, pe, r, h, h', cs, _, hE, ev => by
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with
      ⟨_, rfl, rfl, _⟩ | ⟨_, _, _, _, _, hne, _, _, _, _⟩
    · exact ⟨rfl, [], E, rfl, rfl, by simpa using hE⟩
    · exact absurd rfl hne
  | m + 1, k, E, pe, r, h, h', cs, hlt, hE, ev => by
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with
      ⟨hv, _, _, _⟩ | ⟨w42, x_body, w43, cs62, v66, _, ld34, op87, ev64, _⟩
    · exact absurd hv (succ_field_ne_zero_bounded hlt)
    · obtain ⟨T, B, ℓ, rfl, _, hb, _⟩ := hE.forallE_of_load ld34
      rw [evalBinOp_sub_succ m op87] at ev64
      obtain ⟨hh, bs, body, hstrip, hlen, hbody⟩ :=
        peel_n_foralls_tm_bounded m (by omega) hb ev64
      refine ⟨hh, (T, bmeta ℓ) :: bs, body, ?_, by simp [hlen], ?_⟩
      · simp [Expr.stripPis, hstrip]
      · rw [show k + (m + 1) = k + 1 + m by omega]
        exact hbody

/-! ## The address of a constructor projection -/

/-- `KernelCheck::projection_addr_ctor` at member and constructor indices in the field's range
(the function itself range-checks both with `UInt64::from_field`). -/
theorem projection_addr_ctor_bounded {c : Ctx} {bp r : SourceValue F} {b : Bytes.Address}
    {idx cidx : Nat} {h h' : Heap F} {cs : List (Call F)}
    (hidx : idx < 18446744069414584321) (hcidx : cidx < 18446744069414584321)
    (hb : Bytes.RepAddressRef addrTy h b bp)
    (hgood : Good c cs)
    (ev : ObsFn W "KernelCheck::projection_addr_ctor"
      [.field (idx : F), .field (cidx : F), bp] h r h' cs) :
    ∃ a : Bytes.Address, Bytes.RepAddressRef addrTy h' a r ∧
      ixAddr a = cprjAddr (ixAddr b) idx cidx := by
  have hval_idx : ZMod.val (idx : F) = idx := ZMod.val_natCast_of_lt hidx
  have hval_cidx : ZMod.val (cidx : F) = cidx := ZMod.val_natCast_of_lt hcidx
  obtain ⟨a, ha, haddr⟩ := projection_addr_ctor_step (ScopedCtx.unrestricted c) ev
    (idx : F) (cidx : F) bp b rfl (CoreGood.unrestricted hgood) hb
  rw [hval_idx, hval_cidx] at haddr
  exact ⟨a, ha, haddr⟩

end IxVM.Refinement.Decl
