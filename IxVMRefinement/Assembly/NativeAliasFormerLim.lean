import IxVMRefinement.Assembly.NativeAliasFormer
import IxVMRefinement.Assembly.NativeBlockReadsLim

/-! # A block whose former is declared at a definition is recognised, at either role context

`nativePartsAt_of_member_lim`: `nativePartsAt_of_member` for a member check under the role
context of either validator (`Claim.MemberCheckedLimAt … lim`), with the same proof over the
block's readings at either context (`Assembly/NativeBlockReadsLim.lean`).
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Model (nativePartsAt?)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u

section Recognise

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E₀ : Ixon.Env}
  {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive} {lim : Option Nat}

/-- **The declared block is recognised at the record's index count**, at a former declared at a
definition, with distinct constructor names; the recognised index count is the record's. -/
theorem nativePartsAt_of_member_lim (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim)
    (halias : FormerAtAlias t E₀ B cb ind) {blk : List (ConstantInfo .anon)}
    (hblk : BlockReadings t E₀ B ind blk)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x)) :
    ∃ p₀, nativePartsAt? ind.params.toNat ind.indices.toNat blk = some p₀ ∧
      (p₀.ctors.map (·.1.name)).Nodup ∧ p₀.nIdx = ind.indices.toNat := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  obtain ⟨ty₀, caps, cs, rfl, hty, hlen, hcs⟩ := blockReads_shape_lim ht hbound hS hrec hchk hblk
  have hal := halias ty₀ hty
  have hfreeF : Decl.KeyFree (keyOf t (memberAddr B 0 (.indc ind))) :=
    hfree _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)
  have hfreeC : ∀ j, j < ind.ctors.size → Decl.KeyFree (keyOf t (ctorAddr B 0 j)) :=
    fun j hj => hfree _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inr ⟨ind, j, rfl, hj, rfl⟩⟩)
  have hlt : ∀ j c, cs[j]? = some c → j < ind.ctors.size := by
    intro j c hc
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hc).1
  obtain ⟨p₀, hp₀⟩ := nativePartsAt?_isSome (nIdx := ind.indices.toNat) (caps := caps) (cs := cs)
    (cvT := ⟨keyOf t (memberAddr B 0 (.indc ind)), List.range ind.lvls.toNat, ty₀⟩) hal
    hfreeF.1 (by
      intro c hc
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
      obtain ⟨ct, tyj, -, -, hl, hp, -, rfl, -⟩ := hcs j c hj
      exact ⟨_, _, by rw [hp], by simp [hl], (hfreeC j (hlt j _ hj)).1⟩)
  obtain ⟨caps₀, hshape, -, -, -, -, hnIdx⟩ := nativePartsAt?_inv hp₀
  injection hshape with hhead hcs'
  injection hhead with hcv _
  refine ⟨p₀, hp₀, ?_, hnIdx (by rw [← hcv]; exact hal)⟩
  have hnames : p₀.ctors.map (·.1.name) = cs.map (·.name) := by
    rw [hcs', List.map_map]
    rfl
  rw [hnames]
  obtain ⟨-, -, -, -, hnc, -⟩ := ctorSlots_of_member_lim hbound hS hrec hchk
  have hjb : ∀ {j}, j < ind.ctors.size → j < UInt64.size := fun hj => by
    show _ < 18446744073709551616
    omega
  refine nodup_names_of_index (f := fun j => keyOf t (ctorAddr B 0 j)) (fun j c hc => ?_)
    (fun j j' hj hj' e => ctorAddr_inj hrec hjb j j' (by omega) (by omega)
      (Core.keyOf_inj (a₁ := ctorAddr B 0 j) (a₂ := ctorAddr B 0 j') htwf e))
  obtain ⟨ct, tyj, -, -, -, -, -, rfl, -⟩ := hcs j c hc
  rfl

end Recognise

end IxVM.Refinement.Typing
