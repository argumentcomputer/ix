import IxVMRefinement.Binding.ClosureFold
import IxVMRefinement.Binding.StoreClausesWalk
import IxVMRefinement.Binding.BasisAt
import IxVMRefinement.RoleVal.GroupAdmit
import IxVMRefinement.Claim.TopProj
import IxVM.Obs.KernelRoles

/-! # Literal anchors are never inductive projections (`ClosureRunFacts.literals`)

`KernelRoles::validate_anchor` asserts `KernelRoles::anchor_kind_ok(r, ci) = 1`, which requires
`List.nil` and `List.cons` (role indices 30 and 31) to load as `KConstantInfo::Ctor` and
`String.ofList` and `Char.ofNat` (role indices 38 and 40) to load as `KConstantInfo::Defn`.
An inductive projection record (`Ixon.ConstantInfo.iPrj`) loads via `Ingress::get_ci` as
`KConstantInfo::Induct` (`Claim.GetCIHead.iPrj`), which is neither `Ctor` nor `Defn`.
Therefore the key of the member of a single-inductive block is never one of the four literal
support names (`literals_of_run`). -/

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **`KernelRoles::anchor_kind_ok` returning `1`** forces the loaded constant to be `Ctor` for
roles 30 and 31 (`List.nil`, `List.cons`) and `Defn` for roles 38 and 40 (`String.ofList`,
`Char.ofNat`). -/
private theorem anchor_kind_ok_not_induct {k : F} {v : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (hk : k = 30 ∨ k = 31 ∨ k = 38 ∨ k = 40)
    (ev : ObsFn Obs.W "KernelRoles::anchor_kind_ok" [.field k, v] h (.field 1) h' cs)
    {args : List (SourceValue F)}
    (hv : v = .construct "KernelTypes::KConstantInfo" "Induct" args) : False := by
  subst hv
  match Obs.«KernelRoles::anchor_kind_ok».obs ev with
  | .n30 (sg_velmfrir := sg) (he_xeykxhlo := he) ..
  | .n31 (sg_velmfrir := sg) (he_sxwtxnmc := he) .. =>
    cases sg with
    | Ctor _ _ _ _ _ _ _ _ hv' _ _ _ =>
      exact absurd (Value.construct.inj hv').2.1 (by decide)
    | other _ he0 _ _ =>
      rw [he0] at he
      exact absurd (Value.field.inj he) one_ne_zero
  | .n38 (sg_abgsitku := sg) (he_cqnyfhye := he) ..
  | .n40 (sg_abgsitku := sg) (he_iqfjvdhm := he) .. =>
    cases sg with
    | Defn _ _ _ _ _ hv' _ _ _ =>
      exact absurd (Value.construct.inj hv').2.1 (by decide)
    | other _ he0 _ _ =>
      rw [he0] at he
      exact absurd (Value.field.inj he) one_ne_zero
  | .other (hne_qbrqficx := h30) (hne_whbdvark := h31) (hne_dxmrrfvb := h38)
      (hne_fmpbplsa := h40) .. =>
    rcases hk with rfl | rfl | rfl | rfl
    · exact h30 rfl
    · exact h31 rfl
    · exact h38 rfl
    · exact h40 rfl

/-- **None of the four literal-support anchor roles is bound to an inductive projection record.** -/
theorem validateRole_literal_not_iPrj {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {r : Ix.Kernel.Role} (hr : r = .stringOfList ∨ r = .listNil ∨ r = .listCons ∨ r = .charOfNat)
    (hv : RoleValidationIn calls bAddr t (Ix.SpecDigest.groupOf r) r)
    {a : _root_.Address} (had : t.addressOf? r = some a)
    {c : Ixon.Constant} (hc : recordOf E₀ a = some c) {p : Ixon.InductiveProj}
    (hp : c.info = .iPrj p) : False := by
  have hsk1 : RoleVal.roleSpecKindNat r = 1 := by
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  have hk : Core.roleNum r = 30 ∨ Core.roleNum r = 31 ∨ Core.roleNum r = 38 ∨
      Core.roleNum r = 40 := by
    rcases hr with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl (by decide)))
    · exact Or.inl (by decide)
    · exact Or.inr (Or.inl (by decide))
    · exact Or.inr (Or.inr (Or.inr (by decide)))
  obtain ⟨h, h', x_rc, x_tbl, res, cs, -, htbl, ev, hsub⟩ := hv
  match Obs.«KernelRoles::validate_role».obs ev with
  | .n0 (ev124 := ev124) .. | .n2 (ev124 := ev124) .. | .n3 (ev124 := ev124) ..
  | .n4 (ev124 := ev124) .. | .n5 (ev124 := ev124) .. =>
    obtain ⟨hsk, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [hsk1] at hsk
    exact absurd (Value.field.inj hsk) (by decide)
  | .n1 (v1 := v1) (m2 := m2) (v31 := v31) (m32 := m32) (p39 := p39) (cs45 := cs45)
      (ev14 := ev14) (ev47 := ev47) (ld41 := ld41) (ev194 := ev194) (hc227 := hc227) .. =>
    obtain ⟨-, a', ⟨ab, hab, rfl⟩, had'⟩ := RoleVal.role_bound_addr_uncond htbl.toTableRep ev14
    have ea : Core.ixAddr ab = a := Option.some.inj (had'.symm.trans had)
    rw [← ea] at hc
    have hsub45 : ∀ cl ∈ cs45, cl ∈ calls :=
      fun cl hcl => hsub cl (by rw [hc227]; simp [hcl])
    obtain ⟨raw, c', -, hh, hba, hde, -, hhead⟩ := Claim.get_ci_head hab ev47
    have hcc : c' = c := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc)
      (Core.hashed_mono hsub45 hh) hba hde
    subst hcc
    obtain ⟨_, _, _, _, _, _, nl, ty, np, ni, x_blk, b, hld_ind, -, -⟩ :=
      hhead.iPrj p.idx p.block hp
    have hv31 : v31 = .construct "KernelTypes::KConstantInfo" "Induct"
        [nl, ty, np, ni, _, _, x_blk, _] := Except.ok.inj (ld41.symm.trans hld_ind)
    match Obs.«KernelRoles::validate_anchor».obs ev194 with
    | .n1 (ev_sdakvhwc := evk) (heq_ovguopqr := heq1) ..
    | .other (ev_sdakvhwc := evk) (heq_ovguopqr := heq1) .. =>
      rw [heq1] at evk
      exact anchor_kind_ok_not_induct hk evk hv31

/-- **`ClosureRunFacts.literals` of every run**: the key of the member of a plain unit that is a
single-inductive block is never one of the four literal-support anchor names, because each of
those roles was validated by `KernelRoles::validate_anchor`, which rejects inductive projections
via `KernelRoles::anchor_kind_ok`. -/
theorem literals_of_run {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {Pay : PayloadRel}
    (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀) (hcheck : t.check = .ok ())
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    {g : Nat} (hg6 : 6 ≤ g)
    (hcl : UsedClosed (groupStore t E₀ Pay (g + 1)))
    {famOf : _root_.Address → Option _root_.Address} :
    ∀ A c ind, PlainUnitAt t g (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) famOf A c →
      c.info = .muts #[.indc ind] →
      keyOf t (memberAddr A 0 (.indc ind)) ≠ Ix.Kernel.stringOfListName ∧
      keyOf t (memberAddr A 0 (.indc ind)) ≠ Ix.Kernel.listNilName ∧
      keyOf t (memberAddr A 0 (.indc ind)) ≠ Ix.Kernel.listConsName ∧
      keyOf t (memberAddr A 0 (.indc ind)) ≠ Ix.Kernel.charOfNatName := by
  intro A c ind hplain hmuts
  have hmemR' : recordOf (groupStore t E₀ Pay (g + 1)) (memberAddr A 0 (.indc ind)) =
      some (memberProjection A 0 (.indc ind)) :=
    (hcl.2 A c #[.indc ind] hplain.2.1 hmuts 0 (.indc ind) rfl).1
  have hmemE : recordOf E₀ (memberAddr A 0 (.indc ind)) =
      some (memberProjection A 0 (.indc ind)) :=
    ((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hmemR').2
  have hne : ∀ r : Ix.Kernel.Role,
      (r = .stringOfList ∨ r = .listNil ∨ r = .listCons ∨ r = .charOfNat) →
      keyOf t (memberAddr A 0 (.indc ind)) ≠ Ix.Kernel.roleKey r := by
    intro r hr hk
    have had : t.addressOf? r = some (memberAddr A 0 (.indc ind)) :=
      Core.addressOf_of_keyOf (wf_of_check hcheck) (by rw [LoadedReads.keyOf_eq]; exact hk)
    exact validateRole_literal_not_iPrj hC.runStore hr
      (hvalAll _ r (role_mem_roleGroup r)) had hmemE rfl
  exact ⟨hne .stringOfList (Or.inl rfl),
    hne .listNil (Or.inr (Or.inl rfl)),
    hne .listCons (Or.inr (Or.inr (Or.inl rfl))),
    hne .charOfNat (Or.inr (Or.inr (Or.inr rfl)))⟩

end IxVM.Refinement.Binding
