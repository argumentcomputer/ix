import IxVMRefinement.FamilyGraph.AdviceChecked
import IxVMRefinement.Claim.TopProj

/-! # The checks a family check runs on its inner records, beyond one-constant advice

`Decl.adviceRecord_checked` reads an advice record that declares one constant. This module reads
the other records a family check checks itself:

* `containerRec_checked`: an observed `check_container_rec [rc, x, iblock]` ran `run_check(rc, x)`,
  so the record at `x` is checked at the limit of `rc` (`Claim.CheckedLimAt`); and the record is
  no block (`rec_family_block` reads it with `Ingress::get_ci`, which returns no block record);
* `adviceBlock_checked`: an observed `check_advice_record [rc, a, aset, wset]` at a block record
  ran `check_muts_all(rc, a, members, members, 0)`, so every member is checked at the limit of
  `rc` (`Claim.MemberCheckedLimAt`), and the dispatch answered `0` on the block
  (`Claim.NativeObsAt`). -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Library Aiur.Library.List Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- A member represented in full is represented by kind. -/
theorem mutShape_of_repMutConst {h : Heap F} {m : Ixon.MutConst} {v : SourceValue F}
    (hr : L1.RepMutConst h m v) : Specs.Callees.MutShape h m v := by
  cases m with
  | defn d => obtain ⟨dv, hv, _⟩ := hr; exact ⟨dv, hv⟩
  | indc i => obtain ⟨iv, hv, _⟩ := hr; exact ⟨iv, hv⟩
  | recr r => obtain ⟨rv, hv, _⟩ := hr; exact ⟨rv, hv⟩

/-- A block's members represented in full are represented by kind. -/
theorem membersRep_of_repMutConstList {h : Heap F} {xs : List Ixon.MutConst} {p : SourceValue F}
    (hrep : RepList Obs.Names.«Lists::Node<Ixon::MutConst>» L1.RepMutConst h xs p) :
    Specs.Callees.MembersRep h xs p := by
  induction hrep with
  | nil cell => exact .nil cell
  | cons cell rh _ ih => exact .cons cell (mutShape_of_repMutConst rh) ih

/-- **An observed container-recursor check checked the record at the limit of its context**,
and the record is no block. -/
theorem containerRec_checked {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} {calls cs : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀)
    {x_rc x_x x_ib r : SourceValue F} {h h' : Heap F} {a : _root_.Address}
    (hrc : Claim.RCLimRep t bAddr lim h x_rc) (ha : S0.addr h x_x a)
    (ev : ObsFn Obs.W "KernelModeled::check_container_rec" [x_rc, x_x, x_ib] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    Claim.CheckedLimAt calls bAddr t a lim ∧
      ∀ c, IxVM.Consistency.recordOf E₀ a = some c → ∀ ms, c.info ≠ .muts ms := by
  match Obs.«KernelModeled::check_container_rec».obs ev with
  | .run (ev39 := ev39) (ev25 := ev25) (ev75 := ev75) (hc96 := hc96) .. =>
    have ext : Heap.Extends h _ := ev39.heap_extends.trans ev25.heap_extends
    refine ⟨(Claim.run_check_lim_spec (hrc.mono ext) (S0.addr_mono ext ha) ev75).2.mono
      (fun cl hcl => hsub cl (by rw [hc96]; simp [hcl])), ?_⟩
    intro c hc ms hms
    match Obs.«KernelModeled::rec_family_block».obs ev39 with
    | .run (cs16 := cs16) (ev18 := ev18) (hc333 := hc333) .. =>
      obtain ⟨ab, hab, rfl⟩ := ha
      obtain ⟨raw, c', -, hh, hba, hx, -, hhead⟩ := Claim.get_ci_head hab ev18
      have hsub16 : ∀ cl ∈ cs16, cl ∈ calls := fun cl hcl =>
        hsub cl (by rw [hc96]; simp [hc333, hcl])
      have hcc : c' = c := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc)
        (Core.hashed_mono hsub16 hh) hba hx
      subst hcc
      exact hhead.notMuts ms hms

/-- **An observed advice-record check at a block record checked every member at the limit of
its context**, and the dispatch answered `0` on the block. -/
theorem adviceBlock_checked {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} {calls cs : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀)
    {x_rc x_a x_aset x_wset r : SourceValue F} {h h' : Heap F} {ab : Bytes.Address}
    (hrc : Claim.RCLimRep t bAddr lim h x_rc)
    (ha : Bytes.RepAddressRef addrTy h ab x_a)
    (ev : ObsFn Obs.W "KernelModeled::check_advice_record" [x_rc, x_a, x_aset, x_wset] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    {c : Ixon.Constant} (hc : IxVM.Consistency.recordOf E₀ (ixAddr ab) = some c)
    {ms : Array Ixon.MutConst} (hms : c.info = .muts ms) :
    (∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t (ixAddr ab) ms k lim) ∧
      Claim.NativeObsAt calls (ixAddr ab) := by
  match Obs.«KernelModeled::check_advice_record».obs ev with
  | .run (m2 := m2) (cs12 := cs12) (x_info := x_info) (cs947 := cs947) (ev14 := ev14)
      (sg952 := sg952) (hc1011 := hc1011) .. =>
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc1011]; simp [hcl])
    have hsub947 : ∀ cl ∈ cs947, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc1011]; simp [hcl])
    obtain ⟨ext1, bytes, c', -, hh, haddr, hexact, -, -, -, -, -, -, cRep⟩ :=
      L1.load_verified_constant_decode_bounded ha ev14
    have hrec₀ : Ix.Cert.recordAt E₀ (ixAddr ab) = some c :=
      (hS.recordOf_eq_recordAt _).symm.trans hc
    have hcc : c' = c := hS.record_eq hrec₀ (hashed_mono hsub12 hh) haddr hexact
    rw [hcc] at cRep
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfoRep, -, -, -, -⟩ := cRep
    have hinfo_eq : x_info = infoVal := by
      have h1 := (Value.construct.inj hc_eq).2.2
      exact (List.cons.inj h1).1
    rw [← hinfo_eq, hms] at hinfoRep
    obtain ⟨msPtr, hxm, hlist⟩ := hinfoRep
    have hrc2 : Claim.RCLimRep t bAddr lim m2 x_rc := hrc.mono ext1
    have ha2 : S0.addr m2 x_a (ixAddr ab) :=
      ⟨ab, Bytes.repAddressRef_heapMono₂ addrTy ext1 ha, rfl⟩
    match sg952 with
    | .Defn_Definition_Safe (hv81 := hv) .. =>
      exact absurd (Value.construct.inj (hv.symm.trans hxm)).2.1 (by decide)
    | .Defn_Definition_other (hv81 := hv) .. =>
      exact absurd (Value.construct.inj (hv.symm.trans hxm)).2.1 (by decide)
    | .Defn_Theorem (hv81 := hv) .. =>
      exact absurd (Value.construct.inj (hv.symm.trans hxm)).2.1 (by decide)
    | .Defn_Opaque (hv81 := hv) .. =>
      exact absurd (Value.construct.inj (hv.symm.trans hxm)).2.1 (by decide)
    | .Recr (hv403 := hv) .. =>
      exact absurd (Value.construct.inj (hv.symm.trans hxm)).2.1 (by decide)
    | .IPrj (hv790 := hv) .. =>
      exact absurd (Value.construct.inj (hv.symm.trans hxm)).2.1 (by decide)
    | .CPrj (hv869 := hv) .. =>
      exact absurd (Value.construct.inj (hv.symm.trans hxm)).2.1 (by decide)
    | .Muts (x_members := xm) (hv598 := hv) (ev629 := ev629) (ev649 := ev649)
        (ev683 := ev683) (heq698 := heq698) (ev723 := ev723) (ev744 := ev744)
        (hc784 := hcs) .. =>
      have hxe : xm = msPtr := (List.cons.inj (Value.construct.inj (hv.symm.trans hxm)).2.2).1
      subst hxe
      have ext2 : Heap.Extends m2 _ :=
        ev629.heap_extends.trans (ev649.heap_extends.trans
          (ev683.heap_extends.trans ev723.heap_extends))
      have hmem : Specs.Callees.MembersRep _ ms.toList xm :=
        membersRep_of_repMutConstList
          (RepLinkedList.mono L1.repMutConst_heapMono₂ ext2 hlist)
      have hsubm : ∀ cl ∈ cs947, cl ∈ calls := hsub947
      refine ⟨fun k hk => ?_, ?_⟩
      · exact ((Claim.check_muts_all_lim_spec (hrc2.mono ext2) (S0.addr_mono ext2 ha2) hmem
          ev744).2 k hk).mono (fun cl hcl => hsub947 cl (by rw [hcs]; simp [hcl]))
      · have ext3 : Heap.Extends m2 _ := ev629.heap_extends.trans ev649.heap_extends
        rw [heq698] at ev683
        exact ⟨x_a, _, _, _, ab, ev683, fun cl hcl => hsub947 cl (by rw [hcs]; simp [hcl]),
          Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans ext3) ha, rfl⟩

end IxVM.Refinement.Decl
