import IxVMRefinement.FamilyGraph.AdviceChecked
import IxVMRefinement.Claim.TopProj
import IxVMRefinement.Claim.TopRec

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

/-! ## An advice block is one inductive type -/

/-- **A load of a block record of the run store reads its info**, and the record's resource
size is below `2^33`. -/
theorem load_block_info {calls cs12 : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) {x_a infoV w1 w2 w3 w4 : SourceValue F}
    {h m2 : Heap F} {ab : Bytes.Address} (ha : Bytes.RepAddressRef addrTy h ab x_a)
    (evl : ObsFn Obs.W "Ingress::load_verified_constant" [x_a] h
      (.construct "Ixon::Constant" "Mk" [infoV, w1, w2, w3, w4]) m2 cs12)
    (hsub : ∀ cl ∈ cs12, cl ∈ calls) {c : Ixon.Constant}
    (hc : IxVM.Consistency.recordOf E₀ (ixAddr ab) = some c) {ms : Array Ixon.MutConst}
    (hms : c.info = .muts ms) :
    ∃ msPtr, infoV = .construct "Ixon::ConstantInfo" "Muts" [msPtr] ∧
      RepList Obs.Names.«Lists::Node<Ixon::MutConst>» L1.RepMutConst m2 ms.toList msPtr ∧
      ms.size < 8589934592 := by
  obtain ⟨-, bytes, c', hlen, hh, haddr, hexact, -, -, -, -, -, -, cRep⟩ :=
    L1.load_verified_constant_decode_bounded ha evl
  have hrec₀ : Ix.Cert.recordAt E₀ (ixAddr ab) = some c :=
    (hS.recordOf_eq_recordAt _).symm.trans hc
  have hcc : c' = c := hS.record_eq hrec₀ (hashed_mono hsub hh) haddr hexact
  subst hcc
  have hbl : Claim.BlockLoad calls (ixAddr ab) c' ms :=
    ⟨⟨bytes.toArray⟩, by simpa only [ByteArray.size, List.size_toArray] using hlen,
      hashed_mono hsub hh, haddr, hexact, hms⟩
  have hres := (hbl.record hS hc).2
  have hsize := Claim.muts_size_le hms
  obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfoRep, -, -, -, -⟩ := cRep
  have hinfo_eq : infoV = infoVal := (List.cons.inj (Value.construct.inj hc_eq).2.2).1
  rw [← hinfo_eq, hms] at hinfoRep
  obtain ⟨msPtr, hxm, hlist⟩ := hinfoRep
  exact ⟨msPtr, hxm, hlist, by omega⟩

/-- **The dispatch answering `0` on a block record counts at most one inductive type.** -/
theorem block_is_modeled_zero_count {calls cs : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) {x_a : SourceValue F} {h h' : Heap F}
    {ab : Bytes.Address} (ha : Bytes.RepAddressRef addrTy h ab x_a)
    (ev : ObsFn Obs.W "KernelModeled::block_is_modeled" [x_a] h (.field 0) h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) {c : Ixon.Constant}
    (hc : IxVM.Consistency.recordOf E₀ (ixAddr ab) = some c) {ms : Array Ixon.MutConst}
    (hms : c.info = .muts ms) :
    (ms.toList.filter Specs.Callees.isIndc).length ≤ 1 := by
  have hcnt_le : (ms.toList.filter Specs.Callees.isIndc).length ≤ ms.size := by
    have := List.length_filter_le Specs.Callees.isIndc ms.toList
    simpa using this
  match Obs.«KernelModeled::block_is_modeled».obs ev with
  | .Muts_n0 (ev14 := evl) (ev103 := evc) (hc118 := hcs) .. =>
    obtain ⟨msPtr, hxm, hlist, hlt⟩ := load_block_info hS ha evl
      (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])) hc hms
    have hxe := (List.cons.inj (Value.construct.inj hxm).2.2).1
    subst hxe
    obtain ⟨hv, -⟩ := Core.ModeledAux.muts_indc_count_spec
      (membersRep_of_repMutConstList hlist) evc
    have h0 : (((ms.toList.filter Specs.Callees.isIndc).length : Nat) : F) = ((0 : Nat) : F) := by
      rw [Nat.cast_zero]; exact (Value.field.inj hv).symm
    have := Core.ModeledAux.natCast_inj_lt
      (Nat.lt_of_le_of_lt hcnt_le (Nat.lt_trans hlt (by decide))) (by decide) h0
    omega
  | .Muts_n1 (ev14 := evl) (ev103 := evc) (hc241 := hcs) .. =>
    obtain ⟨msPtr, hxm, hlist, hlt⟩ := load_block_info hS ha evl
      (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])) hc hms
    have hxe := (List.cons.inj (Value.construct.inj hxm).2.2).1
    subst hxe
    obtain ⟨hv, -⟩ := Core.ModeledAux.muts_indc_count_spec
      (membersRep_of_repMutConstList hlist) evc
    have h1 : (((ms.toList.filter Specs.Callees.isIndc).length : Nat) : F) = ((1 : Nat) : F) := by
      rw [Nat.cast_one]; exact (Value.field.inj hv).symm
    have := Core.ModeledAux.natCast_inj_lt
      (Nat.lt_of_le_of_lt hcnt_le (Nat.lt_trans hlt (by decide))) (by decide) h1
    omega
  | .Muts_other (he246 := he) .. =>
    exact absurd (Value.field.inj he) zero_ne_one
  | .other (ev14 := evl) (hne249 := hne) (hc255 := hcs) .. =>
    obtain ⟨msPtr, hxm, -, -⟩ := load_block_info hS ha evl
      (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])) hc hms
    exact absurd hxm (hne [msPtr] rfl)

/-- **An observed advice-record check at a non-empty block record is at one inductive type.**
The arm asserts that every member is inductive (`muts_indc_count` against the length) and that
the dispatch answers `0` on the block, which counts at most one inductive type. -/
theorem adviceBlock_shape {lim : Option Nat} {calls cs : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀)
    {x_rc x_a x_aset x_wset r : SourceValue F} {h h' : Heap F} {ab : Bytes.Address}
    (ha : Bytes.RepAddressRef addrTy h ab x_a)
    (ev : ObsFn Obs.W "KernelModeled::check_advice_record" [x_rc, x_a, x_aset, x_wset] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    {c : Ixon.Constant} (hc : IxVM.Consistency.recordOf E₀ (ixAddr ab) = some c)
    {ms : Array Ixon.MutConst} (hms : c.info = .muts ms) (h0 : ms.size ≠ 0) :
    ∃ ind : Ixon.Inductive, ms = #[.indc ind] := by
  match Obs.«KernelModeled::check_advice_record».obs ev with
  | .run (m2 := m2) (cs12 := cs12) (x_info := x_info) (cs947 := cs947) (ev14 := ev14)
      (sg952 := sg952) (hc1011 := hc1011) .. =>
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc1011]; simp [hcl])
    have hsub947 : ∀ cl ∈ cs947, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc1011]; simp [hcl])
    obtain ⟨msPtr, hxm, hlist, hlt⟩ := load_block_info hS ha ev14 hsub12 hc hms
    have ext1 : Heap.Extends h m2 := ev14.heap_extends
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
    | .Muts (x_members := xm) (m619 := m619) (v616 := v616) (v617 := v617) (m639 := m639)
        (cs647 := cs647) (hv598 := hv) (ev629 := ev629) (ev649 := ev649)
        (heq658 := heq658) (ev683 := ev683) (heq698 := heq698) (hc784 := hcs) .. =>
      have hxe : xm = msPtr := (List.cons.inj (Value.construct.inj (hv.symm.trans hxm)).2.2).1
      subst hxe
      obtain ⟨hv616, hm619⟩ := Core.ModeledAux.muts_indc_count_spec
        (membersRep_of_repMutConstList hlist) ev629
      have ev' : ObsFn W (Instance.mk "Lists::length" [.named "Ixon::MutConst" []]).symbol
          [xm] m619 v617 m639 cs647 := by
        rw [Obs.Names.«Lists::length<Ixon::MutConst>».symbol]; exact ev649
      have hl' : RepList (Instance.mk "Lists::Node" [.named "Ixon::MutConst" []]).symbol
          L1.RepMutConst m619 ms.toList xm := by
        rw [Obs.Names.«Lists::Node<Ixon::MutConst>».symbol, hm619]; exact hlist
      obtain ⟨hv617, hm639⟩ := Lib.Lists.length_spec ev' hl'
      have ha' : Bytes.RepAddressRef addrTy m639 ab x_a := by
        rw [hm639, hm619]; exact Bytes.repAddressRef_heapMono₂ addrTy ext1 ha
      have hcnt_le : (ms.toList.filter Specs.Callees.isIndc).length ≤ ms.size := by
        have := List.length_filter_le Specs.Callees.isIndc ms.toList
        simpa using this
      have hceq : (((ms.toList.filter Specs.Callees.isIndc).length : Nat) : F) =
          ((ms.toList.length : Nat) : F) := by
        have := hv616.symm.trans (heq658.trans hv617)
        exact Value.field.inj this
      have hlen : ms.toList.length = ms.size := by simp
      have hcnt := Core.ModeledAux.natCast_inj_lt
        (Nat.lt_of_le_of_lt hcnt_le (Nat.lt_trans hlt (by decide)))
        (by rw [hlen]; exact Nat.lt_trans hlt (by decide)) hceq
      rw [heq698] at ev683
      have hle := block_is_modeled_zero_count hS ha' ev683
        (fun cl hcl => hsub947 cl (by rw [hcs]; simp [hcl])) hc hms
      -- one member, an inductive one
      match hl : ms.toList with
      | [] => rw [hl] at hlen; simp at hlen; omega
      | [m] =>
        rw [hl] at hcnt
        cases m with
        | indc ind =>
          exact ⟨ind, Array.toList_inj.mp (by rw [hl]; rfl)⟩
        | defn d => simp [Specs.Callees.isIndc] at hcnt
        | recr rc => simp [Specs.Callees.isIndc] at hcnt
      | _ :: _ :: _ =>
        rw [hl] at hcnt hle
        simp only [List.length_cons] at hcnt
        omega

end IxVM.Refinement.Decl
