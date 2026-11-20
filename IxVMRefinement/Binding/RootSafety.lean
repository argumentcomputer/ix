import IxVMRefinement.Binding.StoreLogic
import IxVMRefinement.Binding.WalkChecks
import IxVMRefinement.Binding.BlockSafety
import IxVMRefinement.RoleVal.BoundSafety
import IxVMRefinement.Claim.TopCheckFacts
import IxVMRefinement.StatementRel.LoadedReadsTrace

/-! # The roots of the groups' admissions are in Lean's logic

`RootsAndTheoremsSafe t E₀` for every run that validates every role, without a premise:

* the record bound to a role whose validation walks it (`bound`): the validation checked the
  loaded constant's safety (`RoleVal.ValidateRoleIn.bound_load_safe`), which gives the record's
  own flag (`Ingress::get_ci`'s value, `Claim.GetCIHead`, and the definition's converted value,
  `StatementRel.get_ci_trace_spec`); for a projection record, the block's member-kind check
  (`KernelCheck::check_block_member_kinds`) makes the whole block safe with that member
  (`Assembly.block_inLogic_of_member_kinds`). The check is observed in the load of a definition
  projection, in the check of an inductive or recursor projection (`check_const`'s `Induct` and
  `Rec` arms), and for a constructor projection in the check of its block's members, which the
  walk's closure holds.
* the theorem of a proof in the evidence of a definition specified by equations
  (`eqnsEvidence`): its load returned a `Thm` value (`RoleVal.GetThmCiIn`), so it is a theorem
  record or a theorem member of a block whose member-kind check passed.

`rootsAndTheoremsSafe_of_run` proves what `RemainingStoreClauses` held as its field `rootsSafe`.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

variable {calls : List (Call F)}

/-! ## A projection record's load reaches its block's member-kind check

The same specifications as the private ones of `IxVMRefinement.Claim.TopCheckFacts`, restated
here for the roots of a binding run. -/

/-- The record a load reads at a projection record's address is the projection record. -/
private theorem rs_loaded_proj_eq {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {info : Ixon.ConstantInfo} (hwf : info.wireWF)
    (hhp : Hashed calls (Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩))
    {raw : ByteArray} {c : Ixon.Constant} (hh : Hashed calls raw)
    (hb : Address.blake3Pure raw = Core.projAddr info)
    (hde : Ixon.deConstantExact raw = .ok c) :
    c = ⟨info, #[], #[], #[], #[]⟩ := by
  have hraw : raw = Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩ :=
    hS.hashed_inj hh hhp (hb.trans rfl)
  subst hraw
  have hrt := Ixon.Verify.deConstantExact_serConstant _ (Ingress.emptyTablesConstant_wireWF.mpr hwf)
  exact Except.ok.inj (hde.symm.trans hrt)

/-- **`get_ci` at a definition member's projection record** runs the member-kind check of the
block. -/
private theorem get_ci_dprj_block_kinds {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {i : UInt64} {B : _root_.Address} (hB : B.hash.size = 32)
    (hhp : Hashed calls (Ixon.serConstant ⟨.dPrj ⟨i, B⟩, #[], #[], #[], #[]⟩))
    {ap ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ha : BaseSeams.addr h ap (Core.projAddr (.dPrj ⟨i, B⟩)))
    (ev : ObsFn Obs.W "Ingress::get_ci" [ap] h ptr h' cs) (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∃ (x r : SourceValue F) (h₁ h₂ : Heap F) (cs₁ : List (Call F)),
      BaseSeams.addr h₁ x B ∧ ObsFn Obs.W "KernelCheck::check_block_member_kinds" [x] h₁ r h₂ cs₁ ∧
      (∀ cl ∈ cs₁, cl ∈ calls) := by
  have hid : ∀ (raw : ByteArray) (c' : Ixon.Constant), Hashed calls raw →
      Address.blake3Pure raw = Core.projAddr (.dPrj ⟨i, B⟩) →
      Ixon.deConstantExact raw = .ok c' → c' = ⟨.dPrj ⟨i, B⟩, #[], #[], #[], #[]⟩ :=
    fun raw c' hh hb hd =>
      rs_loaded_proj_eq hS (info := .dPrj ⟨i, B⟩) (show (Ixon.ConstantInfo.dPrj ⟨i, B⟩).wireWF from hB)
        hhp hh hb hd
  match Obs.«Ingress::get_ci».obs ev with
  | .Defn_n0 (cs12 := cs12) (ev14 := ev14) (hc302 := hc) ..
  | .Defn_other (cs12 := cs12) (ev14 := ev14) (hc423 := hc) ..
  | .Axio (cs12 := cs12) (ev14 := ev14) (hc515 := hc) ..
  | .Quot (cs12 := cs12) (ev14 := ev14) (hc606 := hc) ..
  | .IPrj (cs12 := cs12) (ev14 := ev14) (hc750 := hc) ..
  | .CPrj (cs12 := cs12) (ev14 := ev14) (hc851 := hc) ..
  | .RPrj (cs12 := cs12) (ev14 := ev14) (hc926 := hc) ..
  | .Recr (cs12 := cs12) (ev14 := ev14) (hc1071 := hc) .. =>
    obtain ⟨_, raw, c_x, _, hh_x, hbl_x, _, hex_x, hrep_x, _⟩ := load_verified_constant_de ha ev14
    have hcx := hid raw c_x
      (hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) hh_x) hbl_x hex_x
    subst hcx
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfo_r, _, _, _, _⟩ := hrep_x
    injection hv_c with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo_r
    change Claim.RepConstantInfo _ (.dPrj ⟨i, B⟩) _ at hinfo_r
    obtain ⟨_, hv_bad, _⟩ := hinfo_r
    simp at hv_bad
  | .DPrj (m2 := m2) (cs12 := cs12) (x_block_addr := x_block_addr) (cs648 := cs648)
      (ev14 := ev14) (ev650 := ev650) (hc675 := hc) .. =>
    obtain ⟨_, raw, c_x, _, hh_x, hbl_x, _, hex_x, hrep_x, _⟩ := load_verified_constant_de ha ev14
    have hcx := hid raw c_x
      (hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) hh_x) hbl_x hex_x
    subst hcx
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfo_r, _, _, _, _⟩ := hrep_x
    injection hv_c with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo_r
    change Claim.RepConstantInfo _ (.dPrj ⟨i, B⟩) _ at hinfo_r
    obtain ⟨pv, hpv, blkPtr, hdp, hblk_addr⟩ := hinfo_r
    injection hpv with _ _ hpv_args
    simp only [List.cons.injEq, and_true] at hpv_args
    rw [← hpv_args] at hdp
    injection hdp with _ _ hdp_args
    simp only [List.cons.injEq, and_true] at hdp_args
    rcases hdp_args with ⟨_, hblk_eq⟩
    rw [← hblk_eq] at hblk_addr
    match Obs.«Ingress::get_ci_dprj».obs ev650 with
    | .run (v1 := v1) (m2 := m2') (cs12 := cs12') (ev14 := ev_mk) (hc348 := hc348) .. =>
      refine ⟨x_block_addr, v1, m2, m2', cs12', hblk_addr, ev_mk, fun cl hcl => ?_⟩
      have h1 : cl ∈ cs648 := by rw [hc348]; simp [hcl]
      exact hsub cl (by rw [hc]; simp [h1])

/-- **`get_ci` at an inductive member's projection record, then `check_const`**, runs the
member-kind check of the block (`check_const`'s `Induct` arm). -/
private theorem get_ci_iprj_block_kinds {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {i : UInt64} {B : _root_.Address} (hB : B.hash.size = 32)
    (hhp : Hashed calls (Ixon.serConstant ⟨.iPrj ⟨i, B⟩, #[], #[], #[], #[]⟩))
    {ap ptr v rc r_chk : SourceValue F} {h h' h'' : Heap F} {cs cs_chk : List (Call F)}
    (ha : BaseSeams.addr h ap (Core.projAddr (.iPrj ⟨i, B⟩)))
    (ev : ObsFn Obs.W "Ingress::get_ci" [ap] h ptr h' cs) (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (hld : loadValue h' ptr = .ok v)
    (ev_chk : ObsFn Obs.W "KernelCheck::check_const" [rc, v, ap] h' r_chk h'' cs_chk)
    (hsub_chk : ∀ cl ∈ cs_chk, cl ∈ calls) :
    ∃ (x r : SourceValue F) (h₁ h₂ : Heap F) (cs₁ : List (Call F)),
      BaseSeams.addr h₁ x B ∧ ObsFn Obs.W "KernelCheck::check_block_member_kinds" [x] h₁ r h₂ cs₁ ∧
      (∀ cl ∈ cs₁, cl ∈ calls) := by
  have hid : ∀ (raw : ByteArray) (c' : Ixon.Constant), Hashed calls raw →
      Address.blake3Pure raw = Core.projAddr (.iPrj ⟨i, B⟩) →
      Ixon.deConstantExact raw = .ok c' → c' = ⟨.iPrj ⟨i, B⟩, #[], #[], #[], #[]⟩ :=
    fun raw c' hh hb hd =>
      rs_loaded_proj_eq hS (info := .iPrj ⟨i, B⟩) (show (Ixon.ConstantInfo.iPrj ⟨i, B⟩).wireWF from hB)
        hhp hh hb hd
  match Obs.«Ingress::get_ci».obs ev with
  | .Defn_n0 (cs12 := cs12) (ev14 := ev14) (hc302 := hc) ..
  | .Defn_other (cs12 := cs12) (ev14 := ev14) (hc423 := hc) ..
  | .Axio (cs12 := cs12) (ev14 := ev14) (hc515 := hc) ..
  | .Quot (cs12 := cs12) (ev14 := ev14) (hc606 := hc) ..
  | .DPrj (cs12 := cs12) (ev14 := ev14) (hc675 := hc) ..
  | .CPrj (cs12 := cs12) (ev14 := ev14) (hc851 := hc) ..
  | .RPrj (cs12 := cs12) (ev14 := ev14) (hc926 := hc) ..
  | .Recr (cs12 := cs12) (ev14 := ev14) (hc1071 := hc) .. =>
    obtain ⟨_, raw, c_x, _, hh_x, hbl_x, _, hex_x, hrep_x, _⟩ := load_verified_constant_de ha ev14
    have hcx := hid raw c_x
      (hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) hh_x) hbl_x hex_x
    subst hcx
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfo_r, _, _, _, _⟩ := hrep_x
    injection hv_c with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo_r
    change Claim.RepConstantInfo _ (.iPrj ⟨i, B⟩) _ at hinfo_r
    obtain ⟨_, hv_bad, _⟩ := hinfo_r
    simp at hv_bad
  | .IPrj (m2 := m2) (cs12 := cs12) (x_block_addr := x_block_addr) (ev14 := ev14)
      (ev741 := ev741) (ev720 := ev720) (hc750 := hc) .. =>
    obtain ⟨_, raw, c_x, _, hh_x, hbl_x, _, hex_x, hrep_x, _⟩ := load_verified_constant_de ha ev14
    have hcx := hid raw c_x
      (hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) hh_x) hbl_x hex_x
    subst hcx
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfo_r, _, _, _, _⟩ := hrep_x
    injection hv_c with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo_r
    change Claim.RepConstantInfo _ (.iPrj ⟨i, B⟩) _ at hinfo_r
    obtain ⟨pv, hpv, blkPtr, hdp, hblk_addr⟩ := hinfo_r
    injection hpv with _ _ hpv_args
    simp only [List.cons.injEq, and_true] at hpv_args
    rw [← hpv_args] at hdp
    injection hdp with _ _ hdp_args
    simp only [List.cons.injEq, and_true] at hdp_args
    rcases hdp_args with ⟨_, hblk_eq⟩
    rw [← hblk_eq] at hblk_addr
    have ext_m2 : Heap.Extends m2 h' := ev741.heap_extends.trans ev720.heap_extends
    match Obs.«Ingress::get_ci_iprj».obs ev720 with
    | .run (v166 := v166) (m167 := m167) (he170 := he170) (hm169 := hm169) (ev176 := ev176) .. =>
      match Obs.«Convert::convert_inductive».obs ev176 with
      | .run (he128 := he128) .. =>
        rw [he170, hm169, Ingress.loadValue_snoc] at hld
        have hv : v166 = v := Except.ok.inj hld
        subst hv
        subst he128
        match Obs.«KernelCheck::check_const».obs ev_chk with
        | .Axiom_n1 (hv37 := hv) .. | .Axiom_other_n0 (hv37 := hv) ..
        | .Axiom_other_other (hv37 := hv) ..
        | .Defn (hv269 := hv) .. | .Thm (hv526 := hv) ..
        | .Opaque (hv825 := hv) .. | .Quot (hv1076 := hv) ..
        | .Ctor_n0_n0 (hv1989 := hv) .. | .Ctor_n0_other (hv1989 := hv) ..
        | .Ctor_other_n0 (hv1989 := hv) ..
        | .Ctor_other_other (hv1989 := hv) ..
        | .Rec_n0 (hv2727 := hv) .. | .Rec_other (hv2727 := hv) .. =>
          injection hv with _ htag _
          exact absurd htag (by decide)
        | .Induct_n0 (x_ind_block := xblk) (m1283 := m1283) (m1333 := m1333)
            (m1354 := m1354) (m1376 := m1376)
            (m1427 := m1427) (m1440 := m1440) (v1469 := r_mk) (m1470 := m_mk) (cs1480 := cs_mk)
            (ev14 := ev1) (hv1240 := hv_ind) (ev1295 := ev2)
            (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev3)
            (hm1435 := hm1427) (ev1408 := ev4) (ev1452 := ev5)
            (ev1482 := ev_mk) (hc1634 := hc') ..
        | .Induct_other_n0 (x_ind_block := xblk) (m1283 := m1283) (m1333 := m1333)
            (m1354 := m1354) (m1376 := m1376)
            (m1427 := m1427) (m1440 := m1440) (v1469 := r_mk) (m1470 := m_mk) (cs1480 := cs_mk)
            (ev14 := ev1) (hv1240 := hv_ind) (ev1295 := ev2)
            (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev3)
            (hm1435 := hm1427) (ev1408 := ev4) (ev1452 := ev5)
            (ev1482 := ev_mk) (hc1974 := hc') ..
        | .Induct_other_other (x_ind_block := xblk) (m1283 := m1283) (m1333 := m1333)
            (m1354 := m1354) (m1376 := m1376)
            (m1427 := m1427) (m1440 := m1440) (v1469 := r_mk) (m1470 := m_mk) (cs1480 := cs_mk)
            (ev14 := ev1) (hv1240 := hv_ind) (ev1295 := ev2)
            (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev3)
            (hm1435 := hm1427) (ev1408 := ev4) (ev1452 := ev5)
            (ev1482 := ev_mk) (hc1983 := hc') .. =>
          injection hv_ind with _ _ hargs
          injection hargs with _ hargs; injection hargs with _ hargs
          injection hargs with _ hargs; injection hargs with _ hargs
          injection hargs with _ hargs; injection hargs with _ hargs
          injection hargs with hblk _
          subst hblk
          have e_1376 : Heap.Extends m1283 m1376 := by rw [hm1376]; exact Heap.Extends.snoc _ _
          have e_1354 : Heap.Extends m1376 m1354 := by rw [hm1354]; exact Heap.Extends.snoc _ _
          have e_1427 : Heap.Extends m1333 m1427 := by rw [hm1427]; exact Heap.Extends.snoc _ _
          have hext : Heap.Extends h' m1440 :=
            ev1.heap_extends.trans (ev2.heap_extends.trans
              (e_1376.trans (e_1354.trans (ev3.heap_extends.trans
                (e_1427.trans (ev4.heap_extends.trans ev5.heap_extends))))))
          exact ⟨_, r_mk, m1440, m_mk, cs_mk, BaseSeams.addr_mono (ext_m2.trans hext) hblk_addr, ev_mk,
            fun cl hcl => hsub_chk cl (by rw [hc']; simp [hcl])⟩

/-- **`get_ci` at a recursor member's projection record, then `check_const`**, runs the
member-kind check of the block (`check_const`'s `Rec` arm). -/
private theorem get_ci_rprj_block_kinds {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {i : UInt64} {B : _root_.Address} (hB : B.hash.size = 32)
    (hhp : Hashed calls (Ixon.serConstant ⟨.rPrj ⟨i, B⟩, #[], #[], #[], #[]⟩))
    {ap ptr v rc r_chk : SourceValue F} {h h' h'' : Heap F} {cs cs_chk : List (Call F)}
    (ha : BaseSeams.addr h ap (Core.projAddr (.rPrj ⟨i, B⟩)))
    (ev : ObsFn Obs.W "Ingress::get_ci" [ap] h ptr h' cs) (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (hld : loadValue h' ptr = .ok v)
    (ev_chk : ObsFn Obs.W "KernelCheck::check_const" [rc, v, ap] h' r_chk h'' cs_chk)
    (hsub_chk : ∀ cl ∈ cs_chk, cl ∈ calls) :
    ∃ (x r : SourceValue F) (h₁ h₂ : Heap F) (cs₁ : List (Call F)),
      BaseSeams.addr h₁ x B ∧ ObsFn Obs.W "KernelCheck::check_block_member_kinds" [x] h₁ r h₂ cs₁ ∧
      (∀ cl ∈ cs₁, cl ∈ calls) := by
  have hid : ∀ (raw : ByteArray) (c' : Ixon.Constant), Hashed calls raw →
      Address.blake3Pure raw = Core.projAddr (.rPrj ⟨i, B⟩) →
      Ixon.deConstantExact raw = .ok c' → c' = ⟨.rPrj ⟨i, B⟩, #[], #[], #[], #[]⟩ :=
    fun raw c' hh hb hd =>
      rs_loaded_proj_eq hS (info := .rPrj ⟨i, B⟩) (show (Ixon.ConstantInfo.rPrj ⟨i, B⟩).wireWF from hB)
        hhp hh hb hd
  match Obs.«Ingress::get_ci».obs ev with
  | .Defn_n0 (cs12 := cs12) (ev14 := ev14) (hc302 := hc) ..
  | .Defn_other (cs12 := cs12) (ev14 := ev14) (hc423 := hc) ..
  | .Axio (cs12 := cs12) (ev14 := ev14) (hc515 := hc) ..
  | .Quot (cs12 := cs12) (ev14 := ev14) (hc606 := hc) ..
  | .DPrj (cs12 := cs12) (ev14 := ev14) (hc675 := hc) ..
  | .IPrj (cs12 := cs12) (ev14 := ev14) (hc750 := hc) ..
  | .CPrj (cs12 := cs12) (ev14 := ev14) (hc851 := hc) ..
  | .Recr (cs12 := cs12) (ev14 := ev14) (hc1071 := hc) .. =>
    obtain ⟨_, raw, c_x, _, hh_x, hbl_x, _, hex_x, hrep_x, _⟩ := load_verified_constant_de ha ev14
    have hcx := hid raw c_x
      (hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) hh_x) hbl_x hex_x
    subst hcx
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfo_r, _, _, _, _⟩ := hrep_x
    injection hv_c with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo_r
    change Claim.RepConstantInfo _ (.rPrj ⟨i, B⟩) _ at hinfo_r
    obtain ⟨_, hv_bad, _⟩ := hinfo_r
    simp at hv_bad
  | .RPrj (m2 := m2) (cs12 := cs12) (x_block_addr := x_block_addr) (ev14 := ev14)
      (ev917 := ev917) (ev896 := ev896) (hc926 := hc) .. =>
    obtain ⟨_, raw, c_x, _, hh_x, hbl_x, _, hex_x, hrep_x, _⟩ := load_verified_constant_de ha ev14
    have hcx := hid raw c_x
      (hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) hh_x) hbl_x hex_x
    subst hcx
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfo_r, _, _, _, _⟩ := hrep_x
    injection hv_c with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo_r
    change Claim.RepConstantInfo _ (.rPrj ⟨i, B⟩) _ at hinfo_r
    obtain ⟨pv, hpv, blkPtr, hdp, hblk_addr⟩ := hinfo_r
    injection hpv with _ _ hpv_args
    simp only [List.cons.injEq, and_true] at hpv_args
    rw [← hpv_args] at hdp
    injection hdp with _ _ hdp_args
    simp only [List.cons.injEq, and_true] at hdp_args
    rcases hdp_args with ⟨_, hblk_eq⟩
    rw [← hblk_eq] at hblk_addr
    have ext_m2 : Heap.Extends m2 h' := ev917.heap_extends.trans ev896.heap_extends
    match Obs.«Ingress::get_ci_rprj».obs ev896 with
    | .run (v166 := v166) (m167 := m167) (he170 := he170) (hm169 := hm169) (ev176 := ev176) .. =>
      match Obs.«Convert::convert_recursor».obs ev176 with
      | .run (he237 := he237) .. =>
        rw [he170, hm169, Ingress.loadValue_snoc] at hld
        have hv : v166 = v := Except.ok.inj hld
        subst hv
        subst he237
        match Obs.«KernelCheck::check_const».obs ev_chk with
        | .Axiom_n1 (hv37 := hv) .. | .Axiom_other_n0 (hv37 := hv) ..
        | .Axiom_other_other (hv37 := hv) ..
        | .Defn (hv269 := hv) .. | .Thm (hv526 := hv) ..
        | .Opaque (hv825 := hv) .. | .Quot (hv1076 := hv) ..
        | .Induct_n0 (hv1240 := hv) .. | .Induct_other_n0 (hv1240 := hv) ..
        | .Induct_other_other (hv1240 := hv) ..
        | .Ctor_n0_n0 (hv1989 := hv) .. | .Ctor_n0_other (hv1989 := hv) ..
        | .Ctor_other_n0 (hv1989 := hv) ..
        | .Ctor_other_other (hv1989 := hv) .. =>
          injection hv with _ htag _
          exact absurd htag (by decide)
        | .Rec_n0 (x_rec_block := xblk) (m2789 := m2637) (m2857 := m2705) (m2900 := m2718)
            (v2929 := r_mk) (m2930 := m_mk) (cs2940 := cs_mk)
            (ev14 := ev1) (hv2727 := hv_rec) (ev2801 := ev2)
            (hm2865 := hm2705) (ev2838 := ev3) (ev2882 := ev4) (ev2912 := ev_rules)
            (ev2942 := ev_mk) (hc3093 := hc') ..
        | .Rec_other (x_rec_block := xblk) (m2789 := m2637) (m2857 := m2705) (m2900 := m2718)
            (v2929 := r_mk) (m2930 := m_mk) (cs2940 := cs_mk)
            (ev14 := ev1) (hv2727 := hv_rec) (ev2801 := ev2)
            (hm2865 := hm2705) (ev2838 := ev3) (ev2882 := ev4) (ev2912 := ev_rules)
            (ev2942 := ev_mk) (hc3182 := hc') .. =>
          injection hv_rec with _ _ hargs
          injection hargs with _ hargs; injection hargs with _ hargs
          injection hargs with _ hargs; injection hargs with _ hargs
          injection hargs with _ hargs; injection hargs with _ hargs
          injection hargs with _ hargs; injection hargs with _ hargs
          injection hargs with _ hargs; injection hargs with hblk _
          subst hblk
          have e_2705 : Heap.Extends m2637 m2705 := by rw [hm2705]; exact Heap.Extends.snoc _ _
          have hext : Heap.Extends h' m2718 :=
            ev1.heap_extends.trans (ev2.heap_extends.trans
              (e_2705.trans (ev3.heap_extends.trans (ev4.heap_extends.trans
                ev_rules.heap_extends))))
          exact ⟨_, r_mk, m2718, m_mk, cs_mk, BaseSeams.addr_mono (ext_m2.trans hext) hblk_addr, ev_mk,
            fun cl hcl => hsub_chk cl (by rw [hc']; simp [hcl])⟩

/-- **The check of member `0` of a block runs the block's member-kind check.** -/
private theorem member_zero_block_kinds {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {bAddr B : _root_.Address} {t : Ix.Kernel.RoleTable} {ms : Array Ixon.MutConst}
    {lim : Option Nat} (hm : MemberCheckedLimAt calls bAddr t B ms 0 lim) :
    ∃ (x r : SourceValue F) (h₁ h₂ : Heap F) (cs₁ : List (Call F)),
      BaseSeams.addr h₁ x B ∧ ObsFn Obs.W "KernelCheck::check_block_member_kinds" [x] h₁ r h₂ cs₁ ∧
      (∀ cl ∈ cs₁, cl ∈ calls) := by
  obtain ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmem, hblk, ev_pa, -, hsub_pa,
    -, -, ev_ld, -, hsub_ld, hld, ev_chk, -, hsub_chk⟩ := hm
  obtain ⟨b, hb, rfl⟩ := hblk
  obtain ⟨-, -, -, mc, a, -, ra, hixa, hhp⟩ := Ingress.projection_addr_hashed_spec hmem hb ev_pa
  have hhp' := hashed_mono hsub_pa hhp
  have hB : (Core.ixAddr b).hash.size = 32 := b.size_toArray
  cases mc with
  | defn d =>
    exact get_ci_dprj_block_kinds hS (B := Core.ixAddr b) hB hhp' ⟨a, ra, hixa⟩ ev_ld hsub_ld
  | indc ind =>
    exact get_ci_iprj_block_kinds hS (B := Core.ixAddr b) hB hhp' ⟨a, ra, hixa⟩ ev_ld hsub_ld
      hld ev_chk hsub_chk
  | recr rcr =>
    exact get_ci_rprj_block_kinds hS (B := Core.ixAddr b) hB hhp' ⟨a, ra, hixa⟩ ev_ld hsub_ld
      hld ev_chk hsub_chk

/-! ## The block checks the roots' loads and walks observed -/

/-- **The run checked the member kinds of the block at `B`**: an observed
`KernelCheck::check_block_member_kinds` on `B` among `calls`. -/
def BlockKindsChecked (calls : List (Call F)) (B : _root_.Address) : Prop :=
  ∃ (x r : SourceValue F) (h₁ h₂ : Heap F) (cs₁ : List (Call F)),
    BaseSeams.addr h₁ x B ∧ ObsFn Obs.W "KernelCheck::check_block_member_kinds" [x] h₁ r h₂ cs₁ ∧
    (∀ cl ∈ cs₁, cl ∈ calls)

/-- A projection record the run loaded at `A` is its canonical serialization, which the run
hashed, and `A` is its projection address. -/
private theorem loaded_proj_canonical {raw : ByteArray} {c : Ixon.Constant} {A : _root_.Address}
    (hh : Hashed calls raw) (hba : Address.blake3Pure raw = A)
    (hx : Ixon.deConstantExact raw = .ok c) (htv : Ingress.ConstantTablesValid c)
    (hproj : Assembly.IsProjInfo c.info) :
    Hashed calls (Ixon.serConstant ⟨c.info, #[], #[], #[], #[]⟩) ∧ A = Core.projAddr c.info := by
  obtain ⟨hcanon, hA⟩ := proj_canon hba hx htv hproj
  have hemp : Ix.Kernel.Reader.emptyTables c = true := by
    rw [hcanon]
    rfl
  obtain ⟨hraw, -⟩ := Assembly.deConstantExact_proj_eq_serConstant hx hemp hproj
  have hser : Ixon.serConstant ⟨c.info, #[], #[], #[], #[]⟩ = raw := by
    rw [hraw]
    exact congrArg Ixon.serConstant hcanon.symm
  refine ⟨by rw [hser]; exact hh, ?_⟩
  rw [hA]
  exact congrArg (fun x => Address.blake3Pure (Ixon.serConstant x)) hcanon

/-- **A load of a definition projection record runs its block's member-kind check**
(`Ingress::get_ci_dprj`). -/
theorem get_ci_dprj_kinds_at {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {A : _root_.Address} {c : Ixon.Constant} {p : Ixon.DefinitionProj}
    (hrec : recordOf E₀ A = some c) (hinfo : c.info = .dPrj p)
    {ap ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ha : BaseSeams.addr h ap A) (ev : ObsFn Obs.W "Ingress::get_ci" [ap] h ptr h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) : BlockKindsChecked calls p.block := by
  obtain ⟨ab, hab, rfl⟩ := ha
  obtain ⟨raw, c', hsz, hh, hba, hx, htv, hhead⟩ := get_ci_head hab ev
  have hcc : c' = c := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hrec)
    (Core.hashed_mono hsub hh) hba hx
  subst c'
  have hproj : Assembly.IsProjInfo c.info := by rw [hinfo]; exact True.intro
  obtain ⟨hhp, hA⟩ := loaded_proj_canonical (Core.hashed_mono hsub hh) hba hx htv hproj
  obtain ⟨i, B⟩ := p
  rw [hinfo] at hhp hA
  obtain ⟨cb, ms, d, ⟨bytes, -, -, hbB, -, -⟩, -⟩ := hhead.dPrj i B hinfo
  have hB : B.hash.size = 32 := by
    rw [← hbB]
    exact (Blake3.Pure.hash _).property
  exact get_ci_dprj_block_kinds hS hB hhp ⟨ab, hab, hA⟩ ev hsub

/-- **The walk's check of an inductive projection record runs its block's member-kind check**
(`check_const`'s `Induct` arm). -/
theorem CheckedLimAt.iprj_block_kinds {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {A : _root_.Address} {c : Ixon.Constant} {p : Ixon.InductiveProj}
    (hrec : recordOf E₀ A = some c) (hinfo : c.info = .iPrj p)
    (hchk : CheckedLimAt calls bAddr t A lim) : BlockKindsChecked calls p.block := by
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    -, -, ha_pre, -, ev_ld, -, hsub_ld, hld, ev_chk, -, hsub_chk⟩ := hchk
  obtain ⟨ab, hab, rfl⟩ := ha_pre
  obtain ⟨raw, c', hsz, hh, hba, hx, htv, hhead⟩ := get_ci_head hab ev_ld
  have hcc : c' = c := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hrec)
    (Core.hashed_mono hsub_ld hh) hba hx
  subst c'
  have hproj : Assembly.IsProjInfo c.info := by rw [hinfo]; exact True.intro
  obtain ⟨hhp, hA⟩ := loaded_proj_canonical (Core.hashed_mono hsub_ld hh) hba hx htv hproj
  obtain ⟨i, B⟩ := p
  rw [hinfo] at hhp hA
  obtain ⟨cb, ms, ind, -, -, -, nl, ty, np, ni, x_blk, b, -, -, hbeq⟩ := hhead.iPrj i B hinfo
  have hB : B.hash.size = 32 := by
    rw [← hbeq]
    exact Core.ixAddr_size b
  exact get_ci_iprj_block_kinds hS hB hhp ⟨ab, hab, hA⟩ ev_ld hsub_ld hld ev_chk hsub_chk

/-- **The walk's check of a recursor projection record runs its block's member-kind check**
(`check_const`'s `Rec` arm). -/
theorem CheckedLimAt.rprj_block_kinds {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {A : _root_.Address} {c : Ixon.Constant} {p : Ixon.RecursorProj}
    (hrec : recordOf E₀ A = some c) (hinfo : c.info = .rPrj p)
    (hchk : CheckedLimAt calls bAddr t A lim) : BlockKindsChecked calls p.block := by
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    -, -, ha_pre, -, ev_ld, -, hsub_ld, hld, ev_chk, -, hsub_chk⟩ := hchk
  obtain ⟨ab, hab, rfl⟩ := ha_pre
  obtain ⟨raw, c', hsz, hh, hba, hx, htv, hhead⟩ := get_ci_head hab ev_ld
  have hcc : c' = c := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hrec)
    (Core.hashed_mono hsub_ld hh) hba hx
  subst c'
  have hproj : Assembly.IsProjInfo c.info := by rw [hinfo]; exact True.intro
  obtain ⟨hhp, hA⟩ := loaded_proj_canonical (Core.hashed_mono hsub_ld hh) hba hx htv hproj
  obtain ⟨i, B⟩ := p
  rw [hinfo] at hhp hA
  obtain ⟨cb, ms, rcr, -, -, nl, ty, np, ni, nm, nmin, rules, k, x_blk, b, -, -, hbeq⟩ :=
    hhead.rPrj i B hinfo
  have hB : B.hash.size = 32 := by
    rw [← hbeq]
    exact Core.ixAddr_size b
  exact get_ci_rprj_block_kinds hS hB hhp ⟨ab, hab, hA⟩ ev_ld hsub_ld hld ev_chk hsub_chk

/-- **The walk's check of a block's members runs the block's member-kind check.** -/
theorem MemberCheckedLimAt.block_kinds {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {bAddr B : _root_.Address} {t : Ix.Kernel.RoleTable} {ms : Array Ixon.MutConst}
    {lim : Option Nat} (hm : MemberCheckedLimAt calls bAddr t B ms 0 lim) :
    BlockKindsChecked calls B :=
  member_zero_block_kinds hS hm

/-- **The check of member `0` of a block runs the block's member-kind check, under any role
context**: the member's projection address, the load at it and the check of the loaded value,
as observed (`MemberCheckedLimAt.block_kinds` without the context). -/
theorem member_zero_block_kinds_of {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {B : _root_.Address} {ms : Array Ixon.MutConst} {h_pa h_pre m_chk h'_chk : Heap F}
    {rc x_members x_block ap ptr v r_chk : SourceValue F} {cs_pa cs_load cs_chk : List (Call F)}
    (hmem : Specs.Callees.MembersRep h_pa ms.toList x_members) (hblk : BaseSeams.addr h_pa x_block B)
    (ev_pa : ObsFn Obs.W "Ingress::projection_addr" [x_members, x_block, .field ((0 : Nat) : F)]
      h_pa ap h_pre cs_pa)
    (hsub_pa : ∀ cl ∈ cs_pa, cl ∈ calls)
    (ev_ld : ObsFn Obs.W "Ingress::get_ci" [ap] h_pre ptr m_chk cs_load)
    (hsub_ld : ∀ cl ∈ cs_load, cl ∈ calls) (hld : loadValue m_chk ptr = .ok v)
    (ev_chk : ObsFn Obs.W "KernelCheck::check_const" [rc, v, ap] m_chk r_chk h'_chk cs_chk)
    (hsub_chk : ∀ cl ∈ cs_chk, cl ∈ calls) : BlockKindsChecked calls B := by
  obtain ⟨b, hb, rfl⟩ := hblk
  obtain ⟨-, -, -, mc, a, -, ra, hixa, hhp⟩ := Ingress.projection_addr_hashed_spec hmem hb ev_pa
  have hhp' := hashed_mono hsub_pa hhp
  have hB : (Core.ixAddr b).hash.size = 32 := b.size_toArray
  cases mc with
  | defn d =>
    exact get_ci_dprj_block_kinds hS (B := Core.ixAddr b) hB hhp' ⟨a, ra, hixa⟩ ev_ld hsub_ld
  | indc ind =>
    exact get_ci_iprj_block_kinds hS (B := Core.ixAddr b) hB hhp' ⟨a, ra, hixa⟩ ev_ld hsub_ld
      hld ev_chk hsub_chk
  | recr rcr =>
    exact get_ci_rprj_block_kinds hS (B := Core.ixAddr b) hB hhp' ⟨a, ra, hixa⟩ ev_ld hsub_ld
      hld ev_chk hsub_chk

/-- **A loaded block whose member-kind check the run observed is in Lean's logic when one of
its members has a constant in Lean's logic.** -/
theorem BlockLoad.inLogic {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀) {B : _root_.Address} {cb₁ : Ixon.Constant}
    {ms : Array Ixon.MutConst} (hbl : BlockLoad calls B cb₁ ms) (hk : BlockKindsChecked calls B)
    (hm : ∃ m ∈ ms.toList, Assembly.MemberHasLogic m) :
    ∀ cb, recordOf E₀ B = some cb → InLogic cb := by
  intro cb hcb
  obtain ⟨hrec1, hinfo1⟩ := hbl.stored hH
  have e : cb₁ = cb := Option.some.inj (hrec1.symm.trans hcb)
  subst e
  obtain ⟨x, r, h₁, h₂, cs₁, ha, ev, hsub⟩ := hk
  exact Assembly.block_inLogic_of_member_kinds hS ha ev hsub
    ((hS.recordOf_eq_recordAt B).symm.trans hrec1) hinfo1 hm

/-! ## Flags read off a value that passed a role's safety check -/

private theorem bound_safe_axiom {a₁ a₂ u : SourceValue F}
    (hvs : RoleVal.BoundValueSafe (.construct "KernelTypes::KConstantInfo" "Axiom" [a₁, a₂, u])) :
    u = .field 0 := by
  rcases hvs with ⟨h, h', cs, ev⟩ | ⟨nl', ty', val', hint', hv⟩
  · match Obs.«KernelCheck::is_unsafe_ci».obs ev with
    | .Axiom (hv15 := hv) (he35 := he) .. =>
      injection hv with _ _ hargs
      injection hargs with _ hargs
      injection hargs with _ hargs
      injection hargs with hu _
      rw [hu]
      exact he.symm
    | .Defn_Safe (hv43 := hv) .. | .Defn_other (hv43 := hv) .. | .Thm (hv105 := hv) ..
    | .Opaque (hv133 := hv) .. | .Quot (hv167 := hv) .. | .Induct (hv195 := hv) ..
    | .Ctor (hv253 := hv) .. | .Rec (hv311 := hv) .. =>
      injection hv with _ htag _
      exact absurd htag (by decide)
  · injection hv with _ htag _
    exact absurd htag (by decide)

private theorem bound_safe_induct {a₁ a₂ a₃ a₄ a₅ u a₇ a₈ : SourceValue F}
    (hvs : RoleVal.BoundValueSafe
      (.construct "KernelTypes::KConstantInfo" "Induct" [a₁, a₂, a₃, a₄, a₅, u, a₇, a₈])) :
    u = .field 0 := by
  rcases hvs with ⟨h, h', cs, ev⟩ | ⟨nl', ty', val', hint', hv⟩
  · match Obs.«KernelCheck::is_unsafe_ci».obs ev with
    | .Induct (hv195 := hv) (he245 := he) .. =>
      injection hv with _ _ hargs
      injection hargs with _ hargs
      injection hargs with _ hargs
      injection hargs with _ hargs
      injection hargs with _ hargs
      injection hargs with _ hargs
      injection hargs with hu _
      rw [hu]
      exact he.symm
    | .Axiom (hv15 := hv) .. | .Defn_Safe (hv43 := hv) .. | .Defn_other (hv43 := hv) ..
    | .Thm (hv105 := hv) .. | .Opaque (hv133 := hv) .. | .Quot (hv167 := hv) ..
    | .Ctor (hv253 := hv) .. | .Rec (hv311 := hv) .. =>
      injection hv with _ htag _
      exact absurd htag (by decide)
  · injection hv with _ htag _
    exact absurd htag (by decide)

private theorem bound_safe_ctor {a₁ a₂ a₃ a₄ a₅ a₆ a₇ u : SourceValue F}
    (hvs : RoleVal.BoundValueSafe
      (.construct "KernelTypes::KConstantInfo" "Ctor" [a₁, a₂, a₃, a₄, a₅, a₆, a₇, u])) :
    u = .field 0 := by
  rcases hvs with ⟨h, h', cs, ev⟩ | ⟨nl', ty', val', hint', hv⟩
  · match Obs.«KernelCheck::is_unsafe_ci».obs ev with
    | .Ctor (hv253 := hv) (he303 := he) .. =>
      injection hv with _ _ hargs
      injection hargs with _ hargs
      injection hargs with _ hargs
      injection hargs with _ hargs
      injection hargs with _ hargs
      injection hargs with _ hargs
      injection hargs with _ hargs
      injection hargs with _ hargs
      injection hargs with hu _
      rw [hu]
      exact he.symm
    | .Axiom (hv15 := hv) .. | .Defn_Safe (hv43 := hv) .. | .Defn_other (hv43 := hv) ..
    | .Thm (hv105 := hv) .. | .Opaque (hv133 := hv) .. | .Quot (hv167 := hv) ..
    | .Induct (hv195 := hv) .. | .Rec (hv311 := hv) .. =>
      injection hv with _ htag _
      exact absurd htag (by decide)
  · injection hv with _ htag _
    exact absurd htag (by decide)

private theorem bound_safe_rec {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ u a₁₀ a₁₁ : SourceValue F}
    (hvs : RoleVal.BoundValueSafe
      (.construct "KernelTypes::KConstantInfo" "Rec" [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, u, a₁₀, a₁₁])) :
    u = .field 0 := by
  rcases hvs with ⟨h, h', cs, ev⟩ | ⟨nl', ty', val', hint', hv⟩
  · match Obs.«KernelCheck::is_unsafe_ci».obs ev with
    | .Rec (hv311 := hv) (he379 := he) .. =>
      injection hv with _ _ hargs
      injection hargs with _ hargs
      injection hargs with _ hargs
      injection hargs with _ hargs
      injection hargs with _ hargs
      injection hargs with _ hargs
      injection hargs with _ hargs
      injection hargs with _ hargs
      injection hargs with _ hargs
      injection hargs with hu _
      rw [hu]
      exact he.symm
    | .Axiom (hv15 := hv) .. | .Defn_Safe (hv43 := hv) .. | .Defn_other (hv43 := hv) ..
    | .Thm (hv105 := hv) .. | .Opaque (hv133 := hv) .. | .Quot (hv167 := hv) ..
    | .Induct (hv195 := hv) .. | .Ctor (hv253 := hv) .. =>
      injection hv with _ htag _
      exact absurd htag (by decide)
  · injection hv with _ htag _
    exact absurd htag (by decide)

/-- A converted definition matched as a `Defn` value with safety `Safe` is one the reader
accepts. -/
private theorem safetyDecline_none_of_defn_safe {d : Ixon.Definition}
    {tyPtr valPtr hint nl ty val hint' : SourceValue F}
    (hv : Ingress.defnValShape d tyPtr valPtr hint = .construct "KernelTypes::KConstantInfo" "Defn"
      [nl, ty, val, .construct "Ixon::DefinitionSafety" "Safe" [], hint']) :
    Ix.Kernel.Reader.safetyDecline d = none := by
  cases hk : d.kind with
  | defn =>
    simp only [Ingress.defnValShape, hk] at hv
    injection hv with _ _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with hs _
    have hsafe : d.safety = .safe := by
      cases hds : d.safety with
      | safe => rfl
      | unsaf => rw [hds] at hs; simp [Ingress.repDefSafetyVal] at hs
      | part => rw [hds] at hs; simp [Ingress.repDefSafetyVal] at hs
    rw [Ix.Kernel.Reader.safetyDecline, hk, hsafe]
    decide
  | opaq =>
    simp only [Ingress.defnValShape, hk] at hv
    injection hv with _ htag _
    exact absurd htag (by decide)
  | thm =>
    simp only [Ingress.defnValShape, hk] at hv
    injection hv with _ htag _
    exact absurd htag (by decide)

/-- A converted definition loaded as a `Thm` value is a theorem, which the reader accepts. -/
private theorem safetyDecline_none_of_thm_shape {d : Ixon.Definition}
    {tyPtr valPtr hint nl ty val : SourceValue F}
    (hv : Ingress.defnValShape d tyPtr valPtr hint =
      .construct "KernelTypes::KConstantInfo" "Thm" [nl, ty, val]) :
    Ix.Kernel.Reader.safetyDecline d = none := by
  cases hk : d.kind with
  | thm =>
    rw [Ix.Kernel.Reader.safetyDecline, hk]
    cases d.safety <;> decide
  | defn =>
    simp only [Ingress.defnValShape, hk] at hv
    injection hv with _ htag _
    exact absurd htag (by decide)
  | opaq =>
    simp only [Ingress.defnValShape, hk] at hv
    injection hv with _ htag _
    exact absurd htag (by decide)

private theorem defn_safe_of_bound {d : Ixon.Definition} {tyPtr valPtr hint : SourceValue F}
    (hvs : RoleVal.BoundValueSafe (Ingress.defnValShape d tyPtr valPtr hint)) :
    Ix.Kernel.Reader.safetyDecline d = none := by
  rcases hvs with ⟨h, h', cs, ev⟩ | ⟨nl, ty, val, hint', hv⟩
  · exact Assembly.safetyDecline_none_of_unsafe_ci_zero ev
  · exact safetyDecline_none_of_defn_safe hv

/-! ## The safety of a record from its load -/

private theorem sourceSafe_self {E₀ : Ixon.Env} {A : _root_.Address} {c : Ixon.Constant}
    (hrec : recordOf E₀ A = some c) (hl : InLogic c) (hown : Ix.Cert.ownerOf A c = A) :
    InLogic c ∧ ∀ cb, recordOf E₀ (Ix.Cert.ownerOf A c) = some cb → InLogic cb := by
  refine ⟨hl, fun cb hcb => ?_⟩
  rw [hown, hrec] at hcb
  rw [← Option.some.inj hcb]
  exact hl

private theorem inLogic_proj {c : Ixon.Constant}
    (hp : (∃ p, c.info = .dPrj p) ∨ (∃ p, c.info = .iPrj p) ∨ (∃ p, c.info = .cPrj p) ∨
      ∃ p, c.info = .rPrj p) : InLogic c := by
  rcases hp with ⟨p, hp⟩ | ⟨p, hp⟩ | ⟨p, hp⟩ | ⟨p, hp⟩ <;> simp only [InLogic, hp]

/-- **The record bound to a walked role is in Lean's logic with its block**, from the role
validation's safety check of the loaded constant (`RoleVal.BoundLoadSafeIn`) and the closed
list of records the role's walk checked, which holds the record: the loaded value carries the
record's flag (or, for a definition, its safety); for a projection record the block's
member-kind check, observed in the load (a definition projection), in the record's own check
(an inductive or recursor projection) or in the check of its block's members (a constructor
projection), makes the whole block safe with that member. -/
theorem sourceSafe_of_bound_load {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {recs : List (TopRec calls bAddr t lim)} (hcl : TopRecsClosed recs)
    {A : _root_.Address} (hA : A ∈ recs.map (·.addr)) (hsafe : RoleVal.BoundLoadSafeIn calls A) :
    SourceSafe E₀ A := by
  obtain ⟨h, h', ap, ptr, v, cs, ha, ev, hsub, hld, hvs⟩ := hsafe
  obtain ⟨ab, hab, rfl⟩ := ha
  obtain ⟨raw, c, hsz, hh, hba, hx, htv, hhead⟩ := get_ci_head hab ev
  have hhc := Core.hashed_mono hsub hh
  have hrec : recordOf E₀ (Core.ixAddr ab) = some c := by
    rw [← hba]
    exact recordOf_of_hashed hH hhc hsz hx
  have hrecAt : Ix.Cert.recordAt E₀ (Core.ixAddr ab) = some c :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec
  obtain ⟨raw', c', hh', hba', hx', htrace⟩ := Ingress.get_ci_trace_spec hab ev
  have hc' : c' = c := hS.record_eq hrecAt (Core.hashed_mono hsub hh') hba' hx'
  subst c'
  obtain ⟨r, hr, hra⟩ := List.mem_map.mp hA
  have hrc : r.c = c := by
    have h1 := Binding.topRec_recordOf hH r
    rw [hra, hrec] at h1
    exact (Option.some.inj h1).symm
  have hrchk : CheckedLimAt calls bAddr t (Core.ixAddr ab) lim := by
    rcases r.hchecked with ⟨ms', hms', -⟩ | hchk
    · rw [hrc] at hms'
      exact absurd hms' (hhead.notMuts ms')
    · rw [hra] at hchk
      exact hchk
  suffices hmain : InLogic c ∧
      ∀ cb, recordOf E₀ (Ix.Cert.ownerOf (Core.ixAddr ab) c) = some cb → InLogic cb by
    intro c₁ hc₁
    rw [Option.some.inj (hc₁.symm.trans hrec)]
    exact hmain
  cases hci : c.info with
  | muts ms => exact absurd hci (hhead.notMuts ms)
  | defn d =>
    unfold Ingress.GetCITraceResult at htrace
    rw [hci] at htrace
    obtain ⟨blobs, tree, v', -, -, hld', htr⟩ := htrace
    have hv : v' = v := Except.ok.inj (hld'.symm.trans hld)
    subst hv
    obtain ⟨-, tyPtr, valPtr, hint, -, -, hvshape, -⟩ := htr
    rw [hvshape] at hvs
    have hl : InLogic c := by
      simp only [InLogic, hci]
      exact defn_safe_of_bound hvs
    exact sourceSafe_self hrec hl (by simp only [Ix.Cert.ownerOf, hci])
  | axio ax =>
    obtain ⟨nl, ty, hldv⟩ := hhead.axio ax hci
    have hv := Except.ok.inj (hldv.symm.trans hld)
    rw [← hv] at hvs
    have hf := Assembly.repBoolField_zero_false (bound_safe_axiom hvs)
    have hl : InLogic c := by simp only [InLogic, hci, hf]
    exact sourceSafe_self hrec hl (by simp only [Ix.Cert.ownerOf, hci])
  | quot q =>
    have hl : InLogic c := by simp only [InLogic, hci]
    exact sourceSafe_self hrec hl (by simp only [Ix.Cert.ownerOf, hci])
  | recr rcr =>
    obtain ⟨nl, ty, np, ni, nm, nmin, rules, k, x_a, hldv⟩ := hhead.recr rcr hci
    have hv := Except.ok.inj (hldv.symm.trans hld)
    rw [← hv] at hvs
    have hf := Assembly.repBoolField_zero_false (bound_safe_rec hvs)
    have hl : InLogic c := by simp only [InLogic, hci, hf]
    exact sourceSafe_self hrec hl (by simp only [Ix.Cert.ownerOf, hci])
  | dPrj p =>
    have hk := get_ci_dprj_kinds_at hS hrec hci ⟨ab, hab, rfl⟩ ev hsub
    obtain ⟨i, B⟩ := p
    obtain ⟨cb, ms, d, hbl, hmem⟩ := hhead.dPrj i B hci
    unfold Ingress.GetCITraceResult at htrace
    rw [hci] at htrace
    obtain ⟨-, blkBytes, cbt, mst, dt, blobs, tree, v', hhb, hbb, hxb, hinfot, hmemt, -, -, hld',
      htr⟩ := htrace
    have hv : v' = v := Except.ok.inj (hld'.symm.trans hld)
    subst hv
    obtain ⟨hrecB, -⟩ := (hbl.mono hsub).stored hH
    have hcbeq : cbt = cb := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hrecB)
      (Core.hashed_mono hsub hhb) hbb hxb
    subst cbt
    have hms : mst = ms := Ixon.ConstantInfo.muts.inj (hinfot.symm.trans hbl.info)
    subst mst
    have hdt : dt = d := Ixon.MutConst.defn.inj (Option.some.inj (hmemt.symm.trans hmem))
    subst dt
    obtain ⟨-, tyPtr, valPtr, hint, -, -, hvshape, -⟩ := htr
    rw [hvshape] at hvs
    have hsd := defn_safe_of_bound hvs
    refine ⟨inLogic_proj (.inl ⟨_, hci⟩), fun cb' hcb' => ?_⟩
    have hown : Ix.Cert.ownerOf (Core.ixAddr ab) c = B := by simp only [Ix.Cert.ownerOf, hci]
    rw [hown] at hcb'
    exact BlockLoad.inLogic hS hH (hbl.mono hsub) hk
      ⟨.defn d, List.mem_of_getElem? hmem, hsd⟩ cb' hcb'
  | iPrj p =>
    have hk := CheckedLimAt.iprj_block_kinds hS hrec hci hrchk
    obtain ⟨i, B⟩ := p
    obtain ⟨cb, ms, ind, hbl, hmem, -, nl, ty, np, ni, x_blk, b, hldv, -, -⟩ := hhead.iPrj i B hci
    have hv := Except.ok.inj (hldv.symm.trans hld)
    rw [← hv] at hvs
    have hf := Assembly.repBoolField_zero_false (bound_safe_induct hvs)
    refine ⟨inLogic_proj (.inr (.inl ⟨_, hci⟩)), fun cb' hcb' => ?_⟩
    have hown : Ix.Cert.ownerOf (Core.ixAddr ab) c = B := by simp only [Ix.Cert.ownerOf, hci]
    rw [hown] at hcb'
    exact BlockLoad.inLogic hS hH (hbl.mono hsub) hk
      ⟨.indc ind, List.mem_of_getElem? hmem, Or.inl hf⟩ cb' hcb'
  | rPrj p =>
    have hk := CheckedLimAt.rprj_block_kinds hS hrec hci hrchk
    obtain ⟨i, B⟩ := p
    obtain ⟨cb, ms, rcr, hbl, hmem, nl, ty, np, ni, nm, nmin, rules, k, x_blk, b, hldv, -, -⟩ :=
      hhead.rPrj i B hci
    have hv := Except.ok.inj (hldv.symm.trans hld)
    rw [← hv] at hvs
    have hf := Assembly.repBoolField_zero_false (bound_safe_rec hvs)
    refine ⟨inLogic_proj (.inr (.inr (.inr ⟨_, hci⟩))), fun cb' hcb' => ?_⟩
    have hown : Ix.Cert.ownerOf (Core.ixAddr ab) c = B := by simp only [Ix.Cert.ownerOf, hci]
    rw [hown] at hcb'
    exact BlockLoad.inLogic hS hH (hbl.mono hsub) hk
      ⟨.recr rcr, List.mem_of_getElem? hmem, hf⟩ cb' hcb'
  | cPrj p =>
    obtain ⟨i, j, B⟩ := p
    obtain ⟨cb, ms, ind, hbl, hmem, hlt, ctor, hctor, nl, ty, ci, np, nf, x_blk, b, hldv, -, -⟩ :=
      hhead.cPrj i j B hci
    have hv := Except.ok.inj (hldv.symm.trans hld)
    rw [← hv] at hvs
    have hf := Assembly.repBoolField_zero_false (bound_safe_ctor hvs)
    obtain ⟨hrecB, hinfoB⟩ := (hbl.mono hsub).stored hH
    -- the block is a record of the walk, checked member by member
    have hk : BlockKindsChecked calls B := by
      have hproj : IsProjRec r.c := by rw [hrc]; exact .inr (.inr (.inl ⟨_, hci⟩))
      obtain ⟨r', hr', hra', -⟩ := (hcl r hr).1 hproj
      have hown : Ix.Cert.ownerOf r.addr r.c = B := by
        rw [hrc]; simp only [Ix.Cert.ownerOf, hci]
      rw [hown] at hra'
      have hrc' : r'.c = cb := by
        have h1 := Binding.topRec_recordOf hH r'
        rw [hra', hrecB] at h1
        exact (Option.some.inj h1).symm
      have hpos : 0 < ms.size := by
        have := (List.getElem?_eq_some_iff.mp hmem).1
        rw [Array.length_toList] at this
        omega
      rcases r'.hchecked with ⟨ms', hms', hkm⟩ | hchk'
      · rw [hrc', hinfoB] at hms'
        injection hms' with hms'
        subst hms'
        have hm0 := hkm 0 hpos
        rw [hra'] at hm0
        exact MemberCheckedLimAt.block_kinds hS hm0
      · exfalso
        rw [hra'] at hchk'
        exact checked_not_block hS hrecB hinfoB hchk'
    refine ⟨inLogic_proj (.inr (.inr (.inl ⟨_, hci⟩))), fun cb' hcb' => ?_⟩
    have hown : Ix.Cert.ownerOf (Core.ixAddr ab) c = B := by simp only [Ix.Cert.ownerOf, hci]
    rw [hown] at hcb'
    exact BlockLoad.inLogic hS hH (hbl.mono hsub) hk
      ⟨.indc ind, List.mem_of_getElem? hmem, Or.inr ⟨ctor, List.mem_of_getElem? hctor, hf⟩⟩ cb' hcb'

/-- **A record the run loaded as a `Thm` value is in Lean's logic with its block**: it is a
theorem record, or a theorem member's projection into a block whose member-kind check the load
ran (`Ingress::get_ci_dprj`); every other kind of record loads as another value. -/
theorem sourceSafe_of_thm_load {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀) {A : _root_.Address}
    (hthm : RoleVal.GetThmCiIn calls A) : SourceSafe E₀ A := by
  obtain ⟨h, h', ap, ptr, nl₀, tty, val₀, cs, ha, ev, -, hsub, hld⟩ := hthm
  obtain ⟨ab, hab, rfl⟩ := ha
  obtain ⟨raw, c, hsz, hh, hba, hx, htv, hhead⟩ := get_ci_head hab ev
  have hhc := Core.hashed_mono hsub hh
  have hrec : recordOf E₀ (Core.ixAddr ab) = some c := by
    rw [← hba]
    exact recordOf_of_hashed hH hhc hsz hx
  have hrecAt : Ix.Cert.recordAt E₀ (Core.ixAddr ab) = some c :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec
  obtain ⟨raw', c', hh', hba', hx', htrace⟩ := Ingress.get_ci_trace_spec hab ev
  have hc' : c' = c := hS.record_eq hrecAt (Core.hashed_mono hsub hh') hba' hx'
  subst c'
  suffices hmain : InLogic c ∧
      ∀ cb, recordOf E₀ (Ix.Cert.ownerOf (Core.ixAddr ab) c) = some cb → InLogic cb by
    intro c₁ hc₁
    rw [Option.some.inj (hc₁.symm.trans hrec)]
    exact hmain
  have tag_ne : ∀ {tag : String} {args : List (SourceValue F)}, tag ≠ "Thm" →
      loadValue h' ptr = .ok (.construct "KernelTypes::KConstantInfo" tag args) → False := by
    intro tag args hne hl
    have hv := Except.ok.inj (hl.symm.trans hld)
    injection hv with _ htag _
    exact hne htag
  cases hci : c.info with
  | muts ms => exact absurd hci (hhead.notMuts ms)
  | defn d =>
    unfold Ingress.GetCITraceResult at htrace
    rw [hci] at htrace
    obtain ⟨blobs, tree, v', -, -, hld', htr⟩ := htrace
    obtain ⟨-, tyPtr, valPtr, hint, -, -, hvshape, -⟩ := htr
    have hv : v' = _ := Except.ok.inj (hld'.symm.trans hld)
    rw [hvshape] at hv
    have hl : InLogic c := by
      simp only [InLogic, hci]
      exact safetyDecline_none_of_thm_shape hv
    exact sourceSafe_self hrec hl (by simp only [Ix.Cert.ownerOf, hci])
  | axio ax =>
    obtain ⟨nl, ty, hldv⟩ := hhead.axio ax hci
    exact (tag_ne (by decide) hldv).elim
  | quot q =>
    obtain ⟨nl, ty, hldv⟩ := hhead.quot q hci
    exact (tag_ne (by decide) hldv).elim
  | recr rcr =>
    obtain ⟨nl, ty, np, ni, nm, nmin, rules, k, x_a, hldv⟩ := hhead.recr rcr hci
    exact (tag_ne (by decide) hldv).elim
  | iPrj p =>
    obtain ⟨i, B⟩ := p
    obtain ⟨cb, ms, ind, -, -, -, nl, ty, np, ni, x_blk, b, hldv, -, -⟩ := hhead.iPrj i B hci
    exact (tag_ne (by decide) hldv).elim
  | rPrj p =>
    obtain ⟨i, B⟩ := p
    obtain ⟨cb, ms, rcr, -, -, nl, ty, np, ni, nm, nmin, rules, k, x_blk, b, hldv, -, -⟩ :=
      hhead.rPrj i B hci
    exact (tag_ne (by decide) hldv).elim
  | cPrj p =>
    obtain ⟨i, j, B⟩ := p
    obtain ⟨cb, ms, ind, -, -, -, ctor, -, nl, ty, ci, np, nf, x_blk, b, hldv, -, -⟩ :=
      hhead.cPrj i j B hci
    exact (tag_ne (by decide) hldv).elim
  | dPrj p =>
    have hk := get_ci_dprj_kinds_at hS hrec hci ⟨ab, hab, rfl⟩ ev hsub
    obtain ⟨i, B⟩ := p
    obtain ⟨cb, ms, d, hbl, hmem⟩ := hhead.dPrj i B hci
    unfold Ingress.GetCITraceResult at htrace
    rw [hci] at htrace
    obtain ⟨-, blkBytes, cbt, mst, dt, blobs, tree, v', hhb, hbb, hxb, hinfot, hmemt, -, -, hld',
      htr⟩ := htrace
    obtain ⟨hrecB, -⟩ := (hbl.mono hsub).stored hH
    have hcbeq : cbt = cb := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hrecB)
      (Core.hashed_mono hsub hhb) hbb hxb
    subst cbt
    have hms : mst = ms := Ixon.ConstantInfo.muts.inj (hinfot.symm.trans hbl.info)
    subst mst
    have hdt : dt = d := Ixon.MutConst.defn.inj (Option.some.inj (hmemt.symm.trans hmem))
    subst dt
    obtain ⟨-, tyPtr, valPtr, hint, -, -, hvshape, -⟩ := htr
    have hv : v' = _ := Except.ok.inj (hld'.symm.trans hld)
    rw [hvshape] at hv
    have hsd := safetyDecline_none_of_thm_shape hv
    refine ⟨inLogic_proj (.inl ⟨_, hci⟩), fun cb' hcb' => ?_⟩
    have hown : Ix.Cert.ownerOf (Core.ixAddr ab) c = B := by simp only [Ix.Cert.ownerOf, hci]
    rw [hown] at hcb'
    exact BlockLoad.inLogic hS hH (hbl.mono hsub) hk
      ⟨.defn d, List.mem_of_getElem? hmem, hsd⟩ cb' hcb'

end IxVM.Refinement.Claim

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

set_option maxRecDepth 100000 in
private theorem roleHasEquations_of_kind5 (r : Ix.Kernel.Role) :
    RoleVal.roleSpecKindNat r = 5 → RoleVal.roleHasEquations r = true := by
  cases r <;> decide

set_option maxRecDepth 100000 in
private theorem eqnsAnchor_specKind_one (r ar : Ix.Kernel.Role) :
    ar ∈ RoleVal.eqnsAnchorsOf r → RoleVal.roleSpecKindNat ar = 1 := by
  have hall : ∀ r, (RoleVal.eqnsAnchorsOf r).all (fun x => RoleVal.roleSpecKindNat x == 1) = true := by
    intro r; cases r <;> decide
  intro h
  exact beq_iff_eq.mp (List.all_eq_true.mp (hall r) ar h)

/-- **The walked roots and the equation theorems of a run are in Lean's logic**
(`RootsAndTheoremsSafe`), for a run that validates every role of the 77 groups and has a
collision-free store, with no further premise. -/
theorem rootsAndTheoremsSafe_of_run {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} (hC : CollisionFreeRun calls E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r) :
    RootsAndTheoremsSafe t E₀ where
  bound := by
    intro r hw a had
    have hv := hval _ (groupOf_lt_groups r) r (role_mem_roleGroup r)
    have hv' : RoleVal.ValidateRoleIn calls bAddr t (Ix.SpecDigest.groupOf r) r := hv
    obtain ⟨a', had', hsafe⟩ :=
      RoleVal.ValidateRoleIn.bound_load_safe hv' (RoleVal.roleSpecKind_of_walked r hw)
    obtain ⟨a'', recs, had'', hcl, hmem⟩ := RoleVal.ValidateRoleIn.lim_walks hv' hw
    have e1 : a' = a := Option.some.inj (had'.symm.trans had)
    have e2 : a'' = a := Option.some.inj (had''.symm.trans had)
    subst e1 e2
    exact Claim.sourceSafe_of_bound_load hC.runStore hC.hashedStored hcl hmem hsafe
  eqnsEvidence := by
    intro r arr thm h5 hm hthm
    have hv := hval _ (groupOf_lt_groups r) r (role_mem_roleGroup r)
    obtain ⟨⟨a, had, -, -, heqns⟩, -⟩ := RoleValidationIn.walks hv
    obtain ⟨arr₀, hm₀, -, hprf⟩ := heqns (roleHasEquations_of_kind5 r h5)
    have harr : arr = arr₀ := RoleVal.evidence_eq_of_wf hv.wf hm hm₀
    subst harr
    exact Claim.sourceSafe_of_thm_load hC.runStore hC.hashedStored (hprf thm hthm).1
  eqnsAnchors := by
    intro r ar a h5 har had
    have hvAr := hval _ (groupOf_lt_groups ar) ar (role_mem_roleGroup ar)
    have hvAr' : RoleVal.ValidateRoleIn calls bAddr t (Ix.SpecDigest.groupOf ar) ar := hvAr
    obtain ⟨a', had', hsafe⟩ :=
      RoleVal.ValidateRoleIn.bound_load_safe hvAr' (Or.inr (Or.inl (eqnsAnchor_specKind_one r ar har)))
    have hvR := hval _ (groupOf_lt_groups r) r (role_mem_roleGroup r)
    have hvR' : RoleVal.ValidateRoleIn calls bAddr t (Ix.SpecDigest.groupOf r) r := hvR
    obtain ⟨a'', recs, had'', hcl, hmem⟩ := RoleVal.ValidateRoleIn.eqns_anchors_walks hvR' h5 har
    have e1 : a' = a := Option.some.inj (had'.symm.trans had)
    have e2 : a'' = a := Option.some.inj (had''.symm.trans had)
    subst e1 e2
    exact Claim.sourceSafe_of_bound_load hC.runStore hC.hashedStored hcl hmem hsafe

end IxVM.Refinement.Binding
