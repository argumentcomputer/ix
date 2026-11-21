import IxVMRefinement.Nat.PrimInt

/-! # Step lemmas of `KernelNatPrim`: `BitVec` natives (`BitVec.toNat`, `BitVec.ult`)

Each `BitVec` accelerator extracts the width `w` (`try_extract_nat_or_whnf`) and checks that each
`BitVec.ofNat vw n` operand agrees with `w` (`KernelLevels::klimbs_eq`), capping `w ≤ 2^24` before
calling `klimbs_pow`. Under `PrimEqnEnv`, the resulting reductions match `bitVecToNat` and
`bitVecUlt` from the validated `BitVec` equations. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red)
open NatAux

set_option linter.unusedVariables false

namespace PrimBitVecAux

theorem bvPrimOp_group_ge46 {ro : Ix.Kernel.Role} {o : Nat}
    (h : Specs.Nat.bvPrimOp ro = some o) : 46 ≤ Ix.SpecDigest.groupOf ro := by
  cases ro <;> simp [Specs.Nat.bvPrimOp] at h <;> decide

theorem bvPrimOp_eq_of_val {ro : Ix.Kernel.Role} {o : Nat}
    (h : Specs.Nat.bvPrimOp ro = some o) :
    (o = 1 → ro = .bitVecToNat) ∧ (o = 2 → ro = .bitVecUlt) := by
  cases ro <;> simp [Specs.Nat.bvPrimOp] at h <;> subst h <;> decide

theorem bvOpAt_key_and_prim {c : ScopedCtx} (hc : ScopedCoreBase c) {a : Bytes.Address} {o : Nat}
    {ro : Ix.Kernel.Role} (hro : Specs.Nat.bvPrimOp ro = some o)
    (haddr : c.t.addressOf? ro = some (ixAddr a)) (hforce : c.inForce ro) :
    PrimEqnEnv c.env ∧ c.κ (ixAddr a) = .role ro := by
  have hprim := hc.env.primEqn ⟨ro, bvPrimOp_group_ge46 hro, hforce⟩
  have hmem : ro ∈ [.bitVecToNat, .bitVecUlt] := by
    cases ro <;> simp [Specs.Nat.bvPrimOp] at hro <;> decide
  obtain ⟨ci, hci⟩ := hprim.bitVecOpStored ro hmem
  have hres : c.κ (ixAddr a) ≠ unresolvedKey :=
    hc.loads.storedRes (ixAddr a) ci (by rw [keyOf_of_addressOf hc.env.tableWf haddr]; exact hci)
  exact ⟨hprim, (c.key_eq hres).trans (keyOf_of_addressOf hc.env.tableWf haddr)⟩

theorem sub_one_bool_ite (a b : Nat) :
    (if (1 : F) - (if b ≤ a then (1 : F) else 0) = 0 then Ix.Kernel.boolFalseName (md := .anon)
      else Ix.Kernel.boolTrueName) =
    (if a < b then Ix.Kernel.boolTrueName else Ix.Kernel.boolFalseName) := by
  by_cases h : a < b
  · have hle : ¬ b ≤ a := Nat.not_le.mpr h
    simp [h, hle]
  · have hle : b ≤ a := Nat.le_of_not_lt h
    simp [h, hle]

end PrimBitVecAux

open PrimBitVecAux

/-- `KernelNatPrim::bitvec_of_nat_args_direct(rc, e)`. -/
theorem bitvec_of_nat_args_direct_step (c : ScopedCtx) (hc : ScopedCoreBase c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::bitvec_of_nat_args_direct" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.bitvec_of_nat_args_direct c args h r h' calls := by
  intro rc e hargs good hrc d Γ E hE we ne hr
  subst hargs
  cases Obs.«KernelNatPrim::bitvec_of_nat_args_direct».obs ev with
  | App_App_Const_n1_n1 x_f1 x_n_e x_f0 x_w_e x_caddr x_clvls m1 cs1 m3 cs3 v_ron m2 cs2
      ld_e ld_f1 ld_f0 ev_le ev_ron ev_ris he_r he_h hc_c =>
    subst hc_c he_h
    obtain ⟨rfl, rfl⟩ := PrimNat.tag3_snd (hr.symm.trans he_r)
    obtain ⟨Ef1, En, rfl, hf1, hn⟩ := Tm.app_of_load hE ld_e
    obtain ⟨Ef0, Ew, rfl, hf0, hw⟩ := Tm.app_of_load hf1 ld_f1
    obtain ⟨a, us, rfl, ha_addr, hus⟩ := Tm.const_of_load hf0 ld_f0
    obtain ⟨hle, rfl⟩ := ih.get (.nat .lvls_empty) (by nat_lt_calls) ev_le x_clvls rfl
      (good.sub fun x hx => by simp [hx]) us hus
    have hus_nil : us = [] := by
      by_contra hne; rw [ite_eq_right hne] at hle; exact field_one_ne_zero hle
    subst hus_nil
    obtain ⟨hv_ron, hm2⟩ := ih.get (.roles .role_bit_vec_of_nat) (by nat_lt_calls) ev_ron rfl
    subst hv_ron hm2
    have ⟨hb_on, _⟩ := ih.get (.roles .role_is) (by nat_lt_calls) ev_ris rc x_caddr a .bitVecOfNat
      rfl (good.sub fun x hx => by simp [hx]) hrc ha_addr field_one_ne_zero
    have e3 := ObsFn.heap_extends ev_ris
    have hk : c.κ (ixAddr a) = .role .bitVecOfNat :=
      (c.key_eq (by resolve_key)).trans (keyOf_of_addressOf hc.env.tableWf hb_on)
    rw [hk]
    exact ⟨Ew, En, rfl, Tm.mono e3 hw, Tm.mono e3 hn⟩
  | App_App_Const_n1_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he_r _ _ _ _ =>
    exact (PrimInt.tag_tuple3_ne (hr.symm.trans he_r)).elim
  | App_App_Const_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he_r _ _ _ _ =>
    exact (PrimInt.tag_tuple3_ne (hr.symm.trans he_r)).elim
  | App_App_other _ _ _ _ _ _ _ _ _ _ _ he_r _ _ _ _ =>
    exact (PrimInt.tag_tuple3_ne (hr.symm.trans he_r)).elim
  | App_other _ _ _ _ _ _ _ _ he_r _ _ _ _ =>
    exact (PrimInt.tag_tuple3_ne (hr.symm.trans he_r)).elim
  | other _ _ _ _ _ he_r _ _ _ _ =>
    exact (PrimInt.tag_tuple3_ne (hr.symm.trans he_r)).elim

/-- `KernelNatPrim::bv_extract_of_nat(rc, val_e, types)`. -/
theorem bv_extract_of_nat_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::bv_extract_of_nat" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.bv_extract_of_nat c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE we ne hr
  subst hargs
  cases Obs.«KernelNatPrim::bv_extract_of_nat».obs ev with
  | n1_bind_bind m1 cs1 x_vw x_n ev_dir he_r he_h hc_c =>
    subst hc_c he_h
    obtain ⟨rfl, rfl⟩ := PrimNat.tag3_snd (hr.symm.trans he_r)
    obtain ⟨Ew, En, hEq, hw, hn⟩ := ih.get (.nat .bitvec_of_nat_args_direct) (by nat_lt_calls)
      ev_dir rc e rfl (good.sub fun x hx => by simp [hx]) hrc d Γ E hE we ne rfl
    exact ⟨Ew, En, hEq ▸ .refl, hw, hn⟩
  | other v1 m1 cs1 cs3 v2 m2 cs2 ev_dir1 ev_whnf ev_dir2 hc_c =>
    subst hc_c
    have e1 := ObsFn.heap_extends ev_dir1
    obtain ⟨E', hE', hred⟩ := ih.get (.whnf .whnf_nd) (by nat_lt_calls) ev_whnf rc e types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) E
      (Tm.mono e1 hE)
    have e2 := ObsFn.heap_extends ev_whnf
    obtain ⟨Ew, En, hEq, hw, hn⟩ := ih.get (.nat .bitvec_of_nat_args_direct) (by nat_lt_calls)
      ev_dir2 rc v2 rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono (e1.trans e2) hrc) d Γ E'
      hE' we ne hr
    exact ⟨Ew, En, hEq ▸ hred, hw, hn⟩

/-- `KernelNatPrim::bv_extract_checked_val(rc, w_kl, val_e, types)`. -/
theorem bv_extract_checked_val_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::bv_extract_checked_val" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.bv_extract_checked_val c args h r h' calls := by
  intro rc wkl e types hargs good hrc w hw d Γ htypes E hE x hr
  subst hargs
  cases Obs.«KernelNatPrim::bv_extract_checked_val».obs ev with
  | n1_bind_bind_n1_bind_n1 m1 cs1 x_vw x_n m2 cs2 x_vw_kl m3 cs3 cs4
      ev_ofnat ev_w ev_eq ev_n hc_c =>
    subst hc_c
    obtain ⟨Ew, En, hred0, hEw, hEn⟩ := ih.get (.nat .bv_extract_of_nat) (by nat_lt_calls) ev_ofnat
      rc e types rfl (good.sub fun z hz => by simp [hz]) hrc d Γ htypes E hE x_vw x_n rfl
    have e1 := ObsFn.heap_extends ev_ofnat
    obtain ⟨vw, hvw, hredW⟩ := ih.get (.nat .try_extract_nat_or_whnf) (by nat_lt_calls) ev_w
      rc x_vw types rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono e1 hrc) d Γ
      (types_mono e1 htypes) Ew hEw x_vw_kl rfl
    have e2 := ObsFn.heap_extends ev_w
    have e12 := e1.trans e2
    obtain ⟨la, hla, hvalA, _⟩ := repLimbsC_mono e12 hw
    obtain ⟨lb, hlb, hvalB, _⟩ := hvw
    obtain ⟨heq, hm3⟩ := ih.get (.levels .klimbs_eq) (by nat_lt_calls) ev_eq wkl x_vw_kl rfl
      (good.sub fun z hz => by simp [hz]) la lb hla hlb
    subst hm3
    have hlab : la = lb := by
      by_contra hne; rw [ite_eq_right hne] at heq; exact field_one_ne_zero heq
    have hvw_eq : vw = w := by rw [← hvalB, ← hlab, hvalA]
    subst hvw_eq
    obtain ⟨n, hn, hredN⟩ := ih.get (.nat .try_extract_nat_or_whnf) (by nat_lt_calls) ev_n
      rc x_n types rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono e12 hrc) d Γ
      (types_mono e12 htypes) En (Tm.mono e2 hEn) x hr
    refine ⟨n, hn, .trans hred0 (.trans (.appFn (.appArg hredW)) (.appArg hredN))⟩
  | n1_bind_bind_n1_bind_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he_r _ _ _ =>
    exact (PrimInt.tag_tuple2_ne (hr.symm.trans he_r)).elim
  | n1_bind_bind_other _ _ _ _ _ _ _ _ _ _ he_r _ _ _ =>
    exact (PrimInt.tag_tuple2_ne (hr.symm.trans he_r)).elim
  | other _ _ _ _ _ he_r _ _ _ =>
    exact (PrimInt.tag_tuple2_ne (hr.symm.trans he_r)).elim

/-- `KernelNatPrim::try_bitvec_to_nat(rc, width_e, val_e, post, types)`. -/
theorem try_bitvec_to_nat_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_bitvec_to_nat" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_bitvec_to_nat c args h r h' calls := by
  intro rc we ve post types hargs good hrc hprim d Γ htypes W V Ps hW hV hPs t x hr ht
  subst hargs
  cases Obs.«KernelNatPrim::try_bitvec_to_nat».obs ev with
  | n1_bind_n1_bind_n1 m1 cs1 x_w m2 cs2 x_n m_cap1 m_cap0 m3 cs3 m_two1 m_two0 v_mod m4 cs4
      v_out m7 cs7 v_lit m6 cs6 v_rem m5 cs5
      ev_w ev_v hm_cap1 hm_cap0 ev_le hm_two1 hm_two0 ev_pow he_r ev_mod ev_lit ev_app he_h hc_c =>
    subst hc_c he_h
    obtain rfl : x = v_out := PrimNat.tag_snd (hr.symm.trans he_r)
    obtain ⟨w, hw, hredW⟩ := ih.get (.nat .try_extract_nat_or_whnf) (by nat_lt_calls) ev_w
      rc we types rfl (good.sub fun z hz => by simp [hz]) hrc d Γ htypes W hW x_w rfl
    have e1 := ObsFn.heap_extends ev_w
    obtain ⟨n, hn, hredV⟩ := ih.get (.nat .bv_extract_checked_val) (by nat_lt_calls) ev_v
      rc x_w ve types rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono e1 hrc) w hw d Γ
      (types_mono e1 htypes) V (Tm.mono e1 hV) x_n rfl
    have e2 := ObsFn.heap_extends ev_v
    have e_cap : Heap.Extends m2 m_cap1 :=
      (Heap.Extends.snoc m2 _).trans (hm_cap0 ▸ hm_cap1 ▸ Heap.Extends.snoc m_cap0 _)
    have hcap := PrimInt.repLimbs_pow24 hm_cap0 hm_cap1
    have hle := ih.get (.nat .klimbs_le) (by nat_lt_calls) ev_le x_w _ rfl
      (good.sub fun z hz => by simp [hz]) w (2 ^ 24)
      (RepLimbsC.toRepLimbs (repLimbsC_mono (e2.trans e_cap) hw)) hcap
    have hw_le : w ≤ 2 ^ 24 := by
      by_contra hgt; rw [ite_eq_right hgt] at hle; exact field_one_ne_zero hle
    have e3 := ObsFn.heap_extends ev_le
    have e_two : Heap.Extends m3 m_two1 :=
      (Heap.Extends.snoc m3 _).trans (hm_two0 ▸ hm_two1 ▸ Heap.Extends.snoc m_two0 _)
    have htwo := PrimInt.repLimbs_two hm_two0 hm_two1
    have e_w_to_pow := ((e2.trans e_cap).trans e3).trans e_two
    have hpow := ih.get (.nat .klimbs_pow) (by nat_lt_calls) ev_pow _ x_w rfl
      (good.sub fun z hz => by simp [hz]) 2 w htwo
      (RepLimbsC.toRepLimbs (repLimbsC_mono e_w_to_pow hw))
    have e4 := ObsFn.heap_extends ev_pow
    have e_n_to_mod := ((e_cap.trans e3).trans e_two).trans e4
    have hrem := ih.get (.nat .klimbs_mod) (by nat_lt_calls) ev_mod x_n v_mod rfl
      (good.sub fun z hz => by simp [hz]) n (2 ^ w)
      (RepLimbsC.toRepLimbs (repLimbsC_mono e_n_to_mod hn)) hpow
    have hlit := ih.get (.nat .mk_nat_lit) (by nat_lt_calls) ev_lit v_rem rfl
      (good.sub fun z hz => by simp [hz]) (n % 2 ^ w) hrem
    have e_all := ((e1.trans e2).trans e_n_to_mod).trans
      ((ObsFn.heap_extends ev_mod).trans (ObsFn.heap_extends ev_lit))
    have happ := ih.get (.nat .np_apply_spine) (by nat_lt_calls) ev_app v_lit post rfl
      (good.sub fun z hz => by simp [hz]) d Γ (.lit (.natVal (n % 2 ^ w))) Ps
      (hlit d Γ) (TmL.mono e_all hPs)
    refine ⟨_, happ, ?_⟩
    exact PrimNat.red_mkAppN₂ Ps
      (.trans (.appFn (.appArg hredW)) (.trans (.appArg hredV) (hprim.bitVecToNat d w n hw_le)))
  | n1_bind_n1_bind_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he_r _ _ _ =>
    exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  | n1_bind_other _ _ _ _ _ _ _ _ _ he_r _ _ _ =>
    exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  | other _ _ _ _ _ he_r _ _ _ =>
    exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht

/-- `KernelNatPrim::try_bitvec_ult(rc, width_e, lhs_e, rhs_e, post, types)`. -/
theorem try_bitvec_ult_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_bitvec_ult" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_bitvec_ult c args h r h' calls := by
  intro rc we le re post types hargs good hrc hprim d Γ htypes W L R Ps hW hL hR hPs t x hr ht
  subst hargs
  cases Obs.«KernelNatPrim::try_bitvec_ult».obs ev with
  | n1_bind_n1_bind_n1_bind_n1 m1 cs1 x_w m2 cs2 x_ln m3 cs3 x_rn m_cap1 m_cap0 m4 cs4
      m_two1 m_two0 v_mod m5 cs5 v_lrem m6 cs6 v_rrem m7 cs7 v_sub m8 v_cmp cs8
      v_out m10 cs10 v_bool m9 cs9
      ev_w ev_l ev_r hm_cap1 hm_cap0 ev_le hm_two1 hm_two0 ev_pow ev_lmod ev_rmod ev_cmp
      op_sub he_r ev_bool ev_app he_h hc_c =>
    subst hc_c he_h
    obtain rfl : x = v_out := PrimNat.tag_snd (hr.symm.trans he_r)
    obtain ⟨w, hw, hredW⟩ := ih.get (.nat .try_extract_nat_or_whnf) (by nat_lt_calls) ev_w
      rc we types rfl (good.sub fun z hz => by simp [hz]) hrc d Γ htypes W hW x_w rfl
    have e1 := ObsFn.heap_extends ev_w
    obtain ⟨n₁, hn₁, hredL⟩ := ih.get (.nat .bv_extract_checked_val) (by nat_lt_calls) ev_l
      rc x_w le types rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono e1 hrc) w hw d Γ
      (types_mono e1 htypes) L (Tm.mono e1 hL) x_ln rfl
    have e2 := ObsFn.heap_extends ev_l
    have e12 := e1.trans e2
    obtain ⟨n₂, hn₂, hredR⟩ := ih.get (.nat .bv_extract_checked_val) (by nat_lt_calls) ev_r
      rc x_w re types rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono e12 hrc) w
      (repLimbsC_mono e2 hw) d Γ (types_mono e12 htypes) R (Tm.mono e12 hR) x_rn rfl
    have e3 := ObsFn.heap_extends ev_r
    have e_cap : Heap.Extends m3 m_cap1 :=
      (Heap.Extends.snoc m3 _).trans (hm_cap0 ▸ hm_cap1 ▸ Heap.Extends.snoc m_cap0 _)
    have hcap := PrimInt.repLimbs_pow24 hm_cap0 hm_cap1
    have hle := ih.get (.nat .klimbs_le) (by nat_lt_calls) ev_le x_w _ rfl
      (good.sub fun z hz => by simp [hz]) w (2 ^ 24)
      (RepLimbsC.toRepLimbs (repLimbsC_mono ((e2.trans e3).trans e_cap) hw)) hcap
    have hw_le : w ≤ 2 ^ 24 := by
      by_contra hgt; rw [ite_eq_right hgt] at hle; exact field_one_ne_zero hle
    have e4 := ObsFn.heap_extends ev_le
    have e_two : Heap.Extends m4 m_two1 :=
      (Heap.Extends.snoc m4 _).trans (hm_two0 ▸ hm_two1 ▸ Heap.Extends.snoc m_two0 _)
    have htwo := PrimInt.repLimbs_two hm_two0 hm_two1
    have e_m3_to_two := (e_cap.trans e4).trans e_two
    have hpow := ih.get (.nat .klimbs_pow) (by nat_lt_calls) ev_pow _ x_w rfl
      (good.sub fun z hz => by simp [hz]) 2 w htwo
      (RepLimbsC.toRepLimbs (repLimbsC_mono ((e2.trans e3).trans e_m3_to_two) hw))
    have e5 := ObsFn.heap_extends ev_pow
    have hpow_m5 := hpow
    have hlrem := ih.get (.nat .klimbs_mod) (by nat_lt_calls) ev_lmod x_ln v_mod rfl
      (good.sub fun z hz => by simp [hz]) n₁ (2 ^ w)
      (RepLimbsC.toRepLimbs (repLimbsC_mono ((e3.trans e_m3_to_two).trans e5) hn₁)) hpow_m5
    have e6 := ObsFn.heap_extends ev_lmod
    have hrrem := ih.get (.nat .klimbs_mod) (by nat_lt_calls) ev_rmod x_rn v_mod rfl
      (good.sub fun z hz => by simp [hz]) n₂ (2 ^ w)
      (RepLimbsC.toRepLimbs (repLimbsC_mono ((e_m3_to_two.trans e5).trans e6) hn₂))
      (repLimbs_mono e6 hpow_m5)
    have e7 := ObsFn.heap_extends ev_rmod
    have hcmp := ih.get (.nat .klimbs_le) (by nat_lt_calls) ev_cmp v_rrem v_lrem rfl
      (good.sub fun z hz => by simp [hz]) (n₂ % 2 ^ w) (n₁ % 2 ^ w)
      (RepLimbsC.toRepLimbs hrrem) (RepLimbsC.toRepLimbs (repLimbsC_mono e7 hlrem))
    subst hcmp
    simp only [evalBinOp, Except.ok.injEq] at op_sub
    subst op_sub
    have e8 := ObsFn.heap_extends ev_cmp
    have e_to_m8 := ((((e12.trans e3).trans e_m3_to_two).trans e5).trans e6).trans (e7.trans e8)
    have hbool := ih.get (.nat .mk_bool) (by nat_lt_calls) ev_bool rc _ rfl
      (good.sub fun z hz => by simp [hz]) (RCRep.mono e_to_m8 hrc)
    rw [sub_one_bool_ite] at hbool
    have e9 := ObsFn.heap_extends ev_bool
    have happ := ih.get (.nat .np_apply_spine) (by nat_lt_calls) ev_app v_bool post rfl
      (good.sub fun z hz => by simp [hz]) d Γ _ Ps (hbool d Γ) (TmL.mono (e_to_m8.trans e9) hPs)
    refine ⟨_, happ, ?_⟩
    have h3 : Red c.env d (.app (.app (.app (.const (.role .bitVecUlt) []) W) L) R)
        (.const (if n₁ % 2 ^ w < n₂ % 2 ^ w then Ix.Kernel.boolTrueName
          else Ix.Kernel.boolFalseName) []) :=
      .trans (.appFn (.appFn (.appArg hredW)))
        (.trans (.appFn (.appArg hredL))
          (.trans (.appArg hredR) (hprim.bitVecUlt d w n₁ n₂ hw_le)))
    exact PrimNat.red_mkAppN Ps h3
  | n1_bind_n1_bind_n1_bind_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he_r _ _ _ =>
    exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  | n1_bind_n1_bind_other _ _ _ _ _ _ _ _ _ _ _ _ _ he_r _ _ _ =>
    exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  | n1_bind_other _ _ _ _ _ _ _ _ _ he_r _ _ _ =>
    exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  | other _ _ _ _ _ he_r _ _ _ =>
    exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht

/-- `KernelNatPrim::try_bitvec_dispatch(rc, op, spine, types)`. -/
theorem try_bitvec_dispatch_step (c : ScopedCtx) (hc : ScopedCoreBase c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_bitvec_dispatch" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_bitvec_dispatch c args h r h' calls := by
  intro rc o sp types hargs good hrc headAddr hop d Γ htypes As hAs t x hr ht
  subst hargs
  obtain ⟨ro, hro, haddr, hforce⟩ := hop
  cases Obs.«KernelNatPrim::try_bitvec_dispatch».obs ev with
  | Cons_Cons_n1 x_w x_r0 x_a1 x_r1 cs1 ld0 ld1 hv1 ev_op hc_c =>
    subst hc_c
    obtain ⟨W, As0, rfl, hW, hAs0⟩ := RepList.cons_of_load hAs ld0
    obtain ⟨V, Ps, rfl, hV, hPs⟩ := RepList.cons_of_load hAs0 ld1
    have ho1 : ZMod.val o = 1 := PrimInt.field_val_eq_nat (by omega) (Value.field.inj hv1)
    obtain rfl : ro = .bitVecToNat := (bvPrimOp_eq_of_val hro).1 ho1
    obtain ⟨hprim, hkey⟩ := bvOpAt_key_and_prim hc hro haddr hforce
    rw [hkey]
    exact ih.get (.nat .try_bitvec_to_nat) (by nat_lt_calls) ev_op rc x_w x_a1 x_r1 types rfl
      (good.sub fun z hz => by simp [hz]) hrc hprim d Γ htypes W V Ps hW hV hPs t x hr ht
  | Cons_Cons_n2_Cons x_w x_r0 x_a1 x_r1 x_a2 x_r2 cs1 ld0 ld1 _ hv2 ld2 ev_op hc_c =>
    subst hc_c
    obtain ⟨W, As0, rfl, hW, hAs0⟩ := RepList.cons_of_load hAs ld0
    obtain ⟨L, As1, rfl, hL, hAs1⟩ := RepList.cons_of_load hAs0 ld1
    obtain ⟨R, Ps, rfl, hR, hPs⟩ := RepList.cons_of_load hAs1 ld2
    have ho2 : ZMod.val o = 2 := PrimInt.field_val_eq_nat (by omega) (Value.field.inj hv2)
    obtain rfl : ro = .bitVecUlt := (bvPrimOp_eq_of_val hro).2 ho2
    obtain ⟨hprim, hkey⟩ := bvOpAt_key_and_prim hc hro haddr hforce
    rw [hkey]
    exact ih.get (.nat .try_bitvec_ult) (by nat_lt_calls) ev_op rc x_w x_a1 x_a2 x_r2 types rfl
      (good.sub fun z hz => by simp [hz]) hrc hprim d Γ htypes W L R Ps hW hL hR hPs t x hr ht
  | Cons_Cons_n2_other _ _ _ _ _ _ _ _ _ _ _ _ he_r _ _ _ =>
    exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  | Cons_Cons_other _ _ _ _ _ _ _ _ _ he_r _ _ _ =>
    exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  | Cons_other _ _ _ _ _ _ _ he_r _ _ _ =>
    exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  | other _ _ _ _ he_r _ _ _ =>
    exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht

end IxVM.Refinement.Core
