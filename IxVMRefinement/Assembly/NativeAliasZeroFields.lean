import IxVMRefinement.Assembly.NativeAliasZero
import IxVMRefinement.Assembly.NativeAliasParamHeads

/-! # Alias constructor zero-ness from actual parameter and field checks

The new parameter-head observations supply the parameter cases. The existing positivity
observations supply the field cases. No external assumption excluding all family occurrences
from parameter domains is used.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (Expr Level LevelParam ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (ctorZeroOk famHead)

set_option maxHeartbeats 2400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem ctor_zero_all_from_fields {t : Ix.Kernel.RoleTable}
    {b₀ a_t : Bytes.Address} {T : KKey} {nP : Nat} {ind_lvl : KLevel}
    {cs_root : List (Call F)} {ctors ctorsA : List (KConstantVal × Nat)}
    {ctorRawTypes : List KExpr}
    (hwf : t.wf = true)
    (hlps_ctors : ∀ c ∈ ctors, c.1.levelParams = List.range c.1.levelParams.length)
    (hT_eq : T = keyOf t (ixAddr a_t))
    (hcload : StagedCtorLoads (keyOf t) t b₀ nP 0 cs_root ctors ctorsA ctorRawTypes)
    (hctor_sp : ∀ k < ctors.length, ∀ c cvCa₀,
      ctors[k]? = some c →
      ctorsA[k]? = some (cvCa₀, c.2) →
      ∃ rcbs rargs cbs eargs us₀,
        (ctorRawTypes.getD k default).stripPis (nP + c.2) =
          some (rcbs, Expr.mkAppN (.const T us₀) rargs) ∧
        cvCa₀.type.stripPis (nP + c.2) =
          some (cbs, Expr.mkAppN (.const T us₀) eargs) ∧
        ∀ idx, nP ≤ idx → idx < nP + c.2,
          famHead T (cbs.getD idx default).1 = false ∨
          RawRecSpine T (rcbs.getD idx default).1 (cbs.getD idx default).1)
    (hnP_lt : nP < 18446744069414584321)
    (hroot : IxVM.Consistency.Bounded cs_root)
    (hnCtors_lt : ctors.length < 549755813888) :
    ∀ (m j : Nat) {bp pt pind r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      m + j = ctors.length →
      (∀ x ∈ cs, x ∈ cs_root) →
      Bytes.RepAddressRef addrTy h b₀ bp →
      Bytes.RepAddressRef addrTy h a_t pt →
      RepKLevel h ind_lvl pind →
      ObsFn W "KernelCheck::ctor_zero_all"
        [bp, .field 0, .field (ctors.length : F), .field (j : F), pt, pind] h r h' cs →
      ∀ k, j ≤ k → k < ctors.length → ∀ cA, ctorsA[k]? = some cA →
        ctorZeroOk T ind_lvl.zeronessOf cA.1.type = true
  | 0, _, _, _, _, _, _, _, _, hmj, _, _, _, _, _, _, hjk, hkt, _, _ => by omega
  | m + 1, j, bp, pt, pind, r, h, h', cs, hmj, hsub, hbp, hpt, hpind, ev, k, hjk, hkt, cA, hcA => by
    match Obs.«KernelCheck::ctor_zero_all».obs ev with
    | .n0 (op17 := op) .. =>
      have hsub_op : (.field ((0 : Nat) : F) : SourceValue F) =
          .field (((ctors.length - j : Nat) : F)) := by
        simpa using evalBinOp_sub_nat (by omega : j ≤ ctors.length) op
      have hj_eq := nat_eq_of_field_eq (by decide) (by omega) hsub_op
      omega
    | .other (m34 := m34) (p41 := p41) (cs47 := cs_cprj) (x_cty := xcty) (cs134 := paramCalls)
        (m162 := m162) (cs202 := cs_rec) (v208 := v208)
        (ev49 := ev_cprj) (ld43 := ld_ctor) (ev136 := ev_params) (ev174 := ev_cz)
        (op245 := op_add) (ev204 := ev_rec) (hc261 := hc) .. =>
      obtain ⟨c_j, cvCa₀, hc_j, hcA_j, hvs_j, hload_j⟩ := hcload.2 j (by omega)
      have hsub_cprj : ∀ x ∈ cs_cprj, x ∈ cs_root := fun x hx => hsub x (by simp [hc, hx])
      have hsub_rec : ∀ x ∈ cs_rec, x ∈ cs_root := fun x hx => hsub x (by simp [hc, hx])
      obtain ⟨nl', cty', cblk', cnp', cnf', _, ld_c', _, _, hraw_rep, hval_rep, hnp, hnf⟩ :=
        hload_j bp p41 h m34 cs_cprj hsub_cprj hbp ev_cprj
      rw [ld_c'] at ld_ctor
      injection ld_ctor with hval; injection hval with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      obtain ⟨-, hcty_eq, -, -, -, hnp_eq, -, -⟩ := h1
      cases hcty_eq.symm
      rw [← hnp_eq, hnp] at ev_params
      have e1 := ev_cprj.heap_extends.trans ev_params.heap_extends
      have e2 := ev_cz.heap_extends
      by_cases hkj : k = j
      · subst hkj
        rw [hcA_j] at hcA
        injection hcA with hcA_eq; subst hcA_eq
        have hlps_cj : cvCa₀.levelParams = List.range cvCa₀.levelParams.length := by
          rw [hvs_j.2.1]
          exact hlps_ctors c_j (List.mem_of_getElem? hc_j)
        have hcty_raw :
            RawTmExact (keyOf t) 0 (fun _ => default) m34 0
              (ctorRawTypes.getD k default) cvCa₀.type xcty := by
          have h0 := hraw_rep 0 (fun _ => default)
          rwa [hlps_cj, posOf_range] at h0
        obtain ⟨rcbs, rargs, cbs, eargs, us₀, hstR, hstE, hfields⟩ :=
          hctor_sp k (by omega) c_j cvCa₀ hc_j hcA_j
        have hκ_inj : ∀ a : Bytes.Address, keyOf t (ixAddr a) = T → ixAddr a = ixAddr a_t := by
          intro a ha
          rw [hT_eq] at ha
          exact nat_keyOf_injective hwf ha
        have hparams := alias_parameter_heads_spec
          (fun a ha => ixAddr_inj (hκ_inj a ha)) nP hnP_lt
          (bounded_sub (fun cl hx => hsub cl (by simp [hc, hx])) hroot)
          hcty_raw.toTm (Bytes.repAddressRef_heapMono₂ addrTy ev_cprj.heap_extends hpt) ev_params
        obtain ⟨cbsP, cbodyP, cbsF, hstP, -, happ, hlenP⟩ := stripPis_split nP c_j.2 hstE
        have hdoms : ∀ idx < nP + c_j.2,
            famHead T (cbs.getD idx default).1 = false ∨
              RawRecSpine T (rcbs.getD idx default).1 (cbs.getD idx default).1 := by
          intro idx hi
          by_cases hp : idx < nP
          · left
            have he : cbs[idx]? = cbsP[idx]? := by
              rw [← happ, List.getElem?_append_left (by omega)]
            rw [List.getD_eq_getElem?_getD, he, ← List.getD_eq_getElem?_getD]
            exact hparams.domains hstP idx hp
          · exact hfields idx (by omega) hi
        exact ctor_zero_ok_head_go hκ_inj (nP + c_j.2) hstR hstE hdoms (hcty_raw.mono ev_params.heap_extends)
          (Bytes.repAddressRef_heapMono₂ addrTy e1 hpt)
          (repKLevel_heapMono₂ e1 hpind) ev_cz
      · have hv171 : v208 = .field ((j + 1 : Nat) : F) := evalBinOp_add_nat j 1 op_add
        rw [hv171] at ev_rec
        exact ctor_zero_all_from_fields hwf hlps_ctors hT_eq hcload hctor_sp hnP_lt hroot hnCtors_lt
          m (j + 1) (by omega) hsub_rec
          (Bytes.repAddressRef_heapMono₂ addrTy (e1.trans e2) hbp)
          (Bytes.repAddressRef_heapMono₂ addrTy (e1.trans e2) hpt)
          (repKLevel_heapMono₂ (e1.trans e2) hpind) ev_rec
          k (by omega) hkt cA hcA

theorem former_decl_ok_observed_from_fields {c : Ctx}
    {b₀ : Bytes.Address} {T : KKey} {nP nIdx : Nat} {ty : KExpr} {ind_lvl : KLevel}
    {cs_root : List (Call F)} {ctors ctorsA : List (KConstantVal × Nat)}
    {ctorRawTypes : List KExpr}
    {pty bp pind r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hwf : c.t.wf = true)
    (hnPI_lt : nP + nIdx < 18446744069414584321)
    (hnCtors_lt : ctors.length < 549755813888)
    (hroot : IxVM.Consistency.Bounded cs_root)
    (hT_iprj : T = c.κ (iprjAddr (ixAddr b₀) 0))
    (hlps_ctors : ∀ cb ∈ ctors, cb.1.levelParams = List.range cb.1.levelParams.length)
    (hcload : StagedCtorLoads (keyOf c.t) c.t b₀ nP 0 cs_root ctors ctorsA ctorRawTypes)
    (hctor_sp : ∀ k < ctors.length, ∀ c cvCa₀,
      ctors[k]? = some c →
      ctorsA[k]? = some (cvCa₀, c.2) →
      ∃ rcbs rargs cbs eargs us₀,
        (ctorRawTypes.getD k default).stripPis (nP + c.2) =
          some (rcbs, Expr.mkAppN (.const T us₀) rargs) ∧
        cvCa₀.type.stripPis (nP + c.2) =
          some (cbs, Expr.mkAppN (.const T us₀) eargs) ∧
        ∀ idx, nP ≤ idx → idx < nP + c.2,
          famHead T (cbs.getD idx default).1 = false ∨
          RawRecSpine T (rcbs.getD idx default).1 (cbs.getD idx default).1)
    (hsub : ∀ x ∈ cs, x ∈ cs_root)
    (hgood : Good c cs)
    (hty : TmExact c.κ 0 (fun _ => default) h 0 ty pty)
    (hbp : Bytes.RepAddressRef addrTy h b₀ bp)
    (hpind : RepKLevel h ind_lvl pind)
    (ev : ObsFn W "KernelCheck::former_decl_ok"
      [pty, .field (nP : F), .field (nIdx : F), .field (ctors.length : F),
        bp, .field 0, pind] h r h' cs) :
    (∃ testAfter testCalls, ObsFn W "KernelCheck::former_is_tele"
      [pty, .field ((nP + nIdx : Nat) : F)] h (.field 1) testAfter testCalls) ∨
    (nIdx ≠ 0 ∧ ∀ k < ctorsA.length, ∀ cA, ctorsA[k]? = some cA →
      ctorZeroOk T ind_lvl.zeronessOf cA.1.type = true) := by
  match Obs.«KernelCheck::former_decl_ok».obs ev with
  | .n1 (m2 := testAfter) (cs13 := testCalls) (v17 := v17) (op38 := op_add) (ev15 := ev_tele) .. =>
    have hv17 : v17 = .field ((nP + nIdx : Nat) : F) := evalBinOp_add_nat nP nIdx op_add
    rw [hv17] at ev_tele
    exact Or.inl ⟨testAfter, testCalls, ev_tele⟩
  | .other (m2 := m2) (v65 := v65) (m68 := m68)
      (cs97 := cs_cz) (v104 := v104) (m134 := m134) (cs142 := cs_ip)
      (ev15 := ev_tele) (ev78 := ev_iz) (heq93 := hv65)
      (ev144 := ev_iprj) (ev99 := ev_cz) (hc168 := hc) .. =>
    subst hv65
    obtain ⟨hiz, _⟩ := Lib.is_zero_spec ev_iz
    have hnIdx_ne : nIdx ≠ 0 := by
      intro h0
      subst h0
      simp at hiz
    have e1 := ev_tele.heap_extends
    have e2 := ev_iz.heap_extends
    have hg_ip : Good c cs_ip := hgood.sub (fun x hx => by simp [hc, hx])
    obtain ⟨a_t, ha_t, hix_t⟩ :=
      compute_iprj_addr_spec (idx := 0) (by omega)
        (Bytes.repAddressRef_heapMono₂ addrTy (e1.trans e2) hbp) hg_ip ev_iprj
    have e3 := ev_iprj.heap_extends
    have hT_at : T = keyOf c.t (ixAddr a_t) := by
      rw [hT_iprj, hix_t]
    have hsub_cz : ∀ x ∈ cs_cz, x ∈ cs_root := fun x hx => hsub x (by simp [hc, hx])
    have hcz := ctor_zero_all_from_fields hwf hlps_ctors hT_at hcload hctor_sp (by omega) hroot hnCtors_lt
      ctors.length 0 (by omega) hsub_cz
      (Bytes.repAddressRef_heapMono₂ addrTy (e1.trans (e2.trans e3)) hbp)
      ha_t
      (repKLevel_heapMono₂ (e1.trans (e2.trans e3)) hpind) ev_cz
    exact Or.inr ⟨hnIdx_ne, fun k hk cA hcA =>
      hcz k (Nat.zero_le k) (by rw [← hcload.1]; exact hk) cA hcA⟩



/-- The semantic shape-or-zero result follows from the actual guard alternative. -/
theorem former_decl_ok_from_fields {c : Ctx}
    {b₀ : Bytes.Address} {T : KKey} {nP nIdx : Nat} {ty : KExpr} {ind_lvl : KLevel}
    {cs_root : List (Call F)} {ctors ctorsA : List (KConstantVal × Nat)}
    {ctorRawTypes : List KExpr}
    {pty bp pind r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hwf : c.t.wf = true)
    (hnPI_lt : nP + nIdx < 18446744069414584321)
    (hnCtors_lt : ctors.length < 549755813888)
    (hroot : IxVM.Consistency.Bounded cs_root)
    (hT_iprj : T = c.κ (iprjAddr (ixAddr b₀) 0))
    (hlps_ctors : ∀ cb ∈ ctors, cb.1.levelParams = List.range cb.1.levelParams.length)
    (hcload : StagedCtorLoads (keyOf c.t) c.t b₀ nP 0 cs_root ctors ctorsA ctorRawTypes)
    (hctor_sp : ∀ k < ctors.length, ∀ c cvCa₀,
      ctors[k]? = some c →
      ctorsA[k]? = some (cvCa₀, c.2) →
      ∃ rcbs rargs cbs eargs us₀,
        (ctorRawTypes.getD k default).stripPis (nP + c.2) =
          some (rcbs, Expr.mkAppN (.const T us₀) rargs) ∧
        cvCa₀.type.stripPis (nP + c.2) =
          some (cbs, Expr.mkAppN (.const T us₀) eargs) ∧
        ∀ idx, nP ≤ idx → idx < nP + c.2,
          famHead T (cbs.getD idx default).1 = false ∨
          RawRecSpine T (rcbs.getD idx default).1 (cbs.getD idx default).1)
    (hsub : ∀ x ∈ cs, x ∈ cs_root)
    (hgood : Good c cs)
    (hty : TmExact c.κ 0 (fun _ => default) h 0 ty pty)
    (hbp : Bytes.RepAddressRef addrTy h b₀ bp)
    (hpind : RepKLevel h ind_lvl pind)
    (ev : ObsFn W "KernelCheck::former_decl_ok"
      [pty, .field (nP : F), .field (nIdx : F), .field (ctors.length : F),
        bp, .field 0, pind] h r h' cs) :
    (∃ bs s, ty.stripPis (nP + nIdx) = some (bs, .sort s) ∧ bs.length = nP + nIdx) ∨
    (nIdx ≠ 0 ∧ ∀ k < ctorsA.length, ∀ cA, ctorsA[k]? = some cA →
      ctorZeroOk T ind_lvl.zeronessOf cA.1.type = true) := by
  rcases former_decl_ok_observed_from_fields hwf hnPI_lt hnCtors_lt hroot hT_iprj
    hlps_ctors hcload hctor_sp hsub hgood hty hbp hpind ev with htele | hzero
  · obtain ⟨testAfter, testCalls, htest⟩ := htele
    obtain ⟨-, bs, s, hs, hl⟩ := former_is_tele_one_bounded_spec (nP + nIdx) hnPI_lt hty htest
    exact Or.inl ⟨bs, s, hs, hl⟩
  · exact Or.inr hzero

end IxVM.Refinement.Decl
