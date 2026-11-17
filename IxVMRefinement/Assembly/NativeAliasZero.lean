import IxVMRefinement.Decl.NativeFront

/-! # The observed alias-former zero check at the bounded-run limits

The domain condition needed by `ctor_zero_ok` is that a parameter or field is not headed by
its family, or its raw and read recursive spines align. Merely containing the family elsewhere
in the domain is allowed. The loop bound is the public call bound, and the former's binder sum
only needs to be below the field characteristic. The statements here refine actual observations;
producers must still supply the domain condition for parameters and fields.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels
open Ix.Kernel (Expr Level LevelParam ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (ctorZeroOk famDomOk famHead pwsAll)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem ctor_zero_ok_head_go {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {t_addr : Bytes.Address} {T : KKey} {ℓ_res : KLevel} {us₀ : List KLevel}
    (hκ_inj : ∀ a : Bytes.Address, κ (ixAddr a) = T → ixAddr a = ixAddr t_addr) :
    ∀ (n : Nat) {k : Nat} {R E : KExpr} {rbs ebs : List (KExpr × Ix.Kernel.BinderMeta)}
      {rargs eargs : List KExpr} {pe pt pres r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      R.stripPis n = some (rbs, Expr.mkAppN (.const T us₀) rargs) →
      E.stripPis n = some (ebs, Expr.mkAppN (.const T us₀) eargs) →
      (∀ idx < n,
        famHead T (ebs.getD idx default).1 = false ∨
        RawRecSpine T (rbs.getD idx default).1 (ebs.getD idx default).1) →
      RawTmExact κ 0 Γ h k R E pe →
      Bytes.RepAddressRef addrTy h t_addr pt →
      RepKLevel h ℓ_res pres →
      ObsFn W "KernelCheck::ctor_zero_ok" [pe, pt, pres] h r h' cs →
      ctorZeroOk T ℓ_res.zeronessOf E = true
  | 0, k, R, E, rbs, ebs, rargs, eargs, pe, pt, pres, r, h, h', cs,
      hstR, hstE, _, hRaw, _, _, ev => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hstR hstE
    obtain ⟨_, rfl⟩ := hstR
    obtain ⟨_, rfl⟩ := hstE
    match Obs.«KernelCheck::ctor_zero_ok».obs ev with
    | .Forall (ld12 := ld) .. =>
      obtain ⟨RT, RB, _, _, _, hR_eq, _, _, _, _⟩ := hRaw.forallE_of_load ld
      exact (mkAppN_const_not_forallE T us₀ rargs RT RB _ hR_eq).elim
    | .other .. =>
      cases hE : Expr.mkAppN (.const T us₀) eargs with
      | forallE dom bo bi => exact (mkAppN_const_not_forallE T us₀ eargs dom bo bi hE).elim
      | _ => rfl
  | m + 1, k, R, E, rbs, ebs, rargs, eargs, pe, pt, pres, r, h, h', cs,
      hstR, hstE, hdoms, hRaw, hpt, hres, ev => by
    cases R with
    | forallE rdom rbo rm =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hstR
      obtain ⟨⟨rbs₁, rbody₁⟩, hstR₁, hstR⟩ := hstR
      simp only [Prod.mk.injEq] at hstR
      obtain ⟨rfl, rfl⟩ := hstR
      cases hRaw with
      | @forallE _ _ _ _ _ _ _ edom _ _ cell hdom hbo hℓ =>
        simp only [Expr.stripPis, Option.map_eq_some_iff] at hstE
        obtain ⟨⟨ebs₁, ebody₁⟩, hstE₁, hstE⟩ := hstE
        simp only [Prod.mk.injEq] at hstE
        obtain ⟨rfl, rfl⟩ := hstE
        match Obs.«KernelCheck::ctor_zero_ok».obs ev with
        | .other (ld12 := ld) (hne301 := hne) .. =>
          rw [loadValue_enum_cell cell] at ld
          injection ld with hv
          exact absurd hv.symm (hne [_, _, _] rfl)
        | .Forall (x_d := xd) (x_b := xb) (x_m := xm) (m49 := m1)
            (x_last := xlast) (m84 := m2) (x_h := xh) (m120 := m3) (m262 := m4)
            (ld12 := ld) (ev59 := ev_pw) (heq82 := heq) (ev96 := ev_pb) (ev132 := ev_sp)
            (sg269 := sg) (ev275 := ev_rec) .. =>
          obtain ⟨-, hxs⟩ := load_cell cell ld
          injection hxs with h1 hxs; injection hxs with h2 hxs; injection hxs with h3
          subst h1 h2 h3
          rw [heq] at ev_pw
          have hpw := pw_eq_one hℓ hres ev_pw
          have ext1 := ev_pw.heap_extends
          have ext2 := ev_pb.heap_extends
          have ext3 := ev_sp.heap_extends
          have ext123 := ext1.trans (ext2.trans ext3)
          have hfam_dom : famDomOk T ℓ_res.zeronessOf edom = true := by
            have hd0 := hdoms 0 (by omega)
            simp only [List.getD_cons_zero] at hd0
            rcases hd0 with hnoT | hrec_sp
            · simp [famDomOk, hnoT]
            · obtain ⟨k', us, rAs, eAs, hlast⟩ :=
                nat_pi_binders_of_rawRecSpine hrec_sp (hdom.mono ext1) ev_pb
              obtain ⟨hd, sp, RH, EH, RAs', _, htup, hH, hna, _, hlast_eq, _⟩ :=
                collect_spine_raw_spec hlast ev_sp
              injection htup with hl; injection hl with hxh hl; injection hl with _; subst hxh
              have hRH_eq : RH = .const T us := by
                have hfn := congrArg Expr.getAppFn hlast_eq
                rw [nat_getAppFn_mkAppN, nat_getAppFn_mkAppN] at hfn
                cases RH with
                | app rf ra => exact (hna rf ra rfl).elim
                | _ => exact hfn.symm
              subst hRH_eq
              cases sg with
              | Const_n1 _ _ m_eq _ _ _ ev_eq ev_dom _ =>
                have ext_eq := ev_eq.heap_extends
                have hpws := dom_zero_ok_of_rawRecSpine hrec_sp
                  (hdom.mono (ext123.trans ext_eq)) (hres.mono (ext123.trans ext_eq)) ev_dom
                simp [famDomOk, hpws]
              | Const_other xc _ v_eq m_eq _ ld_h ev_eq hne_eq _ _ _ =>
                obtain ⟨a_c, ls_c, hR_c, _, ha_c, _⟩ := hH.const_of_load ld_h
                injection hR_c with hc_eq _
                have ha_eq : a_c = t_addr := ixAddr_inj (hκ_inj a_c hc_eq.symm)
                subst ha_eq
                obtain ⟨hv_eq, _⟩ := Lib.address_eq_spec ev_eq ha_c
                  (Bytes.repAddressRef_heapMono₂ addrTy ext123 hpt)
                simp at hv_eq
                exact (hne_eq hv_eq).elim
              | other _ ld_h hne_c _ _ _ =>
                cases hH with
                | const cell_c _ _ =>
                  rw [loadValue_enum_cell cell_c] at ld_h
                  injection ld_h with hv
                  exact (hne_c [_, _] rfl hv.symm).elim
          have ext4 : Heap.Extends m3 m4 := by
            cases sg with
            | Const_n1 _ _ _ _ _ _ ev_eq ev_dom _ =>
              exact ev_eq.heap_extends.trans ev_dom.heap_extends
            | Const_other _ _ _ _ _ _ ev_eq _ _ hm4 _ =>
              rw [hm4]; exact ev_eq.heap_extends
            | other _ _ _ _ hm4 _ =>
              rw [hm4]
          have ext_all := ext123.trans ext4
          have hdoms' : ∀ idx < m,
              famHead T (ebs₁.getD idx default).1 = false ∨
              RawRecSpine T (rbs₁.getD idx default).1 (ebs₁.getD idx default).1 := by
            intro idx hidx
            have h := hdoms (idx + 1) (by omega)
            simpa [List.getD_cons_succ] using h
          have hrec := ctor_zero_ok_head_go hκ_inj m hstR₁ hstE₁ hdoms' (hbo.mono ext_all)
            (Bytes.repAddressRef_heapMono₂ addrTy ext_all hpt) (hres.mono ext_all) ev_rec
          simp [ctorZeroOk, bmeta, hpw, hfam_dom, hrec]
    | _ => simp [Expr.stripPis] at hstR

theorem ctor_zero_all_bounded_head {t : Ix.Kernel.RoleTable}
    {b₀ a_t : Bytes.Address} {T : KKey} {nP : Nat} {ind_lvl : KLevel}
    {cs_root : List (Call F)} {ctors ctorsA : List (KConstantVal × Nat)}
    {ctorRawTypes : List KExpr}
    (hwf : t.wf = true)
    (hlps_ctors : ∀ c ∈ ctors, c.1.levelParams = List.range c.1.levelParams.length)
    (hT_eq : T = keyOf t (ixAddr a_t))
    (hcload : CtorLoadAt t b₀ nP cs_root ctors ctorsA ctorRawTypes)
    (hctor_sp : ∀ k < ctors.length, ∀ c cvCa₀,
      ctors[k]? = some c →
      ctorsA[k]? = some (cvCa₀, c.2) →
      ∃ rcbs rargs cbs eargs us₀,
        (ctorRawTypes.getD k default).stripPis (nP + c.2) =
          some (rcbs, Expr.mkAppN (.const T us₀) rargs) ∧
        cvCa₀.type.stripPis (nP + c.2) =
          some (cbs, Expr.mkAppN (.const T us₀) eargs) ∧
        ∀ idx < nP + c.2,
          famHead T (cbs.getD idx default).1 = false ∨
          RawRecSpine T (rcbs.getD idx default).1 (cbs.getD idx default).1)
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
    | .other (m34 := m34) (p41 := p41) (cs47 := cs_cprj) (x_cty := xcty)
        (m125 := m125) (cs165 := cs_rec) (v171 := v171)
        (ev49 := ev_cprj) (ld43 := ld_ctor) (ev137 := ev_cz)
        (op208 := op_add) (ev167 := ev_rec) (hc224 := hc) .. =>
      obtain ⟨c_j, cvCa₀, hc_j, hcA_j, hvs_j, hload_j⟩ := hcload.2 j (by omega)
      have hsub_cprj : ∀ x ∈ cs_cprj, x ∈ cs_root := fun x hx => hsub x (by simp [hc, hx])
      have hsub_rec : ∀ x ∈ cs_rec, x ∈ cs_root := fun x hx => hsub x (by simp [hc, hx])
      obtain ⟨nl', cty', cblk', cnp', cnf', _, ld_c', _, _, hraw_rep, _⟩ :=
        hload_j bp p41 h m34 cs_cprj hsub_cprj hbp ev_cprj
      rw [ld_c'] at ld_ctor
      injection ld_ctor with hval; injection hval with _ _ h1
      injection h1 with _ h1; injection h1 with hcty_eq _
      cases hcty_eq.symm
      have e1 := ev_cprj.heap_extends
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
        obtain ⟨rcbs, rargs, cbs, eargs, us₀, hstR, hstE, hdoms⟩ :=
          hctor_sp k (by omega) c_j cvCa₀ hc_j hcA_j
        have hκ_inj : ∀ a : Bytes.Address, keyOf t (ixAddr a) = T → ixAddr a = ixAddr a_t := by
          intro a ha
          rw [hT_eq] at ha
          exact nat_keyOf_injective hwf ha
        exact ctor_zero_ok_head_go hκ_inj (nP + c_j.2) hstR hstE hdoms hcty_raw
          (Bytes.repAddressRef_heapMono₂ addrTy e1 hpt)
          (repKLevel_heapMono₂ e1 hpind) ev_cz
      · have hv171 : v171 = .field ((j + 1 : Nat) : F) := evalBinOp_add_nat j 1 op_add
        rw [hv171] at ev_rec
        exact ctor_zero_all_bounded_head hwf hlps_ctors hT_eq hcload hctor_sp hnCtors_lt
          m (j + 1) (by omega) hsub_rec
          (Bytes.repAddressRef_heapMono₂ addrTy (e1.trans e2) hbp)
          (Bytes.repAddressRef_heapMono₂ addrTy (e1.trans e2) hpt)
          (repKLevel_heapMono₂ (e1.trans e2) hpind) ev_rec
          k (by omega) hkt cA hcA

theorem former_decl_ok_bounded_head {c : Ctx}
    {b₀ : Bytes.Address} {T : KKey} {nP nIdx : Nat} {ty : KExpr} {ind_lvl : KLevel}
    {cs_root : List (Call F)} {ctors ctorsA : List (KConstantVal × Nat)}
    {ctorRawTypes : List KExpr}
    {pty bp pind r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hwf : c.t.wf = true)
    (hnPI_lt : nP + nIdx < 18446744069414584321)
    (hnCtors_lt : ctors.length < 549755813888)
    (hT_iprj : T = c.κ (iprjAddr (ixAddr b₀) 0))
    (hlps_ctors : ∀ cb ∈ ctors, cb.1.levelParams = List.range cb.1.levelParams.length)
    (hcload : CtorLoadAt c.t b₀ nP cs_root ctors ctorsA ctorRawTypes)
    (hctor_sp : ∀ k < ctors.length, ∀ c cvCa₀,
      ctors[k]? = some c →
      ctorsA[k]? = some (cvCa₀, c.2) →
      ∃ rcbs rargs cbs eargs us₀,
        (ctorRawTypes.getD k default).stripPis (nP + c.2) =
          some (rcbs, Expr.mkAppN (.const T us₀) rargs) ∧
        cvCa₀.type.stripPis (nP + c.2) =
          some (cbs, Expr.mkAppN (.const T us₀) eargs) ∧
        ∀ idx < nP + c.2,
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
  match Obs.«KernelCheck::former_decl_ok».obs ev with
  | .n1 (v17 := v17) (op38 := op_add) (ev15 := ev_tele) .. =>
    have hv17 : v17 = .field ((nP + nIdx : Nat) : F) := evalBinOp_add_nat nP nIdx op_add
    rw [hv17] at ev_tele
    obtain ⟨_, bs, s, hst, hlen⟩ := former_is_tele_one_bounded_spec (nP + nIdx) (by omega) hty ev_tele
    exact Or.inl ⟨bs, s, hst, hlen⟩
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
    have hcz := ctor_zero_all_bounded_head hwf hlps_ctors hT_at hcload hctor_sp hnCtors_lt
      ctors.length 0 (by omega) hsub_cz
      (Bytes.repAddressRef_heapMono₂ addrTy (e1.trans (e2.trans e3)) hbp)
      ha_t
      (repKLevel_heapMono₂ (e1.trans (e2.trans e3)) hpind) ev_cz
    exact Or.inr ⟨hnIdx_ne, fun k hk cA hcA =>
      hcz k (Nat.zero_le k) (by rw [← hcload.1]; exact hk) cA hcA⟩


end IxVM.Refinement.Decl
