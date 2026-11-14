import IxVMRefinement.Callees.FireAux
import IxVMRefinement.Obs.KernelModeled1

/-! # Modeled recursor firing (`KernelModeled::fire_compare`, `KernelModeled::fire_ok`)

Step lemmas for the modeled-family recursor comparison (`fire_compare_step`) and its zero-motive
outer gate (`fire_ok_step`), via the internal helpers:
* `last_binder_dom` and `rec_family_block` (the `FamilyFew` exit when `block_is_modeled = 0`),
* `assert_index_vars`, `lower_pins`, `rec_major_pins`, and `rec_comparands` (`Tier.nestedPins`),
* `level_list_equal` and `inst_pins` (`FireCompared`). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace FireCompareAux

/-! ## `last_binder_dom` and `rec_family_block` -/

theorem last_binder_dom_spec (c : Ctx) :
    ∀ (n : Nat) {x_e r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
      {k0 : Nat} {E : KExpr},
      calls.length = n →
      c.tmk 0 FireAux.Γ₀ k0 h E x_e →
      ObsFn W "KernelModeled::last_binder_dom" [x_e] h r h' calls →
      h' = h ∧ ∃ (m : Nat) (dom : KExpr),
        piDomAt m E = some dom ∧ c.tmk 0 FireAux.Γ₀ (k0 + m) h dom r := by
  intro n
  induction n with
  | zero =>
    intro x_e r h h' calls k0 E hlen hE ev
    cases Obs.«KernelModeled::last_binder_dom».obs ev with
    | Forall _ _ _ _ _ _ _ _ _ _ hc87 =>
      rw [hc87] at hlen; simp at hlen
    | other x_d x_b w20 v36 ld12 _ _ he93 he94 _ =>
      subst he93 he94
      obtain ⟨T0, B0, ℓ, rfl, hT0, -, -⟩ := hE.forallE_of_load ld12
      exact ⟨rfl, 0, T0, rfl, by simpa using hT0⟩
  | succ n ih =>
    intro x_e r h h' calls k0 E hlen hE ev
    cases Obs.«KernelModeled::last_binder_dom».obs ev with
    | Forall x_d x_b w20 w55 w56 w57 cs76 ld12 _ ev78 hc87 =>
      obtain ⟨T0, B0, ℓ, rfl, -, hB0, -⟩ := hE.forallE_of_load ld12
      have hcs : cs76.length = n := by rw [hc87] at hlen; simpa using hlen
      obtain ⟨rfl, m, dom, hpi, hdom⟩ := ih hcs hB0 ev78
      exact ⟨rfl, m + 1, dom, hpi, by rwa [show k0 + (m + 1) = k0 + 1 + m by omega]⟩
    | other x_d x_b w20 v36 ld12 _ _ he93 he94 _ =>
      subst he93 he94
      obtain ⟨T0, B0, ℓ, rfl, hT0, -, -⟩ := hE.forallE_of_load ld12
      exact ⟨rfl, 0, T0, rfl, by simpa using hT0⟩

theorem rec_family_block_spec (c : Ctx) {x_rec_addr r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {a : Bytes.Address} {cv : Ix.Kernel.ConstantVal .anon}
    {mI rP : Nat} {rls : List (Ix.Kernel.RecRule .anon)}
    (ev : ObsFn W "KernelModeled::rec_family_block" [x_rec_addr] h r h' calls)
    (good : Good c calls) (ih : IH c calls)
    (ha : RepAddr h a x_rec_addr)
    (hfind : c.env.find? (c.κ (ixAddr a)) = some (.recInfo cv mI rP rls)) :
    ∃ (b : Bytes.Address) (np k : Nat) (mdom dom : KExpr) (i : Nat) (us : List KLevel),
      RepAddr h' b r ∧
      piDomAt np cv.type = some mdom ∧
      piDomAt k mdom = some dom ∧
      dom.getAppFn = .const (c.κ (iprjAddr (ixAddr b) i)) us := by
  obtain ⟨m2, p10, cs16, w33, x_ty, x_np, w34, w35, w36, w37, w38, w39, w40, w41, v97, m98, cs108,
    x_mdom, w146, w147, v163, m164, cs174, m186, cs196, x_head, w210, x_t0, w240, m252, p260, cs266,
    w283, w284, w285, w286, w287, w288, x_b, w289, ev18, ld12, ev110, ld138, ev176, ev198, ld232,
    ev268, ld262, he331, he332, hc333⟩ := Obs.«KernelModeled::rec_family_block».obs ev
  subst he331 he332
  have hgood1 : Good c cs16 := good.sub (by rw [hc333]; intro z hz; simp [hz])
  obtain ⟨ci', hfind', v_ci, hld_ci, hci⟩ :=
    ih.get (.callees .get_ci) (by rw [hc333]; ModeledAux.callees_lt) ev18 x_rec_addr a rfl hgood1 ha
  rw [hfind] at hfind'; injection hfind' with rfl
  rw [ld12] at hld_ci; injection hld_ci with hv_ci; subst hv_ci
  obtain ⟨p, _, _, _, hv, rfl, -, -, -, -, -, -, -⟩ := FireAux.ciRep_rec_inv hci
  have hty0 : c.tmk 0 FireAux.Γ₀ 0 m2 (posOf cv.levelParams cv.type) x_ty := hv.2.2.2 0 FireAux.Γ₀
  obtain ⟨rfl, bsPos, BPos, hstripPos, hBPos⟩ :=
    ModeledAux.peel_n_foralls_aux c (ZMod.val p) rfl hty0 ev110
  obtain ⟨mdomPos, bodyPos, ℓ, rfl, hmdomPos, -, -⟩ := hBPos.forallE_of_load ld138
  have hpiPos1 : piDomAt (ZMod.val p) (posOf cv.levelParams cv.type) = some mdomPos :=
    ModeledAux.piDomAt_of_stripPis hstripPos
  obtain ⟨mdom, hpi1, rfl⟩ := FireAux.piDomAt_of_posOf (ZMod.val p) hpiPos1
  simp only [Nat.zero_add] at hmdomPos
  obtain ⟨rfl, k, domPos, hpiPos2, hdomPos⟩ :=
    last_binder_dom_spec c cs174.length rfl hmdomPos ev176
  obtain ⟨dom, hpi2, rfl⟩ := FireAux.piDomAt_of_posOf k hpiPos2
  have hgood2 : Good c cs196 := good.sub (by rw [hc333]; intro z hz; simp [hz])
  obtain ⟨hd, sp, H, As_dom, htuple, hH, -, hdom_eq⟩ :=
    ih.get (.subst .collect_spine) (by rw [hc333]; ModeledAux.callees_lt) ev198 v163 rfl hgood2
      0 FireAux.Γ₀ (ZMod.val p + k) (posOf cv.levelParams dom) hdomPos
  injection htuple with h1
  simp only [List.cons.injEq, and_true] at h1
  rcases h1 with ⟨rfl, rfl⟩
  obtain ⟨a_t0, usPos, rfl, ha_t0, -⟩ := hH.const_of_load ld232
  have hfnPos : posOf cv.levelParams dom.getAppFn = .const (c.κ (ixAddr a_t0)) usPos := by
    have h1 := Ix.Kernel.Expr.getAppFn_instantiateLevelParams cv.levelParams
      (posLevels cv.levelParams) dom
    change (posOf cv.levelParams dom).getAppFn = posOf cv.levelParams dom.getAppFn at h1
    rw [← h1, hdom_eq, ModeledAux.getAppFn_mkAppN]
    rfl
  obtain ⟨us, hfn_dom, -⟩ := FireAux.const_of_posOf hfnPos
  have hgood3 : Good c cs266 := good.sub (by rw [hc333]; intro z hz; simp [hz])
  obtain ⟨ci_ind, hfind_ind, v_ind, hld_ind, hci_ind⟩ :=
    ih.get (.callees .get_ci) (by rw [hc333]; ModeledAux.callees_lt) ev268 x_t0 a_t0 rfl
      hgood3 ha_t0
  rw [ld262] at hld_ind; injection hld_ind with hv_ind; subst hv_ind
  obtain ⟨cvI, capsI, -, -, -, b, i_idx, rfl, -, -, -, -, -, -, hb, rfl, hname⟩ :=
    FireAux.ciRep_induct_inv hci_ind
  have hkey_eq : c.κ (ixAddr a_t0) = c.κ (iprjAddr (ixAddr b) (ZMod.val i_idx)) := by
    have hname_find : cvI.name = c.κ (ixAddr a_t0) := FireAux.env_find?_name hfind_ind
    exact hname_find.symm.trans hname
  rw [hkey_eq] at hfn_dom
  exact ⟨b, ZMod.val p, k, mdom, dom, ZMod.val i_idx, us, hb, hpi1, hpi2, hfn_dom⟩

/-! ## `assert_index_vars`, `lower_pins`, `rec_major_pins`, and `rec_comparands` -/

theorem assert_index_vars_spec (c : Ctx) {ni k0 : Nat} (hni : ni < 72057594037927936) :
    ∀ (xs : List KExpr) {idx : Nat} {x_args r : SourceValue F} {h h' : Heap F}
      {calls : List (Call F)},
      idx ≤ ni → xs.length = ni - idx →
      c.tmlk 0 FireAux.Γ₀ k0 h xs x_args →
      ObsFn W "KernelModeled::assert_index_vars" [x_args, .field (ni : F), .field (idx : F)]
        h r h' calls →
      h' = h ∧ xs = ((List.range ni).drop idx).map (fun t => .bvar (ni - 1 - t)) := by
  intro xs
  induction xs with
  | nil =>
    intro idx x_args r h h' calls hle hlen _ ev
    have hidx : idx = ni := by simp at hlen; omega
    subst hidx
    cases Obs.«KernelModeled::assert_index_vars».obs ev with
    | n0 _ _ he27 _ =>
      subst he27
      exact ⟨rfl, by simp⟩
    | other v1 _ _ _ _ _ _ _ op17 hne29 _ _ _ _ _ _ _ _ =>
      simp only [evalBinOp, sub_self, Except.ok.injEq] at op17
      exact (hne29 op17.symm).elim
  | cons E rest ih =>
    intro idx x_args r h h' calls hle hlen hxs ev
    have hlt : idx < ni := by simp at hlen; omega
    have hneF : (ni : F) - (idx : F) ≠ 0 := by
      intro h0
      have heqF : (ni : F) = (idx : F) := sub_eq_zero.mp h0
      have heqN := FireAux.natCast_inj_lt59 (Nat.lt_trans hni (by decide))
        (Nat.lt_trans hlt (Nat.lt_trans hni (by decide))) heqF
      omega
    cases Obs.«KernelModeled::assert_index_vars».obs ev with
    | n0 op17 _ _ _ =>
      simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op17
      exact (hneF op17).elim
    | other v1 x_a x_rest x_j v94 x108 cs130 v135 op17 _ ld43 ld69 op123 op115 heq126 op163 ev132 _ =>
      obtain ⟨E', rest', heq_cons, hE, hrest⟩ := Lib.rep_cons_of_load hxs ld43
      injection heq_cons with h1 h2; subst h1 h2
      have hx108 : x108 = .field ((ni : F) - 1) := by
        simp only [evalBinOp, Except.ok.injEq] at op123; exact op123.symm
      subst hx108
      have hv94 : v94 = .field ((ni : F) - 1 - (idx : F)) := by
        simp only [evalBinOp, Except.ok.injEq] at op115; exact op115.symm
      subst hv94 heq126
      have hnat_sum : (ni - 1 - idx) + idx + 1 = ni := by omega
      have hF_sum : ((ni - 1 - idx : Nat) : F) + (idx : F) + 1 = (ni : F) := by
        exact_mod_cast hnat_sum
      have hsub1 : (ni : F) - 1 = ((ni - 1 - idx : Nat) : F) + (idx : F) := by
        rw [← hF_sum, add_sub_cancel_right]
      have hsub2 : (ni : F) - 1 - (idx : F) = ((ni - 1 - idx : Nat) : F) := by
        rw [hsub1, add_sub_cancel_right]
      rw [hsub2] at ld69
      obtain ⟨jF, hj_eq, -, hj_cases⟩ := hE.bvar_of_load ld69
      have hjF : jF = ((ni - 1 - idx : Nat) : F) := (Value.field.inj hj_eq).symm
      subst hjF
      have hE_eq : E' = .bvar (ni - 1 - idx) := by
        rcases hj_cases with ⟨-, hE'⟩ | ⟨-, hd, -⟩
        · rw [hE', FireAux.val_natCast_lt59
            (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_trans hni (by decide)))]
        · omega
      subst hE_eq
      have hv135 : v135 = .field ((idx + 1 : Nat) : F) := by
        simp only [evalBinOp, Except.ok.injEq] at op163
        rw [← op163]
        simp [Nat.cast_add]
      subst hv135
      obtain ⟨rfl, hrest_eq⟩ := ih (idx := idx + 1) (by omega)
        (by simp at hlen; omega) hrest ev132
      refine ⟨rfl, ?_⟩
      have hdrop_step : (List.range ni).drop idx = idx :: (List.range ni).drop (idx + 1) := by
        have hlt_r : idx < (List.range ni).length := by simp [hlt]
        rw [List.drop_eq_getElem_cons hlt_r, List.getElem_range]
      rw [hdrop_step, List.map_cons, hrest_eq]

theorem lower_pins_spec (c : Ctx) {ps : List Ix.Kernel.LevelParam} {rP nI : Nat}
    (hnI : nI < 72057594037927936) :
    ∀ (raws : List KExpr) {x_ps r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      Good c calls → IH c calls →
      c.tmlk 0 FireAux.Γ₀ (rP + nI) h (raws.map (posOf ps)) x_ps →
      ObsFn W "KernelModeled::lower_pins" [x_ps, .field (nI : F)] h r h' calls →
      (∀ x ∈ raws, (x.lowerBVars nI 0).liftLooseBVars nI 0 = x ∧
        (x.lowerBVars nI 0).hasFvar = false ∧
        (x.lowerBVars nI 0).looseBVarsBounded rP = true) ∧
      c.tmlk 0 FireAux.Γ₀ rP h' ((raws.map (Ix.Kernel.Expr.lowerBVars nI 0)).map (posOf ps)) r := by
  intro raws
  induction raws with
  | nil =>
    intro x_ps r h h' calls _ _ hps ev
    cases Obs.«KernelModeled::lower_pins».obs ev with
    | Nil _ he24 hm23 _ =>
      subst he24 hm23
      exact ⟨fun _ hm => nomatch hm, allocNil_rep _ _ h⟩
    | Cons _ _ _ _ _ _ _ _ _ _ _ ld12 _ _ _ _ _ _ _ =>
      obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hps ld12
      cases he
  | cons x rest ih_list =>
    intro x_ps r h h' calls good ih hps ev
    cases Obs.«KernelModeled::lower_pins».obs ev with
    | Nil ld12 _ _ _ =>
      cases Lib.rep_nil_of_load hps ld12
    | Cons x_p x_rest v57 m60 cs68 v109 v110 m112 cs120 m147 cs155 ld12 ev70 heq100 he105 hm104
        ev122 ev157 hc174 =>
      subst heq100 he105 hm104
      obtain ⟨xPos, restPos, heq_cons, hx_p, hrest_p⟩ := Lib.rep_cons_of_load hps ld12
      simp only [List.map_cons, List.cons.injEq] at heq_cons
      rcases heq_cons with ⟨rfl, rfl⟩
      have hgood1 : Good c cs68 := good.sub (by rw [hc174]; intro z hz; simp [hz])
      obtain ⟨hm60, -, hnoF0⟩ :=
        ih.get (.subst .has_bvar_in_range) (by rw [hc174]; ModeledAux.callees_lt) ev70
          x_p 0 (nI : F) rfl hgood1
      subst hm60
      have hnI_val : ZMod.val (nI : F) = nI :=
        FireAux.val_natCast_lt59 (Nat.lt_trans hnI (by decide))
      have hnoF : Specs.Subst.NoIdxF h 0 nI x_p := by
        have h0 := hnoF0 rfl 0 FireAux.Γ₀ (rP + nI) (posOf ps x) hx_p
        rwa [ZMod.val_zero, hnI_val] at h0
      have hB : nI + 2 ^ 39 ≤ Aiur.Library.U32.Goldilocks.modulus :=
        Nat.le_trans (Nat.add_le_add_right (Nat.le_of_lt hnI) _) (by decide)
      have hcall_hb : (⟨"KernelSubst::has_bvar_in_range", [x_p, .field 0, .field (nI : F)], h⟩ :
          Call F) ∈ calls := by
        rw [hc174]; simp
      have hno : Specs.Subst.NoIdx h 0 nI x_p :=
        Specs.Subst.noIdx_of_noIdxF_call good.2 hcall_hb (by simp) hB hnoF
      have hopen : Tm c.κ (rP + nI) FireAux.Γ₀ h 0
          (FireAux.openZero (rP + nI) 0 (posOf ps x)) x_p :=
        FireAux.tm_openZero hx_p 0 (by omega)
      have hgood2 : Good c cs120 := good.sub (by rw [hc174]; intro z hz; simp [hz])
      have hlow0 := ih.get (.subst .expr_lower) (by rw [hc174]; ModeledAux.callees_lt) ev122
        x_p (nI : F) 0 rfl hgood2 0 nI (by rw [hnI_val]; omega) (Nat.zero_le _)
        (rP + nI) FireAux.Γ₀ (FireAux.openZero (rP + nI) 0 (posOf ps x)) (by omega)
        (by rw [ZMod.val_zero]; exact hopen) (by rw [ZMod.val_zero]; exact hno)
      rw [ZMod.val_zero, show rP + nI - nI = rP by omega] at hlow0
      have hwscPos : (FireAux.openZero (rP + nI) 0 (posOf ps x)).wscopedB rP = true :=
        hlow0.wscopedB FireAux.ghostScoped_Γ₀
      have hwsc : (FireAux.openZero (rP + nI) 0 x).wscopedB rP = true := by
        rw [FireAux.openZero_posOf] at hwscPos
        exact (FireAux.wscopedB_instantiateLevelParams _ _ _ rP).symm.trans hwscPos
      have hfv_x : x.hasFvar = false := by
        have := FireAux.hasFvar_of_tm_zero hx_p
        rwa [posOf, Ix.Kernel.Expr.hasFvar_instantiateLevelParams] at this
      have hbnd_x : x.looseBVarsBounded (0 + rP + nI) = true := by
        have := hx_p.looseBVarsBounded
        rw [posOf, Ix.Kernel.Expr.looseBVarsBounded_instantiateLevelParams] at this
        simpa [Nat.zero_add] using this
      obtain ⟨_, hlift_x, hfv_low, hbnd_low⟩ :=
        FireAux.lowerBVars_of_openZero_wscopedB x 0 hfv_x hbnd_x hwsc
      obtain ⟨hclosePos, -, -, -⟩ :=
        FireAux.lowerBVars_of_openZero_wscopedB (posOf ps x) 0
          (FireAux.hasFvar_of_tm_zero hx_p)
          (by simpa [Nat.zero_add] using hx_p.looseBVarsBounded)
          hwscPos
      have hclosed : Tm c.κ 0 FireAux.Γ₀ m112 rP (posOf ps (x.lowerBVars nI 0)) v109 := by
        have hc0 := FireAux.tm_closeZero hlow0
        rw [Nat.zero_add, hclosePos, ← FireAux.posOf_lowerBVars] at hc0
        exact hc0
      have ext1 := ev122.heap_extends
      have hrest_m112 : c.tmlk 0 FireAux.Γ₀ (rP + nI) m112 (rest.map (posOf ps)) x_rest :=
        repList_heapMono₂ kexprListEnum (fun _ _ _ _ e r => Tm.mono e r) ext1 hrest_p
      have hgood3 : Good c cs155 := good.sub (by rw [hc174]; intro z hz; simp [hz])
      obtain ⟨hrest_props, hrest_out⟩ := ih_list hgood3
        (ih.mono (by rw [hc174]; ModeledAux.callees_lt)) hrest_m112 ev157
      have ext2 := ev157.heap_extends
      refine ⟨?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact ⟨hlift_x, hfv_low, by simpa [Nat.zero_add] using hbnd_low⟩
        · exact hrest_props y hy'
      · simp only [List.map_cons]
        exact Lib.rep_store_cons (R := fun h E p => Tm c.κ 0 FireAux.Γ₀ h rP E p)
          (fun _ _ _ _ e r => Tm.mono e r) (hclosed.mono ext2) hrest_out

theorem rec_major_pins_spec (c : Ctx) {ps : List Ix.Kernel.LevelParam}
    {tyA : KExpr} {mI rP : Nat} {x_ty : SourceValue F} {i_f : F}
    {r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelModeled::rec_major_pins" [x_ty, .field (rP : F), .field i_f] h r h' calls)
    (good : Good c calls) (ih : IH c calls)
    (hty : c.tmk 0 FireAux.Γ₀ 0 h (posOf ps tyA) x_ty)
    (hmI_F : (mI : F) = (rP : F) + i_f)
    (hle : rP ≤ mI) (hmI_lt : mI < 288230376151711744) :
    ∃ (x_iaddr x_ilvls v358 : SourceValue F) (lvls : List KLevel) (pins : List KExpr),
      r = .tuple [x_iaddr, x_ilvls, v358] ∧
      pins.length < 72057594037927936 ∧
      Ix.Kernel.Tier.nestedPins tyA mI rP pins.length = some (lvls, pins) ∧
      LvListRep h' (lvls.map (Ix.Kernel.Level.subst ps (posLevels ps))) x_ilvls ∧
      c.tmlk 0 FireAux.Γ₀ rP h' (pins.map (posOf ps)) v358 := by
  obtain ⟨v1, m2, cs12, v16, x_dom, w59, w60, m77, cs87, x_h, x_args, x_iaddr, x_ilvls, m141,
    p149, cs155, w172, w173, x_inp, x_ini, w174, w175, w176, w177, v257, v258, m260, cs268,
    v296, m297, cs307, v310, m314, cs322, v358, m375, cs383, v386, m389, cs397,
    op37, ev14, ld51, ev89, ld122, ev157, ld151, heq245, ev270, op292, heq295,
    ev324, ev309, he359, ev399, ev385, he423, hc424⟩ :=
    Obs.«KernelModeled::rec_major_pins».obs ev
  subst he359 he423
  have hv16 : v16 = .field (mI : F) := by
    simp only [evalBinOp, Except.ok.injEq] at op37
    rw [← op37, ← hmI_F]
  subst hv16
  have hmI_val : ZMod.val (mI : F) = mI :=
    FireAux.val_natCast_lt59 (Nat.lt_trans hmI_lt (by decide))
  obtain ⟨rfl, bsPos, BPos, hstripPos, hBPos⟩ :=
    ModeledAux.peel_n_foralls_aux c mI hmI_val hty ev14
  obtain ⟨domPos, bodyPos, ℓ, rfl, hdomPos, -, -⟩ := hBPos.forallE_of_load ld51
  simp only [Nat.zero_add] at hdomPos
  obtain ⟨bs, B, hstrip, hB_eq⟩ := FireAux.stripPis_of_posOf mI hstripPos
  obtain ⟨dom, body, bm, rfl, hdomPos_eq, -⟩ := FireAux.forallE_of_posOf hB_eq.symm
  subst hdomPos_eq
  have hgood1 : Good c cs87 := good.sub (by rw [hc424]; intro z hz; simp [hz])
  obtain ⟨hd, sp, H, argsPos, htuple, hH, hargsPos, hdom_mk⟩ :=
    ih.get (.subst .collect_spine) (by rw [hc424]; ModeledAux.callees_lt) ev89 x_dom rfl hgood1
      0 FireAux.Γ₀ mI (posOf ps dom) hdomPos
  injection htuple with h1
  simp only [List.cons.injEq, and_true] at h1
  rcases h1 with ⟨rfl, rfl⟩
  obtain ⟨a_i, lsPos, rfl, ha_i, hlsPos⟩ := hH.const_of_load ld122
  have hfnPos : posOf ps dom.getAppFn = .const (c.κ (ixAddr a_i)) lsPos := by
    have h1 := Ix.Kernel.Expr.getAppFn_instantiateLevelParams ps (posLevels ps) dom
    change (posOf ps dom).getAppFn = posOf ps dom.getAppFn at h1
    rw [← h1, hdom_mk, ModeledAux.getAppFn_mkAppN]
    rfl
  obtain ⟨lvls, hfn_dom, rfl⟩ := FireAux.const_of_posOf hfnPos
  have hargsPos_eq : argsPos = dom.getAppArgs.map (posOf ps) := by
    have h1 := Ix.Kernel.Expr.getAppArgs_instantiateLevelParams ps (posLevels ps) dom
    change (posOf ps dom).getAppArgs = dom.getAppArgs.map (posOf ps) at h1
    rw [hdom_mk, ModeledAux.getAppArgs_mkAppN] at h1
    simpa [Ix.Kernel.Expr.getAppArgs] using h1.symm
  subst hargsPos_eq
  have hgood2 : Good c cs155 := good.sub (by rw [hc424]; intro z hz; simp [hz])
  obtain ⟨ci_i, _, v_i, hld_i, hci_i⟩ :=
    ih.get (.callees .get_ci) (by rw [hc424]; ModeledAux.callees_lt) ev157 x_iaddr a_i rfl
      hgood2 ha_i
  rw [ld151] at hld_i; injection hld_i with hv_i; subst hv_i
  obtain ⟨_, _, nP, nI, _, _, _, rfl, rfl, hni_eq, -, hnP_lt, hnI_lt, -, -, -, -⟩ :=
    FireAux.ciRep_induct_inv hci_i
  have hi_f : i_f = (nI : F) := by
    have := heq245.symm.trans hni_eq
    exact Value.field.inj this
  subst hi_f heq245
  have hmI_eq : mI = rP + nI := by
    have hcast : (mI : F) = ((rP + nI : Nat) : F) := by simpa [Nat.cast_add] using hmI_F
    exact FireAux.natCast_inj_lt59 (Nat.lt_trans hmI_lt (by decide))
      (by
        have hrP_lt : rP < 288230376151711744 := Nat.lt_of_le_of_lt hle hmI_lt
        have hsum : rP + nI < 288230376151711744 + 72057594037927936 :=
          Nat.add_lt_add hrP_lt hnI_lt
        exact Nat.lt_trans hsum (by decide))
      hcast
  have hnI_sub : nI = mI - rP := by omega
  have ext_141 := ev157.heap_extends
  have hargs_141 : c.tmlk 0 FireAux.Γ₀ mI m141 (dom.getAppArgs.map (posOf ps)) x_args :=
    repList_heapMono₂ kexprListEnum (fun _ _ _ _ e r => Tm.mono e r) ext_141 hargsPos
  have hcall_len : (⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [x_args], m141⟩ :
      Call F) ∈ calls := by
    rw [hc424]; simp
  have hargs_len_lt : (dom.getAppArgs.map (posOf ps)).length < 2 ^ 39 :=
    RomBound.bounded_length_lt good.2 hcall_len (by simp) hargs_141
  obtain ⟨hv257, rfl⟩ := FireAux.kexpr_length ev270 hargs_141
  have hv258 : v258 = .field ((nP + nI : Nat) : F) := by
    simp only [evalBinOp, Except.ok.injEq] at op292
    rw [← op292, Nat.cast_add]
  rw [hv257, hv258] at heq295
  have hargs_len : dom.getAppArgs.length = nP + nI := by
    have h1 := FireAux.natCast_inj_lt59 (Nat.lt_trans hargs_len_lt (by decide))
      (Nat.lt_trans (Nat.add_lt_add hnP_lt hnI_lt) (by decide)) (Value.field.inj heq295)
    simpa using h1
  have hnP_val : ZMod.val (nP : F) = nP :=
    FireAux.val_natCast_lt59 (Nat.lt_trans hnP_lt (by decide))
  obtain ⟨-, hdrop_314, rfl⟩ := FireAux.kexpr_drop ev324 hargs_141
  rw [hnP_val, ← List.map_drop] at hdrop_314
  have hdrop_len : ((dom.getAppArgs.drop nP).map (posOf ps)).length = nI - 0 := by
    simp [hargs_len]
  obtain ⟨rfl, hdropPos_eq⟩ :=
    assert_index_vars_spec c hnI_lt ((dom.getAppArgs.drop nP).map (posOf ps))
      (Nat.zero_le _) hdrop_len hdrop_314 ev309
  simp only [List.drop_zero] at hdropPos_eq
  have hdrop_eq : dom.getAppArgs.drop nP =
      (List.range nI).map (fun t => Ix.Kernel.Expr.bvar (nI - 1 - t)) := by
    have hrhs : (List.range nI).map (fun t => (Ix.Kernel.Expr.bvar (nI - 1 - t) : KExpr)) =
        ((List.range nI).map (fun t => nI - 1 - t)).map Ix.Kernel.Expr.bvar := by
      rw [List.map_map]; rfl
    rw [hrhs] at hdropPos_eq ⊢
    exact FireAux.map_posOf_bvar_inv hdropPos_eq
  obtain ⟨-, htake_389⟩ := FireAux.kexpr_take
    (R := fun h E p => Tm c.κ 0 FireAux.Γ₀ h mI E p)
    (fun _ _ _ _ e r => Tm.mono e r) ev399 hargs_141
  rw [hnP_val, ← List.map_take, hmI_eq] at htake_389
  have hgood3 : Good c cs383 := good.sub (by rw [hc424]; intro z hz; simp [hz])
  obtain ⟨hlift_props, hpins_375⟩ :=
    lower_pins_spec c (ps := ps) (rP := rP) hnI_lt (dom.getAppArgs.take nP)
      hgood3 (ih.mono (by rw [hc424]; ModeledAux.callees_lt)) htake_389 ev385
  let pins : List KExpr := (dom.getAppArgs.take nP).map (Ix.Kernel.Expr.lowerBVars (mI - rP) 0)
  have hpins_eq' : (dom.getAppArgs.take nP).map (Ix.Kernel.Expr.lowerBVars nI 0) = pins := by
    rw [hnI_sub]
  rw [hpins_eq'] at hpins_375
  have hlift_props' : ∀ x ∈ dom.getAppArgs.take nP,
      (x.lowerBVars (mI - rP) 0).liftLooseBVars (mI - rP) 0 = x ∧
      (x.lowerBVars (mI - rP) 0).hasFvar = false ∧
      (x.lowerBVars (mI - rP) 0).looseBVarsBounded rP = true := by
    rw [← hnI_sub]; exact hlift_props
  obtain ⟨hpins_len, hnested⟩ := FireAux.nestedPins_of_parts hle hstrip hfn_dom
    (by rw [hargs_len, hnI_sub]) (by rw [← hnI_sub]; exact hdrop_eq) rfl hlift_props'
  have ext_all : Heap.Extends m77 m375 :=
    ext_141.trans (ev399.heap_extends.trans ev385.heap_extends)
  exact ⟨x_iaddr, x_ilvls, v358, lvls, pins, rfl,
    by rw [hpins_len]; exact hnP_lt, hnested, hlsPos.mono ext_all, hpins_375⟩

theorem rec_comparands_spec (c : Ctx) {x_raddr r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {a : Bytes.Address} {cv : Ix.Kernel.ConstantVal .anon}
    {mI rP : Nat} {rls : List (Ix.Kernel.RecRule .anon)}
    (ev : ObsFn W "KernelModeled::rec_comparands" [x_raddr] h r h' calls)
    (good : Good c calls) (ih : IH c calls)
    (ha : RepAddr h a x_raddr)
    (hfind : c.env.find? (c.κ (ixAddr a)) = some (.recInfo cv mI rP rls)) :
    ∃ (x_iaddr x_ilvls x_pins : SourceValue F) (lvls : List KLevel) (pins : List KExpr),
      r = .tuple [x_iaddr, x_ilvls, x_pins, .field (rP : F)] ∧
      pins.length < 72057594037927936 ∧
      rP < 288230376151711744 ∧
      Ix.Kernel.Tier.nestedPins cv.type mI rP pins.length = some (lvls, pins) ∧
      LvListRep h' (lvls.map (Ix.Kernel.Level.subst cv.levelParams (posLevels cv.levelParams)))
        x_ilvls ∧
      c.tmlk 0 FireAux.Γ₀ rP h' (pins.map (posOf cv.levelParams)) x_pins := by
  obtain ⟨m2, p10, cs16, w33, x_ty, x_np, x_ni, x_nmot, x_nmin, w34, w35, w36, w37, w38, m95,
    cs105, v109, x124, x_iaddr, x_ilvls, x_pins, v173, x202,
    ev18, ld12, op139, op131, ev107, he174, op217, op209, he221, hc222⟩ :=
    Obs.«KernelModeled::rec_comparands».obs ev
  subst he174 he221
  have hgood1 : Good c cs16 := good.sub (by rw [hc222]; intro z hz; simp [hz])
  obtain ⟨ci', hfind', v_ci, hld_ci, hci⟩ :=
    ih.get (.callees .get_ci) (by rw [hc222]; ModeledAux.callees_lt) ev18 x_raddr a rfl hgood1 ha
  rw [hfind] at hfind'; injection hfind' with rfl
  rw [ld12] at hld_ci; injection hld_ci with hv_ci; subst hv_ci
  obtain ⟨p, i_f, m_f, mi_f, hv, rfl, rfl, rfl, rfl, hrP_F, hmI_F, hle, hmI_lt⟩ :=
    FireAux.ciRep_rec_inv hci
  have hx124 : x124 = .field (p + m_f) := by
    simp only [evalBinOp, Except.ok.injEq] at op139; exact op139.symm
  subst hx124
  have hv109 : v109 = .field (rP : F) := by
    simp only [evalBinOp, Except.ok.injEq] at op131
    rw [← op131, hrP_F]
  subst hv109
  have hx202 : x202 = .field (p + m_f) := by
    simp only [evalBinOp, Except.ok.injEq] at op217; exact op217.symm
  subst hx202
  have hv173 : v173 = .field (rP : F) := by
    simp only [evalBinOp, Except.ok.injEq] at op209
    rw [← op209, hrP_F]
  subst hv173
  have hmI_F' : (mI : F) = (rP : F) + i_f := by rw [hmI_F, hrP_F]
  have hgood2 : Good c cs105 := good.sub (by rw [hc222]; intro z hz; simp [hz])
  obtain ⟨x_iaddr', x_ilvls', x_pins', lvls, pins, htuple, hplen, hnested, hilvls, hpins⟩ :=
    rec_major_pins_spec c ev107 hgood2 (ih.mono (by rw [hc222]; ModeledAux.callees_lt))
      (hv.2.2.2 0 FireAux.Γ₀) hmI_F' hle hmI_lt
  injection htuple with h1
  simp only [List.cons.injEq, and_true] at h1
  rcases h1 with ⟨rfl, rfl, rfl⟩
  exact ⟨x_iaddr, x_ilvls, x_pins, lvls, pins, rfl, hplen,
    Nat.lt_of_le_of_lt hle hmI_lt, hnested, hilvls, hpins⟩

/-! ## `level_list_equal` and `inst_pins` -/

theorem level_list_equal_spec :
    ∀ {as bs : List KLevel} {x_a x_b r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      IxVM.Consistency.Bounded calls →
      KernelLevels.RepKLevelList h as x_a →
      KernelLevels.RepKLevelList h bs x_b →
      ObsFn W "KernelModeled::level_list_equal" [x_a, x_b] h r h' calls →
      r ≠ .field 0 →
      LvEqList as bs := by
  intro as
  induction as with
  | nil =>
    intro bs x_a x_b r h h' calls _ ha hb ev hr
    cases Obs.«KernelModeled::level_list_equal».obs ev with
    | Nil_Nil _ ld31 _ _ _ =>
      have hbs := Lib.rep_nil_of_load hb ld31
      subst hbs
      exact LvEqList.refl []
    | Nil_other _ _ _ _ he46 _ _ => exact (hr he46).elim
    | Cons_Nil _ _ ld12 _ _ _ _ => cases Lib.rep_cons_of_load ha ld12
    | Cons_Cons_n1 _ _ _ _ _ _ _ ld12 _ _ _ _ =>
      obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load ha ld12; cases he
    | Cons_Cons_other _ _ _ _ _ _ _ ld12 _ _ _ he167 _ _ =>
      exact (hr he167).elim
  | cons a as ih =>
    intro bs x_a x_b r h h' calls hbnd ha hb ev hr
    cases Obs.«KernelModeled::level_list_equal».obs ev with
    | Nil_Nil ld12 _ _ _ _ => cases Lib.rep_nil_of_load ha ld12
    | Nil_other _ _ _ _ he46 _ _ => exact (hr he46).elim
    | Cons_Nil _ _ _ _ he85 _ _ => exact (hr he85).elim
    | Cons_Cons_other _ _ _ _ _ _ _ _ _ _ _ he167 _ _ => exact (hr he167).elim
    | Cons_Cons_n1 x_x x_xr x_y x_yr m106 cs117 cs143 ld12 ld77 ev119 ev145 hc162 =>
      obtain ⟨a', as', hea, ha_hd, ha_tl⟩ := Lib.rep_cons_of_load ha ld12
      obtain ⟨b', bs', heb, hb_hd, hb_tl⟩ := Lib.rep_cons_of_load hb ld77
      injection hea with h1 h2; subst h1 h2
      injection heb with h3 h4; subst h3 h4
      have hbnd1 : IxVM.Consistency.Bounded cs117 :=
        hbnd.sub (by rw [hc162]; intro z hz; simp [hz])
      obtain ⟨heq_r, ext1⟩ := Levels.levelEqual_step ev119 x_x x_y rfl hbnd1 a' b' ha_hd hb_hd
      have heq_true : KernelLevels.levelEqual a' b' = true := by
        cases hbe : KernelLevels.levelEqual a' b'
        · simp [hbe] at heq_r
        · rfl
      have hhead : LvEq a' b' := KernelLevels.levelEqual_eq_true_sound heq_true
      have hbnd2 : IxVM.Consistency.Bounded cs143 :=
        hbnd.sub (by rw [hc162]; intro z hz; simp [hz])
      have htail : LvEqList as' bs' :=
        ih hbnd2 (ha_tl.mono ext1) (hb_tl.mono ext1) ev145 hr
      exact fun φ => ⟨hhead φ, htail φ⟩

theorem inst_pins_run (c : Ctx) {ps : List Ix.Kernel.LevelParam} {usK : List KLevel}
    {As : List KExpr} {d rP : Nat} {Γ : Nat → KExpr}
    (hperm : ps.Perm (List.range ps.length)) (hlen : usK.length = ps.length)
    (hrP_le : rP ≤ As.length) :
    ∀ (pins : List KExpr) {x_pins x_us x_substs r : SourceValue F}
      {h h' : Heap F} {calls : List (Call F)},
      Good c calls → IH c calls →
      c.tmlk 0 FireAux.Γ₀ rP h (pins.map (posOf ps)) x_pins →
      LvListRep h usK x_us →
      c.tml d Γ h (As.take rP).reverse x_substs →
      ObsFn W "KernelModeled::inst_pins" [x_pins, x_us, x_substs] h r h' calls →
      c.tml d Γ h'
        (pins.map fun p => Ix.Kernel.Expr.instSpine (As.take rP) (rP - 1)
          (p.instantiateLevelParams ps usK)) r := by
  intro pins
  induction pins with
  | nil =>
    intro x_pins x_us x_substs r h h' calls _ _ hpins _ _ ev
    cases Obs.«KernelModeled::inst_pins».obs ev with
    | Nil _ he24 hm23 _ =>
      subst he24 hm23
      exact TmL.store_nil h
    | Cons _ _ _ _ _ _ _ _ _ _ _ ld12 _ _ _ _ _ _ =>
      obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hpins ld12
      cases he
  | cons p rest ih_list =>
    intro x_pins x_us x_substs r h h' calls good ih hpins hus hsubsts ev
    cases Obs.«KernelModeled::inst_pins».obs ev with
    | Nil ld12 _ _ _ =>
      cases Lib.rep_nil_of_load hpins ld12
    | Cons x_p x_rest v46 m47 cs57 v84 v85 m87 cs95 m122 cs130 ld12 ev59 he80 hm79 ev97 ev132
        hc157 =>
      subst he80 hm79
      obtain ⟨pPos, restPos, heq_cons, hp, hrest⟩ := Lib.rep_cons_of_load hpins ld12
      simp only [List.map_cons, List.cons.injEq] at heq_cons
      rcases heq_cons with ⟨rfl, rfl⟩
      have hgood1 : Good c cs57 := good.sub (by rw [hc157]; intro z hz; simp [hz])
      have hv46_0 :=
        ih.get (.subst .expr_inst_levels) (by rw [hc157]; ModeledAux.callees_lt) ev59
          x_p x_us rfl hgood1 FireAux.Γ₀ rP (posOf ps p) usK hp hus
      rw [FireAux.posOf_instantiateLevelParams_perm hperm hlen p] at hv46_0
      have hv46_d : c.tmk d Γ rP m47 (p.instantiateLevelParams ps usK) v46 :=
        hv46_0.of_depth_zero d
      have ext1 := ev59.heap_extends
      have hsubsts_47 : c.tml d Γ m47 (As.take rP).reverse x_substs :=
        TmL.mono ext1 hsubsts
      have hsub_len : ZMod.val (0 : F) + (As.take rP).reverse.length = rP := by
        rw [ZMod.val_zero, Nat.zero_add, List.length_reverse, List.length_take]
        omega
      have hgood2 : Good c cs95 := good.sub (by rw [hc157]; intro z hz; simp [hz])
      have hv84 :=
        ih.get (.subst .expr_inst_many) (by rw [hc157]; ModeledAux.callees_lt) ev97
          v46 x_substs 0 rfl hgood2 d Γ (p.instantiateLevelParams ps usK) (As.take rP).reverse
          (by rwa [hsub_len]) hsubsts_47
      rw [ZMod.val_zero, FireAux.instSpine_eq_instantiateList_all hrP_le] at hv84
      have ext2 := ev97.heap_extends
      have ext12 := ext1.trans ext2
      have hrest_87 : c.tmlk 0 FireAux.Γ₀ rP m87 (rest.map (posOf ps)) x_rest :=
        repList_heapMono₂ kexprListEnum (fun _ _ _ _ e r => Tm.mono e r) ext12 hrest
      have hgood3 : Good c cs130 := good.sub (by rw [hc157]; intro z hz; simp [hz])
      have hv85 := ih_list hgood3 (ih.mono (by rw [hc157]; ModeledAux.callees_lt))
        hrest_87 (hus.mono ext12) (TmL.mono ext2 hsubsts_47) ev132
      have ext3 := ev132.heap_extends
      exact TmL.store_cons (hv84.mono ext3) hv85

end FireCompareAux

/-- `KernelModeled::fire_compare`: modeled recursor firing comparison (`FamilyFew` when
`block_is_modeled = 0`, or `FireCompared` against `Tier.nestedPins`). -/
theorem fire_compare_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelModeled::fire_compare" args h r h' calls) (ih : IH c calls) :
    Specs.Callees.fire_compare c args h r h' calls := by
  intro rc head us spine major types hargs good hrc ap lp hhead a cv mI rP rls ha hfind
    usK hus hus_len d Γ htypes As M hAs hM hr
  subst hargs
  cases Obs.«KernelModeled::fire_compare».obs ev with
  | other v1 ld12 hne422 _ _ _ =>
    rw [hhead] at ld12; injection ld12 with hv1; subst hv1
    exact (hne422 [ap, lp] rfl rfl).elim
  | Const_other_Const_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _ he335 _ _ =>
    exact (hr he335).elim
  | Const_other_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _ he419 _ _ =>
    exact (hr he419).elim
  | Const_n0 x_raddr w20 m32 cs43 v46 m48 cs56 ld12 ev58 ev45 _ _ hc73 =>
    rw [hhead] at ld12
    injection ld12 with _ _ hfields
    injection hfields with hap _
    subst hap
    have hgood1 : Good c cs56 := good.sub (by rw [hc73]; intro z hz; simp [hz])
    obtain ⟨b, np, k, mdom, dom, i, us_dom, hb, hpi1, hpi2, hfn_dom⟩ :=
      FireCompareAux.rec_family_block_spec c ev58 hgood1
        (ih.mono (by rw [hc73]; ModeledAux.callees_lt)) ha hfind
    have hgood2 : Good c cs43 := good.sub (by rw [hc73]; intro z hz; simp [hz])
    have hbim := ih.get (.callees .block_is_modeled) (by rw [hc73]; ModeledAux.callees_lt) ev45
    have hfew : FewInductives c (ixAddr b) :=
      ModeledAux.fewInductives_of_modeled_zero c hbim hgood2 hb
    exact .inl ⟨np, k, mdom, dom, ixAddr b, i, us_dom, hpi1, hpi2, hfn_dom, hfew⟩
  | Const_other_Const_other x_raddr w20 v31 m32 cs43 v46 m48 cs56 m79 cs89 w103 x_ilvls x_pins x_rp
      v124 m125 cs135 v154 m155 cs165 v168 m170 cs178 v197 m198 cs208 m236 cs246 x_mh x_margs
      w289 x_usj v300 m301 cs312 cs345 v349 m360 cs368 v372 m381 cs389
      ld12 ev58 ev45 _ ev91 ev137 ev180 ev167 ev210 ev248 ld281 ev314 hne338 ev391 ev370 ev347
      hc414 =>
    rw [hhead] at ld12
    injection ld12 with _ _ hfields
    injection hfields with hap _
    subst hap
    -- Extract `cv.levelParams.Perm` via `get_ci` inside `rec_comparands`? Even simpler:
    -- `rec_comparands` itself invokes `get_ci`, and we also get `hperm` from `rec_comparands`'s
    -- first step or include `hperm` in `rec_comparands_spec`! Let's get `hperm` cleanly:
    have hperm : cv.levelParams.Perm (List.range cv.levelParams.length) := by
      obtain ⟨m_rc, p_rc, cs_rc, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        ev_ci, ld_ci, _, _, _, _, _, _, _, hc_rc⟩ := Obs.«KernelModeled::rec_comparands».obs ev91
      have ext_h_32 := ev58.heap_extends.trans ev45.heap_extends
      have hgood_ci : Good c cs_rc :=
        good.sub (by rw [hc414, hc_rc]; intro z hz; simp [hz])
      obtain ⟨ci', hfind', v_ci, hld_ci, hci⟩ :=
        ih.get (.callees .get_ci) (by rw [hc414, hc_rc]; ModeledAux.callees_lt) ev_ci
          x_raddr a rfl hgood_ci (Bytes.repAddressRef_heapMono₂ addrTy ext_h_32 ha)
      rw [hfind] at hfind'; injection hfind' with rfl
      rw [ld_ci] at hld_ci; injection hld_ci with hv_ci; subst hv_ci
      obtain ⟨_, _, _, _, hv, -⟩ := FireAux.ciRep_rec_inv hci
      exact hv.2.2.1
    have ext_32 := ev58.heap_extends.trans ev45.heap_extends
    have hgood_rc : Good c cs89 := good.sub (by rw [hc414]; intro z hz; simp [hz])
    obtain ⟨x_iaddr', x_ilvls', x_pins', lvls, pins, htuple_rc, hplen, hrP_lt,
        hnested, hilvls_79, hpins_79⟩ :=
      FireCompareAux.rec_comparands_spec c ev91 hgood_rc
        (ih.mono (by rw [hc414]; ModeledAux.callees_lt))
        (Bytes.repAddressRef_heapMono₂ addrTy ext_32 ha) hfind
    injection htuple_rc with h1
    simp only [List.cons.injEq, and_true] at h1
    rcases h1 with ⟨rfl, rfl, rfl, rfl⟩
    have ext_79 := ext_32.trans ev91.heap_extends
    obtain ⟨ls_ilvls, hrep_ilvls, heq_ilvls⟩ := hilvls_79
    obtain ⟨ls_us, hrep_us, heq_us⟩ := hus.mono ext_79
    have hbnd_135 : IxVM.Consistency.Bounded cs135 :=
      good.2.sub (by rw [hc414]; intro z hz; simp [hz])
    obtain ⟨-, hv124, ext_125_step⟩ :=
      Levels.levelListInst_step ev137 x_ilvls us rfl hbnd_135 ls_ilvls ls_us hrep_ilvls hrep_us
    have ext_125 := ext_79.trans ext_125_step
    have hrP_val : ZMod.val (rP : F) = rP :=
      FireAux.val_natCast_lt59 (Nat.lt_trans hrP_lt (by decide))
    obtain ⟨hrP_le_val, htake_170⟩ :=
      FireAux.kexpr_take tmE_heapMono₂ ev180 (TmL.mono ext_125 hAs)
    rw [hrP_val] at hrP_le_val htake_170
    have hrev_155 : c.tml d Γ m155 (As.take rP).reverse v154 :=
      FireAux.kexpr_reverse tmE_heapMono₂ ev167 htake_170
    have ext_79_155 := ext_125_step.trans (ev180.heap_extends.trans ev167.heap_extends)
    have ext_155 := ext_79.trans ext_79_155
    have hpins_155 : c.tmlk 0 FireAux.Γ₀ rP m155 (pins.map (posOf cv.levelParams)) x_pins :=
      repList_heapMono₂ kexprListEnum (fun _ _ _ _ e r => Tm.mono e r) ext_79_155 hpins_79
    have hgood_inst : Good c cs208 := good.sub (by rw [hc414]; intro z hz; simp [hz])
    have hv197 := FireCompareAux.inst_pins_run c hperm hus_len hrP_le_val pins hgood_inst
      (ih.mono (by rw [hc414]; ModeledAux.callees_lt)) hpins_155 (hus.mono ext_155) hrev_155 ev210
    have ext_198 := ext_155.trans ev210.heap_extends
    have hgood_sp : Good c cs246 := good.sub (by rw [hc414]; intro z hz; simp [hz])
    obtain ⟨hd_m, sp_m, H_m, M_args, htuple_m, hH_m, hM_args, hM_eq⟩ :=
      ih.get (.subst .collect_spine) (by rw [hc414]; ModeledAux.callees_lt) ev248 major rfl
        hgood_sp d Γ 0 M (Tm.mono ext_198 hM)
    injection htuple_m with h2
    simp only [List.cons.injEq, and_true] at h2
    rcases h2 with ⟨rfl, rfl⟩
    obtain ⟨a_mj, usj, rfl, -, husj⟩ := hH_m.const_of_load ld281
    have hM_fn : M.getAppFn = .const (c.κ (ixAddr a_mj)) usj := by
      rw [hM_eq, ModeledAux.getAppFn_mkAppN]; rfl
    have hM_args_eq : M.getAppArgs = M_args := by
      rw [hM_eq, ModeledAux.getAppArgs_mkAppN]; simp [Ix.Kernel.Expr.getAppArgs]
    subst hM_args_eq
    obtain ⟨ls_usj, hrep_usj, heq_usj⟩ := husj
    have ext_125_236 :=
      ev180.heap_extends.trans (ev167.heap_extends.trans
        (ev210.heap_extends.trans ev248.heap_extends))
    have hbnd_312 : IxVM.Consistency.Bounded cs312 :=
      good.2.sub (by rw [hc414]; intro z hz; simp [hz])
    have hlveq_raw : LvEqList ls_usj (KernelLevels.substLevelList ls_ilvls ls_us) :=
      FireCompareAux.level_list_equal_spec hbnd_312 hrep_usj (hv124.mono ext_125_236) ev314 hne338
    have hlveq_final : LvEqList usj (lvls.map (Ix.Kernel.Level.subst cv.levelParams usK)) :=
      FireAux.lvEqList_subst_chain hperm hus_len heq_usj hlveq_raw heq_ilvls heq_us
    have ext_198_301 := ev248.heap_extends.trans ev314.heap_extends
    have hv197_301 := TmL.mono ext_198_301 hv197
    obtain ⟨hv372, rfl⟩ := FireAux.kexpr_length ev391 hv197_301
    rw [List.length_map] at hv372
    subst hv372
    have hplen_val : ZMod.val (pins.length : F) = pins.length :=
      FireAux.val_natCast_lt59 (Nat.lt_trans hplen (by decide))
    obtain ⟨-, hv349⟩ :=
      FireAux.kexpr_take tmE_heapMono₂ ev370 (TmL.mono ev314.heap_extends hM_args)
    rw [hplen_val] at hv349
    have ext_360 :=
      ext_198.trans (ext_198_301.trans ev370.heap_extends)
    have hgood_de : Good c cs345 := good.sub (by rw [hc414]; intro z hz; simp [hz])
    have hdefeq :=
      ih.get (.callees .defeq_list_ok) (by rw [hc414]; ModeledAux.callees_lt) ev347
        rc v349 v197 types rfl hgood_de (RCRep.mono ext_360 hrc) d Γ
        ⟨htypes.1.mono ext_360, htypes.2⟩
        (M.getAppArgs.take pins.length)
        (pins.map fun p => Ix.Kernel.Expr.instSpine (As.take rP) (rP - 1)
          (p.instantiateLevelParams cv.levelParams usK))
        hv349 (TmL.mono ev370.heap_extends hv197_301) hr
    exact .inr ⟨lvls, pins, c.κ (ixAddr a_mj), usj, hnested, hM_fn, hlveq_final, hdefeq⟩

/-- `KernelModeled::fire_ok`: returns `1` immediately when `nmot = 1`, or delegates to
`KernelModeled::fire_compare`. -/
theorem fire_ok_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelModeled::fire_ok" args h r h' calls) (ih : IH c calls) :
    Specs.Callees.fire_ok c args h r h' calls := by
  intro rc nmot head us spine major types hargs good hrc ap lp hhead a cv mI rP rls ha hfind
    usK hus hus_len d Γ htypes As M hAs hM hr
  subst hargs
  cases Obs.«KernelModeled::fire_ok».obs ev with
  | n0 op17 _ _ _ =>
    cases nmot with
    | field f =>
      simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op17
      exact .inl (congrArg Value.field (sub_eq_zero.mp op17))
    | _ => simp [evalBinOp] at op17
  | other v1 cs33 _ _ ev35 hc84 =>
    have hgood1 : Good c cs33 := good.sub (by rw [hc84]; intro z hz; simp [hz])
    have hfc :=
      ih.get (.callees .fire_compare) (by rw [hc84]; ModeledAux.callees_lt) ev35
        rc head us spine major types rfl hgood1 hrc ap lp hhead a cv mI rP rls ha hfind
        usK hus hus_len d Γ htypes As M hAs hM hr
    exact .inr hfc

end IxVM.Refinement.Core
