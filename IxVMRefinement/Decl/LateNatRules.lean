import IxVMRefinement.Decl.LateWrapRel

/-! # The native recursor's rule generators at any member index and keying

The specifications of `KernelCheck::nat_ctor`, `nat_minors`, `nat_minor_ty`, `nat_ih_apps`,
`nat_rule_rhs` and `nat_check_rules` (`NativeRecCheck.lean`, `NativeRec.lean`,
`NativeRecRules.lean`) are stated there at block member `0`, at the table's keying (under which
every key resolves) and under the unrestricted load contract. Here they are restated

* at any member index `idx` (the circuit passes the parent inductive's index, and the inductive
  of a native block need not be its first member): the constructor projections read are
  `cprjAddr b₀ idx j`;
* at any keying `κ`, assuming the resolution only of the keys the generators build constants
  at: the recursor's address (the induction hypotheses apply it) and the constructors' projection
  addresses (each minor premise applies its constructor);
* under `WrapLoads` (`LateWrapRel.lean`) in place of the load contract, at a lookup `find?`. -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (Expr Level LevelParam ConstantVal ConstantInfo RecRule Declaration)
open Ix.Kernel.Rules (Red DefEq Infer Annot)
open Ix.Kernel.Semantics (letFree)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- Per-constructor `get_ci_cprj` load witness at member `idx` of the block `b₀`: each entry
`(C, nF, R₀, C₀, recIdx)` carries the key of the constructor projection `j` of the member, the
field count, the raw constructor type `R₀`, the annotated constructor type `C₀` and the recursive
field indices. -/
def NatCtorLoadI (κ : _root_.Address → KKey) (b₀ : Bytes.Address) (idx k : Nat)
    (ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat))
    (x_block : SourceValue F) (calls_bound : List (Call F)) : Prop :=
  ∀ (j : Nat), j < ctors_info.length →
    ∀ (p9 : SourceValue F) (h m2 : Heap F) (cs15 : List (Call F))
      (w45 x_cty0 w46 w47 w48 w49 x_nf w50 : SourceValue F),
      (∀ x ∈ cs15, x ∈ calls_bound) →
      Bytes.RepAddressRef addrTy h b₀ x_block →
      ObsFn W "Ingress::get_ci_cprj" [x_block, .field (idx : F), .field (j : F)] h p9 m2 cs15 →
      loadValue m2 p9 = .ok (.construct kciEnum "Ctor"
        [w45, x_cty0, w46, w47, w48, w49, x_nf, w50]) →
      ∀ info, ctors_info[j]? = some info →
        info.1 = κ (cprjAddr (ixAddr b₀) idx j) ∧
        x_nf = .field (info.2.1 : F) ∧
        RawTm κ 0 (fun _ => default) m2 0
          (posOf (List.range k) info.2.2.1) (posOf (List.range k) info.2.2.2.1) x_cty0

theorem NatCtorLoadI.mono_calls {κ : _root_.Address → KKey} {b₀ : Bytes.Address} {idx k : Nat}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)} {x_block : SourceValue F}
    {cs₁ cs₂ : List (Call F)} (hsub : ∀ x ∈ cs₁, x ∈ cs₂)
    (h : NatCtorLoadI κ b₀ idx k ctors_info x_block cs₂) :
    NatCtorLoadI κ b₀ idx k ctors_info x_block cs₁ :=
  fun j hj p9 hp m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50 hs =>
    h j hj p9 hp m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50 (fun x hx => hsub x (hs x hx))

/-- The member-`0` load witness is the load witness at index `0`. -/
theorem NatCtorLoadI.of_natCtorLoad {κ : _root_.Address → KKey} {b₀ : Bytes.Address} {k : Nat}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)} {x_block : SourceValue F}
    {cs : List (Call F)} (h : NatCtorLoad κ b₀ k ctors_info x_block cs) :
    NatCtorLoadI κ b₀ 0 k ctors_info x_block cs := by
  intro j hj p9 hp m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50 hs hb ev ld info hinfo
  have ev' : ObsFn W "Ingress::get_ci_cprj" [x_block, .field 0, .field (j : F)] hp p9 m2 cs15 := by
    simpa using ev
  exact h j hj p9 hp m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50 hs hb ev' ld info hinfo

/-- `KernelCheck::nat_ctor` at member `idx` loads constructor `j`, instantiates its universe
parameters to the recursor's frame `rlps`, verifies that its return spine mentions `T` nowhere in
its indices, and computes its recursive field indices `recIdx` along with
`structUsedLater = false` on each. -/
theorem natI_ctor_spec {κ : _root_.Address → KKey}
    {T : KKey} {b₀ bT : Bytes.Address} {idx k nP nIdx num_ctors j : Nat} {large : Bool}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)}
    {info : KKey × Nat × KExpr × KExpr × List Nat}
    {x_block x_t x_lps r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hT : κ (ixAddr bT) = T)
    (hκ_inj : ∀ a : Bytes.Address, κ (ixAddr a) = T → a = bT)
    (hj : j < ctors_info.length)
    (hinfo : ctors_info[j]? = some info)
    (hwf : NatCtorInfoWf T k large nP nIdx num_ctors info)
    (hload : NatCtorLoadI κ b₀ idx k ctors_info x_block cs)
    (hbnd : IxVM.Consistency.Bounded cs)
    (hb₀ : Bytes.RepAddressRef addrTy h b₀ x_block)
    (hbT : Bytes.RepAddressRef addrTy h bT x_t)
    (hlps : RepKLevelList h
      ((List.range k).map (fun i => Level.param ((if large then 1 else 0) + i))) x_lps)
    (ev : ObsFn W "KernelCheck::nat_ctor"
      [x_block, .field (idx : F), .field (j : F), x_t, x_lps, .field (nP : F), .field (nIdx : F),
        .field ((if large then 1 else 0 : Nat) : F)]
      h r h' cs) :
    let rlps := if large then k :: List.range k else List.range k
    ∃ x_cty x_rec_idx,
      r = .tuple [x_cty, .field (info.2.1 : F), x_rec_idx] ∧
      RawTm κ 0 (fun _ => default) h' 0 (posOf rlps info.2.2.1) (posOf rlps info.2.2.2.1) x_cty ∧
      RepList fieldListEnum (fun _ (i : Nat) v => v = .field (i : F)) h'
        info.2.2.2.2 x_rec_idx ∧
      (∀ i ∈ info.2.2.2.2, Ix.Kernel.structUsedLater info.2.2.2.1 nP i = false) := by
  intro rlps
  dsimp only [rlps]
  rcases Obs.«KernelCheck::nat_ctor».obs ev with
    ⟨m2, p9, cs15, w45, x_cty0, w46, w47, w48, w49, x_nf, w50,
      v136, m137, cs139, m146, cs156, v159, m161, cs169, v173, w200, x_rargs,
      v222, m225, cs233, v236, m239, cs247, v284, m301, cs309,
      ev17, ld11, sg144, op194, ev171, ev158, ev249, ev235, heq279, htup_out, ev311, hm_out, hc⟩
  subst hc htup_out hm_out
  obtain ⟨_, hnf_eq, hRaw0⟩ :=
    hload j hj p9 h m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50
      (fun x hx => by simp [hx]) hb₀ ev17 ld11 info hinfo
  subst hnf_eq
  let nF := info.2.1
  let R₀ := info.2.2.1
  let C₀ := info.2.2.2.1
  let recIdx := info.2.2.2.2
  have hnPF_lt : nP + nF < 2147483648 := hwf.nf_lt
  -- Step 1: `Seg1` produces `RawTm` for `(posOf rlps R₀, posOf rlps C₀)` at `v136`
  have hRaw_rlps :
      RawTm κ 0 (fun _ => default) m137 0
        (posOf (if large then k :: List.range k else List.range k) R₀)
        (posOf (if large then k :: List.range k else List.range k) C₀) v136 ∧
      Heap.Extends m2 m137 := by
    cases sg144 with
    | n0 hv104 hv136 hm137 _ =>
      subst hv136 hm137
      cases large with
      | false => exact ⟨hRaw0, Heap.Extends.refl _⟩
      | true =>
        simp only [↓reduceIte] at hv104
        exact absurd (Value.field.inj hv104) one_ne_zero
    | other cs116 hne109 ev118 hc_sg =>
      subst hc_sg
      cases large with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hne109
        exact absurd rfl hne109
      | true =>
        simp only [↓reduceIte] at hlps ⊢
        have hbnd_inst : IxVM.Consistency.Bounded cs116 :=
          RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
        have hlps_m2 := RepKLevelList.mono hlps ev17.heap_extends
        have hlv_rep : LvListRep m2 ((List.range k).map (fun i => Level.param (1 + i))) x_lps :=
          ⟨_, hlps_m2, LvEqList.refl _⟩
        have hinst := expr_inst_levels_rawTm hbnd_inst hRaw0 hlv_rep ev118
        simp only [List.length_map, List.length_range] at hinst
        rw [posOf_range, posOf_range, ← posOf_large_eq_inst_shifted k hwf.lps_R,
          ← posOf_large_eq_inst_shifted k hwf.lps_C] at hinst
        exact ⟨hinst, ev118.heap_extends⟩
  rcases hRaw_rlps with ⟨hRaw137, ext_2_137⟩
  have ext_h_137 := ev17.heap_extends.trans ext_2_137
  -- Step 2: `peel_n_foralls`, `collect_spine`, `drop`, `nat_none_mention`
  rw [evalBinOp_add_nat nP nF op194] at ev171
  obtain ⟨hm161_eq, _, _, _, _, _, _, hmid⟩ :=
    peel_n_foralls_rawTm_spec (nP + nF) (by omega) hRaw137 ev171
  rw [hm161_eq] at ev158
  obtain ⟨hd_sp, sp_sp, _, _, _, Eas, htup_sp, _, hEas, _, _, _, _⟩ :=
    collect_spine_rawTm_spec hmid ev158
  injection htup_sp with hsp_list
  injection hsp_list with _ hsp_tl
  injection hsp_tl with hsp_eq _
  subst hsp_eq
  rw [Nat.zero_add] at hEas
  obtain ⟨_, hdrop, hm239_eq⟩ := kexpr_list_drop_spec' (by omega) ev249 hEas
  rw [hm239_eq, heq279] at ev235
  have ext_h_146 := ext_h_137.trans ev158.heap_extends
  have hbT_146 := Bytes.repAddressRef_heapMono₂ addrTy ext_h_146 hbT
  have hm225 := nat_none_mention_one_spec hdrop hbT_146 ev235
  rw [hm225] at ev311
  -- Step 3: `nat_rec_idx`
  let rlps' := if large then k :: List.range k else List.range k
  obtain ⟨rcbs₀, rus₀, rargs₀, hsR₀⟩ := hwf.strip_R
  obtain ⟨ecbs₀, eus₀, eargs₀, hsC₀⟩ := hwf.strip_C
  have hsR_pos := ilp_stripPis rlps' (posLevels rlps') (nP + nF) hsR₀
  change (posOf rlps' R₀).stripPis (nP + nF) = _ at hsR_pos
  have hsE_pos := ilp_stripPis rlps' (posLevels rlps') (nP + nF) hsC₀
  change (posOf rlps' C₀).stripPis (nP + nF) = _ at hsE_pos
  have hnp_pos : noProjAt T (posOf rlps' C₀) = true := by
    unfold posOf
    rw [noProjAt_ilp]
    exact hwf.noProj_C
  obtain ⟨hnp_doms, _⟩ := noProjAt_stripPis_binder (nP + nF) hnp_pos hsE_pos
  have hnp_dom_f : ∀ i < nF,
      noProjAt T ((ecbs₀.map (fun b => (posOf rlps' b.1,
        { b.2 with pw := Level.substPW rlps' (posLevels rlps') b.2.pw }))).getD
        (nP + i) default).1 = true :=
    fun i hi => hnp_doms (nP + i) (by omega)
  have hbnd_rec : IxVM.Consistency.Bounded cs309 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have ev311' : ObsFn W "KernelCheck::nat_rec_idx"
      [v136, x_t, x_lps, .field (nP : F), .field (nIdx : F), .field (nF : F),
        .field ((0 : Nat) : F)]
      m146 v284 h' cs309 := by
    simpa using ev311
  obtain ⟨hrep_idx, hunused_idx⟩ :=
    nat_rec_idx_spec hT hκ_inj (by omega) hsR_pos hsE_pos hnp_dom_f nF 0 (by omega) hbnd_rec
      (hRaw137.mono ev158.heap_extends) hbT_146 ev311'
  have hrec_eq := hwf.recIdx_eq _ _ hsE_pos
  rw [← hrec_eq] at hrep_idx hunused_idx
  refine ⟨v136, v284, rfl, (hRaw137.mono ev158.heap_extends).mono ev311'.heap_extends,
    hrep_idx, fun i hi => ?_⟩
  obtain ⟨hi_lt, _⟩ := hwf.rec_spines i hi
  obtain ⟨ebs₁, emid, hsE₁, hbvarF⟩ := hunused_idx i hi
  have hsplit : nP + nF = (nP + i + 1) + (nF - 1 - i) := by omega
  have hsC₀' : C₀.stripPis ((nP + i + 1) + (nF - 1 - i)) =
      some (ecbs₀, Expr.mkAppN (.const T eus₀) eargs₀) := by
    rwa [← hsplit]
  obtain ⟨cbs₁, cbody₁, _, hsC₁, _, _, _⟩ := stripPis_split (nP + i + 1) (nF - 1 - i) hsC₀'
  exact structUsedLater_false_of_posOf_stripPis hsC₁ hsE₁ hbvarF

/-- `KernelCheck::nat_minor_ty` builds `cMinorTy C clvls nP nF o ℓ.zeronessOf Ecty recIdx`, at a
keying under which the constructor's key resolves. -/
theorem natI_minor_ty_spec {κ : _root_.Address → KKey} {Γ₀ : Nat → KExpr}
    {T C : KKey} {bC : Bytes.Address} [hC_res : Resolved (κ (ixAddr bC))]
    {clvls : List KLevel} {nP nF o : Nat} {ℓ : KLevel}
    {Rcty Ecty : KExpr} {rus eus : List KLevel} {rargs eargs : List KExpr}
    {rcbs ecbs : List (KExpr × Ix.Kernel.BinderMeta)} {recIdx : List Nat}
    {pcprj plps ppw pcty prec r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hC : κ (ixAddr bC) = C)
    (ho : 1 ≤ o)
    (hsR : Rcty.stripPis (nP + nF) = some (rcbs, Expr.mkAppN (.const T rus) rargs))
    (hsE : Ecty.stripPis (nP + nF) = some (ecbs, Expr.mkAppN (.const T eus) eargs))
    (hall : ∀ i ∈ recIdx, i < nF ∧
      RawRecSpine T (rcbs.getD (nP + i) default).1 (ecbs.getD (nP + i) default).1)
    (hlt_base : nP + o + nF + recIdx.length < 2305843009213693952)
    (hbnd : IxVM.Consistency.Bounded cs)
    (hcprj : Bytes.RepAddressRef addrTy h bC pcprj)
    (hlps : RepKLevelList h clvls plps)
    (hpw : RepKLevel h ℓ ppw)
    (hRaw : RawTm κ 0 Γ₀ h 0 Rcty Ecty pcty)
    (hrec : RepList fieldListEnum (fun _ (i : Nat) v => v = .field (i : F)) h recIdx prec)
    (ev : ObsFn W "KernelCheck::nat_minor_ty"
      [pcprj, plps, .field (nP : F), .field (nF : F), .field (o : F), ppw, pcty, prec]
      h r h' cs) :
    ∃ mty,
      cMinorTy C clvls nP nF o ℓ.zeronessOf Ecty recIdx = some mty ∧
      Tm κ 0 Γ₀ h' (nP + o) mty r := by
  rcases Obs.«KernelCheck::nat_minor_ty».obs ev with
    ⟨v1, m2, cs12, m32, cs42, v45, m47, cs55, w77, x_rargs, v88, m89, cs99, v103, m105,
      m134, cs142, v145, v146, m148, cs156, v159, m185, cs193, v211, m212, cs222,
      v225, v226, m229, cs237, v241, m243, v255, x262, m281, cs289, v292, m295, cs303,
      v306, m310, cs318, m359, cs367, cs387, v392, v393, m410, cs418, m445, cs453,
      ev14, ev57, ev44, hm105, op174, ev158, ev195, ev144, ev101, hm243, op277, op269,
      ev320, ev305, ev291, ev239, ev369, ev224, ev420, ev455, ev389, hc⟩
  subst hc
  -- Step 1 & 2: peel `nP` then `nF` Pis on `pcty`
  obtain ⟨hm2, rbsP, ebsP, Rq, Eq, hsRP, hsEP, hRq⟩ :=
    peel_n_foralls_rawTm_bounded nP (by omega) hRaw ev14
  rw [hm2] at ev57
  obtain ⟨hm47, rbsF, ebsF, Rr, Er, hsRF, hsEF, hRr⟩ :=
    peel_n_foralls_rawTm_bounded nF (by omega) hRq ev57
  rw [hm47] at ev44
  obtain ⟨bsP_R, q2_R, bsF_R, hsRP', hsRF', _, _⟩ := stripPis_split nP nF hsR
  rw [hsRP] at hsRP'; injection hsRP' with hp; injection hp with _ hRq_eq; subst hRq_eq
  rw [hsRF] at hsRF'; injection hsRF' with hp; injection hp with _ hRr_eq; subst hRr_eq
  obtain ⟨bsP_E, q2_E, bsF_E, hsEP', hsEF', _, _⟩ := stripPis_split nP nF hsE
  rw [hsEP] at hsEP'; injection hsEP' with hp; injection hp with _ hEq_eq; subst hEq_eq
  rw [hsEF] at hsEF'; injection hsEF' with hp; injection hp with _ hEr_eq; subst hEr_eq
  -- Step 3: `collect_spine` on `v45` (`nP + nF` depth)
  have hRr' : RawTm κ 0 Γ₀ h (nP + nF)
      (Expr.mkAppN (.const T rus) rargs) (Expr.mkAppN (.const T eus) eargs) v45 := by
    simpa [Nat.zero_add] using hRr
  obtain ⟨hd, sp, Rh, Eh, Ras, Eas, htup, hH, hEas, _, hR_sp, hE_sp, hnot_app⟩ :=
    collect_spine_rawTm_spec hRr' ev44
  injection htup with hl; injection hl with h1 hl; injection hl with h2
  subst h1 h2
  have hRh_fn : Rh = .const T rus := by
    have hfn := congrArg Expr.getAppFn hR_sp
    rw [nat_getAppFn_mkAppN, nat_getAppFn_mkAppN] at hfn
    cases Rh with
    | app f a => exact (hnot_app f a rfl).elim
    | bvar _ | fvar _ _ | sort _ | const _ _ | lam _ _ _ | forallE _ _ _ | letE _ _ _ _
    | lit _ | proj _ _ _ => exact hfn.symm
  subst hRh_fn
  have hEh := hH.const_left_inv
  subst hEh
  obtain ⟨-, heus_eq, heas_eq⟩ := mkAppN_const_inj hE_sp
  subst heus_eq
  rw [← heas_eq] at hEas
  -- Step 4 & 5: `v88 = Expr.mkAppN (.const C clvls) (structPsAt (o + nF) nP ++ structPsAt 0 nF)`
  have ext_m105 : Heap.Extends m32 m105 := by rw [hm105]; exact Heap.Extends.snoc _ _
  have hC_const : Tm κ 0 Γ₀ m105 (nP + o + nF) (.const C clvls)
      (.ptr (.enum kexprEnum) m32.length) := by
    rw [hm105, ← hC]
    exact .const (by simp)
      (Bytes.repAddressRef_heapMono₂ addrTy (ev44.heap_extends.trans (Heap.Extends.snoc _ _)) hcprj)
      (hlps.mono (ev44.heap_extends.trans (Heap.Extends.snoc _ _))) (LvEqList.refl clvls)
  rw [evalBinOp_add_nat o nF op174] at ev158
  have hps1 := nat_ps_at_bounded (κ := κ) (d := 0) (Γ := Γ₀) nP (o + nF) (nP + o + nF) (by omega) (by omega) ev158
  have hps2 := nat_ps_at_bounded (κ := κ) (d := 0) (Γ := Γ₀) nF 0 (nP + o + nF) (by omega) (by omega) ev195
  have hps12 := kexpr_list_concat_spec' ev144 (tmRepList_mono ev195.heap_extends hps1) hps2
  have hv88 := nat_app_n_spec
    ((hC_const.mono (ev158.heap_extends.trans (ev195.heap_extends.trans ev144.heap_extends))))
    hps12 ev101
  -- Step 6–8: `v225 = Expr.mkAppN (.bvar (nF + o - 1)) (...)`
  rw [evalBinOp_add_nat nF o op277] at op269
  rw [evalBinOp_sub_nat (by omega : 1 ≤ nF + o) op269] at hm243
  have ext_m243 : Heap.Extends m89 m243 := by rw [hm243]; exact Heap.Extends.snoc _ _
  have hbvar_mot : Tm κ 0 Γ₀ m243 (nP + o + nF) (.bvar (nF + o - 1))
      (.ptr (.enum kexprEnum) m89.length) := by
    rw [hm243]; exact tm_bvarLocal_nat_bounded (by simp) (by omega) (by omega)
  have ext_32_243 := ext_m105.trans (ev158.heap_extends.trans (ev195.heap_extends.trans
    (ev144.heap_extends.trans (ev101.heap_extends.trans ext_m243))))
  obtain ⟨_, hdrop_rargs, hm310⟩ :=
    kexpr_list_drop_spec' (by omega) ev320 (tmRepList_mono ext_32_243 hEas)
  rw [hm310] at ev305
  have hbnd_ml : IxVM.Consistency.Bounded cs303 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have hmap_rargs := nat_map_lift_spec (by omega : nF ≤ nP + nF) (by omega) (by omega)
    hbnd_ml hdrop_rargs ev305
  have hmap_rargs' : RepList kexprListEnum (fun h E p => Tm κ 0 Γ₀ h (nP + o + nF) E p)
      m295 ((eargs.drop nP).map (Expr.liftLooseBVars o nF)) v292 := by
    rwa [show nP + o + nF = (nP + nF) + o by omega]
  have hsnoc := SubstAux.ksnoc (R := fun h E p => Tm κ 0 Γ₀ h (nP + o + nF) E p)
    (fun _ _ _ _ ext r => Tm.mono ext r) ev291 hmap_rargs'
    ((hv88.mono ext_m243).mono ev305.heap_extends)
  have hv225 := nat_app_n_spec
    ((hbvar_mot.mono ev305.heap_extends).mono ev291.heap_extends) hsnoc ev239
  -- Step 9 & 10: lift `v225` by `recIdx.length`
  have ext_h_229 := ev44.heap_extends.trans (ext_32_243.trans
    (ev305.heap_extends.trans (ev291.heap_extends.trans ev239.heap_extends)))
  obtain ⟨hv226, hm359⟩ := field_list_length_spec ev369 (fieldRepList_mono ext_h_229 hrec)
  rw [hv226, hm359] at ev224
  have hbnd_l1 : IxVM.Consistency.Bounded cs222 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have hv211 := expr_lift_local_bounded (k := nP + o + nF) (shift := recIdx.length) (cut := 0)
    (by omega) (by omega) (by omega) hbnd_l1 hv225 (by simpa using ev224)
  -- Step 11: lift `v1` (`Eq`) by `o` at `0`
  have ext_h_212 := ext_h_229.trans ev224.heap_extends
  have hbnd_l2 : IxVM.Consistency.Bounded cs418 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have hv1_tm : Tm κ 0 Γ₀ m212 nP Eq v1 := by
    simpa [Nat.zero_add] using hRq.toTm.mono ext_h_212
  have hv392 := expr_lift_local_bounded (k := nP) (shift := o) (cut := 0)
    (by omega) (by omega) (by omega) hbnd_l2 hv1_tm (by simpa using ev420)
  -- Step 12: `nat_ih_pis`
  have ext_h_410 := ext_h_212.trans ev420.heap_extends
  have hbnd_ih : IxVM.Consistency.Bounded cs453 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have hv211' := hv211.mono ev420.heap_extends
  rw [show (nP + o + nF) + recIdx.length = nP + o + nF + 0 + recIdx.length by omega] at hv211'
  have hv393 := nat_ih_pis_spec ho hsR hsE 0
    hall
    (by omega) hbnd_ih
    (repKLevel_heapMono₂ ext_h_410 hpw)
    (hRaw.mono ext_h_410) (fieldRepList_mono ext_h_410 hrec) hv211' ev455
  -- Step 13: `nat_replace_pis`
  have ext_h_445 := ext_h_410.trans ev455.heap_extends
  have hv393' := hv393
  rw [show nP + o + nF + 0 = (nP + o) + nF by omega] at hv393'
  obtain ⟨mty, hmty, hmty_tm⟩ := nat_replace_pis_bounded nF (by omega)
    (repKLevel_heapMono₂ ext_h_445 hpw)
    (hv392.mono ev455.heap_extends) hv393' ev389
  simp only [↓reduceIte] at hmty
  refine ⟨mty, ?_, hmty_tm⟩
  unfold cMinorTy
  rw [hsEP, Option.bind_some, hsEF, Option.bind_some, getAppArgs_mkAppN_const]
  exact hmty

/-- `KernelCheck::nat_minors` at member `idx` builds `cMinorsPis` (when `isLam = false`) or
`cMinorsLams` (when `isLam = true`) from constructor index `j` (`o = j + 1`) upward, at a keying
under which the member's constructor projections resolve. -/
theorem natI_minors_spec {c : Ctx} {κ : _root_.Address → KKey}
    {T : KKey} {b₀ bT : Bytes.Address} {idx k nP nIdx : Nat} {large isLam : Bool} {ℓ : KLevel}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)}
    (hT : κ (ixAddr bT) = T)
    (hκ_inj : ∀ a : Bytes.Address, κ (ixAddr a) = T → a = bT)
    (hidx : idx < 4294967296)
    (hCres : ∀ i, i < ctors_info.length → κ (cprjAddr (ixAddr b₀) idx i) ≠ unresolvedKey)
    (hnCtors_lt : ctors_info.length < 4294967296)
    (hwf_all : ∀ info ∈ ctors_info,
      NatCtorInfoWf T k large nP nIdx ctors_info.length info) :
    ∀ (rem j : Nat) {body : KExpr}
      {x_block x_t x_lps x_pw x_body r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      j + rem = ctors_info.length →
      NatCtorLoadI κ b₀ idx k ctors_info x_block cs →
      Good c cs →
      IxVM.Consistency.Bounded cs →
      Bytes.RepAddressRef addrTy h b₀ x_block →
      Bytes.RepAddressRef addrTy h bT x_t →
      RepKLevelList h
        ((List.range k).map (fun i => Level.param ((if large then 1 else 0) + i))) x_lps →
      RepKLevel h ℓ x_pw →
      Tm κ 0 (fun _ => default) h (nP + 1 + ctors_info.length) body x_body →
      ObsFn W "KernelCheck::nat_minors"
        [x_block, .field (idx : F), x_t, x_lps, .field (nP : F), .field (nIdx : F), x_pw,
          .field (ctors_info.length : F),
          .field ((if large then 1 else 0 : Nat) : F),
          .field (j : F), x_body,
          .field ((if isLam then 1 else 0 : Nat) : F)]
        h r h' cs →
      let rlps := if large then k :: List.range k else List.range k
      let clvls := (List.range k).map (fun i => Level.param ((if large then 1 else 0) + i))
      let cs_tail := (ctors_info.drop j).map
        (fun info => (info.1, info.2.1, posOf rlps info.2.2.2.1, info.2.2.2.2))
      ∃ out,
        (if isLam then cMinorsLams clvls nP ℓ.zeronessOf cs_tail (j + 1) body
         else cMinorsPis clvls nP ℓ.zeronessOf cs_tail (j + 1) body) = some out ∧
        Tm κ 0 (fun _ => default) h' (nP + j + 1) out r
  | 0, j, body, x_block, x_t, x_lps, x_pw, x_body, r, h, h', cs, hjr, _, _, _, _, _, _, _, hbody, ev => by
    have hj_eq : j = ctors_info.length := by omega
    subst hj_eq
    match Obs.«KernelCheck::nat_minors».obs ev with
    | .n0 (he25 := hr) (he26 := hh) .. =>
      subst hr hh
      refine ⟨body, ?_, by simpa [Nat.add_assoc, Nat.add_comm 1] using hbody⟩
      cases isLam <;> simp [List.drop_length, cMinorsPis, cMinorsLams]
    | .other_n0 (op17 := op17) (hne28 := hne28) .. =>
      rw [evalBinOp_sub_nat (Nat.le_refl ctors_info.length) op17] at hne28
      simp only [Nat.sub_self, Nat.cast_zero] at hne28
      exact (hne28 rfl).elim
    | .other_other (op17 := op17) (hne28 := hne28) .. =>
      rw [evalBinOp_sub_nat (Nat.le_refl ctors_info.length) op17] at hne28
      simp only [Nat.sub_self, Nat.cast_zero] at hne28
      exact (hne28 rfl).elim
  | rem + 1, j, body, x_block, x_t, x_lps, x_pw, x_body, r, h, h', cs,
      hjr, hload, hgood, hbnd, hb₀, hbT, hlps, hpw, hbody, ev => by
    let rlps := if large then k :: List.range k else List.range k
    let clvls := (List.range k).map (fun i => Level.param ((if large then 1 else 0) + i))
    have hj_lt : j < ctors_info.length := by omega
    let info := ctors_info[j]'hj_lt
    have hinfo_get : ctors_info[j]? = some info := List.getElem?_eq_getElem hj_lt
    have hwf_j : NatCtorInfoWf T k large nP nIdx ctors_info.length info :=
      hwf_all info (List.mem_of_getElem? hinfo_get)
    have hdrop_j : ctors_info.drop j = info :: ctors_info.drop (j + 1) := by
      rw [← List.cons_getElem_drop_succ (h := hj_lt)]
    obtain ⟨rcbs₀, rus₀, rargs₀, hsR₀⟩ := hwf_j.strip_R
    obtain ⟨ecbs₀, eus₀, eargs₀, hsC₀⟩ := hwf_j.strip_C
    have hsR_pos : (posOf rlps info.2.2.1).stripPis (nP + info.2.1) =
        some (rcbs₀.map (fun b => (posOf rlps b.1,
          { b.2 with pw := Level.substPW rlps (posLevels rlps) b.2.pw })),
          Expr.mkAppN (.const T (rus₀.map (Level.subst rlps (posLevels rlps))))
            (rargs₀.map (posOf rlps))) := by
      have hs := ilp_stripPis rlps (posLevels rlps) (nP + info.2.1) hsR₀
      unfold posOf at hs ⊢
      rwa [ilp_mkAppN, Expr.instantiateLevelParams] at hs
    have hsE_pos : (posOf rlps info.2.2.2.1).stripPis (nP + info.2.1) =
        some (ecbs₀.map (fun b => (posOf rlps b.1,
          { b.2 with pw := Level.substPW rlps (posLevels rlps) b.2.pw })),
          Expr.mkAppN (.const T (eus₀.map (Level.subst rlps (posLevels rlps))))
            (eargs₀.map (posOf rlps))) := by
      have hs := ilp_stripPis rlps (posLevels rlps) (nP + info.2.1) hsC₀
      unfold posOf at hs ⊢
      rwa [ilp_mkAppN, Expr.instantiateLevelParams] at hs
    have hall_minor : ∀ i ∈ info.2.2.2.2, i < info.2.1 ∧
        RawRecSpine T
          ((rcbs₀.map (fun b => (posOf rlps b.1,
            { b.2 with pw := Level.substPW rlps (posLevels rlps) b.2.pw }))).getD
            (nP + i) default).1
          ((ecbs₀.map (fun b => (posOf rlps b.1,
            { b.2 with pw := Level.substPW rlps (posLevels rlps) b.2.pw }))).getD
            (nP + i) default).1 ∧
        nP + (j + 1) + info.2.1 + info.2.2.2.2.length +
          (Ix.Kernel.structFieldTeleOf (posOf rlps info.2.2.2.1) nP info.2.1 i).length <
            4294967296 := by
      intro i hi
      obtain ⟨hi_lt, hsp_fn⟩ := hwf_j.rec_spines i hi
      have hsp0 := hsp_fn rcbs₀ _ ecbs₀ _ hsR₀ hsC₀
      have hlenR : rcbs₀.length = nP + info.2.1 := stripPis_length (nP + info.2.1) hsR₀
      have hlenC : ecbs₀.length = nP + info.2.1 := stripPis_length (nP + info.2.1) hsC₀
      have hltR : nP + i < rcbs₀.length := by omega
      have hltC : nP + i < ecbs₀.length := by omega
      have hgetR : (rcbs₀.map (fun b => (posOf rlps b.1,
          { b.2 with pw := Level.substPW rlps (posLevels rlps) b.2.pw }))).getD (nP + i) default =
          (posOf rlps (rcbs₀[nP + i]'hltR).1,
            { (rcbs₀[nP + i]'hltR).2 with
              pw := Level.substPW rlps (posLevels rlps) (rcbs₀[nP + i]'hltR).2.pw }) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hltR]; rfl
      have hgetC : (ecbs₀.map (fun b => (posOf rlps b.1,
          { b.2 with pw := Level.substPW rlps (posLevels rlps) b.2.pw }))).getD (nP + i) default =
          (posOf rlps (ecbs₀[nP + i]'hltC).1,
            { (ecbs₀[nP + i]'hltC).2 with
              pw := Level.substPW rlps (posLevels rlps) (ecbs₀[nP + i]'hltC).2.pw }) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hltC]; rfl
      have hgetR0 : rcbs₀.getD (nP + i) default = rcbs₀[nP + i]'hltR := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hltR]; rfl
      have hgetC0 : ecbs₀.getD (nP + i) default = ecbs₀[nP + i]'hltC := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hltC]; rfl
      rw [hgetR0, hgetC0] at hsp0
      have hft_len : (Ix.Kernel.structFieldTeleOf (posOf rlps info.2.2.2.1) nP info.2.1 i).length =
          (Ix.Kernel.structFieldTeleOf info.2.2.2.1 nP info.2.1 i).length := by
        unfold posOf
        rw [ilp_structFieldTeleOf rlps (posLevels rlps) info.2.2.2.1 nP info.2.1 i
          ⟨_, _, hsC₀, hltC⟩, List.length_map]
      have htl_lt := hwf_j.tele_lt i hi
      refine ⟨hi_lt, ?_, by rw [hft_len]; omega⟩
      rw [hgetR, hgetC]
      exact rawRecSpine_ilp rlps (posLevels rlps) hsp0
    have hbase_lt : nP + (j + 1) + info.2.1 + info.2.2.2.2.length < 4294967296 := by
      have := hwf_j.minor_base_lt
      omega
    match Obs.«KernelCheck::nat_minors».obs ev with
    | .n0 (op17 := op17) .. =>
      have hsub := evalBinOp_sub_nat (by omega : j ≤ ctors_info.length) op17
      have hval := congrArg ZMod.val (Value.field.inj hsub.symm)
      have h1 : ZMod.val ((ctors_info.length - j : Nat) : F) = ctors_info.length - j :=
        ZMod.val_natCast_of_lt (Nat.lt_trans (by omega : ctors_info.length - j < 4294967296) (by decide))
      rw [h1, ZMod.val_zero] at hval
      omega
    | .other_n0 (m33 := m33) (cs43 := cs_ctor) (x_cty := x_cty) (x_nf := x_nf)
        (x_rec_idx := x_rec_idx) (v128 := v128) (m129 := m129) (cs139 := cs_mty)
        (v142 := v142) (v146 := v146) (m151 := m151) (cs159 := cs_proj)
        (v243 := v243) (m244 := m244) (cs254 := cs_rec) (v266 := v266)
        (ev45 := ev_ctor) (ev161 := ev_proj) (op220 := op220) (ev141 := ev_mty)
        (op345 := op345) (ev256 := ev_rec) (hv374 := hv_lam) (he379 := hr)
        (hm378 := hm_end) (hc407 := hc) .. =>
      subst hc hr hm_end
      have hisLam : isLam = false := by
        cases isLam with
        | false => rfl
        | true =>
          simp only [↓reduceIte] at hv_lam
          exact absurd (Value.field.inj hv_lam) one_ne_zero
      subst hisLam
      have hbnd_ctor : IxVM.Consistency.Bounded cs_ctor :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hload_ctor : NatCtorLoadI κ b₀ idx k ctors_info x_block cs_ctor :=
        hload.mono_calls (fun x hx => by simp [hx])
      obtain ⟨x_cty', x_rec_idx', htup_c, hRaw_c, hrec_c, _⟩ :=
        natI_ctor_spec hT hκ_inj hj_lt hinfo_get hwf_j hload_ctor hbnd_ctor hb₀ hbT hlps ev_ctor
      injection htup_c with hl_c
      injection hl_c with h1 hl_c; injection hl_c with h2 hl_c; injection hl_c with h3
      subst h1 h2 h3
      have hC_key : info.1 = κ (cprjAddr (ixAddr b₀) idx j) := by
        rcases Obs.«KernelCheck::nat_ctor».obs ev_ctor with ⟨m2_c, p9_c, cs15_c,
          w45_c, x_cty0_c, w46_c, w47_c, w48_c, w49_c, x_nf_c, w50_c, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _, _, ev17_c, ld11_c, _, _, _, _, _, _, _, _, _, _, hc_c⟩
        subst hc_c
        exact (hload_ctor j hj_lt p9_c h m2_c cs15_c w45_c x_cty0_c w46_c w47_c w48_c w49_c
          x_nf_c w50_c (fun x hx => by simp [hx]) hb₀ ev17_c ld11_c info hinfo_get).1
      have hb₀_33 := Bytes.repAddressRef_heapMono₂ addrTy ev_ctor.heap_extends hb₀
      have hgood_proj : Good c cs_proj :=
        hgood.sub (fun x hx => by simp [hx])
      obtain ⟨bC, hbC, hbC_addr⟩ := projection_addr_ctor_spec hidx
        (by omega : j < 4294967296) hb₀_33 hgood_proj ev_proj
      have hres_C : Resolved (κ (ixAddr bC)) := ⟨by rw [hbC_addr]; exact hCres j hj_lt⟩
      rw [evalBinOp_add_one j op220] at ev_mty
      have ext_h_151 := ev_ctor.heap_extends.trans ev_proj.heap_extends
      have hbnd_mty : IxVM.Consistency.Bounded cs_mty :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      obtain ⟨mty, hmty_eq, hmty_tm⟩ :=
        natI_minor_ty_spec (κ := κ) (Γ₀ := fun _ => default) (bC := bC) (hC_res := hres_C)
          (by rw [hbC_addr, ← hC_key])
          (by omega : 1 ≤ j + 1) hsR_pos hsE_pos
          (fun i hi => ⟨(hall_minor i hi).1, (hall_minor i hi).2.1⟩) (by omega) hbnd_mty hbC
          (RepKLevelList.mono hlps ext_h_151)
          (repKLevel_heapMono₂ ext_h_151 hpw)
          (hRaw_c.mono ev_proj.heap_extends)
          (fieldRepList_mono ev_proj.heap_extends hrec_c) ev_mty
      rw [evalBinOp_add_one j op345] at ev_rec
      have ext_h_129 := ext_h_151.trans ev_mty.heap_extends
      have hbnd_rec : IxVM.Consistency.Bounded cs_rec :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hgood_rec : Good c cs_rec :=
        hgood.sub (fun x hx => by simp [hx])
      have hload_rec : NatCtorLoadI κ b₀ idx k ctors_info x_block cs_rec :=
        hload.mono_calls (fun x hx => by simp [hx])
      obtain ⟨rest_out, hrest_eq, hrest_tm⟩ :=
        natI_minors_spec hT hκ_inj hidx hCres hnCtors_lt hwf_all rem (j + 1) (by omega)
          hload_rec hgood_rec hbnd_rec
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_129 hb₀)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_129 hbT)
          (RepKLevelList.mono hlps ext_h_129)
          (repKLevel_heapMono₂ ext_h_129 hpw)
          (hbody.mono ext_h_129) ev_rec
      simp only [Bool.false_eq_true, ↓reduceIte] at hrest_eq ⊢
      have ext_end : Heap.Extends m244
          (m244 ++ [.construct kexprEnum "Forall" [v128, v243, x_pw]]) :=
        Heap.Extends.snoc _ _
      refine ⟨.forallE mty rest_out { pw := ℓ.zeronessOf }, ?_, ?_⟩
      · rw [hdrop_j, List.map_cons, cMinorsPis, hmty_eq]
        dsimp only [Option.bind]
        rw [hrest_eq, Option.map_some]
      · have hmty_end : Tm κ 0 (fun _ => default)
            (m244 ++ [.construct kexprEnum "Forall" [v128, v243, x_pw]])
            (nP + j + 1) mty v128 := by
          rw [show nP + j + 1 = nP + (j + 1) by omega]
          exact (hmty_tm.mono ev_rec.heap_extends).mono ext_end
        have hrest_end : Tm κ 0 (fun _ => default)
            (m244 ++ [.construct kexprEnum "Forall" [v128, v243, x_pw]])
            ((nP + j + 1) + 1) rest_out v243 := by
          rw [show (nP + j + 1) + 1 = nP + (j + 1) + 1 by omega]
          exact hrest_tm.mono ext_end
        exact .forallE (by simp) hmty_end hrest_end
          (repKLevel_heapMono₂ (ext_h_129.trans (ev_rec.heap_extends.trans ext_end)) hpw)
    | .other_other (m33 := m33) (cs43 := cs_ctor) (x_cty := x_cty) (x_nf := x_nf)
        (x_rec_idx := x_rec_idx) (v128 := v128) (m129 := m129) (cs139 := cs_mty)
        (v142 := v142) (v146 := v146) (m151 := m151) (cs159 := cs_proj)
        (v243 := v243) (m244 := m244) (cs254 := cs_rec) (v266 := v266)
        (ev45 := ev_ctor) (ev161 := ev_proj) (op220 := op220) (ev141 := ev_mty)
        (op345 := op345) (ev256 := ev_rec) (hne408 := hne_lam) (he416 := hr)
        (hm415 := hm_end) (hc444 := hc) .. =>
      subst hc hr hm_end
      have hisLam : isLam = true := by
        cases isLam with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hne_lam
          exact absurd rfl hne_lam
        | true => rfl
      subst hisLam
      have hbnd_ctor : IxVM.Consistency.Bounded cs_ctor :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hload_ctor : NatCtorLoadI κ b₀ idx k ctors_info x_block cs_ctor :=
        hload.mono_calls (fun x hx => by simp [hx])
      obtain ⟨x_cty', x_rec_idx', htup_c, hRaw_c, hrec_c, _⟩ :=
        natI_ctor_spec hT hκ_inj hj_lt hinfo_get hwf_j hload_ctor hbnd_ctor hb₀ hbT hlps ev_ctor
      injection htup_c with hl_c
      injection hl_c with h1 hl_c; injection hl_c with h2 hl_c; injection hl_c with h3
      subst h1 h2 h3
      have hC_key : info.1 = κ (cprjAddr (ixAddr b₀) idx j) := by
        rcases Obs.«KernelCheck::nat_ctor».obs ev_ctor with ⟨m2_c, p9_c, cs15_c,
          w45_c, x_cty0_c, w46_c, w47_c, w48_c, w49_c, x_nf_c, w50_c, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _, _, ev17_c, ld11_c, _, _, _, _, _, _, _, _, _, _, hc_c⟩
        subst hc_c
        exact (hload_ctor j hj_lt p9_c h m2_c cs15_c w45_c x_cty0_c w46_c w47_c w48_c w49_c
          x_nf_c w50_c (fun x hx => by simp [hx]) hb₀ ev17_c ld11_c info hinfo_get).1
      have hb₀_33 := Bytes.repAddressRef_heapMono₂ addrTy ev_ctor.heap_extends hb₀
      have hgood_proj : Good c cs_proj :=
        hgood.sub (fun x hx => by simp [hx])
      obtain ⟨bC, hbC, hbC_addr⟩ := projection_addr_ctor_spec hidx
        (by omega : j < 4294967296) hb₀_33 hgood_proj ev_proj
      have hres_C : Resolved (κ (ixAddr bC)) := ⟨by rw [hbC_addr]; exact hCres j hj_lt⟩
      rw [evalBinOp_add_one j op220] at ev_mty
      have ext_h_151 := ev_ctor.heap_extends.trans ev_proj.heap_extends
      have hbnd_mty : IxVM.Consistency.Bounded cs_mty :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      obtain ⟨mty, hmty_eq, hmty_tm⟩ :=
        natI_minor_ty_spec (κ := κ) (Γ₀ := fun _ => default) (bC := bC) (hC_res := hres_C)
          (by rw [hbC_addr, ← hC_key])
          (by omega : 1 ≤ j + 1) hsR_pos hsE_pos
          (fun i hi => ⟨(hall_minor i hi).1, (hall_minor i hi).2.1⟩) (by omega) hbnd_mty hbC
          (RepKLevelList.mono hlps ext_h_151)
          (repKLevel_heapMono₂ ext_h_151 hpw)
          (hRaw_c.mono ev_proj.heap_extends)
          (fieldRepList_mono ev_proj.heap_extends hrec_c) ev_mty
      rw [evalBinOp_add_one j op345] at ev_rec
      have ext_h_129 := ext_h_151.trans ev_mty.heap_extends
      have hbnd_rec : IxVM.Consistency.Bounded cs_rec :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hgood_rec : Good c cs_rec :=
        hgood.sub (fun x hx => by simp [hx])
      have hload_rec : NatCtorLoadI κ b₀ idx k ctors_info x_block cs_rec :=
        hload.mono_calls (fun x hx => by simp [hx])
      obtain ⟨rest_out, hrest_eq, hrest_tm⟩ :=
        natI_minors_spec hT hκ_inj hidx hCres hnCtors_lt hwf_all rem (j + 1) (by omega)
          hload_rec hgood_rec hbnd_rec
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_129 hb₀)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_129 hbT)
          (RepKLevelList.mono hlps ext_h_129)
          (repKLevel_heapMono₂ ext_h_129 hpw)
          (hbody.mono ext_h_129) ev_rec
      simp only [↓reduceIte] at hrest_eq ⊢
      have ext_end : Heap.Extends m244
          (m244 ++ [.construct kexprEnum "Lam" [v128, v243, x_pw]]) :=
        Heap.Extends.snoc _ _
      refine ⟨.lam mty rest_out { pw := ℓ.zeronessOf }, ?_, ?_⟩
      · rw [hdrop_j, List.map_cons, cMinorsLams, hmty_eq]
        dsimp only [Option.bind]
        rw [hrest_eq, Option.map_some]
      · have hmty_end : Tm κ 0 (fun _ => default)
            (m244 ++ [.construct kexprEnum "Lam" [v128, v243, x_pw]])
            (nP + j + 1) mty v128 := by
          rw [show nP + j + 1 = nP + (j + 1) by omega]
          exact (hmty_tm.mono ev_rec.heap_extends).mono ext_end
        have hrest_end : Tm κ 0 (fun _ => default)
            (m244 ++ [.construct kexprEnum "Lam" [v128, v243, x_pw]])
            ((nP + j + 1) + 1) rest_out v243 := by
          rw [show (nP + j + 1) + 1 = nP + (j + 1) + 1 by omega]
          exact hrest_tm.mono ext_end
        exact .lam (by simp) hmty_end hrest_end
          (repKLevel_heapMono₂ (ext_h_129.trans (ev_rec.heap_extends.trans ext_end)) hpw)

/-- `KernelCheck::nat_ih_apps` builds the induction-hypothesis applications of the recursor
`recC`, at a keying under which the recursor's key resolves. -/
theorem natI_ih_apps_spec {κ : _root_.Address → KKey} {Γ₀ : Nat → KExpr}
    {T recC : KKey} {bRec : Bytes.Address} [hRec_res : Resolved (κ (ixAddr bRec))]
    {rlvls_c : List KLevel}
    {nP n nF : Nat} {ℓ : KLevel} {Rcty Ecty rbody ebody : KExpr}
    {rcbs ecbs : List (KExpr × Ix.Kernel.BinderMeta)}
    (hRec : κ (ixAddr bRec) = recC)
    (hsR : Rcty.stripPis (nP + nF) = some (rcbs, rbody))
    (hsE : Ecty.stripPis (nP + nF) = some (ecbs, ebody)) :
    ∀ {is : List Nat}
      {x_rec x_rlvls x_pw x_rec_idx x_cty r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      (∀ i ∈ is, i < nF ∧
        RawRecSpine T (rcbs.getD (nP + i) default).1 (ecbs.getD (nP + i) default).1) →
      nP + 1 + n + nF < 2305843009213693952 →
      IxVM.Consistency.Bounded cs →
      Bytes.RepAddressRef addrTy h bRec x_rec →
      RepKLevelList h rlvls_c x_rlvls →
      RepKLevel h ℓ x_pw →
      RepList fieldListEnum (fun _ (i : Nat) v => v = .field (i : F)) h is x_rec_idx →
      RawTm κ 0 Γ₀ h 0 Rcty Ecty x_cty →
      ObsFn W "KernelCheck::nat_ih_apps"
        [x_rec, x_rlvls, x_pw, .field (nP : F), .field (n : F), .field (nF : F),
          x_rec_idx, x_cty] h r h' cs →
      RepList kexprListEnum (fun h E p => Tm κ 0 Γ₀ h (nP + 1 + n + nF) E p) h'
        (is.map (fun i => Ix.Kernel.structIhApp recC rlvls_c ℓ.zeronessOf nP n nF i
          (Ix.Kernel.structFieldTeleOf Ecty nP nF i)
          (Ix.Kernel.structFieldIdxOf Ecty nP nF i))) r := by
  intro is
  induction is with
  | nil =>
    intro x_rec x_rlvls x_pw x_rec_idx x_cty r h h' cs _ _ _ _ _ _ his _ ev
    match Obs.«KernelCheck::nat_ih_apps».obs ev with
    | .Nil (he24 := hr) (hm23 := hm) .. =>
      subst hr hm
      exact .nil (by simp)
    | .Cons (ld12 := ld) .. =>
      have ld' : loadValue h x_rec_idx = .ok (.construct fieldListEnum "Cons" [_, _]) := ld
      cases his with | nil cell => exact (load_cell_ne cell ld' (by decide)).elim
  | cons i rest ih =>
    intro x_rec x_rlvls x_pw x_rec_idx x_cty r h h' cs hall hlt_base hbnd hbR hrlvls hpw his hRaw ev
    match Obs.«KernelCheck::nat_ih_apps».obs ev with
    | .Nil (ld12 := ld) .. =>
      have ld' : loadValue h x_rec_idx = .ok (.construct fieldListEnum "Nil" []) := ld
      cases his with | cons cell _ _ => exact (load_cell_ne cell ld' (by decide)).elim
    | .Cons (m47 := m47) (x_tele := x_tele) (x_idx := x_idx) (v97 := v97) (m98 := m98)
        (v119 := v119) (m120 := m120) (v133 := v133) (v134 := v134) (m136 := m136)
        (v147 := v147) (m150 := m150) (v161 := v161) (x169 := x169) (x177 := x177)
        (m204 := m204) (v216 := v216) (x223 := x223) (m243 := m243) (v254 := v254)
        (v279 := v279) (m280 := m280) (v294 := v294) (m296 := m296) (v308 := v308)
        (x315 := x315) (x323 := x323) (m343 := m343) (v369 := v369) (m370 := m370)
        (v383 := v383) (m386 := m386) (v398 := v398) (m407 := m407) (cs415 := cs_map)
        (v419 := v419) (v480 := v480) (m481 := m481) (v494 := v494) (v495 := v495)
        (m498 := m498) (cs506 := cs_ta) (v510 := v510) (m572 := m572) (m586 := m586)
        (v636 := v636) (m645 := m645) (cs653 := cs_rec)
        (ld12 := ld) (ev59 := ev_ft) (ev110 := ev_len)
        (op192 := op192) (op184 := op184) (op176 := op176) (ev160 := ev_psP)
        (hm212 := hm204) (op238 := op238) (op230 := op230) (ev146 := ev_snoc1)
        (op269 := op269) (ev253 := ev_psN) (ev132 := ev_cat1)
        (hm304 := hm296) (op338 := op338) (op330 := op330) (op322 := op322)
        (ev353 := ev_psM) (ev292 := ev_app_fi)
        (op444 := op444) (ev417 := ev_map) (ev396 := ev_cat2) (ev382 := ev_snoc2)
        (op536 := op536) (ev508 := ev_ta) (hm594 := hm586) (ev582 := ev_app_rec)
        (ev493 := ev_mk) (he631 := hr) (hm630 := hm_end) (ev655 := ev_rec) (hc720 := hc) .. =>
      subst hc hr hm_end
      obtain ⟨i', rest', heq, hi_eq, hrest_rep⟩ := RepList.cons_of_load his ld
      injection heq with h1 h2; subst h1 h2; subst hi_eq
      obtain ⟨hi_lt, hspine_i⟩ := hall i List.mem_cons_self
      let tele_i := Ix.Kernel.structFieldTeleOf Ecty nP nF i
      let idx_i := Ix.Kernel.structFieldIdxOf Ecty nP nF i
      let m := tele_i.length
      obtain ⟨ptele, pidx, htup_ft, htele_m47, hidx_m47⟩ :=
        nat_field_tele_spec hi_lt (by omega) hRaw hsR hsE hspine_i ev_ft
      injection htup_ft with hl_ft; injection hl_ft with h1 hl_ft; injection hl_ft with h2
      subst h1 h2
      -- the telescope is a list the run passes to `Lists::length`: fewer than `2^39` binders
      have hm_lt : m < 549755813888 :=
        teleRep_length_lt_of_call hbnd ev_len (by simp) htele_m47
      have hlt_m' : nP + 1 + n + nF + m < 4611686018427387904 := by omega
      obtain ⟨hv97, hm98⟩ := tele_length_spec ev_len htele_m47
      rw [hm98] at ev_psP
      have hv97' : v97 = .field (m : F) := hv97
      rw [hv97'] at op192 op238 op269 op322 ev_psM ev_map
      -- `structRecPrefixAt nP n nF m`
      rw [evalBinOp_add_nat m nF op192] at op184
      rw [evalBinOp_add_nat (m + nF) n op184] at op176
      rw [evalBinOp_add_one (m + nF + n) op176] at ev_psP
      have hpsP := nat_ps_at_bounded (κ := κ) (d := 0) (Γ := Γ₀)
        nP (m + nF + n + 1) (nP + 1 + n + nF + m) (by omega) (by omega) ev_psP
      rw [evalBinOp_add_nat m nF op238] at op230
      rw [evalBinOp_add_nat (m + nF) n op230] at hm204
      have ext_m204 : Heap.Extends m150 m204 := by rw [hm204]; exact Heap.Extends.snoc _ _
      have hbvar_mot : Tm κ 0 Γ₀ m204 (nP + 1 + n + nF + m)
          (.bvar (m + nF + n)) (.ptr (.enum kexprEnum) m150.length) := by
        rw [hm204]; exact tm_bvarLocal_nat_bounded (by simp) (by omega) (by omega)
      have hsnoc1 := SubstAux.ksnoc (R := fun h E p => Tm κ 0 Γ₀ h (nP + 1 + n + nF + m) E p)
        (fun _ _ _ _ ext r => Tm.mono ext r) ev_snoc1 (tmRepList_mono ext_m204 hpsP) hbvar_mot
      rw [evalBinOp_add_nat m nF op269] at ev_psN
      have hpsN := nat_ps_at_bounded (κ := κ) (d := 0) (Γ := Γ₀)
        n (m + nF) (nP + 1 + n + nF + m) (by omega) (by omega) ev_psN
      have hpref := kexpr_list_concat_spec' ev_cat1
        (tmRepList_mono ev_psN.heap_extends hsnoc1) hpsN
      have hpref_eq :
          Ix.Kernel.structPsAt (m + nF + n + 1) nP ++ [.bvar (m + nF + n)] ++
            Ix.Kernel.structPsAt (m + nF) n =
          Ix.Kernel.structRecPrefixAt (md := .anon) nP n nF m := by
        rfl
      rw [hpref_eq] at hpref
      -- `f_i a⃗`
      rw [evalBinOp_sub_nat (by omega : 1 ≤ nF) op338] at op330
      rw [evalBinOp_sub_nat (by omega : i ≤ nF - 1) op330] at op322
      rw [evalBinOp_add_nat (nF - 1 - i) m op322] at hm296
      have ext_m296 : Heap.Extends m120 m296 := by rw [hm296]; exact Heap.Extends.snoc _ _
      have hbvar_fi : Tm κ 0 Γ₀ m296 (nP + 1 + n + nF + m)
          (.bvar (nF - 1 - i + m)) (.ptr (.enum kexprEnum) m120.length) := by
        rw [hm296]; exact tm_bvarLocal_nat_bounded (by simp) (by omega) (by omega)
      have hpsM := nat_ps_at_bounded (κ := κ) (d := 0) (Γ := Γ₀)
        m 0 (nP + 1 + n + nF + m) (by omega) (by omega) ev_psM
      rw [structPsAt_zero_eq_structTeleVars] at hpsM
      have hfi_app := nat_app_n_spec (hbvar_fi.mono ev_psM.heap_extends) hpsM ev_app_fi
      -- `idx_i.map (structIdxAt nF (n + 1) i 0 m)` and full spine
      rw [evalBinOp_add_one n op444] at ev_map
      have ext_47_280 := ev_psP.heap_extends.trans (ext_m204.trans (ev_snoc1.heap_extends.trans
        (ev_psN.heap_extends.trans (ev_cat1.heap_extends.trans (ext_m296.trans
          (ev_psM.heap_extends.trans ev_app_fi.heap_extends))))))
      have hidx_280 : RepList kexprListEnum (fun h E p => Tm κ 0 Γ₀ h (nP + i + m) E p)
          m280 idx_i x_idx := by
        simpa [Nat.zero_add] using tmRepList_mono ext_47_280 hidx_m47
      have hbnd_map : IxVM.Consistency.Bounded cs_map :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hmap_idx := nat_map_idx_at_spec (k_base := nP) (o := n + 1) (l := 0) (m := m)
        (by omega : i ≤ nF) (by omega) hbnd_map hidx_280 ev_map
      have hmap_idx' : RepList kexprListEnum
          (fun h E p => Tm κ 0 Γ₀ h (nP + 1 + n + nF + m) E p)
          m407 (idx_i.map (Ix.Kernel.structIdxAt nF (n + 1) i 0 m)) v398 := by
        rw [show nP + (n + 1) + nF + 0 + m = nP + 1 + n + nF + m by omega] at hmap_idx
        exact hmap_idx
      have ext_120_407 := ext_m296.trans (ev_psM.heap_extends.trans
        (ev_app_fi.heap_extends.trans ev_map.heap_extends))
      have hcat2 := kexpr_list_concat_spec' ev_cat2 (tmRepList_mono ext_120_407 hpref) hmap_idx'
      have hsnoc2 := SubstAux.ksnoc (R := fun h E p => Tm κ 0 Γ₀ h (nP + 1 + n + nF + m) E p)
        (fun _ _ _ _ ext r => Tm.mono ext r) ev_snoc2 hcat2
        ((hfi_app.mono ev_map.heap_extends).mono ev_cat2.heap_extends)
      -- `nat_tele_at`, `Const`, `nat_app_n`, `nat_mk_binders`
      rw [evalBinOp_add_one n op536] at ev_ta
      have ext_47_370 := ext_47_280.trans
        (ev_map.heap_extends.trans (ev_cat2.heap_extends.trans ev_snoc2.heap_extends))
      have ext_h_370 := ev_ft.heap_extends.trans ext_47_370
      have hbnd_ta : IxVM.Consistency.Bounded cs_ta :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have htele_370 := htele_m47.mono ext_47_370
      rw [Nat.zero_add] at htele_370
      have hta := nat_tele_at_bounded (k_base := nP) (o := n + 1) (l := 0)
        (by omega : i ≤ nF) (by omega) hbnd_ta
        (repKLevel_heapMono₂ ext_h_370 hpw) htele_370 ev_ta
      have hta' : TeleRep κ 0 Γ₀ m498 (nP + 1 + n + nF)
          (Ix.Kernel.structTeleAt nF (n + 1) i 0 ℓ.zeronessOf tele_i) v494 := by
        rw [show nP + (n + 1) + nF + 0 = nP + 1 + n + nF by omega] at hta
        exact hta
      have ext_m586 : Heap.Extends m498 m586 := by rw [hm586]; exact Heap.Extends.snoc _ _
      have ext_h_498 := ext_h_370.trans ev_ta.heap_extends
      have ext_h_586 := ext_h_498.trans ext_m586
      have hconst_rec : Tm κ 0 Γ₀ m586 (nP + 1 + n + nF + m)
          (.const recC rlvls_c) (.ptr (.enum kexprEnum) m498.length) := by
        rw [← hRec]
        exact .const (by rw [hm586]; simp)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_586 hbR)
          (RepKLevelList.mono hrlvls ext_h_586)
          (LvEqList.refl _)
      have happ_rec := nat_app_n_spec hconst_rec
        (tmRepList_mono (ev_ta.heap_extends.trans ext_m586) hsnoc2) ev_app_rec
      have hta_len : (Ix.Kernel.structTeleAt nF (n + 1) i 0 ℓ.zeronessOf tele_i).length = m := by
        simp [Ix.Kernel.structTeleAt, m]
      have happ_rec' : Tm κ 0 Γ₀ m572
          ((nP + 1 + n + nF) + (Ix.Kernel.structTeleAt nF (n + 1) i 0 ℓ.zeronessOf tele_i).length)
          (Expr.mkAppN (.const recC rlvls_c)
            (Ix.Kernel.structRecPrefixAt nP n nF m ++
              idx_i.map (Ix.Kernel.structIdxAt nF (n + 1) i 0 m) ++
              [Expr.mkAppN (.bvar (nF - 1 - i + m)) (Ix.Kernel.structTeleVars m)])) v495 := by
        rw [hta_len]
        simpa [List.append_assoc] using happ_rec
      have hih_app := nat_mk_binders_spec
        (hta'.mono (ext_m586.trans ev_app_rec.heap_extends)) happ_rec' ev_mk
      have h1_ne_0 : (.field 1 : SourceValue F) ≠ .field 0 := by
        intro h01; exact absurd (Value.field.inj h01) one_ne_zero
      rw [ite_eq_right h1_ne_0] at hih_app
      -- Recursive call on `rest`
      have ext_h_481 := ext_h_586.trans (ev_app_rec.heap_extends.trans ev_mk.heap_extends)
      have hbnd_rec : IxVM.Consistency.Bounded cs_rec :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hall_rest : ∀ k ∈ rest, k < nF ∧
          RawRecSpine T (rcbs.getD (nP + k) default).1 (ecbs.getD (nP + k) default).1 :=
        fun k hk => hall k (List.mem_cons_of_mem _ hk)
      have hrest_ih := ih hall_rest hlt_base hbnd_rec
        (Bytes.repAddressRef_heapMono₂ addrTy ext_h_481 hbR)
        (RepKLevelList.mono hrlvls ext_h_481)
        (repKLevel_heapMono₂ ext_h_481 hpw)
        (fieldRepList_mono ext_h_481 hrest_rep)
        (hRaw.mono ext_h_481) ev_rec
      have ext_end : Heap.Extends m645
          (m645 ++ [.construct kexprListEnum "Cons" [v480, v636]]) := Heap.Extends.snoc _ _
      exact .cons (by simp)
        ((hih_app.mono ev_rec.heap_extends).mono ext_end)
        (tmRepList_mono ext_end hrest_ih)

/-- The binder shape of the minor premises `KernelCheck::nat_minors` builds at member `idx` over a
body with a `ForallDomHeadLvls` witness: the witness persists below the added binders. -/
theorem natI_forallDomHeadLvls_minors
    {κ : _root_.Address → KKey} {T : KKey} {bT : Bytes.Address} {idx nP nIdx m : Nat}
    {large : Bool} {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)}
    {ls : List KLevel}
    (hnCtors_lt : ctors_info.length < 18446744069414584321) :
    ∀ (rem j : Nat) {x_block x_t x_lps x_pw x_body r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      j + rem = ctors_info.length →
      ForallDomHeadLvls κ 0 (fun _ => default) h
        T bT ls m (nP + 1 + ctors_info.length) x_body →
      ObsFn W "KernelCheck::nat_minors"
        [x_block, .field (idx : F), x_t, x_lps, .field (nP : F), .field (nIdx : F), x_pw,
          .field (ctors_info.length : F),
          .field ((if large then 1 else 0 : Nat) : F),
          .field (j : F), x_body, .field 0]
        h r h' cs →
      ForallDomHeadLvls κ 0 (fun _ => default) h' T bT ls (rem + m) (nP + j + 1) r
  | 0, j, _, _, _, _, _, _, _, _, _, hjr, hbody, ev => by
    have hj_eq : j = ctors_info.length := by omega
    subst hj_eq
    match Obs.«KernelCheck::nat_minors».obs ev with
    | .n0 (he25 := hr) (he26 := hh) .. =>
      subst hr hh
      simpa [Nat.add_assoc, Nat.add_comm 1] using hbody
    | .other_n0 (op17 := op17) (hne28 := hne28) .. =>
      rw [evalBinOp_sub_nat (Nat.le_refl ctors_info.length) op17] at hne28
      simp only [Nat.sub_self, Nat.cast_zero] at hne28
      exact (hne28 rfl).elim
    | .other_other (op17 := op17) (hne28 := hne28) .. =>
      rw [evalBinOp_sub_nat (Nat.le_refl ctors_info.length) op17] at hne28
      simp only [Nat.sub_self, Nat.cast_zero] at hne28
      exact (hne28 rfl).elim
  | rem + 1, j, _, _, _, x_pw, _, _, _, _, _, hjr, hbody, ev => by
    match Obs.«KernelCheck::nat_minors».obs ev with
    | .n0 (op17 := op17) .. =>
      have hsub := evalBinOp_sub_nat (by omega : j ≤ ctors_info.length) op17
      have hval := congrArg ZMod.val (Value.field.inj hsub.symm)
      have h1 : ZMod.val ((ctors_info.length - j : Nat) : F) = ctors_info.length - j :=
        ZMod.val_natCast_of_lt (by omega : ctors_info.length - j < 18446744069414584321)
      rw [h1, ZMod.val_zero] at hval
      omega
    | .other_other (hne408 := hne_lam) .. =>
      exact absurd rfl hne_lam
    | .other_n0 (v128 := v128) (v243 := v243) (m244 := m244)
        (ev45 := ev_ctor) (ev161 := ev_proj) (ev141 := ev_mty)
        (op345 := op345) (ev256 := ev_rec) (he379 := hr) (hm378 := hm_end) .. =>
      subst hr hm_end
      rw [evalBinOp_add_one j op345] at ev_rec
      have ext_h_129 := ev_ctor.heap_extends.trans
        (ev_proj.heap_extends.trans ev_mty.heap_extends)
      have ih_out := natI_forallDomHeadLvls_minors hnCtors_lt rem (j + 1) (by omega)
        (hbody.mono ext_h_129) ev_rec
      have ih_out' :
          ForallDomHeadLvls κ 0 (fun _ => default) m244
            T bT ls (rem + m) ((nP + j + 1) + 1) v243 := by
        rwa [show (nP + j + 1) + 1 = nP + (j + 1) + 1 by omega]
      have hsucc :
          ForallDomHeadLvls κ 0 (fun _ => default)
            (m244 ++ [.construct kexprEnum "Forall" [v128, v243, x_pw]])
            T bT ls ((rem + m) + 1) (nP + j + 1) (.ptr (.enum kexprEnum) m244.length) :=
        .succ (by simp; exact ⟨rfl, rfl⟩) (ih_out'.mono (Heap.Extends.snoc _ _))
      rwa [show (rem + 1) + m = (rem + m) + 1 by omega]

/-- `KernelCheck::nat_rule_rhs` at member `idx` builds the circuit-frame generated rule right-hand
side `cRuleRhs` for constructor `j`, at a keying under which the recursor's key and the member's
constructor projections resolve. -/
theorem natI_rule_rhs_spec {c : Ctx} {κ : _root_.Address → KKey}
    {T recC : KKey} {b₀ bT bRec : Bytes.Address} {idx k nP nIdx j : Nat} {large : Bool}
    {ℓ : KLevel} {rlvls_c : List KLevel} {tty₀ motiveTy : KExpr}
    {tbsP : List (KExpr × Ix.Kernel.BinderMeta)} {itele_pos : KExpr}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)}
    {x_block x_t x_lps x_pw x_tty x_motive_ty x_rec x_rlvls r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    [Resolved (κ (ixAddr bRec))]
    (hT : κ (ixAddr bT) = T)
    (hκ_inj : ∀ a : Bytes.Address, κ (ixAddr a) = T → a = bT)
    (hRec : κ (ixAddr bRec) = recC)
    (hidx : idx < 4294967296)
    (hCres : ∀ i, i < ctors_info.length → κ (cprjAddr (ixAddr b₀) idx i) ≠ unresolvedKey)
    (hnCtors_lt : ctors_info.length < 2147483648)
    (hnP_lt : nP < 2147483648)
    (hj : j < ctors_info.length)
    (hwf_all : ∀ info ∈ ctors_info,
      NatCtorInfoWf T k large nP nIdx ctors_info.length info)
    (hsT_pos : (posOf (if large then k :: List.range k else List.range k) tty₀).stripPis nP =
      some (tbsP, itele_pos))
    (hmot_eq : cMotiveTyI T
      ((List.range k).map (fun i => Level.param ((if large then 1 else 0) + i)))
      ℓ nP nIdx itele_pos = some motiveTy)
    (hload : NatCtorLoadI κ b₀ idx k ctors_info x_block cs)
    (hgood : Good c cs)
    (hbnd : IxVM.Consistency.Bounded cs)
    (hb₀ : Bytes.RepAddressRef addrTy h b₀ x_block)
    (hbT : Bytes.RepAddressRef addrTy h bT x_t)
    (hbRec : Bytes.RepAddressRef addrTy h bRec x_rec)
    (hlps : RepKLevelList h
      ((List.range k).map (fun i => Level.param ((if large then 1 else 0) + i))) x_lps)
    (hrlvls : RepKLevelList h rlvls_c x_rlvls)
    (hpw : RepKLevel h ℓ x_pw)
    (htty : Tm κ 0 (fun _ => default) h 0
      (posOf (if large then k :: List.range k else List.range k) tty₀) x_tty)
    (hmotive : Tm κ 0 (fun _ => default) h nP motiveTy x_motive_ty)
    (ev : ObsFn W "KernelCheck::nat_rule_rhs"
      [x_block, .field (idx : F), x_t, x_lps, .field (nP : F), .field (nIdx : F), x_pw,
        .field (ctors_info.length : F),
        .field ((if large then 1 else 0 : Nat) : F),
        x_tty, x_motive_ty, x_rec, x_rlvls, .field (j : F)]
      h r h' cs) :
    let rlps := if large then k :: List.range k else List.range k
    let clvls := (List.range k).map (fun i => Level.param ((if large then 1 else 0) + i))
    let cs_pos := ctors_info.map (fun info => (info.1, info.2.1, posOf rlps info.2.2.2.1, info.2.2.2.2))
    ∃ rhs_c,
      cRuleRhs T clvls ℓ nP nIdx (posOf rlps tty₀) cs_pos recC rlvls_c j = some rhs_c ∧
      Tm κ 0 (fun _ => default) h' 0 rhs_c r := by
  intro rlps clvls cs_pos
  dsimp only [rlps, clvls, cs_pos]
  let n := ctors_info.length
  let info := ctors_info[j]'hj
  have hinfo_get : ctors_info[j]? = some info := List.getElem?_eq_getElem hj
  have hwf_j : NatCtorInfoWf T k large nP nIdx n info :=
    hwf_all info (List.mem_of_getElem? hinfo_get)
  let nF := info.2.1
  let R₀ := info.2.2.1
  let C₀ := info.2.2.2.1
  let recIdx := info.2.2.2.2
  have hnPF_lt : nP + nF < 2147483648 := hwf_j.nf_lt
  have hbase_lt : nP + 1 + n + nF < 4294967296 := by
    have := hwf_j.minor_base_lt
    omega
  rcases Obs.«KernelCheck::nat_rule_rhs».obs ev with
    ⟨m2, cs12, x_cty, x_nf, x_rec_idx, v97, m98, cs108, v112, m114, v126, x133, x141,
      m161, cs169, v172, v173, m175, cs183, m202, cs210, v277, m278, cs288, v293, m311,
      cs319, v322, v323, m326, cs334, v387, m388, cs398, cs498, m528,
      ev14, hm122, op156, op148, op140, ev185, ev212, ev171, ev110, ev336, op366, ev321,
      ev290, ev400, hm536, ev500, hc⟩
  subst hc
  -- Step 1: `nat_ctor`
  have hbnd_ctor : IxVM.Consistency.Bounded cs12 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have hload_ctor : NatCtorLoadI κ b₀ idx k ctors_info x_block cs12 :=
    hload.mono_calls (fun x hx => by simp [hx])
  obtain ⟨x_cty', x_rec_idx', htup_c, hRaw_c, hrec_c, _⟩ :=
    natI_ctor_spec hT hκ_inj hj hinfo_get hwf_j hload_ctor hbnd_ctor hb₀ hbT hlps ev14
  injection htup_c with hl_c
  injection hl_c with h1 hl_c; injection hl_c with h2 hl_c; injection hl_c with h3
  subst h1 h2 h3
  -- Step 2: `structRuleBodyR` via `BVar`, `nat_ps_at`, `nat_ih_apps`, `concat`, `nat_app_n`
  rw [evalBinOp_add_nat nF n op156] at op148
  rw [evalBinOp_sub_nat (by omega : 1 ≤ nF + n) op148] at op140
  rw [evalBinOp_sub_nat (by omega : j ≤ nF + n - 1) op140] at hm122
  have ext_2_114 : Heap.Extends m2 m114 := by rw [hm122]; exact Heap.Extends.snoc _ _
  have hbvar_min : Tm κ 0 (fun _ => default) m114 (nP + 1 + n + nF)
      (.bvar (nF + n - 1 - j)) (.ptr (.enum kexprEnum) m2.length) := by
    rw [hm122]
    exact tm_bvarLocal_nat (by simp) (by omega) (by omega)
  have hps_f := nat_ps_at_spec (κ := κ) (d := 0) (Γ := fun _ => default)
    nF 0 (nP + 1 + n + nF) (by omega) hbase_lt ev185
  have hps_f' : RepList kexprListEnum
      (fun h E p => Tm κ 0 (fun _ => default) h (nP + 1 + n + nF) E p)
      m175 ((List.range nF).map fun i => Expr.bvar (nF - 1 - i)) v172 := by
    rw [structPsAt_zero_eq_structTeleVars] at hps_f
    exact hps_f
  let rlps' := if large then k :: List.range k else List.range k
  obtain ⟨rcbs₀, rus₀, rargs₀, hsR₀⟩ := hwf_j.strip_R
  obtain ⟨ecbs₀, eus₀, eargs₀, hsC₀⟩ := hwf_j.strip_C
  have hsR_pos := ilp_stripPis rlps' (posLevels rlps') (nP + nF) hsR₀
  change (posOf rlps' R₀).stripPis (nP + nF) = _ at hsR_pos
  have hsE_pos := ilp_stripPis rlps' (posLevels rlps') (nP + nF) hsC₀
  change (posOf rlps' C₀).stripPis (nP + nF) = _ at hsE_pos
  have hall_ih : ∀ i ∈ recIdx, i < nF ∧
      RawRecSpine T
        ((rcbs₀.map (fun b => (posOf rlps' b.1,
          { b.2 with pw := Level.substPW rlps' (posLevels rlps') b.2.pw }))).getD
          (nP + i) default).1
        ((ecbs₀.map (fun b => (posOf rlps' b.1,
          { b.2 with pw := Level.substPW rlps' (posLevels rlps') b.2.pw }))).getD
          (nP + i) default).1 ∧
      nP + 1 + n + nF +
        (Ix.Kernel.structFieldTeleOf (posOf rlps' C₀) nP nF i).length < 4294967296 := by
    intro i hi
    obtain ⟨hi_lt, hsp_fn⟩ := hwf_j.rec_spines i hi
    have hsp0 := hsp_fn rcbs₀ _ ecbs₀ _ hsR₀ hsC₀
    have hlenR : rcbs₀.length = nP + nF := stripPis_length (nP + nF) hsR₀
    have hlenC : ecbs₀.length = nP + nF := stripPis_length (nP + nF) hsC₀
    have hltR : nP + i < rcbs₀.length := by omega
    have hltC : nP + i < ecbs₀.length := by omega
    have hgetR : (rcbs₀.map (fun b => (posOf rlps' b.1,
        { b.2 with pw := Level.substPW rlps' (posLevels rlps') b.2.pw }))).getD (nP + i) default =
        (posOf rlps' (rcbs₀[nP + i]'hltR).1,
          { (rcbs₀[nP + i]'hltR).2 with
            pw := Level.substPW rlps' (posLevels rlps') (rcbs₀[nP + i]'hltR).2.pw }) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hltR]; rfl
    have hgetC : (ecbs₀.map (fun b => (posOf rlps' b.1,
        { b.2 with pw := Level.substPW rlps' (posLevels rlps') b.2.pw }))).getD (nP + i) default =
        (posOf rlps' (ecbs₀[nP + i]'hltC).1,
          { (ecbs₀[nP + i]'hltC).2 with
            pw := Level.substPW rlps' (posLevels rlps') (ecbs₀[nP + i]'hltC).2.pw }) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hltC]; rfl
    have hgetR0 : rcbs₀.getD (nP + i) default = rcbs₀[nP + i]'hltR := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hltR]; rfl
    have hgetC0 : ecbs₀.getD (nP + i) default = ecbs₀[nP + i]'hltC := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hltC]; rfl
    rw [hgetR0, hgetC0] at hsp0
    have hft_len : (Ix.Kernel.structFieldTeleOf (posOf rlps' C₀) nP nF i).length =
        (Ix.Kernel.structFieldTeleOf C₀ nP nF i).length := by
      unfold posOf
      rw [ilp_structFieldTeleOf rlps' (posLevels rlps') C₀ nP nF i
        ⟨_, _, hsC₀, hltC⟩, List.length_map]
    have htl_lt := hwf_j.tele_lt i hi
    refine ⟨hi_lt, ?_, by rw [hft_len]; dsimp only [n, nF, C₀]; omega⟩
    rw [hgetR, hgetC]
    exact rawRecSpine_ilp rlps' (posLevels rlps') hsp0
  have ext_2_175 := ext_2_114.trans ev185.heap_extends
  have ext_h_175 := ev14.heap_extends.trans ext_2_175
  have hbnd_ih : IxVM.Consistency.Bounded cs210 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have hih_apps := natI_ih_apps_spec hRec hsR_pos hsE_pos
    (fun i hi => ⟨(hall_ih i hi).1, (hall_ih i hi).2.1⟩) (by omega) hbnd_ih
    (Bytes.repAddressRef_heapMono₂ addrTy ext_h_175 hbRec)
    (RepKLevelList.mono hrlvls ext_h_175)
    (repKLevel_heapMono₂ ext_h_175 hpw)
    (fieldRepList_mono ext_2_175 hrec_c)
    (hRaw_c.mono ext_2_175) ev212
  have hcat := kexpr_list_concat_spec' ev171 (tmRepList_mono ev212.heap_extends hps_f') hih_apps
  have ext_114_161 := ev185.heap_extends.trans (ev212.heap_extends.trans ev171.heap_extends)
  have hbody := nat_app_n_spec (hbvar_min.mono ext_114_161) hcat ev110
  change Tm κ 0 (fun _ => default) m98 (nP + 1 + n + nF)
    (Ix.Kernel.structRuleBodyR recC rlvls_c ℓ.zeronessOf nP n nF j recIdx
      (Ix.Kernel.structFieldTeleOf (posOf rlps' C₀) nP nF)
      (Ix.Kernel.structFieldIdxOf (posOf rlps' C₀) nP nF)) v97 at hbody
  -- Step 3: `peel_n_foralls`, `expr_lift`, `nat_replace_pis` (fields -> `inner`)
  have ext_2_98 := ext_2_114.trans (ext_114_161.trans ev110.heap_extends)
  obtain ⟨hm326_eq, _, ecbsP, _, ecrest, _, hsCP_pos, hcrest_raw⟩ :=
    peel_n_foralls_rawTm_spec nP (by omega) (hRaw_c.mono ext_2_98) ev336
  rw [hm326_eq, evalBinOp_add_one n op366] at ev321
  have hbnd_lift : IxVM.Consistency.Bounded cs319 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have hcrest_tm : Tm κ 0 (fun _ => default) m98 nP ecrest v322 := by
    simpa [Nat.zero_add] using hcrest_raw.toTm
  have hcrest_lift := expr_lift_local_spec (Nat.zero_le nP) (by omega) (by decide)
    hbnd_lift hcrest_tm ev321
  have hcrest_lift' : Tm κ 0 (fun _ => default) m311 (nP + 1 + n)
      (ecrest.liftLooseBVars (n + 1) 0) v293 := by
    rw [show nP + (n + 1) = nP + 1 + n by omega] at hcrest_lift
    exact hcrest_lift
  have ext_h_311 := ev14.heap_extends.trans (ext_2_98.trans ev321.heap_extends)
  obtain ⟨inner, hinner_ite, hinner_tm⟩ :=
    nat_replace_pis_spec nF (by omega) (repKLevel_heapMono₂ ext_h_311 hpw)
      hcrest_lift' (hbody.mono ev321.heap_extends) ev290
  have h1_ne_0 : (.field 1 : SourceValue F) ≠ .field 0 := by
    intro h01; exact absurd (Value.field.inj h01) one_ne_zero
  rw [ite_eq_right h1_ne_0] at hinner_ite
  -- Step 4: `nat_minors` (`isLam = true`) and outer `Lam` + `nat_replace_pis`
  have ext_h_278 := ext_h_311.trans ev290.heap_extends
  have hload_min : NatCtorLoadI κ b₀ idx k ctors_info x_block cs398 :=
    hload.mono_calls (fun x hx => by simp [hx])
  have hgood_min : Good c cs398 := hgood.sub (fun x hx => by simp [hx])
  have hbnd_min : IxVM.Consistency.Bounded cs398 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have ev400' : ObsFn W "KernelCheck::nat_minors"
      [x_block, .field (idx : F), x_t, x_lps, .field (nP : F), .field (nIdx : F), x_pw,
        .field (n : F), .field ((if large then 1 else 0 : Nat) : F),
        .field ((0 : Nat) : F), v277, .field ((if true then 1 else 0 : Nat) : F)]
      m278 v387 m388 cs398 := by
    simpa using ev400
  obtain ⟨minors, hmin_eq, hmin_tm⟩ :=
    natI_minors_spec hT hκ_inj hidx hCres (by omega) hwf_all n 0 (by omega)
      hload_min hgood_min hbnd_min
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_278 hb₀)
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_278 hbT)
      (RepKLevelList.mono hlps ext_h_278)
      (repKLevel_heapMono₂ ext_h_278 hpw)
      hinner_tm ev400'
  simp only [↓reduceIte, List.drop_zero, Nat.add_zero] at hmin_eq hmin_tm
  have ext_388_528 : Heap.Extends m388 m528 := by rw [hm536]; exact Heap.Extends.snoc _ _
  have ext_h_528 := ext_h_278.trans (ev400.heap_extends.trans ext_388_528)
  have hlam_mot : Tm κ 0 (fun _ => default) m528 (0 + nP)
      (.lam motiveTy minors { pw := ℓ.zeronessOf }) (.ptr (.enum kexprEnum) m388.length) := by
    rw [Nat.zero_add]
    exact .lam (by rw [hm536]; simp)
      (hmotive.mono ext_h_528)
      (hmin_tm.mono ext_388_528)
      (repKLevel_heapMono₂ ext_h_528 hpw)
  obtain ⟨rhs_c, hrhs_ite, hrhs_tm⟩ :=
    nat_replace_pis_spec nP (by omega) (repKLevel_heapMono₂ ext_h_528 hpw)
      (htty.mono ext_h_528) hlam_mot ev500
  rw [ite_eq_right h1_ne_0] at hrhs_ite
  refine ⟨rhs_c, ?_, hrhs_tm⟩
  unfold cRuleRhs
  dsimp only
  have hcj_pos :
      (ctors_info.map fun info => (info.1, info.2.1, posOf rlps' info.2.2.2.1, info.2.2.2.2))[j]? =
        some (info.1, nF, posOf rlps' C₀, recIdx) := by
    simp [List.getElem?_map, hinfo_get, nF, C₀, recIdx]
  rw [hcj_pos]
  dsimp only [Option.bind]
  rw [hsT_pos]
  dsimp only [Option.bind]
  rw [hmot_eq]
  dsimp only [Option.bind]
  rw [hsCP_pos]
  dsimp only [Option.bind]
  simp only [List.length_map]
  change Expr.pisToLamsPw ℓ.zeronessOf nF (ecrest.liftLooseBVars (n + 1) 0) _ = some inner
    at hinner_ite
  rw [hinner_ite]
  dsimp only [Option.bind]
  rw [hmin_eq]
  dsimp only [Option.bind]
  exact hrhs_ite

/-- `KernelCheck::nat_check_rules` at member `idx` verifies each rule's field count `nF` and
establishes `WrapRelSem find?` between the generated rule right-hand side `structRecRhsR` and the
declared one, under `WrapLoads` at the keying `κ`. -/
theorem natI_check_rules_spec {c : Ctx} {κ : _root_.Address → KKey}
    {find? : KKey → Option (ConstantInfo .anon)}
    {T recC : KKey} {b₀ bT bRec : Bytes.Address} {idx k nP nIdx : Nat}
    {large : Bool} {tty₀ motiveTy : KExpr}
    {tbs₀ : List (KExpr × Ix.Kernel.BinderMeta)} {tsort₀ : KExpr}
    {tbsP : List (KExpr × Ix.Kernel.BinderMeta)} {itele_pos : KExpr}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)}
    [Resolved (κ (ixAddr bRec))]
    (hlf : WrapLoads c κ find?)
    (hT : κ (ixAddr bT) = T)
    (hκ_inj : ∀ a : Bytes.Address, κ (ixAddr a) = T → a = bT)
    (hRec : κ (ixAddr bRec) = recC)
    (hidx : idx < 4294967296)
    (hCres : ∀ i, i < ctors_info.length → κ (cprjAddr (ixAddr b₀) idx i) ≠ unresolvedKey)
    (hnCtors_lt : ctors_info.length < 2147483648)
    (hnP_lt : nP < 2147483648)
    (hwf_all : ∀ info ∈ ctors_info,
      NatCtorInfoWf T k large nP nIdx ctors_info.length info)
    (hsT₀ : tty₀.stripPis (nP + nIdx) = some (tbs₀, tsort₀))
    (hsT_pos : (posOf (if large then k :: List.range k else List.range k) tty₀).stripPis nP =
      some (tbsP, itele_pos))
    (hmot_eq : cMotiveTyI T
      ((List.range k).map (fun i => Level.param ((if large then 1 else 0) + i)))
      (if large then Level.param 0 else Level.zero) nP nIdx itele_pos = some motiveTy) :
    ∀ {rls_tail : List (RecRule .anon)} (j : Nat)
      {x_rules x_block x_t x_lps x_pw x_tty x_motive_ty x_rec x_rlvls r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      j + rls_tail.length = ctors_info.length →
      RulesRep κ h (if large then k :: List.range k else List.range k) j x_rules rls_tail →
      NatCtorLoadI κ b₀ idx k ctors_info x_block cs →
      Good c cs →
      IxVM.Consistency.Bounded cs →
      Bytes.RepAddressRef addrTy h b₀ x_block →
      Bytes.RepAddressRef addrTy h bT x_t →
      Bytes.RepAddressRef addrTy h bRec x_rec →
      RepKLevelList h
        ((List.range k).map (fun i => Level.param ((if large then 1 else 0) + i))) x_lps →
      RepKLevelList h
        ((List.range ((if large then k :: List.range k else List.range k).length)).map Level.param)
        x_rlvls →
      RepKLevel h (if large then Level.param 0 else Level.zero) x_pw →
      Tm κ 0 (fun _ => default) h 0
        (posOf (if large then k :: List.range k else List.range k) tty₀) x_tty →
      Tm κ 0 (fun _ => default) h nP motiveTy x_motive_ty →
      ObsFn W "KernelCheck::nat_check_rules"
        [x_rules, x_block, .field (idx : F), x_t, x_lps, .field (nP : F), .field (nIdx : F), x_pw,
          .field (ctors_info.length : F),
          .field ((if large then 1 else 0 : Nat) : F),
          x_tty, x_motive_ty, x_rec, x_rlvls, .field (j : F)]
        h r h' cs →
      let rlps := if large then k :: List.range k else List.range k
      let elim := if large then k else 0
      let ctors₀ := ctors_info.map (fun info => (info.1, info.2.1, info.2.2.2.1, info.2.2.2.2))
      ∀ i (hlt : i < rls_tail.length) (hj_i : j + i < ctors_info.length),
        (rls_tail[i]'hlt).nfields = (ctors_info[j + i]'hj_i).2.1 ∧
        ∃ rhsG,
          Ix.Kernel.structRecRhsR T (List.range k) elim large nP nIdx tty₀ ctors₀
            recC (rlps.map .param) (j + i) = some rhsG ∧
          WrapRelSem find? rhsG (rls_tail[i]'hlt).rhs := by
  intro rls_tail
  induction rls_tail with
  | nil =>
    intro j x_rules x_block x_t x_lps x_pw x_tty x_motive_ty x_rec x_rlvls r h h' cs
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i hlt
    exact absurd hlt (Nat.not_lt_zero _)
  | cons rl rls_rest ih =>
    intro j x_rules x_block x_t x_lps x_pw x_tty x_motive_ty x_rec x_rlvls r h h' cs
      hj_len hrules hload hgood hbnd hb₀ hbT hbRec hlps hrlvls hpw htty hmotive ev
    have hj : j < ctors_info.length := by
      simp only [List.length_cons] at hj_len
      omega
    have hj_rest : (j + 1) + rls_rest.length = ctors_info.length := by
      simp only [List.length_cons] at hj_len
      omega
    match Obs.«KernelCheck::nat_check_rules».obs ev with
    | .Nil (ld12 := ld0) .. =>
      have ld0' : loadValue h x_rules = .ok (.construct krrListEnum "Nil" []) := ld0
      cases hrules with | cons cell _ _ => exact (load_cell_ne cell ld0' (by decide)).elim
    | .Cons (x_rest := x_rest) (x_cidx := x_cidx) (x_rnf := x_rnf) (x_rhs := x_rhs)
        (m98 := m98) (p105 := p105) (cs111 := cs_cprj)
        (w141 := w141) (w142 := w142) (w143 := w143) (w144 := w144)
        (w145 := w145) (w146 := w146) (x_c_nf := x_c_nf) (w147 := w147)
        (v227 := v227) (m230 := m230) (cs238 := cs_wrap)
        (v241 := v241) (m244 := m244) (cs252 := cs_rhs)
        (cs384 := cs_rec) (v401 := v401)
        (ld12 := ld0) (ev113 := ev_cprj) (ld107 := ld_ctor) (heq215 := heq_nf)
        (ev254 := ev_rhs) (ev240 := ev_wrap) (heq380 := heq_w1)
        (op513 := op_j1) (ev386 := ev_rec) (hc515 := hc) .. =>
      subst hc heq_w1
      cases hrules with
      | cons cell hr hrules_rest =>
        have ld0' : loadValue h _ = .ok (.construct krrListEnum "Cons"
            [.construct krrEnum "Mk" [x_cidx, x_rnf, x_rhs], x_rest]) := ld0
        obtain ⟨-, hxs⟩ := load_cell cell ld0'
        injection hxs with hmk hxs; injection hxs with hrest_eq; subst hrest_eq
        obtain ⟨rhs_p, hmk_eq, hrnf_lt, hrhs_tmC⟩ := hr
        rw [hmk] at hmk_eq
        injection hmk_eq with _ _ hmk_args
        injection hmk_args with _ hmk_args
        injection hmk_args with hrnf_eq hmk_args
        injection hmk_args with hrhs_eq
        subst hrnf_eq hrhs_eq
        -- Step 1: constructor `j` field count from `NatCtorLoadI`
        let info := ctors_info[j]'hj
        have hinfo_get : ctors_info[j]? = some info := List.getElem?_eq_getElem hj
        have hwf_j : NatCtorInfoWf T k large nP nIdx ctors_info.length info :=
          hwf_all info (List.mem_of_getElem? hinfo_get)
        have ld_ctor' : loadValue m98 p105 = .ok (.construct kciEnum "Ctor"
            [w141, w142, w143, w144, w145, w146, x_c_nf, w147]) := ld_ctor
        obtain ⟨_, hcnf_eq, _⟩ :=
          hload j hj p105 h m98 cs_cprj w141 w142 w143 w144 w145 w146 x_c_nf w147
            (fun x hx => by simp [hx]) hb₀ ev_cprj ld_ctor' info hinfo_get
        have hnf_val : rl.nfields = info.2.1 := by
          rw [hcnf_eq] at heq_nf
          have hv := congrArg ZMod.val (Value.field.inj heq_nf)
          have h1 : ZMod.val (rl.nfields : F) = rl.nfields :=
            ZMod.val_natCast_of_lt (Nat.lt_trans hrnf_lt (by decide))
          have h2 : ZMod.val (info.2.1 : F) = info.2.1 :=
            ZMod.val_natCast_of_lt (Nat.lt_trans
              (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hwf_j.nf_lt) (by decide))
          omega
        -- Step 2: `nat_rule_rhs` + `posOf_structRecRhsR` + `wrap_rel`
        have ext_h_98 := ev_cprj.heap_extends
        have hload_rhs : NatCtorLoadI κ b₀ idx k ctors_info x_block cs_rhs :=
          hload.mono_calls (fun x hx => by simp [hx])
        have hgood_rhs : Good c cs_rhs := hgood.sub (fun x hx => by simp [hx])
        have hbnd_rhs : IxVM.Consistency.Bounded cs_rhs :=
          RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
        obtain ⟨rhs_c, hrhs_c, hrhs_c_tm⟩ :=
          natI_rule_rhs_spec hT hκ_inj hRec hidx hCres hnCtors_lt hnP_lt hj hwf_all hsT_pos
            hmot_eq hload_rhs hgood_rhs hbnd_rhs
            (Bytes.repAddressRef_heapMono₂ addrTy ext_h_98 hb₀)
            (Bytes.repAddressRef_heapMono₂ addrTy ext_h_98 hbT)
            (Bytes.repAddressRef_heapMono₂ addrTy ext_h_98 hbRec)
            (RepKLevelList.mono hlps ext_h_98)
            (RepKLevelList.mono hrlvls ext_h_98)
            (repKLevel_heapMono₂ ext_h_98 hpw)
            (htty.mono ext_h_98)
            (hmotive.mono ext_h_98)
            ev_rhs
        let rlps := if large then k :: List.range k else List.range k
        let elim := if large then k else 0
        let ctors₀ := ctors_info.map (fun info => (info.1, info.2.1, info.2.2.2.1, info.2.2.2.2))
        have hj₀ : j < ctors₀.length := by simp [ctors₀, hj]
        have hcs₀ : ∀ entry ∈ ctors₀,
            (∃ cbs cbody, entry.2.2.1.stripPis (nP + entry.2.1) = some (cbs, cbody)) ∧
            ∀ i ∈ entry.2.2.2, i < entry.2.1 := by
          intro entry hentry
          simp only [ctors₀, List.mem_map] at hentry
          obtain ⟨inf, hinf_mem, rfl⟩ := hentry
          have hwf_inf := hwf_all inf hinf_mem
          obtain ⟨cbs, _, cbody, hsC⟩ := hwf_inf.strip_C
          exact ⟨⟨cbs, _, hsC⟩, fun i hi => (hwf_inf.rec_spines i hi).1⟩
        have hpos_rhs := posOf_structRecRhsR k large T nP nIdx tty₀ ctors₀ recC j
          hj₀ ⟨tbs₀, tsort₀, hsT₀⟩ hcs₀
        dsimp only at hpos_rhs
        rw [← clvls_eq_subst_params k large, ← rlvls_eq_subst_params k large] at hpos_rhs
        have hmap_cs :
            (ctors₀.map fun entry => (entry.1, entry.2.1, posOf rlps entry.2.2.1, entry.2.2.2)) =
            (ctors_info.map fun inf => (inf.1, inf.2.1, posOf rlps inf.2.2.2.1, inf.2.2.2.2)) := by
          simp [ctors₀, List.map_map, Function.comp_def]
        rw [hmap_cs, hrhs_c] at hpos_rhs
        rw [Option.map_eq_some_iff] at hpos_rhs
        obtain ⟨rhsG, hrhsG, hpos_rhsG⟩ := hpos_rhs
        rw [← hpos_rhsG] at hrhs_c_tm
        have ext_h_244 := ext_h_98.trans ev_rhs.heap_extends
        have hgood_wrap : Good c cs_wrap := hgood.sub (fun x hx => by simp [hx])
        have hrhs_decl_tm : Tm κ 0 (fun _ => default) m244 0 (posOf rlps rl.rhs) x_rhs :=
          (hrhs_tmC 0 (fun _ => default)).mono ext_h_244
        have hwrap_pos := wrapL_rel_spec hlf hgood_wrap hrhs_c_tm hrhs_decl_tm ev_wrap
        have hwrap_j : WrapRelSem find? rhsG rl.rhs :=
          WrapRelSem.of_posOf_perm (rlps_perm k large) hwrap_pos
        -- Step 3: recursive tail `rls_rest` at `j + 1`
        rw [evalBinOp_add_one j op_j1] at ev_rec
        have ext_h_230 := ext_h_244.trans ev_wrap.heap_extends
        have hload_rec : NatCtorLoadI κ b₀ idx k ctors_info x_block cs_rec :=
          hload.mono_calls (fun x hx => by simp [hx])
        have hgood_rec : Good c cs_rec := hgood.sub (fun x hx => by simp [hx])
        have hbnd_rec : IxVM.Consistency.Bounded cs_rec :=
          RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
        have htail := ih (j + 1) hj_rest
          (hrules_rest.mono ext_h_230)
          hload_rec hgood_rec hbnd_rec
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_230 hb₀)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_230 hbT)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_230 hbRec)
          (RepKLevelList.mono hlps ext_h_230)
          (RepKLevelList.mono hrlvls ext_h_230)
          (repKLevel_heapMono₂ ext_h_230 hpw)
          (htty.mono ext_h_230)
          (hmotive.mono ext_h_230)
          ev_rec
        intro _ _ _ i hlt hj_i
        cases i with
        | zero =>
          simp only [List.getElem_cons_zero, Nat.add_zero]
          exact ⟨hnf_val, rhsG, hrhsG, hwrap_j⟩
        | succ i' =>
          have hlt' : i' < rls_rest.length := Nat.lt_of_succ_lt_succ hlt
          have hj_i' : (j + 1) + i' < ctors_info.length := by omega
          obtain ⟨hnf', rhsG', hrhsG', hwrap'⟩ := htail i' hlt' hj_i'
          have hadd : j + (i' + 1) = (j + 1) + i' := by omega
          simp only [List.getElem_cons_succ, hadd]
          exact ⟨hnf', rhsG', hrhsG', hwrap'⟩

end IxVM.Refinement.Decl
