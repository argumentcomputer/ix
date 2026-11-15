import IxVMRefinement.Decl.NativeRecCheck
import IxVMRefinement.Decl.NativeFront
import IxVMRefinement.Callees.Loads
import IxVMRefinement.Callees.ProjAddr
import IxVMRefinement.Callees.Modeled
import IxVMRefinement.Obs.KernelCheck7
import IxVMRefinement.Obs.KernelCheck8
import IxVMRefinement.Obs.KernelCheck9
import IxVMRefinement.Obs.KernelCheck11
import IxVMRefinement.Obs.KernelCheck12

/-!
# Native One-Type Inductive Blocks with Recursor (`L5` Native Recursor Rules & Assembly)

Circuit refinement specifications for `nat_rule_rhs`, `nat_check_rules`,
`find_peer_recursor_with_spec`, `nat_rec_check`, `check_recursor_canonical_full`, and
`check_recursor_member`, assembling `DeclNativeRunJ`, `InstallStep`, and `DeclInv` preservation
for canonical native inductive blocks with recursor.
-/

universe u

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (Expr Level LevelParam ConstantVal ConstantInfo RecRule Declaration)
open Ix.Kernel.Rules (Red DefEq Infer Annot)
open Ix.Kernel.Model (rulesJ)
open Ix.Kernel.Semantics (Judgements ConstantValCheckJ StructDomsJ FieldSortsJ
  SumIndRunJ SumCtorRunJ SumCtorsRunJ FormerReadJ
  NativeRecRunJ RecStoredJ NativeRecJ DeclNativeRunJ letFree)

set_option maxHeartbeats 1600000

private theorem level_allParamsDefined_mono {ps qs : List LevelParam}
    (hsub : ∀ x ∈ ps, x ∈ qs) {u : Level}
    (h : u.allParamsDefined ps = true) : u.allParamsDefined qs = true := by
  induction u with
  | zero => rfl
  | succ l ih => exact ih h
  | max l r ihl ihr | imax l r ihl ihr =>
    simp only [Level.allParamsDefined, Bool.and_eq_true] at h ⊢
    exact ⟨ihl h.1, ihr h.2⟩
  | param n =>
    simp only [Level.allParamsDefined, List.contains_iff_mem] at h ⊢
    exact hsub n h

private theorem pw_paramsDefined_mono {ps qs : List LevelParam}
    (hsub : ∀ x ∈ ps, x ∈ qs) {pw : Ix.Kernel.PropWhen}
    (h : pw.paramsDefined ps = true) : pw.paramsDefined qs = true := by
  unfold Ix.Kernel.PropWhen.paramsDefined at h ⊢
  split at h
  · rfl
  · rfl
  · simp only [List.contains_iff_mem] at h ⊢
    exact hsub _ h
  · simp only [Bool.and_eq_true, List.contains_iff_mem] at h ⊢
    exact ⟨hsub _ h.1, hsub _ h.2⟩
  · simp only [List.all_eq_true, List.contains_iff_mem] at h ⊢
    exact fun x hx => hsub x (h x hx)

private theorem expr_allLevelParamsDefined_mono {ps qs : List LevelParam}
    (hsub : ∀ x ∈ ps, x ∈ qs) {e : KExpr}
    (he : e.allLevelParamsDefined ps = true) :
    e.allLevelParamsDefined qs = true := by
  induction e with
  | bvar _ | lit _ => rfl
  | sort u => exact level_allParamsDefined_mono hsub he
  | const _ us =>
    simp only [Expr.allLevelParamsDefined, List.all_eq_true] at he ⊢
    exact fun v hv => level_allParamsDefined_mono hsub (he v hv)
  | fvar _ ty iht =>
    simp only [Expr.allLevelParamsDefined] at he ⊢
    exact iht he
  | app f a ihf iha =>
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at he ⊢
    exact ⟨ihf he.1, iha he.2⟩
  | lam ty body m iht ihb | forallE ty body m iht ihb =>
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at he ⊢
    exact ⟨⟨iht he.1.1, ihb he.1.2⟩, pw_paramsDefined_mono hsub he.2⟩
  | letE ty val body _ iht ihv ihb =>
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at he ⊢
    exact ⟨⟨iht he.1.1, ihv he.1.2⟩, ihb he.2⟩
  | proj _ _ sub ih =>
    simp only [Expr.allLevelParamsDefined] at he ⊢
    exact ih he

private theorem toSemanticsForall₂ {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) : Ix.Kernel.Semantics.Forall₂ R xs ys := by
  induction h with
  | nil => exact .nil
  | cons hr _ ih => exact .cons hr ih

private theorem listForall₂_append {α β : Type _} {R : α → β → Prop}
    {xs₁ xs₂ : List α} {ys₁ ys₂ : List β}
    (h₁ : List.Forall₂ R xs₁ ys₁) (h₂ : List.Forall₂ R xs₂ ys₂) :
    List.Forall₂ R (xs₁ ++ xs₂) (ys₁ ++ ys₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons hr _ ih => exact .cons hr ih

/-! ## Section 1: Recursor level-frame helpers and `find_peer_recursor_with_spec` -/

theorem rlps_perm (k : Nat) (large : Bool) :
    let rlps := if large then k :: List.range k else List.range k
    rlps.Perm (List.range rlps.length) := by
  intro rlps
  dsimp only [rlps]
  cases large with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.length_range]
    exact List.Perm.refl _
  | true =>
    simp only [↓reduceIte, List.length_cons, List.length_range, List.range_succ]
    exact (List.perm_append_singleton k (List.range k)).symm

theorem rlvls_eq_subst_params (k : Nat) (large : Bool) :
    let rlps := if large then k :: List.range k else List.range k
    (List.range rlps.length).map Level.param =
      ((rlps.map .param).map (Level.subst rlps (posLevels rlps))) := by
  intro rlps
  dsimp only [rlps]
  cases large with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have h0 := map_subst_range_params k (posLevels (List.range k)) (by simp [posLevels])
    simpa [posLevels] using h0.symm
  | true =>
    simp only [↓reduceIte]
    have hpos : posLevels (k :: List.range k) =
        Level.param 0 :: (List.range k).map (fun i => Level.param (1 + i)) := by
      simp only [posLevels, List.length_cons, List.length_range, List.range_succ_eq_map,
        List.map_cons, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro x _
      simp [Nat.add_comm]
    have hhead :
        Level.subst (k :: List.range k) (posLevels (k :: List.range k)) (.param k) =
          Level.param 0 := by
      simp [Level.subst, Level.subst.go, hpos]
    have htail := map_subst_large_former_params k
    simp only [List.length_cons, List.length_range, List.map_cons, hhead]
    rw [htail]
    simpa [posLevels] using hpos

private theorem find_peer_rec_seg1_heap_extends
    {e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : SourceValue F}
    {h : Heap F} {r : SourceValue F} {h' : Heap F} {cs : List (Call F)}
    (sg : Obs.«KernelCheck::find_peer_rec_spec_walk».Seg1
      e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 h r h' cs) :
    Heap.Extends h h' := by
  cases sg with
  | Rec_Induct_n1_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ ev1 ev2 _ ev3 _ _ hh _ =>
    subst hh
    exact ev1.heap_extends.trans (ev2.heap_extends.trans ev3.heap_extends)
  | Rec_Induct_n1_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ ev1 ev2 _ ev3 _ ev4 ev5 _ =>
    exact ev1.heap_extends.trans (ev2.heap_extends.trans
      (ev3.heap_extends.trans (ev4.heap_extends.trans ev5.heap_extends)))
  | Rec_Induct_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ ev1 ev2 _ ev3 _ _ hh _ =>
    subst hh
    exact ev1.heap_extends.trans (ev2.heap_extends.trans ev3.heap_extends)
  | Rec_other_n1_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ ev1 ev2 _ _ ev3 _ _ hh _ =>
    subst hh
    exact ev1.heap_extends.trans (ev2.heap_extends.trans ev3.heap_extends)
  | Rec_other_n1_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ ev1 ev2 _ _ ev3 _ ev4 ev5 _ =>
    exact ev1.heap_extends.trans (ev2.heap_extends.trans
      (ev3.heap_extends.trans (ev4.heap_extends.trans ev5.heap_extends)))
  | Rec_other_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ ev1 ev2 _ _ ev3 _ _ hh _ =>
    subst hh
    exact ev1.heap_extends.trans (ev2.heap_extends.trans ev3.heap_extends)
  | other _ _ hh _ =>
    subst hh
    exact Heap.Extends.refl _

/-- On a 2-member mutual block `[.indc ind, .recr rec]` at `b₀` in `c.E`,
`KernelCheck::find_peer_recursor_with_spec` returns a heap address representing `rprjAddr (ixAddr b₀) 1`
(the block's unique recursor projection address `bRec`). -/
theorem find_peer_recursor_two_spec {c : Ctx} (hc : CoreFacts c)
    {cst : Ixon.Constant} {ind : Ixon.Inductive} {rec_m : Ixon.Recursor}
    {b₀ bRec : Bytes.Address}
    {x_block x_t x_sp x_aux x_self r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrec_at : Ix.Cert.recordAt c.E (ixAddr b₀) = some cst)
    (hcst_info : cst.info = .muts #[.indc ind, .recr rec_m])
    (hbRec_addr : ixAddr bRec = rprjAddr (ixAddr b₀) 1)
    (hgood : Good c cs)
    (hb₀ : Bytes.RepAddressRef addrTy h b₀ x_block)
    (hbRec : Bytes.RepAddressRef addrTy h bRec x_self)
    (ev : ObsFn W "KernelCheck::find_peer_recursor_with_spec"
      [x_block, x_t, x_sp, x_aux, x_self] h r h' cs) :
    ∃ bOut : Bytes.Address,
      Bytes.RepAddressRef addrTy h' bOut r ∧ ixAddr bOut = ixAddr bRec := by
  match Obs.«KernelCheck::find_peer_recursor_with_spec».obs ev with
  | .other (cs12 := cs12) (ev14 := ev_ld) (hne159 := hne) (hc166 := hc_cs) .. =>
    subst hc_cs
    have hgood_ld : Good c cs12 := hgood.sub (fun x hx => by simp [hx])
    have hshape := (load_verified_constant_step c hc ev_ld _ b₀ rfl hgood_ld hb₀).2 cst hrec_at
    rcases hshape with ⟨info_v, sh, rf, un, bd, hv_mk, hinfo⟩
    injection hv_mk with _ _ hv_args
    injection hv_args with hinfo_eq _
    subst hinfo_eq
    rw [hcst_info] at hinfo
    rcases hinfo with ⟨lp, hv_muts, _⟩
    exact (hne [lp] rfl hv_muts).elim
  | .Muts (m2 := m2) (cs12 := cs12) (x_members := x_members) (cs92 := cs92)
      (ev14 := ev_ld) (ev94 := ev_walk) (hc158 := hc_cs) .. =>
    subst hc_cs
    have hgood_ld : Good c cs12 := hgood.sub (fun x hx => by simp [hx])
    have hshape := (load_verified_constant_step c hc ev_ld _ b₀ rfl hgood_ld hb₀).2 cst hrec_at
    rcases hshape with ⟨info_v, sh, rf, un, bd, hv_mk, hinfo⟩
    injection hv_mk with _ _ hv_args
    injection hv_args with hinfo_eq _
    subst hinfo_eq
    rw [hcst_info] at hinfo
    rcases hinfo with ⟨lp, hv_muts, hms⟩
    injection hv_muts with _ _ hlp_args
    injection hlp_args with hlp_eq
    subst hlp_eq
    change Specs.Callees.MembersRep m2 [.indc ind, .recr rec_m] x_members at hms
    -- Step 0 (`pos = 0`, `.indc ind`): must take `Cons_other`
    have hgood_w0 : Good c cs92 := hgood.sub (fun x hx => by simp [hx])
    match Obs.«KernelCheck::find_peer_rec_spec_walk».obs ev_walk with
    | .Nil (ld12 := ld0) .. =>
      have ld0' : loadValue m2 x_members =
          .ok (.construct Specs.Callees.mutListEnum "Nil" []) := ld0
      cases hms with | cons cell _ _ => exact (load_cell_ne cell ld0' (by decide)).elim
    | .Cons_Recr_n1 (w57 := w57) (ld12 := ld0) .. =>
      obtain ⟨_, _, heq, hm0, _⟩ := RepList.cons_of_load hms ld0
      injection heq with h1 _; subst h1
      rcases hm0 with ⟨x0, hx0⟩
      exact absurd hx0 (by simp [Specs.Callees.mutCtor])
    | .Cons_Recr_other (w57 := w57) (ld12 := ld0) .. =>
      obtain ⟨_, _, heq, hm0, _⟩ := RepList.cons_of_load hms ld0
      injection heq with h1 _; subst h1
      rcases hm0 with ⟨x0, hx0⟩
      exact absurd hx0 (by simp [Specs.Callees.mutCtor])
    | .Cons_other (x_m := xm0) (x_rest := xrest1) (cs796 := cs_w1) (v806 := vpos1)
        (ld12 := ld0) (op869 := op_pos1) (ev798 := ev_walk1) (hc871 := hc_w0) .. =>
      subst hc_w0
      obtain ⟨_, _, heq0, _, hms1⟩ := RepList.cons_of_load hms ld0
      injection heq0 with _ htl0; subst htl0
      rw [evalBinOp_add_one 0 op_pos1] at ev_walk1
      -- Step 1 (`pos = 1`, `.recr rec_m`)
      have hgood_w1 : Good c cs_w1 := hgood_w0.sub (fun x hx => by simp [hx])
      match Obs.«KernelCheck::find_peer_rec_spec_walk».obs ev_walk1 with
      | .Nil (ld12 := ld1) .. =>
        have ld1' : loadValue m2 xrest1 =
            .ok (.construct Specs.Callees.mutListEnum "Nil" []) := ld1
        cases hms1 with | cons cell _ _ => exact (load_cell_ne cell ld1' (by decide)).elim
      | .Cons_other (ld12 := ld1) (hne789 := hne1) .. =>
        obtain ⟨_, _, heq1, hm1, _⟩ := RepList.cons_of_load hms1 ld1
        injection heq1 with h1 _; subst h1
        rcases hm1 with ⟨x1, hx1⟩
        exact (hne1 [x1] rfl hx1).elim
      | .Cons_Recr_n1 (v63 := v63) (m64 := m64) (cs74 := cs_pa) (m102 := m102)
          (cs115 := cs_gci) (m680 := m680) (cs682 := cs_sg)
          (ev76 := ev_pa) (ev117 := ev_gci) (sg687 := sg1)
          (he703 := hr) (he704 := hh) (hc705 := hc_w1) .. =>
        subst hc_w1 hr hh
        have hgood_pa : Good c cs_pa := hgood_w1.sub (fun x hx => by simp [hx])
        have hb₀_m2 := Bytes.repAddressRef_heapMono₂ addrTy ev_ld.heap_extends hb₀
        obtain ⟨bOut, hbOut, hbOut_addr⟩ :=
          ProjAddrAux.projection_addr_spec c (ms := [.indc ind, .recr rec_m]) (i := 1)
            (by simp) (by simp) hgood_pa hms hb₀_m2 ev_pa
        have ext_64_680 := ev_gci.heap_extends.trans (find_peer_rec_seg1_heap_extends sg1)
        refine ⟨bOut, Bytes.repAddressRef_heapMono₂ addrTy ext_64_680 hbOut, ?_⟩
        rw [hbRec_addr]
        exact hbOut_addr
      | .Cons_Recr_other (x_rest := xrest2) (m64 := m64) (cs74 := cs_pa) (m102 := m102)
          (cs115 := cs_gci) (m680 := m680) (cs682 := cs_sg) (cs713 := cs_w2) (v723 := vpos2)
          (ld12 := ld1) (ev76 := ev_pa) (ev117 := ev_gci) (sg687 := sg1)
          (op786 := op_pos2) (ev715 := ev_walk2) (hc788 := hc_w1) .. =>
        subst hc_w1
        obtain ⟨_, _, heq1, _, hms2⟩ := RepList.cons_of_load hms1 ld1
        injection heq1 with _ htl1; subst htl1
        have ext_m2_680 := ev_pa.heap_extends.trans
          (ev_gci.heap_extends.trans (find_peer_rec_seg1_heap_extends sg1))
        have hms2_680 : Specs.Callees.MembersRep m680 [] xrest2 := by
          cases hms2 with | nil cell => exact .nil (ext_m2_680.getElem?_eq cell)
        -- Step 2 (`pos = 2`, `[]`): must take `Nil` returning `x_self`
        match Obs.«KernelCheck::find_peer_rec_spec_walk».obs ev_walk2 with
        | .Nil (he21 := hr) (he22 := hh) .. =>
          subst hr hh
          exact ⟨bRec,
            Bytes.repAddressRef_heapMono₂ addrTy (ev_ld.heap_extends.trans ext_m2_680) hbRec,
            rfl⟩
        | .Cons_Recr_n1 (ld12 := ld2) .. =>
          have ld2' : loadValue m680 xrest2 =
              .ok (.construct Specs.Callees.mutListEnum "Cons" [_, _]) := ld2
          cases hms2_680 with | nil cell => exact (load_cell_ne cell ld2' (by decide)).elim
        | .Cons_Recr_other (ld12 := ld2) .. =>
          have ld2' : loadValue m680 xrest2 =
              .ok (.construct Specs.Callees.mutListEnum "Cons" [_, _]) := ld2
          cases hms2_680 with | nil cell => exact (load_cell_ne cell ld2' (by decide)).elim
        | .Cons_other (ld12 := ld2) .. =>
          have ld2' : loadValue m680 xrest2 =
              .ok (.construct Specs.Callees.mutListEnum "Cons" [_, _]) := ld2
          cases hms2_680 with | nil cell => exact (load_cell_ne cell ld2' (by decide)).elim

/-! ## Section 2: `nat_rule_rhs`, `nat_check_rules`, and `nat_rec_check` -/

/-- `KernelCheck::nat_rule_rhs` builds the circuit-frame generated rule RHS `cRuleRhs` for
constructor `j` (`posOf rlps rhsG`). -/
theorem nat_rule_rhs_spec {c : Ctx}
    {T recC : KKey} {b₀ bT bRec : Bytes.Address} {k nP nIdx j : Nat} {large : Bool}
    {ℓ : KLevel} {rlvls_c : List KLevel} {tty₀ motiveTy : KExpr}
    {tbsP : List (KExpr × Ix.Kernel.BinderMeta)} {itele_pos : KExpr}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)}
    {x_block x_t x_lps x_pw x_tty x_motive_ty x_rec x_rlvls r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hT : keyOf c.t (ixAddr bT) = T)
    (hκ_inj : ∀ a : Bytes.Address, keyOf c.t (ixAddr a) = T → a = bT)
    (hRec : keyOf c.t (ixAddr bRec) = recC)
    (hnCtors_lt : ctors_info.length < 2147483648)
    (hnP_lt : nP < 2147483648)
    (hj : j < ctors_info.length)
    (hwf_all : ∀ info ∈ ctors_info,
      NatCtorInfoWf T k large nP nIdx ctors_info.length info)
    (hsT_pos : (posOf (if large then k :: List.range k else List.range k) tty₀).stripPis nP =
      some (tbsP, itele_pos))
    (hmot_eq : cMotiveTyI T
      ((List.range k).map (fun idx => Level.param ((if large then 1 else 0) + idx)))
      ℓ nP nIdx itele_pos = some motiveTy)
    (hload : NatCtorLoad (keyOf c.t) b₀ k ctors_info x_block cs)
    (hgood : Good c cs)
    (hbnd : IxVM.Consistency.Bounded cs)
    (hb₀ : Bytes.RepAddressRef addrTy h b₀ x_block)
    (hbT : Bytes.RepAddressRef addrTy h bT x_t)
    (hbRec : Bytes.RepAddressRef addrTy h bRec x_rec)
    (hlps : RepKLevelList h
      ((List.range k).map (fun idx => Level.param ((if large then 1 else 0) + idx))) x_lps)
    (hrlvls : RepKLevelList h rlvls_c x_rlvls)
    (hpw : RepKLevel h ℓ x_pw)
    (htty : Tm (keyOf c.t) 0 (fun _ => default) h 0
      (posOf (if large then k :: List.range k else List.range k) tty₀) x_tty)
    (hmotive : Tm (keyOf c.t) 0 (fun _ => default) h nP motiveTy x_motive_ty)
    (ev : ObsFn W "KernelCheck::nat_rule_rhs"
      [x_block, .field 0, x_t, x_lps, .field (nP : F), .field (nIdx : F), x_pw,
        .field (ctors_info.length : F),
        .field ((if large then 1 else 0 : Nat) : F),
        x_tty, x_motive_ty, x_rec, x_rlvls, .field (j : F)]
      h r h' cs) :
    let rlps := if large then k :: List.range k else List.range k
    let clvls := (List.range k).map (fun idx => Level.param ((if large then 1 else 0) + idx))
    let cs_pos := ctors_info.map (fun info => (info.1, info.2.1, posOf rlps info.2.2.2.1, info.2.2.2.2))
    ∃ rhs_c,
      cRuleRhs T clvls ℓ nP nIdx (posOf rlps tty₀) cs_pos recC rlvls_c j = some rhs_c ∧
      Tm (keyOf c.t) 0 (fun _ => default) h' 0 rhs_c r := by
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
  have hload_ctor : NatCtorLoad (keyOf c.t) b₀ k ctors_info x_block cs12 :=
    hload.mono_calls (fun x hx => by simp [hx])
  obtain ⟨x_cty', x_rec_idx', htup_c, hRaw_c, hrec_c, _⟩ :=
    nat_ctor_spec hT hκ_inj hj hinfo_get hwf_j hload_ctor hbnd_ctor hb₀ hbT hlps ev14
  injection htup_c with hl_c
  injection hl_c with h1 hl_c; injection hl_c with h2 hl_c; injection hl_c with h3
  subst h1 h2 h3
  -- Step 2: `structRuleBodyR` via `BVar`, `nat_ps_at`, `nat_ih_apps`, `concat`, `nat_app_n`
  rw [evalBinOp_add_nat nF n op156] at op148
  rw [evalBinOp_sub_nat (by omega : 1 ≤ nF + n) op148] at op140
  rw [evalBinOp_sub_nat (by omega : j ≤ nF + n - 1) op140] at hm122
  have ext_2_114 : Heap.Extends m2 m114 := by rw [hm122]; exact Heap.Extends.snoc _ _
  have hbvar_min : Tm (keyOf c.t) 0 (fun _ => default) m114 (nP + 1 + n + nF)
      (.bvar (nF + n - 1 - j)) (.ptr (.enum kexprEnum) m2.length) := by
    rw [hm122]
    exact tm_bvarLocal_nat (by simp) (by omega) (by omega)
  have hps_f := nat_ps_at_spec (κ := keyOf c.t) (d := 0) (Γ := fun _ => default)
    nF 0 (nP + 1 + n + nF) (by omega) hbase_lt ev185
  have hps_f' : RepList kexprListEnum
      (fun h E p => Tm (keyOf c.t) 0 (fun _ => default) h (nP + 1 + n + nF) E p)
      m175 ((List.range nF).map fun idx => Expr.bvar (nF - 1 - idx)) v172 := by
    rw [structPsAt_zero_eq_structTeleVars] at hps_f
    exact hps_f
  let rlps' := if large then k :: List.range k else List.range k
  obtain ⟨rcbs₀, rus₀, rargs₀, hsR₀⟩ := hwf_j.strip_R
  obtain ⟨ecbs₀, eus₀, eargs₀, hsC₀⟩ := hwf_j.strip_C
  have hsR_pos := ilp_stripPis rlps' (posLevels rlps') (nP + nF) hsR₀
  change (posOf rlps' R₀).stripPis (nP + nF) = _ at hsR_pos
  have hsE_pos := ilp_stripPis rlps' (posLevels rlps') (nP + nF) hsC₀
  change (posOf rlps' C₀).stripPis (nP + nF) = _ at hsE_pos
  have hall_ih : ∀ idx ∈ recIdx, idx < nF ∧
      RawRecSpine T
        ((rcbs₀.map (fun b => (posOf rlps' b.1,
          { b.2 with pw := Level.substPW rlps' (posLevels rlps') b.2.pw }))).getD
          (nP + idx) default).1
        ((ecbs₀.map (fun b => (posOf rlps' b.1,
          { b.2 with pw := Level.substPW rlps' (posLevels rlps') b.2.pw }))).getD
          (nP + idx) default).1 ∧
      nP + 1 + n + nF +
        (Ix.Kernel.structFieldTeleOf (posOf rlps' C₀) nP nF idx).length < 4294967296 := by
    intro idx hidx
    obtain ⟨hi_lt, hsp_fn⟩ := hwf_j.rec_spines idx hidx
    have hsp0 := hsp_fn rcbs₀ _ ecbs₀ _ hsR₀ hsC₀
    have hlenR : rcbs₀.length = nP + nF := stripPis_length (nP + nF) hsR₀
    have hlenC : ecbs₀.length = nP + nF := stripPis_length (nP + nF) hsC₀
    have hltR : nP + idx < rcbs₀.length := by omega
    have hltC : nP + idx < ecbs₀.length := by omega
    have hgetR : (rcbs₀.map (fun b => (posOf rlps' b.1,
        { b.2 with pw := Level.substPW rlps' (posLevels rlps') b.2.pw }))).getD (nP + idx) default =
        (posOf rlps' (rcbs₀[nP + idx]'hltR).1,
          { (rcbs₀[nP + idx]'hltR).2 with
            pw := Level.substPW rlps' (posLevels rlps') (rcbs₀[nP + idx]'hltR).2.pw }) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hltR]; rfl
    have hgetC : (ecbs₀.map (fun b => (posOf rlps' b.1,
        { b.2 with pw := Level.substPW rlps' (posLevels rlps') b.2.pw }))).getD (nP + idx) default =
        (posOf rlps' (ecbs₀[nP + idx]'hltC).1,
          { (ecbs₀[nP + idx]'hltC).2 with
            pw := Level.substPW rlps' (posLevels rlps') (ecbs₀[nP + idx]'hltC).2.pw }) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hltC]; rfl
    have hgetR0 : rcbs₀.getD (nP + idx) default = rcbs₀[nP + idx]'hltR := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hltR]; rfl
    have hgetC0 : ecbs₀.getD (nP + idx) default = ecbs₀[nP + idx]'hltC := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hltC]; rfl
    rw [hgetR0, hgetC0] at hsp0
    have hft_len : (Ix.Kernel.structFieldTeleOf (posOf rlps' C₀) nP nF idx).length =
        (Ix.Kernel.structFieldTeleOf C₀ nP nF idx).length := by
      unfold posOf
      rw [ilp_structFieldTeleOf rlps' (posLevels rlps') C₀ nP nF idx
        ⟨_, _, hsC₀, hltC⟩, List.length_map]
    have htl_lt := hwf_j.tele_lt idx hidx
    refine ⟨hi_lt, ?_, by rw [hft_len]; dsimp only [n, nF, C₀]; omega⟩
    rw [hgetR, hgetC]
    exact rawRecSpine_ilp rlps' (posLevels rlps') hsp0
  have ext_2_175 := ext_2_114.trans ev185.heap_extends
  have ext_h_175 := ev14.heap_extends.trans ext_2_175
  have hbnd_ih : IxVM.Consistency.Bounded cs210 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have hih_apps := nat_ih_apps_spec hRec hnPF_lt hsR_pos hsE_pos hall_ih hbase_lt hbnd_ih
    (Bytes.repAddressRef_heapMono₂ addrTy ext_h_175 hbRec)
    (RepKLevelList.mono hrlvls ext_h_175)
    (repKLevel_heapMono₂ ext_h_175 hpw)
    (fieldRepList_mono ext_2_175 hrec_c)
    (hRaw_c.mono ext_2_175) ev212
  have hcat := kexpr_list_concat_spec' ev171 (tmRepList_mono ev212.heap_extends hps_f') hih_apps
  have ext_114_161 := ev185.heap_extends.trans (ev212.heap_extends.trans ev171.heap_extends)
  have hbody := nat_app_n_spec (hbvar_min.mono ext_114_161) hcat ev110
  change Tm (keyOf c.t) 0 (fun _ => default) m98 (nP + 1 + n + nF)
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
  have hcrest_tm : Tm (keyOf c.t) 0 (fun _ => default) m98 nP ecrest v322 := by
    simpa [Nat.zero_add] using hcrest_raw.toTm
  have hcrest_lift := expr_lift_local_spec (Nat.zero_le nP) (by omega) (by decide)
    hbnd_lift hcrest_tm ev321
  have hcrest_lift' : Tm (keyOf c.t) 0 (fun _ => default) m311 (nP + 1 + n)
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
  have hload_min : NatCtorLoad (keyOf c.t) b₀ k ctors_info x_block cs398 :=
    hload.mono_calls (fun x hx => by simp [hx])
  have hgood_min : Good c cs398 := hgood.sub (fun x hx => by simp [hx])
  have hbnd_min : IxVM.Consistency.Bounded cs398 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have ev400' : ObsFn W "KernelCheck::nat_minors"
      [x_block, .field 0, x_t, x_lps, .field (nP : F), .field (nIdx : F), x_pw,
        .field (n : F), .field ((if large then 1 else 0 : Nat) : F),
        .field ((0 : Nat) : F), v277, .field ((if true then 1 else 0 : Nat) : F)]
      m278 v387 m388 cs398 := by
    simpa using ev400
  obtain ⟨minors, hmin_eq, hmin_tm⟩ :=
    nat_minors_spec hT hκ_inj (by omega) hwf_all n 0 (by omega)
      hload_min hgood_min hbnd_min
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_278 hb₀)
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_278 hbT)
      (RepKLevelList.mono hlps ext_h_278)
      (repKLevel_heapMono₂ ext_h_278 hpw)
      hinner_tm ev400'
  simp only [↓reduceIte, List.drop_zero, Nat.add_zero] at hmin_eq hmin_tm
  have ext_388_528 : Heap.Extends m388 m528 := by rw [hm536]; exact Heap.Extends.snoc _ _
  have ext_h_528 := ext_h_278.trans (ev400.heap_extends.trans ext_388_528)
  have hlam_mot : Tm (keyOf c.t) 0 (fun _ => default) m528 (0 + nP)
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

/-- `KernelCheck::nat_check_rules` verifies each rule's field count `nF` and establishes
`WrapRelSem` between the generated rule RHS `structRecRhsR` and the declared rule RHS `rl.rhs`. -/
theorem nat_check_rules_spec {c : Ctx}
    {T recC : KKey} {b₀ bT bRec : Bytes.Address} {k nP nIdx : Nat}
    {large : Bool} {tty₀ motiveTy : KExpr}
    {tbs₀ : List (KExpr × Ix.Kernel.BinderMeta)} {tsort₀ : KExpr}
    {tbsP : List (KExpr × Ix.Kernel.BinderMeta)} {itele_pos : KExpr}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)}
    (hlf : LoadFacts c)
    (hT : keyOf c.t (ixAddr bT) = T)
    (hκ_inj : ∀ a : Bytes.Address, keyOf c.t (ixAddr a) = T → a = bT)
    (hRec : keyOf c.t (ixAddr bRec) = recC)
    (hnCtors_lt : ctors_info.length < 2147483648)
    (hnP_lt : nP < 2147483648)
    (hwf_all : ∀ info ∈ ctors_info,
      NatCtorInfoWf T k large nP nIdx ctors_info.length info)
    (hsT₀ : tty₀.stripPis (nP + nIdx) = some (tbs₀, tsort₀))
    (hsT_pos : (posOf (if large then k :: List.range k else List.range k) tty₀).stripPis nP =
      some (tbsP, itele_pos))
    (hmot_eq : cMotiveTyI T
      ((List.range k).map (fun idx => Level.param ((if large then 1 else 0) + idx)))
      (if large then Level.param 0 else Level.zero) nP nIdx itele_pos = some motiveTy) :
    ∀ {rls_tail : List (RecRule .anon)} (j : Nat)
      {x_rules x_block x_t x_lps x_pw x_tty x_motive_ty x_rec x_rlvls r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      j + rls_tail.length = ctors_info.length →
      RulesRep (keyOf c.t) h (if large then k :: List.range k else List.range k) j x_rules rls_tail →
      NatCtorLoad (keyOf c.t) b₀ k ctors_info x_block cs →
      Good c cs →
      IxVM.Consistency.Bounded cs →
      Bytes.RepAddressRef addrTy h b₀ x_block →
      Bytes.RepAddressRef addrTy h bT x_t →
      Bytes.RepAddressRef addrTy h bRec x_rec →
      RepKLevelList h
        ((List.range k).map (fun idx => Level.param ((if large then 1 else 0) + idx))) x_lps →
      RepKLevelList h
        ((List.range ((if large then k :: List.range k else List.range k).length)).map Level.param)
        x_rlvls →
      RepKLevel h (if large then Level.param 0 else Level.zero) x_pw →
      Tm (keyOf c.t) 0 (fun _ => default) h 0
        (posOf (if large then k :: List.range k else List.range k) tty₀) x_tty →
      Tm (keyOf c.t) 0 (fun _ => default) h nP motiveTy x_motive_ty →
      ObsFn W "KernelCheck::nat_check_rules"
        [x_rules, x_block, .field 0, x_t, x_lps, .field (nP : F), .field (nIdx : F), x_pw,
          .field (ctors_info.length : F),
          .field ((if large then 1 else 0 : Nat) : F),
          x_tty, x_motive_ty, x_rec, x_rlvls, .field (j : F)]
        h r h' cs →
      let rlps := if large then k :: List.range k else List.range k
      let elim := if large then k else 0
      let ctors₀ := ctors_info.map (fun info => (info.1, info.2.1, info.2.2.2.1, info.2.2.2.2))
      ∀ idx (hlt : idx < rls_tail.length) (hj_idx : j + idx < ctors_info.length),
        (rls_tail[idx]'hlt).nfields = (ctors_info[j + idx]'hj_idx).2.1 ∧
        ∃ rhsG,
          Ix.Kernel.structRecRhsR T (List.range k) elim large nP nIdx tty₀ ctors₀
            recC (rlps.map .param) (j + idx) = some rhsG ∧
          WrapRelSem c.env.find? rhsG (rls_tail[idx]'hlt).rhs := by
  intro rls_tail
  induction rls_tail with
  | nil =>
    intro j x_rules x_block x_t x_lps x_pw x_tty x_motive_ty x_rec x_rlvls r h h' cs
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ idx hlt
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
        -- Step 1: constructor `j` field count from `NatCtorLoad`
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
        have hload_rhs : NatCtorLoad (keyOf c.t) b₀ k ctors_info x_block cs_rhs :=
          hload.mono_calls (fun x hx => by simp [hx])
        have hgood_rhs : Good c cs_rhs := hgood.sub (fun x hx => by simp [hx])
        have hbnd_rhs : IxVM.Consistency.Bounded cs_rhs :=
          RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
        obtain ⟨rhs_c, hrhs_c, hrhs_c_tm⟩ :=
          nat_rule_rhs_spec hT hκ_inj hRec hnCtors_lt hnP_lt hj hwf_all hsT_pos hmot_eq
            hload_rhs hgood_rhs hbnd_rhs
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
        have hrhs_decl_tm : Tm (keyOf c.t) 0 (fun _ => default) m244 0 (posOf rlps rl.rhs) x_rhs :=
          (hrhs_tmC 0 (fun _ => default)).mono ext_h_244
        have hwrap_pos := wrap_rel_spec hlf hgood_wrap hrhs_c_tm hrhs_decl_tm ev_wrap
        have hwrap_j : WrapRelSem c.env.find? rhsG rl.rhs :=
          WrapRelSem.of_posOf_perm (rlps_perm k large) hwrap_pos
        -- Step 3: recursive tail `rls_rest` at `j + 1`
        rw [evalBinOp_add_one j op_j1] at ev_rec
        have ext_h_230 := ext_h_244.trans ev_wrap.heap_extends
        have hload_rec : NatCtorLoad (keyOf c.t) b₀ k ctors_info x_block cs_rec :=
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
        intro _ _ _ idx hlt hj_idx
        cases idx with
        | zero =>
          simp only [List.getElem_cons_zero, Nat.add_zero]
          exact ⟨hnf_val, rhsG, hrhsG, hwrap_j⟩
        | succ idx' =>
          have hlt' : idx' < rls_rest.length := Nat.lt_of_succ_lt_succ hlt
          have hj_idx' : (j + 1) + idx' < ctors_info.length := by omega
          obtain ⟨hnf', rhsG', hrhsG', hwrap'⟩ := htail idx' hlt' hj_idx'
          have hadd : j + (idx' + 1) = (j + 1) + idx' := by omega
          simp only [List.getElem_cons_succ, hadd]
          exact ⟨hnf', rhsG', hrhsG', hwrap'⟩

/-- Heap witness that `p` is a literal `"App"`-spine over a literal `"Const" [ap, lsp]` cell
representing address `a` and exact level list `ls`. -/
inductive AppHeadConstLvls (h : Heap F) (a : Bytes.Address) (ls : List KLevel) :
    SourceValue F → Prop where
  | const {addr : Nat} {ap lsp : SourceValue F}
      (cell : h[addr]? = some (.construct kexprEnum "Const" [ap, lsp]))
      (ra : Bytes.RepAddressRef addrTy h a ap)
      (rls : RepKLevelList h ls lsp) :
      AppHeadConstLvls h a ls (.ptr (.enum kexprEnum) addr)
  | app {addr : Nat} {fp ap : SourceValue F}
      (cell : h[addr]? = some (.construct kexprEnum "App" [fp, ap]))
      (rf : AppHeadConstLvls h a ls fp) :
      AppHeadConstLvls h a ls (.ptr (.enum kexprEnum) addr)

theorem AppHeadConstLvls.mono {h₁ h₂ : Heap F} {a : Bytes.Address} {ls : List KLevel}
    {p : SourceValue F} (ext : Heap.Extends h₁ h₂) (hp : AppHeadConstLvls h₁ a ls p) :
    AppHeadConstLvls h₂ a ls p := by
  induction hp with
  | const cell ra rls =>
    exact .const (ext.getElem?_eq cell)
      (Bytes.repAddressRef_heapMono₂ addrTy ext ra) (rls.mono ext)
  | app cell _ ih =>
    exact .app (ext.getElem?_eq cell) ih

/-- Heap witness on the generated left-hand side of `wrap_rel` that `p` starts with `m` literal
`"Forall"` cells followed by `"Forall" [xd, xb, xm]` whose domain `xd` represents `dom` at depth `k`
with `dom.getAppFn = .const T ls` and `AppHeadConstLvls h a ls xd`. -/
inductive ForallDomHeadLvls (κ : _root_.Address → KKey) (d : Nat) (Γ : Nat → KExpr)
    (h : Heap F) (T : KKey) (a : Bytes.Address) (ls : List KLevel) :
    Nat → Nat → SourceValue F → Prop where
  | zero {k addr : Nat} {xd xb xm : SourceValue F} {dom : KExpr}
      (cell : h[addr]? = some (.construct kexprEnum "Forall" [xd, xb, xm]))
      (hdom : Tm κ d Γ h k dom xd)
      (hfn : dom.getAppFn = .const T ls)
      (hhead : AppHeadConstLvls h a ls xd) :
      ForallDomHeadLvls κ d Γ h T a ls 0 k (.ptr (.enum kexprEnum) addr)
  | succ {m k addr : Nat} {xt xb xm : SourceValue F}
      (cell : h[addr]? = some (.construct kexprEnum "Forall" [xt, xb, xm]))
      (hrest : ForallDomHeadLvls κ d Γ h T a ls m (k + 1) xb) :
      ForallDomHeadLvls κ d Γ h T a ls (m + 1) k (.ptr (.enum kexprEnum) addr)

theorem ForallDomHeadLvls.mono {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h₁ h₂ : Heap F} {T : KKey} {a : Bytes.Address} {ls : List KLevel}
    {m k : Nat} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hp : ForallDomHeadLvls κ d Γ h₁ T a ls m k p) :
    ForallDomHeadLvls κ d Γ h₂ T a ls m k p := by
  induction hp with
  | zero cell hdom hfn hhead =>
    exact .zero (ext.getElem?_eq cell) (hdom.mono ext) hfn (hhead.mono ext)
  | succ cell _ ih =>
    exact .succ (ext.getElem?_eq cell) ih

/-- Pure heap witness on the declared right-hand side of `wrap_rel` (certified by
`rec_to_parent_addr`) that `p` starts with `m` literal `"Forall"` cells followed by
`"Forall" [xd, xb, xm]` with `AppHeadConstLvls h a ls xd`. -/
inductive ForallRightHeadLvls (h : Heap F) (a : Bytes.Address) (ls : List KLevel) :
    Nat → SourceValue F → Prop where
  | zero {addr : Nat} {xd xb xm : SourceValue F}
      (cell : h[addr]? = some (.construct kexprEnum "Forall" [xd, xb, xm]))
      (hhead : AppHeadConstLvls h a ls xd) :
      ForallRightHeadLvls h a ls 0 (.ptr (.enum kexprEnum) addr)
  | succ {m addr : Nat} {xt xb xm : SourceValue F}
      (cell : h[addr]? = some (.construct kexprEnum "Forall" [xt, xb, xm]))
      (hrest : ForallRightHeadLvls h a ls m xb) :
      ForallRightHeadLvls h a ls (m + 1) (.ptr (.enum kexprEnum) addr)

theorem ForallRightHeadLvls.mono {h₁ h₂ : Heap F} {a : Bytes.Address} {ls : List KLevel}
    {m : Nat} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hp : ForallRightHeadLvls h₁ a ls m p) :
    ForallRightHeadLvls h₂ a ls m p := by
  induction hp with
  | zero cell hhead => exact .zero (ext.getElem?_eq cell) (hhead.mono ext)
  | succ cell _ ih => exact .succ (ext.getElem?_eq cell) ih

private theorem getAppFn_mkAppN_eq : ∀ (As : List KExpr) (f : KExpr),
    (Expr.mkAppN f As).getAppFn = f.getAppFn
  | [], _ => rfl
  | a :: As, f => by
    show (Expr.mkAppN (.app f a) As).getAppFn = f.getAppFn
    rw [getAppFn_mkAppN_eq As (.app f a)]
    rfl

private theorem nat_app_n_head {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {k : Nat} :
    ∀ {Args : List KExpr} {a : Bytes.Address} {ls : List KLevel} {pf pargs r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      AppHeadConstLvls h a ls pf →
      RepList kexprListEnum (fun h E p => Tm κ d Γ h k E p) h Args pargs →
      ObsFn W "KernelCheck::nat_app_n" [pf, pargs] h r h' cs →
      AppHeadConstLvls h' a ls r := by
  intro Args
  induction Args with
  | nil =>
    intro a ls pf pargs r h h' cs hf hargs ev
    match Obs.«KernelCheck::nat_app_n».obs ev with
    | .Nil (he21 := hr) (he22 := hh) .. =>
      subst hr hh; exact hf
    | .Cons (ld12 := ld12) .. =>
      have ld12' : loadValue h pargs = .ok (.construct kexprListEnum "Cons" [_, _]) := ld12
      cases hargs with | nil cell => exact (load_cell_ne cell ld12' (by decide)).elim
  | cons _ _ ih =>
    intro a ls pf pargs r h h' cs hf hargs ev
    match Obs.«KernelCheck::nat_app_n».obs ev with
    | .Nil (ld12 := ld12) .. =>
      have ld12' : loadValue h pargs = .ok (.construct kexprListEnum "Nil" []) := ld12
      cases hargs with | cons cell _ _ => exact (load_cell_ne cell ld12' (by decide)).elim
    | .Cons (m50 := m50) (ld12 := ld12) (hm58 := hm58) (ev46 := ev46) .. =>
      obtain ⟨_, _, heq, _, has⟩ := RepList.cons_of_load hargs ld12
      injection heq with h1 h2; subst h1 h2
      have ext50 : Heap.Extends h m50 := by rw [hm58]; exact Heap.Extends.snoc _ _
      have happ : AppHeadConstLvls m50 a ls (.ptr (.enum kexprEnum) h.length) := by
        rw [hm58]
        exact .app (by simp; rfl) (hf.mono (Heap.Extends.snoc _ _))
      exact ih happ (tmRepList_mono ext50 has) ev46

private theorem forallDomHeadLvls_replace_pis
    {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {T : KKey} {a : Bytes.Address} {ls : List KLevel} {m : Nat} :
    ∀ (cnt : Nat) {k : Nat} {tele : KExpr} {ppw ptele pb r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      cnt < 2147483648 →
      Tm κ d Γ h k tele ptele →
      ForallDomHeadLvls κ d Γ h T a ls m (k + cnt) pb →
      ObsFn W "KernelCheck::nat_replace_pis"
        [ppw, .field (cnt : F), ptele, pb, .field 0] h r h' cs →
      ForallDomHeadLvls κ d Γ h' T a ls (cnt + m) k r
  | 0, k, _, _, _, _, _, _, _, _, _, _, hpb, ev => by
    match Obs.«KernelCheck::nat_replace_pis».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh
      simpa [Nat.zero_add] using hpb
    | .other_n0 (hne19 := hne) .. => exact (hne rfl).elim
    | .other_other (hne19 := hne) .. => exact (hne rfl).elim
  | cnt + 1, k, tele, ppw, ptele, pb, r, h, h', cs, hcnt, htele, hpb, ev => by
    have hne0 : (.field ((cnt + 1 : Nat) : F) : SourceValue F) ≠ .field 0 :=
      succ_field_ne_zero (by omega)
    match Obs.«KernelCheck::nat_replace_pis».obs ev with
    | .n0 (hv14 := hv) .. =>
      exact absurd hv hne0
    | .other_other (hne163 := hne) .. =>
      exact (hne rfl).elim
    | .other_n0 (x_ty := xty) (v54 := v54) (m55 := m55) (ld33 := ld) (op93 := op) (ev67 := ev')
        (he134 := hr) (hm133 := hm) .. =>
      subst hr hm
      obtain ⟨_, B, _, rfl, _, hb, _⟩ := htele.forallE_of_load ld
      rw [evalBinOp_sub_succ cnt op] at ev'
      have hpb' : ForallDomHeadLvls κ d Γ h T a ls m ((k + 1) + cnt) pb := by
        rwa [show (k + 1) + cnt = k + (cnt + 1) by omega]
      have ih_out := forallDomHeadLvls_replace_pis cnt (by omega) hb hpb' ev'
      have hsucc :
          ForallDomHeadLvls κ d Γ
            (m55 ++ [.construct kexprEnum "Forall" [xty, v54, ppw]])
            T a ls ((cnt + m) + 1) k (.ptr (.enum kexprEnum) m55.length) :=
        .succ (by simp; exact ⟨rfl, rfl⟩) (ih_out.mono (Heap.Extends.snoc _ _))
      rwa [show (cnt + 1) + m = (cnt + m) + 1 by omega]

private theorem forallDomHeadLvls_nat_minors
    {c : Ctx} {T : KKey} {bT : Bytes.Address} {nP nIdx m : Nat} {large : Bool}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)}
    {ls : List KLevel}
    (hnCtors_lt : ctors_info.length < 2147483648) :
    ∀ (rem j : Nat) {x_block x_t x_lps x_pw x_body r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      j + rem = ctors_info.length →
      ForallDomHeadLvls (keyOf c.t) 0 (fun _ => default) h
        T bT ls m (nP + 1 + ctors_info.length) x_body →
      ObsFn W "KernelCheck::nat_minors"
        [x_block, .field 0, x_t, x_lps, .field (nP : F), .field (nIdx : F), x_pw,
          .field (ctors_info.length : F),
          .field ((if large then 1 else 0 : Nat) : F),
          .field (j : F), x_body, .field 0]
        h r h' cs →
      ForallDomHeadLvls (keyOf c.t) 0 (fun _ => default) h' T bT ls (rem + m) (nP + j + 1) r
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
        ZMod.val_natCast_of_lt (Nat.lt_trans (by omega : ctors_info.length - j < 4294967296) (by decide))
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
      have ih_out := forallDomHeadLvls_nat_minors hnCtors_lt rem (j + 1) (by omega)
        (hbody.mono ext_h_129) ev_rec
      have ih_out' :
          ForallDomHeadLvls (keyOf c.t) 0 (fun _ => default) m244
            T bT ls (rem + m) ((nP + j + 1) + 1) v243 := by
        rwa [show (nP + j + 1) + 1 = nP + (j + 1) + 1 by omega]
      have hsucc :
          ForallDomHeadLvls (keyOf c.t) 0 (fun _ => default)
            (m244 ++ [.construct kexprEnum "Forall" [v128, v243, x_pw]])
            T bT ls ((rem + m) + 1) (nP + j + 1) (.ptr (.enum kexprEnum) m244.length) :=
        .succ (by simp; exact ⟨rfl, rfl⟩) (ih_out'.mono (Heap.Extends.snoc _ _))
      rwa [show (rem + 1) + m = (rem + m) + 1 by omega]

private theorem wrap_rel_appHeadConstLvls {a_g a_d : Bytes.Address} {ls_g ls_d : List KLevel} :
    ∀ {xg xd : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      AppHeadConstLvls h a_g ls_g xg →
      AppHeadConstLvls h a_d ls_d xd →
      ObsFn W "KernelCheck::wrap_rel" [xg, xd] h (.field 1) h' cs →
      ls_g = ls_d := by
  intro xg xd h h' cs hg hd ev
  induction hg generalizing xd h' cs with
  | const cell_g _ rls_g =>
    match Obs.«KernelCheck::wrap_rel».obs ev with
    | .other_other_App_App_other (he301 := he) ..
    | .other_other_App_other (he308 := he) ..
    | .other_other_Lam_other (he426 := he) ..
    | .other_other_Forall_other (he544 := he) ..
    | .other_other_Proj_Proj_other (he696 := he) ..
    | .other_other_Proj_other (he703 := he) .. =>
      exact absurd (Value.field.inj he) one_ne_zero
    | .Let (ld12 := ld) ..
    | .other_other_App_App_n1 (ld192 := ld) ..
    | .other_other_Lam_Lam (ld192 := ld) ..
    | .other_other_Forall_Forall (ld192 := ld) ..
    | .other_other_Proj_Proj_n1 (ld192 := ld) .. =>
      exact (load_cell_ne cell_g ld (by decide)).elim
    | .other_Let (ld102 := ld) .. =>
      cases hd with
      | const cell_d _ _ | app cell_d _ =>
        exact (load_cell_ne cell_d ld (by decide)).elim
    | .other_other_other (ev715 := ev715) .. =>
      rcases Obs.«KernelCheck::kexpr_struct_eq».obs ev715 with
        ⟨_, _, ld12, _, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, ld12, _, _, _⟩ |
        ⟨_, _, _, _, _, he, _, _⟩ |
        ⟨x_ca, x_lsa, x_cb, x_lsb, m202, _, _, ld12, ld183, ev215, ev241, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, _, ld12, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, _, ld12, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, _, ld12, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, ld12, _, _, _⟩ |
        ⟨_, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, _, he, _, _⟩
      all_goals try exact absurd (Value.field.inj he) one_ne_zero
      all_goals try exact (load_cell_ne cell_g ld12 (by decide)).elim
      · obtain ⟨-, hxs1⟩ := load_cell cell_g ld12
        injection hxs1 with _ hxs1
        injection hxs1 with hlsa
        rw [hlsa] at rls_g
        cases hd with
        | app cell_d _ => exact (load_cell_ne cell_d ld183 (by decide)).elim
        | const cell_d _ rls_d =>
          obtain ⟨-, hxs2⟩ := load_cell cell_d ld183
          injection hxs2 with _ hxs2
          injection hxs2 with hlsb
          rw [hlsb] at rls_d
          exact (level_list_struct_eq_one
            (rls_g.mono ev215.heap_extends) (rls_d.mono ev215.heap_extends) ev241).1
  | app cell_g rf_g ih =>
    match Obs.«KernelCheck::wrap_rel».obs ev with
    | .other_other_App_App_other (he301 := he) ..
    | .other_other_App_other (he308 := he) ..
    | .other_other_Lam_other (he426 := he) ..
    | .other_other_Forall_other (he544 := he) ..
    | .other_other_Proj_Proj_other (he696 := he) ..
    | .other_other_Proj_other (he703 := he) .. =>
      exact absurd (Value.field.inj he) one_ne_zero
    | .Let (ld12 := ld) ..
    | .other_other_Lam_Lam (ld192 := ld) ..
    | .other_other_Forall_Forall (ld192 := ld) ..
    | .other_other_Proj_Proj_n1 (ld192 := ld) .. =>
      exact (load_cell_ne cell_g ld (by decide)).elim
    | .other_Let (ld102 := ld) .. =>
      cases hd with
      | const cell_d _ _ | app cell_d _ =>
        exact (load_cell_ne cell_d ld (by decide)).elim
    | .other_other_other (ld192 := ld192) (hne311 := hne311) .. =>
      rw [loadValue_enum_cell cell_g] at ld192
      injection ld192 with hv
      exact (hne311 [_, _] rfl hv.symm).elim
    | .other_other_App_App_n1 (ld192 := ld192) (ld221 := ld221) (ev253 := ev253) .. =>
      obtain ⟨-, hxs1⟩ := load_cell cell_g ld192
      injection hxs1 with hfg _
      cases hd with
      | const cell_d _ _ => exact (load_cell_ne cell_d ld221 (by decide)).elim
      | app cell_d rf_d =>
        obtain ⟨-, hxs2⟩ := load_cell cell_d ld221
        injection hxs2 with hfd _
        rw [← hfg, ← hfd] at ev253
        exact ih rf_d ev253

private theorem wrap_rel_forallDomHeadLvls
    {c : Ctx} {T : KKey} {a_g a_d : Bytes.Address} {ls_g ls_d : List KLevel}
    (hlf : LoadFacts c)
    (hT_ind : ∃ cv caps, c.env.find? T = some (.indInfo cv caps)) :
    ∀ (m : Nat) {k : Nat} {xg xd : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      Good c cs →
      ForallDomHeadLvls (keyOf c.t) 0 (fun _ => default) h T a_g ls_g m k xg →
      ForallRightHeadLvls h a_d ls_d m xd →
      ObsFn W "KernelCheck::wrap_rel" [xg, xd] h (.field 1) h' cs →
      ls_g = ls_d
  | 0, k, xg, xd, h, h', cs, hgood, hg, hd, ev => by
    cases hg with
    | @zero _ _ _ _ _ dom cell_g hdom hfn hhead_g =>
      cases hd with
      | zero cell_d hhead_d =>
        match Obs.«KernelCheck::wrap_rel».obs ev with
        | .other_other_App_App_other (he301 := he) ..
        | .other_other_App_other (he308 := he) ..
        | .other_other_Lam_other (he426 := he) ..
        | .other_other_Forall_other (he544 := he) ..
        | .other_other_Proj_Proj_other (he696 := he) ..
        | .other_other_Proj_other (he703 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .Let (ld12 := ld) ..
        | .other_other_App_App_n1 (ld192 := ld) ..
        | .other_other_Lam_Lam (ld192 := ld) ..
        | .other_other_Proj_Proj_n1 (ld192 := ld) .. =>
          exact (load_cell_ne cell_g ld (by decide)).elim
        | .other_Let (ld102 := ld) .. =>
          exact (load_cell_ne cell_d ld (by decide)).elim
        | .other_other_other (ld192 := ld192) (hne547 := hne547) .. =>
          rw [loadValue_enum_cell cell_g] at ld192
          injection ld192 with hv
          exact (hne547 [_, _, _] rfl hv.symm).elim
        | .other_other_Forall_Forall (ld192 := ld192) (ld462 := ld462)
            (ev490 := ev490) (hc539 := hc539) .. =>
          obtain ⟨-, hxs1⟩ := load_cell cell_g ld192
          injection hxs1 with htg _
          obtain ⟨-, hxs2⟩ := load_cell cell_d ld462
          injection hxs2 with htd _
          rw [htg] at hdom hhead_g
          rw [htd] at hhead_d
          match Obs.«KernelCheck::wrap_binder».obs ev490 with
          | .n1_other (he98 := he) .. | .other (he105 := he) .. =>
            exact absurd (Value.field.inj he) one_ne_zero
          | .n1_n1 (m2 := m2) (cs48 := cs48) (ev15 := ev15) (ev50 := ev50) (hc93 := hc93) .. =>
            have e1 := ev15.heap_extends
            match Obs.«KernelCheck::wrap_dom».obsx ev50 with
            | .other_other_other (he200 := he) .. =>
              exact absurd (Value.field.inj he) one_ne_zero
            | .Let (ld12 := ld12) .. =>
              cases hhead_g with
              | const cg _ _ | app cg _ =>
                exact (load_cell_ne (e1.getElem?_eq cg) ld12 (by decide)).elim
            | .other_n1 (ev105 := ev105) .. =>
              exact wrap_rel_appHeadConstLvls (hhead_g.mono e1) (hhead_d.mono e1) ev105
            | .other_other_n1_bind (m92 := m92) (cs145 := cs145)
                (ev105 := ev105) (ev147 := ev147) (hc196 := hc196) .. =>
              have hgood_cw : Good c cs145 :=
                hgood.sub (fun z hz => by subst hc539 hc93 hc196; simp [hz])
              match Obs.«KernelCheck::consume_wrapper».obsx ev147 with
              | .Const_Cons_Defn_n1_bind_other (he276 := he) ..
              | .Const_Cons_Defn_other (he299 := he) ..
              | .Const_Cons_other (he323 := he) ..
              | .Const_other (he347 := he) ..
              | .other (he371 := he) .. =>
                injection he with hxs; injection hxs with h10 _
                exact absurd (Value.field.inj h10) one_ne_zero
              | .Const_Cons_Defn_n1_bind_n0 (m2 := mc2) (cs12 := cs12)
                  (x_w := xw) (m96 := m96) (p104 := p104) (cs110 := cs110)
                  (ev14 := ev14) (ld47 := ld47) (ev112 := ev112) (ld106 := ld106)
                  (hc267 := hc267) .. =>
                have hbnd_sp : IxVM.Consistency.Bounded cs12 :=
                  RomBound.bounded_mono hgood_cw.2 (fun z hz => by subst hc267; simp [hz])
                have hdom_92 : Tm c.κ 0 (fun _ => default) m92 k dom _ :=
                  (hdom.mono e1).mono ev105.heap_extends
                obtain ⟨hd_sp, sp, H, As, hpair, hH, _, heq_dom⟩ :=
                  SubstAux.gall c.κ .collect_spine _ _ _ _ _ ev14 _ rfl hbnd_sp
                    0 (fun _ => default) k dom hdom_92
                injection hpair with hlist; injection hlist with hhd _
                subst hhd
                obtain ⟨aw, us, rfl, haw, _, _, _⟩ := hH.const_of_load ld47
                have hg_ci : Good c cs110 :=
                  hgood_cw.sub (fun z hz => by subst hc267; simp [hz])
                obtain ⟨ci, hfind, p_v, hp_ld, hci_rep⟩ :=
                  hlf.getCI xw p104 mc2 m96 cs110 aw ev112 hg_ci haw
                rw [hp_ld] at ld106
                injection ld106 with hv_eq; subst hv_eq
                obtain ⟨_, _, _, rfl, _, _⟩ := CIRep.defn_inv hci_rep
                rw [heq_dom, getAppFn_mkAppN_eq] at hfn
                injection hfn with hkey_eq _
                rw [hkey_eq] at hfind
                obtain ⟨_, _, hfind_ind⟩ := hT_ind
                rw [hfind] at hfind_ind
                cases hfind_ind
  | m + 1, k, xg, xd, h, h', cs, hgood, hg, hd, ev => by
    cases hg with
    | succ cell_g hrest_g =>
      cases hd with
      | succ cell_d hrest_d =>
        match Obs.«KernelCheck::wrap_rel».obs ev with
        | .other_other_App_App_other (he301 := he) ..
        | .other_other_App_other (he308 := he) ..
        | .other_other_Lam_other (he426 := he) ..
        | .other_other_Forall_other (he544 := he) ..
        | .other_other_Proj_Proj_other (he696 := he) ..
        | .other_other_Proj_other (he703 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .Let (ld12 := ld) ..
        | .other_other_App_App_n1 (ld192 := ld) ..
        | .other_other_Lam_Lam (ld192 := ld) ..
        | .other_other_Proj_Proj_n1 (ld192 := ld) .. =>
          exact (load_cell_ne cell_g ld (by decide)).elim
        | .other_Let (ld102 := ld) .. =>
          exact (load_cell_ne cell_d ld (by decide)).elim
        | .other_other_other (ld192 := ld192) (hne547 := hne547) .. =>
          rw [loadValue_enum_cell cell_g] at ld192
          injection ld192 with hv
          exact (hne547 [_, _, _] rfl hv.symm).elim
        | .other_other_Forall_Forall (ld192 := ld192) (ld462 := ld462)
            (ev490 := ev490) (hc539 := hc539) .. =>
          obtain ⟨-, hxs1⟩ := load_cell cell_g ld192
          injection hxs1 with _ hxs1; injection hxs1 with hbg _
          obtain ⟨-, hxs2⟩ := load_cell cell_d ld462
          injection hxs2 with _ hxs2; injection hxs2 with hbd _
          rw [hbg] at hrest_g
          rw [hbd] at hrest_d
          match Obs.«KernelCheck::wrap_binder».obs ev490 with
          | .n1_other (he98 := he) .. | .other (he105 := he) .. =>
            exact absurd (Value.field.inj he) one_ne_zero
          | .n1_n1 (ev15 := ev15) (ev50 := ev50) (cs74 := cs74) (ev76 := ev76) (hc93 := hc93) .. =>
            have e12 := ev15.heap_extends.trans ev50.heap_extends
            have hgood76 : Good c cs74 :=
              hgood.sub (fun z hz => by subst hc539 hc93; simp [hz])
            exact wrap_rel_forallDomHeadLvls hlf hT_ind m hgood76
              (hrest_g.mono e12) (hrest_d.mono e12) ev76


/-- `KernelCheck::nat_rec_check` verifies the recursor's level count, motive/minor counts,
canonical generated recursor type `structRecTyR` up to `WrapRelSem`, and all constructor
computation rules `structRecRhsR` up to `WrapRelSem` on a 2-member block `[.indc ind, .recr rec_m]`
whose former raw type has `nP + nIdx` syntactic outer `∀`-binders. -/
theorem nat_rec_check_spec {c : Ctx} (hc : CoreFacts c)
    {cst : Ixon.Constant} {ind : Ixon.Inductive} {rec_m : Ixon.Recursor}
    {T recC : KKey} {b₀ bT bRec : Bytes.Address} {k nP nIdx : Nat} {large : Bool}
    {R_tty₀ tty₀ rec_ty₀ : KExpr}
    {rbs₀ tbs₀ : List (KExpr × Ix.Kernel.BinderMeta)} {rbody₀ tsort₀ : KExpr}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)}
    {rls : List (RecRule .anon)}
    {x_rc x_nlvls x_ty x_n_mot x_n_min x_rules w_k w_u x_rec_blk w_ridx : SourceValue F}
    {x_pty w_p1 w_p2 w_pu x_block : SourceValue F}
    {x_addr x_parent_addr r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hlf : LoadFacts c)
    (hT_ind : ∃ cv caps, c.env.find? T = some (.indInfo cv caps))
    (hrec_at : Ix.Cert.recordAt c.E (ixAddr b₀) = some cst)
    (hcst_info : cst.info = .muts #[.indc ind, .recr rec_m])
    (hbRec_addr : ixAddr bRec = rprjAddr (ixAddr b₀) 1)
    (hT : keyOf c.t (ixAddr bT) = T)
    (hκ_inj : ∀ a : Bytes.Address, keyOf c.t (ixAddr a) = T → a = bT)
    (hRec : keyOf c.t (ixAddr bRec) = recC)
    (hk_lt : k < 2147483648)
    (hnP_lt : nP < 2147483648)
    (hnIdx_lt : nIdx < 2147483648)
    (hnCtors_lt : ctors_info.length < 2147483648)
    (hnall_lt : nP + 1 + ctors_info.length + nIdx + 1 < 4294967296)
    (hlps_R_tty : R_tty₀.allLevelParamsDefined (List.range k) = true)
    (hlps_tty : tty₀.allLevelParamsDefined (List.range k) = true)
    (hsR_tty₀ : R_tty₀.stripPis (nP + nIdx) = some (rbs₀, rbody₀))
    (hsT₀ : tty₀.stripPis (nP + nIdx) = some (tbs₀, tsort₀))
    (hwf_all : ∀ info ∈ ctors_info,
      NatCtorInfoWf T k large nP nIdx ctors_info.length info)
    (hrls_len : rls.length = ctors_info.length)
    (hload : NatCtorLoad (keyOf c.t) b₀ k ctors_info x_block cs)
    (hgood : Good c cs)
    (hbnd : IxVM.Consistency.Bounded cs)
    (hb₀_blk : Bytes.RepAddressRef addrTy h b₀ x_block)
    (hb₀_rec_blk : Bytes.RepAddressRef addrTy h b₀ x_rec_blk)
    (hbT : Bytes.RepAddressRef addrTy h bT x_parent_addr)
    (hbRec : Bytes.RepAddressRef addrTy h bRec x_addr)
    (hpty : RawTm (keyOf c.t) 0 (fun _ => default) h 0
      (posOf (List.range k) R_tty₀) (posOf (List.range k) tty₀) x_pty)
    (hrec_ty : Tm (keyOf c.t) 0 (fun _ => default) h 0
      (posOf (if large then k :: List.range k else List.range k) rec_ty₀) x_ty)
    (hrules : RulesRep (keyOf c.t) h
      (if large then k :: List.range k else List.range k) 0 x_rules rls)
    (ev : ObsFn W "KernelCheck::nat_rec_check"
      [x_rc,
        .construct kciEnum "Rec"
          [x_nlvls, x_ty, .field (nP : F), .field (nIdx : F), x_n_mot, x_n_min,
            x_rules, w_k, w_u, x_rec_blk, w_ridx],
        x_addr,
        .construct kciEnum "Induct"
          [.field (k : F), x_pty, w_p1, w_p2, .field (ctors_info.length : F),
            w_pu, x_block, .field 0],
        x_parent_addr,
        .field ((if large then 1 else 0 : Nat) : F)]
      h r h' cs) :
    let rlps := if large then k :: List.range k else List.range k
    let elim := if large then k else 0
    let ctors₀ := ctors_info.map (fun info => (info.1, info.2.1, info.2.2.2.1, info.2.2.2.2))
    x_nlvls = .field (rlps.length : F) ∧
    x_n_mot = .field 1 ∧
    x_n_min = .field (ctors_info.length : F) ∧
    (∃ recTy,
      Ix.Kernel.structRecTyR T (List.range k) elim large nP nIdx tty₀ ctors₀ = some recTy ∧
      WrapRelSem c.env.find? recTy rec_ty₀) ∧
    (∀ a_d ls_d,
      ForallRightHeadLvls h a_d ls_d (nP + 1 + ctors_info.length + nIdx) x_ty →
      ls_d = (List.range k).map (fun idx => Level.param ((if large then 1 else 0) + idx))) ∧
    ∀ idx (hlt : idx < rls.length) (hidx : idx < ctors_info.length),
      (rls[idx]'hlt).nfields = (ctors_info[idx]'hidx).2.1 ∧
      ∃ rhsG,
        Ix.Kernel.structRecRhsR T (List.range k) elim large nP nIdx tty₀ ctors₀
          recC (rlps.map .param) idx = some rhsG ∧
        WrapRelSem c.env.find? rhsG (rls[idx]'hlt).rhs := by
  intro rlps elim ctors₀
  dsimp only [rlps, elim, ctors₀]
  let n := ctors_info.length
  let uoff := if large then 1 else 0
  let ℓ_c : KLevel := if large then Level.param 0 else Level.zero
  let rlps' := if large then k :: List.range k else List.range k
  let clvls := (List.range k).map (fun idx => Level.param (uoff + idx))
  have hrlps_len : k + uoff = rlps'.length := by
    dsimp only [uoff, rlps']
    cases large <;> simp
  rcases Obs.«KernelCheck::nat_rec_check».obs ev with
    ⟨x_nlvls', x_ty', x_n_p', x_n_i', x_n_mot', x_n_min', x_rules', w13, w14, x_rec_blk', w15,
      x_pnlvls', x_pty', w83, w84, x_num_ctors', w85, x_block', x_idx',
      v138, v218, m219, cs229, v298, m299, cs301, m308, m324, v381, m382, cs384,
      v390, m391, cs401, v406, m439, v451, m452, cs462, m482, v512, m513, cs523,
      v527, m536, cs544, v547, v548, m550, cs558, m578, cs586, v604, m605, cs615,
      m645, m668, v701, m702, cs712, v716, m725, cs733, v736, v737, m739, cs747,
      v750, x758, m784, cs792, v810, m811, cs821, v825, m827, v839, x846, m865, cs873,
      v876, m879, cs887, m906, v925, m926, cs936, v941, m959, cs967, v971, m1002,
      v1044, m1045, cs1055, v1152, m1153, cs1163, m1193, v1246, m1249, cs1257,
      v1283, m1284, cs1294, m1317, cs1345, v1361, m1455, cs1463,
      hv11, hv81, op159, heq162, heq189, heq217, ev231, sg306, hm318, hm332, sg389,
      op435, hm447, ev403, ev464, hm492, ev560, ev588, ev546, ev525, hm653, hm676, ev617,
      op773, op765, ev749, ev794, ev735, ev714, hm835, op861, op853, ev889, hm914, ev875, ev823,
      op993, ev969, hm1010, ev938, ev1057, hm1201, ev1165, ev1259, heq1282,
      hm1325, ev1296, ev1465, ev1347, hc⟩
  subst hc
  -- Unify `Rec` and `Induct` constructor fields
  injection hv11 with _ _ hr_args
  injection hr_args with h1 hr_args; injection hr_args with h2 hr_args
  injection hr_args with h3 hr_args; injection hr_args with h4 hr_args
  injection hr_args with h5 hr_args; injection hr_args with h6 hr_args
  injection hr_args with h7 hr_args; injection hr_args with _ hr_args
  injection hr_args with _ hr_args; injection hr_args with h10 _
  subst h1 h2 h3 h4 h5 h6 h7 h10
  injection hv81 with _ _ hp_args
  injection hp_args with hp1 hp_args; injection hp_args with hp2 hp_args
  injection hp_args with _ hp_args; injection hp_args with _ hp_args
  injection hp_args with hp5 hp_args; injection hp_args with _ hp_args
  injection hp_args with hp7 hp_args; injection hp_args with hp8
  subst hp1 hp2 hp5 hp7 hp8
  -- Header equalities
  have hv138_eq : v138 = .field (rlps'.length : F) := by
    rw [evalBinOp_add_nat k uoff op159, hrlps_len]
  have hnlvls_eq : x_nlvls = .field (rlps'.length : F) := heq162.trans hv138_eq
  -- Step 1: `clvls`, `pw` (`Seg1`), `never = .succ .zero`, and `Seg2` (`v381`)
  have hlps_219 : RepKLevelList m219 clvls v218 :=
    nat_build_param_lvls_range_spec
      (by dsimp only [uoff]; cases large <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
        have := hk_lt <;> omega)
      ev231
  have hseg1 : RepKLevel m299 ℓ_c v298 ∧ Heap.Extends m219 m299 ∧ cs301 = [] := by
    cases sg306 with
    | n1 hv268 he273 hm272 hc284 =>
      subst he273 hm272 hc284
      have hl_true : large = true := by
        cases large with
        | true => rfl
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_zero] at hv268
          exact absurd (Value.field.inj hv268.symm) one_ne_zero
      subst hl_true
      exact ⟨(RepKLevel.allocParam m219 (by decide : 0 < 4294967296)).1,
        Heap.Extends.snoc _ _, rfl⟩
    | other hne285 he293 hm292 hc297 =>
      subst he293 hm292 hc297
      have hl_false : large = false := by
        cases large with
        | false => rfl
        | true => exact absurd rfl hne285
      subst hl_false
      exact ⟨(RepKLevel.allocZero m219).1, Heap.Extends.snoc _ _, rfl⟩
  rcases hseg1 with ⟨hpw_299, ext_219_299, hcs301⟩
  subst hcs301
  have ext_299_324 : Heap.Extends m299 m324 := by rw [hm332]; exact Heap.Extends.snoc _ _
  have ext_324_308 : Heap.Extends m324 m308 := by rw [hm318]; exact Heap.Extends.snoc _ _
  have hzero_324 : RepKLevel m324 .zero (.ptr (.enum "KernelTypes::KLevelNode") m299.length) := by
    rw [hm332]; exact (RepKLevel.allocZero m299).1
  have hnever_308 : RepKLevel m308 (.succ .zero)
      (.ptr (.enum "KernelTypes::KLevelNode") m324.length) := by
    rw [hm318]; exact (RepKLevel.allocSucc hzero_324).1
  have ext_h_308 := ev231.heap_extends.trans
    (ext_219_299.trans (ext_299_324.trans ext_324_308))
  have hseg2 : RawTm (keyOf c.t) 0 (fun _ => default) m382 0
      (posOf rlps' R_tty₀) (posOf rlps' tty₀) v381 ∧ Heap.Extends m308 m382 := by
    cases sg389 with
    | n0 hv349 he351 he352 hc353 =>
      subst he351 he352 hc353
      have hl_false : large = false := by
        cases large with
        | false => rfl
        | true =>
          simp only [↓reduceIte, Nat.cast_one] at hv349
          exact absurd (Value.field.inj hv349) one_ne_zero
      subst hl_false
      exact ⟨hpty.mono ext_h_308, Heap.Extends.refl _⟩
    | other cs_inst hne354 ev_inst hc_inst =>
      have hl_true : large = true := by
        cases large with
        | true => rfl
        | false => exact absurd rfl hne354
      subst hl_true
      have hbnd_inst : IxVM.Consistency.Bounded cs_inst :=
        RomBound.bounded_mono hbnd (fun x hx => by rw [hc_inst]; simp [hx])
      have hlps_308 := RepKLevelList.mono hlps_219
        (ext_219_299.trans (ext_299_324.trans ext_324_308))
      have hlv_rep : LvListRep m308 ((List.range k).map (fun idx => Level.param (1 + idx))) v218 :=
        ⟨_, hlps_308, LvEqList.refl _⟩
      have hinst := expr_inst_levels_rawTm hbnd_inst (hpty.mono ext_h_308) hlv_rep ev_inst
      simp only [List.length_map, List.length_range] at hinst
      dsimp only [rlps']
      simp only [↓reduceIte]
      rw [posOf_range, posOf_range, ← posOf_large_eq_inst_shifted k hlps_R_tty,
        ← posOf_large_eq_inst_shifted k hlps_tty] at hinst
      exact ⟨hinst, ev_inst.heap_extends⟩
  rcases hseg2 with ⟨hRaw_381, ext_308_382⟩
  -- Step 2: `nat_former_tele` (syntactic) + `peel_n_foralls`
  rw [evalBinOp_add_nat nP nIdx op435] at ev403
  have ext_382_439 : Heap.Extends m382 m439 := by rw [hm447]; exact Heap.Extends.snoc _ _
  have hsR_pos := ilp_stripPis rlps' (posLevels rlps') (nP + nIdx) hsR_tty₀
  change (posOf rlps' R_tty₀).stripPis (nP + nIdx) = _ at hsR_pos
  have hRaw_390 := nat_former_tele_syntactic_spec (nP + nIdx) (by omega) hsR_pos
    (hRaw_381.mono ext_382_439) ev403
  have htty_390 : Tm (keyOf c.t) 0 (fun _ => default) m391 0 (posOf rlps' tty₀) v390 := by
    simpa [Nat.zero_add] using hRaw_390.toTm
  obtain ⟨hm452_eq, _, tbsP, _, itele_pos, _, hsT_pos, hitele_raw⟩ :=
    peel_n_foralls_rawTm_spec nP (by omega) hRaw_390 ev464
  have hitele_tm : Tm (keyOf c.t) 0 (fun _ => default) m452 nP itele_pos v451 := by
    rw [hm452_eq]
    simpa [Nat.zero_add] using hitele_raw.toTm
  -- Step 3: `motive_ty` (`v604`)
  have ext_308_452 : Heap.Extends m308 m452 := by
    rw [hm452_eq]
    exact ext_308_382.trans (ext_382_439.trans ev403.heap_extends)
  have ext_452_482 : Heap.Extends m452 m482 := by rw [hm492]; exact Heap.Extends.snoc _ _
  have ext_h_482 := ext_h_308.trans (ext_308_452.trans ext_452_482)
  have hT_const1 : Tm (keyOf c.t) 0 (fun _ => default) m482 (nP + nIdx) (.const T clvls)
      (.ptr (.enum kexprEnum) m452.length) := by
    rw [← hT]
    exact .const (by rw [hm492]; simp)
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_482 hbT)
      (RepKLevelList.mono hlps_219
        (ext_219_299.trans (ext_299_324.trans (ext_324_308.trans (ext_308_452.trans ext_452_482)))))
      (LvEqList.refl _)
  have hps_m1 := nat_ps_at_spec (κ := keyOf c.t) (d := 0) (Γ := fun _ => default)
    nP nIdx (nP + nIdx) (by omega) (by omega) ev560
  have hps_m2 := nat_ps_at_spec (κ := keyOf c.t) (d := 0) (Γ := fun _ => default)
    nIdx 0 (nP + nIdx) (by omega) (by omega) ev588
  have hcat_m := kexpr_list_concat_spec' ev546 (tmRepList_mono ev588.heap_extends hps_m1) hps_m2
  have ext_482_536 := ev560.heap_extends.trans (ev588.heap_extends.trans ev546.heap_extends)
  have hfam_m := nat_app_n_spec (hT_const1.mono ext_482_536) hcat_m ev525
  have hfam_m' : Tm (keyOf c.t) 0 (fun _ => default) m513 (nP + nIdx)
      (cFamI T clvls nP nIdx 0 0) v512 := by
    simpa [cFamI] using hfam_m
  have ext_513_668 : Heap.Extends m513 m668 := by rw [hm676]; exact Heap.Extends.snoc _ _
  have ext_668_645 : Heap.Extends m668 m645 := by rw [hm653]; exact Heap.Extends.snoc _ _
  have ext_308_513 := ext_308_452.trans
    (ext_452_482.trans (ext_482_536.trans ev525.heap_extends))
  have ext_299_513 := ext_299_324.trans (ext_324_308.trans ext_308_513)
  have hsrt_668 : Tm (keyOf c.t) 0 (fun _ => default) m668 (nP + nIdx + 1) (.sort ℓ_c)
      (.ptr (.enum kexprEnum) m513.length) := by
    exact .sort (by rw [hm676]; simp)
      (repKLevel_heapMono₂ (ext_299_513.trans ext_513_668) hpw_299)
      (fun _ => rfl)
  have ext_308_645 := ext_308_513.trans (ext_513_668.trans ext_668_645)
  have hnever_645 := repKLevel_heapMono₂ ext_308_645 hnever_308
  have hmot_body_645 : Tm (keyOf c.t) 0 (fun _ => default) m645 (nP + nIdx)
      (.forallE (cFamI T clvls nP nIdx 0 0) (.sort ℓ_c) { pw := .never })
      (.ptr (.enum kexprEnum) m668.length) := by
    exact .forallE (by rw [hm653]; simp)
      (hfam_m'.mono (ext_513_668.trans ext_668_645))
      (hsrt_668.mono ext_668_645)
      hnever_645
  have ext_452_645 := ext_452_482.trans
    (ext_482_536.trans (ev525.heap_extends.trans (ext_513_668.trans ext_668_645)))
  obtain ⟨motiveTy, hmot_ite, hmot_tm⟩ :=
    nat_replace_pis_spec nIdx (by omega) hnever_645
      (hitele_tm.mono ext_452_645) hmot_body_645 ev617
  simp only [↓reduceIte] at hmot_ite
  have hmot_eq : cMotiveTyI T clvls ℓ_c nP nIdx itele_pos = some motiveTy := hmot_ite
  -- Step 4: `major` (`v925`)
  rw [evalBinOp_add_one n op773] at op765
  rw [evalBinOp_add_nat (n + 1) nIdx op765] at ev749
  have hps_j1 := nat_ps_at_spec (κ := keyOf c.t) (d := 0) (Γ := fun _ => default)
    nP (n + 1 + nIdx) (nP + (n + 1) + nIdx) (by omega) (by omega) ev749
  have hps_j2 := nat_ps_at_spec (κ := keyOf c.t) (d := 0) (Γ := fun _ => default)
    nIdx 0 (nP + (n + 1) + nIdx) (by omega) (by omega) ev794
  have hcat_j := kexpr_list_concat_spec' ev735 (tmRepList_mono ev794.heap_extends hps_j1) hps_j2
  have ext_482_725 := ext_482_536.trans (ev525.heap_extends.trans (ext_513_668.trans
    (ext_668_645.trans (ev617.heap_extends.trans (ev749.heap_extends.trans
      (ev794.heap_extends.trans ev735.heap_extends))))))
  have hT_const2 : Tm (keyOf c.t) 0 (fun _ => default) m725 (nP + (n + 1) + nIdx)
      (.const T clvls) (.ptr (.enum kexprEnum) m452.length) := by
    rw [← hT]
    exact .const (ext_482_725.getElem?_eq (by rw [hm492]; simp))
      (Bytes.repAddressRef_heapMono₂ addrTy (ext_h_482.trans ext_482_725) hbT)
      (RepKLevelList.mono hlps_219
        (ext_219_299.trans (ext_299_324.trans (ext_324_308.trans
          (ext_308_452.trans (ext_452_482.trans ext_482_725))))))
      (LvEqList.refl _)
  have hfam_j := nat_app_n_spec hT_const2 hcat_j ev714
  have hT_head2 : AppHeadConstLvls m725 bT clvls (.ptr (.enum kexprEnum) m452.length) :=
    .const (ext_482_725.getElem?_eq (by rw [hm492]; simp))
      (Bytes.repAddressRef_heapMono₂ addrTy (ext_h_482.trans ext_482_725) hbT)
      (RepKLevelList.mono hlps_219
        (ext_219_299.trans (ext_299_324.trans (ext_324_308.trans
          (ext_308_452.trans (ext_452_482.trans ext_482_725))))))
  have hfam_head := nat_app_n_head hT_head2 hcat_j ev714
  have hfam_j' : Tm (keyOf c.t) 0 (fun _ => default) m702 (nP + (n + 1) + nIdx)
      (cFamI T clvls nP nIdx (n + 1) 0) v701 := by
    simpa [cFamI] using hfam_j
  rw [evalBinOp_add_nat nIdx n op861] at op853
  rw [evalBinOp_add_one (nIdx + n) op853] at hm835
  have ext_702_827 : Heap.Extends m702 m827 := by rw [hm835]; exact Heap.Extends.snoc _ _
  have hbvar_mot_j : Tm (keyOf c.t) 0 (fun _ => default) m827 (nP + (n + 1) + nIdx + 1)
      (.bvar (nIdx + n + 1)) (.ptr (.enum kexprEnum) m702.length) := by
    rw [hm835]
    exact tm_bvarLocal_nat (by simp) (by dsimp only [n]; omega) (by dsimp only [n]; omega)
  have hps_idx1 := nat_ps_at_spec (κ := keyOf c.t) (d := 0) (Γ := fun _ => default)
    nIdx 1 (nP + (n + 1) + nIdx + 1) (by omega) (by dsimp only [n]; omega) ev889
  have ext_879_906 : Heap.Extends m879 m906 := by rw [hm914]; exact Heap.Extends.snoc _ _
  have hbvar0_906 : Tm (keyOf c.t) 0 (fun _ => default) m906 (nP + (n + 1) + nIdx + 1)
      (.bvar 0) (.ptr (.enum kexprEnum) m879.length) := by
    rw [hm914]
    exact tm_bvarLocal_nat (n := 0) (by simp) (by omega) (by omega)
  have hsnoc_j := SubstAux.ksnoc
    (R := fun h E p => Tm (keyOf c.t) 0 (fun _ => default) h (nP + (n + 1) + nIdx + 1) E p)
    (fun _ _ _ _ ext r => Tm.mono ext r) ev875
    (tmRepList_mono ext_879_906 hps_idx1) hbvar0_906
  have ext_827_865 := ev889.heap_extends.trans (ext_879_906.trans ev875.heap_extends)
  have hmot_app_j := nat_app_n_spec (hbvar_mot_j.mono ext_827_865) hsnoc_j ev823
  rw [evalBinOp_add_one n op993] at ev969
  have hbnd_lj : IxVM.Consistency.Bounded cs967 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have ext_702_811 := ext_702_827.trans (ext_827_865.trans ev823.heap_extends)
  have ext_452_811 := ext_452_482.trans
    (ext_482_725.trans (ev714.heap_extends.trans ext_702_811))
  have hitele_lift := expr_lift_local_spec (Nat.zero_le nP) (by omega) (by decide)
    hbnd_lj (hitele_tm.mono ext_452_811) ev969
  have ext_959_1002 : Heap.Extends m959 m1002 := by rw [hm1010]; exact Heap.Extends.snoc _ _
  have ext_299_1002 := ext_299_513.trans (ext_513_668.trans (ext_668_645.trans
    (ev617.heap_extends.trans (ev749.heap_extends.trans (ev794.heap_extends.trans
      (ev735.heap_extends.trans (ev714.heap_extends.trans
        (ext_702_811.trans (ev969.heap_extends.trans ext_959_1002)))))))))
  have hpw_1002 := repKLevel_heapMono₂ ext_299_1002 hpw_299
  have hmaj_core : Tm (keyOf c.t) 0 (fun _ => default) m1002 ((nP + (n + 1)) + nIdx)
      (.forallE (cFamI T clvls nP nIdx (n + 1) 0)
        (Expr.mkAppN (.bvar (nIdx + n + 1)) (Ix.Kernel.structPsAt 1 nIdx ++ [.bvar 0]))
        { pw := ℓ_c.zeronessOf })
      (.ptr (.enum kexprEnum) m959.length) := by
    exact .forallE (by rw [hm1010]; simp)
      (hfam_j'.mono (ext_702_811.trans (ev969.heap_extends.trans ext_959_1002)))
      (hmot_app_j.mono (ev969.heap_extends.trans ext_959_1002))
      hpw_1002
  have hmaj_core_head :
      ForallDomHeadLvls (keyOf c.t) 0 (fun _ => default) m1002
        T bT clvls 0 ((nP + (n + 1)) + nIdx) (.ptr (.enum kexprEnum) m959.length) :=
    .zero (by rw [hm1010]; simp; exact ⟨rfl, rfl⟩)
      (hfam_j'.mono (ext_702_811.trans (ev969.heap_extends.trans ext_959_1002)))
      (by simp [cFamI, getAppFn_mkAppN_eq]; rfl)
      (hfam_head.mono (ext_702_811.trans (ev969.heap_extends.trans ext_959_1002)))
  obtain ⟨major, hmaj_ite, hmaj_tm⟩ :=
    nat_replace_pis_spec nIdx (by omega) hpw_1002
      (hitele_lift.mono ext_959_1002) hmaj_core ev938
  have hmaj_head :=
    forallDomHeadLvls_replace_pis nIdx (by omega)
      (hitele_lift.mono ext_959_1002) hmaj_core_head ev938
  simp only [↓reduceIte] at hmaj_ite
  have hmaj_tm' : Tm (keyOf c.t) 0 (fun _ => default) m926 (nP + 1 + n) major v925 := by
    rwa [show nP + 1 + n = nP + (n + 1) by omega]
  have hmaj_head' :
      ForallDomHeadLvls (keyOf c.t) 0 (fun _ => default) m926
        T bT clvls nIdx (nP + 1 + n) v925 := by
    rwa [show nIdx = nIdx + 0 by omega, show nP + 1 + n = nP + (n + 1) by omega]
  -- Step 5: `nat_minors` (`isLam = false`) + outer `Forall` + `nat_replace_pis` (`recTy_c`)
  have ext_299_926 := ext_299_1002.trans ev938.heap_extends
  have ext_h_926 := ev231.heap_extends.trans (ext_219_299.trans ext_299_926)
  have hload_min : NatCtorLoad (keyOf c.t) b₀ k ctors_info x_block cs1055 :=
    hload.mono_calls (fun x hx => by simp [hx])
  have hgood_min : Good c cs1055 := hgood.sub (fun x hx => by simp [hx])
  have hbnd_min : IxVM.Consistency.Bounded cs1055 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have ev1057' : ObsFn W "KernelCheck::nat_minors"
      [x_block, .field 0, x_parent_addr, v218, .field (nP : F), .field (nIdx : F), v298,
        .field (n : F), .field ((if large then 1 else 0 : Nat) : F),
        .field ((0 : Nat) : F), v925, .field ((if false then 1 else 0 : Nat) : F)]
      m926 v1044 m1045 cs1055 := by
    simpa using ev1057
  obtain ⟨minors, hmin_eq, hmin_tm⟩ :=
    nat_minors_spec hT hκ_inj (by omega) hwf_all n 0 (by omega)
      hload_min hgood_min hbnd_min
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_926 hb₀_blk)
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_926 hbT)
      (RepKLevelList.mono hlps_219 (ext_219_299.trans ext_299_926))
      (repKLevel_heapMono₂ ext_299_926 hpw_299)
      hmaj_tm' ev1057'
  have hmin_head :=
    forallDomHeadLvls_nat_minors (c := c) (large := large) hnCtors_lt n 0 (by omega) hmaj_head'
      (by simpa using ev1057)
  simp only [Bool.false_eq_true, ↓reduceIte, List.drop_zero, Nat.add_zero] at hmin_eq hmin_tm hmin_head
  have ext_1045_1193 : Heap.Extends m1045 m1193 := by rw [hm1201]; exact Heap.Extends.snoc _ _
  have ext_605_1193 := ev749.heap_extends.trans (ev794.heap_extends.trans
    (ev735.heap_extends.trans (ev714.heap_extends.trans (ext_702_811.trans
      (ev969.heap_extends.trans (ext_959_1002.trans (ev938.heap_extends.trans
        (ev1057.heap_extends.trans ext_1045_1193))))))))
  have ext_299_1193 := ext_299_926.trans (ev1057.heap_extends.trans ext_1045_1193)
  have hpw_1193 := repKLevel_heapMono₂ ext_299_1193 hpw_299
  have hforall_mot : Tm (keyOf c.t) 0 (fun _ => default) m1193 (0 + nP)
      (.forallE motiveTy minors { pw := ℓ_c.zeronessOf })
      (.ptr (.enum kexprEnum) m1045.length) := by
    rw [Nat.zero_add]
    exact .forallE (by rw [hm1201]; simp)
      (hmot_tm.mono ext_605_1193)
      (hmin_tm.mono ext_1045_1193)
      hpw_1193
  have hforall_mot_head :
      ForallDomHeadLvls (keyOf c.t) 0 (fun _ => default) m1193
        T bT clvls ((n + nIdx) + 1) (0 + nP) (.ptr (.enum kexprEnum) m1045.length) := by
    rw [Nat.zero_add]
    exact .succ (by rw [hm1201]; simp; exact ⟨rfl, rfl⟩) (hmin_head.mono ext_1045_1193)
  have ext_391_1193 : Heap.Extends m391 m1193 := by
    rw [← hm452_eq]
    exact ext_452_645.trans (ev617.heap_extends.trans ext_605_1193)
  obtain ⟨recTy_c, hrecTy_ite, hrecTy_tm⟩ :=
    nat_replace_pis_spec nP (by omega) hpw_1193
      (htty_390.mono ext_391_1193) hforall_mot ev1165
  have hrecTy_head :=
    forallDomHeadLvls_replace_pis nP (by omega)
      (htty_390.mono ext_391_1193) hforall_mot_head ev1165
  have hrecTy_head' :
      ForallDomHeadLvls (keyOf c.t) 0 (fun _ => default) m1153
        T bT clvls (nP + 1 + n + nIdx) 0 v1152 := by
    rwa [show nP + 1 + n + nIdx = nP + ((n + nIdx) + 1) by omega]
  simp only [↓reduceIte] at hrecTy_ite
  -- Connect `recTy_c` to `posOf rlps' recTy` via `posOf_structRecTyR`
  have hcRecTy_eq :
      cRecTy T clvls ℓ_c nP nIdx (posOf rlps' tty₀)
        (ctors_info.map fun inf => (inf.1, inf.2.1, posOf rlps' inf.2.2.2.1, inf.2.2.2.2)) =
      some recTy_c := by
    unfold cRecTy
    dsimp only
    rw [hsT_pos]
    dsimp only [Option.bind]
    rw [hmot_eq]
    dsimp only [Option.bind]
    simp only [List.length_map]
    rw [hmaj_ite]
    dsimp only [Option.bind]
    rw [hmin_eq]
    dsimp only [Option.bind]
    exact hrecTy_ite
  have hcs₀ : ∀ entry ∈ ctors₀,
      (∃ cbs cbody, entry.2.2.1.stripPis (nP + entry.2.1) = some (cbs, cbody)) ∧
      ∀ i ∈ entry.2.2.2, i < entry.2.1 := by
    intro entry hentry
    simp only [ctors₀, List.mem_map] at hentry
    obtain ⟨inf, hinf_mem, rfl⟩ := hentry
    have hwf_inf := hwf_all inf hinf_mem
    obtain ⟨cbs, _, cbody, hsC⟩ := hwf_inf.strip_C
    exact ⟨⟨cbs, _, hsC⟩, fun i hi => (hwf_inf.rec_spines i hi).1⟩
  have hpos_ty := posOf_structRecTyR k large T nP nIdx tty₀ ctors₀ ⟨tbs₀, tsort₀, hsT₀⟩ hcs₀
  dsimp only at hpos_ty
  rw [← clvls_eq_subst_params k large] at hpos_ty
  have hmap_cs :
      (ctors₀.map fun entry => (entry.1, entry.2.1, posOf rlps' entry.2.2.1, entry.2.2.2)) =
      (ctors_info.map fun inf => (inf.1, inf.2.1, posOf rlps' inf.2.2.2.1, inf.2.2.2.2)) := by
    simp [ctors₀, List.map_map, Function.comp_def]
  rw [hmap_cs, hcRecTy_eq] at hpos_ty
  rw [Option.map_eq_some_iff] at hpos_ty
  obtain ⟨recTy, hrecTy, hpos_recTy⟩ := hpos_ty
  rw [← hpos_recTy] at hrecTy_tm
  -- Step 6: `wrap_rel` on `recTy`
  subst heq1282
  have ext_h_1153 := ev231.heap_extends.trans
    (ext_219_299.trans (ext_299_1193.trans ev1165.heap_extends))
  have hgood_wty : Good c cs1257 := hgood.sub (fun x hx => by simp [hx])
  have hwrap_ty_pos := wrap_rel_spec hlf hgood_wty hrecTy_tm (hrec_ty.mono ext_h_1153) ev1259
  have hwrap_ty : WrapRelSem c.env.find? recTy rec_ty₀ :=
    WrapRelSem.of_posOf_perm (rlps_perm k large) hwrap_ty_pos
  -- Step 7: `find_peer_recursor_with_spec`, `build_rec_lvls_list`, `nat_check_rules`
  have ext_1249_1317 : Heap.Extends m1249 m1317 := by rw [hm1325]; exact Heap.Extends.snoc _ _
  have ext_h_1317 := ext_h_1153.trans (ev1259.heap_extends.trans ext_1249_1317)
  have hgood_peer : Good c cs1294 := hgood.sub (fun x hx => by simp [hx])
  obtain ⟨bOut, hbOut_1284, hbOut_addr⟩ :=
    find_peer_recursor_two_spec hc hrec_at hcst_info hbRec_addr hgood_peer
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_1317 hb₀_rec_blk)
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_1317 hbRec)
      ev1296
  have hOut_recC : keyOf c.t (ixAddr bOut) = recC := by rw [hbOut_addr, hRec]
  rw [hnlvls_eq] at ev1465
  have hrlvls_1455 := build_rec_lvls_list_spec
    (by dsimp only [rlps']; cases large <;>
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_range] <;>
      have := hk_lt <;> omega) ev1465
  have ext_h_1455 := ext_h_1317.trans (ev1296.heap_extends.trans ev1465.heap_extends)
  have ext_605_1455 := ext_605_1193.trans (ev1165.heap_extends.trans
    (ev1259.heap_extends.trans (ext_1249_1317.trans
      (ev1296.heap_extends.trans ev1465.heap_extends))))
  have ext_391_1455 := ext_391_1193.trans (ev1165.heap_extends.trans
    (ev1259.heap_extends.trans (ext_1249_1317.trans
      (ev1296.heap_extends.trans ev1465.heap_extends))))
  have ext_299_1455 := ext_299_1193.trans (ev1165.heap_extends.trans
    (ev1259.heap_extends.trans (ext_1249_1317.trans
      (ev1296.heap_extends.trans ev1465.heap_extends))))
  have hload_rules : NatCtorLoad (keyOf c.t) b₀ k ctors_info x_block cs1345 :=
    hload.mono_calls (fun x hx => by simp [hx])
  have hgood_rules : Good c cs1345 := hgood.sub (fun x hx => by simp [hx])
  have hbnd_rules : IxVM.Consistency.Bounded cs1345 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have ev1347' : ObsFn W "KernelCheck::nat_check_rules"
      [x_rules, x_block, .field 0, x_parent_addr, v218, .field (nP : F), .field (nIdx : F),
        v298, .field (n : F), .field ((if large then 1 else 0 : Nat) : F),
        v390, v604, v1283, v1361, .field ((0 : Nat) : F)]
      m1455 r h' cs1345 := by
    simpa using ev1347
  have hrules_ok := nat_check_rules_spec hlf hT hκ_inj hOut_recC hnCtors_lt hnP_lt hwf_all
    hsT₀ hsT_pos hmot_eq 0 (by omega)
    (hrules.mono ext_h_1455) hload_rules hgood_rules hbnd_rules
    (Bytes.repAddressRef_heapMono₂ addrTy ext_h_1455 hb₀_blk)
    (Bytes.repAddressRef_heapMono₂ addrTy ext_h_1455 hbT)
    (Bytes.repAddressRef_heapMono₂ addrTy ev1465.heap_extends hbOut_1284)
    (RepKLevelList.mono hlps_219 (ext_219_299.trans ext_299_1455))
    hrlvls_1455
    (repKLevel_heapMono₂ ext_299_1455 hpw_299)
    (htty_390.mono ext_391_1455)
    (hmot_tm.mono ext_605_1455)
    ev1347'
  have hhead_eq :
      ∀ a_d ls_d,
        ForallRightHeadLvls h a_d ls_d (nP + 1 + n + nIdx) x_ty →
        ls_d = clvls := by
    intro a_d ls_d hright
    exact (wrap_rel_forallDomHeadLvls hlf hT_ind (nP + 1 + n + nIdx)
      hgood_wty hrecTy_head' (hright.mono ext_h_1153) ev1259).symm
  refine ⟨hnlvls_eq, heq189, heq217, ⟨recTy, hrecTy, hwrap_ty⟩, hhead_eq, ?_⟩
  intro idx hlt hidx
  have h0_idx : 0 + idx < ctors_info.length := by simpa using hidx
  simpa using hrules_ok idx hlt h0_idx

/-! ## Section 3: Recursor Member & Block Assembly (`check_recursor_canonical_full`, `check_recursor_member`, `DeclNativeRunJ`) -/

/-- `sumRules` preserves constructor names, field counts, and rule RHS annotations (`RuleStored`)
against the declared recursor rules. -/
theorem sumRules_forall2_ruleStored
    (find? : KKey → Option KConstantInfo) (recName : KKey) (nP mI rP : Nat) (recTy : KExpr) :
    ∀ (ctorsA : List (KConstantVal × Nat)) (rhssA : List KExpr) (rules₀ : List (RecRule .anon)),
      ctorsA.length = rules₀.length →
      rhssA.length = rules₀.length →
      (∀ j < rules₀.length, ∀ cA rhsA rl₀,
        ctorsA[j]? = some cA → rhssA[j]? = some rhsA → rules₀[j]? = some rl₀ →
        cA.1.name = rl₀.ctor ∧ cA.2 = rl₀.nfields ∧ IxVM.Consistency.Annotates rhsA rl₀.rhs) →
      List.Forall₂ IxVM.Consistency.RuleStored
        (Ix.Kernel.sumRules find? recName nP mI rP recTy ctorsA rhssA) rules₀
  | [], [], [], _, _, _ => List.Forall₂.nil
  | _ :: _, [], _ :: _, _, hlen₂, _ => nomatch hlen₂
  | [], _ :: _, _ :: _, hlen₁, _, _ => nomatch hlen₁
  | _ :: _, _ :: _, [], hlen₁, _, _ => nomatch hlen₁
  | cA :: csA, rhsA :: rsA, rl₀ :: rls₀, hlen₁, hlen₂, hrel => by
    obtain ⟨hctor, hnfields, hannot⟩ :=
      hrel 0 (by simp) cA rhsA rl₀ rfl rfl rfl
    refine List.Forall₂.cons ⟨hctor, hnfields, hannot⟩
      (sumRules_forall2_ruleStored find? recName nP mI rP recTy csA rsA rls₀
        (Nat.succ.inj hlen₁) (Nat.succ.inj hlen₂) fun j hj cA' rhsA' rl₀' hc hr hrl => ?_)
    exact hrel (j + 1) (Nat.succ_lt_succ hj) cA' rhsA' rl₀' hc hr hrl

private theorem large?_cons_range (k : Nat) :
    (if (List.range k == List.range k) && !(List.range k).contains k then some k else none) =
      some k := by
  simp

/-- On a block recognized by `Ix.Kernel.nativeParts?` with `p₀.cvT.levelParams = List.range k`
and `p₀.cvR.levelParams = if large₀ then k :: List.range k else List.range k`, `p₀.large = large₀`,
`p₀.elim = if large₀ then k else 0`, and `Ix.Kernel.nativeRecLpsOk p₀.toInductiveShape = true`. -/
theorem nativeParts?_lps_inv {nPd k : Nat} {large₀ : Bool} {block : List KConstantInfo}
    {p₀ : Ix.Kernel.NativeParts .anon}
    (hp : Ix.Kernel.nativeParts? nPd block = some p₀)
    (hlpsT : p₀.cvT.levelParams = List.range k)
    (hlpsR : p₀.cvR.levelParams = if large₀ then k :: List.range k else List.range k) :
    p₀.large = large₀ ∧
    p₀.elim = (if large₀ then k else 0) ∧
    Ix.Kernel.nativeRecLpsOk p₀.toInductiveShape = true := by
  unfold Ix.Kernel.nativeParts? at hp
  rw [Option.map_eq_some_iff] at hp
  obtain ⟨psh, hsh, rfl⟩ := hp
  change psh.cvT.levelParams = List.range k at hlpsT
  change psh.cvR.levelParams = (if large₀ then k :: List.range k else List.range k) at hlpsR
  unfold Ix.Kernel.nativeShape? at hsh
  cases block with
  | nil => exact nomatch hsh
  | cons hd rest =>
    cases hd with
    | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | ctorInfo _ _ _
    | recInfo _ _ _ _ | projInfo _ => exact nomatch hsh
    | indInfo cvT caps₀ =>
      dsimp only at hsh
      cases hsp : Ix.Kernel.sumSplit rest with
      | none => rw [hsp] at hsh; exact nomatch hsh
      | some q =>
        obtain ⟨cs, cvR, mI, rP, rules⟩ := q
        rw [hsp] at hsh
        dsimp only at hsh
        cases hcnt : Ix.Kernel.nativeCounts? nPd cvT cs mI rP with
        | none => rw [hcnt] at hsh; exact nomatch hsh
        | some pair =>
          obtain ⟨nP, nIdx⟩ := pair
          rw [hcnt] at hsh
          dsimp only at hsh
          split at hsh
          · have hcvT_eq : psh.cvT = cvT ∧ psh.cvR = cvR := by
              split at hsh <;> (injection hsh with hsh_eq; subst hsh_eq; exact ⟨rfl, rfl⟩)
            rw [hcvT_eq.1] at hlpsT
            rw [hcvT_eq.2] at hlpsR
            rw [hlpsT, hlpsR] at hsh
            cases large₀ with
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at hsh hlpsR ⊢
              cases h_rng : List.range k with
              | nil =>
                simp [h_rng] at hsh
                subst hsh
                simp [Ix.Kernel.nativeRecLpsOk, hlpsT, hlpsR]
              | cons hd tl =>
                simp [h_rng] at hsh
                subst hsh
                simp [Ix.Kernel.nativeRecLpsOk, hlpsT, hlpsR]
            | true =>
              simp only [↓reduceIte] at hsh hlpsR ⊢
              rw [large?_cons_range k] at hsh
              injection hsh with hsh_eq
              subst hsh_eq
              simp [Ix.Kernel.nativeRecLpsOk, hlpsT, hlpsR]
          · exact nomatch hsh

/-- `p₀.recPinned = true` holds whenever the recursor's `rP`, `mI`, rule count, and per-rule
constructor names and field counts match the parent inductive block's constructors. -/
theorem nativeParts?_recPinned_true {nPd : Nat} {block : List KConstantInfo}
    {p₀ : Ix.Kernel.NativeParts .anon}
    {caps₀ : Ix.Kernel.IndCaps .anon} {cs : List (KConstantVal × Nat × Nat)}
    {mI rP : Nat} {rules : List (RecRule .anon)}
    (hp : Ix.Kernel.nativeParts? nPd block = some p₀)
    (hblk : block = .indInfo p₀.cvT caps₀ ::
      (cs.map fun c => ConstantInfo.ctorInfo c.1 c.2.1 c.2.2) ++
      [.recInfo p₀.cvR mI rP rules])
    (hctors : p₀.ctors = cs.map (fun c => (c.1, c.2.2)))
    (hrP : rP = p₀.nP + 1 + p₀.ctors.length)
    (hmI : mI = p₀.nP + 1 + p₀.ctors.length + p₀.nIdx)
    (hrules_len : rules.length = p₀.ctors.length)
    (hrules_match : ∀ j < p₀.ctors.length, ∀ rule c,
      rules[j]? = some rule → p₀.ctors[j]? = some c →
      rule.ctor = c.1.name ∧ rule.nfields = c.2) :
    p₀.recPinned = true := by
  have hsplit :
      ∀ (xs : List (KConstantVal × Nat × Nat)),
        Ix.Kernel.sumSplit
          ((xs.map fun c => ConstantInfo.ctorInfo c.1 c.2.1 c.2.2) ++
            [.recInfo p₀.cvR mI rP rules]) =
          some (xs, p₀.cvR, mI, rP, rules) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, List.cons_append, Ix.Kernel.sumSplit, ih, Option.map_some]
  unfold Ix.Kernel.nativeParts? at hp
  rw [Option.map_eq_some_iff] at hp
  obtain ⟨psh, hsh, heq_p₀⟩ := hp
  have hpin_eq : p₀.recPinned = Ix.Kernel.nativeRecPinOk p₀.toInductiveShape block := by
    rw [← heq_p₀]
  rw [hpin_eq, hblk, List.cons_append]
  simp only [Ix.Kernel.nativeRecPinOk, hsplit cs]
  have hcs_len : p₀.ctors.length = cs.length := by simp [hctors]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨hrP, hmI⟩, hrules_len⟩, ?_⟩
  rw [List.all_eq_true]
  intro j hj_mem
  have hj : j < p₀.ctors.length := List.mem_range.mp hj_mem
  have hj_r : j < rules.length := by omega
  have hj_cs : j < cs.length := by omega
  rw [List.getElem?_eq_getElem hj_r, List.getElem?_eq_getElem hj_cs]
  dsimp only
  have hc_get : p₀.ctors[j]? = some (cs[j].1, cs[j].2.2) := by
    simp [hctors, hj_cs]
  obtain ⟨hc_eq, hnf_eq⟩ := hrules_match j hj rules[j] (cs[j].1, cs[j].2.2)
    (List.getElem?_eq_getElem hj_r) hc_get
  simp [hc_eq, hnf_eq]

theorem wrapperArity_congr_defn {find₁ find₂ : KKey → Option KConstantInfo}
    (h : ∀ k cv v hn, find₁ k = some (.defnInfo cv v hn) ↔ find₂ k = some (.defnInfo cv v hn))
    (w : KKey) :
    Ix.Kernel.Semantics.wrapperArity find₁ w = Ix.Kernel.Semantics.wrapperArity find₂ w := by
  unfold Ix.Kernel.Semantics.wrapperArity
  cases h₁ : find₁ w with
  | none =>
    cases h₂ : find₂ w with
    | none => rfl
    | some ci₂ =>
      cases ci₂ with
      | defnInfo cv v hn =>
        rw [(h w cv v hn).mpr h₂] at h₁
        exact nomatch h₁
      | _ => rfl
  | some ci₁ =>
    cases ci₁ with
    | defnInfo cv v hn =>
      rw [(h w cv v hn).mp h₁]
    | _ =>
      cases h₂ : find₂ w with
      | none => rfl
      | some ci₂ =>
        cases ci₂ with
        | defnInfo cv v hn =>
          rw [(h w cv v hn).mpr h₂] at h₁
          exact nomatch h₁
        | _ => rfl

theorem WrapRelSem.congr_defn {find₁ find₂ : KKey → Option KConstantInfo}
    (h : ∀ k cv v hn, find₁ k = some (.defnInfo cv v hn) ↔ find₂ k = some (.defnInfo cv v hn))
    {g d : KExpr} (hw : WrapRelSem find₁ g d) :
    WrapRelSem find₂ g d :=
  WrapRelSem.congr_wrapperArity (wrapperArity_congr_defn h) hw

theorem CapsUpgradeAt.defnInfo_iff {T : KKey} {cvS : KConstantVal}
    {caps : Ix.Kernel.IndCaps .anon} {envₐ envᵦ : Ix.Kernel.Env .anon}
    (hup : CapsUpgradeAt T cvS caps envₐ envᵦ) :
    ∀ k cv v hn,
      envₐ.find? k = some (.defnInfo cv v hn) ↔ envᵦ.find? k = some (.defnInfo cv v hn) := by
  intro k cv v hn
  by_cases hkeq : k = T
  · subst hkeq
    rw [hup.find_self_a, hup.find_self_b]
    simp
  · rw [hup.find_ne hkeq]

theorem RulesRepExact.toRepListTrue {κ : _root_.Address → KKey} {h : Heap F}
    {ps : List LevelParam} {j : Nat} {v : SourceValue F} {rls : List (RecRule .anon)}
    (hr : RulesRepExact κ h ps j v rls) :
    RepList krrListEnum (fun _ _ _ => True) h rls v := by
  induction hr with
  | nil cell => exact .nil cell
  | cons cell _ _ ih => exact .cons cell trivial ih

theorem rules_length_spec {κ : _root_.Address → KKey} {ps : List LevelParam}
    {j : Nat} {rls : List (RecRule .anon)} {p r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<KernelTypes::KRecRule>» [p] h r h' cs)
    (hr : RulesRepExact κ h ps j p rls) :
    r = .field (rls.length : F) ∧ h' = h := by
  have ev' : ObsFn W
      (Instance.mk "Lists::length" [(.named "KernelTypes::KRecRule" [])]).symbol
      [p] h r h' cs := by
    rw [Obs.Names.«Lists::length<KernelTypes::KRecRule>».symbol]
    exact ev
  have hl' : RepList
      (Instance.mk "Lists::Node" [(.named "KernelTypes::KRecRule" [])]).symbol
      (fun _ _ _ => True) h rls p := by
    rw [Obs.Names.«Lists::Node<KernelTypes::KRecRule>».symbol]
    exact hr.toRepListTrue
  exact Lib.Lists.length_spec ev' hl'

theorem CIRepExact.ctor_key_and_nf {κ : _root_.Address → KKey} {h : Heap F}
    {nl ty blk np nf u : SourceValue F} {b₀ b_c : Bytes.Address}
    {cv : KConstantVal} {nP nF j : Nat}
    (hj_lt : j < 2147483648)
    (hb_c : Bytes.RepAddressRef addrTy h b_c blk)
    (hix : ixAddr b_c = ixAddr b₀)
    (hci : CIRepExact κ h
      (.construct kciEnum "Ctor" [nl, ty, blk, .field 0, .field (j : F), np, nf, u])
      (.ctorInfo cv nP nF)) :
    ValRepExact κ h nl ty cv ∧
    np = .field (nP : F) ∧
    nf = .field (nF : F) ∧
    cv.name = κ (cprjAddr (ixAddr b₀) 0 j) := by
  generalize hv : Value.construct kciEnum "Ctor"
      [nl, ty, blk, .field 0, .field (j : F), np, nf, u] = v₀ at hci
  generalize hinfo : ConstantInfo.ctorInfo cv nP nF = ci₀ at hci
  cases hci
  case ctor hv_rep hnp hnf _ hkey =>
    injection hv with _ _ hxs
    injection hxs with h1 hxs; injection hxs with h2 hxs; injection hxs with h3 hxs
    injection hxs with h4 hxs; injection hxs with h5 hxs; injection hxs with h6 hxs
    injection hxs with h7 _
    injection hinfo with hcv hnP hnF
    subst h1 h2 h3 h6 h7 hcv hnP hnF
    obtain ⟨b_k, i_k, j_k, hb_k, hi_k, hj_k, hname⟩ := hkey
    have hb_eq : b_k = b_c := IxVMRep.repAddressRef_det U32.Goldilocks.compatible hb_k hb_c
    have hi_eq : ZMod.val i_k = 0 := by
      have hi_f : (0 : F) = i_k := Value.field.inj (h4.trans hi_k)
      rw [← hi_f, ZMod.val_zero]
    have hj_eq : ZMod.val j_k = j := by
      have hj_f : (j : F) = j_k := Value.field.inj (h5.trans hj_k)
      rw [← hj_f]
      exact ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt (by decide))
    rw [hb_eq, hix, hi_eq, hj_eq] at hname
    exact ⟨hv_rep, hnp, hnf, hname⟩
  all_goals
    injection hv with _ hc _
    exact absurd hc (by decide)

private theorem env_find?_cons_ne {c : ConstantInfo .anon} {env : Ix.Kernel.Env .anon} {k : KKey}
    (hne : c.name ≠ k) :
    (Ix.Kernel.Env.mk (c :: env.consts)).find? k = env.find? k := by
  rw [Ix.Kernel.Env.find?_cons, ite_eq_right hne]

private theorem mem_of_eq_map_const {α β : Type _} {xs : List α} {ys : List β} {v : α}
    (h : xs = ys.map fun _ => v) {i : Nat} (hi : i < xs.length) : v ∈ xs := by
  have hi' : i < ys.length := by
    have hl := congrArg List.length h
    rw [List.length_map] at hl
    omega
  rw [h]
  exact List.mem_map.mpr ⟨ys[i], List.getElem_mem hi', rfl⟩

theorem recIdxOf_mem_mentionsConst {T : KKey} {lps : List LevelParam}
    {nP nIdx : Nat} {cA : KConstantVal × Nat} {ks : List Ix.Kernel.RecFieldKind}
    {cbs : List (KExpr × Ix.Kernel.BinderMeta)} {cbody : KExpr}
    (hrck : Ix.Kernel.recCtorKinds T lps nP nIdx cA = some ks)
    (hok : ∀ k ∈ ks, k ≠ .negative ∧ k ≠ .unsupported)
    (hst : cA.1.type.stripPis (nP + cA.2) = some (cbs, cbody))
    {i : Nat} (hi_mem : i ∈ Ix.Kernel.recIdxOf ks) :
    i < cA.2 ∧ (cbs.getD (nP + i) default).1.mentionsConst T = true := by
  unfold Ix.Kernel.recCtorKinds at hrck
  rw [hst] at hrck
  dsimp only at hrck
  by_cases hret : (cbody.getAppArgs.drop nP).all (fun a => !a.mentionsConst T) = true
  · rw [ite_eq_left hret] at hrck
    injection hrck with hks
    simp only [Ix.Kernel.recIdxOf, List.mem_filter, List.mem_range] at hi_mem
    obtain ⟨hi_ks, hkind⟩ := hi_mem
    have hks_len : ks.length = cA.2 := by
      rw [← hks, List.length_map, List.length_range]
    have hi_lt : i < cA.2 := by omega
    refine ⟨hi_lt, ?_⟩
    cases hmen : (cbs.getD (nP + i) default).1.mentionsConst T with
    | true => rfl
    | false =>
      have hget : ks.getD i .ordinary = .ordinary := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_ks, Option.getD_some]
        have hgi : ks[i]'hi_ks =
            (match Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 with
              | .recursive =>
                if Ix.Kernel.structUsedLater cA.1.type nP i then
                  Ix.Kernel.RecFieldKind.unsupported
                else Ix.Kernel.RecFieldKind.recursive
              | .reflexive =>
                if Ix.Kernel.structUsedLater cA.1.type nP i then
                  Ix.Kernel.RecFieldKind.unsupported
                else Ix.Kernel.RecFieldKind.reflexive
              | k => k) := by
          have hq := congrArg (fun xs => xs[i]?) hks.symm
          rw [List.getElem?_eq_getElem hi_ks, List.getElem?_map, List.getElem?_range hi_lt,
            Option.map_some, Option.some.injEq] at hq
          exact hq
        rw [hgi]
        unfold Ix.Kernel.recFieldKind
        rw [hmen]
        rfl
      rw [hget] at hkind
      exact nomatch hkind
  · have hret_f : (cbody.getAppArgs.drop nP).all (fun a => !a.mentionsConst T) = false :=
      Bool.eq_false_iff.mpr hret
    rw [hret_f] at hrck
    simp only [Bool.false_eq_true, ↓reduceIte] at hrck
    injection hrck with hks
    simp only [Ix.Kernel.recIdxOf, List.mem_filter, List.mem_range] at hi_mem
    obtain ⟨hi_ks, _⟩ := hi_mem
    have hneg_mem : Ix.Kernel.RecFieldKind.negative ∈ ks :=
      mem_of_eq_map_const hks.symm hi_ks
    exact absurd rfl (hok _ hneg_mem).1

/-- Build the 5-tuple constructor table `(C, nF, R₀, C₀, recIdx)` expected by `nat_rec_check_spec`
from `ctorsA`, `ctorRawTypes`, and classified `kinds`. -/
def buildCtorsInfo (ctorsA : List (KConstantVal × Nat)) (ctorRawTypes : List KExpr)
    (kinds : List (List Ix.Kernel.RecFieldKind)) :
    List (KKey × Nat × KExpr × KExpr × List Nat) :=
  (List.range ctorsA.length).map fun j =>
    let cA := ctorsA.getD j default
    let ks := kinds.getD j []
    (cA.1.name, cA.2, ctorRawTypes.getD j default, cA.1.type, Ix.Kernel.recIdxOf ks)

@[simp] theorem buildCtorsInfo_length (ctorsA : List (KConstantVal × Nat))
    (ctorRawTypes : List KExpr) (kinds : List (List Ix.Kernel.RecFieldKind)) :
    (buildCtorsInfo ctorsA ctorRawTypes kinds).length = ctorsA.length := by
  simp [buildCtorsInfo]

theorem buildCtorsInfo_getElem? {ctorsA : List (KConstantVal × Nat)}
    {ctorRawTypes : List KExpr} {kinds : List (List Ix.Kernel.RecFieldKind)}
    {j : Nat} (hj : j < ctorsA.length) (hk_len : kinds.length = ctorsA.length) :
    (buildCtorsInfo ctorsA ctorRawTypes kinds)[j]? =
      some (ctorsA[j].1.name, ctorsA[j].2, ctorRawTypes.getD j default, ctorsA[j].1.type,
        Ix.Kernel.recIdxOf (kinds[j]'(by omega))) := by
  have hj_k : j < kinds.length := by omega
  simp only [buildCtorsInfo, List.getElem?_map, List.getElem?_range hj, Option.map_some]
  congr 1
  have h1 : ctorsA.getD j default = ctorsA[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  have h2 : kinds.getD j [] = kinds[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj_k]; rfl
  rw [h1, h2]

theorem buildCtorsInfo_map_eq_nativeCtors4 {ctorsA : List (KConstantVal × Nat)}
    {ctorRawTypes : List KExpr} {kinds : List (List Ix.Kernel.RecFieldKind)}
    (hk_len : kinds.length = ctorsA.length) :
    (buildCtorsInfo ctorsA ctorRawTypes kinds).map
      (fun info => (info.1, info.2.1, info.2.2.2.1, info.2.2.2.2)) =
    Ix.Kernel.nativeCtors4 ctorsA kinds := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < ctorsA.length
  · have hj_k : j < kinds.length := by omega
    rw [List.getElem?_map, buildCtorsInfo_getElem? hj hk_len, Option.map_some]
    simp [Ix.Kernel.nativeCtors4, List.getElem?_zipWith,
      List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj_k]
  · have hj_b : ¬ j < (buildCtorsInfo ctorsA ctorRawTypes kinds).length := by
      simpa [buildCtorsInfo] using hj
    have hj_n : ¬ j < (Ix.Kernel.nativeCtors4 ctorsA kinds).length := by
      simp [Ix.Kernel.nativeCtors4, hk_len, hj]
    rw [List.getElem?_map, List.getElem?_eq_none (Nat.le_of_not_lt hj_b), Option.map_none,
      List.getElem?_eq_none (Nat.le_of_not_lt hj_n)]

theorem natCtorLoad_of_ctorLoadAt {t : Ix.Kernel.RoleTable} {b₀ : Bytes.Address}
    {k nP : Nat} {cs_root cs : List (Call F)}
    {ctors ctorsA : List (KConstantVal × Nat)} {ctorRawTypes : List KExpr}
    {kinds : List (List Ix.Kernel.RecFieldKind)} {x_block : SourceValue F}
    (hcload : CtorLoadAt t b₀ nP cs_root ctors ctorsA ctorRawTypes)
    (hlps_ctors : ∀ c ∈ ctors, c.1.levelParams = List.range k)
    (hnCtors_lt : ctors.length < 2147483648)
    (hk_len : kinds.length = ctorsA.length)
    (hsub : ∀ x ∈ cs, x ∈ cs_root) :
    NatCtorLoad (keyOf t) b₀ k (buildCtorsInfo ctorsA ctorRawTypes kinds) x_block cs := by
  intro j hj_info p9 h m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50 hsub15 hb₀ ev_cprj ld_ctor
    info hinfo
  have hjA : j < ctorsA.length := by simpa using hj_info
  have hj : j < ctors.length := by rwa [← hcload.1]
  have hj_lt : j < 2147483648 := by omega
  rw [buildCtorsInfo_getElem? hjA hk_len] at hinfo
  injection hinfo with hinfo_eq
  subst hinfo_eq
  obtain ⟨c_j, cvCa₀, hc_j, hcA_j, hvs_j, hload_j⟩ := hcload.2 j hj
  rw [List.getElem?_eq_getElem hjA] at hcA_j
  injection hcA_j with hcA_eq
  obtain ⟨nl', cty', cblk', cnp', cnf', b_c, ld_c', hb_c, hix_c, hraw_rep, hci_rep⟩ :=
    hload_j x_block p9 h m2 cs15 (fun x hx => hsub x (hsub15 x hx)) hb₀ ev_cprj
  rw [ld_c'] at ld_ctor
  injection ld_ctor with hval
  injection hval with _ _ h1
  injection h1 with _ h1; injection h1 with hcty_eq h1; injection h1 with _ h1
  injection h1 with _ h1; injection h1 with _ h1; injection h1 with _ h1
  injection h1 with hcnf_eq _
  cases hcty_eq; cases hcnf_eq
  obtain ⟨_, _, hnf_f, hname_eq⟩ := CIRepExact.ctor_key_and_nf hj_lt hb_c hix_c hci_rep
  have hcA_fst : ctorsA[j].1 = cvCa₀ := by rw [hcA_eq]
  have hcA_snd : ctorsA[j].2 = c_j.2 := by rw [hcA_eq]
  have hlps_cj : cvCa₀.levelParams = List.range k := by
    rw [hvs_j.2.1]
    exact hlps_ctors c_j (List.mem_of_getElem? hc_j)
  have hraw0 := (hraw_rep 0 (fun _ => default)).toRawTm
  rw [hlps_cj, posOf_range, ← posOf_range k (ctorRawTypes.getD j default),
    ← posOf_range k cvCa₀.type, ← hcA_fst] at hraw0
  refine ⟨?_, ?_, hraw0⟩
  · rw [hcA_fst]; exact hname_eq
  · rw [hcA_snd]; exact hnf_f

/-! ## Section 4: Top-Level Witness, Bridges, & Deliverable 1 (`nativeWithRec_step`) -/

/-- Circuit/record witness for a one-type native inductive block with recursor (`L5-N` with recursor).
Extends `OneTypeBlockWitness` (which packages the `Induct` `check_const` pass and constructor loads)
with the `Rec` `check_const` pass on the block's recursor member (`rprjAddr (ixAddr b₀) 1`). -/
structure NativeWithRecWitness (calls : List (Call F)) (env : Ix.Kernel.Env .anon)
    (block : List KConstantInfo) (p₀ : Ix.Kernel.NativeParts .anon) where
  front : OneTypeBlockWitness calls env p₀
  E_rec : Ixon.Env
  cst : Ixon.Constant
  ind_m : Ixon.Inductive
  rec_m : Ixon.Recursor
  bT : Bytes.Address
  bRec : Bytes.Address
  cvRa₀ : KConstantVal
  rawT : KExpr
  rules₀ : List (RecRule .anon)
  rulesA : List (RecRule .anon)
  rec_np : Nat
  rec_ni : Nat
  rec_nm : Nat
  rec_nmi : Nat
  rc_rec : SourceValue F
  nl_rec : SourceValue F
  ty_rec : SourceValue F
  rules_rec : SourceValue F
  k_rec : SourceValue F
  bp_rec : SourceValue F
  ap_rec : SourceValue F
  r_rec : SourceValue F
  h_rec : Heap F
  h_rec' : Heap F
  cs_rec : List (Call F)
  record_b₀ : Ix.Cert.recordAt E_rec (ixAddr front.b₀) = some cst
  cst_muts : cst.info = .muts #[.indc ind_m, .recr rec_m]
  bT_addr : ixAddr bT = iprjAddr (ixAddr front.b₀) 0
  bRec_addr : ixAddr bRec = rprjAddr (ixAddr front.b₀) 1
  key_bT_inj : ∀ a : Bytes.Address, keyOf front.t (ixAddr a) = p₀.cvT.name → a = bT
  R_rprj : p₀.cvR.name = keyOf front.t (rprjAddr (ixAddr front.b₀) 1)
  fresh_R : env.find? p₀.cvR.name = none
  R_ne_T : p₀.cvR.name ≠ p₀.cvT.name
  R_not_in_ctors : p₀.cvR.name ∉ p₀.ctors.map (·.1.name)
  basis_R : Ix.Kernel.reservedBasisNames.contains p₀.cvR.name = false
  lps_R_or :
    p₀.cvR.levelParams = List.range p₀.cvT.levelParams.length ∨
    p₀.cvR.levelParams =
      p₀.cvT.levelParams.length :: List.range p₀.cvT.levelParams.length
  lbd_R : p₀.cvR.type.looseBVarsBounded 0 = true
  fv_R : p₀.cvR.type.hasFvar = false
  former_sort :
    ∃ bsT s, front.cvTa₀.type.stripPis (p₀.nP + p₀.nIdx) = some (bsT, .sort s)
  rawT_strip :
    ∃ rbs₀ rbody₀, rawT.stripPis (p₀.nP + p₀.nIdx) = some (rbs₀, rbody₀)
  lps_rawT : rawT.allLevelParamsDefined p₀.cvT.levelParams = true
  lps_ctorRaw :
    ∀ j < p₀.ctors.length,
      (front.ctorRawTypes.getD j default).allLevelParamsDefined p₀.cvT.levelParams = true
  valStored_R : IxVM.Consistency.ValStored cvRa₀ p₀.cvR
  valRep_R : ValRepExact (keyOf front.t) h_rec nl_rec ty_rec cvRa₀
  rulesRep_R : RulesRepExact (keyOf front.t) h_rec cvRa₀.levelParams 0 rules_rec rulesA
  rules_block :
    ∃ (caps₀ : Ix.Kernel.IndCaps .anon) (cs : List (KConstantVal × Nat × Nat))
      (mI rP : Nat),
      block = .indInfo p₀.cvT caps₀ ::
        (cs.map fun c => ConstantInfo.ctorInfo c.1 c.2.1 c.2.2) ++
        [.recInfo p₀.cvR mI rP rules₀] ∧
      rP = rec_np + rec_nm + rec_nmi ∧
      mI = rP + rec_ni
  rules_stored : List.Forall₂ IxVM.Consistency.RuleStored rulesA rules₀
  rules_ctor :
    ∀ j < p₀.ctors.length, ∀ rl₀ c,
      rules₀[j]? = some rl₀ → p₀.ctors[j]? = some c → rl₀.ctor = c.1.name
  rules_rhs_scoped :
    ∀ rl₀ ∈ rules₀, rl₀.rhs.hasFvar = false ∧ rl₀.rhs.looseBVarsBounded 0 = true
  rec_counts_lt :
    p₀.cvT.levelParams.length < 2147483648 ∧
    p₀.ctors.length < 2147483648 ∧
    rules₀.length < 2147483648 ∧
    rec_np < 2147483648 ∧
    rec_ni < 2147483648 ∧
    rec_nm < 2147483648 ∧
    rec_nmi < 2147483648 ∧
    p₀.nP + 1 + p₀.ctors.length + p₀.nIdx + 1 < 4294967296 ∧
    ∀ cA ∈ front.ctorsA,
      p₀.nP + cA.2 < 2147483648 ∧
      p₀.nP + 1 + p₀.ctors.length + 2 * cA.2 < 4294967296 ∧
      ∀ i < cA.2,
        p₀.nP + 1 + p₀.ctors.length + 2 * cA.2 +
          (Ix.Kernel.structFieldTeleOf cA.1.type p₀.nP cA.2 i).length < 4294967296
  rcRep_rec : RCRep front.t front.lim₀ h_rec rc_rec
  bpRep_rec : Bytes.RepAddressRef addrTy h_rec front.b₀ bp_rec
  apRep_rec : Bytes.RepAddressRef addrTy h_rec bRec ap_rec
  ev_rec : ObsFn W "KernelCheck::check_const"
    [rc_rec, .construct kciEnum "Rec"
      [nl_rec, ty_rec, .field (rec_np : F), .field (rec_ni : F),
        .field (rec_nm : F), .field (rec_nmi : F),
        rules_rec, k_rec, .field 0, bp_rec, .field 1], ap_rec]
    h_rec r_rec h_rec' cs_rec
  sub_rec : ∀ x ∈ cs_rec, x ∈ calls
  unmodeled_rec :
    ∀ m₁ blk_v m₂ r_mod m₃ cs₁ cs₂,
      ObsFn W "KernelModeled::rec_family_block" [ap_rec] m₁ blk_v m₂ cs₁ →
      ObsFn W "KernelModeled::block_is_modeled" [blk_v] m₂ r_mod m₃ cs₂ →
      (∀ x ∈ cs₁, x ∈ cs_rec) →
      (∀ x ∈ cs₂, x ∈ cs_rec) →
      r_mod = .field 0
  parent_ind_load :
    ∀ (v_par p_par : SourceValue F) (m_a m_b m_c : Heap F) (cs_rpa cs_gci : List (Call F)),
      ObsFn W "KernelCheck::rec_to_parent_addr"
        [ty_rec, .field (rec_np : F), .field (rec_nm : F),
          .field (rec_nmi : F), .field (rec_ni : F)]
        m_a v_par m_b cs_rpa →
      ObsFn W "Ingress::get_ci" [v_par] m_b p_par m_c cs_gci →
      (∀ x ∈ cs_rpa, x ∈ cs_rec) →
      (∀ x ∈ cs_gci, x ∈ cs_rec) →
      ∃ (bT' b_p : Bytes.Address) (pty_par u_par blk_par : SourceValue F),
        Bytes.RepAddressRef addrTy m_b bT' v_par ∧
        ixAddr bT' = iprjAddr (ixAddr front.b₀) 0 ∧
        loadValue m_c p_par = .ok (.construct kciEnum "Induct"
          [.field (p₀.cvT.levelParams.length : F), pty_par,
            .field (p₀.nP : F), .field (p₀.nIdx : F), .field (p₀.ctors.length : F),
            u_par, blk_par, .field 0]) ∧
        Bytes.RepAddressRef addrTy m_c b_p blk_par ∧
        ixAddr b_p = ixAddr front.b₀ ∧
        (∀ d Γ, RawTmExact (keyOf front.t) d Γ m_c 0 rawT
          (posOf front.cvTa₀.levelParams front.cvTa₀.type) pty_par)
  cload_rec : CtorLoadAt front.t front.b₀ p₀.nP cs_rec p₀.ctors front.ctorsA front.ctorRawTypes
  good₁_rec : Good ⟨front.E₁, ⟨.indInfo front.cvTa₀ {} :: env.consts⟩, front.t, front.lim₀⟩ cs_rec
  roles_rec : CtxRoleFacts
    ⟨E_rec, Ix.Kernel.consSumCtors p₀.nP front.ctorsA ⟨.indInfo front.cvTa₀ {} :: env.consts⟩,
      front.t, front.lim₀⟩
  lf_rec : LoadFacts
    ⟨E_rec, Ix.Kernel.consSumCtors p₀.nP front.ctorsA ⟨.indInfo front.cvTa₀ {} :: env.consts⟩,
      front.t, front.lim₀⟩
  good_rec : Good
    ⟨E_rec, Ix.Kernel.consSumCtors p₀.nP front.ctorsA ⟨.indInfo front.cvTa₀ {} :: env.consts⟩,
      front.t, front.lim₀⟩ cs_rec

/-- Hypothesis bundle for native one-type inductive blocks with recursor,
collecting the shared front-end parameter/positivity obligations and `PosSortLift`. -/
structure NativeWithRecExtra (calls : List (Call F)) (env : Ix.Kernel.Env .anon)
    (block : List KConstantInfo) (p₀ : Ix.Kernel.NativeParts .anon) where
  witness : NativeWithRecWitness calls env block p₀
  doms_bridge :
    ∀ cA ∈ witness.front.ctorsA,
      StructDomsShared ⟨.indInfo witness.front.cvTa₀ {} :: env.consts⟩
        witness.front.cvTa₀.type cA.1.type p₀.nP →
      ∀ fvsP crest tfvs trest cbs cbody tbs tbody,
        Ix.Kernel.openPisAtFvars p₀.nP cA.1.type 0 = some (fvsP, crest) →
        Ix.Kernel.openPisAtFvars p₀.nP witness.front.cvTa₀.type 0 = some (tfvs, trest) →
        witness.front.cvTa₀.type.stripPis p₀.nP = some (tbs, tbody) →
        cA.1.type.stripPis p₀.nP = some (cbs, cbody) →
        (¬ ∀ i < p₀.nP, (cbs.getD i default).1 = (tbs.getD i default).1) →
        StructDomsJ rulesJ ⟨.indInfo witness.front.cvTa₀ {} :: env.consts⟩
          0 fvsP (tfvs.map Expr.fvarTypeD) p₀.nP ∧
          (∀ p < p₀.nP, (cbs.getD p default).1.mentionsConst p₀.cvT.name = false)
  unused_later :
    ∀ cA ∈ witness.front.ctorsA, ∀ cbs body,
      cA.1.type.stripPis (p₀.nP + cA.2) = some (cbs, body) →
      ∀ i < cA.2,
        (Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
           (cbs.getD (p₀.nP + i) default).1 = .recursive ∨
         Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
           (cbs.getD (p₀.nP + i) default).1 = .reflexive) →
        Ix.Kernel.structUsedLater cA.1.type p₀.nP i = false
  pos_sort_lift :
    p₀.large = true →
      PosSortLift
        (Ix.Kernel.consSumCtors p₀.nP witness.front.ctorsA
          ⟨.indInfo witness.front.cvTa₀ {} :: env.consts⟩)
        witness.cvRa₀

/-- `KernelCheck::check_recursor_canonical_full` certifies the large-eliminator guard + field-sort
upgrade (`is_large_eliminator_one_spec` when `large = true`) and delegates to `nat_rec_check_spec`
to establish `structRecTyR` and `structRecRhsR` up to `WrapRelSem`. -/
theorem check_recursor_canonical_full_spec
    (hLevels : IxVM.Consistency.Levels) (hCore : IxVM.Consistency.Core S₀)
    {t : Ix.Kernel.RoleTable} {lim₀ : Option Nat}
    {E₁ E_rec : Ixon.Env} {envI₀ env_base₀ : Ix.Kernel.Env .anon}
    {cst : Ixon.Constant} {ind : Ixon.Inductive} {rec_m : Ixon.Recursor}
    {T recC : KKey} {b₀ bT bRec : Bytes.Address} {k nP nIdx : Nat} {large : Bool}
    {resSort : KLevel} {cvTa : KConstantVal}
    {ctors ctorsA : List (KConstantVal × Nat)} {ctorRawTypes : List KExpr}
    {sortss₀ : List (List KLevel)} {kinds : List (List Ix.Kernel.RecFieldKind)}
    {rawT rec_ty₀ : KExpr}
    {rbs₀ tbs₀ : List (KExpr × Ix.Kernel.BinderMeta)} {rbody₀ : KExpr}
    {rls : List (RecRule .anon)} {cs_root : List (Call F)}
    {x_rc x_ty x_n_mot x_n_min x_rules w_k w_u x_rec_blk w_ridx : SourceValue F}
    {x_pty w_pu x_block x_addr x_parent_addr r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hef₁ : EnvFacts ⟨E₁, envI₀, t, lim₀⟩)
    (hlf₁ : LoadFacts ⟨E₁, envI₀, t, lim₀⟩)
    (hg₁ : Good ⟨E₁, envI₀, t, lim₀⟩ cs)
    (hc_rec : CoreFacts ⟨E_rec, env_base₀, t, lim₀⟩)
    (hg_rec : Good ⟨E_rec, env_base₀, t, lim₀⟩ cs)
    (hT_ind : ∃ cv caps, env_base₀.find? T = some (.indInfo cv caps))
    (hrec_at : Ix.Cert.recordAt E_rec (ixAddr b₀) = some cst)
    (hcst_info : cst.info = .muts #[.indc ind, .recr rec_m])
    (hbRec_addr : ixAddr bRec = rprjAddr (ixAddr b₀) 1)
    (hT : keyOf t (ixAddr bT) = T)
    (hκ_inj : ∀ a : Bytes.Address, keyOf t (ixAddr a) = T → a = bT)
    (hRec : keyOf t (ixAddr bRec) = recC)
    (hk_lt : k < 2147483648)
    (hnP_lt : nP < 2147483648)
    (hnIdx_lt : nIdx < 2147483648)
    (hnCtors_lt : ctors.length < 2147483648)
    (hnall_lt : nP + 1 + ctors.length + nIdx + 1 < 4294967296)
    (hnPF_lt : ∀ cA ∈ ctorsA, nP + cA.2 < 2147483648)
    (hlps_ctors : ∀ c ∈ ctors, c.1.levelParams = List.range k)
    (hlps_rawT : rawT.allLevelParamsDefined (List.range k) = true)
    (hlps_tty : cvTa.type.allLevelParamsDefined (List.range k) = true)
    (hsR_tty₀ : rawT.stripPis (nP + nIdx) = some (rbs₀, rbody₀))
    (hsT₀ : cvTa.type.stripPis (nP + nIdx) = some (tbs₀, .sort resSort))
    (hk_len : kinds.length = ctorsA.length)
    (hwf_all : ∀ info ∈ buildCtorsInfo ctorsA ctorRawTypes kinds,
      NatCtorInfoWf T k large nP nIdx ctors.length info)
    (hrls_len : rls.length = ctors.length)
    (hcload : CtorLoadAt t b₀ nP cs_root ctors ctorsA ctorRawTypes)
    (hsub : ∀ x ∈ cs, x ∈ cs_root)
    (hctors₀ : SumCtorsRunJ rulesJ envI₀ envI₀ T (List.range k) nP nIdx resSort
      (Level.isEquiv resSort .zero == some true) false cvTa ctors ctorsA sortss₀)
    (hrc : RCRep t lim₀ h x_rc)
    (hb₀_blk : Bytes.RepAddressRef addrTy h b₀ x_block)
    (hb₀_rec_blk : Bytes.RepAddressRef addrTy h b₀ x_rec_blk)
    (hbT : Bytes.RepAddressRef addrTy h bT x_parent_addr)
    (hbRec : Bytes.RepAddressRef addrTy h bRec x_addr)
    (hpty : RawTmExact (keyOf t) 0 (fun _ => default) h 0 rawT cvTa.type x_pty)
    (hrec_ty : Tm (keyOf t) 0 (fun _ => default) h 0
      (posOf (if large then k :: List.range k else List.range k) rec_ty₀) x_ty)
    (hrules : RulesRep (keyOf t) h
      (if large then k :: List.range k else List.range k) 0 x_rules rls)
    (ev : ObsFn W "KernelCheck::check_recursor_canonical_full"
      [x_rc,
        .construct kciEnum "Rec"
          [.field (((if large then k :: List.range k else List.range k).length : Nat) : F),
            x_ty, .field (nP : F), .field (nIdx : F), x_n_mot, x_n_min,
            x_rules, w_k, w_u, x_rec_blk, w_ridx],
        x_addr,
        .construct kciEnum "Induct"
          [.field (k : F), x_pty, .field (nP : F), .field (nIdx : F),
            .field (ctors.length : F), w_pu, x_block, .field 0],
        x_parent_addr]
      h r h' cs) :
    let rlps := if large then k :: List.range k else List.range k
    let elim := if large then k else 0
    let ctors4 := Ix.Kernel.nativeCtors4 ctorsA kinds
    x_n_mot = .field 1 ∧
    x_n_min = .field (ctors.length : F) ∧
    (large = true →
      (∀ φ : LevelParam → Nat, Level.eval φ resSort ≠ 0) ∨ ctors.length < 2) ∧
    (∃ sortss : List (List KLevel),
      SumCtorsRunJ rulesJ envI₀ envI₀ T (List.range k) nP nIdx resSort
        (Level.isEquiv resSort .zero == some true) large cvTa ctors ctorsA sortss) ∧
    (∃ recTy,
      Ix.Kernel.structRecTyR T (List.range k) elim large nP nIdx cvTa.type ctors4 = some recTy ∧
      WrapRelSem env_base₀.find? recTy rec_ty₀) ∧
    (∀ a_d ls_d,
      ForallRightHeadLvls h a_d ls_d (nP + 1 + ctors.length + nIdx) x_ty →
      ls_d = (List.range k).map (fun idx => Level.param ((if large then 1 else 0) + idx))) ∧
    ∀ idx (hlt : idx < rls.length) (hidx : idx < ctors4.length),
      (rls[idx]'hlt).nfields = (ctors4[idx]'hidx).2.1 ∧
      ∃ rhsG,
        Ix.Kernel.structRecRhsR T (List.range k) elim large nP nIdx cvTa.type ctors4
          recC (rlps.map .param) idx = some rhsG ∧
        WrapRelSem env_base₀.find? rhsG (rls[idx]'hlt).rhs := by
  intro rlps elim ctors4
  dsimp only [rlps, elim, ctors4]
  let c₁ : Ctx := ⟨E₁, envI₀, t, lim₀⟩
  let c_rec : Ctx := ⟨E_rec, env_base₀, t, lim₀⟩
  match Obs.«KernelCheck::check_recursor_canonical_full».obs ev with
  | .other (hne568 := hne) .. =>
    exact absurd rfl (hne [_, _, _, _, _, _, _, _] rfl)
  | .Induct (v271 := v271) (m272 := m272) (cs274 := cs274)
      (v280 := v280) (m281 := m281) (cs291 := cs291)
      (v296 := v296) (m329 := m329) (v341 := v341) (m342 := m342) (cs352 := cs352)
      (v359 := v359) (m389 := m389) (m417 := m417) (cs516 := cs516)
      (hv15 := hv15) (hv86 := hv86) (sg279 := sg279)
      (op325 := op325) (hm337 := hm337) (ev293 := ev293) (ev399 := ev399)
      (ev354 := ev354) (ev429 := ev429) (ev518 := ev518) (hc567 := hc) .. =>
    injection hv15 with _ _ hr_xs
    injection hr_xs with hr1 hr_xs; injection hr_xs with hr2 hr_xs
    injection hr_xs with hr3 hr_xs; injection hr_xs with hr4 hr_xs
    injection hr_xs with hr5 hr_xs; injection hr_xs with hr6 hr_xs
    injection hr_xs with hr7 hr_xs; injection hr_xs with hr8 hr_xs
    injection hr_xs with hr9 hr_xs; injection hr_xs with hr10 hr_xs
    injection hr_xs with hr11 _
    subst hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr11
    injection hv86 with _ _ hp_xs
    injection hp_xs with hp1 hp_xs; injection hp_xs with hp2 hp_xs
    injection hp_xs with hp3 hp_xs; injection hp_xs with hp4 hp_xs
    injection hp_xs with hp5 hp_xs; injection hp_xs with hp6 hp_xs
    injection hp_xs with hp7 hp_xs; injection hp_xs with hp8 _
    subst hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8
    have e_329 : Heap.Extends m272 m329 := by rw [hm337]; exact Heap.Extends.snoc m272 _
    have e_272_to_389 := e_329.trans (ev293.heap_extends.trans ev399.heap_extends)
    -- `Seg1` single-constructor option witness
    have hseg1 :
        Heap.Extends h m272 ∧
        (ctors.length = 1 →
          ∃ cA₀ xnl xcty w2 w3 w4 w5,
            ctorsA = [cA₀] ∧
            v271 = .tuple [.field 1,
              .construct kciEnum "Ctor"
                [xnl, xcty, w2, w3, w4, .field (nP : F), .field (cA₀.2 : F), w5]] ∧
            Tm (keyOf t) 0 (fun _ => default) m389 0 cA₀.1.type xcty) := by
      cases sg279 with
      | n1 v143 m144 p151 cs157 _ ev159 ld153 he187 he201 hc202 =>
        subst he187 he201 hc202
        refine ⟨ev159.heap_extends, fun hlen1 => ?_⟩
        have hsub157 : ∀ x ∈ cs157, x ∈ cs_root := fun x hx =>
          hsub x (by simp [hc, hx])
        obtain ⟨c₀, cvCa₀, hc₀, hcA₀, hvs₀, hload₀⟩ := hcload.2 0 (by omega)
        obtain ⟨nl', cty', cblk', cnp', cnf', b_c, ld_c', hb_c, hix_c, hraw_rep, hci_rep⟩ :=
          hload₀ x_block p151 h m272 cs157 hsub157 hb₀_blk ev159
        rw [ld_c'] at ld153
        injection ld153 with hv143_eq
        subst hv143_eq
        obtain ⟨_, hnp_f, hnf_f, _⟩ :=
          CIRepExact.ctor_key_and_nf (by decide) hb_c hix_c hci_rep
        subst hnp_f hnf_f
        have hctorsA_len : ctorsA.length = 1 := by rw [hcload.1, hlen1]
        have hctorsA_eq : ctorsA = [(cvCa₀, c₀.2)] := by
          cases ctorsA with
          | nil => simp at hctorsA_len
          | cons hd tl =>
            simp only [List.length_cons, Nat.succ.injEq, List.length_eq_zero_iff] at hctorsA_len
            subst hctorsA_len
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hcA₀
            rw [hcA₀]
        have hlps_c₀ : cvCa₀.levelParams = List.range k := by
          rw [hvs₀.2.1]
          exact hlps_ctors c₀ (List.mem_of_getElem? hc₀)
        have hcty_tm : Tm (keyOf t) 0 (fun _ => default) m272 0 cvCa₀.type cty' := by
          have h0 := (hraw_rep 0 (fun _ => default)).toTmExact
          rw [hlps_c₀, posOf_range] at h0
          exact h0.toTm
        exact ⟨(cvCa₀, c₀.2), nl', cty', cblk', .field 0, .field ((0 : Nat) : F), .field 0,
          hctorsA_eq, rfl, hcty_tm.mono e_272_to_389⟩
      | other m237 m251 hne203 _ hm245 hm259 he269 _ =>
        subst he269
        have e_251 : Heap.Extends h m251 := by rw [hm259]; exact Heap.Extends.snoc h _
        have e_272 : Heap.Extends m251 m272 := by rw [hm245]; exact Heap.Extends.snoc m251 _
        refine ⟨e_251.trans e_272, fun hlen1 => ?_⟩
        rw [hlen1, Nat.cast_one] at hne203
        exact absurd rfl hne203
    rcases hseg1 with ⟨e_h_272, hopt⟩
    -- `get_result_sort_level`
    rw [evalBinOp_add_nat nP nIdx op325] at ev293
    have hty_nil_329 : TypesRep c₁.κ (fun _ => default) m329 0
        (.ptr (.enum kexprListEnum) m272.length) := by
      rw [hm337]; exact typesRep_alloc_nil c₁.κ (fun _ => default) m272
    have hg₁_grs : Good c₁ cs291 := hg₁.sub (fun x hx => by simp [hc, hx])
    have e_h_329 := e_h_272.trans e_329
    obtain ⟨ind_lvl', hpind', hsort_lveq'⟩ :=
      get_result_sort_level_spec hCore (c := c₁) (nP + nIdx) (by omega)
        (hrc.mono e_h_329) hty_nil_329 (ghostScoped_zero _) hef₁ hlf₁ hg₁_grs
        (hpty.toTmExact.mono e_h_329).toTm ev293
    have hres_eq' : LvEq resSort ind_lvl' := hsort_lveq' tbs₀ resSort hsT₀
    -- Pin `v341 = .field ((if large then 1 else 0 : Nat) : F)` via `nat_rec_check` header
    have hv341_eq : v341 = .field ((if large then 1 else 0 : Nat) : F) := by
      match Obs.«KernelCheck::nat_rec_check».obs ev518 with
      | .run (v138 := v138_p) (hv11 := hv11_p) (hv81 := hv81_p)
          (op159 := op159_p) (heq162 := heq162_p) .. =>
        injection hv11_p with _ _ hr_p
        injection hr_p with hnl_p _
        injection hv81_p with _ _ hp_p
        injection hp_p with hpnl_p _
        rw [← hnl_p] at heq162_p
        rw [← hpnl_p] at op159_p
        cases v341 with
        | ptr _ _ | tuple _ | construct _ _ _ => simp [evalBinOp] at op159_p
        | field u_f =>
          simp only [evalBinOp, Except.ok.injEq] at op159_p
          rw [← op159_p] at heq162_p
          cases large with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, List.length_range] at heq162_p ⊢
            have hf_eq : (k : F) + 0 = (k : F) + u_f := by
              rw [add_zero]; exact Value.field.inj heq162_p
            simp [add_left_cancel hf_eq]
          | true =>
            simp only [↓reduceIte, List.length_cons, List.length_range] at heq162_p ⊢
            have hf_eq : (k : F) + 1 = (k : F) + u_f := by
              simpa [Nat.cast_add] using Value.field.inj heq162_p
            simp [(add_left_cancel hf_eq).symm]
    -- `is_large_eliminator` when `large = true`
    have e_h_389 := e_h_272.trans e_272_to_389
    have hlarge_res :
        (large = true →
          (∀ φ : LevelParam → Nat, Level.eval φ resSort ≠ 0) ∨ ctors.length < 2) ∧
        (∃ sortss : List (List KLevel),
          SumCtorsRunJ rulesJ envI₀ envI₀ T (List.range k) nP nIdx resSort
            (Level.isEquiv resSort .zero == some true) large cvTa ctors ctorsA sortss) := by
      cases large with
      | false =>
        exact ⟨(fun h => nomatch h), ⟨sortss₀, hctors₀⟩⟩
      | true =>
        simp only [↓reduceIte] at hv341_eq
        rw [hv341_eq] at ev354
        have hg₁_lg : Good c₁ cs352 := hg₁.sub (fun x hx => by simp [hc, hx])
        obtain ⟨hguard, sortss_lg, hsum_lg⟩ :=
          is_large_eliminator_one_spec hLevels hCore (c := c₁) hef₁ hlf₁
            (Nat.lt_trans hnCtors_lt (by decide)) hnPF_lt
            (repKLevel_heapMono₂ ev399.heap_extends hpind') hres_eq'
            (hrc.mono e_h_389) hg₁_lg hctors₀ hopt ev354
        exact ⟨fun _ => hguard, ⟨sortss_lg, hsum_lg⟩⟩
    -- `nat_rec_check`
    rw [hv341_eq] at ev518
    have e_h_417 := e_h_389.trans (ev354.heap_extends.trans ev429.heap_extends)
    have hg_rec_516 : Good c_rec cs516 := hg_rec.sub (fun x hx => by simp [hc, hx])
    have hsub_516 : ∀ x ∈ cs516, x ∈ cs_root := fun x hx =>
      hsub x (by simp [hc, hx])
    let ctors_info := buildCtorsInfo ctorsA ctorRawTypes kinds
    have hinfo_len : ctors_info.length = ctors.length := by
      simp [ctors_info, hcload.1]
    have hnat_load : NatCtorLoad (keyOf t) b₀ k ctors_info x_block cs516 :=
      natCtorLoad_of_ctorLoadAt hcload hlps_ctors hnCtors_lt hk_len hsub_516
    have hpty_417 : RawTm (keyOf t) 0 (fun _ => default) m417 0
        (posOf (List.range k) rawT) (posOf (List.range k) cvTa.type) x_pty := by
      rw [posOf_range, posOf_range]
      exact (hpty.mono e_h_417).toRawTm
    have ev518' : ObsFn W "KernelCheck::nat_rec_check"
        [x_rc,
          .construct kciEnum "Rec"
            [.field (((if large then k :: List.range k else List.range k).length : Nat) : F),
              x_ty, .field (nP : F), .field (nIdx : F), x_n_mot, x_n_min,
              x_rules, w_k, w_u, x_rec_blk, w_ridx],
          x_addr,
          .construct kciEnum "Induct"
            [.field (k : F), x_pty, .field (nP : F), .field (nIdx : F),
              .field (ctors_info.length : F), w_pu, x_block, .field 0],
          x_parent_addr,
          .field ((if large then 1 else 0 : Nat) : F)]
        m417 r h' cs516 := by
      rwa [hinfo_len]
    obtain ⟨_, hmot_eq, hmin_eq, ⟨recTy, hrecTy, hwrap_ty⟩, hhead_eq, hrules_out⟩ :=
      nat_rec_check_spec (c := c_rec) hc_rec hc_rec.loads hT_ind
        hrec_at hcst_info hbRec_addr hT hκ_inj hRec
        hk_lt hnP_lt hnIdx_lt (by rw [hinfo_len]; exact hnCtors_lt)
        (by rw [hinfo_len]; exact hnall_lt)
        hlps_rawT hlps_tty hsR_tty₀ hsT₀
        (by rw [hinfo_len]; exact hwf_all)
        (by rw [hinfo_len]; exact hrls_len)
        hnat_load hg_rec_516 hg_rec_516.2
        (Bytes.repAddressRef_heapMono₂ addrTy e_h_417 hb₀_blk)
        (Bytes.repAddressRef_heapMono₂ addrTy e_h_417 hb₀_rec_blk)
        (Bytes.repAddressRef_heapMono₂ addrTy e_h_417 hbT)
        (Bytes.repAddressRef_heapMono₂ addrTy e_h_417 hbRec)
        hpty_417 (hrec_ty.mono e_h_417) (hrules.mono e_h_417) ev518'
    rw [hinfo_len] at hmin_eq hhead_eq
    have hmap_ctors4 :
        ctors_info.map (fun info => (info.1, info.2.1, info.2.2.2.1, info.2.2.2.2)) =
        Ix.Kernel.nativeCtors4 ctorsA kinds :=
      buildCtorsInfo_map_eq_nativeCtors4 hk_len
    rw [hmap_ctors4] at hrecTy
    have hhead_h :
        ∀ a_d ls_d,
          ForallRightHeadLvls h a_d ls_d (nP + 1 + ctors.length + nIdx) x_ty →
          ls_d = (List.range k).map (fun idx => Level.param ((if large then 1 else 0) + idx)) :=
      fun a_d ls_d hr => hhead_eq a_d ls_d (hr.mono e_h_417)
    refine ⟨hmot_eq, hmin_eq, hlarge_res.1, hlarge_res.2, ⟨recTy, hrecTy, hwrap_ty⟩, hhead_h, ?_⟩
    intro idx hlt hidx4
    have hidx_info : idx < ctors_info.length := by
      have hlen4 : (Ix.Kernel.nativeCtors4 ctorsA kinds).length = ctors_info.length := by
        rw [← hmap_ctors4, List.length_map]
      omega
    obtain ⟨hnf_idx, rhsG, hrhsG, hwrap_rhs⟩ := hrules_out idx hlt hidx_info
    rw [hmap_ctors4] at hrhsG
    have h21_eq :
        (ctors_info[idx]'hidx_info).2.1 =
          ((Ix.Kernel.nativeCtors4 ctorsA kinds)[idx]'hidx4).2.1 := by
      have hget := congrArg (fun xs => xs[idx]?) hmap_ctors4
      rw [List.getElem?_map, List.getElem?_eq_getElem hidx_info, Option.map_some,
        List.getElem?_eq_getElem hidx4, Option.some.injEq] at hget
      exact congrArg (fun x => x.2.1) hget
    rw [h21_eq] at hnf_idx
    exact ⟨hnf_idx, rhsG, hrhsG, hwrap_rhs⟩

private theorem check_rec_rules_wellscoped_spec {κ : _root_.Address → KKey}
    {rlps : List LevelParam} (hnl : rlps.length < 4294967296)
    (hperm : rlps.Perm (List.range rlps.length)) :
    ∀ {j : Nat} {x_rules x_depth r : SourceValue F} {rls : List (RecRule .anon)}
      {h h' : Heap F} {cs : List (Call F)},
      RulesRepExact κ h rlps j x_rules rls →
      ObsFn W "KernelCheck::check_rec_rules_wellscoped"
        [x_rules, x_depth, .field (rlps.length : F)] h r h' cs →
      ∀ rl ∈ rls, rl.rhs.allLevelParamsDefined rlps = true
  | _, _, _, _, [], _, _, _, .nil _, _ => by
    intro _ hmem; cases hmem
  | _, _, _, _, rl :: _, h, _, _, .cons cell hr hrs, ev => by
    match Obs.«KernelCheck::check_rec_rules_wellscoped».obs ev with
    | .Nil (ld12 := ld12) .. =>
      have ld12' : loadValue h _ = .ok (.construct krrListEnum "Nil" []) := ld12
      exact (load_cell_ne cell ld12' (by decide)).elim
    | .Cons (x_rhs := x_rhs) (x_rest := x_rest) (ld12 := ld12)
        (ev87 := ev87) (ev116 := ev116) .. =>
      have ld12' : loadValue h _ = .ok (.construct krrListEnum "Cons" [_, x_rest]) := ld12
      obtain ⟨-, hxs⟩ := load_cell cell ld12'
      injection hxs with hmk hxs; injection hxs with hrest_eq; subst hrest_eq
      obtain ⟨rhs_p, hmk_eq, _, hrhs_tmC⟩ := hr
      rw [hmk] at hmk_eq
      injection hmk_eq with _ _ hmk_args
      injection hmk_args with _ hmk_args
      injection hmk_args with _ hmk_args
      injection hmk_args with hrhs_eq
      subst hrhs_eq
      have hlpd_pos := validate_expr_well_scoped_spec hnl
        (hrhs_tmC 0 (fun _ => default)) ev87
      have hlpd_rl : rl.rhs.allLevelParamsDefined rlps = true :=
        allLevelParamsDefined_of_posOf_perm hperm hlpd_pos
      have ih_rest := check_rec_rules_wellscoped_spec hnl hperm
        (hrs.mono ev87.heap_extends) ev116
      intro rl' hmem
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact hlpd_rl
      · exact ih_rest rl' hmem'

private theorem collect_spine_exact_head {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelTypes::collect_spine" →
      ∀ (k : Nat) (E : KExpr) (x_e x_head x_sp : SourceValue F),
        args = [x_e] → r = .tuple [x_head, x_sp] →
        TmExact κ d Γ h k E x_e →
        ∃ H,
          E.getAppFn = H.getAppFn ∧
          TmExact κ d Γ h' k H x_head ∧
          (∀ h₂ a ls, Heap.Extends h' h₂ →
            AppHeadConstLvls h₂ a ls x_head → AppHeadConstLvls h₂ a ls x_e) :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' _ => fname = "KernelTypes::collect_spine" →
      ∀ (k : Nat) (E : KExpr) (x_e x_head x_sp : SourceValue F),
        args = [x_e] → r = .tuple [x_head, x_sp] →
        TmExact κ d Γ h k E x_e →
        ∃ H,
          E.getAppFn = H.getAppFn ∧
          TmExact κ d Γ h' k H x_head ∧
          (∀ h₂ a ls, Heap.Extends h' h₂ →
            AppHeadConstLvls h₂ a ls x_head → AppHeadConstLvls h₂ a ls x_e))
    (fun fname args h r h' _ ev ih hfn k E x_e x_head x_sp hargs hr htm => by
      subst hfn hargs
      match Obs.«KernelTypes::collect_spine».obs ev with
      | .other (he115 := hr') (hm132 := hm) (he136 := he) .. =>
        subst he hm
        rw [hr'] at hr
        injection hr with hlist; injection hlist with hhead _
        subst hhead
        exact ⟨E, rfl, htm.mono (Heap.Extends.snoc _ _), fun _ _ _ _ hh => hh⟩
      | .App (x_f := xf) (x_a := xa) (m31 := m31) (cs41 := cs41)
          (x_head := xh) (x_args := xargs) (cs86 := cs86) (ld12 := ld) (ev43 := e1)
          (he69 := hr') (ev88 := e2) (he105 := he) (hc106 := hc) .. =>
        subst he hc
        rw [hr'] at hr
        injection hr with hlist; injection hlist with hhead _
        subst hhead
        cases htm with
        | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _
        | const cell _ _ | lam cell _ _ _ | forallE cell _ _ _
        | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _
        | proj cell _ _ =>
          exact (load_cell_ne cell ld (by decide)).elim
        | app cell rf _ =>
          obtain ⟨-, hxs⟩ := load_cell cell ld
          injection hxs with hxf _
          rw [hxf] at rf
          have hlt : cs41.length <
              (((⟨"KernelTypes::collect_spine", [xf], h⟩ : Call F) ::
                (cs41 ++ ((⟨Obs.Names.«Lists::snoc<&KernelTypes::KExprNode>», [xargs, xa], m31⟩ : Call F) :: cs86)))).length := by
            simp only [List.length_cons, List.length_append]; omega
          obtain ⟨H, hfn_f, hH, hwrap⟩ := ih _ _ _ _ _ _ hlt e1 rfl k _ xf xh xargs rfl rfl rf
          exact ⟨H, hfn_f, hH.mono e2.heap_extends,
            fun h₂ a ls ext₂ hh =>
              .app ((e1.heap_extends.trans (e2.heap_extends.trans ext₂)).getElem?_eq cell)
                (by rw [hxf]; exact hwrap h₂ a ls (e2.heap_extends.trans ext₂) hh)⟩)

private theorem peel_n_foralls_exact {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (m : Nat) {n : F} {x_e r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
      {k : Nat} {T : KExpr},
      ZMod.val n = m →
      TmExact κ d Γ h k T x_e →
      ObsFn W "KernelCheck::peel_n_foralls" [x_e, .field n] h r h' calls →
      h' = h ∧ ∃ (bs : List (KExpr × Ix.Kernel.BinderMeta)) (B : KExpr),
        T.stripPis m = some (bs, B) ∧ TmExact κ d Γ h (k + m) B r ∧
        (∀ h₂ a ls, Heap.Extends h h₂ →
          ForallRightHeadLvls h₂ a ls 0 r → ForallRightHeadLvls h₂ a ls m x_e)
  | 0, n, x_e, r, h, h', _, k, T, hval, hT, ev => by
    have hn0 : n = 0 := (ZMod.val_eq_zero n).mp hval
    rw [hn0] at ev
    cases Obs.«KernelCheck::peel_n_foralls».obs ev with
    | n0 _ hr hh _ =>
      subst hr hh
      exact ⟨rfl, [], T, rfl, by simpa using hT, fun _ _ _ _ hh => hh⟩
    | other _ _ _ _ _ hne19 _ _ _ _ =>
      exact (hne19 rfl).elim
  | m + 1, n, x_e, r, h, h', _, k, T, hval, hT, ev => by
    have hn0 : n ≠ 0 := by intro e; rw [e] at hval; simp at hval
    cases Obs.«KernelCheck::peel_n_foralls».obs ev with
    | n0 hv14 _ _ _ =>
      exact (hn0 (Value.field.inj hv14)).elim
    | other _ x_body _ _ v66 _ ld34 op87 ev64 _ =>
      cases hT with
      | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _
      | const cell _ _ | app cell _ _ | lam cell _ _ _
      | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _
      | proj cell _ _ =>
        exact (load_cell_ne cell ld34 (by decide)).elim
      | @forallE _ _ _ _ _ T_p _ ℓ_p cell _ rb _ =>
        obtain ⟨-, hxs⟩ := load_cell cell ld34
        injection hxs with _ hxs; injection hxs with hxb _
        rw [hxb] at rb
        have hv66 : v66 = .field (n - 1) := by
          simp only [evalBinOp, Except.ok.injEq] at op87
          exact op87.symm
        rw [hv66] at ev64
        have hval' : ZMod.val (n - 1) = m := by
          have hs := Lib.val_sub_one hn0
          omega
        obtain ⟨rfl, bs, B, hstrip, hB, hwrap⟩ := peel_n_foralls_exact m hval' rb ev64
        refine ⟨rfl, (T_p, bmeta ℓ_p) :: bs, B, ?_, ?_, fun h₂ a ls ext₂ hh =>
          .succ (ext₂.getElem?_eq cell) (by rw [hxb]; exact hwrap h₂ a ls ext₂ hh)⟩
        · simp [Ix.Kernel.Expr.stripPis, hstrip]
        · rwa [show k + (m + 1) = k + 1 + m by omega]

private theorem getAppFn_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ (e : KExpr),
      (e.instantiateLevelParams ks us).getAppFn =
        e.getAppFn.instantiateLevelParams ks us
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _
  | .lam _ _ _ | .forallE _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ => rfl
  | .app f _ => getAppFn_instantiateLevelParams ks us f

private theorem rec_to_parent_addr_head_lvls {κ : _root_.Address → KKey}
    {np nm nmi ni : Nat} {E : KExpr} {x_ty r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hsum_lt : np + nm + nmi + ni < 4294967296)
    (hT : TmExact κ 0 (fun _ => default) h 0 E x_ty)
    (ev : ObsFn W "KernelCheck::rec_to_parent_addr"
      [x_ty, .field (np : F), .field (nm : F), .field (nmi : F), .field (ni : F)]
      h r h' calls) :
    ∃ a_d ls_d,
      ForallRightHeadLvls h' a_d ls_d (np + nm + nmi + ni) x_ty ∧
      ∀ bs dom B bm,
        E.stripPis (np + nm + nmi + ni) = some (bs, .forallE dom B bm) →
        dom.getAppFn = .const (κ (ixAddr a_d)) ls_d := by
  obtain ⟨v1, x9, x17, v37, m38, _, x_major_ty, _, _, m104, _, x_head, w132, x_caddr,
    w162, op32, op24, op16, ev50, ld78, ev117, ld154, _, he175, _⟩ :=
    Obs.«KernelCheck::rec_to_parent_addr».obs ev
  have hx17 : x17 = .field ((np + nm : Nat) : F) := by
    simp only [evalBinOp, Except.ok.injEq, Nat.cast_add] at op32 ⊢; exact op32.symm
  rw [hx17] at op24
  have hx9 : x9 = .field ((np + nm + nmi : Nat) : F) := by
    simp only [evalBinOp, Except.ok.injEq, Nat.cast_add] at op24 ⊢; exact op24.symm
  rw [hx9] at op16
  have hv1 : v1 = .field ((np + nm + nmi + ni : Nat) : F) := by
    simp only [evalBinOp, Except.ok.injEq, Nat.cast_add] at op16 ⊢; exact op16.symm
  rw [hv1] at ev50
  have hval : ZMod.val (((np + nm + nmi + ni : Nat) : F)) = np + nm + nmi + ni :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hsum_lt (by decide))
  obtain ⟨rfl, bs₀, B_peel, hstrip₀, hB_peel, hwrap_peel⟩ :=
    peel_n_foralls_exact (np + nm + nmi + ni) hval hT ev50
  cases hB_peel with
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _
  | const cell _ _ | app cell _ _ | lam cell _ _ _
  | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _
  | proj cell _ _ =>
    exact (load_cell_ne cell ld78 (by decide)).elim
  | forallE cell_maj rt_maj _ _ =>
    obtain ⟨-, hxs⟩ := load_cell cell_maj ld78
    injection hxs with hxm _
    rw [hxm] at rt_maj
    obtain ⟨H, hfn_dom, hH, hwrap_sp⟩ :=
      collect_spine_exact_head _ _ _ _ _ _ ev117 rfl _ _ x_major_ty x_head w132 rfl rfl rt_maj
    cases hH with
    | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _
    | app cell _ _ | lam cell _ _ _ | forallE cell _ _ _
    | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _
    | proj cell _ _ =>
      exact (load_cell_ne cell ld154 (by decide)).elim
    | const cell_c ra_c rls_c =>
      have hhead_m104 : AppHeadConstLvls m104 _ _ x_major_ty :=
        hwrap_sp m104 _ _ (Heap.Extends.refl _) (.const cell_c ra_c rls_c)
      have hzero_m104 : ForallRightHeadLvls m104 _ _ 0 (.ptr (.enum kexprEnum) _) :=
        .zero (ev117.heap_extends.getElem?_eq cell_maj) (by rwa [hxm])
      have hpeel_m104 := hwrap_peel m104 _ _ ev117.heap_extends hzero_m104
      rw [← he175] at hpeel_m104
      refine ⟨_, _, hpeel_m104, ?_⟩
      intro bs dom B bm hs
      rw [hstrip₀] at hs
      injection hs with hp_eq
      have hB_eq := congrArg Prod.snd hp_eq
      dsimp only at hB_eq
      injection hB_eq with hdom_eq _ _
      rw [← hdom_eq]
      exact hfn_dom

/-- `KernelCheck::check_recursor_member` resolves the parent `Induct` record via `rec_to_parent_addr`
+ `Ingress::get_ci`, verifies rule count and non-aux parameter/index counts (`Seg1.other`), and
delegates to `check_recursor_canonical_full_spec`. -/
theorem check_recursor_member_spec
    (hLevels : IxVM.Consistency.Levels) (hCore : IxVM.Consistency.Core S₀)
    {t : Ix.Kernel.RoleTable} {lim₀ : Option Nat}
    {E₁ E_rec : Ixon.Env} {envI₀ env_base₀ : Ix.Kernel.Env .anon}
    {cst : Ixon.Constant} {ind : Ixon.Inductive} {rec_m : Ixon.Recursor}
    {T recC : KKey} {b₀ bT bRec : Bytes.Address} {k nP nIdx : Nat} {large : Bool}
    {rec_np rec_ni rec_nm rec_nmi : Nat}
    {resSort : KLevel} {cvTa : KConstantVal}
    {ctors ctorsA : List (KConstantVal × Nat)} {ctorRawTypes : List KExpr}
    {sortss₀ : List (List KLevel)} {kinds : List (List Ix.Kernel.RecFieldKind)}
    {rawT rec_ty₀ : KExpr}
    {rbs₀ tbs₀ : List (KExpr × Ix.Kernel.BinderMeta)} {rbody₀ : KExpr}
    {rls : List (RecRule .anon)} {cs_root : List (Call F)}
    {x_rc x_ty x_rules w_k x_rec_blk x_addr r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hef₁ : EnvFacts ⟨E₁, envI₀, t, lim₀⟩)
    (hlf₁ : LoadFacts ⟨E₁, envI₀, t, lim₀⟩)
    (hg₁ : Good ⟨E₁, envI₀, t, lim₀⟩ cs)
    (hc_rec : CoreFacts ⟨E_rec, env_base₀, t, lim₀⟩)
    (hg_rec : Good ⟨E_rec, env_base₀, t, lim₀⟩ cs)
    (hT_ind : ∃ cv caps, env_base₀.find? T = some (.indInfo cv caps))
    (hrec_at : Ix.Cert.recordAt E_rec (ixAddr b₀) = some cst)
    (hcst_info : cst.info = .muts #[.indc ind, .recr rec_m])
    (hbT_addr : ixAddr bT = iprjAddr (ixAddr b₀) 0)
    (hbRec_addr : ixAddr bRec = rprjAddr (ixAddr b₀) 1)
    (hT : keyOf t (ixAddr bT) = T)
    (hκ_inj : ∀ a : Bytes.Address, keyOf t (ixAddr a) = T → a = bT)
    (hRec : keyOf t (ixAddr bRec) = recC)
    (hk_lt : k < 2147483648)
    (hnP_lt : nP < 2147483648)
    (hnIdx_lt : nIdx < 2147483648)
    (hnCtors_lt : ctors.length < 2147483648)
    (hrec_np_lt : rec_np < 2147483648)
    (hrec_ni_lt : rec_ni < 2147483648)
    (hrec_nm_lt : rec_nm < 2147483648)
    (hrec_nmi_lt : rec_nmi < 2147483648)
    (hnall_lt : nP + 1 + ctors.length + nIdx + 1 < 4294967296)
    (hnPF_lt : ∀ cA ∈ ctorsA, nP + cA.2 < 2147483648)
    (hlps_ctors : ∀ c ∈ ctors, c.1.levelParams = List.range k)
    (hlps_rawT : rawT.allLevelParamsDefined (List.range k) = true)
    (hlps_tty : cvTa.type.allLevelParamsDefined (List.range k) = true)
    (hsR_tty₀ : rawT.stripPis (nP + nIdx) = some (rbs₀, rbody₀))
    (hsT₀ : cvTa.type.stripPis (nP + nIdx) = some (tbs₀, .sort resSort))
    (hk_len : kinds.length = ctorsA.length)
    (hwf_all : ∀ info ∈ buildCtorsInfo ctorsA ctorRawTypes kinds,
      NatCtorInfoWf T k large nP nIdx ctors.length info)
    (hcload : CtorLoadAt t b₀ nP cs_root ctors ctorsA ctorRawTypes)
    (hparent :
      ∀ (v_par p_par : SourceValue F) (m_a m_b m_c : Heap F) (cs_rpa cs_gci : List (Call F)),
        ObsFn W "KernelCheck::rec_to_parent_addr"
          [x_ty, .field (rec_np : F), .field (rec_nm : F),
            .field (rec_nmi : F), .field (rec_ni : F)]
          m_a v_par m_b cs_rpa →
        ObsFn W "Ingress::get_ci" [v_par] m_b p_par m_c cs_gci →
        (∀ x ∈ cs_rpa, x ∈ cs_root) →
        (∀ x ∈ cs_gci, x ∈ cs_root) →
        ∃ (bT' b_p : Bytes.Address) (pty_par u_par blk_par : SourceValue F),
          Bytes.RepAddressRef addrTy m_b bT' v_par ∧
          ixAddr bT' = iprjAddr (ixAddr b₀) 0 ∧
          loadValue m_c p_par = .ok (.construct kciEnum "Induct"
            [.field (k : F), pty_par,
              .field (nP : F), .field (nIdx : F), .field (ctors.length : F),
              u_par, blk_par, .field 0]) ∧
          Bytes.RepAddressRef addrTy m_c b_p blk_par ∧
          ixAddr b_p = ixAddr b₀ ∧
          (∀ d Γ, RawTmExact (keyOf t) d Γ m_c 0 rawT cvTa.type pty_par))
    (hsub : ∀ x ∈ cs, x ∈ cs_root)
    (hctors₀ : SumCtorsRunJ rulesJ envI₀ envI₀ T (List.range k) nP nIdx resSort
      (Level.isEquiv resSort .zero == some true) false cvTa ctors ctorsA sortss₀)
    (hrc : RCRep t lim₀ h x_rc)
    (hb₀_rec_blk : Bytes.RepAddressRef addrTy h b₀ x_rec_blk)
    (hbRec : Bytes.RepAddressRef addrTy h bRec x_addr)
    (hrec_ty : TmExact (keyOf t) 0 (fun _ => default) h 0
      (posOf (if large then k :: List.range k else List.range k) rec_ty₀) x_ty)
    (hrules : RulesRepExact (keyOf t) h
      (if large then k :: List.range k else List.range k) 0 x_rules rls)
    (hrls_lt : rls.length < 2147483648)
    (ev : ObsFn W "KernelCheck::check_recursor_member"
      [x_rc,
        .construct kciEnum "Rec"
          [.field (((if large then k :: List.range k else List.range k).length : Nat) : F),
            x_ty, .field (rec_np : F), .field (rec_ni : F),
            .field (rec_nm : F), .field (rec_nmi : F),
            x_rules, w_k, .field 0, x_rec_blk, .field 1],
        x_addr]
      h r h' cs) :
    let rlps := if large then k :: List.range k else List.range k
    let elim := if large then k else 0
    let ctors4 := Ix.Kernel.nativeCtors4 ctorsA kinds
    rec_np = nP ∧
    rec_ni = nIdx ∧
    rec_nm = 1 ∧
    rec_nmi = ctors.length ∧
    rls.length = ctors.length ∧
    (large = true →
      (∀ φ : LevelParam → Nat, Level.eval φ resSort ≠ 0) ∨ ctors.length < 2) ∧
    (∃ sortss : List (List KLevel),
      SumCtorsRunJ rulesJ envI₀ envI₀ T (List.range k) nP nIdx resSort
        (Level.isEquiv resSort .zero == some true) large cvTa ctors ctorsA sortss) ∧
    (∃ recTy,
      Ix.Kernel.structRecTyR T (List.range k) elim large nP nIdx cvTa.type ctors4 = some recTy ∧
      WrapRelSem env_base₀.find? recTy rec_ty₀) ∧
    (∀ rl ∈ rls, rl.rhs.allLevelParamsDefined rlps = true) ∧
    (∀ bs dom B bm,
      rec_ty₀.stripPis (nP + 1 + ctors.length + nIdx) = some (bs, .forallE dom B bm) →
      ∃ K, dom.getAppFn = .const K ((List.range k).map .param)) ∧
    ∀ idx (hlt : idx < rls.length) (hidx : idx < ctors4.length),
      (rls[idx]'hlt).nfields = (ctors4[idx]'hidx).2.1 ∧
      ∃ rhsG,
        Ix.Kernel.structRecRhsR T (List.range k) elim large nP nIdx cvTa.type ctors4
          recC (rlps.map .param) idx = some rhsG ∧
        WrapRelSem env_base₀.find? rhsG (rls[idx]'hlt).rhs := by
  intro rlps elim ctors4
  dsimp only [rlps, elim, ctors4]
  match Obs.«KernelCheck::check_recursor_member».obs ev with
  | .run (v72 := v72) (m73 := m73) (cs83 := cs83) (m127 := m127) (p134 := p134) (cs140 := cs140)
      (v209 := v209) (m210 := m210) (m219 := m219) (m227 := m227)
      (v329 := v329) (m332 := m332) (m360 := m360) (m425 := m425)
      (m624 := m624) (m633 := m633) (m699 := m699) (cs731 := cs731)
      (hv15 := hv15) (ev85 := ev85) (ev142 := ev142) (ld136 := ld136)
      (ev238 := ev238) (ev252 := ev252) (ev274 := ev274) (heq317 := heq317)
      (ev342 := ev342) (heq358 := heq358) (ev372 := ev372) (ev437 := ev437)
      (sg631 := sg631) (ev645 := ev645) (ev711 := ev711) (ev733 := ev733) (hc774 := hc) .. =>
    injection hv15 with _ _ hr_xs
    injection hr_xs with hr1 hr_xs; injection hr_xs with hr2 hr_xs
    injection hr_xs with hr3 hr_xs; injection hr_xs with hr4 hr_xs
    injection hr_xs with hr5 hr_xs; injection hr_xs with hr6 hr_xs
    injection hr_xs with hr7 hr_xs; injection hr_xs with hr8 hr_xs
    injection hr_xs with hr9 hr_xs; injection hr_xs with hr10 hr_xs
    injection hr_xs with hr11 _
    subst hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr11
    have hsub_rpa : ∀ x ∈ cs83, x ∈ cs_root := fun x hx => hsub x (by simp [hc, hx])
    have hsub_gci : ∀ x ∈ cs140, x ∈ cs_root := fun x hx => hsub x (by simp [hc, hx])
    obtain ⟨bT', b_p, pty_par, u_par, blk_par, hbT'_73, hbT'_ix, ld_par, hb_p_127, hb_p_ix,
      hpty_127⟩ := hparent v72 p134 h m73 m127 cs83 cs140 ev85 ev142 hsub_rpa hsub_gci
    have hbT'_eq : bT' = bT := ixAddr_inj (hbT'_ix.trans hbT_addr.symm)
    have hb_p_eq : b_p = b₀ := ixAddr_inj hb_p_ix
    subst hbT'_eq hb_p_eq
    rw [ld_par] at ld136
    injection ld136 with hp_val
    injection hp_val with _ _ hp_xs
    injection hp_xs with hp1 hp_xs; injection hp_xs with hp2 hp_xs
    injection hp_xs with hp3 hp_xs; injection hp_xs with hp4 hp_xs
    injection hp_xs with hp5 hp_xs; injection hp_xs with hp6 hp_xs
    injection hp_xs with hp7 hp_xs; injection hp_xs with hp8 _
    subst hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8
    have e_73_127 := ev142.heap_extends
    have e_127_210 := ev238.heap_extends.trans (ev252.heap_extends.trans ev274.heap_extends)
    have e_h_210 := ev85.heap_extends.trans (e_73_127.trans e_127_210)
    -- `Lists::length<KRecRule>` pins `rls.length = ctors.length`
    obtain ⟨hv329_eq, hm332_eq⟩ := rules_length_spec ev342 (hrules.mono e_h_210)
    rw [hv329_eq] at heq358
    have hrls_len : rls.length = ctors.length :=
      nat_eq_of_field_eq (Nat.lt_trans hrls_lt (by decide))
        (Nat.lt_trans hnCtors_lt (by decide)) heq358
    -- `Seg1` pins `rec_np = nP`, `rec_ni = nIdx`, and `Heap.Extends m425 m624`
    have hseg1 : rec_np = nP ∧ rec_ni = nIdx ∧ Heap.Extends m425 m624 := by
      cases sg631 with
      | n1 hv493 _ _ _ =>
        rw [heq317] at hv493
        exact absurd (Value.field.inj hv493.symm) one_ne_zero
      | other _ _ _ heq530 heq558 _ ev564 _ =>
        exact ⟨nat_eq_of_field_eq (Nat.lt_trans hrec_np_lt (by decide))
            (Nat.lt_trans hnP_lt (by decide)) heq530,
          nat_eq_of_field_eq (Nat.lt_trans hrec_ni_lt (by decide))
            (Nat.lt_trans hnIdx_lt (by decide)) heq558,
          ev564.heap_extends⟩
    rcases hseg1 with ⟨hnp_eq, hni_eq, e_425_624⟩
    subst hnp_eq hni_eq
    have e_210_332 : Heap.Extends m210 m332 := by rw [hm332_eq]
    have e_210_699 := e_210_332.trans (ev372.heap_extends.trans (ev437.heap_extends.trans
      (e_425_624.trans (ev645.heap_extends.trans ev711.heap_extends))))
    have e_127_699 := e_127_210.trans e_210_699
    have e_73_699 := e_73_127.trans e_127_699
    have e_h_699 := ev85.heap_extends.trans e_73_699
    have hg₁_731 : Good ⟨E₁, envI₀, t, lim₀⟩ cs731 :=
      hg₁.sub (fun x hx => by simp [hc, hx])
    have hg_rec_731 : Good ⟨E_rec, env_base₀, t, lim₀⟩ cs731 :=
      hg_rec.sub (fun x hx => by simp [hc, hx])
    have hsub_731 : ∀ x ∈ cs731, x ∈ cs_root := fun x hx =>
      hsub x (by simp [hc, hx])
    let rlps' := if large then k :: List.range k else List.range k
    have hnl_lt : rlps'.length < 4294967296 := by
      dsimp only [rlps']
      cases large <;> simp <;> omega
    have hrls_lpd : ∀ rl ∈ rls, rl.rhs.allLevelParamsDefined rlps' = true :=
      check_rec_rules_wellscoped_spec hnl_lt (rlps_perm k large)
        (hrules.mono (e_h_210.trans (e_210_332.trans ev372.heap_extends))) ev437
    obtain ⟨hmot_f, hmin_f, hlg_guard, hsum_out, hrecTy_out, hhead_f, hrules_out⟩ :=
      check_recursor_canonical_full_spec hLevels hCore
        hef₁ hlf₁ hg₁_731 hc_rec hg_rec_731 hT_ind
        hrec_at hcst_info hbRec_addr hT hκ_inj hRec
        hk_lt hnP_lt hnIdx_lt hnCtors_lt hnall_lt hnPF_lt
        hlps_ctors hlps_rawT hlps_tty hsR_tty₀ hsT₀ hk_len hwf_all hrls_len
        hcload hsub_731 hctors₀
        (hrc.mono e_h_699)
        (Bytes.repAddressRef_heapMono₂ addrTy e_127_699 hb_p_127)
        (Bytes.repAddressRef_heapMono₂ addrTy e_h_699 hb₀_rec_blk)
        (Bytes.repAddressRef_heapMono₂ addrTy e_73_699 hbT'_73)
        (Bytes.repAddressRef_heapMono₂ addrTy e_h_699 hbRec)
        ((hpty_127 0 (fun _ => default)).mono e_127_699)
        (hrec_ty.toTm.mono e_h_699)
        (hrules.toRulesRep.mono e_h_699)
        ev733
    have hnm_eq : rec_nm = 1 :=
      nat_eq_of_field_eq (Nat.lt_trans hrec_nm_lt (by decide))
        (by decide) hmot_f
    have hnmi_eq : rec_nmi = ctors.length :=
      nat_eq_of_field_eq (Nat.lt_trans hrec_nmi_lt (by decide))
        (Nat.lt_trans hnCtors_lt (by decide)) hmin_f
    have hmaj_lvls :
        ∀ bs dom B bm,
          rec_ty₀.stripPis (rec_np + 1 + ctors.length + rec_ni) = some (bs, .forallE dom B bm) →
          ∃ K, dom.getAppFn = .const K ((List.range k).map .param) := by
      have ev85' : ObsFn W "KernelCheck::rec_to_parent_addr"
          [x_ty, .field (rec_np : F), .field ((1 : Nat) : F),
            .field (ctors.length : F), .field (rec_ni : F)]
          h v72 m73 cs83 := by
        rwa [hnm_eq, hnmi_eq] at ev85
      obtain ⟨a_d, ls_d, hright_73, hdom_pos⟩ :=
        rec_to_parent_addr_head_lvls (by omega) hrec_ty ev85'
      have hls_d := hhead_f a_d ls_d (hright_73.mono e_73_699)
      intro bs dom B bm hs
      have hs_pos := ilp_stripPis rlps' (posLevels rlps') (rec_np + 1 + ctors.length + rec_ni) hs
      have hfn_pos := hdom_pos _ (posOf rlps' dom) (posOf rlps' B) _ hs_pos
      have hfn_pos' : posOf rlps' dom.getAppFn =
          posOf rlps' (.const (keyOf t (ixAddr a_d)) ((List.range k).map .param)) := by
        unfold posOf at hfn_pos ⊢
        rw [← getAppFn_instantiateLevelParams, hfn_pos, hls_d]
        simpa [rlps', Expr.instantiateLevelParams] using
          congrArg (Expr.const (keyOf t (ixAddr a_d))) (clvls_eq_subst_params k large)
      have hinv := congrArg
        (fun e => e.instantiateLevelParams (List.range rlps'.length) (rlps'.map .param))
        hfn_pos'
      rw [posOf_perm_inv (rlps_perm k large), posOf_perm_inv (rlps_perm k large)] at hinv
      exact ⟨keyOf t (ixAddr a_d), hinv⟩
    exact ⟨rfl, rfl, hnm_eq, hnmi_eq, hrls_len, hlg_guard, hsum_out, hrecTy_out,
      hrls_lpd, hmaj_lvls, hrules_out⟩

private theorem no_new_defn_consSumCtors (nP : Nat) :
    ∀ (ctorsA : List (KConstantVal × Nat)) {envₐ : Ix.Kernel.Env .anon}
      {n : KKey} {cv : KConstantVal} {v : KExpr} {hn : Ix.Kernel.ReducibilityHint},
      (Ix.Kernel.consSumCtors nP ctorsA envₐ).find? n = some (.defnInfo cv v hn) →
      envₐ.find? n = some (.defnInfo cv v hn)
  | [], _, _, _, _, _, h => h
  | c :: cs, envₐ, n, cv, v, hn, h => by
    have h₁ := no_new_defn_consSumCtors nP cs h
    rw [Ix.Kernel.Env.find?_cons] at h₁
    split at h₁
    · exact nomatch h₁
    · exact h₁

private theorem find?_consSumCtors_mem (nP : Nat) :
    ∀ (ctorsA : List (KConstantVal × Nat)) (envₐ : Ix.Kernel.Env .anon) {c : KConstantVal × Nat},
      (ctorsA.map (·.1.name)).Nodup →
      c ∈ ctorsA →
      (Ix.Kernel.consSumCtors nP ctorsA envₐ).find? c.1.name = some (.ctorInfo c.1 nP c.2)
  | [], _, _, _, hm => nomatch hm
  | x :: xs, envₐ, c, hnd, hm => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hm with rfl | hmem
    · have hne : ∀ y ∈ xs, y.1.name ≠ c.1.name := fun y hy he =>
        hnd.1 (by rw [← he]; exact List.mem_map.mpr ⟨y, hy, rfl⟩)
      rw [Ix.Kernel.consSumCtors, find?_consSumCtors_ne nP xs _ hne]
      exact Ix.Kernel.Env.find?_cons_self (.ctorInfo c.1 nP c.2) envₐ
    · exact find?_consSumCtors_mem nP xs _ hnd.2 hmem

private theorem sumSplit_map_ctor_append :
    ∀ (xs : List (KConstantVal × Nat × Nat)) (cvR : KConstantVal)
      (mI rP : Nat) (rls : List (RecRule .anon)),
      Ix.Kernel.sumSplit
        ((xs.map fun c => ConstantInfo.ctorInfo c.1 c.2.1 c.2.2) ++
          [.recInfo cvR mI rP rls]) =
        some (xs, cvR, mI, rP, rls)
  | [], _, _, _, _ => rfl
  | x :: xs, cvR, mI, rP, rls => by
    simp only [List.map_cons, List.cons_append, Ix.Kernel.sumSplit,
      sumSplit_map_ctor_append xs cvR mI rP rls, Option.map_some]

/-- **Deliverable 1 (`L5` Native One-Type Inductive Block with Recursor)**:
Refines an unpinned `.indDecl block nPd` with `Ix.Kernel.nativeParts? nPd block = some p₀` to
`InstallStep env (.indDecl block nPd) env₂` and `DeclNativeRunJ rulesJ env p₀ env₂`. -/
theorem nativeWithRec_step (hLevels : IxVM.Consistency.Levels) (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Ix.Kernel.Env .anon}
    {block : List KConstantInfo} {nPd : Nat} {p₀ : Ix.Kernel.NativeParts .anon}
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hparts : Ix.Kernel.nativeParts? nPd block = some p₀)
    (hS : DeclStoreInv env)
    (extra : NativeWithRecExtra calls env block p₀) :
    ∃ env₂,
      IxVM.Consistency.InstallStep env (.indDecl block nPd) env₂ ∧
      DeclNativeRunJ rulesJ env p₀ env₂ := by
  obtain ⟨caps₀_p, cs_p, mI_p, rP_p, rules_p, hblk_p, hnP_eq, hctors_p, hrhss_p,
    hbasis_T, hbasis_R, hcs_p, _⟩ := nativeParts?_withRec_inv hparts
  let w := extra.witness
  let wf := w.front
  let k := p₀.cvT.levelParams.length
  obtain ⟨caps₀, cs, mI, rP, hblk_w, hrP_w, hmI_w⟩ := w.rules_block
  -- Unify `w.rules_block` with `nativeParts?_withRec_inv`
  have hblk_eq := hblk_w.symm.trans hblk_p
  injection hblk_eq with hhead htail
  injection hhead with _ hcaps_eq
  simp only [List.append_eq] at htail
  have hsp_eq := congrArg Ix.Kernel.sumSplit htail
  rw [sumSplit_map_ctor_append, sumSplit_map_ctor_append] at hsp_eq
  injection hsp_eq with hprod_eq
  simp only [Prod.mk.injEq] at hprod_eq
  rcases hprod_eq with ⟨rfl, _, rfl, rfl, hrules_eq⟩
  subst hcaps_eq
  subst hrules_eq
  have hcs_map_eq :
      (cs.map fun c => (ConstantInfo.ctorInfo c.1 c.2.1 c.2.2 : KConstantInfo)) =
      p₀.ctors.map (fun c => (ConstantInfo.ctorInfo c.1 p₀.nP c.2 : KConstantInfo)) := by
    rw [hctors_p, List.map_map]
    refine List.map_congr_left fun c hc => ?_
    simp [(hcs_p c hc).1]
  have hblk_clean :
      block = .indInfo p₀.cvT caps₀ ::
        ((p₀.ctors.map fun c => (ConstantInfo.ctorInfo c.1 p₀.nP c.2 : KConstantInfo)) ++
          [.recInfo p₀.cvR mI rP w.rules₀]) := by
    refine hblk_w.trans ?_
    rw [hcs_map_eq, List.cons_append]
  -- Level parameter shape of `p₀.cvR` and `nativeRecLpsOk`
  have hlps_inv :
      p₀.cvR.levelParams = (if p₀.large then k :: List.range k else List.range k) ∧
      p₀.elim = (if p₀.large then k else 0) ∧
      Ix.Kernel.nativeRecLpsOk p₀.toInductiveShape = true := by
    rcases w.lps_R_or with hlps₀ | hlps₁
    · obtain ⟨hlg, hel, hok⟩ :=
        nativeParts?_lps_inv (large₀ := false) hparts wf.lps_T (by simpa using hlps₀)
      exact ⟨by rw [hlg]; simpa using hlps₀, by rw [hlg]; exact hel, hok⟩
    · obtain ⟨hlg, hel, hok⟩ :=
        nativeParts?_lps_inv (large₀ := true) hparts wf.lps_T (by simpa using hlps₁)
      exact ⟨by rw [hlg]; simpa using hlps₁, by rw [hlg]; exact hel, hok⟩
  rcases hlps_inv with ⟨hlps_R, helim_eq, hlps_ok⟩
  have hlps_Ta₀ : wf.cvTa₀.levelParams = List.range k := by
    rw [wf.valStored_T.2.1]; exact wf.lps_T
  have hlps_Ra₀ : w.cvRa₀.levelParams = if p₀.large then k :: List.range k else List.range k := by
    rw [w.valStored_R.2.1]; exact hlps_R
  -- Run shared `Induct` front-end pass
  obtain ⟨ind_lvl, sortss₀, fout⟩ := nativeFront_pass hLevels hCore hS wf
  obtain ⟨bsT, s₀, hst_Ta₀⟩ := w.former_sort
  obtain ⟨rbs₀, rbody₀, hsR_tty₀⟩ := w.rawT_strip
  let isProp₀ : Bool := (Level.isEquiv s₀ .zero == some true)
  let envI₀ : Ix.Kernel.Env .anon := ⟨.indInfo wf.cvTa₀ {} :: env.consts⟩
  obtain ⟨tbs, tbody, _, hst_Ta₀_P, _, _, _⟩ := stripPis_split p₀.nP p₀.nIdx hst_Ta₀
  obtain ⟨tfvsP, trestP, hopT_P⟩ :=
    Ix.Kernel.Model.openPisAtFvars_of_stripPis_isSome p₀.nP 0 (by rw [hst_Ta₀_P]; rfl)
  have hlveq : LvEq s₀ ind_lvl := fout.sort_lveq bsT s₀ hst_Ta₀
  have hbasis_Ta₀ : Ix.Kernel.reservedBasisNames.contains wf.cvTa₀.name = false := by
    rw [wf.valStored_T.1]; exact hbasis_T
  -- Per-constructor classification & `SumCtorRunJ` at `large = false` in `envI₀`
  have hctor_stage :
      ∀ (j : Nat) (c cA : KConstantVal × Nat),
        p₀.ctors[j]? = some c → wf.ctorsA[j]? = some cA →
        cA.2 = c.2 ∧ ∃ sorts ks,
          sortss₀[j]? = some sorts ∧
          SumCtorRunJ rulesJ envI₀ envI₀ p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx
            s₀ isProp₀ false c.1 c.2 wf.cvTa₀ cA.1 sorts ∧
          Ix.Kernel.recCtorKinds p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx cA = some ks ∧
          ks.length = cA.2 ∧
          (∀ k₀ ∈ ks, k₀ ≠ .negative ∧ k₀ ≠ .unsupported) ∧
          Ix.Kernel.nativeOpenedOk env p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx
            cA.1.type cA.2 ks = true := by
    intro j c cA hc hcA
    have hj : j < p₀.ctors.length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hc
      exact nomatch hc
    obtain ⟨c', cA', sorts, hc', hcA', hsorts, hout⟩ := fout.ctors_out j hj
    rw [hc] at hc'; injection hc' with hc_eq; cases hc_eq
    rw [hcA] at hcA'; injection hcA' with hcA_eq; cases hcA_eq
    have hcA_mem : cA ∈ wf.ctorsA := List.mem_of_getElem? hcA
    obtain ⟨_, _, cbs, es, _, _, hstrip_c, hcbs_len, hes_len, hes_noT, hpos_c, _⟩ := hout.residual
    obtain ⟨fvsP, crest, xFvs, idxArgs, hopP, hopF, hidx_len, hxFvs_res, hidx_res, hfsorts₀⟩ :=
      hout.opened
    obtain ⟨cbsP, cbodyP, _, hst_c_P, _, _, _⟩ := stripPis_split p₀.nP c.2 hstrip_c
    have hcbs_get_eq : ∀ i < p₀.nP, (cbsP.getD i default).1 = (cbs.getD i default).1 := by
      obtain ⟨cbs₁, _, cbs₂, hstP₁, _, hcbs_app, hlen₁⟩ := stripPis_split p₀.nP c.2 hstrip_c
      rw [hst_c_P] at hstP₁; injection hstP₁ with h1
      simp only [Prod.mk.injEq] at h1
      rcases h1 with ⟨rfl, _⟩
      intro i hi
      have hi₁ : i < cbsP.length := by omega
      have hi₂ : i < cbs.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₁,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₂]
      simp only [Option.getD_some]
      have hq : cbs[i]? = cbsP[i]? := by
        rw [← hcbs_app, List.getElem?_append_left hi₁]
      rw [List.getElem?_eq_getElem hi₂, List.getElem?_eq_getElem hi₁, Option.some.injEq] at hq
      exact congrArg Prod.fst hq.symm
    have hdoms_and_noT :
        StructDomsJ rulesJ envI₀ 0 fvsP (tfvsP.map Expr.fvarTypeD) p₀.nP ∧
          (∀ p < p₀.nP, (cbs.getD p default).1.mentionsConst p₀.cvT.name = false) := by
      by_cases hsame : ∀ i < p₀.nP, (cbsP.getD i default).1 = (tbs.getD i default).1
      · obtain ⟨hdj, hnoT⟩ :=
          structDomsJ_and_noT_of_same_doms hopP hopT_P hst_Ta₀_P hst_c_P fout.ta_noT hsame
        exact ⟨hdj, fun p hp => by rw [← hcbs_get_eq p hp]; exact hnoT p hp⟩
      · obtain ⟨hdj, hnoT⟩ :=
          extra.doms_bridge cA hcA_mem hout.domsShared fvsP crest tfvsP trestP cbsP cbodyP
            tbs tbody hopP hopT_P hst_Ta₀_P hst_c_P hsame
        exact ⟨hdj, fun p hp => by rw [← hcbs_get_eq p hp]; exact hnoT p hp⟩
    have hfsorts :
        FieldSortsJ rulesJ envI₀ isProp₀ false s₀ p₀.nP xFvs idxArgs c.2 sorts :=
      fieldSortsJ_congr_sort hlveq.symm hfsorts₀
    have hsum_c :
        SumCtorRunJ rulesJ envI₀ envI₀ p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx
          s₀ isProp₀ false c.1 c.2 wf.cvTa₀ cA.1 sorts :=
      ⟨⟨cA.1, hout.cvCheck, Or.inl rfl⟩,
        ⟨cbs, es, hstrip_c, hes_len⟩,
        fvsP, crest, tfvsP, trestP, xFvs, idxArgs,
        hopP, hopT_P, hdoms_and_noT.1, hopF, hidx_len, hxFvs_res, hidx_res, hfsorts⟩
    obtain ⟨sty_c, _, hinf_c, _⟩ := hout.inferSort
    have hfv_c : cA.1.type.hasFvar = false :=
      annotates_hasFvar_false hout.stored.2.2 (wf.fv_ctors c (List.mem_of_getElem? hc))
    have hres_c : cA.1.type.constsResolve envI₀ = true := by
      obtain ⟨ty', ⟨_, _, _, _, _, _, _, _, hcr, _⟩, hcv⟩ := hout.cvCheck
      have hty_eq : cA.1.type = ty' := by rw [hcv]
      rwa [hty_eq]
    have hlit_c : litResolve env cA.1.type = true :=
      litResolve_of_infer_cons_former (ci := .indInfo wf.cvTa₀ {}) hS.store rfl hbasis_Ta₀
        ⟨p₀.nP + p₀.nIdx, bsT, s₀, hst_Ta₀⟩ hinf_c hfv_c
    have hstrip_c' :
        cA.1.type.stripPis (p₀.nP + cA.2) =
          some (cbs, Expr.mkAppN (.const p₀.cvT.name (p₀.cvT.levelParams.map .param))
            (Ix.Kernel.structPsAt cA.2 p₀.nP ++ es)) := by
      rwa [hout.nF_eq]
    have hpos_c' : ∀ i < cA.2,
        Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
          (cbs.getD (p₀.nP + i) default).1 ≠ .negative ∧
        Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
          (cbs.getD (p₀.nP + i) default).1 ≠ .unsupported := by
      rw [hout.nF_eq]; exact hpos_c
    have hunused_c := extra.unused_later cA hcA_mem cbs _ hstrip_c'
    obtain ⟨ks, hrck, hks_len, hks_ok, hopen_ok⟩ :=
      recCtorKinds_and_nativeOpenedOk (ci := .indInfo wf.cvTa₀ {})
        rfl wf.valStored_T.1 hstrip_c' hes_len hes_noT hfv_c hres_c hlit_c
        hdoms_and_noT.2 hpos_c' hunused_c
    exact ⟨hout.nF_eq, sorts, ks, hsorts, hsum_c, hrck, hks_len, hks_ok, hopen_ok⟩
  -- Build `kinds` list via `Fin wf.ctorsA.length`
  have hk_ex : ∀ idx : Fin wf.ctorsA.length, ∃ ks,
      Ix.Kernel.recCtorKinds p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx wf.ctorsA[idx.1] = some ks ∧
      ks.length = wf.ctorsA[idx.1].2 ∧
      (∀ k₀ ∈ ks, k₀ ≠ .negative ∧ k₀ ≠ .unsupported) ∧
      Ix.Kernel.nativeOpenedOk env p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx
        wf.ctorsA[idx.1].1.type wf.ctorsA[idx.1].2 ks = true := by
    intro ⟨j, hjA⟩
    have hj : j < p₀.ctors.length := by rwa [← wf.cload.1]
    obtain ⟨_, _, _, _, _, hrck, hkl, hkok, hopok⟩ :=
      hctor_stage j p₀.ctors[j] wf.ctorsA[j]
        (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hjA)
    exact ⟨_, hrck, hkl, hkok, hopok⟩
  let kinds : List (List Ix.Kernel.RecFieldKind) :=
    (List.finRange wf.ctorsA.length).map fun i => Classical.choose (hk_ex i)
  have hall_kinds :
      List.Forall₂
        (fun cA ks =>
          Ix.Kernel.recCtorKinds p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx cA = some ks ∧
          ks.length = cA.2 ∧
          (∀ k₀ ∈ ks, k₀ ≠ .negative ∧ k₀ ≠ .unsupported) ∧
          Ix.Kernel.nativeOpenedOk env p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx
            cA.1.type cA.2 ks = true)
        wf.ctorsA kinds := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp [kinds], fun j hj₁ hj₂ => ?_⟩
    have hspec := Classical.choose_spec (hk_ex ⟨j, hj₁⟩)
    have hget : kinds[j] = Classical.choose (hk_ex ⟨j, hj₁⟩) := by
      simp [kinds]
    simpa [hget] using hspec
  obtain ⟨hclassify, hfields_ok⟩ := classifyFixKinds_and_nativeFieldsOk hall_kinds
  have hk_len : kinds.length = wf.ctorsA.length := by simp [kinds]
  have hsum_ctors₀ :
      SumCtorsRunJ rulesJ envI₀ envI₀ p₀.cvT.name (List.range k) p₀.nP p₀.nIdx
        s₀ isProp₀ false wf.cvTa₀ p₀.ctors wf.ctorsA sortss₀ := by
    rw [← wf.lps_T]
    refine ⟨wf.cload.1, fout.sortss_len, fun j c cA hc hcA => ?_⟩
    obtain ⟨hnF, sorts, _, hsorts, hsc, _⟩ := hctor_stage j c cA hc hcA
    exact ⟨hnF, sorts, hsorts, hsc⟩
  -- Build `NatCtorInfoWf` for every `info ∈ buildCtorsInfo wf.ctorsA wf.ctorRawTypes kinds`
  have hk_len : kinds.length = wf.ctorsA.length := hall_kinds.length_eq.symm
  obtain ⟨hk_lt, hnCtors_lt, hrls₀_lt, hrec_np_lt, hrec_ni_lt, hrec_nm_lt, hrec_nmi_lt,
    hnall_lt, hcA_bounds⟩ := w.rec_counts_lt
  obtain ⟨_, hnP_lt, hnIdx_lt, _, _⟩ := wf.counts_lt
  have hwf_all :
      ∀ info ∈ buildCtorsInfo wf.ctorsA wf.ctorRawTypes kinds,
        NatCtorInfoWf p₀.cvT.name k p₀.large p₀.nP p₀.nIdx p₀.ctors.length info := by
    intro info hmem
    obtain ⟨j, hj_info, rfl⟩ := List.getElem_of_mem hmem
    have hj_info' := hj_info
    rw [buildCtorsInfo_length] at hj_info
    have hjA : j < wf.ctorsA.length := hj_info
    have hjK : j < kinds.length := by omega
    have hj : j < p₀.ctors.length := by rwa [← wf.cload.1]
    have hget_info :
        (buildCtorsInfo wf.ctorsA wf.ctorRawTypes kinds)[j]'hj_info' =
        ((wf.ctorsA[j]'hjA).1.name, (wf.ctorsA[j]'hjA).2, wf.ctorRawTypes.getD j default,
          (wf.ctorsA[j]'hjA).1.type, Ix.Kernel.recIdxOf (kinds[j]'hjK)) := by
      have hq := buildCtorsInfo_getElem? (ctorRawTypes := wf.ctorRawTypes) hjA hk_len
      rw [List.getElem?_eq_getElem hj_info', Option.some.injEq] at hq
      exact hq
    rw [hget_info]
    obtain ⟨c, cA, _, hc, hcA, _, hout⟩ := fout.ctors_out j hj
    rw [List.getElem?_eq_getElem hjA] at hcA; injection hcA with hcA_eq; subst hcA_eq
    have hcA_mem : wf.ctorsA[j] ∈ wf.ctorsA := List.getElem_mem hjA
    obtain ⟨hrck, hks_len, hks_ok, _⟩ :=
      (List.forall₂_iff_get.mp hall_kinds).2 j hjA hjK
    obtain ⟨rcbs, rargs, cbs, es, hsR, _, hsC, _, _, _, _, hsp_c⟩ := hout.residual
    rw [← hout.nF_eq] at hsR hsC
    obtain ⟨ty', ⟨_, _, _, _, _, _, _, hlpd_c', _, _⟩, hcv⟩ := hout.cvCheck
    have hlps_C : (wf.ctorsA[j]).1.type.allLevelParamsDefined (List.range k) = true := by
      have hpL : (List.range k) = c.1.levelParams := by
        rw [← wf.lps_T]; exact (wf.lps_ctors c (List.mem_of_getElem? hc)).symm
      rw [hpL, hcv]; exact hlpd_c'
    have hlps_R_j : (wf.ctorRawTypes.getD j default).allLevelParamsDefined (List.range k) = true := by
      rw [← wf.lps_T]; exact w.lps_ctorRaw j hj
    obtain ⟨hnPF_c, hmb_c, htele_c⟩ := hcA_bounds wf.ctorsA[j] hcA_mem
    have hrec_len_le : (Ix.Kernel.recIdxOf (kinds[j]'hjK)).length ≤ (wf.ctorsA[j]).2 := by
      unfold Ix.Kernel.recIdxOf
      have hle := List.length_filter_le
        (fun i => (kinds[j]'hjK).getD i .ordinary == .recursive ||
          (kinds[j]'hjK).getD i .ordinary == .reflexive)
        (List.range (kinds[j]'hjK).length)
      simp only [List.get_eq_getElem] at hks_len
      rw [List.length_range] at hle
      omega
    refine
      { nf_lt := hnPF_c
        lps_R := hlps_R_j
        lps_C := hlps_C
        noProj_C := hout.noProj
        strip_R := ⟨rcbs, p₀.cvT.levelParams.map .param, rargs, hsR⟩
        strip_C := ⟨cbs, p₀.cvT.levelParams.map .param,
          Ix.Kernel.structPsAt (wf.ctorsA[j]).2 p₀.nP ++ es, hsC⟩
        recIdx_eq := fun ecbs ebody hsE =>
          recIdxOf_eq_recIdxFrom hrck hks_ok hsC hsE
        rec_spines := fun i hi_mem => ?_
        minor_base_lt := by dsimp only; omega
        tele_lt := fun i hi_mem => ?_ }
    · obtain ⟨hi_lt, hment_true⟩ := recIdxOf_mem_mentionsConst hrck hks_ok hsC hi_mem
      refine ⟨hi_lt, fun rcbs' rbody' ecbs' ebody' hsR' hsC' => ?_⟩
      rw [hsR] at hsR'; injection hsR' with hR_eq
      rw [hsC] at hsC'; injection hsC' with hC_eq
      rw [← (Prod.mk.inj hR_eq).1, ← (Prod.mk.inj hC_eq).1]
      rcases hsp_c i (by rw [← hout.nF_eq]; exact hi_lt) with hment_false | hsp_raw
      · rw [hment_true] at hment_false; exact nomatch hment_false
      · exact hsp_raw
    · obtain ⟨hi_lt, _⟩ := recIdxOf_mem_mentionsConst hrck hks_ok hsC hi_mem
      have htele_i := htele_c i hi_lt
      dsimp only at htele_i ⊢
      omega
  -- Stage `env_base₀ = consSumCtors p₀.nP wf.ctorsA envI₀` and establish `DeclStoreInv env_base₀`
  let env_base₀ := Ix.Kernel.consSumCtors p₀.nP wf.ctorsA envI₀
  have hctorsA_names : wf.ctorsA.map (·.1.name) = p₀.ctors.map (·.1.name) := by
    apply List.ext_getElem?
    intro j
    by_cases hj : j < p₀.ctors.length
    · obtain ⟨c, cvCa₀, hc, hcA, hvs, _⟩ := wf.cload.2 j hj
      simp [hc, hcA, hvs.1]
    · have hjA : ¬ j < wf.ctorsA.length := by rw [wf.cload.1]; exact hj
      simp [List.getElem?_eq_none (Nat.le_of_not_lt hj),
        List.getElem?_eq_none (Nat.le_of_not_lt hjA)]
  have hnd_ctorsA : (wf.ctorsA.map (·.1.name)).Nodup := by
    rw [hctorsA_names]; exact wf.ctors_nodup
  have hshape_ctorsA : ∀ cA ∈ wf.ctorsA, cA.1.name.isProjFnShape = false := by
    intro cA hcA
    obtain ⟨j, hjA, rfl⟩ := List.getElem_of_mem hcA
    have hj : j < p₀.ctors.length := by rwa [← wf.cload.1]
    obtain ⟨c, cvCa₀, hc, hcA', hvs, _⟩ := wf.cload.2 j hj
    rw [List.getElem?_eq_getElem hjA] at hcA'
    injection hcA' with heq
    have hn : wf.ctorsA[j].1.name = c.1.name := by rw [heq]; exact hvs.1
    rw [hn]
    exact wf.shape_ctors c (List.mem_of_getElem? hc)
  have hfresh_ctorsA_envI₀ : ∀ cA ∈ wf.ctorsA, envI₀.find? cA.1.name = none := by
    intro cA hcA
    have hc_mem_names : cA.1.name ∈ p₀.ctors.map (·.1.name) := by
      rw [← hctorsA_names]; exact List.mem_map.mpr ⟨cA, hcA, rfl⟩
    obtain ⟨c, hc_mem, hname_eq⟩ := List.mem_map.mp hc_mem_names
    have hne : wf.cvTa₀.name ≠ cA.1.name := by
      rw [wf.valStored_T.1, ← hname_eq]
      exact fun heq => wf.T_not_in_ctors (by rw [heq]; exact List.mem_map.mpr ⟨c, hc_mem, rfl⟩)
    show (Ix.Kernel.Env.mk (.indInfo wf.cvTa₀ {} :: env.consts)).find? cA.1.name = none
    rw [env_find?_cons_ne (c := .indInfo wf.cvTa₀ {}) hne, ← hname_eq]
    exact wf.fresh_ctors c hc_mem
  have hty_ctorsA_envI₀ :
      ∀ cA ∈ wf.ctorsA,
        cA.1.type.hasFvar = false ∧
        cA.1.type.allLevelParamsDefined cA.1.levelParams = true ∧
        cA.1.type.constsResolve envI₀ = true ∧
        cA.1.type.looseBVarsBounded 0 = true := by
    intro cA hcA
    obtain ⟨j, hjA, rfl⟩ := List.getElem_of_mem hcA
    have hj : j < p₀.ctors.length := by rwa [← wf.cload.1]
    obtain ⟨c, cA', _, hc, hcA', _, hout⟩ := fout.ctors_out j hj
    rw [List.getElem?_eq_getElem hjA] at hcA'; injection hcA' with hcA_eq; cases hcA_eq
    obtain ⟨ty', ⟨_, _, _, _, hlbd₀, hfv₀, _, hlpd', hcr₀, _⟩, hcv⟩ := hout.cvCheck
    have hty_eq : wf.ctorsA[j].1.type = ty' := by rw [hcv]
    have hfv' : wf.ctorsA[j].1.type.hasFvar = false :=
      annotates_hasFvar_false hout.stored.2.2 hfv₀
    have hlbd' : wf.ctorsA[j].1.type.looseBVarsBounded 0 = true :=
      annotates_looseBVarsBounded hout.stored.2.2 0 hlbd₀
    have hlpd'' : wf.ctorsA[j].1.type.allLevelParamsDefined wf.ctorsA[j].1.levelParams = true := by
      rw [hout.stored.2.1, hty_eq]; exact hlpd'
    have hcr' : wf.ctorsA[j].1.type.constsResolve envI₀ = true := by
      rw [hty_eq]; exact hcr₀
    exact ⟨hfv', hlpd'', hcr', hlbd'⟩
  have hS_base₀ : DeclStoreInv env_base₀ :=
    DeclStoreInv.consSumCtors p₀.nP wf.ctorsA fout.storeInv₁ hnd_ctorsA
      hfresh_ctorsA_envI₀ hshape_ctorsA hty_ctorsA_envI₀
  -- Contexts for `check_const` on `Rec`
  let c₁ : Ctx := ⟨wf.E₁, envI₀, wf.t, wf.lim₀⟩
  let c_rec : Ctx := ⟨w.E_rec, env_base₀, wf.t, wf.lim₀⟩
  have hef₁ : EnvFacts c₁ := fout.storeInv₁.toEnvFacts wf.twf wf.roles₁
  have hef_rec : EnvFacts c_rec := hS_base₀.toEnvFacts wf.twf w.roles_rec
  have hc_rec : CoreFacts c_rec := ⟨hef_rec, w.lf_rec⟩
  have hfresh_R_base₀ : env_base₀.find? p₀.cvR.name = none := by
    have hR_ne_ctorsA : ∀ cA ∈ wf.ctorsA, cA.1.name ≠ p₀.cvR.name := by
      intro cA hcA heq
      have hm : p₀.cvR.name ∈ p₀.ctors.map (·.1.name) := by
        rw [← hctorsA_names, ← heq]
        exact List.mem_map.mpr ⟨cA, hcA, rfl⟩
      exact w.R_not_in_ctors hm
    rw [find?_consSumCtors_ne p₀.nP wf.ctorsA envI₀ hR_ne_ctorsA]
    have hne_TR : wf.cvTa₀.name ≠ p₀.cvR.name := by
      rw [wf.valStored_T.1]; exact fun heq => w.R_ne_T heq.symm
    show (Ix.Kernel.Env.mk (.indInfo wf.cvTa₀ {} :: env.consts)).find? p₀.cvR.name = none
    rw [env_find?_cons_ne (c := .indInfo wf.cvTa₀ {}) hne_TR]
    exact w.fresh_R
  have hshape_R : p₀.cvR.name.isProjFnShape = false := by
    rw [w.R_rprj]; exact nat_keyOf_isProjFnShape_false wf.t _
  have hpos_lift_R : PosSortLift env_base₀ w.cvRa₀ := by
    cases hlg : p₀.large with
    | false =>
      have hrng : w.cvRa₀.levelParams = List.range k := by simpa [hlg] using hlps_Ra₀
      exact PosSortLift.of_range hrng
    | true =>
      exact extra.pos_sort_lift hlg
  have hT_ind_base₀ : ∃ cv caps, env_base₀.find? p₀.cvT.name = some (.indInfo cv caps) := by
    have hT_ne_ctorsA₀ : ∀ cA ∈ wf.ctorsA, cA.1.name ≠ p₀.cvT.name := by
      intro cA hcA heq
      have hm : p₀.cvT.name ∈ p₀.ctors.map (·.1.name) := by
        rw [← hctorsA_names, ← heq]
        exact List.mem_map.mpr ⟨cA, hcA, rfl⟩
      exact wf.T_not_in_ctors hm
    refine ⟨wf.cvTa₀, {}, ?_⟩
    rw [find?_consSumCtors_ne p₀.nP wf.ctorsA envI₀ hT_ne_ctorsA₀, ← wf.valStored_T.1]
    exact Ix.Kernel.Env.find?_cons_self (.indInfo wf.cvTa₀ {}) env
  -- Invert `Obs.«KernelCheck::check_const».obs w.ev_rec`
  have hrec_pass :
      ConstantValCheckJ rulesJ env_base₀ p₀.cvR w.cvRa₀ ∧
      w.rec_np = p₀.nP ∧
      w.rec_ni = p₀.nIdx ∧
      w.rec_nm = 1 ∧
      w.rec_nmi = p₀.ctors.length ∧
      w.rulesA.length = p₀.ctors.length ∧
      (p₀.large = true →
        (∀ φ : LevelParam → Nat, Level.eval φ s₀ ≠ 0) ∨ p₀.ctors.length < 2) ∧
      (∃ sortss : List (List KLevel),
        SumCtorsRunJ rulesJ envI₀ envI₀ p₀.cvT.name (List.range k) p₀.nP p₀.nIdx s₀
          isProp₀ p₀.large wf.cvTa₀ p₀.ctors wf.ctorsA sortss) ∧
      (∃ recTy,
        Ix.Kernel.structRecTyR p₀.cvT.name (List.range k)
          (if p₀.large then k else 0) p₀.large p₀.nP p₀.nIdx wf.cvTa₀.type
          (Ix.Kernel.nativeCtors4 wf.ctorsA kinds) = some recTy ∧
        WrapRelSem env_base₀.find? recTy w.cvRa₀.type) ∧
      (∀ rl ∈ w.rulesA,
        rl.rhs.allLevelParamsDefined
          (if p₀.large then k :: List.range k else List.range k) = true) ∧
      (∀ bs dom B bm,
        w.cvRa₀.type.stripPis (p₀.nP + 1 + p₀.ctors.length + p₀.nIdx) =
          some (bs, .forallE dom B bm) →
        ∃ K, dom.getAppFn = .const K ((List.range k).map .param)) ∧
      ∀ idx (hlt : idx < w.rulesA.length)
        (hidx : idx < (Ix.Kernel.nativeCtors4 wf.ctorsA kinds).length),
        (w.rulesA[idx]'hlt).nfields =
          ((Ix.Kernel.nativeCtors4 wf.ctorsA kinds)[idx]'hidx).2.1 ∧
        ∃ rhsG,
          Ix.Kernel.structRecRhsR p₀.cvT.name (List.range k)
            (if p₀.large then k else 0) p₀.large p₀.nP p₀.nIdx wf.cvTa₀.type
            (Ix.Kernel.nativeCtors4 wf.ctorsA kinds) p₀.cvR.name
            ((if p₀.large then k :: List.range k else List.range k).map .param) idx = some rhsG ∧
          WrapRelSem env_base₀.find? rhsG (w.rulesA[idx]'hlt).rhs := by
    match Obs.«KernelCheck::check_const».obs w.ev_rec with
    | .Axiom_n1 (hv37 := hv) .. | .Axiom_other_n0 (hv37 := hv) ..
    | .Axiom_other_other (hv37 := hv) ..
    | .Defn (hv269 := hv) .. | .Thm (hv526 := hv) .. | .Opaque (hv825 := hv) ..
    | .Quot (hv1076 := hv) ..
    | .Induct_n0 (hv1240 := hv) .. | .Induct_other_n0 (hv1240 := hv) ..
    | .Induct_other_other (hv1240 := hv) ..
    | .Ctor_n0_n0 (hv1884 := hv) .. | .Ctor_n0_other (hv1884 := hv) ..
    | .Ctor_other_n0 (hv1884 := hv) .. | .Ctor_other_other (hv1884 := hv) .. =>
      injection hv with _ htag _
      exact absurd htag (by decide)
    | .Rec_other (v2836 := v2769) (m2815 := m2748) (m2837 := m2770) (v2858 := v2791)
        (m2859 := m2792) (cs2847 := cs2780) (cs2870 := cs2803)
        (ev2849 := ev2782) (ev2872 := ev2805) (hne2943 := hne2876) (hc3031 := hc) .. =>
      have hsub₁ : ∀ x ∈ cs2780, x ∈ w.cs_rec := fun x hx => by simp [hc, hx]
      have hsub₂ : ∀ x ∈ cs2803, x ∈ w.cs_rec := fun x hx => by simp [hc, hx]
      exact absurd (w.unmodeled_rec m2748 v2769 m2770 v2791 m2792 cs2780 cs2803
        ev2782 ev2805 hsub₁ hsub₂) hne2876
    | .Rec_n0 (v1 := v1) (m2 := m2) (v2673 := v2636) (m2674 := m2637) (cs2684 := cs2647)
        (v2710 := v2673) (m2711 := m2674) (cs2721 := cs2684) (m2742 := m2705)
        (m2755 := m2718) (m2815 := m2748) (m2837 := m2770) (m2859 := m2792) (cs2915 := cs2848)
        (ev14 := ev14) (hv2612 := hv2574) (ev2686 := ev2649) (hm2750 := hm2713)
        (ev2723 := ev2686) (ev2767 := ev2730) (ev2797 := ev_rules)
        (ev2827 := ev2760) (ev2849 := ev2782)
        (ev2872 := ev2805) (ev2917 := ev2850) (hc2942 := hc) .. =>
      injection hv2574 with _ _ hr_xs
      injection hr_xs with hr1 hr_xs; injection hr_xs with hr2 hr_xs
      injection hr_xs with hr3 hr_xs; injection hr_xs with hr4 hr_xs
      injection hr_xs with hr5 hr_xs; injection hr_xs with hr6 hr_xs
      injection hr_xs with hr7 hr_xs; injection hr_xs with hr8 hr_xs
      injection hr_xs with hr9 hr_xs; injection hr_xs with hr10 hr_xs
      injection hr_xs with hr11 _
      subst hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr11
      have e_iu := ev14.heap_extends
      have e_ws := ev2649.heap_extends
      have e_2705 : Heap.Extends m2637 m2705 := by rw [hm2713]; exact Heap.Extends.snoc m2637 _
      have e_m2_to_2705 := e_ws.trans e_2705
      have e_to_2705 := e_iu.trans e_m2_to_2705
      have hv_R_m2 : ValRepExact c_rec.κ m2 w.nl_rec w.ty_rec w.cvRa₀ :=
        ⟨w.valRep_R.1, w.valRep_R.2.1, w.valRep_R.2.2.1, w.valRep_R.2.2.2.mono e_iu⟩
      have hty_nil_es : TypesRep c_rec.κ (fun _ => default) m2705 0
          (.ptr (.enum kexprListEnum) m2637.length) := by
        rw [hm2713]; exact typesRep_alloc_nil c_rec.κ (fun _ => default) m2637
      have hg_rec_es : Good c_rec cs2684 := w.good_rec.sub (fun x hx => by simp [hc, hx])
      obtain ⟨hcvR_chk₀, _, _, _, _, _, _, _⟩ :=
        constantValCheckJ_of_checked hCore (c := c_rec) (Γ := fun _ => default)
          w.valStored_R hv_R_m2 w.lbd_R w.fv_R hfresh_R_base₀ w.basis_R hshape_R
          hS_base₀.store hpos_lift_R ev2649 e_m2_to_2705
          (w.rcRep_rec.mono e_to_2705) hty_nil_es hef_rec w.lf_rec hg_rec_es ev2686
      have e_to_2792 := e_to_2705.trans (ev2686.heap_extends.trans
        (ev2730.heap_extends.trans (ev_rules.heap_extends.trans
          (ev2760.heap_extends.trans (ev2782.heap_extends.trans ev2805.heap_extends)))))
      have hg₁_2848 : Good c₁ cs2848 := w.good₁_rec.sub (fun x hx => by simp [hc, hx])
      have hg_rec_2848 : Good c_rec cs2848 := w.good_rec.sub (fun x hx => by simp [hc, hx])
      have hsub_2848 : ∀ x ∈ cs2848, x ∈ w.cs_rec := fun x hx => by simp [hc, hx]
      have hT_key : keyOf wf.t (ixAddr w.bT) = p₀.cvT.name := by
        rw [w.bT_addr, wf.T_iprj]
      have hRec_key : keyOf wf.t (ixAddr w.bRec) = p₀.cvR.name := by
        rw [w.bRec_addr, w.R_rprj]
      have hlps_ctors_k : ∀ c ∈ p₀.ctors, c.1.levelParams = List.range k := by
        intro c hc; rw [wf.lps_ctors c hc, wf.lps_T]
      have hlps_rawT_k : w.rawT.allLevelParamsDefined (List.range k) = true := by
        rw [← wf.lps_T]; exact w.lps_rawT
      have hlps_tty_k : wf.cvTa₀.type.allLevelParamsDefined (List.range k) = true := by
        obtain ⟨ty', ⟨_, _, _, _, _, _, _, hlpd', _, _⟩, hcv⟩ := fout.cvT_check
        rw [← wf.lps_T, hcv]; exact hlpd'
      have hparent_k :
          ∀ (v_par p_par : SourceValue F) (m_a m_b m_c : Heap F) (cs_rpa cs_gci : List (Call F)),
            ObsFn W "KernelCheck::rec_to_parent_addr"
              [w.ty_rec, .field (w.rec_np : F), .field (w.rec_nm : F),
                .field (w.rec_nmi : F), .field (w.rec_ni : F)]
              m_a v_par m_b cs_rpa →
            ObsFn W "Ingress::get_ci" [v_par] m_b p_par m_c cs_gci →
            (∀ x ∈ cs_rpa, x ∈ w.cs_rec) →
            (∀ x ∈ cs_gci, x ∈ w.cs_rec) →
            ∃ (bT' b_p : Bytes.Address) (pty_par u_par blk_par : SourceValue F),
              Bytes.RepAddressRef addrTy m_b bT' v_par ∧
              ixAddr bT' = iprjAddr (ixAddr wf.b₀) 0 ∧
              loadValue m_c p_par = .ok (.construct kciEnum "Induct"
                [.field (k : F), pty_par,
                  .field (p₀.nP : F), .field (p₀.nIdx : F), .field (p₀.ctors.length : F),
                  u_par, blk_par, .field 0]) ∧
              Bytes.RepAddressRef addrTy m_c b_p blk_par ∧
              ixAddr b_p = ixAddr wf.b₀ ∧
              (∀ d Γ, RawTmExact (keyOf wf.t) d Γ m_c 0 w.rawT wf.cvTa₀.type pty_par) := by
        intro v_par p_par m_a m_b m_c cs_rpa cs_gci hrpa hgci hs₁ hs₂
        obtain ⟨bT', b_p, pty_par, u_par, blk_par, h1, h2, h3, h4, h5, h6⟩ :=
          w.parent_ind_load v_par p_par m_a m_b m_c cs_rpa cs_gci hrpa hgci hs₁ hs₂
        refine ⟨bT', b_p, pty_par, u_par, blk_par, h1, h2, h3, h4, h5, fun d Γ => ?_⟩
        have hraw := h6 d Γ
        rwa [hlps_Ta₀, posOf_range] at hraw
      have hnl_rec_eq :
          w.nl_rec =
            .field (((if p₀.large then k :: List.range k else List.range k).length : Nat) : F) := by
        rw [w.valRep_R.1, hlps_Ra₀]
      have hrec_ty_2792 :
          TmExact (keyOf wf.t) 0 (fun _ => default) m2792 0
            (posOf (if p₀.large then k :: List.range k else List.range k) w.cvRa₀.type) w.ty_rec := by
        have h0 := (w.valRep_R.2.2.2 0 (fun _ => default)).mono e_to_2792
        rwa [hlps_Ra₀] at h0
      have hrules_2792 :
          RulesRepExact (keyOf wf.t) m2792
            (if p₀.large then k :: List.range k else List.range k) 0 w.rules_rec w.rulesA := by
        rw [← hlps_Ra₀]; exact w.rulesRep_R.mono e_to_2792
      have hrlsA_lt : w.rulesA.length < 2147483648 := by
        rw [w.rules_stored.length_eq]; exact hrls₀_lt
      rw [hnl_rec_eq] at ev2850
      obtain ⟨hnp_eq, hni_eq, hnm_eq, hnmi_eq, hrlsA_len, hlg_guard,
        ⟨sortss, hsum_ctors_lg₀⟩, ⟨recTy, hrecTy, hwrap_ty₀⟩,
        hrlsA_lpd, hmaj_lvls₀, hrules_out⟩ :=
        check_recursor_member_spec hLevels hCore
          hef₁ wf.lf₁ hg₁_2848 hc_rec hg_rec_2848 hT_ind_base₀
          w.record_b₀ w.cst_muts w.bT_addr w.bRec_addr hT_key w.key_bT_inj hRec_key
          hk_lt hnP_lt hnIdx_lt hnCtors_lt hrec_np_lt hrec_ni_lt hrec_nm_lt hrec_nmi_lt
          hnall_lt (fun cA hcA => (hcA_bounds cA hcA).1)
          hlps_ctors_k hlps_rawT_k hlps_tty_k hsR_tty₀ hst_Ta₀
          hk_len hwf_all w.cload_rec hparent_k hsub_2848 hsum_ctors₀
          (w.rcRep_rec.mono e_to_2792)
          (Bytes.repAddressRef_heapMono₂ addrTy e_to_2792 w.bpRep_rec)
          (Bytes.repAddressRef_heapMono₂ addrTy e_to_2792 w.apRep_rec)
          hrec_ty_2792 hrules_2792 hrlsA_lt ev2850
      exact ⟨hcvR_chk₀, hnp_eq, hni_eq, hnm_eq, hnmi_eq, hrlsA_len,
        hlg_guard, ⟨sortss, hsum_ctors_lg₀⟩, ⟨recTy, hrecTy, hwrap_ty₀⟩,
        hrlsA_lpd, hmaj_lvls₀, hrules_out⟩
  obtain ⟨hcvR_chk₀, hnp_eq, hni_eq, hnm_eq, hnmi_eq, hrlsA_len,
    hlg_guard, ⟨sortss, hsum_ctors_lg₀⟩, ⟨recTy, hrecTy, hwrap_ty₀⟩,
    hrlsA_lpd, hmaj_lvls₀, hrules_out⟩ := hrec_pass
  -- Establish `p₀.recPinned = true`
  have hmap_ctors4 :
      (buildCtorsInfo wf.ctorsA wf.ctorRawTypes kinds).map
        (fun info => (info.1, info.2.1, info.2.2.2.1, info.2.2.2.2)) =
      Ix.Kernel.nativeCtors4 wf.ctorsA kinds :=
    buildCtorsInfo_map_eq_nativeCtors4 hk_len
  have hctors4_len : (Ix.Kernel.nativeCtors4 wf.ctorsA kinds).length = p₀.ctors.length := by
    rw [← hmap_ctors4, List.length_map, buildCtorsInfo_length]
    have hcA_len : wf.ctorsA.length = p₀.ctors.length := wf.cload.1
    omega
  have hrP_pin : rP = p₀.nP + 1 + p₀.ctors.length := by
    rw [hrP_w, hnp_eq, hnm_eq, hnmi_eq]
  have hmI_pin : mI = p₀.nP + 1 + p₀.ctors.length + p₀.nIdx := by
    rw [hmI_w, hrP_pin, hni_eq]
  have hrls₀_len : w.rules₀.length = p₀.ctors.length := by
    rw [← w.rules_stored.length_eq, hrlsA_len]
  have hctors4_nf :
      ∀ j (hj4 : j < (Ix.Kernel.nativeCtors4 wf.ctorsA kinds).length)
        (hjA : j < wf.ctorsA.length),
        ((Ix.Kernel.nativeCtors4 wf.ctorsA kinds)[j]'hj4).2.1 = (wf.ctorsA[j]'hjA).2 := by
    intro j hj4 hjA
    have hjK : j < kinds.length := by omega
    have hj_info : j < (buildCtorsInfo wf.ctorsA wf.ctorRawTypes kinds).length := by
      rw [buildCtorsInfo_length]; omega
    have hq_map := congrArg (fun xs => xs[j]?) hmap_ctors4
    rw [List.getElem?_map, List.getElem?_eq_getElem hj_info, Option.map_some,
      List.getElem?_eq_getElem hj4, Option.some.injEq] at hq_map
    have hq_info := buildCtorsInfo_getElem? (ctorRawTypes := wf.ctorRawTypes) hjA hk_len
    rw [List.getElem?_eq_getElem hj_info, Option.some.injEq] at hq_info
    rw [← hq_map, hq_info]
  have hpinned : p₀.recPinned = true := by
    refine nativeParts?_recPinned_true hparts hblk_w hctors_p hrP_pin hmI_pin hrls₀_len
      (fun j hj rule c hrule hc => ?_)
    refine ⟨w.rules_ctor j hj rule c hrule hc, ?_⟩
    have hj_r₀ : j < w.rules₀.length := by omega
    have hj_rA : j < w.rulesA.length := by omega
    have hj_4 : j < (Ix.Kernel.nativeCtors4 wf.ctorsA kinds).length := by omega
    have hj_cA : j < wf.ctorsA.length := by rwa [wf.cload.1]
    have hrs_j := (List.forall₂_iff_get.mp w.rules_stored).2 j hj_rA hj_r₀
    simp only [List.get_eq_getElem] at hrs_j
    rw [List.getElem?_eq_getElem hj_r₀, Option.some.injEq] at hrule
    obtain ⟨c', _, _, hc', hcA', _, _⟩ := fout.ctors_out j hj
    obtain ⟨hnF_c, _⟩ := hctor_stage j c' wf.ctorsA[j] hc' (List.getElem?_eq_getElem hj_cA)
    rw [hc] at hc'; injection hc' with hc_eq; subst hc_eq
    have hnf_rA := (hrules_out j hj_rA hj_4).1
    rw [hctors4_nf j hj_4 hj_cA] at hnf_rA
    rw [← hrule, ← hrs_j.2.1, hnf_rA, hnF_c]
  -- Stage `p₁`, `isRec`, `p`, `caps`, `env₁`, `env_base`, and upgrade via `CapsUpgradeAt`
  let p₁ : Ix.Kernel.InductiveShape .anon := p₀.toInductiveShape.withSort s₀
  let isRec : Bool := Ix.Kernel.nativeIsRec kinds
  let p : Ix.Kernel.NativeParts .anon := (p₀.complete p₁).withKinds kinds
  let caps : Ix.Kernel.IndCaps .anon := Ix.Kernel.nativeCapsAt p₁ isRec
  let env₁ : Ix.Kernel.Env .anon := ⟨.indInfo wf.cvTa₀ caps :: env.consts⟩
  let env_base : Ix.Kernel.Env .anon := Ix.Kernel.consSumCtors p.nP wf.ctorsA env₁
  have hfresh_Ta₀ : env.find? wf.cvTa₀.name = none := by
    rw [wf.valStored_T.1]; exact wf.fresh_T
  have hup₀ : CapsUpgradeAt wf.cvTa₀.name wf.cvTa₀ caps envI₀ env₁ :=
    CapsUpgradeAt.of_fresh_ind caps hS.store hfresh_Ta₀ hbasis_Ta₀
  have hup_base : CapsUpgradeAt wf.cvTa₀.name wf.cvTa₀ caps env_base₀ env_base :=
    CapsUpgradeAt.consSumCtors p₀.nP wf.ctorsA hup₀ fout.storeInv₁
      hnd_ctorsA hfresh_ctorsA_envI₀ hshape_ctorsA hty_ctorsA_envI₀
  have hsum_ctors₁ :
      SumCtorsRunJ rulesJ env₁ env₁ p.cvT.name p.cvT.levelParams p.nP p.nIdx
        p.resSort p.isProp p.large wf.cvTa₀ p.ctors wf.ctorsA sortss := by
    have hsum_lps :
        SumCtorsRunJ rulesJ envI₀ envI₀ p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx s₀
          isProp₀ p₀.large wf.cvTa₀ p₀.ctors wf.ctorsA sortss := by
      rwa [wf.lps_T]
    have hup_sc := hup₀.sumCtorsRunJ hsum_lps
    simpa [p, p₁, isProp₀] using hup_sc
  have hshape_Ta₀ : wf.cvTa₀.name.isProjFnShape = false := by
    rw [wf.valStored_T.1, wf.T_iprj]
    exact nat_keyOf_isProjFnShape_false wf.t _
  have hext_env₁ : Ix.Kernel.EnvExt env env₁ :=
    envExt_cons_nonProj hfresh_Ta₀ (ne_projTableName_of_isProjFnShape_false hshape_Ta₀)
  obtain ⟨tfvs_all, isorts, hop_all, hisorts⟩ :=
    index_fieldSortsJ_of_former fout.cvT_check hst_Ta₀ hext_env₁
  have hcvR_chk : ConstantValCheckJ rulesJ env_base p.cvR w.cvRa₀ :=
    hup_base.constantValCheckJ hcvR_chk₀
  have hwrap_ty : WrapRelSem env_base.find? recTy w.cvRa₀.type :=
    hwrap_ty₀.congr_defn hup_base.defnInfo_iff
  -- Establish `GenScoped` on `wf.cvTa₀.type`, constructor types, and `recTy` in `env_base` / `env_rec₀`
  have hfresh_ctorsA_env₁ : ∀ cA ∈ wf.ctorsA, env₁.find? cA.1.name = none := by
    intro cA hcA
    have hc_mem_names : cA.1.name ∈ p₀.ctors.map (·.1.name) := by
      rw [← hctorsA_names]; exact List.mem_map.mpr ⟨cA, hcA, rfl⟩
    obtain ⟨c, hc_mem, hname_eq⟩ := List.mem_map.mp hc_mem_names
    have hne : wf.cvTa₀.name ≠ cA.1.name := by
      rw [wf.valStored_T.1, ← hname_eq]
      exact fun heq => wf.T_not_in_ctors (by rw [heq]; exact List.mem_map.mpr ⟨c, hc_mem, rfl⟩)
    show (Ix.Kernel.Env.mk (.indInfo wf.cvTa₀ caps :: env.consts)).find? cA.1.name = none
    rw [env_find?_cons_ne (c := .indInfo wf.cvTa₀ caps) hne, ← hname_eq]
    exact wf.fresh_ctors c hc_mem
  have hext_ctors : Ix.Kernel.EnvExt env₁ env_base :=
    envExt_consSumCtors p.nP wf.ctorsA hnd_ctorsA hfresh_ctorsA_env₁ hshape_ctorsA
  have hT_ne_ctorsA : ∀ cA ∈ wf.ctorsA, cA.1.name ≠ p.cvT.name := by
    intro cA hcA heq
    have hm : p₀.cvT.name ∈ p₀.ctors.map (·.1.name) := by
      rw [← hctorsA_names]
      have hpT : p.cvT.name = p₀.cvT.name := rfl
      rw [← hpT, ← heq]
      exact List.mem_map.mpr ⟨cA, hcA, rfl⟩
    exact wf.T_not_in_ctors hm
  have hT_find_base : env_base.find? p.cvT.name = some (.indInfo wf.cvTa₀ caps) := by
    rw [find?_consSumCtors_ne p.nP wf.ctorsA env₁ hT_ne_ctorsA]
    have hpT : p.cvT.name = wf.cvTa₀.name := wf.valStored_T.1.symm
    rw [hpT]; exact hup₀.find_self_b
  have hlps_sub : ∀ x ∈ p.cvT.levelParams, x ∈ p.cvR.levelParams := by
    intro x hx
    have hx' : x ∈ List.range k := by
      have hpL : p.cvT.levelParams = p₀.cvT.levelParams := rfl
      rwa [hpL, wf.lps_T] at hx
    have hpR : p.cvR.levelParams = p₀.cvR.levelParams := rfl
    rw [hpR, hlps_R]
    cases p₀.large <;> simp [hx']
  have helim_mem : p.large = true → p.elim ∈ p.cvR.levelParams := by
    intro hlg
    have hpR : p.cvR.levelParams = p₀.cvR.levelParams := rfl
    have hpE : p.elim = p₀.elim := rfl
    have hpG : p.large = p₀.large := rfl
    rw [hpG] at hlg
    rw [hpR, hlps_R, hpE, helim_eq, hlg]
    simp
  have hno_defn_base_to_env :
      ∀ n cv v hn, env_base.find? n = some (.defnInfo cv v hn) →
        env.find? n = some (.defnInfo cv v hn) := by
    intro n cv v hn hf
    have hf₁ := no_new_defn_consSumCtors p.nP wf.ctorsA hf
    rw [Ix.Kernel.Env.find?_cons] at hf₁
    split at hf₁
    · exact nomatch hf₁
    · exact hf₁
  have hno_defn_base_to_envI₀ :
      ∀ n cv v hn, env_base.find? n = some (.defnInfo cv v hn) →
        envI₀.find? n = some (.defnInfo cv v hn) := by
    intro n cv v hn hf
    have hf_env := hno_defn_base_to_env n cv v hn hf
    have hne : wf.cvTa₀.name ≠ n := by
      intro heq; rw [← heq, hfresh_Ta₀] at hf_env; exact nomatch hf_env
    show (Ix.Kernel.Env.mk (.indInfo wf.cvTa₀ {} :: env.consts)).find? n = some (.defnInfo cv v hn)
    rw [env_find?_cons_ne (c := .indInfo wf.cvTa₀ {}) hne]
    exact hf_env
  have htty_sc_base : GenScoped env_base p.cvR.levelParams 0 wf.cvTa₀.type := by
    obtain ⟨ty', ⟨_, _, _, _, hlbd₀, hfv₀, _, hlpd', hcr₀, ⟨styT, _, hinfT, _⟩⟩, hcv⟩ :=
      fout.cvT_check
    have hty_eq : wf.cvTa₀.type = ty' := by rw [hcv]
    have hlbd_T' : wf.cvTa₀.type.looseBVarsBounded 0 = true :=
      annotates_looseBVarsBounded wf.valStored_T.2.2 0 hlbd₀
    have hfv_T' : wf.cvTa₀.type.hasFvar = false :=
      annotates_hasFvar_false wf.valStored_T.2.2 hfv₀
    have hlpd_T' : wf.cvTa₀.type.allLevelParamsDefined p.cvR.levelParams = true :=
      expr_allLevelParamsDefined_mono hlps_sub (by rw [hty_eq]; exact hlpd')
    have hcr_T' : wf.cvTa₀.type.constsResolve env_base = true := by
      have hcr₁ : wf.cvTa₀.type.constsResolve env₁ = true :=
        Ix.Kernel.Expr.constsResolve_le
          (fun m hm => by
            obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hm
            rw [hext_env₁.find hci]; rfl)
          (by rw [hty_eq]; exact hcr₀)
      exact Ix.Kernel.Expr.constsResolve_le
        (fun m hm => by
          obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hm
          rw [hext_ctors.find hci]; rfl)
        hcr₁
    have hdao_T' : defnAritiesOk env_base.find? wf.cvTa₀.type = true :=
      defnAritiesOk_congr_defn hno_defn_base_to_env _
        (by rw [hty_eq]; exact defnAritiesOk_of_infer_full hinfT)
    exact ⟨hlbd_T', hlpd_T', hcr_T', hfv_T', hdao_T'⟩
  have hcs4_info :
      ∀ c4 ∈ Ix.Kernel.nativeCtors4 wf.ctorsA kinds,
        ∃ cA ∈ wf.ctorsA,
          c4.1 = cA.1.name ∧
          c4.2.1 = cA.2 ∧
          c4.2.2.1 = cA.1.type ∧
          (∀ i ∈ c4.2.2.2, i < c4.2.1) ∧
          GenScoped env_base p.cvR.levelParams 0 cA.1.type ∧
          (∃ cbs cbody, cA.1.type.stripPis (p.nP + cA.2) = some (cbs, cbody)) := by
    intro c4 hc4
    rw [← hmap_ctors4, List.mem_map] at hc4
    obtain ⟨info, hinfo_mem, rfl⟩ := hc4
    obtain ⟨j, hj_info, rfl⟩ := List.getElem_of_mem hinfo_mem
    have hjA : j < wf.ctorsA.length := by rw [buildCtorsInfo_length] at hj_info; exact hj_info
    have hjK : j < kinds.length := by omega
    have hj : j < p₀.ctors.length := by rwa [← wf.cload.1]
    have hq_info := buildCtorsInfo_getElem? (ctorRawTypes := wf.ctorRawTypes) hjA hk_len
    rw [List.getElem?_eq_getElem hj_info, Option.some.injEq] at hq_info
    obtain ⟨c, cA', _, hc, hcA', _, hout⟩ := fout.ctors_out j hj
    rw [List.getElem?_eq_getElem hjA] at hcA'; injection hcA' with hcA_eq; subst hcA_eq
    obtain ⟨hrck, _, hks_ok, _⟩ := (List.forall₂_iff_get.mp hall_kinds).2 j hjA hjK
    obtain ⟨_, _, cbs, es, _, _, hsC, _⟩ := hout.residual
    rw [← hout.nF_eq] at hsC
    obtain ⟨hfv_c, hlpd_c, hcr_c₀, hlbd_c⟩ := hty_ctorsA_envI₀ wf.ctorsA[j] (List.getElem_mem hjA)
    obtain ⟨_, _, hinf_c, _⟩ := hout.inferSort
    have hlpd_cR : (wf.ctorsA[j]).1.type.allLevelParamsDefined p.cvR.levelParams = true := by
      have hpC : (wf.ctorsA[j]).1.levelParams = p.cvT.levelParams := by
        rw [hout.stored.2.1]; exact wf.lps_ctors c (List.mem_of_getElem? hc)
      rw [hpC] at hlpd_c
      exact expr_allLevelParamsDefined_mono hlps_sub hlpd_c
    have hcr_c_base : (wf.ctorsA[j]).1.type.constsResolve env_base = true := by
      have hcr₁ : (wf.ctorsA[j]).1.type.constsResolve env₁ = true := by
        rwa [hup₀.constsResolve_eq]
      exact Ix.Kernel.Expr.constsResolve_le
        (fun m hm => by
          obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hm
          rw [hext_ctors.find hci]; rfl)
        hcr₁
    have hdao_c : defnAritiesOk env_base.find? (wf.ctorsA[j]).1.type = true :=
      defnAritiesOk_congr_defn hno_defn_base_to_envI₀ _ (defnAritiesOk_of_infer_full hinf_c)
    refine ⟨wf.ctorsA[j], List.getElem_mem hjA, ?_, ?_, ?_, ?_,
      ⟨hlbd_c, hlpd_cR, hcr_c_base, hfv_c, hdao_c⟩, cbs, _, hsC⟩
    · rw [hq_info]
    · rw [hq_info]
    · rw [hq_info]
    · intro i hi
      rw [hq_info] at hi ⊢
      exact (recIdxOf_mem_mentionsConst hrck hks_ok hsC hi).1
  have hrecTy_p :
      Ix.Kernel.structRecTyR p.cvT.name p.cvT.levelParams p.elim p.large p.nP p.nIdx
        wf.cvTa₀.type (Ix.Kernel.nativeCtors4 wf.ctorsA p.kinds) = some recTy := by
    change Ix.Kernel.structRecTyR p₀.cvT.name p₀.cvT.levelParams p₀.elim p₀.large p₀.nP p₀.nIdx
      wf.cvTa₀.type (Ix.Kernel.nativeCtors4 wf.ctorsA kinds) = some recTy
    rwa [wf.lps_T, helim_eq]
  have hsc_recTy : GenScoped env_base p.cvR.levelParams 0 recTy := by
    refine GenScoped.structRecTyR hlps_sub helim_mem
      (by rw [hT_find_base]; rfl)
      (fun cv v hn hf => by rw [hT_find_base] at hf; exact nomatch hf)
      htty_sc_base
      (fun c4 hc4 => ?_)
      hrecTy_p
    obtain ⟨cA, hcA_mem, hn_eq, hnf_eq, hty_eq, hidx_lt, hsc_cA, _⟩ := hcs4_info c4 hc4
    have hf_cA := find?_consSumCtors_mem p.nP wf.ctorsA env₁ hnd_ctorsA hcA_mem
    refine ⟨(by rw [hn_eq, hf_cA]; rfl),
      (fun cv v hn hf => by rw [hn_eq, hf_cA] at hf; exact nomatch hf),
      (by rwa [hty_eq]), hidx_lt⟩
  have hlf_Ra₀ : letFree w.cvRa₀.type = true := annotates_letFree w.valStored_R.2.2
  have hdefeq_recTy : DefEq env_base 0 w.cvRa₀.type recTy :=
    hwrap_ty.defeq hlf_Ra₀ hsc_recTy.2.2.2.2 hsc_recTy.1
  -- Run `checkNativeRules_ok_go` in `env_rec₀`
  let cvRg : KConstantVal := ⟨p.cvR.name, p.cvR.levelParams, recTy⟩
  let env_rec₀ : Ix.Kernel.Env .anon :=
    ⟨.recInfo cvRg p.majorIdx p.rulePrefix [] :: env_base.consts⟩
  have hno_defn_rec₀_to_base :
      ∀ n cv v hn, env_rec₀.find? n = some (.defnInfo cv v hn) →
        env_base.find? n = some (.defnInfo cv v hn) := by
    intro n cv v hn hf
    rw [Ix.Kernel.Env.find?_cons] at hf
    split at hf
    · exact nomatch hf
    · exact hf
  have hsub_base_rec₀ : ∀ m ci, env_base.find? m = some ci → env_rec₀.find? m = some ci := by
    intro m ci hci
    have hne : cvRg.name ≠ m := by
      intro heq
      have hpR : cvRg.name = p₀.cvR.name := rfl
      rw [hpR] at heq
      subst heq
      have hR_ne_cA : ∀ cA ∈ wf.ctorsA, cA.1.name ≠ p₀.cvR.name := by
        intro cA hcA heq'
        have hm : p₀.cvR.name ∈ p₀.ctors.map (·.1.name) := by
          rw [← hctorsA_names, ← heq']
          exact List.mem_map.mpr ⟨cA, hcA, rfl⟩
        exact w.R_not_in_ctors hm
      rw [find?_consSumCtors_ne p.nP wf.ctorsA env₁ hR_ne_cA] at hci
      have hne_TR : wf.cvTa₀.name ≠ p₀.cvR.name := by
        rw [wf.valStored_T.1]; exact fun he => w.R_ne_T he.symm
      change (Ix.Kernel.Env.mk (.indInfo wf.cvTa₀ caps :: env.consts)).find? p₀.cvR.name = some ci at hci
      rw [env_find?_cons_ne (c := .indInfo wf.cvTa₀ caps) hne_TR, w.fresh_R] at hci
      exact nomatch hci
    exact (env_find?_cons_ne (c := .recInfo cvRg p.majorIdx p.rulePrefix []) hne).trans hci
  have hT_find_rec₀ : env_rec₀.find? p.cvT.name = some (.indInfo wf.cvTa₀ caps) :=
    hsub_base_rec₀ _ _ hT_find_base
  have hR_find_rec₀ :
      env_rec₀.find? p.cvR.name = some (.recInfo cvRg p.majorIdx p.rulePrefix []) :=
    Ix.Kernel.Env.find?_cons_self (.recInfo cvRg p.majorIdx p.rulePrefix []) env_base
  have htty_sc_rec₀ : GenScoped env_rec₀ p.cvR.levelParams 0 wf.cvTa₀.type :=
    ⟨htty_sc_base.1, htty_sc_base.2.1,
      constsResolve_mono_env hsub_base_rec₀ htty_sc_base.2.2.1,
      htty_sc_base.2.2.2.1,
      defnAritiesOk_congr_defn hno_defn_rec₀_to_base _ htty_sc_base.2.2.2.2⟩
  obtain ⟨rhsG, hchk_rules, hrhsG_len, hrhsG_get⟩ :=
    checkNativeRules_ok_go (envR := env_rec₀) (rlps := p.cvR.levelParams)
      (lps := p.cvT.levelParams) (T := p.cvT.name) (recC := p.cvR.name)
      (elim := p.elim) (large := p.large) (nP := p.nP) (nIdx := p.nIdx)
      (tty := wf.cvTa₀.type) (ctors := Ix.Kernel.nativeCtors4 wf.ctorsA p.kinds)
      hlps_sub helim_mem
      (by rw [hT_find_rec₀]; rfl)
      (fun cv v hn hf => by rw [hT_find_rec₀] at hf; exact nomatch hf)
      (by rw [hR_find_rec₀]; rfl)
      (fun cv v hn hf => by rw [hR_find_rec₀] at hf; exact nomatch hf)
      htty_sc_rec₀
      ⟨bsT, .sort s₀, hst_Ta₀⟩
      (fun c4 hc4 => by
        obtain ⟨cA, hcA_mem, hn_eq, hnf_eq, hty_eq, hidx_lt, hsc_cA, hst_cA⟩ := hcs4_info c4 hc4
        have hf_cA := hsub_base_rec₀ _ _
          (find?_consSumCtors_mem p.nP wf.ctorsA env₁ hnd_ctorsA hcA_mem)
        refine ⟨(by rw [hn_eq, hf_cA]; rfl),
          (fun cv v hn hf => by rw [hn_eq, hf_cA] at hf; exact nomatch hf),
          ⟨(by rw [hty_eq]; exact hsc_cA.1),
            (by rw [hty_eq]; exact hsc_cA.2.1),
            constsResolve_mono_env hsub_base_rec₀ (by rw [hty_eq]; exact hsc_cA.2.2.1),
            (by rw [hty_eq]; exact hsc_cA.2.2.2.1),
            defnAritiesOk_congr_defn hno_defn_rec₀_to_base _
              (by rw [hty_eq]; exact hsc_cA.2.2.2.2)⟩,
          hidx_lt, (by rw [hty_eq, hnf_eq]; exact hst_cA)⟩)
      (Ix.Kernel.nativeCtors4 wf.ctorsA p.kinds).length 0 (Nat.zero_add _)
  -- Assemble `NativeRecRunJ`, `RecStoredJ`, and `NativeRecJ`
  let rhssA : List KExpr := w.rulesA.map (·.rhs)
  have hwrap_rhss : List.Forall₂ (Ix.Kernel.Semantics.WrapRel env_base.find?) rhsG rhssA := by
    rw [List.forall₂_iff_get]
    have hpK : p.kinds = kinds := rfl
    have hlen_rhsG : rhsG.length = p₀.ctors.length := by
      rw [hrhsG_len, hpK, hctors4_len]
    have hlen_rhssA : rhssA.length = p₀.ctors.length := by
      simp [rhssA, hrlsA_len]
    refine ⟨by omega, fun idx hidx₁ hidx₂ => ?_⟩
    simp only [List.get_eq_getElem, rhssA, List.getElem_map]
    have hidx_rem : idx < (Ix.Kernel.nativeCtors4 wf.ctorsA p.kinds).length := by
      rwa [← hrhsG_len]
    obtain ⟨rhs_i, hrhs_get, hrhs_eq_p, _⟩ := hrhsG_get idx hidx_rem
    rw [List.getElem?_eq_getElem hidx₁, Option.some.injEq] at hrhs_get
    subst hrhs_get
    rw [Nat.zero_add] at hrhs_eq_p
    have hidx_A : idx < w.rulesA.length := by simp [rhssA] at hidx₂; exact hidx₂
    have hidx_4 : idx < (Ix.Kernel.nativeCtors4 wf.ctorsA kinds).length := by
      simpa [hpK] using hidx_rem
    obtain ⟨_, rhsG', hrhsG', hwrap_i₀⟩ := hrules_out idx hidx_A hidx_4
    change Ix.Kernel.structRecRhsR p₀.cvT.name p₀.cvT.levelParams p₀.elim p₀.large p₀.nP p₀.nIdx
        wf.cvTa₀.type (Ix.Kernel.nativeCtors4 wf.ctorsA kinds) p₀.cvR.name
        (p₀.cvR.levelParams.map .param) idx = some rhsG[idx] at hrhs_eq_p
    have hrhs_eq₀ :
        Ix.Kernel.structRecRhsR p₀.cvT.name (List.range k) (if p₀.large then k else 0)
          p₀.large p₀.nP p₀.nIdx wf.cvTa₀.type (Ix.Kernel.nativeCtors4 wf.ctorsA kinds)
          p₀.cvR.name ((if p₀.large then k :: List.range k else List.range k).map .param) idx =
        some rhsG[idx] := by
      rwa [wf.lps_T, helim_eq, hlps_R] at hrhs_eq_p
    rw [hrhsG'] at hrhs_eq₀
    injection hrhs_eq₀ with heq_rhs
    subst heq_rhs
    exact (hwrap_i₀.congr_defn hup_base.defnInfo_iff).toWrapRel
  have hlf_rhssA : ∀ r ∈ rhssA, letFree r = true := by
    intro r hr
    obtain ⟨rlA, hrlA_mem, rfl⟩ := List.mem_map.mp hr
    obtain ⟨idx, hidx_A, rfl⟩ := List.getElem_of_mem hrlA_mem
    have hidx_₀ : idx < w.rules₀.length := by rw [← w.rules_stored.length_eq]; exact hidx_A
    have hrs := (List.forall₂_iff_get.mp w.rules_stored).2 idx hidx_A hidx_₀
    simp only [List.get_eq_getElem] at hrs
    exact annotates_letFree hrs.2.2
  have hannot_rhss :
      List.Forall₂
        (rulesJ.annot ⟨.recInfo w.cvRa₀ p.majorIdx p.rulePrefix [] :: env_base.consts⟩ 0)
        p.rhss rhssA := by
    have hp_rhss : p.rhss = w.rules₀.map (·.rhs) := hrhss_p
    rw [hp_rhss, List.forall₂_iff_get]
    refine ⟨by simp [rhssA, w.rules_stored.length_eq], fun idx hidx₀ hidxA => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_map, rhssA]
    have hj₀ : idx < w.rules₀.length := by simpa using hidx₀
    have hjA : idx < w.rulesA.length := by simpa [rhssA] using hidxA
    have hrs := (List.forall₂_iff_get.mp w.rules_stored).2 idx hjA hj₀
    simp only [List.get_eq_getElem] at hrs
    obtain ⟨hfv_r₀, hlbd_r₀⟩ := w.rules_rhs_scoped w.rules₀[idx] (List.getElem_mem hj₀)
    exact annot_of_annotates hrs.2.2 hfv_r₀ hlbd_r₀ 0
  have hcvRa₀_eta : w.cvRa₀ = ⟨p.cvR.name, p.cvR.levelParams, w.cvRa₀.type⟩ := by
    cases h_cv : w.cvRa₀ with
    | mk nm lps ty =>
      have hpR_eq : p.cvR = p₀.cvR := rfl
      have hn : nm = p.cvR.name := by rw [hpR_eq]; simpa [h_cv] using w.valStored_R.1
      have hl : lps = p.cvR.levelParams := by rw [hpR_eq]; simpa [h_cv] using w.valStored_R.2.1
      simp [hn, hl]
  have hrhssA_lpd : ∀ r ∈ rhssA, r.allLevelParamsDefined p.cvR.levelParams = true := by
    intro r hr
    obtain ⟨rlA, hrlA_mem, rfl⟩ := List.mem_map.mp hr
    have hpR : p.cvR.levelParams = p₀.cvR.levelParams := rfl
    rw [hpR, hlps_R]
    exact hrlsA_lpd rlA hrlA_mem
  have hmaj_lvls_p :
      ∀ bs dom B bm,
        w.cvRa₀.type.stripPis p.majorIdx = some (bs, .forallE dom B bm) →
        ∃ K, dom.getAppFn = .const K (p.cvT.levelParams.map .param) := by
    intro bs dom B bm hs
    change w.cvRa₀.type.stripPis (p₀.nP + 1 + p₀.ctors.length + p₀.nIdx) =
      some (bs, .forallE dom B bm) at hs
    have hpT : p.cvT.levelParams = p₀.cvT.levelParams := rfl
    rw [hpT, wf.lps_T]
    exact hmaj_lvls₀ bs dom B bm hs
  have hRecRun : NativeRecRunJ rulesJ env_base p wf.cvTa₀ wf.ctorsA cvRg rhsG :=
    ⟨hlps_ok, hpinned, w.cvRa₀, recTy, hcvR_chk, hrecTy_p,
      hsc_recTy.2.1, hsc_recTy.2.2.1, hsc_recTy.1, hsc_recTy.2.2.2.1,
      hdefeq_recTy, hchk_rules, rfl⟩
  have hRecStored : RecStoredJ rulesJ env_base p cvRg rhsG w.cvRa₀ rhssA :=
    Or.inr ⟨w.cvRa₀, hcvR_chk, hcvRa₀_eta,
      hwrap_ty.toWrapRel,
      toSemanticsForall₂ hwrap_rhss, hlf_rhssA, toSemanticsForall₂ hannot_rhss, hlf_Ra₀,
      hrhssA_lpd, hmaj_lvls_p⟩
  have hNativeRec : NativeRecJ rulesJ env_base p wf.cvTa₀ wf.ctorsA w.cvRa₀ rhssA :=
    ⟨cvRg, rhsG, hRecRun, hRecStored⟩
  -- Run `checkNativeTable_ok` on `env_rec`
  let rules_sum :=
    Ix.Kernel.sumRules env_base.find? w.cvRa₀.name p.nP p.majorIdx p.rulePrefix
      w.cvRa₀.type wf.ctorsA rhssA
  let ciR : KConstantInfo := .recInfo w.cvRa₀ p.majorIdx p.rulePrefix rules_sum
  let env_rec : Ix.Kernel.Env .anon := ⟨ciR :: env_base.consts⟩
  have hR_ne_T' : ciR.name ≠ p.cvT.name := by
    show w.cvRa₀.name ≠ p₀.cvT.name
    rw [w.valStored_R.1]; exact w.R_ne_T
  have hT_in_rec : (env_rec.find? p.cvT.name).isSome = true := by
    show ((Ix.Kernel.Env.mk (ciR :: env_base.consts)).find? p.cvT.name).isSome = true
    rw [env_find?_cons_ne (c := ciR) hR_ne_T', hT_find_base]
    rfl
  have hsub_base_rec : ∀ m ci, env_base.find? m = some ci → env_rec.find? m = some ci := by
    intro m ci hci
    have hne : ciR.name ≠ m := by
      show w.cvRa₀.name ≠ m
      rw [w.valStored_R.1]
      intro heq; subst heq
      have hR_ne_cA : ∀ cA ∈ wf.ctorsA, cA.1.name ≠ p₀.cvR.name := by
        intro cA hcA heq'
        have hm : p₀.cvR.name ∈ p₀.ctors.map (·.1.name) := by
          rw [← hctorsA_names, ← heq']
          exact List.mem_map.mpr ⟨cA, hcA, rfl⟩
        exact w.R_not_in_ctors hm
      rw [find?_consSumCtors_ne p.nP wf.ctorsA env₁ hR_ne_cA] at hci
      have hne_TR : wf.cvTa₀.name ≠ p₀.cvR.name := by
        rw [wf.valStored_T.1]; exact fun he => w.R_ne_T he.symm
      change (Ix.Kernel.Env.mk (.indInfo wf.cvTa₀ caps :: env.consts)).find? p₀.cvR.name = some ci at hci
      rw [env_find?_cons_ne (c := .indInfo wf.cvTa₀ caps) hne_TR, w.fresh_R] at hci
      exact nomatch hci
    exact (env_find?_cons_ne (c := ciR) hne).trans hci
  have hc_wf_rec : ∀ cA ∈ wf.ctorsA,
      (cA.1.type.stripPis (p.nP + cA.2)).isSome = true ∧
      cA.1.type.hasFvar = false ∧
      cA.1.type.allLevelParamsDefined p.cvT.levelParams = true ∧
      cA.1.type.constsResolve env_rec = true ∧
      cA.1.type.looseBVarsBounded 0 = true := by
    intro cA hcA
    obtain ⟨j, hjA, rfl⟩ := List.getElem_of_mem hcA
    have hj : j < p₀.ctors.length := by rwa [← wf.cload.1]
    obtain ⟨c, cA', _, hc, hcA', _, hout⟩ := fout.ctors_out j hj
    rw [List.getElem?_eq_getElem hjA] at hcA'; injection hcA' with hcA_eq; cases hcA_eq
    obtain ⟨_, _, cbs, _, _, _, hstrip_c, _⟩ := hout.residual
    have hst_some : (wf.ctorsA[j].1.type.stripPis (p.nP + wf.ctorsA[j].2)).isSome = true := by
      have hpN : p.nP = p₀.nP := rfl
      rw [hpN, hout.nF_eq, hstrip_c]; rfl
    obtain ⟨hfv', hlpd_c, hcr_c₀, hlbd'⟩ := hty_ctorsA_envI₀ wf.ctorsA[j] (List.getElem_mem hjA)
    have hlpd'' : wf.ctorsA[j].1.type.allLevelParamsDefined p.cvT.levelParams = true := by
      have hpC : wf.ctorsA[j].1.levelParams = p.cvT.levelParams := by
        rw [hout.stored.2.1]; exact wf.lps_ctors c (List.mem_of_getElem? hc)
      rwa [← hpC]
    have hcr₁ : wf.ctorsA[j].1.type.constsResolve env₁ = true := by
      rwa [hup₀.constsResolve_eq]
    have hcr_base : wf.ctorsA[j].1.type.constsResolve env_base = true :=
      Ix.Kernel.Expr.constsResolve_le
        (fun m hm => by
          obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hm
          rw [hext_ctors.find hci]; rfl)
        hcr₁
    exact ⟨hst_some, hfv', hlpd'', constsResolve_mono_env hsub_base_rec hcr_base, hlbd'⟩
  have hshape_Ra₀ : w.cvRa₀.name.isProjFnShape = false := by
    rw [w.valStored_R.1]; exact hshape_R
  have hfn_fresh_rec : ∀ j, env_rec.find? (Ix.Kernel.projFnName p.cvT.name j) = none := by
    intro j
    show (Ix.Kernel.Env.mk (ciR :: env_base.consts)).find?
      (Ix.Kernel.projFnName p.cvT.name j) = none
    rw [env_find?_cons_ne (c := ciR)
      (ne_projFnName_of_isProjFnShape_false hshape_Ra₀ _ _)]
    rw [find?_consSumCtors_ne p.nP wf.ctorsA env₁
      (fun cA hcA => ne_projFnName_of_isProjFnShape_false (hshape_ctorsA cA hcA) _ _)]
    show (Ix.Kernel.Env.mk (.indInfo wf.cvTa₀ caps :: env.consts)).find?
      (Ix.Kernel.projFnName p₀.cvT.name j) = none
    rw [env_find?_cons_ne (c := .indInfo wf.cvTa₀ caps)
      (ne_projFnName_of_isProjFnShape_false hshape_Ta₀ _ _)]
    exact wf.fresh_projFn j
  have htbl_fresh_rec : env_rec.find? (Ix.Kernel.projTableName p.cvT.name) = none := by
    show (Ix.Kernel.Env.mk (ciR :: env_base.consts)).find?
      (Ix.Kernel.projTableName p.cvT.name) = none
    rw [env_find?_cons_ne (c := ciR)
      (ne_projTableName_of_isProjFnShape_false hshape_Ra₀ _)]
    rw [find?_consSumCtors_ne p.nP wf.ctorsA env₁
      (fun cA hcA => ne_projTableName_of_isProjFnShape_false (hshape_ctorsA cA hcA) _)]
    show (Ix.Kernel.Env.mk (.indInfo wf.cvTa₀ caps :: env.consts)).find?
      (Ix.Kernel.projTableName p₀.cvT.name) = none
    rw [env_find?_cons_ne (c := .indInfo wf.cvTa₀ caps)
      (ne_projTableName_of_isProjFnShape_false hshape_Ta₀ _)]
    exact wf.fresh_projTbl
  obtain ⟨env₂, htable_ok, henv₂_cases⟩ :=
    checkNativeTable_ok hT_in_rec hc_wf_rec hfn_fresh_rec htbl_fresh_rec
  -- Assemble `DeclNativeRunJ rulesJ env p₀ env₂`
  have hNativeRun : DeclNativeRunJ rulesJ env p₀ env₂ := by
    refine ⟨wf.ctors_nodup, isRec, env₁, wf.cvTa₀, p₁, p, wf.ctorsA, sortss, kinds,
      w.cvRa₀, rhssA, tfvs_all, .sort s₀, isorts,
      ⟨wf.cvTa₀, s₀, bsT, wf.cvTa₀, fout.cvT_check, Or.inl rfl, hst_Ta₀,
        Or.inl rfl, rfl, rfl⟩,
      rfl, hsum_ctors₁, ?_, rfl, ?_, ?_, ?_, ?_, hNativeRec, htable_ok, ?_⟩
    · simpa [p, p₁] using hclassify
    · simpa [p, p₁] using hlg_guard
    · simpa [p, p₁] using hop_all
    · simpa [p, p₁] using hisorts
    · simpa [p, p₁] using hfields_ok
    · refine Or.inl ⟨caps, ?_⟩
      have hpT : p.cvT.name = wf.cvTa₀.name := wf.valStored_T.1.symm
      rw [hpT]; exact hup₀.find_self_b
  -- Assemble `InstallStep env (.indDecl block nPd) env₂`
  let ciT : KConstantInfo := .indInfo wf.cvTa₀ caps
  let ctors_ci : List KConstantInfo :=
    wf.ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p₀.nP c.2)
  let blockA : List KConstantInfo := ciT :: (ctors_ci ++ [ciR])
  let new_base : List KConstantInfo := ciR :: (ctors_ci.reverse ++ [ciT])
  have hrec_consts : env_rec.consts = new_base ++ env.consts := by
    show (ciR :: (Ix.Kernel.consSumCtors p₀.nP wf.ctorsA ⟨ciT :: env.consts⟩).consts) =
      (ciR :: (ctors_ci.reverse ++ [ciT])) ++ env.consts
    rw [consts_consSumCtors_eq, List.cons_append, List.append_assoc]
    rfl
  have hperm : new_base.Perm blockA := by
    have hp_ctors : (ctors_ci.reverse ++ [ciT]).Perm (ciT :: ctors_ci) :=
      (perm_append_singleton ctors_ci.reverse ciT).trans (List.Perm.cons ciT (perm_reverse ctors_ci))
    have hp_left : new_base.Perm (ciR :: ciT :: ctors_ci) :=
      List.Perm.cons ciR hp_ctors
    have hp_right : ((ciT :: ctors_ci) ++ [ciR]).Perm (ciR :: ciT :: ctors_ci) :=
      perm_append_singleton (ciT :: ctors_ci) ciR
    rw [List.cons_append] at hp_right
    exact hp_left.trans hp_right.symm
  have hstored_ctors :
      List.Forall₂ IxVM.Consistency.StoredAs ctors_ci
        (p₀.ctors.map (fun c => ConstantInfo.ctorInfo c.1 p₀.nP c.2)) := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp [ctors_ci, wf.cload.1], fun j hj₁ hj₂ => ?_⟩
    simp only [List.get_eq_getElem, ctors_ci, List.getElem_map]
    have hj : j < p₀.ctors.length := by simpa [ctors_ci] using hj₂
    obtain ⟨c, cvCa₀, hc, hcA, hvs, _⟩ := wf.cload.2 j hj
    rw [List.getElem?_eq_getElem hj] at hc; injection hc with hc_eq
    have hjA : j < wf.ctorsA.length := by rwa [wf.cload.1]
    rw [List.getElem?_eq_getElem hjA] at hcA; injection hcA with hcA_eq
    rw [hc_eq, hcA_eq]
    exact ⟨hvs, rfl, rfl⟩
  have hstored_rules : List.Forall₂ IxVM.Consistency.RuleStored rules_sum w.rules₀ := by
    refine sumRules_forall2_ruleStored env_base.find? w.cvRa₀.name p.nP p.majorIdx p.rulePrefix
      w.cvRa₀.type wf.ctorsA rhssA w.rules₀
      (by rw [wf.cload.1, hrls₀_len])
      (by simp [rhssA, w.rules_stored.length_eq])
      (fun j hj_r₀ cA rhsA rl₀ hcA hrhsA hrl₀ => ?_)
    have hj : j < p₀.ctors.length := by omega
    have hjA : j < wf.ctorsA.length := by rwa [wf.cload.1]
    have hj_rA : j < w.rulesA.length := by rw [w.rules_stored.length_eq]; exact hj_r₀
    obtain ⟨c, cvCa₀, hc, hcA', hvs, _⟩ := wf.cload.2 j hj
    rw [hcA] at hcA'; injection hcA' with hcA_eq
    have hctor_eq : cA.1.name = rl₀.ctor := by
      rw [hcA_eq]; dsimp only
      rw [hvs.1, w.rules_ctor j hj rl₀ c hrl₀ hc]
    have hrs_j := (List.forall₂_iff_get.mp w.rules_stored).2 j hj_rA hj_r₀
    simp only [List.get_eq_getElem] at hrs_j
    rw [List.getElem?_eq_getElem hj_r₀, Option.some.injEq] at hrl₀
    simp only [rhssA, List.getElem?_map, List.getElem?_eq_getElem hj_rA,
      Option.map_some, Option.some.injEq] at hrhsA
    have hj_4 : j < (Ix.Kernel.nativeCtors4 wf.ctorsA kinds).length := by omega
    have hnf_rA := (hrules_out j hj_rA hj_4).1
    rw [hctors4_nf j hj_4 hjA] at hnf_rA
    rw [List.getElem?_eq_getElem hjA, Option.some.injEq] at hcA
    have hnf_eq : cA.2 = rl₀.nfields := by
      rw [← hcA, ← hnf_rA, hrs_j.2.1, hrl₀]
    have hannot_j : IxVM.Consistency.Annotates rhsA rl₀.rhs := by
      rw [← hrhsA, ← hrl₀]; exact hrs_j.2.2
    exact ⟨hctor_eq, hnf_eq, hannot_j⟩
  have hrP_eq : p.rulePrefix = rP := by
    show p₀.nP + 1 + p₀.ctors.length = rP
    exact hrP_pin.symm
  have hmI_eq : p.majorIdx = mI := by
    show (p₀.nP + 1 + p₀.ctors.length) + p₀.nIdx = mI
    exact hmI_pin.symm
  have hstored_rec :
      IxVM.Consistency.StoredAs ciR (.recInfo p₀.cvR mI rP w.rules₀) :=
    ⟨w.valStored_R, hmI_eq, hrP_eq, hstored_rules⟩
  have hstored_block : List.Forall₂ IxVM.Consistency.StoredAs blockA block := by
    rw [hblk_clean]
    exact List.Forall₂.cons ⟨wf.valStored_T, trivial⟩
      (listForall₂_append hstored_ctors (List.Forall₂.cons hstored_rec List.Forall₂.nil))
  have hnd_block : (block.map (·.name)).Nodup := by
    rw [hblk_clean, List.map_cons, List.map_append, List.map_map, List.map_singleton]
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · simp only [List.mem_append, List.mem_singleton]
      rintro (hm | heq)
      · exact wf.T_not_in_ctors hm
      · exact w.R_ne_T heq.symm
    · rw [List.nodup_append]
      refine ⟨wf.ctors_nodup, List.nodup_singleton _, fun x hx y hy heq => ?_⟩
      rw [List.mem_singleton] at hy
      subst hy; subst heq
      exact w.R_not_in_ctors hx
  have hfresh_block : ∀ ci₀ ∈ block, env.find? ci₀.name = none := by
    intro ci₀ hci₀
    rw [hblk_clean] at hci₀
    rcases List.mem_cons.mp hci₀ with rfl | hci₀
    · exact wf.fresh_T
    · rcases List.mem_append.mp hci₀ with hci₀ | hci₀
      · obtain ⟨c, hc_mem, rfl⟩ := List.mem_map.mp hci₀
        exact wf.fresh_ctors c hc_mem
      · rw [List.mem_singleton] at hci₀
        subst hci₀
        exact w.fresh_R
  have henv₂_step :
      env₂ = ⟨new_base ++ env.consts⟩ ∨
      ∃ tbl : Ix.Kernel.ProjTable .anon,
        (⟨new_base ++ env.consts⟩ : Ix.Kernel.Env .anon).find?
          (Ix.Kernel.projTableName tbl.structName) = none ∧
        env₂ = ⟨.projInfo tbl :: new_base ++ env.consts⟩ := by
    have heq_env : env_rec = ⟨new_base ++ env.consts⟩ := by
      show ⟨env_rec.consts⟩ = (⟨new_base ++ env.consts⟩ : Ix.Kernel.Env .anon)
      rw [hrec_consts]
    rcases henv₂_cases with rfl | ⟨tbl, hfr, hsn, rfl⟩
    · exact Or.inl heq_env
    · refine Or.inr ⟨tbl, ?_, ?_⟩
      · rw [hsn, ← heq_env]; exact hfr
      · simp [hrec_consts]
  have hinst : IxVM.Consistency.InstallStep env (.indDecl block nPd) env₂ :=
    installStep_of_perm_and_optTable hpin hnd_block hfresh_block hstored_block hperm henv₂_step
  exact ⟨env₂, hinst, hNativeRun⟩

/-- `DeclInv`-preserving wrapper for Deliverable 1 (`nativeWithRec_step`). -/
theorem nativeWithRec_declInv_step (hLevels : IxVM.Consistency.Levels)
    (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Ix.Kernel.Env .anon}
    {block : List KConstantInfo} {nPd : Nat} {p₀ : Ix.Kernel.NativeParts .anon}
    (hchk : S0.Checked calls env (.indDecl block nPd))
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hparts : Ix.Kernel.nativeParts? nPd block = some p₀)
    (extra : NativeWithRecExtra calls env block p₀) :
    ∃ env₂,
      IxVM.Consistency.InstallStep env (.indDecl block nPd) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInv V env → DeclInv V env₂ := by
  obtain ⟨caps₀_p, cs_p, mI_p, rP_p, rules_p, hblk_p, _, hctors_p, _, _, _, hcs_p, _⟩ :=
    nativeParts?_withRec_inv hparts
  let w := extra.witness
  let wf := w.front
  have hcs_map_eq :
      (cs_p.map fun c => ConstantInfo.ctorInfo c.1 c.2.1 c.2.2) =
      p₀.ctors.map (fun c => ConstantInfo.ctorInfo c.1 p₀.nP c.2) := by
    rw [hctors_p, List.map_map]
    refine List.map_congr_left fun c hc => ?_
    simp [(hcs_p c hc).1]
  have hblk_clean :
      block = .indInfo p₀.cvT caps₀_p ::
        ((p₀.ctors.map fun c => ConstantInfo.ctorInfo c.1 p₀.nP c.2) ++
          [.recInfo p₀.cvR mI_p rP_p rules_p]) := by
    rw [hblk_p, hcs_map_eq, List.cons_append]
  have hinst_eq : IxVM.Consistency.installs (.indDecl block nPd) = block := by
    simp [IxVM.Consistency.installs, hpin]
  have hnd : ((IxVM.Consistency.installs (.indDecl block nPd)).map (·.name)).Nodup := by
    rw [hinst_eq, hblk_clean, List.map_cons, List.map_append, List.map_map, List.map_singleton]
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · simp only [List.mem_append, List.mem_singleton]
      rintro (hm | heq)
      · exact wf.T_not_in_ctors hm
      · exact w.R_ne_T heq.symm
    · rw [List.nodup_append]
      refine ⟨wf.ctors_nodup, List.nodup_singleton _, fun x hx y hy heq => ?_⟩
      rw [List.mem_singleton] at hy
      subst hy; subst heq
      exact w.R_not_in_ctors hx
  have hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs (.indDecl block nPd),
      env.find? ci₀.name = none := by
    rw [hinst_eq, hblk_clean]
    intro ci₀ hci₀
    rcases List.mem_cons.mp hci₀ with rfl | hci₀
    · exact wf.fresh_T
    · rcases List.mem_append.mp hci₀ with hci₀ | hci₀
      · obtain ⟨c, hc_mem, rfl⟩ := List.mem_map.mp hci₀
        exact wf.fresh_ctors c hc_mem
      · rw [List.mem_singleton] at hci₀
        subst hci₀
        exact w.fresh_R
  refine decls_step_of_store hchk hnd hfresh (fun hS => ?_)
  obtain ⟨env₂, hstep, hrun⟩ := nativeWithRec_step hLevels hCore hpin hparts hS extra
  exact ⟨env₂, hstep, declRunJ_of_native hpin hparts hrun⟩

end IxVM.Refinement.Decl
