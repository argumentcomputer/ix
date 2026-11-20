import IxVMRefinement.FamilyAlias.CallProjsPure
import IxVMRefinement.FamilyAlias.CallIotaRule
import IxVMRefinement.FamilyAlias.CallMembers
import IxVMRefinement.FamilyAlias.CallRecs
import IxVMRefinement.FamilyAlias.ProjEligible
import IxVMRefinement.Obs.KernelModeled6
import IxVMRefinement.Obs.KernelModeled7
import IxVMRefinement.Obs.KernelLevels0

/-! # Inversion of `KernelModeled::check_projs` and its callees

Produces `BlockProjFacts` from an accepted observation of `KernelModeled::check_projs`
inside `KernelModeled::check_family`:

* `check_proj_iota_spec`: inverts `KernelModeled::check_proj_iota`;
* `check_member_projs_spec`: inverts `KernelModeled::check_member_projs`, maintaining the
  folded telescope `projFieldTeleAt` at `(d = nP + 1, Γ = zeroGhost, k = 0)` and the raw
  constructor field telescope `ctele` at `(d = 0, k = nP + fidx)`;
* `check_member_projs_start_spec`: inverts `KernelModeled::check_member_projs_start`,
  combining canonical exact readings (`IndMemberData` / `CtorMemberData`) with
  `check_member_projs_spec` to produce `MemberProjFacts`;
* `check_projs_facts`: inverts `KernelModeled::check_projs` over all block members,
  pairing `ProjEligible.modeled_proj_eligible_one_facts` and `modeled_proj_eligible_det`
  with `check_member_projs_start_spec` to return `BlockProjFacts`. -/

universe u

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.Decl (ExprSemEq)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList substLevel)
open IxVM.Consistency
open IxVM (F)
open Ix.Kernel (Expr Level ConstantInfo ConstantVal RecRule LevelParam)
open Ix.Kernel.Semantics (NativeFam)

set_option maxHeartbeats 2400000
set_option linter.unusedVariables false

/-! ## Section 1: Pure helpers for `CallProjs` -/

private theorem repList_imp {E : String} {R₁ R₂ : Heap F → KExpr → SourceValue F → Prop}
    (himp : ∀ h x p, R₁ h x p → R₂ h x p) {h : Heap F} {xs : List KExpr} {p : SourceValue F}
    (hr : RepList E R₁ h xs p) : RepList E R₂ h xs p := by
  induction hr with
  | nil c => exact .nil c
  | cons c hx _ ih => exact .cons c (himp _ _ _ hx) ih

private theorem rcRep_of_rcLimRep_p {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} {h : Heap F} {rc : SourceValue F}
    (hrc : Claim.RCLimRep t bAddr lim h rc) : RCRep t lim h rc := by
  obtain ⟨tbl, htbl, hnd⟩ := hrc.cases
  rcases hnd with ⟨n, rfl, hn, hl⟩ | ⟨rfl, hl⟩
  · exact ⟨tbl, .construct addrMapEnum "Nil" [], _, hl, .inl ⟨n, rfl, hn, rfl⟩, htbl.toTableRep⟩
  · exact ⟨tbl, .construct addrMapEnum "Nil" [], _, hl, .inr ⟨rfl, rfl⟩, htbl.toTableRep⟩

private theorem collect_spine_tuple_p {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {e hd sp : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {k : Nat} {E : KExpr}
    (ev : ObsFn Obs.W "KernelTypes::collect_spine" [e] h (.tuple [hd, sp]) h' cs)
    (hE : Tm κ d Γ h k E e) :
    ∃ H As, E = Expr.mkAppN H As ∧ Tm κ d Γ h' k H hd ∧
      RepList kexprListEnum (fun h A p => Tm κ d Γ h k A p) h' As sp := by
  obtain ⟨hd', sp', H, As, htup, hH, hAs, hEq⟩ := collect_spine_tm ev hE
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
  obtain ⟨rfl, rfl⟩ := htup
  exact ⟨H, As, hEq, hH, hAs⟩

private theorem bvars_desc_tm_p {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {k : Nat}
    {start cnt : Nat} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hcnt : cnt ≤ start) (hstart : start ≤ k) (hk : k < 4611686018427387904)
    (ev : ObsFn Obs.W "KernelModeled::bvars_desc" [.field (start : F), .field (cnt : F)] h r h' cs) :
    RepList kexprListEnum (fun h E p => Tm κ 0 Γ h k E p) h'
      ((List.range cnt).map fun m => .bvar (start - 1 - m)) r := by
  have hc : ZMod.val (cnt : F) = cnt := val_natCast_wide_p (by omega)
  have hs : ZMod.val (start : F) = start := val_natCast_wide_p (by omega)
  have h1 := bvars_desc_tm (κ := κ) (Γ := Γ) (k := k) (top := (start : F)) (cnt := (cnt : F))
    (by omega) (by omega) hk ev
  rwa [hc, hs] at h1

private theorem bvars_desc_exact_local_go (rem : Nat) :
    ∀ {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {k : Nat}
      {top cnt : F} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val cnt = rem →
      rem ≤ ZMod.val top →
      ZMod.val top ≤ k →
      k < 4611686018427387904 →
      ObsFn Obs.W "KernelModeled::bvars_desc" [.field top, .field cnt] h r h' cs →
      RepList kexprListEnum (fun h E p => Decl.TmExact κ 0 Γ h k E p) h'
        ((List.range rem).map fun m => .bvar (ZMod.val top - 1 - m)) r := by
  induction rem with
  | zero =>
    intro κ Γ k top cnt r h h' cs hcnt _ _ _ ev
    have h0 : cnt = 0 := (ZMod.val_eq_zero cnt).mp hcnt
    subst h0
    match Obs.«KernelModeled::bvars_desc».obs ev with
    | .n0 (he19 := hr) (hm18 := hh) .. => subst hr hh; exact .nil (by simp)
    | .other (hne24 := hne) .. => exact absurd rfl hne
  | succ rem ih =>
    intro κ Γ k top cnt r h h' cs hcnt hle htop hk ev
    match Obs.«KernelModeled::bvars_desc».obs ev with
    | .n0 (hv14 := hv) .. => injection hv with h0; subst h0; simp at hcnt
    | .other (hne24 := hne) (he32 := hr) (hm31 := hm2) (hm47 := hm1)
        (op65 := op_t1) (op94 := op_t2) (op109 := op_c) (ev78 := ev_rec) .. =>
      subst hr hm1 hm2
      obtain rfl := Lib.sub_one_inv op_t1
      obtain rfl := Lib.sub_one_inv op_t2
      obtain rfl := Lib.sub_one_inv op_c
      have hcne : cnt ≠ 0 := fun e => hne (by rw [e])
      have htne : top ≠ 0 := by intro e; subst e; simp at hle
      have hpc := Lib.val_sub_one hcne
      have hpt := Lib.val_sub_one htne
      have hhead : Decl.TmExact κ 0 Γ (h ++ [.construct kexprEnum "BVar" [.field (top - 1)]]) k
          (.bvar (ZMod.val top - 1)) (.ptr (.enum kexprEnum) h.length) := by
        have h1 : Decl.TmExact κ 0 Γ (h ++ [.construct kexprEnum "BVar" [.field (top - 1)]]) k
            (.bvar (ZMod.val (top - 1))) (.ptr (.enum kexprEnum) h.length) :=
          .bvarLocal (by simp) (by omega) (by omega)
        rwa [show ZMod.val (top - 1) = ZMod.val top - 1 by omega] at h1
      have htail := ih (κ := κ) (Γ := Γ) (k := k) (top := top - 1) (cnt := cnt - 1)
        (by omega) (by omega) (by omega) hk ev_rec
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.sub_zero]
      have htail_eq :
          ((List.range rem).map ((fun m => (Expr.bvar (ZMod.val top - 1 - m) : KExpr)) ∘ (· + 1))) =
          (List.range rem).map (fun m => .bvar (ZMod.val (top - 1) - 1 - m)) := by
        apply List.map_congr_left
        intro m _; simp only [Function.comp_apply]; congr 1; omega
      rw [htail_eq]
      exact Lib.rep_store_cons (fun _ _ _ _ e x => x.mono e) (hhead.mono ev_rec.heap_extends) htail

private theorem bvars_desc_exact_local {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {k : Nat}
    {start cnt : Nat} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hcnt : cnt ≤ start) (hstart : start ≤ k) (hk : k < 4611686018427387904)
    (ev : ObsFn Obs.W "KernelModeled::bvars_desc" [.field (start : F), .field (cnt : F)] h r h' cs) :
    RepList kexprListEnum (fun h E p => Decl.TmExact κ 0 Γ h k E p) h'
      ((List.range cnt).map fun m => .bvar (start - 1 - m)) r := by
  have hc : ZMod.val (cnt : F) = cnt := val_natCast_wide_p (by omega)
  have hs : ZMod.val (start : F) = start := val_natCast_wide_p (by omega)
  have h1 := bvars_desc_exact_local_go cnt (κ := κ) (Γ := Γ) (k := k)
    (top := (start : F)) (cnt := (cnt : F)) hc (by omega) (by omega) hk ev
  rwa [hs] at h1

private theorem peel_collect_body_exact (m : Nat) :
    ∀ {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {k : Nat} {E : KExpr}
      {e acc r_e r_acc : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val n = m →
      ObsFn Obs.W "KernelModeled::peel_collect" [e, .field n, acc] h (.tuple [r_e, r_acc]) h' cs →
      Decl.TmExact κ 0 Γ h k E e →
      ∃ bs rem, E.stripPis m = some (bs, rem) ∧ Decl.TmExact κ 0 Γ h' (k + m) rem r_e := by
  induction m with
  | zero =>
    intro κ Γ k E e acc r_e r_acc n h h' cs hn ev hE
    match Obs.«KernelModeled::peel_collect».obs ev with
    | .n0 (he19 := hr) (he34 := hh) .. =>
      subst hh
      injection hr with hl; injection hl with h1 _; subst h1
      exact ⟨[], E, rfl, by simpa using hE⟩
    | .other (hne36 := hne) .. =>
      have := Lib.val_sub_one (fun (e : n = 0) => hne (by rw [e])); omega
  | succ m ih =>
    intro κ Γ k E e acc r_e r_acc n h h' cs hn ev hE
    match Obs.«KernelModeled::peel_collect».obs ev with
    | .n0 (hv14 := hv) .. => injection hv with h0; subst h0; simp at hn
    | .other (x_d := xd) (x_b := xb) (m107 := m107) (hne36 := hne) (ld51 := ld)
        (op104 := opSub) (hm115 := hm107) (ev80 := evRec) .. =>
      subst hm107
      obtain rfl := Lib.sub_one_inv opSub
      have hpred := Lib.val_sub_one (fun (e : n = 0) => hne (by rw [e]))
      obtain ⟨T, B, ℓ, rfl, _, hB, _⟩ := hE.forallE_of_load ld
      have ext := Heap.Extends.snoc h (.construct kexprListEnum "Cons" [xd, acc])
      obtain ⟨bs, rem, hstrip, hrem⟩ := ih (k := k + 1) (by omega) evRec (hB.mono ext)
      refine ⟨(T, Core.bmeta ℓ) :: bs, rem, by simp [Expr.stripPis, hstrip], ?_⟩
      rwa [show k + (m + 1) = k + 1 + m by omega]

private theorem pw_eq_bit {pa pb r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "KernelLevels::pw_eq" [pa, pb] h r h' cs) :
    r = .field 0 ∨ r = .field 1 := by
  match Obs.«KernelLevels::pw_eq».obs ev with
  | .n0_n1 (he108 := hr) .. => exact Or.inr hr
  | .other (he155 := hr) .. => exact Or.inl hr
  | .n0_other (ev120 := evIz) .. =>
    obtain ⟨hr, -⟩ := Lib.is_zero_spec evIz
    split at hr
    · exact Or.inr hr
    · exact Or.inl hr

private theorem stripPis_sort_of_annotates :
    ∀ (n : Nat) {eA e₀ : KExpr} {bs₀ : List (KExpr × Ix.Kernel.BinderMeta)} {u : KLevel},
      Annotates eA e₀ → e₀.stripPis n = some (bs₀, .sort u) →
      ∃ bsA, eA.stripPis n = some (bsA, .sort u)
  | 0, _, _, _, _, hann, hs => by
    injection hs with hp; injection hp with _ hr; subst hr
    cases hann with
    | sort => exact ⟨[], rfl⟩
  | n + 1, _, _, _, _, hann, hs => by
    cases hann with
    | forallE hT hB =>
      rename_i b₀ _ _
      simp only [Expr.stripPis] at hs ⊢
      cases hsb : b₀.stripPis n with
      | none => rw [hsb] at hs; simp at hs
      | some p =>
        rcases p with ⟨bs₁, rem₁⟩
        rw [hsb] at hs
        injection hs with hp; injection hp with _ hr; dsimp only at hr; rw [hr] at hsb
        obtain ⟨bsA, hA⟩ := stripPis_sort_of_annotates n hB hsb
        exact ⟨_ :: bsA, by rw [hA]; rfl⟩
    | bvar | fvar | sort | const | app | lam | letE | lit | proj => nomatch hs

private theorem stripPis_add {m n : Nat} {e rem1 rem2 : KExpr}
    {bs1 bs2 : List (KExpr × Ix.Kernel.BinderMeta)}
    (h1 : e.stripPis m = some (bs1, rem1)) (h2 : rem1.stripPis n = some (bs2, rem2)) :
    e.stripPis (m + n) = some (bs1 ++ bs2, rem2) := by
  induction m generalizing e bs1 with
  | zero =>
    injection h1 with hp; injection hp with h1a h1b; subst h1a h1b
    simpa using h2
  | succ m ih =>
    cases e with
    | forallE t b bm =>
      simp only [Expr.stripPis] at h1 ⊢
      cases hsb : b.stripPis m with
      | none => rw [hsb] at h1; simp at h1
      | some p =>
        rcases p with ⟨bs₀, rem₀⟩
        rw [hsb] at h1
        injection h1 with hp; injection hp with h1a h1b; dsimp only at h1a h1b; subst h1a h1b
        rw [Nat.succ_add, Expr.stripPis, ih hsb]
        rfl
    | _ => nomatch h1

/-- Folded telescope state starting from an arbitrary expression `e0` at field index `start`,
stepping `k` fields using `projKeyAt (start + j)`. -/
private def projFieldTeleFrom (nP bnl : Nat) (projKeyAt : Nat → KKey) (start : Nat) (e0 : KExpr) :
    Nat → Option KExpr
  | 0 => some e0
  | k + 1 =>
    match projFieldTeleFrom nP bnl projKeyAt start e0 k with
    | some (.forallE _ frest _) =>
      let projApp := Expr.mkAppN (.const (projKeyAt (start + k)) ((List.range bnl).map .param))
        (((List.range nP).map fun m => .fvar m (.sort .zero)) ++ [.fvar nP (.sort .zero)])
      some (frest.instantiate1 projApp 0)
    | _ => none

private theorem projFieldTeleFrom_congr {nP bnl start : Nat} {e0 : KExpr}
    {g₁ g₂ : Nat → KKey} :
    ∀ (k : Nat), (∀ j < k, g₁ (start + j) = g₂ (start + j)) →
      projFieldTeleFrom nP bnl g₁ start e0 k = projFieldTeleFrom nP bnl g₂ start e0 k
  | 0, _ => rfl
  | k + 1, hg => by
    simp only [projFieldTeleFrom]
    rw [projFieldTeleFrom_congr k (fun j hj => hg j (by omega)), hg k (Nat.lt_succ_self k)]

private theorem projFieldTeleFrom_succ {nP bnl start : Nat} {fdom frest : KExpr}
    {fbm : Ix.Kernel.BinderMeta} {g : Nat → KKey} :
    ∀ (k : Nat),
      let projApp := Expr.mkAppN (.const (g start) ((List.range bnl).map .param))
        (((List.range nP).map fun m => .fvar m (.sort .zero)) ++ [.fvar nP (.sort .zero)])
      projFieldTeleFrom nP bnl g start (.forallE fdom frest fbm) (k + 1) =
        projFieldTeleFrom nP bnl g (start + 1) (frest.instantiate1 projApp 0) k
  | 0 => by simp [projFieldTeleFrom]
  | k + 1 => by
    dsimp only
    conv_lhs => unfold projFieldTeleFrom
    conv_rhs => unfold projFieldTeleFrom
    rw [projFieldTeleFrom_succ k, show start + (k + 1) = start + 1 + k by omega]

private theorem projFieldTeleAt_eq_from {ctyMPos e0 : KExpr} {nP bnl : Nat} {g : Nat → KKey}
    (h0 : (Expr.instPisAt ((List.range nP).map fun m => .fvar m (.sort .zero)) ctyMPos).map Prod.snd =
      some e0) :
    ∀ k, projFieldTeleAt ctyMPos nP bnl g k = projFieldTeleFrom nP bnl g 0 e0 k
  | 0 => h0
  | k + 1 => by
    simp only [projFieldTeleAt, projFieldTeleFrom, Nat.zero_add]
    rw [projFieldTeleAt_eq_from h0 k]
    rfl

/-! ## Section 2: `KernelModeled::check_proj_iota` -/

theorem check_proj_iota_spec (P : ProjsCtx.{u})
    {projKey iotaKey cModelKey : KKey} {aProj aIota aCModel : Bytes.Address}
    {x_rc x_proj_i x_iota_i x_c_model x_cty_m x_raw_dom r : SourceValue F}
    {ctyMPos rawDom : KExpr} {nP bnl nF fidx : Nat} {h h' : Heap F} {cs : List (Call F)}
    (hnP : nP < 72057594037927936) (hbnl : bnl < 4294967296)
    (hnF : nF < 72057594037927936) (hfidx : fidx < nF)
    (haProj_eq : Core.keyOf P.t (ixAddr aProj) = projKey)
    (haIota_eq : Core.keyOf P.t (ixAddr aIota) = iotaKey)
    (haCModel_eq : Core.keyOf P.t (ixAddr aCModel) = cModelKey)
    (hAdvIota : AdvChecked P.calls P.bAddr P.t P.lim P.csFam P.advAs aIota)
    (hrc : Claim.RCLimRep P.t P.bAddr P.lim h x_rc)
    (haProj : Bytes.RepAddressRef addrTy h aProj x_proj_i)
    (haIota : Bytes.RepAddressRef addrTy h aIota x_iota_i)
    (haCModel : Bytes.RepAddressRef addrTy h aCModel x_c_model)
    (hcty : Tm (Core.keyOf P.t) 0 zeroGhost h 0 ctyMPos x_cty_m)
    (hraw : Tm (Core.keyOf P.t) 0 zeroGhost h (nP + fidx) rawDom x_raw_dom)
    (hsub : ∀ cl ∈ cs, cl ∈ P.calls)
    (ev : ObsFn Obs.W "KernelModeled::check_proj_iota"
      [x_rc, x_proj_i, x_iota_i, x_c_model, x_cty_m, x_raw_dom,
       .field (nP : F), .field (bnl : F), .field (nF : F), .field (fidx : F)] h r h' cs) :
    ∃ (cvIota : ConstantVal .anon) (iotaVal : KExpr)
      (ibsI cbsI : List (KExpr × Ix.Kernel.BinderMeta)) (cremI : KExpr)
      (uEq : KLevel) (alpha lhs : KExpr),
      P.env.find? iotaKey = some (.thmInfo cvIota iotaVal) ∧
      cvIota.levelParams.length = bnl ∧
      cvIota.levelParams.Perm (List.range bnl) ∧
      (Core.posOf cvIota.levelParams cvIota.type).stripPis (nP + nF) =
        some (ibsI, Expr.mkAppN (.const Ix.Kernel.eqName [uEq]) [alpha, lhs, .bvar (nF - 1 - fidx)]) ∧
      ctyMPos.stripPis (nP + nF) = some (cbsI, cremI) ∧
      List.Forall₂ ExprSemEq (ibsI.map Prod.fst) (cbsI.map Prod.fst) ∧
      ExprSemEq alpha (rawDom.liftLooseBVars (nF - fidx) 0) ∧
      ExprSemEq lhs
        (Expr.mkAppN (.const projKey ((List.range bnl).map .param))
          (((List.range nP).map fun m => .bvar (nP + nF - 1 - m)) ++
            [Expr.mkAppN (.const cModelKey ((List.range bnl).map .param))
              (((List.range nP).map fun m => .bvar (nP + nF - 1 - m)) ++
                ((List.range nF).map fun m => .bvar (nF - 1 - m)))])) := by
  match Obs.«KernelModeled::check_proj_iota».obs ev with
  | .run (m_qoxuhpcf := m_ci) (p_tnidvomk := p_ci) (cs_yjnjtmnv := cs_ci)
      (x_inl := x_inl) (x_ity := x_ity) (m_pjlgtkhu := m_tele) (v_utorrpjn := v_npnf1)
      (m_ifurhvaw := m_sp) (x_eqh := x_eqh) (x_targs := x_targs) (x_eqa := x_eqa)
      (x_eqls := x_eqls) (m_ksicvqzz := m_eqa) (m_ouaxlrxw := m_raddr) (cs_dkzijfxu := cs_raddr)
      (m_vkjhguge := m_req) (m_eoyzbmoy := m_len) (m_xrozglhy := m_a0)
      (m_xbocpxpe := m_a1) (m_yqtkaxkk := m_a2) (m_zclhbitx := m_lift) (cs_elsidvfa := cs_lift)
      (v_zqfvhlrl := v_sh) (m_lkduaedg := m_aeq) (v_qdacqrgy := v_plvls)
      (m_aintkoeo := m_plvls) (m_zdlcefzp := m_bvp) (v_bmtqqbhb := v_npnf2)
      (m_owpjclho := m_capp) (m_ynmjhdgs := m_cconst) (m_acxwdugw := m_cat)
      (m_gewjbwtm := m_bvf) (m_mvpeumji := m_papp) (m_vetkiame := m_pconst)
      (m_crjlbxfc := m_snoc) (m_ibauiwoe := m_lhseq) (x_rbv := x_rbv)
      (v_wnussrrs := v_rbv)
      (ev_ppzlqbyw := evCi) (ld_kmyxbtot := ldCi) (heq_dwauttge := hinlEq)
      (op_xxftuxqp := opNpnf1) (ev_aezdhuwm := evTele) (ev_ppnjwepq := evSp)
      (ld_agzkflbe := ldEqh) (ev_jjivtrkj := evReq) (ev_oneiqvqt := evRaddr)
      (ev_lsutwlwt := evEqa) (heq_fqzdfvrt := heqa1)
      (ld_pjhbjhbm := ldLsCons) (ld_rlsiriab := ldLsNil)
      (ev_ihcqjonn := evLen) (heq_ljvksbho := hlen3)
      (ev_nggoypss := evA0) (ev_cnezlkip := evA1) (ev_huindbxu := evA2)
      (op_fdqhdobe := opSh) (ev_jxwhtakm := evLift) (ev_yzlxejwx := evAeq)
      (heq_dffqylzl := haeq1) (ev_rshtqdit := evPlvls) (op_qoynajrk := opNpnf2)
      (ev_lzaulhuz := evBvp) (hm_gkullxtv := hmCconst) (ev_pukzvexx := evBvf)
      (ev_zakitowg := evCat) (ev_xdgdcvtc := evCapp) (hm_onqkidpr := hmPconst)
      (ev_poainfkt := evSnoc) (ev_qfktqfdx := evPapp) (ev_qpavrhxx := evLhseq)
      (heq_kihrgkgj := hlhseq1) (ld_pswmmysh := ldRhs) (op_bhztbkor := opR1)
      (op_lhzlvbth := opR2) (heq_txslvrxe := hrbvEq) (hc_sgljalbe := hc) .. =>
    subst heqa1 haeq1 hlhseq1
    obtain ⟨cvIota, iotaVal, _, hfindIota, hinl_f, hIota_lvls_lt, hIota_perm0, hityTmC, _, _⟩ :=
      P.getCI_thm_of_advChecked hAdvIota haIota evCi
        (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) ldCi
    rw [haIota_eq] at hfindIota
    have hIota_lvls : cvIota.levelParams.length = bnl :=
      nat_eq_of_field_eq_u56_p (by omega) (by omega) (Value.field.inj (hinl_f.symm.trans hinlEq))
    have hIota_perm : cvIota.levelParams.Perm (List.range bnl) := by rw [← hIota_lvls]; exact hIota_perm0
    have hnpnf1_eq : v_npnf1 = .field ((nP + nF : Nat) : F) := by
      rw [evalBinOp_add_field_p opNpnf1]; push_cast; rfl
    rw [hnpnf1_eq] at evTele
    obtain ⟨ibsI, cbsI, irem, cremI, hIota_strip, hC_strip, hIota_doms, hiremTm⟩ :=
      struct_eq_tele_tm (nP + nF) (by omega) (hityTmC 0 zeroGhost) (hcty.mono evCi.heap_extends) evTele
    simp only [Nat.zero_add] at hiremTm
    obtain ⟨H_eq, targs, hiremEq, hHeqTm, htargsRep⟩ := collect_spine_tuple_p evSp hiremTm
    obtain ⟨aEq, eqls, rfl, haEq, eqls', heqlsRep, heqlsEq⟩ := hHeqTm.const_of_load ldEqh
    have ext_h_req : Heap.Extends h m_req :=
      ((evCi.heap_extends.trans evTele.heap_extends).trans evSp.heap_extends).trans evReq.heap_extends
    have haEq_raddr := Bytes.repAddressRef_heapMono₂ addrTy
      (evReq.heap_extends.trans evRaddr.heap_extends) haEq
    obtain ⟨heqKey, hm_eqa⟩ := eq_addr_key_scoped (c := P.sc) P.htwf
      (P.hcoreGoodSub (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])))
      (rcRep_of_rcLimRep_p (hrc.mono ext_h_req)) haEq_raddr evReq evRaddr evEqa
    subst m_eqa
    change Core.keyOf P.t (ixAddr aEq) = Ix.Kernel.eqName at heqKey
    rw [heqKey] at hiremEq
    -- `eqls` has length 1: `eqls = [uEq]`
    have hke : Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» = KernelLevels.klevelListEnum :=
      Core.klevelListEnum_eq
    rw [hke] at ldLsCons ldLsNil
    have heqlsRep_r := heqlsRep.mono (evReq.heap_extends.trans evRaddr.heap_extends)
    obtain ⟨uEq', eqlsTail', rfl, -, htailRep⟩ := Lib.rep_cons_of_load heqlsRep_r ldLsCons
    have htail_nil : eqlsTail' = [] := Lib.rep_nil_of_load htailRep ldLsNil
    subst htail_nil
    have heqls_sing : ∃ uEq, eqls = [uEq] := by
      have h0 := heqlsEq (fun _ => 0)
      cases eqls with
      | nil => simp [Level.EvalEqList] at h0
      | cons uEq rest =>
        cases rest with
        | nil => exact ⟨uEq, rfl⟩
        | cons _ _ => simp [Level.EvalEqList] at h0
    cases heqls_sing with
    | intro uEq h_eq =>
      subst h_eq
      -- `targs` has length 3: `[alpha, lhs, rhs]`
      have ext_sp_raddr : Heap.Extends m_sp m_raddr := evReq.heap_extends.trans evRaddr.heap_extends
      have htargsRep_r := RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_sp_raddr htargsRep
      obtain ⟨htlen_f, hm_len⟩ := kexprList_length_spec evLen htargsRep_r
      have htargs_lt := RomBound.bounded_length_lt P.hbd
        (hsub ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [x_targs], m_raddr⟩ (by rw [hc]; simp))
        (by simp) htargsRep_r
      subst m_len
      have htargs_len : targs.length = 3 :=
        nat_eq_of_field_eq_wide_p (by omega) (by decide) (Value.field.inj (htlen_f.symm.trans hlen3))
      obtain ⟨⟨alpha, ha0_get, halphaTm⟩, hm_a0⟩ := kexprList_lookup_spec evA0 htargsRep_r
      rw [ZMod.val_zero] at ha0_get; subst m_a0
      obtain ⟨⟨lhs, ha1_get, hlhsTm⟩, hm_a1⟩ := kexprList_lookup_spec evA1 htargsRep_r
      rw [ZMod.val_one] at ha1_get; subst m_a1
      obtain ⟨⟨rhs, ha2_get, hrhsTm⟩, hm_a2⟩ := kexprList_lookup_spec evA2 htargsRep_r
      rw [show ZMod.val (2 : F) = 2 from val_natCast_wide_p (by decide)] at ha2_get; subst m_a2
      have htargs_eq : targs = [alpha, lhs, rhs] := by
        cases targs with
        | nil => simp at htargs_len
        | cons x0 t1 =>
          cases t1 with
          | nil => simp at htargs_len
          | cons x1 t2 =>
            cases t2 with
            | nil => simp at htargs_len
            | cons x2 t3 =>
              cases t3 with
              | nil =>
                simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at ha0_get ha1_get ha2_get
                subst ha0_get ha1_get ha2_get; rfl
              | cons _ _ => simp at htargs_len
      -- `expr_lift [x_raw_dom, nF - fidx, 0]` → `ExprSemEq alpha (rawDom.liftLooseBVars (nF - fidx) 0)`
      have hsh_eq : v_sh = .field ((nF - fidx : Nat) : F) := by
        rw [evalBinOp_sub_field_p opSh]
        congr 1
        have h1 : ((nF - fidx : Nat) : F) + (fidx : F) = (nF : F) := by
          rw [← Nat.cast_add, Nat.sub_add_cancel (by omega)]
        linear_combination -h1
      rw [hsh_eq] at evLift
      have ext_h_raddr : Heap.Extends h m_raddr := ext_h_req.trans evRaddr.heap_extends
      have hliftTm := Decl.expr_lift_local_bounded (k := nP + fidx) (shift := nF - fidx) (cut := 0)
        (Nat.zero_le _) (by omega) (by decide)
        (P.hbdSub (fun cl (hcl : cl ∈ cs_lift) => hsub cl (by rw [hc]; simp [hcl])))
        (hraw.mono ext_h_raddr) (by simpa using evLift)
      rw [show nP + fidx + (nF - fidx) = nP + nF by omega] at hliftTm
      have hIota_alpha := Decl.kexpr_struct_eq_tm_one (halphaTm.mono evLift.heap_extends) hliftTm evAeq
      -- Build `lhs` expected expression and match via `kexpr_struct_eq`
      have hplvlsRep := build_param_lvls_range_start (start := 0) (n := bnl) (by omega) evPlvls
      have hnpnf2_eq : v_npnf2 = .field ((nP + nF : Nat) : F) := by
        rw [evalBinOp_add_field_p opNpnf2]; push_cast; rfl
      rw [hnpnf2_eq] at evBvp
      have hbvpRep := bvars_desc_tm_p (κ := Core.keyOf P.t) (Γ := zeroGhost)
        (k := nP + nF) (start := nP + nF) (cnt := nP) (by omega) (le_refl _) (by omega) evBvp
      have ext_h_bvp : Heap.Extends h m_bvp :=
        (((ext_h_raddr.trans evLift.heap_extends).trans evAeq.heap_extends).trans
          evPlvls.heap_extends).trans evBvp.heap_extends
      have ext_bvp_cconst : Heap.Extends m_bvp m_cconst := by rw [hmCconst]; exact Heap.Extends.snoc _ _
      have hcConstTm : Tm (Core.keyOf P.t) 0 zeroGhost m_cconst (nP + nF)
          (.const cModelKey ((List.range bnl).map .param))
          (.ptr (.enum kexprEnum) m_bvp.length) := by
        have : Resolved (Core.keyOf P.t (ixAddr aCModel)) := ⟨P.keyOf_ne_unresolved _⟩
        rw [← haCModel_eq]
        exact .const (by rw [hmCconst]; simp)
          (Bytes.repAddressRef_heapMono₂ addrTy (ext_h_bvp.trans ext_bvp_cconst) haCModel)
          (hplvlsRep.mono (evBvp.heap_extends.trans ext_bvp_cconst))
          (by simpa using LvEqList.refl ((List.range bnl).map Level.param))
      have hbvfRep := bvars_desc_tm_p (κ := Core.keyOf P.t) (Γ := zeroGhost)
        (k := nP + nF) (start := nF) (cnt := nF) (le_refl _) (by omega) (by omega) evBvf
      have hcatRep := kexprList_concat_spec (fun _ _ _ _ ext r => r.mono ext) evCat
        (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext)
          (ext_bvp_cconst.trans evBvf.heap_extends) hbvpRep) hbvfRep
      have hcAppTm := Decl.apply_spine_tm evCapp
        (hcConstTm.mono (evBvf.heap_extends.trans evCat.heap_extends)) hcatRep
      have ext_bvp_capp : Heap.Extends m_bvp m_capp :=
        (ext_bvp_cconst.trans evBvf.heap_extends).trans (evCat.heap_extends.trans evCapp.heap_extends)
      have ext_capp_pconst : Heap.Extends m_capp m_pconst := by rw [hmPconst]; exact Heap.Extends.snoc _ _
      have hpConstTm : Tm (Core.keyOf P.t) 0 zeroGhost m_pconst (nP + nF)
          (.const projKey ((List.range bnl).map .param))
          (.ptr (.enum kexprEnum) m_capp.length) := by
        have : Resolved (Core.keyOf P.t (ixAddr aProj)) := ⟨P.keyOf_ne_unresolved _⟩
        rw [← haProj_eq]
        exact .const (by rw [hmPconst]; simp)
          (Bytes.repAddressRef_heapMono₂ addrTy ((ext_h_bvp.trans ext_bvp_capp).trans ext_capp_pconst) haProj)
          (hplvlsRep.mono ((evBvp.heap_extends.trans ext_bvp_capp).trans ext_capp_pconst))
          (by simpa using LvEqList.refl ((List.range bnl).map Level.param))
      have hsnocRep := kexprList_snoc_spec (fun _ _ _ _ ext r => r.mono ext) evSnoc
        (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) (ext_bvp_capp.trans ext_capp_pconst) hbvpRep)
        (hcAppTm.mono ext_capp_pconst)
      have hpAppTm := Decl.apply_spine_tm evPapp (hpConstTm.mono evSnoc.heap_extends) hsnocRep
      have ext_raddr_papp : Heap.Extends m_raddr m_papp :=
        ((((evLift.heap_extends.trans evAeq.heap_extends).trans evPlvls.heap_extends).trans
          evBvp.heap_extends).trans ext_bvp_capp).trans
            ((ext_capp_pconst.trans evSnoc.heap_extends).trans evPapp.heap_extends)
      have hIota_lhs := Decl.kexpr_struct_eq_tm_one (hlhsTm.mono ext_raddr_papp) hpAppTm evLhseq
      -- `rhs = .bvar (nF - 1 - fidx)`
      obtain ⟨rbv_f, hx_rbv, -, ⟨-, hrhs_eq⟩ | ⟨_, hd0, _⟩⟩ :=
        (hrhsTm.mono (ext_raddr_papp.trans evLhseq.heap_extends)).bvar_of_load ldRhs
      · subst hrhs_eq
        rw [hx_rbv] at hrbvEq
        have hrbv_eq : v_rbv = .field ((nF - 1 - fidx : Nat) : F) := by
          rw [evalBinOp_sub_field_p opR1] at opR2
          rw [evalBinOp_sub_field_p opR2]
          congr 1
          have h1 : ((nF - 1 - fidx : Nat) : F) + 1 + (fidx : F) = (nF : F) := by
            rw [show (1 : F) = ((1 : Nat) : F) from rfl, ← Nat.cast_add, ← Nat.cast_add,
              show nF - 1 - fidx + 1 + fidx = nF by omega]
          linear_combination -h1
        rw [hrbv_eq] at hrbvEq
        have hrbv_nat : ZMod.val rbv_f = nF - 1 - fidx := by
          have h1 := congrArg ZMod.val (Value.field.inj hrbvEq)
          rwa [val_natCast_wide_p (by omega)] at h1
        rw [hrbv_nat] at htargs_eq
        rw [htargs_eq] at hiremEq
        exact ⟨cvIota, iotaVal, ibsI, cbsI, cremI, uEq, alpha, lhs,
          hfindIota, hIota_lvls, hIota_perm, hiremEq ▸ hIota_strip, hC_strip,
          hIota_doms, hIota_alpha, hIota_lhs⟩
      · exact absurd hd0 (by omega)

/-! ## Section 3: `KernelModeled::check_member_projs` -/

private theorem check_member_projs_go (P : ProjsCtx.{u})
    {tModelKey cModelKey : KKey} {aTM aCM : Bytes.Address}
    {x_rc x_t_model x_c_model x_tty x_cty_m x_aset : SourceValue F}
    {tyTPos ctyMPos : KExpr} {nP bnl nF : Nat}
    (hnP : nP < 72057594037927936) (hbnl : bnl < 4294967296)
    (hnF : nF < 72057594037927936)
    (haTM_eq : Core.keyOf P.t (ixAddr aTM) = tModelKey)
    (haCM_eq : Core.keyOf P.t (ixAddr aCM) = cModelKey)
    (hAdvTM : AdvChecked P.calls P.bAddr P.t P.lim P.csFam P.advAs aTM) :
    ∀ (rem fidx : Nat) (hf : fidx + rem = nF)
      {fteleE cteleE : KExpr} {bsPref : List (KExpr × Ix.Kernel.BinderMeta)}
      {x_ftele x_ctele x_s r : SourceValue F} {bytes : List UInt8}
      {h h' : Heap F} {cs : List (Call F)},
      ctyMPos.stripPis (nP + fidx) = some (bsPref, cteleE) →
      Claim.RCLimRep P.t P.bAddr P.lim h x_rc →
      Bytes.RepAddressRef addrTy h aTM x_t_model →
      Bytes.RepAddressRef addrTy h aCM x_c_model →
      Tm (Core.keyOf P.t) 0 zeroGhost h 0 tyTPos x_tty →
      Tm (Core.keyOf P.t) 0 zeroGhost h 0 ctyMPos x_cty_m →
      Tm (Core.keyOf P.t) (nP + 1) zeroGhost h 0 fteleE x_ftele →
      Tm (Core.keyOf P.t) 0 zeroGhost h (nP + fidx) cteleE x_ctele →
      AddrMapAll addrMapEnum (fun _ k _ =>
        AdvChecked P.calls P.bAddr P.t P.lim P.csFam P.advAs k) h x_aset →
      L1.Stream h bytes x_s →
      (∀ cl ∈ cs, cl ∈ P.calls) →
      ObsFn Obs.W "KernelModeled::check_member_projs"
        [x_rc, x_t_model, x_c_model, x_tty, x_cty_m, x_ftele, x_ctele,
         .field (nP : F), .field (bnl : F), .field (nF : F), .field (fidx : F),
         x_aset, x_s] h r h' cs →
      ∃ (bytes' : List UInt8) (projKeyAt : Nat → KKey)
        (bsRaw : List (KExpr × Ix.Kernel.BinderMeta)) (remRaw : KExpr),
        L1.Stream h' bytes' r ∧
        ctyMPos.stripPis (nP + nF) = some (bsRaw, remRaw) ∧
        ∀ k (hk1 : fidx ≤ k) (hk2 : k < nF),
          ∃ (fdom frest rawDom : KExpr) (fbm : Ix.Kernel.BinderMeta),
            projFieldTeleFrom nP bnl projKeyAt fidx fteleE (k - fidx) = some (.forallE fdom frest fbm) ∧
            (bsRaw.map Prod.fst)[nP + k]? = some rawDom ∧
            ∃ fp : FieldProjFacts P.t P.E P.env tModelKey cModelKey tyTPos ctyMPos
                nP bnl nF k fdom rawDom,
              fp.projKey = projKeyAt k := by
  intro rem
  induction rem with
  | zero =>
    intro fidx hf fteleE cteleE bsPref x_ftele x_ctele x_s r bytes h h' cs
      hstripPref hrc haTM haCM htty hcty hftele hctele haset hstr hsub ev
    have hf_eq : fidx = nF := by omega
    subst hf_eq
    match Obs.«KernelModeled::check_member_projs».obs ev with
    | .n0 (he_whiproaa := hr) (he_bzwoglyf := hh) .. =>
      subst hr hh
      exact ⟨bytes, fun _ => default, bsPref, cteleE, hstr, hstripPref,
        fun k hk1 hk2 => by omega⟩
    | .other (op_mmyajoju := op) (hne_xjnibfzs := hne) .. =>
      have h0 := evalBinOp_sub_field_p op
      rw [sub_self] at h0; exact absurd h0 hne
  | succ rem ih =>
    intro fidx hf fteleE cteleE bsPref x_ftele x_ctele x_s r bytes h h' cs
      hstripPref hrc haTM haCM htty hcty hftele hctele haset hstr hsub ev
    have hfidx_lt : fidx < nF := by omega
    match Obs.«KernelModeled::check_member_projs».obs ev with
    | .n0 (op_mmyajoju := op) .. =>
      have h1 := sub_eq_zero.mp (Value.field.inj (evalBinOp_sub_field_p op).symm)
      have h2 := nat_eq_of_field_eq_u56_p (by omega) (by omega) h1
      omega
    | .other (m_mytfjanv := m_ga1) (x_proj_i := x_proj_i) (x_s1 := x_s1)
        (m_rqeyqfxg := m_ga2) (x_iota_i := x_iota_i) (x_s2 := x_s2)
        (m_dvbcplri := m_mem1) (m_dwpofofy := m_mem2)
        (x_fdom := x_fdom) (x_frest := x_frest) (x_raw_dom := x_raw_dom) (x_crest := x_crest)
        (v_braoivot := v_plvls) (m_wzmrgkdh := m_plvls) (m_fzenyfeu := m_ciP)
        (p_thizthzk := p_ciP) (cs_pvlmmhls := cs_ciP)
        (x_pnl := x_pnl) (x_pty := x_pty) (x_pval := x_pval)
        (m_swlcccve := m_tele) (x_sdom := x_sdom) (x_rdom := x_rdom) (x_sbl := x_sbl)
        (m_tcarnugl := m_tapp) (m_copcasqk := m_tconst) (m_cnjolodp := m_tbv)
        (m_lfppkkdw := m_sdeq) (m_ijdtzsnj := m_rdeq) (m_irajczhw := m_iota)
        (cs_ahinigbx := cs_iota) (v_wmvzvmqz := v_ispw) (m_rhiljare := m_ispw)
        (m_vykxxugb := m_zero) (v_igmtlwuz := v_skip) (x_ptotoynq := v_prod)
        (m_ypudadtr := m_iz2) (x_tsjcjkps := v_iz1) (y_jsenetsm := v_iz2)
        (m_dgcnerol := m_iz1) (m_rttfbzwl := m_seg) (cs_ibzrhacr := cs_seg)
        (m_frjpldni := m_papp) (m_vsrfolds := m_pconst) (m_bumauxii := m_psnoc)
        (m_ljnjpehd := m_pbv) (v_vplmyakz := v_np1) (m_etcofxur := m_bv0)
        (v_ofxrdmeh := v_nextf) (m_qqnoexqi := m_inst) (cs_rpilhwgt := cs_inst)
        (v_tbrfkqxq := v_fidx1)
        (ev_oygkcmun := evGa1) (ev_itgeavug := evGa2)
        (ev_hbdezguh := evMem1) (heq_tmwmqsay := hmem1)
        (ev_ttmbnhat := evMem2) (heq_qyusubqf := hmem2)
        (ld_nfiezamm := ldFtele) (ld_bcodxidn := ldCtele)
        (ev_ohmoyxsf := evPlvls) (ev_fwvhehlv := evCiP) (ld_jyalnhqh := ldCiP)
        (heq_wccsaswu := hpnlEq) (ev_twysptnf := evTele) (ld_jmxucimy := ldSforall)
        (hm_vrqsfnzj := hmTconst) (ev_sviwjcrh := evTbv) (ev_kxkivixt := evTapp)
        (ev_qfvxawzi := evSdeq) (heq_etqicely := hsdeq1)
        (ev_lmsixqsg := evRdeq) (heq_phxkvdrh := hrdeq1)
        (ev_kuvxqlxk := evIota) (hm_veyibxeq := hmZero) (ev_tvyispuf := evIspw)
        (ev_qvdjszsf := evIz1) (ev_nrexoriz := evIz2) (op_lzywdmby := opProd)
        (op_jfxmwjpc := opSkip) (sg_aajbpuup := sgPure)
        (hm_epsflryl := hmPconst) (op_tuqnxbyn := opNp1) (ev_iomwrmqj := evPbv)
        (hm_msgufuwo := hmBv0) (ev_wxpjymkh := evPsnoc) (ev_cmnyzdwt := evPapp)
        (ev_tytrytzi := evInst) (op_tvzdyeak := opFidx1) (ev_gpyzuuyd := evRec)
        (hc_kjrxaxhl := hc) .. =>
      subst hmem1 hmem2 hsdeq1 hrdeq1
      -- 1. Deserialize `proj_i` and `iota_i` from `x_s`, check membership in `x_aset`
      obtain ⟨aProj, bytes1, _, _, -, htup1, haProj_ga1, hstr1, -, -⟩ := Decl.get_address_spec hstr evGa1
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup1
      obtain ⟨rfl, rfl⟩ := htup1
      obtain ⟨aIota, bytes2, _, _, -, htup2, haIota_ga2, hstr2, -, -⟩ := Decl.get_address_spec hstr1 evGa2
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup2
      obtain ⟨rfl, rfl⟩ := htup2
      have ext_h_ga2 : Heap.Extends h m_ga2 := evGa1.heap_extends.trans evGa2.heap_extends
      have haProj_ga2 := Bytes.repAddressRef_heapMono₂ addrTy evGa2.heap_extends haProj_ga1
      have hAdvProj := P.advChecked_of_aset_member
        (AddrMapAll.mono (fun _ _ _ _ _ x => x) ext_h_ga2 haset) haProj_ga2 evMem1
      have ext_h_mem1 : Heap.Extends h m_mem1 := ext_h_ga2.trans evMem1.heap_extends
      have hAdvIota := P.advChecked_of_aset_member
        (AddrMapAll.mono (fun _ _ _ _ _ x => x) ext_h_mem1 haset)
        (Bytes.repAddressRef_heapMono₂ addrTy evMem1.heap_extends haIota_ga2) evMem2
      have ext_h_mem2 : Heap.Extends h m_mem2 := ext_h_mem1.trans evMem2.heap_extends
      -- 2. Peel `ftele` (at `d = nP + 1, k = 0`) and `ctele` (at `d = 0, k = nP + fidx`)
      obtain ⟨fdom, frest, ℓf, rfl, hfdomTm, hfrestTm, -⟩ := (hftele.mono ext_h_mem2).forallE_of_load ldFtele
      obtain ⟨rawDom, crest, ℓc, rfl, hrawTm, hcrestTm, -⟩ := (hctele.mono ext_h_mem2).forallE_of_load ldCtele
      -- 3. `build_param_lvls_range` + `get_ci [x_proj_i]` → `Defn`
      have hplvlsRep := build_param_lvls_range_start (start := 0) (n := bnl) (by omega) evPlvls
      have ext_ga2_plvls : Heap.Extends m_ga2 m_plvls :=
        (evMem1.heap_extends.trans evMem2.heap_extends).trans evPlvls.heap_extends
      obtain ⟨cvProj, projVal, projHint, hProj_nonAux, hfindProj, hpnl_f, hProj_lvls_lt,
          hProj_perm0, hptyTmC, hpvalTmC, _, hpvalCr⟩ :=
        P.getCI_defn_of_advChecked hAdvProj
          (Bytes.repAddressRef_heapMono₂ addrTy ext_ga2_plvls haProj_ga2) evCiP
          (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) ldCiP
      have hProj_lvls : cvProj.levelParams.length = bnl :=
        nat_eq_of_field_eq_u56_p (by omega) (by omega) (Value.field.inj (hpnl_f.symm.trans hpnlEq))
      have hProj_perm : cvProj.levelParams.Perm (List.range bnl) := by rw [← hProj_lvls]; exact hProj_perm0
      -- 4. `struct_eq_tele [x_pty, x_tty, nP]`, `sdom`, `rdom`
      have ext_h_ciP : Heap.Extends h m_ciP :=
        (ext_h_mem2.trans evPlvls.heap_extends).trans evCiP.heap_extends
      obtain ⟨pbsP, tbsP, premP, tremP, hProj_strip0, hT_strip, hProj_pdoms, hpremPTm⟩ :=
        struct_eq_tele_tm nP (by omega) (hptyTmC 0 zeroGhost) (htty.mono ext_h_ciP) evTele
      simp only [Nat.zero_add] at hpremPTm
      obtain ⟨sdom, rdom, ℓs, rfl, hsdomTm, hrdomTm, hℓsRep⟩ := hpremPTm.forallE_of_load ldSforall
      have ext_tele_tconst : Heap.Extends m_tele m_tconst := by rw [hmTconst]; exact Heap.Extends.snoc _ _
      have ext_h_tconst : Heap.Extends h m_tconst :=
        (ext_h_ciP.trans evTele.heap_extends).trans ext_tele_tconst
      have htConstTm : Tm (Core.keyOf P.t) 0 zeroGhost m_tconst nP
          (.const tModelKey ((List.range bnl).map .param))
          (.ptr (.enum kexprEnum) m_tele.length) := by
        have : Resolved (Core.keyOf P.t (ixAddr aTM)) := ⟨P.keyOf_ne_unresolved _⟩
        rw [← haTM_eq]
        exact .const (by rw [hmTconst]; simp)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_tconst haTM)
          (hplvlsRep.mono ((evCiP.heap_extends.trans evTele.heap_extends).trans ext_tele_tconst))
          (by simpa using LvEqList.refl ((List.range bnl).map Level.param))
      have htbvRep := bvars_desc_tm_p (κ := Core.keyOf P.t) (Γ := zeroGhost)
        (k := nP) (start := nP) (cnt := nP) (le_refl _) (le_refl _) (by omega) evTbv
      have htAppTm := Decl.apply_spine_tm evTapp (htConstTm.mono evTbv.heap_extends) htbvRep
      have ext_tele_tapp : Heap.Extends m_tele m_tapp :=
        (ext_tele_tconst.trans evTbv.heap_extends).trans evTapp.heap_extends
      have hProj_sdom := Decl.kexpr_struct_eq_tm_one (hsdomTm.mono ext_tele_tapp) htAppTm evSdeq
      -- `rdom` opened with `openDummiesP (nP + 1) 0 0` matches `fdom` at `(d = nP + 1, k = 0)`!
      have ext_tele_sdeq : Heap.Extends m_tele m_sdeq := ext_tele_tapp.trans evSdeq.heap_extends
      have ext_mem2_sdeq : Heap.Extends m_mem2 m_sdeq :=
        ((evPlvls.heap_extends.trans evCiP.heap_extends).trans evTele.heap_extends).trans ext_tele_sdeq
      have hrdomOpen : Tm (Core.keyOf P.t) (nP + 1) zeroGhost m_sdeq 0
          (openDummiesP (nP + 1) 0 0 rdom) x_rdom := by
        have h1 := tm_openDummiesP (nP + 1) 0 0 (by simpa using hrdomTm.mono ext_tele_sdeq)
        simpa using h1
      have hProj_rdom := Decl.kexpr_struct_eq_tm_one hrdomOpen (hfdomTm.mono ext_mem2_sdeq) evRdeq
      -- 5. `check_proj_iota`
      have ext_h_rdeq : Heap.Extends h m_rdeq := ext_h_mem2.trans (ext_mem2_sdeq.trans evRdeq.heap_extends)
      have ext_ga2_rdeq : Heap.Extends m_ga2 m_rdeq :=
        (evMem1.heap_extends.trans evMem2.heap_extends).trans (ext_mem2_sdeq.trans evRdeq.heap_extends)
      have ext_mem2_rdeq : Heap.Extends m_mem2 m_rdeq := ext_mem2_sdeq.trans evRdeq.heap_extends
      obtain ⟨cvIota, iotaVal, ibsI, cbsI, cremI, uEq, alpha, lhs,
          hfindIota, hIota_lvls, hIota_perm, hIota_strip, hC_strip, hIota_doms, hIota_alpha, hIota_lhs⟩ :=
        check_proj_iota_spec P hnP hbnl (by omega) hfidx_lt rfl rfl haCM_eq hAdvIota
          (hrc.mono ext_h_rdeq)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_ga2_rdeq haProj_ga2)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_ga2_rdeq haIota_ga2)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_rdeq haCM)
          (hcty.mono ext_h_rdeq) (hrawTm.mono ext_mem2_rdeq)
          (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) evIota
      -- 6. Purity gate (`Seg_bjevqotc`)
      have ext_tele_zero : Heap.Extends m_tele m_zero :=
        ((ext_tele_sdeq.trans evRdeq.heap_extends).trans evIota.heap_extends).trans
          (by rw [hmZero]; exact Heap.Extends.snoc _ _)
      have hrepZero : RepKLevel m_zero .zero (.ptr (.enum KernelLevels.klevelEnum) m_iota.length) := by
        rw [hmZero]; exact .zero (by simp)
      have hℓs_zero := hℓsRep.mono ext_tele_zero
      have hispw_bit := pw_eq_bit evIspw
      obtain ⟨hiz1, hm_iz1⟩ := Lib.is_zero_field evIz1
      subst m_iz1
      obtain ⟨hiz2, hm_iz2⟩ := Lib.is_zero_field evIz2
      subst m_iz2
      have hpure_and_ext :
          ((nP = 0 ∧ bnl = 0) ∨
            (∀ φ, Ix.Kernel.Model.pwBit φ (Core.bmeta ℓs).pw = 0) ∨
            Nonempty (ProjPureWitness P.t P.E P.env tModelKey
              (Core.posOf cvProj.levelParams projVal) ctyMPos rawDom (Core.bmeta ℓs).pw nP bnl nF fidx)) ∧
          Heap.Extends m_ispw m_seg := by
        match sgPure with
        | .n0 (ev_dbzuvjle := evIzSkip) (he_ctsywody := hhSeg) .. =>
          obtain ⟨hskip_ne, hm_skip⟩ := Lib.is_zero_spec evIzSkip
          have hhSeg' : m_seg = m_ispw := hhSeg.trans hm_skip
          rw [hhSeg']
          rcases hispw_bit with h0 | h1
          · rw [h0] at opSkip
            have hnp_zero : nP = 0 ∧ bnl = 0 := by
              by_cases hnp0 : nP = 0 <;> by_cases hbnl0 : bnl = 0
              · exact ⟨hnp0, hbnl0⟩
              · have h1f : (nP : F) = 0 := by rw [hnp0]; rfl
                have h2f : (bnl : F) ≠ 0 := fun e => hbnl0 (nat_eq_of_field_eq_u56_p (by omega) (by omega) e)
                rw [ite_eq_left h1f] at hiz1; rw [ite_eq_right h2f] at hiz2
                rw [hiz1, hiz2] at opProd; simp only [evalBinOp, mul_zero, Except.ok.injEq] at opProd
                rw [← opProd] at opSkip; simp only [evalBinOp, add_zero, Except.ok.injEq] at opSkip
                rw [← opSkip] at hskip_ne; simp at hskip_ne
              · have h1f : (nP : F) ≠ 0 := fun e => hnp0 (nat_eq_of_field_eq_u56_p (by omega) (by omega) e)
                rw [ite_eq_right h1f] at hiz1; rw [hiz1] at opProd
                cases v_iz2 with
                | field f =>
                  simp only [evalBinOp, zero_mul, Except.ok.injEq] at opProd
                  rw [← opProd] at opSkip; simp only [evalBinOp, add_zero, Except.ok.injEq] at opSkip
                  rw [← opSkip] at hskip_ne; simp at hskip_ne
                | _ => simp [evalBinOp] at opProd
              · have h1f : (nP : F) ≠ 0 := fun e => hnp0 (nat_eq_of_field_eq_u56_p (by omega) (by omega) e)
                rw [ite_eq_right h1f] at hiz1; rw [hiz1] at opProd
                cases v_iz2 with
                | field f =>
                  simp only [evalBinOp, zero_mul, Except.ok.injEq] at opProd
                  rw [← opProd] at opSkip; simp only [evalBinOp, add_zero, Except.ok.injEq] at opSkip
                  rw [← opSkip] at hskip_ne; simp at hskip_ne
                | _ => simp [evalBinOp] at opProd
            exact ⟨Or.inl hnp_zero, Heap.Extends.refl _⟩
          · rw [h1] at evIspw
            have hpw0 : ℓs.zeronessOf = Level.zero.zeronessOf := Decl.pw_eq_one hℓs_zero hrepZero evIspw
            refine ⟨Or.inr (Or.inl fun φ => ?_), Heap.Extends.refl _⟩
            show Ix.Kernel.Model.pwBit φ ℓs.zeronessOf = 0
            rw [hpw0]; rfl
        | .other (m_mjyizhgp := m_izskip) (v_ifaknodx := v_sbl_nz) (m_fhrxiwuu := m_nz)
            (ev_dbzuvjle := evIzSkip) (ev_nsfsqdqf := evNz) (ev_ketzpkds := evPure)
            (hc_kirzjcve := hcSeg) .. =>
          obtain ⟨-, hm_izskip⟩ := Lib.is_zero_spec evIzSkip
          subst m_izskip
          have ext_tele_ispw : Heap.Extends m_tele m_ispw :=
            ext_tele_zero.trans evIspw.heap_extends
          have hsbl_nz_spec : v_sbl_nz = .field 1 → ∀ φ, Ix.Kernel.Model.pwBit φ ℓs.zeronessOf > 0 := by
            intro h1
            rw [h1] at evNz
            exact pwBit_pos_of_level_is_not_zero (hℓsRep.mono ext_tele_ispw) evNz
          have ext_h_nz : Heap.Extends h m_nz :=
            ((ext_h_rdeq.trans evIota.heap_extends).trans
              ((by rw [hmZero]; exact Heap.Extends.snoc _ _ : Heap.Extends m_iota m_zero).trans
                evIspw.heap_extends)).trans evNz.heap_extends
          have ext_ciP_nz : Heap.Extends m_ciP m_nz :=
            (evTele.heap_extends.trans ext_tele_ispw).trans evNz.heap_extends
          have ext_mem2_nz : Heap.Extends m_mem2 m_nz :=
            (evPlvls.heap_extends.trans evCiP.heap_extends).trans ext_ciP_nz
          have hpvalCr' : (Core.posOf cvProj.levelParams projVal).constsResolve P.env = true := by
            rw [Decl.constsResolve_posOf]; exact hpvalCr
          have hwit := check_proj_pure_spec P hnP hbnl (by omega) hfidx_lt haTM_eq hAdvTM
            (hrc.mono ext_h_nz) (Bytes.repAddressRef_heapMono₂ addrTy ext_h_nz haTM)
            ((hpvalTmC 0 zeroGhost).mono ext_ciP_nz) hpvalCr'
            (hcty.mono ext_h_nz) (hrawTm.mono ext_mem2_nz)
            (hℓsRep.mono (ext_tele_ispw.trans evNz.heap_extends)) hsbl_nz_spec
            (AddrMapAll.mono (fun _ _ _ _ _ x => x) ext_h_nz haset)
            (fun cl hcl => hsub cl (by rw [hc, hcSeg]; simp [hcl])) evPure
          exact ⟨Or.inr (Or.inr hwit), evNz.heap_extends.trans evPure.heap_extends⟩
      obtain ⟨hpure, ext_ispw_seg⟩ := hpure_and_ext
      -- 7. Step `ftele` via `expr_inst1 [x_frest, projApp, 0]` at `(d = nP + 1, Γ = zeroGhost, k = 0)`
      have ext_plvls_seg : Heap.Extends m_plvls m_seg :=
        (((evCiP.heap_extends.trans evTele.heap_extends).trans ext_tele_zero).trans
          evIspw.heap_extends).trans ext_ispw_seg
      have ext_ga2_seg : Heap.Extends m_ga2 m_seg := ext_ga2_plvls.trans ext_plvls_seg
      have ext_seg_pconst : Heap.Extends m_seg m_pconst := by rw [hmPconst]; exact Heap.Extends.snoc _ _
      have hpConstF : Tm (Core.keyOf P.t) (nP + 1) zeroGhost m_pconst 0
          (.const (Core.keyOf P.t (ixAddr aProj)) ((List.range bnl).map .param))
          (.ptr (.enum kexprEnum) m_seg.length) := by
        have : Resolved (Core.keyOf P.t (ixAddr aProj)) := ⟨P.keyOf_ne_unresolved _⟩
        exact .const (by rw [hmPconst]; simp)
          (Bytes.repAddressRef_heapMono₂ addrTy (ext_ga2_seg.trans ext_seg_pconst) haProj_ga2)
          (hplvlsRep.mono (ext_plvls_seg.trans ext_seg_pconst))
          (by simpa using LvEqList.refl ((List.range bnl).map Level.param))
      have hnp1_eq : v_np1 = .field ((nP + 1 : Nat) : F) := by
        rw [evalBinOp_add_field_p opNp1]; push_cast; rfl
      rw [hnp1_eq] at evPbv
      have hpbvExact := Decl.bvars_desc_exact_wide (κ := Core.keyOf P.t) (d := nP + 1) (Γ := zeroGhost)
        (top := ((nP + 1 : Nat) : F)) (cnt := (nP : F))
        (by rw [val_natCast_wide_p (by omega), val_natCast_wide_p (by omega)]; omega)
        (by rw [val_natCast_wide_p (by omega)]) (by omega) evPbv
      rw [val_natCast_wide_p (by omega), val_natCast_wide_p (by omega)] at hpbvExact
      have hpbvEq : ((List.range nP).map fun m =>
          (Expr.fvar (nP + 1 - (nP + 1) + m) (zeroGhost (nP + 1 - (nP + 1) + m)) : KExpr)) =
          ((List.range nP).map fun m => .fvar m (.sort .zero)) := by
        apply List.map_congr_left; intro m _; simp [zeroGhost]
      rw [hpbvEq] at hpbvExact
      have hpbvTm := repList_imp (fun _ _ _ r => r.toTm) hpbvExact
      have ext_pbv_bv0 : Heap.Extends m_pbv m_bv0 := by rw [hmBv0]; exact Heap.Extends.snoc _ _
      have hbv0Tm : Tm (Core.keyOf P.t) (nP + 1) zeroGhost m_bv0 0 (.fvar nP (.sort .zero))
          (.ptr (.enum kexprEnum) m_pbv.length) := by
        have h1 : Tm (Core.keyOf P.t) (nP + 1) zeroGhost m_bv0 0
            (.fvar (nP + 1 - 1 - (ZMod.val (0 : F) - 0)) (zeroGhost _))
            (.ptr (.enum kexprEnum) m_pbv.length) :=
          .bvarFree (by rw [hmBv0]; simp) (by rw [ZMod.val_zero]; decide) (by omega) (by rw [ZMod.val_zero]; omega)
        simpa [ZMod.val_zero, zeroGhost] using h1
      have hpsnocRep := kexprList_snoc_spec (fun _ _ _ _ ext r => r.mono ext) evPsnoc
        (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_pbv_bv0 hpbvTm) hbv0Tm
      have hpAppTm := Decl.apply_spine_tm evPapp
        (hpConstF.mono ((evPbv.heap_extends.trans ext_pbv_bv0).trans evPsnoc.heap_extends)) hpsnocRep
      have ext_mem2_papp : Heap.Extends m_mem2 m_papp :=
        ((evPlvls.heap_extends.trans ext_plvls_seg).trans
          ((ext_seg_pconst.trans evPbv.heap_extends).trans ext_pbv_bv0)).trans
            (evPsnoc.heap_extends.trans evPapp.heap_extends)
      have hnextfTm : Tm (Core.keyOf P.t) (nP + 1) zeroGhost m_inst 0
          (frest.instantiate1 (Expr.mkAppN (.const (Core.keyOf P.t (ixAddr aProj)) ((List.range bnl).map .param))
            (((List.range nP).map fun m => .fvar m (.sort .zero)) ++ [.fvar nP (.sort .zero)])) 0)
          v_nextf := by
        have h1 := SubstAux.gall (Core.keyOf P.t) .expr_inst1 _ _ _ _ _ evInst _ _ (0 : F) rfl
          (P.hbdSub (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])))
          (nP + 1) zeroGhost frest _ (hfrestTm.mono ext_mem2_papp) hpAppTm
        rwa [ZMod.val_zero] at h1
      -- 8. Recurse to `fidx + 1`
      have ext_h_inst : Heap.Extends h m_inst :=
        (ext_h_mem2.trans ext_mem2_papp).trans evInst.heap_extends
      have ext_ga2_inst : Heap.Extends m_ga2 m_inst :=
        (ext_ga2_seg.trans ((ext_seg_pconst.trans evPbv.heap_extends).trans ext_pbv_bv0)).trans
          ((evPsnoc.heap_extends.trans evPapp.heap_extends).trans evInst.heap_extends)
      have hfidx1_eq : v_fidx1 = .field ((fidx + 1 : Nat) : F) := by
        rw [evalBinOp_add_field_p opFidx1]; push_cast; rfl
      rw [hfidx1_eq] at evRec
      have hstripNext : ctyMPos.stripPis (nP + (fidx + 1)) =
          some (bsPref ++ [(rawDom, Core.bmeta ℓc)], crest) := by
        rw [show nP + (fidx + 1) = (nP + fidx) + 1 by omega]
        exact stripPis_add hstripPref (by simp [Expr.stripPis])
      obtain ⟨bytes', projKeyRest, bsRaw, remRaw, hstr', hstripRaw, hrest⟩ :=
        ih (fidx + 1) (by omega) hstripNext
          (hrc.mono ext_h_inst)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_inst haTM)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_inst haCM)
          (htty.mono ext_h_inst) (hcty.mono ext_h_inst)
          hnextfTm (by simpa [Nat.add_assoc] using hcrestTm.mono (ext_mem2_papp.trans evInst.heap_extends))
          (AddrMapAll.mono (fun _ _ _ _ _ x => x) ext_h_inst haset)
          (hstr2.mono ext_ga2_inst)
          (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) evRec
      -- 9. Combine `fidx` with `projKeyRest`
      let projKeyAt : Nat → KKey := fun k => if k = fidx then Core.keyOf P.t (ixAddr aProj) else projKeyRest k
      have hraw_get_fidx : (bsRaw.map Prod.fst)[nP + fidx]? = some rawDom := by
        have hrem_split : ∃ bsTail, crest.stripPis rem = some (bsTail, remRaw) ∧
            bsRaw = (bsPref ++ [(rawDom, Core.bmeta ℓc)]) ++ bsTail := by
          have h1 : ∃ bsTail rem', crest.stripPis rem = some (bsTail, rem') := by
            have htot : (nP + (fidx + 1)) + rem = nP + nF := by omega
            rw [← htot] at hstripRaw
            -- `stripPis` of `a + b` implies `stripPis b` on remainder
            have aux : ∀ a b (e r1 r2 : KExpr) (l1 l2 : List (KExpr × Ix.Kernel.BinderMeta)),
                e.stripPis a = some (l1, r1) → e.stripPis (a + b) = some (l2, r2) →
                ∃ lt, r1.stripPis b = some (lt, r2) ∧ l2 = l1 ++ lt := by
              intro a; induction a with
              | zero =>
                intro b e r1 r2 l1 l2 ha hab
                injection ha with hp; injection hp with h1 h2; subst h1 h2
                exact ⟨l2, by simpa using hab, rfl⟩
              | succ a iha =>
                intro b e r1 r2 l1 l2 ha hab
                cases e with
                | forallE t bd bm =>
                  simp only [Expr.stripPis, Nat.succ_add] at ha hab
                  cases ha' : bd.stripPis a with
                  | none => rw [ha'] at ha; simp at ha
                  | some p1 =>
                    rcases p1 with ⟨la, ra⟩
                    rw [ha'] at ha; injection ha with hp1; injection hp1 with h1a h1b; dsimp only at h1a h1b; subst h1a h1b
                    cases hab' : bd.stripPis (a + b) with
                    | none => rw [hab'] at hab; simp at hab
                    | some p2 =>
                      rcases p2 with ⟨lab, rab⟩
                      rw [hab'] at hab; injection hab with hp2; injection hp2 with h2a h2b; dsimp only at h2a h2b; subst h2a h2b
                      obtain ⟨lt, hlt, hleq⟩ := iha b bd ra rab la lab ha' hab'
                      exact ⟨lt, hlt, by simp [hleq]⟩
                | _ => nomatch ha
            obtain ⟨lt, hlt, _⟩ := aux (nP + (fidx + 1)) rem ctyMPos crest remRaw _ bsRaw hstripNext hstripRaw
            exact ⟨lt, remRaw, hlt⟩
          obtain ⟨bsTail, rem', htail⟩ := h1
          have h2 := stripPis_add hstripNext htail
          rw [show nP + (fidx + 1) + rem = nP + nF by omega, hstripRaw] at h2
          injection h2 with hp; injection hp with hbs hrem; subst hrem
          exact ⟨bsTail, htail, hbs⟩
        obtain ⟨bsTail, _, rfl⟩ := hrem_split
        have hpref_len : bsPref.length = nP + fidx := by
          have aux : ∀ m (e r : KExpr) (bs : List (KExpr × Ix.Kernel.BinderMeta)),
              e.stripPis m = some (bs, r) → bs.length = m := by
            intro m; induction m with
            | zero => intro e r bs hs; injection hs with hp; injection hp with h1 _; subst h1; rfl
            | succ m ihm =>
              intro e r bs hs
              cases e with
              | forallE _ bd _ =>
                simp only [Expr.stripPis] at hs
                cases hsb : bd.stripPis m with
                | none => rw [hsb] at hs; simp at hs
                | some p =>
                  rcases p with ⟨bs0, r0⟩; rw [hsb] at hs
                  injection hs with hp; injection hp with h1 _; dsimp only at h1; subst h1
                  simp [ihm bd r0 bs0 hsb]
              | _ => nomatch hs
          exact aux (nP + fidx) ctyMPos _ bsPref hstripPref
        rw [List.map_append, List.map_append, List.getElem?_append_left (by simp [hpref_len]),
          List.getElem?_append_right (by simp [hpref_len])]
        simp [hpref_len]
      refine ⟨bytes', projKeyAt, bsRaw, remRaw, hstr', hstripRaw, fun k hk1 hk2 => ?_⟩
      rcases Nat.eq_or_lt_of_le hk1 with rfl | hgt
      · refine ⟨fdom, frest, rawDom, Core.bmeta ℓf, by simp [projFieldTeleFrom], hraw_get_fidx,
          { projKey := Core.keyOf P.t (ixAddr aProj)
            cvProj := cvProj
            projVal := projVal
            projHint := projHint
            hProj_nonAux := hProj_nonAux
            hfindProj := hfindProj
            hProj_lvls := hProj_lvls
            hProj_perm := hProj_perm
            iotaKey := Core.keyOf P.t (ixAddr aIota)
            cvIota := cvIota
            iotaVal := iotaVal
            hfindIota := hfindIota
            hIota_lvls := hIota_lvls
            hIota_perm := hIota_perm
            pbsP := pbsP
            tbsP := tbsP
            tremP := tremP
            sdom := sdom
            rdom := rdom
            sbm := Core.bmeta ℓs
            hProj_strip := hProj_strip0
            hT_strip := hT_strip
            hProj_pdoms := hProj_pdoms
            hProj_sdom := hProj_sdom
            hProj_rdom := hProj_rdom
            ibsI := ibsI
            cbsI := cbsI
            cremI := cremI
            uEq := uEq
            alpha := alpha
            lhs := lhs
            hIota_strip := hIota_strip
            hC_strip := hC_strip
            hIota_doms := hIota_doms
            hIota_alpha := hIota_alpha
            hIota_lhs := hIota_lhs
            hpure := hpure },
          by simp [projKeyAt]⟩
      · obtain ⟨fdom', frest', rawDom', fbm', htele', hraw', fp', hfp_key⟩ := hrest k hgt hk2
        have hk_sub : k - fidx = (k - (fidx + 1)) + 1 := by omega
        have htele_eq : projFieldTeleFrom nP bnl projKeyAt fidx (.forallE fdom frest (Core.bmeta ℓf)) (k - fidx) =
            projFieldTeleFrom nP bnl projKeyRest (fidx + 1)
              (frest.instantiate1 (Expr.mkAppN (.const (Core.keyOf P.t (ixAddr aProj)) ((List.range bnl).map .param))
                (((List.range nP).map fun m => .fvar m (.sort .zero)) ++ [.fvar nP (.sort .zero)])) 0)
              (k - (fidx + 1)) := by
          rw [hk_sub, projFieldTeleFrom_succ]
          simp only [projKeyAt, ↓reduceIte]
          exact projFieldTeleFrom_congr (k - (fidx + 1)) fun j _ => by
            simp only [show fidx + 1 + j ≠ fidx by omega, ↓reduceIte]
        exact ⟨fdom', frest', rawDom', fbm', htele_eq.trans htele', hraw', fp',
          by simp [projKeyAt, show k ≠ fidx by omega, hfp_key]⟩

/-! ## Section 4: `KernelModeled::check_member_projs_start` -/

private theorem get_ci_ind_tmCExact {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    (ht : t.check = .ok ()) (hbd : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hB : FamBlockRecord E₀ B cb ms)
    {pos : Nat} {ind : Ixon.Inductive} {ty₀ tyA : KExpr}
    (hpos_u64 : pos < UInt64.size) (hmi : ms[pos]? = some (.indc ind))
    (hread : (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B ms)).read ind.typ = .ok ty₀)
    (hlbb : ty₀.looseBVarsBounded 0 = true)
    (hdef : ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true)
    (hcanon : LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
      ((L1.mutsRootOffset ms.toList pos : Nat) : F) ind.typ ty₀ = some tyA)
    {aT : Bytes.Address} {x_t_addr ptr x_tnl x_tty x_tnp x_tni x_tnc w1 w2 w3 : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (haT_eq : ixAddr aT = Core.iprjAddr B pos) (haT : Bytes.RepAddressRef addrTy h aT x_t_addr)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (ev : ObsFn Obs.W "Ingress::get_ci" [x_t_addr] h ptr h' cs)
    (hld : loadValue h' ptr = .ok (.construct kciEnum "Induct" [x_tnl, x_tty, x_tnp, x_tni, x_tnc, w1, w2, w3])) :
    ind.lvls.toNat < 4294967296 ∧ ind.params.toNat < 72057594037927936 ∧
    x_tnl = .field (ind.lvls.toNat : F) ∧ x_tnp = .field (ind.params.toNat : F) ∧
    Decl.TmCExact (Core.keyOf t) h' tyA x_tty := by
  obtain ⟨rawBytes, cM, hhM, hbaM, hexM, -, htrM⟩ :=
    L1.get_ci_block_trace_spec (bounded_sub hsub hbd) haT ev
  have hrecM : recordOf E₀ (ixAddr aT) = some (memberProjection B pos (.indc ind)) := by
    rw [haT_eq, ← LoadedReads.memberAddr_indc]; exact hB.members pos (.indc ind) hmi
  have hcM_eq : cM = memberProjection B pos (.indc ind) :=
    hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hrecM) (Core.hashed_mono hsub hhM) hbaM hexM
  subst hcM_eq
  unfold L1.GetCIBlockTraceResult at htrM; simp only [memberProjection] at htrM
  obtain ⟨-, blkBytes, cb', ms', ind', blobs, tree, plan, v, hhBlk, hbaBlk, hexBlk, hmuts',
    hmi', hhp, built, planned, hldv, hraw, hlevs⟩ := htrM
  have hcb_eq : cb' = cb :=
    hS.record_eq ((hS.recordOf_eq_recordAt B).symm.trans hB.record) (Core.hashed_mono hsub hhBlk) hbaBlk hexBlk
  subst cb'
  have hms_eq : ms' = ms := Ixon.ConstantInfo.muts.inj (hmuts'.symm.trans hB.muts)
  subst ms'
  have hpos_toNat : pos.toUInt64.toNat = pos := by
    change (UInt64.ofNat _).toNat = _; rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hpos_u64]
  rw [hpos_toNat, Array.getElem?_toList, hmi] at hmi'
  have hind_eq : ind' = ind := Ixon.MutConst.indc.inj (Option.some.inj hmi').symm
  subst ind'
  obtain ⟨hlvls_lt, hnp_lt, -, -, -, tyPtr, _, _, -, -, hv_eq, rty⟩ := hraw
  rw [hpos_toNat] at planned
  rw [hld] at hldv; injection hldv with hveq; rw [← hveq] at hv_eq
  simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv_eq
  obtain ⟨-, -, hnl_eq, hty_eq, hnp_eq, -, -, -, -, -⟩ := hv_eq
  subst hty_eq
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := fun x bs hm => by
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hrun := hS.blobs bs (Core.hashed_mono hsub hhx); rwa [hxa] at hrun
  have hagree : L1.BlobReadAgreement (readCtx t (fun x => E₀.blobs.get? x)).blob blobs :=
    L1.BlobReadAgreement.of_mem hblob
  obtain ⟨cnt, tyPtr', flds, hvc, hbl⟩ := hlevs
  rw [← hveq] at hvc
  simp only [Value.construct.injEq, List.cons.injEq] at hvc
  obtain ⟨-, -, -, htp, -⟩ := hvc; subst htp
  obtain ⟨tyA', hcanon', -, htm⟩ :=
    annotation_canon_range_exact ht hlvls_lt (LoadedReads.blockSelf_key t B ms) hagree rty built
      planned hbl hread hlbb hdef
  have htyA_eq : tyA' = tyA := Option.some.inj (hcanon'.symm.trans hcanon)
  subst htyA_eq
  exact ⟨hlvls_lt, hnp_lt, hnl_eq, hnp_eq, htm⟩

private theorem get_ci_ctor_tmCExact {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    (ht : t.check = .ok ()) (hbd : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hB : FamBlockRecord E₀ B cb ms)
    {pos : Nat} {ind : Ixon.Inductive} {ct : Ixon.Constructor} {ty₀ tyA : KExpr}
    (hpos_u64 : pos < UInt64.size) (hmi : ms[pos]? = some (.indc ind))
    (hct : ind.ctors[0]? = some ct)
    (hread : (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B ms)).read ct.typ = .ok ty₀)
    (hlbb : ty₀.looseBVarsBounded 0 = true)
    (hdef : ty₀.allLevelParamsDefined (List.range ct.lvls.toNat) = true)
    (hcanon : LoadedReads.canonAnn cb (List.range ct.lvls.toNat)
      (((L1.mutsRootOffset ms.toList pos : Nat) : F) + 1 + ((0 : Nat) : F)) ct.typ ty₀ = some tyA)
    {aC : Bytes.Address} {x_c_addr ptr x_cnl x_cty w1 w2 w3 x_cnp x_cnf w4 : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (haC_eq : ixAddr aC = Core.cprjAddr B pos 0) (haC : Bytes.RepAddressRef addrTy h aC x_c_addr)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (ev : ObsFn Obs.W "Ingress::get_ci" [x_c_addr] h ptr h' cs)
    (hld : loadValue h' ptr = .ok (.construct kciEnum "Ctor" [x_cnl, x_cty, w1, w2, w3, x_cnp, x_cnf, w4])) :
    ct.lvls.toNat < 4294967296 ∧ ct.params.toNat < 72057594037927936 ∧
    ct.fields.toNat < 72057594037927936 ∧
    x_cnl = .field (ct.lvls.toNat : F) ∧ x_cnp = .field (ct.params.toNat : F) ∧
    x_cnf = .field (ct.fields.toNat : F) ∧
    Decl.TmCExact (Core.keyOf t) h' tyA x_cty := by
  obtain ⟨rawBytes, cM, hhM, hbaM, hexM, -, htrM⟩ :=
    L1.get_ci_block_trace_spec (bounded_sub hsub hbd) haC ev
  have hrecM : recordOf E₀ (ixAddr aC) = some (constructorProjection B pos 0) := by
    rw [haC_eq, ← LoadedReads.ctorAddr_eq_cprjAddr]
    exact hB.ctors pos ind 0 hmi (Array.getElem?_eq_some_iff.mp hct).1
  have hcM_eq : cM = constructorProjection B pos 0 :=
    hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hrecM) (Core.hashed_mono hsub hhM) hbaM hexM
  subst hcM_eq
  unfold L1.GetCIBlockTraceResult at htrM; simp only [constructorProjection] at htrM
  obtain ⟨-, -, blkBytes, cb', ms', ind', ct', blobs, tree, plan, v, hhBlk, hbaBlk, hexBlk, hmuts',
    hmi', hct', hhp, built, planned, hldv, hraw, hlevs⟩ := htrM
  have hcb_eq : cb' = cb :=
    hS.record_eq ((hS.recordOf_eq_recordAt B).symm.trans hB.record) (Core.hashed_mono hsub hhBlk) hbaBlk hexBlk
  subst cb'
  have hms_eq : ms' = ms := Ixon.ConstantInfo.muts.inj (hmuts'.symm.trans hB.muts)
  subst ms'
  have hpos_toNat : pos.toUInt64.toNat = pos := by
    change (UInt64.ofNat _).toNat = _; rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hpos_u64]
  rw [hpos_toNat, Array.getElem?_toList, hmi] at hmi'
  have hind_eq : ind' = ind := Ixon.MutConst.indc.inj (Option.some.inj hmi').symm
  subst ind'
  have h0_toNat : (0 : Nat).toUInt64.toNat = 0 := rfl
  rw [h0_toNat, Array.getElem?_toList, hct] at hct'
  have hct_eq : ct' = ct := (Option.some.inj hct').symm
  subst ct'
  obtain ⟨hlvls_lt, -, hnp_lt, hnf_lt, -, tyPtr, _, _, -, -, hv_eq, rty⟩ := hraw
  rw [hpos_toNat, h0_toNat] at planned
  rw [hld] at hldv; injection hldv with hveq; rw [← hveq] at hv_eq
  simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv_eq
  obtain ⟨-, -, hnl_eq, hty_eq, -, -, -, hnp_eq, hnf_eq, -⟩ := hv_eq
  subst hty_eq
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := fun x bs hm => by
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hrun := hS.blobs bs (Core.hashed_mono hsub hhx); rwa [hxa] at hrun
  have hagree : L1.BlobReadAgreement (readCtx t (fun x => E₀.blobs.get? x)).blob blobs :=
    L1.BlobReadAgreement.of_mem hblob
  obtain ⟨cnt, tyPtr', flds, hvc, hbl⟩ := hlevs
  rw [← hveq] at hvc
  simp only [Value.construct.injEq, List.cons.injEq] at hvc
  obtain ⟨-, -, -, htp, -⟩ := hvc; subst htp
  obtain ⟨tyA', hcanon', -, htm⟩ :=
    annotation_canon_range_exact ht hlvls_lt (LoadedReads.blockSelf_key t B ms) hagree rty built
      planned hbl hread hlbb hdef
  have htyA_eq : tyA' = tyA := Option.some.inj (hcanon'.symm.trans hcanon)
  subst htyA_eq
  exact ⟨hlvls_lt, hnp_lt, hnf_lt, hnl_eq, hnp_eq, hnf_eq, htm⟩

theorem check_member_projs_start_spec (P : ProjsCtx.{u})
    {ms : Array Ixon.MutConst} {g : KKey → KKey}
    (hB : FamBlockRecord P.E₀ P.B P.cb ms)
    {pos : Nat} {ind : Ixon.Inductive} {ct : Ixon.Constructor}
    {ty₀_T tyA_T ty₀_C tyA_C : KExpr} {bsT : List (KExpr × Ix.Kernel.BinderMeta)}
    {structSort : KLevel}
    {bB aT aTM : Bytes.Address}
    {x_rc x_block x_t_addr x_t_model x_src x_dst x_aset x_np x_bnl x_s r : SourceValue F}
    {bytes : List UInt8} {h h' : Heap F} {cs : List (Call F)}
    (hpos_u64 : pos < UInt64.size) (hpos_56 : pos < 72057594037927936)
    (hmi : ms[pos]? = some (.indc ind)) (hct : ind.ctors[0]? = some ct)
    (hni0 : ind.indices.toNat = 0) (hnc1 : ind.ctors.size = 1)
    (hcnl : ct.lvls.toNat = ind.lvls.toNat) (hcnp : ct.params.toNat = ind.params.toNat)
    (hnf_pos : 0 < ct.fields.toNat)
    (hT_sort : tyA_T.stripPis ind.params.toNat = some (bsT, .sort structSort))
    (hT_sort_nz : structSort.isNeverZero = true)
    (hread_T : (exprReader P.t (fun x => P.E₀.blobs.get? x) P.cb id (blockSelf P.t P.B ms)).read ind.typ = .ok ty₀_T)
    (hlbb_T : ty₀_T.looseBVarsBounded 0 = true)
    (hdef_T : ty₀_T.allLevelParamsDefined (List.range ind.lvls.toNat) = true)
    (hcanon_T : LoadedReads.canonAnn P.cb (List.range ind.lvls.toNat)
      ((L1.mutsRootOffset ms.toList pos : Nat) : F) ind.typ ty₀_T = some tyA_T)
    (hA_def_T : tyA_T.allLevelParamsDefined (List.range ind.lvls.toNat) = true)
    (hread_C : (exprReader P.t (fun x => P.E₀.blobs.get? x) P.cb id (blockSelf P.t P.B ms)).read ct.typ = .ok ty₀_C)
    (hlbb_C : ty₀_C.looseBVarsBounded 0 = true)
    (hdef_C : ty₀_C.allLevelParamsDefined (List.range ct.lvls.toNat) = true)
    (hcanon_C : LoadedReads.canonAnn P.cb (List.range ct.lvls.toNat)
      (((L1.mutsRootOffset ms.toList pos : Nat) : F) + 1 + ((0 : Nat) : F)) ct.typ ty₀_C = some tyA_C)
    (hA_def_C : tyA_C.allLevelParamsDefined (List.range ct.lvls.toNat) = true)
    (hbB_eq : ixAddr bB = P.B) (haT_eq : ixAddr aT = Core.iprjAddr P.B pos)
    (haTM_eq : Core.keyOf P.t (ixAddr aTM) = g (Core.keyOf P.t (Core.iprjAddr P.B pos)))
    (hAdvTM : AdvChecked P.calls P.bAddr P.t P.lim P.csFam P.advAs aTM)
    (hrc : Claim.RCLimRep P.t P.bAddr P.lim h x_rc)
    (hbB : Bytes.RepAddressRef addrTy h bB x_block)
    (haT : Bytes.RepAddressRef addrTy h aT x_t_addr)
    (haTM : Bytes.RepAddressRef addrTy h aTM x_t_model)
    (hrm : Decl.RenameMap (Core.keyOf P.t) (Core.keyOf P.t) g h x_src x_dst)
    (haset : AddrMapAll addrMapEnum (fun _ k _ =>
      AdvChecked P.calls P.bAddr P.t P.lim P.csFam P.advAs k) h x_aset)
    (hstr : L1.Stream h bytes x_s)
    (hsub : ∀ cl ∈ cs, cl ∈ P.calls)
    (ev : ObsFn Obs.W "KernelModeled::check_member_projs_start"
      [x_rc, x_block, .field (pos : F), x_t_addr, x_t_model, x_src, x_dst, x_aset,
       x_np, x_bnl, x_s] h r h' cs) :
    ∃ bytes', L1.Stream h' bytes' r ∧
      Nonempty (MemberProjFacts P.t P.E P.env P.B ms g pos tyA_T tyA_C) := by
  have : ∀ a, Resolved (Core.keyOf P.t a) := fun a => ⟨P.keyOf_ne_unresolved a⟩
  match Obs.«KernelModeled::check_member_projs_start».obs ev with
  | .run (m_yrvbrqje := m_ac) (cs_yceqlsmy := cs_ac) (m_muijqqcb := m_cm)
      (m_uesimoai := m_ciT) (p_mmwothor := p_ciT) (cs_mukhqywn := cs_ciT)
      (x_tty := x_tty) (m_xpbxxlbv := m_ciC) (p_lxghpald := p_ciC) (cs_hbhbfyjx := cs_ciC)
      (x_cty := x_cty) (m_czuaafch := m_iz) (m_njnehjhr := m_peel)
      (v_kbpjtqhe := v_npnf1) (m_sovkspti := m_nil) (x_cbody := x_cbody)
      (m_mqnpsyld := m_app) (m_ovwhkqku := m_tconst) (v_unjlsjle := v_plvls)
      (m_yjlkrwoa := m_plvls) (m_renmyjuw := m_bv1) (v_uyylficu := v_npnf2)
      (m_vxulazih := m_eq) (m_qlihiylg := m_ren) (m_fpjikxlm := m_instp)
      (cs_aclhsoit := cs_instp) (m_dckytalq := m_bv2) (v_xlbcnnlh := v_np1)
      (m_mnowfiwk := m_pfor) (cs_uuwazjmd := cs_loop)
      (ev_jdlqxelu := evAc) (ev_urftofoe := evRenA) (ev_owclozni := evCiT)
      (ld_qmougpxj := ldCiT) (heq_lfxjktkx := hbnlEq) (heq_mahoecxe := hnpEq)
      (ev_fasmjnpt := evCiC) (ld_zwnkricu := ldCiC) (ev_dikajveo := evIz)
      (op_zzyiqkxb := opNpnf1) (hm_ldwksjco := hmNil) (ev_bnsyfvjh := evPeel)
      (hm_wiofbzvu := hmTconst) (ev_aofyrxdk := evPlvls) (op_xvyhcsaj := opNpnf2)
      (ev_gdvqdbam := evBv1) (ev_yiggsgzi := evApp) (ev_klqpjhjg := evEq)
      (heq_uqbuhigu := heq1) (ev_rmixwjpg := evRen) (op_vzseefkv := opNp1)
      (ev_bgblmhzs := evBv2) (ev_iweyujte := evInstp) (ev_glsizmat := evPfor)
      (ev_bmhjwqii := evLoop) (hc_sgljalbe := hc) .. =>
    subst heq1
    obtain ⟨aC, haC_rep, haC_eq⟩ := projection_addr_ctor_bounded evAc
      (P.hbdSub (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))) hbB
    rw [hbB_eq, val_natCast_wide_p (by omega), ZMod.val_zero] at haC_eq
    obtain ⟨⟨aCM, haCM_rep, haCM_key⟩, hm_cm⟩ := Decl.rename_addr_spec evRenA haC_rep
      (hrm.mono evAc.heap_extends)
    subst m_cm
    rw [haC_eq] at haCM_key
    have ext_h_ac : Heap.Extends h m_ac := evAc.heap_extends
    -- Canonical exact reading for `x_tty` (`tyA_T`) and `x_cty` (`tyA_C`)
    obtain ⟨hbnl_lt, hnp_lt, htnl_f, htnp_f, httyExact⟩ :=
      get_ci_ind_tmCExact P.ht P.hbd P.hS hB hpos_u64 hmi hread_T hlbb_T hdef_T hcanon_T
        haT_eq (Bytes.repAddressRef_heapMono₂ addrTy ext_h_ac haT)
        (fun cl (hcl : cl ∈ cs_ciT) => hsub cl (by rw [hc]; simp [hcl])) evCiT ldCiT
    have hx_bnl : x_bnl = .field (ind.lvls.toNat : F) := hbnlEq.symm.trans htnl_f
    have hx_np : x_np = .field (ind.params.toNat : F) := hnpEq.symm.trans htnp_f
    subst hx_bnl hx_np
    obtain ⟨_, _, hnf32, _, hcnp_f, hcnf_f, hctyExact⟩ :=
      get_ci_ctor_tmCExact P.ht P.hbd P.hS hB hpos_u64 hmi hct hread_C hlbb_C hdef_C hcanon_C
        haC_eq (Bytes.repAddressRef_heapMono₂ addrTy evCiT.heap_extends haC_rep)
        (fun cl (hcl : cl ∈ cs_ciC) => hsub cl (by rw [hc]; simp [hcl])) evCiC ldCiC
    obtain ⟨-, hm_iz⟩ := Lib.is_zero_spec evIz
    subst m_iz
    -- `peel_collect` + `apply_spine_exact` + `kexpr_struct_eq_one` → literal `hC_ret` and `hC_ret_eq`!
    rw [hcnf_f] at opNpnf1 opNpnf2 evLoop
    have hnpnf1_eq : v_npnf1 = .field ((ind.params.toNat + ct.fields.toNat : Nat) : F) := by
      rw [evalBinOp_add_field_p opNpnf1]; push_cast; rfl
    rw [hnpnf1_eq] at evPeel
    have ext_ciC_nil : Heap.Extends m_ciC m_nil := by rw [hmNil]; exact Heap.Extends.snoc _ _
    obtain ⟨bsC, cret, hC_ret0, hcretExact⟩ :=
      peel_collect_body_exact (ind.params.toNat + ct.fields.toNat)
        (val_natCast_wide_p (by omega)) evPeel ((hctyExact 0 zeroGhost).mono ext_ciC_nil)
    simp only [Nat.zero_add] at hcretExact
    have hplvlsRep := build_param_lvls_range_start (start := 0) (n := ind.lvls.toNat) (by omega) evPlvls
    have ext_plvls_tconst : Heap.Extends m_plvls m_tconst := by rw [hmTconst]; exact Heap.Extends.snoc _ _
    have ext_h_tconst : Heap.Extends h m_tconst :=
      ((((ext_h_ac.trans evCiT.heap_extends).trans evCiC.heap_extends).trans
        (ext_ciC_nil.trans evPeel.heap_extends)).trans evPlvls.heap_extends).trans ext_plvls_tconst
    have htConstExact : Decl.TmExact (Core.keyOf P.t) 0 zeroGhost m_tconst
        (ind.params.toNat + ct.fields.toNat)
        (.const (Core.keyOf P.t (Core.iprjAddr P.B pos)) ((List.range ind.lvls.toNat).map .param))
        (.ptr (.enum kexprEnum) m_plvls.length) := by
      rw [← haT_eq]
      have hcell : m_tconst[m_plvls.length]? =
          some (.construct kexprEnum "Const" [x_t_addr, v_plvls]) := by rw [hmTconst]; simp
      exact .const hcell
        (Bytes.repAddressRef_heapMono₂ addrTy ext_h_tconst haT)
        (by simpa using hplvlsRep.mono ext_plvls_tconst)
    have hnpnf2_eq : v_npnf2 = .field ((ind.params.toNat + ct.fields.toNat : Nat) : F) := by
      rw [evalBinOp_add_field_p opNpnf2]; push_cast; rfl
    rw [hnpnf2_eq] at evBv1
    have hbv1Exact := bvars_desc_exact_local (κ := Core.keyOf P.t) (Γ := zeroGhost)
      (k := ind.params.toNat + ct.fields.toNat)
      (start := ind.params.toNat + ct.fields.toNat) (cnt := ind.params.toNat)
      (by omega) (le_refl _) (by omega) evBv1
    have hretExpExact := Decl.apply_spine_exact evApp (htConstExact.mono evBv1.heap_extends) hbv1Exact
    have ext_peel_app : Heap.Extends m_peel m_app :=
      ((evPlvls.heap_extends.trans ext_plvls_tconst).trans evBv1.heap_extends).trans evApp.heap_extends
    have hC_ret_eq : cret = Expr.mkAppN
        (.const (Core.keyOf P.t (Core.iprjAddr P.B pos)) ((List.range ind.lvls.toNat).map .param))
        ((List.range ind.params.toNat).map fun m =>
          .bvar (ind.params.toNat + ct.fields.toNat - 1 - m)) :=
      Decl.kexpr_struct_eq_one (hcretExact.mono ext_peel_app) hretExpExact evEq
    -- `rename` → `Decl.renameAll g tyA_C` (`TmExact` → `Tm`)
    have ext_ciC_eq : Heap.Extends m_ciC m_eq :=
      (ext_ciC_nil.trans evPeel.heap_extends).trans (ext_peel_app.trans evEq.heap_extends)
    have ext_h_eq : Heap.Extends h m_eq :=
      ((ext_h_ac.trans evCiT.heap_extends).trans evCiC.heap_extends).trans ext_ciC_eq
    have hctyMExact := Decl.rename_exact (Γ₂ := zeroGhost) evRen
      ((hctyExact 0 zeroGhost).mono ext_ciC_eq) (hrm.mono ext_h_eq)
    have hctyMTm : Tm (Core.keyOf P.t) 0 zeroGhost m_ren 0 (Decl.renameAll g tyA_C) _ := hctyMExact.toTm
    -- `bvars_desc (nP + 1) nP` + `inst_params` at `(d = nP + 1, Γ = zeroGhost, k = 0)`
    have hnp1_eq : v_np1 = .field ((ind.params.toNat + 1 : Nat) : F) := by
      rw [evalBinOp_add_field_p opNp1]; push_cast; rfl
    rw [hnp1_eq] at evBv2
    have hbv2Exact := Decl.bvars_desc_exact_wide (κ := Core.keyOf P.t)
      (d := ind.params.toNat + 1) (Γ := zeroGhost)
      (top := ((ind.params.toNat + 1 : Nat) : F)) (cnt := (ind.params.toNat : F))
      (by rw [val_natCast_wide_p (by omega), val_natCast_wide_p (by omega)]; omega)
      (by rw [val_natCast_wide_p (by omega)]) (by omega) evBv2
    rw [val_natCast_wide_p (by omega), val_natCast_wide_p (by omega)] at hbv2Exact
    have hbv2Eq : ((List.range ind.params.toNat).map fun m =>
        (Expr.fvar (ind.params.toNat + 1 - (ind.params.toNat + 1) + m)
          (zeroGhost (ind.params.toNat + 1 - (ind.params.toNat + 1) + m)) : KExpr)) =
        ((List.range ind.params.toNat).map fun m => .fvar m (.sort .zero)) := by
      apply List.map_congr_left; intro m _; simp [zeroGhost]
    rw [hbv2Eq] at hbv2Exact
    have hbv2Tm := repList_imp (fun _ _ _ r => r.toTm) hbv2Exact
    obtain ⟨doms0, ftele0, hinst0, hftele0Tm⟩ := Decl.inst_params_tm
      (P.hbdSub (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])))
      evInstp (tm_liftD_closed (ind.params.toNat + 1) (hctyMTm.mono evBv2.heap_extends)) hbv2Tm
    have hftele0_opt : (Expr.instPisAt ((List.range ind.params.toNat).map fun m => .fvar m (.sort .zero))
        (Decl.renameAll g tyA_C)).map Prod.snd = some ftele0 := by rw [hinst0]; rfl
    -- `peel_n_foralls [cty_m, nP]`
    obtain ⟨bsP0, ctele0, hstripP0, hctele0Tm, hm_pfor⟩ :=
      Decl.peel_n_foralls_tm ind.params.toNat (val_natCast_wide_p (by omega)) evPfor
        (hctyMTm.mono (evBv2.heap_extends.trans evInstp.heap_extends))
    subst m_pfor
    simp only [Nat.zero_add] at hctele0Tm
    -- Run `check_member_projs_go` from `fidx = 0`
    have ext_ren_instp : Heap.Extends m_ren m_instp := evBv2.heap_extends.trans evInstp.heap_extends
    have ext_h_instp : Heap.Extends h m_instp := (ext_h_eq.trans evRen.heap_extends).trans ext_ren_instp
    have ext_ac_instp : Heap.Extends m_ac m_instp :=
      (((evCiT.heap_extends.trans evCiC.heap_extends).trans ext_ciC_eq).trans evRen.heap_extends).trans ext_ren_instp
    have ext_ciT_instp : Heap.Extends m_ciT m_instp :=
      ((evCiC.heap_extends.trans ext_ciC_eq).trans evRen.heap_extends).trans ext_ren_instp
    obtain ⟨bytes', projKeyAt, bsRaw, remRaw, hstr', hstripRaw, hfields_go⟩ :=
      check_member_projs_go P hnp_lt hbnl_lt hnf32 haTM_eq haCM_key hAdvTM
        ct.fields.toNat 0 (Nat.zero_add _) (by simpa using hstripP0)
        (hrc.mono ext_h_instp)
        (Bytes.repAddressRef_heapMono₂ addrTy ext_h_instp haTM)
        (Bytes.repAddressRef_heapMono₂ addrTy ext_ac_instp haCM_rep)
        ((httyExact 0 zeroGhost).toTm.mono ext_ciT_instp)
        (hctyMTm.mono ext_ren_instp) hftele0Tm (by simpa using hctele0Tm)
        (AddrMapAll.mono (fun _ _ _ _ _ x => x) ext_h_instp haset)
        (hstr.mono ext_h_instp)
        (fun cl (hcl : cl ∈ cs_loop) => hsub cl (by rw [hc]; simp [hcl])) evLoop
    have hposT : Core.posOf (List.range ind.lvls.toNat) tyA_T = tyA_T := posOf_range_id _ tyA_T hA_def_T
    have hposC : Core.posOf (List.range ct.lvls.toNat) tyA_C = tyA_C := posOf_range_id _ tyA_C hA_def_C
    refine ⟨bytes', hstr', ⟨{
      ind := ind
      ct := ct
      hms := hmi
      hct := hct
      hni0 := hni0
      hnc1 := hnc1
      hcnl := hcnl
      hcnp := hcnp
      hnf_pos := hnf_pos
      bsT := bsT
      structSort := structSort
      hT_sort := hT_sort
      hT_sort_nz := hT_sort_nz
      bsC := bsC
      cret := cret
      hC_ret := by rw [hposC]; exact hC_ret0
      hC_ret_eq := hC_ret_eq
      projKeyAt := projKeyAt
      hfields := fun fidx hf => by
        obtain ⟨fdom, frest, rawDom, fbm, htele', hraw', fp, hfp_key⟩ :=
          hfields_go fidx (Nat.zero_le fidx) hf
        rw [hposT, hposC]
        exact ⟨fdom, frest, rawDom, fbm, bsRaw, remRaw,
          by rw [projFieldTeleAt_eq_from hftele0_opt fidx]; simpa using htele',
          hstripRaw, hraw', fp, hfp_key⟩ }⟩⟩

/-! ## Section 5: `KernelModeled::check_projs` loop and top-level `check_projs_facts` -/

private theorem check_projs_loop (P : ProjsCtx.{u})
    {ms : Array Ixon.MutConst} {g : KKey → KKey}
    {indTy₀ : Nat → KExpr} {ctorTy₀ : Nat → Nat → KExpr}
    {blk : List (ConstantInfo .anon)} {tys : List KExpr}
    (hB : FamBlockRecord P.E₀ P.B P.cb ms)
    (hcanonE₀ : BlockCanonReadings P.t P.E₀ P.B P.cb ms indTy₀ ctorTy₀)
    (hms_u64 : ms.size < UInt64.size) (hms_56 : ms.size < 72057594037927936)
    {bB : Bytes.Address} {x_rc x_block x_src x_dst x_aset x_np x_bnl : SourceValue F}
    (hbB_eq : ixAddr bB = P.B)
    (hMemInfo : ∀ pos (hpos : pos < ms.size) (ind : Ixon.Inductive) (ct : Ixon.Constructor),
      ms[pos]? = some (.indc ind) → ind.ctors[0]? = some ct →
      ∃ (kT kC : Nat) (ciT ciC : ConstantInfo .anon) (tyA_T tyA_C : KExpr),
        (Decl.FamilyAlias.nonrecsOf blk)[kT]? = some ciT ∧
        ciT.name = Core.keyOf P.t (Core.iprjAddr P.B pos) ∧
        tys[kT]? = some tyA_T ∧
        (Decl.FamilyAlias.nonrecsOf blk)[kC]? = some ciC ∧
        ciC.name = Core.keyOf P.t (Core.cprjAddr P.B pos 0) ∧
        tys[kC]? = some tyA_C ∧
        LoadedReads.canonAnn P.cb (List.range ind.lvls.toNat)
          ((L1.mutsRootOffset ms.toList pos : Nat) : F) ind.typ (indTy₀ pos) = some tyA_T ∧
        Annotates tyA_T (indTy₀ pos) ∧
        tyA_T.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧
        LoadedReads.canonAnn P.cb (List.range ct.lvls.toNat)
          (((L1.mutsRootOffset ms.toList pos : Nat) : F) + 1 + ((0 : Nat) : F)) ct.typ (ctorTy₀ pos 0) =
          some tyA_C ∧
        tyA_C.allLevelParamsDefined (List.range ct.lvls.toNat) = true) :
    ∀ (rem pos : Nat) (hpos : pos + rem = ms.size)
      {mems : List Ixon.MutConst} {tAs tMs : List Bytes.Address}
      {x_members x_tys x_tyM x_s r : SourceValue F} {bytes : List UInt8}
      {h h' : Heap F} {cs : List (Call F)},
      (hmLen : mems.length = rem) → (htLen : tAs.length = rem) → (htmLen : tMs.length = rem) →
      (∀ j (hj : j < rem), ixAddr (tAs[j]'(by omega)) = Core.iprjAddr P.B (pos + j)) →
      (∀ j (hj : j < rem), Core.keyOf P.t (ixAddr (tMs[j]'(by omega))) =
        g (Core.keyOf P.t (Core.iprjAddr P.B (pos + j)))) →
      (∀ j (hj : j < rem), AdvChecked P.calls P.bAddr P.t P.lim P.csFam P.advAs (tMs[j]'(by omega))) →
      Claim.RCLimRep P.t P.bAddr P.lim h x_rc →
      Bytes.RepAddressRef addrTy h bB x_block →
      RepList Obs.Names.«Lists::Node<Ixon::MutConst>» (fun _ _ _ => True) h mems x_members →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h tAs x_tys →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h tMs x_tyM →
      Decl.RenameMap (Core.keyOf P.t) (Core.keyOf P.t) g h x_src x_dst →
      AddrMapAll addrMapEnum (fun _ k _ =>
        AdvChecked P.calls P.bAddr P.t P.lim P.csFam P.advAs k) h x_aset →
      L1.Stream h bytes x_s →
      (∀ cl ∈ cs, cl ∈ P.calls) →
      ObsFn Obs.W "KernelModeled::check_projs"
        [x_rc, x_block, x_members, .field (pos : F), x_tys, x_tyM, x_src, x_dst, x_aset,
         x_np, x_bnl, x_s] h r h' cs →
      ∃ (elig : Nat → Bool),
        (∀ p, pos ≤ p → p < ms.size →
          ∀ {E₂ : Ixon.Env}, BlockCanonReadings P.t E₂ P.B P.cb ms indTy₀ ctorTy₀ →
            ∀ {b₂ : Bytes.Address} {bp₂ r₂ : SourceValue F} {h₂ h₂' : Heap F} {cs₂ : List (Call F)},
              Bytes.RepAddressRef addrTy h₂ b₂ bp₂ → ixAddr b₂ = P.B →
              ¬ View.HashedCollision { env := E₂ } [] cs₂ → Bounded cs₂ →
              ObsFn Obs.W "KernelModeled::modeled_proj_eligible"
                [bp₂, .field (p : F)] h₂ r₂ h₂' cs₂ →
              r₂ = .field (if elig p then 1 else 0)) ∧
        (∀ p, pos ≤ p → p < ms.size → elig p = true →
          ∃ (ind : Ixon.Inductive) (ct : Ixon.Constructor)
            (kT kC : Nat) (ciT ciC : ConstantInfo .anon) (tyA_T tyA_C : KExpr),
            ms[p]? = some (.indc ind) ∧ ind.ctors[0]? = some ct ∧
            (Decl.FamilyAlias.nonrecsOf blk)[kT]? = some ciT ∧
            ciT.name = Core.keyOf P.t (Core.iprjAddr P.B p) ∧
            tys[kT]? = some tyA_T ∧
            (Decl.FamilyAlias.nonrecsOf blk)[kC]? = some ciC ∧
            ciC.name = Core.keyOf P.t (Core.cprjAddr P.B p 0) ∧
            tys[kC]? = some tyA_C ∧
            Nonempty (MemberProjFacts P.t P.E P.env P.B ms g p tyA_T tyA_C)) := by
  have hcanonE : BlockCanonReadings P.t P.E P.B P.cb ms indTy₀ ctorTy₀ :=
    { check := hcanonE₀.check
      record := P.hSE.store.held hcanonE₀.record
      muts := hcanonE₀.muts
      indcs := hcanonE₀.indcs
      ind := fun i ind hi hmi =>
        let ⟨hread, hlbb, hdef⟩ := hcanonE₀.ind i ind hi hmi
        ⟨ReaderReads.exprReader_mono (fun x b hb => P.hSE.store.runBlob x b hb) hread, hlbb, hdef⟩
      ctor := fun i ind j ct hi hj hmi hct =>
        let ⟨hcidx, hread, hlbb, hdef⟩ := hcanonE₀.ctor i ind j ct hi hj hmi hct
        ⟨hcidx, ReaderReads.exprReader_mono (fun x b hb => P.hSE.store.runBlob x b hb) hread,
          hlbb, hdef⟩ }
  intro rem
  induction rem with
  | zero =>
    intro pos hpos mems tAs tMs x_members x_tys x_tyM x_s r bytes h h' cs
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    exact ⟨fun _ => false, fun p hp1 hp2 => by omega, fun p hp1 hp2 => by omega⟩
  | succ rem ih =>
    intro pos hpos mems tAs tMs x_members x_tys x_tyM x_s r bytes h h' cs
      hmLen htLen htmLen htAs htMs htAdv hrc hbB hmRep htRep htmRep hrm haset hstr hsub ev
    cases mems with
    | nil => simp at hmLen
    | cons m0 mrest =>
      cases tAs with
      | nil => simp at htLen
      | cons aT tArest =>
        cases tMs with
        | nil => simp at htmLen
        | cons aTM tMrest =>
          have hpos_lt : pos < ms.size := by omega
          match Obs.«KernelModeled::check_projs».obs ev with
          | .Nil (ld_bolbylmd := ldM) .. =>
            cases hmRep with
            | cons cell _ _ => rw [loadValue_enum_cell cell] at ldM; simp at ldM
          | .Cons (x_rest := x_rest) (x_t_addr := x_t_addr) (x_t_rest := x_t_rest)
              (x_t_model := x_t_model) (x_tm_rest := x_tm_rest) (v_laesfcfp := v_snext)
              (m_pjjxrmhe := m_seg) (cs_xhjbuhxf := cs_seg) (cs_vxexsdkc := cs_rec)
              (v_jcksnrmg := v_pos1) (ld_bolbylmd := ldM) (ld_wbmewqxq := ldT)
              (ld_ltyhajzi := ldTm) (sg_pnkutqbj := sg) (op_jkoahcno := opPos1)
              (ev_wshezqiv := evRec) (hc_zrkfjtnc := hc) .. =>
            obtain ⟨_, _, hm_eq, -, hmrestRep⟩ := Lib.rep_cons_of_load hmRep ldM
            injection hm_eq with _ hm_eq; subst hm_eq
            obtain ⟨_, _, ht_eq, haT_rep, htrestRep⟩ := Lib.rep_cons_of_load htRep ldT
            injection ht_eq with h1 h2; subst h1 h2
            obtain ⟨_, _, htm_eq, haTM_rep, htmrestRep⟩ := Lib.rep_cons_of_load htmRep ldTm
            injection htm_eq with h1 h2; subst h1 h2
            have haT_eq : ixAddr aT = Core.iprjAddr P.B pos := by
              simpa using htAs 0 (Nat.zero_lt_succ rem)
            have haTM_eq : Core.keyOf P.t (ixAddr aTM) = g (Core.keyOf P.t (Core.iprjAddr P.B pos)) := by
              simpa using htMs 0 (Nat.zero_lt_succ rem)
            have hAdvTM : AdvChecked P.calls P.bAddr P.t P.lim P.csFam P.advAs aTM := by
              simpa using htAdv 0 (Nat.zero_lt_succ rem)
            have hstep : ∃ (b0 : Bool) (bytes1 : List UInt8),
                L1.Stream m_seg bytes1 v_snext ∧ Heap.Extends h m_seg ∧
                (∀ {E₂ : Ixon.Env}, BlockCanonReadings P.t E₂ P.B P.cb ms indTy₀ ctorTy₀ →
                  ∀ {b₂ : Bytes.Address} {bp₂ r₂ : SourceValue F} {h₂ h₂' : Heap F} {cs₂ : List (Call F)},
                    Bytes.RepAddressRef addrTy h₂ b₂ bp₂ → ixAddr b₂ = P.B →
                    ¬ View.HashedCollision { env := E₂ } [] cs₂ → Bounded cs₂ →
                    ObsFn Obs.W "KernelModeled::modeled_proj_eligible"
                      [bp₂, .field (pos : F)] h₂ r₂ h₂' cs₂ →
                    r₂ = .field (if b0 then 1 else 0)) ∧
                (b0 = true →
                  ∃ (ind : Ixon.Inductive) (ct : Ixon.Constructor)
                    (kT kC : Nat) (ciT ciC : ConstantInfo .anon) (tyA_T tyA_C : KExpr),
                    ms[pos]? = some (.indc ind) ∧ ind.ctors[0]? = some ct ∧
                    (Decl.FamilyAlias.nonrecsOf blk)[kT]? = some ciT ∧
                    ciT.name = Core.keyOf P.t (Core.iprjAddr P.B pos) ∧
                    tys[kT]? = some tyA_T ∧
                    (Decl.FamilyAlias.nonrecsOf blk)[kC]? = some ciC ∧
                    ciC.name = Core.keyOf P.t (Core.cprjAddr P.B pos 0) ∧
                    tys[kC]? = some tyA_C ∧
                    Nonempty (MemberProjFacts P.t P.E P.env P.B ms g pos tyA_T tyA_C)) := by
              match sg with
              | .n1 (m_pvfaspdm := m_el) (cs_xojymjvr := cs_el) (cs_oqdnerpj := cs_st)
                  (ev_odzbepsr := evEl) (ev_lsokqsbz := evSt) (hc_ssrlebal := hcSeg) .. =>
                have hsubEl : ∀ cl ∈ cs_el, cl ∈ P.calls := fun cl hcl => hsub cl (by rw [hc, hcSeg]; simp [hcl])
                have hncEl : ¬ View.HashedCollision { env := P.E } [] cs_el := (P.hgoodSub hsubEl).1
                have hbdEl : Bounded cs_el := P.hbdSub hsubEl
                obtain ⟨ind, ct, bs₀, structSort, hmi, hct, hni0, hnc1, hcnl, hcnp, hnf_pos, hstrip₀, hnz⟩ :=
                  modeled_proj_eligible_one_facts hcanonE hncEl hbdEl hbB hbB_eq evEl
                rw [val_natCast_wide_p (by omega)] at hmi hstrip₀
                obtain ⟨kT, kC, ciT, ciC, tyA_T, tyA_C, hkT, hciT_nm, htys_kT, hkC, hciC_nm, htys_kC,
                  hcanon_T, hann_T, hA_def_T, hcanon_C, hA_def_C⟩ :=
                  hMemInfo pos hpos_lt ind ct hmi hct
                obtain ⟨bsT, hT_sort⟩ := stripPis_sort_of_annotates ind.params.toNat hann_T hstrip₀
                obtain ⟨hread_T, hlbb_T, hdef_T⟩ := hcanonE₀.ind pos ind (by omega) hmi
                obtain ⟨_, hread_C, hlbb_C, hdef_C⟩ := hcanonE₀.ctor pos ind 0 ct (by omega) (by decide) hmi hct
                have extEl := evEl.heap_extends
                obtain ⟨bytes1, hstr1, hmpf⟩ :=
                  check_member_projs_start_spec P hB (by omega) (by omega) hmi hct hni0 hnc1 hcnl hcnp
                    hnf_pos hT_sort hnz hread_T hlbb_T hdef_T hcanon_T hA_def_T
                    hread_C hlbb_C hdef_C hcanon_C hA_def_C hbB_eq haT_eq haTM_eq hAdvTM
                    (hrc.mono extEl)
                    (Bytes.repAddressRef_heapMono₂ addrTy extEl hbB)
                    (Bytes.repAddressRef_heapMono₂ addrTy extEl haT_rep)
                    (Bytes.repAddressRef_heapMono₂ addrTy extEl haTM_rep)
                    (hrm.mono extEl)
                    (AddrMapAll.mono (fun _ _ _ _ _ x => x) extEl haset)
                    (hstr.mono extEl)
                    (fun cl hcl => hsub cl (by rw [hc, hcSeg]; simp [hcl])) evSt
                refine ⟨true, bytes1, hstr1, extEl.trans evSt.heap_extends, ?_, fun _ =>
                  ⟨ind, ct, kT, kC, ciT, ciC, tyA_T, tyA_C, hmi, hct, hkT, hciT_nm, htys_kT,
                    hkC, hciC_nm, htys_kC, hmpf⟩⟩
                intro E₂ hR₂ b₂ bp₂ r₂ h₂ h₂' cs₂ hbp₂ hb₂B hnc₂ hbd₂ ev₂
                obtain ⟨heq, _⟩ := modeled_proj_eligible_det hcanonE hR₂ hbB hbB_eq hbp₂ hb₂B
                  hncEl hbdEl hnc₂ hbd₂ evEl ev₂
                exact heq.symm
              | .other (v_hznrkjiy := v_el) (m_pvfaspdm := m_el) (cs_xojymjvr := cs_el)
                  (ev_odzbepsr := evEl) (hne_eosakxxi := hne1)
                  (he_rzfpdjgy := hrs) (he_hfzucleg := hhm) (hc_njzuocxa := hcSeg) .. =>
                subst hrs hhm
                have hsubEl : ∀ cl ∈ cs_el, cl ∈ P.calls := fun cl hcl => hsub cl (by rw [hc, hcSeg]; simp [hcl])
                have hncEl : ¬ View.HashedCollision { env := P.E } [] cs_el := (P.hgoodSub hsubEl).1
                have hbdEl : Bounded cs_el := P.hbdSub hsubEl
                refine ⟨false, bytes, hstr.mono evEl.heap_extends, evEl.heap_extends, ?_, fun h => by cases h⟩
                intro E₂ hR₂ b₂ bp₂ r₂ h₂ h₂' cs₂ hbp₂ hb₂B hnc₂ hbd₂ ev₂
                obtain ⟨heq, hbit⟩ := modeled_proj_eligible_det hcanonE hR₂ hbB hbB_eq hbp₂ hb₂B
                  hncEl hbdEl hnc₂ hbd₂ evEl ev₂
                rcases hbit with h0 | h1
                · exact heq.symm.trans h0
                · exact absurd h1 hne1
            obtain ⟨b0, bytes1, hstr1, extSeg, hdet0, hmem0⟩ := hstep
            have hpos1_eq : v_pos1 = .field ((pos + 1 : Nat) : F) := by
              rw [evalBinOp_add_field_p opPos1]; push_cast; rfl
            rw [hpos1_eq] at evRec
            obtain ⟨eligRest, hdetRest, hmemRest⟩ :=
              ih (pos + 1) (by omega) (by simpa using hmLen) (by simpa using htLen) (by simpa using htmLen)
                (fun j hj => by simpa [Nat.add_assoc, Nat.add_comm 1 j] using htAs (j + 1) (by omega))
                (fun j hj => by simpa [Nat.add_assoc, Nat.add_comm 1 j] using htMs (j + 1) (by omega))
                (fun j hj => by simpa using htAdv (j + 1) (by omega))
                (hrc.mono extSeg)
                (Bytes.repAddressRef_heapMono₂ addrTy extSeg hbB)
                (RepLinkedList.mono (fun _ _ _ _ _ _ => trivial) extSeg hmrestRep)
                (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) extSeg htrestRep)
                (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) extSeg htmrestRep)
                (hrm.mono extSeg)
                (AddrMapAll.mono (fun _ _ _ _ _ x => x) extSeg haset)
                hstr1
                (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) evRec
            let elig : Nat → Bool := fun p => if p = pos then b0 else eligRest p
            refine ⟨elig, fun p hp1 hp2 => ?_, fun p hp1 hp2 he => ?_⟩
            · rcases Nat.eq_or_lt_of_le hp1 with rfl | hgt
              · simp only [elig, ↓reduceIte]; exact hdet0
              · simp only [elig, show p ≠ pos by omega, ↓reduceIte]; exact hdetRest p hgt hp2
            · rcases Nat.eq_or_lt_of_le hp1 with rfl | hgt
              · simp only [elig, ↓reduceIte] at he; exact hmem0 he
              · simp only [elig, show p ≠ pos by omega, ↓reduceIte] at he; exact hmemRest p hgt hp2 he

/-- **Top-level inversion of `KernelModeled::check_projs` inside `KernelModeled::check_family`**:
returns `BlockProjFacts` for the entire modeled inductive block. -/
theorem check_projs_facts (P : ProjsCtx.{u})
    {ms : Array Ixon.MutConst} {g : KKey → KKey}
    {indTy₀ : Nat → KExpr} {ctorTy₀ : Nat → Nat → KExpr}
    {blk : List (ConstantInfo .anon)} {tys : List KExpr}
    (hB : FamBlockRecord P.E₀ P.B P.cb ms)
    (hcanonE₀ : BlockCanonReadings P.t P.E₀ P.B P.cb ms indTy₀ ctorTy₀)
    (hms_u64 : ms.size < UInt64.size) (hms_56 : ms.size < 72057594037927936)
    {bB : Bytes.Address} {tAs tMs : List Bytes.Address}
    {x_rc x_block x_members x_tys x_tyM x_src x_dst x_aset x_np x_bnl x_s r : SourceValue F}
    {bytes : List UInt8} {h h' : Heap F} {cs : List (Call F)}
    (hbB_eq : ixAddr bB = P.B)
    (htLen : tAs.length = ms.size) (htmLen : tMs.length = ms.size)
    (htAs : ∀ j (hj : j < ms.size), ixAddr (tAs[j]'(by omega)) = Core.iprjAddr P.B j)
    (htMs : ∀ j (hj : j < ms.size), Core.keyOf P.t (ixAddr (tMs[j]'(by omega))) =
      g (Core.keyOf P.t (Core.iprjAddr P.B j)))
    (htAdv : ∀ j (hj : j < ms.size), AdvChecked P.calls P.bAddr P.t P.lim P.csFam P.advAs (tMs[j]'(by omega)))
    (hMemInfo : ∀ pos (hpos : pos < ms.size) (ind : Ixon.Inductive) (ct : Ixon.Constructor),
      ms[pos]? = some (.indc ind) → ind.ctors[0]? = some ct →
      ∃ (kT kC : Nat) (ciT ciC : ConstantInfo .anon) (tyA_T tyA_C : KExpr),
        (Decl.FamilyAlias.nonrecsOf blk)[kT]? = some ciT ∧
        ciT.name = Core.keyOf P.t (Core.iprjAddr P.B pos) ∧
        tys[kT]? = some tyA_T ∧
        (Decl.FamilyAlias.nonrecsOf blk)[kC]? = some ciC ∧
        ciC.name = Core.keyOf P.t (Core.cprjAddr P.B pos 0) ∧
        tys[kC]? = some tyA_C ∧
        LoadedReads.canonAnn P.cb (List.range ind.lvls.toNat)
          ((L1.mutsRootOffset ms.toList pos : Nat) : F) ind.typ (indTy₀ pos) = some tyA_T ∧
        Annotates tyA_T (indTy₀ pos) ∧
        tyA_T.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧
        LoadedReads.canonAnn P.cb (List.range ct.lvls.toNat)
          (((L1.mutsRootOffset ms.toList pos : Nat) : F) + 1 + ((0 : Nat) : F)) ct.typ (ctorTy₀ pos 0) =
          some tyA_C ∧
        tyA_C.allLevelParamsDefined (List.range ct.lvls.toNat) = true)
    (hrc : Claim.RCLimRep P.t P.bAddr P.lim h x_rc)
    (hbB : Bytes.RepAddressRef addrTy h bB x_block)
    (hmRep : RepList Obs.Names.«Lists::Node<Ixon::MutConst>» (fun _ _ _ => True) h ms.toList x_members)
    (htRep : RepList addrListEnum (Bytes.RepAddressRef addrTy) h tAs x_tys)
    (htmRep : RepList addrListEnum (Bytes.RepAddressRef addrTy) h tMs x_tyM)
    (hrm : Decl.RenameMap (Core.keyOf P.t) (Core.keyOf P.t) g h x_src x_dst)
    (haset : AddrMapAll addrMapEnum (fun _ k _ =>
      AdvChecked P.calls P.bAddr P.t P.lim P.csFam P.advAs k) h x_aset)
    (hstr : L1.Stream h bytes x_s)
    (hsub : ∀ cl ∈ cs, cl ∈ P.calls)
    (ev : ObsFn Obs.W "KernelModeled::check_projs"
      [x_rc, x_block, x_members, .field 0, x_tys, x_tyM, x_src, x_dst, x_aset, x_np, x_bnl, x_s]
      h r h' cs) :
    Nonempty (BlockProjFacts P.t P.E₀ P.E P.env P.B P.cb ms blk tys g) := by
  obtain ⟨elig, hdet, hatPos⟩ :=
    check_projs_loop P hB hcanonE₀ hms_u64 hms_56 hbB_eq hMemInfo
      ms.size 0 (Nat.zero_add _) (by simp) htLen htmLen
      (fun j hj => by simpa using htAs j hj)
      (fun j hj => by simpa using htMs j hj)
      htAdv hrc hbB hmRep htRep htmRep hrm haset hstr hsub (by simpa using ev)
  exact ⟨{
    hms_size := hms_u64
    elig := elig
    indTy₀ := indTy₀
    ctorTy₀ := ctorTy₀
    canonE₀ := hcanonE₀
    eligDet := fun {_} hR₂ {_ _ _ pos} hp {_ _ _} hbp₂ hb₂B hnc₂ hbd₂ ev₂ =>
      hdet pos (Nat.zero_le pos) hp hR₂ hbp₂ hb₂B hnc₂ hbd₂ ev₂
    atPos := fun pos hp he => hatPos pos (Nat.zero_le _) hp he }⟩

end IxVM.Refinement.Typing.FamilyAlias
