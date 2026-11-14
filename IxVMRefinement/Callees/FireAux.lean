import IxVMRefinement.Core.Registry
import IxVMRefinement.Core.Open
import IxVMRefinement.Core.Window
import IxVMRefinement.Levels.Spec
import IxVMRefinement.Callees.Modeled
import IxC.Kernel.Verify.InstLevels
import IxC.Kernel.Verify.InstList

/-! # Pure and representation helpers for `fire_compare` and `fire_ok`

Supporting algebra for `KernelModeled::fire_compare`:
* loaded-constant inversions (`ciRep_rec_inv`, `ciRep_induct_inv`, `env_find?_name`);
* `Lists::*<&KernelTypes::KExprNode>` wrappers (`kexpr_length`, `kexpr_drop`, `kexpr_take`,
  `kexpr_reverse`);
* positional universe-parameter renaming (`posOf`) vs `instantiateLevelParams` and `substLevelList`;
* lifting `stripPis`, `piDomAt`, `getAppFn`, and `bvar` spine arguments across `posOf`;
* `openZero` / `closeZero` bridge between `Tm 0 Γ₀ (k + d)` and `Tm d Γ₀ k`, connecting
  `KernelSubst::expr_lower` to `Expr.lowerBVars` and `Ix.Kernel.Tier.nestedPins`. -/

namespace IxVM.Refinement.Core.FireAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Field casts and environment lookups -/

theorem val_natCast_lt59 {a : Nat} (ha : a < 2 ^ 59) : ZMod.val (a : F) = a :=
  ZMod.val_natCast_of_lt (Nat.lt_trans ha (by decide))

theorem natCast_inj_lt59 {a b : Nat} (ha : a < 2 ^ 59) (hb : b < 2 ^ 59)
    (h : (a : F) = (b : F)) : a = b := by
  have hv := congrArg ZMod.val h
  rwa [val_natCast_lt59 ha, val_natCast_lt59 hb] at hv

theorem env_find?_name {env : Ix.Kernel.Env .anon} {k : KKey}
    {ci : Ix.Kernel.ConstantInfo .anon} (h : env.find? k = some ci) : ci.name = k := by
  unfold Ix.Kernel.Env.find? at h
  exact eq_of_beq (List.find?_some h)

theorem ciRep_rec_inv {κ : _root_.Address → KKey} {h : Heap F}
    {nl ty np ni nm nmi rules k u blk idx : SourceValue F}
    {cv : Ix.Kernel.ConstantVal .anon} {mI rP : Nat} {rls : List (Ix.Kernel.RecRule .anon)}
    (hci : CIRep κ h (.construct kciEnum "Rec" [nl, ty, np, ni, nm, nmi, rules, k, u, blk, idx])
      (.recInfo cv mI rP rls)) :
    ∃ p i m mi : F, ValRep κ h nl ty cv ∧
      np = .field p ∧ ni = .field i ∧ nm = .field m ∧ nmi = .field mi ∧
      (rP : F) = p + m + mi ∧ (mI : F) = p + m + mi + i ∧
      rP ≤ mI ∧ mI < 288230376151711744 := by
  cases hci with
  | recr hv hnp hni hnm hnmi hrP hmI hcounts _ _ _ =>
    exact ⟨_, _, _, _, hv, hnp, hni, hnm, hnmi, hrP, hmI, hcounts.1, hcounts.2⟩

theorem ciRep_induct_inv {κ : _root_.Address → KKey} {h : Heap F}
    {nl ty np ni nc u blk idx : SourceValue F} {ci : Ix.Kernel.ConstantInfo .anon}
    (hci : CIRep κ h (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]) ci) :
    ∃ (cv : Ix.Kernel.ConstantVal .anon) (caps : Ix.Kernel.IndCaps .anon)
      (nP nI nC : Nat) (b : Bytes.Address) (i_idx : F),
      ci = .indInfo cv caps ∧
      np = .field (nP : F) ∧ ni = .field (nI : F) ∧ nc = .field (nC : F) ∧
      nP < 72057594037927936 ∧ nI < 72057594037927936 ∧ nC < 72057594037927936 ∧
      Bytes.RepAddressRef addrTy h b blk ∧ idx = .field i_idx ∧
      cv.name = κ (iprjAddr (ixAddr b) (ZMod.val i_idx)) := by
  cases hci with
  | induct _ hcounts hkey =>
    obtain ⟨nP, nI, nC, hnp, hni, hnc, hbP, hbI, hbC⟩ := hcounts
    obtain ⟨b, i_idx, hb, hidx, hname⟩ := hkey
    exact ⟨_, _, nP, nI, nC, b, i_idx, rfl, hnp, hni, hnc, hbP, hbI, hbC, hb, hidx, hname⟩

/-! ## `Lists::*<&KernelTypes::KExprNode>` wrappers -/

theorem kexpr_length {R : Heap F → KExpr → SourceValue F → Prop} {xs : List KExpr}
    {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [l] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) :
    r = .field (xs.length : F) ∧ h' = h := by
  exact Lib.Lists.length_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) (R := R)
    (by rw [Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)

theorem kexpr_drop {R : Heap F → KExpr → SourceValue F → Prop} {xs : List KExpr}
    {l r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [l, .field n] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) :
    ZMod.val n ≤ xs.length ∧
      RepList kexprListEnum R h (xs.drop (ZMod.val n)) r ∧ h' = h := by
  have := Lib.Lists.drop_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) (R := R) _ rfl
    (by rw [Obs.Names.«Lists::drop<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)
  rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at this
  exact this

theorem kexpr_take {R : Heap F → KExpr → SourceValue F → Prop} (hR : HeapMono₂ R)
    {xs : List KExpr} {l r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::take<&KernelTypes::KExprNode>» [l, .field n] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) :
    ZMod.val n ≤ xs.length ∧ RepList kexprListEnum R h' (xs.take (ZMod.val n)) r := by
  have := Lib.Lists.take_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) hR
    (by rw [Obs.Names.«Lists::take<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)
  rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at this
  exact this

theorem kexpr_reverse {R : Heap F → KExpr → SourceValue F → Prop} (hR : HeapMono₂ R)
    {xs : List KExpr} {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::reverse<&KernelTypes::KExprNode>» [l] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) :
    RepList kexprListEnum R h' xs.reverse r := by
  have := Lib.Lists.reverse_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) hR
    (by rw [Obs.Names.«Lists::reverse<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)
  rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at this
  exact this

/-! ## Level instantiation across `posOf` -/

theorem subst_go_range_shift :
    ∀ (k : Nat) (vs : List KLevel) (i : Nat),
      Ix.Kernel.Level.subst.go ((List.range vs.length).map (· + k)) vs i =
        if h : k ≤ i ∧ i - k < vs.length then vs[i - k]'(h.2) else .param i := by
  intro k vs i
  induction vs generalizing k with
  | nil =>
    simp [Ix.Kernel.Level.subst.go]
  | cons v vs ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    have hfn : ((· + k) ∘ Nat.succ) = (· + (k + 1)) := by
      funext x; simp [Function.comp]; omega
    rw [hfn, Nat.zero_add]
    simp only [Ix.Kernel.Level.subst.go]
    by_cases hki : k = i
    · subst hki
      simp
    · simp only [hki, ↓reduceIte, ih (k + 1)]
      by_cases h1 : k + 1 ≤ i ∧ i - (k + 1) < vs.length
      · have h0 : k ≤ i ∧ i - k < (v :: vs).length := by simp; omega
        have hidx : i - k = (i - (k + 1)) + 1 := by omega
        rw [dif_pos h1, dif_pos h0]
        simp [hidx]
      · have h0 : ¬(k ≤ i ∧ i - k < (v :: vs).length) := by simp; omega
        rw [dif_neg h1, dif_neg h0]

theorem subst_go_range (vs : List KLevel) (i : Nat) :
    Ix.Kernel.Level.subst.go (List.range vs.length) vs i =
      if h : i < vs.length then vs[i]'h else .param i := by
  have h0 := subst_go_range_shift 0 vs i
  simpa using h0

theorem subst_go_posLevels_aux {us : List KLevel} :
    ∀ (k : Nat) (qs : List Ix.Kernel.LevelParam) (vs : List KLevel)
      (n : Ix.Kernel.LevelParam),
      vs.length = qs.length →
      (∀ j (hj : j < vs.length),
        Ix.Kernel.Level.subst.go (List.range us.length) us (j + k) = vs[j]'hj) →
      (n ∉ qs → Ix.Kernel.Level.subst.go (List.range us.length) us n = .param n) →
      Ix.Kernel.Level.subst (List.range us.length) us
        (Ix.Kernel.Level.subst.go qs ((List.range qs.length).map (fun j => .param (j + k))) n) =
        Ix.Kernel.Level.subst.go qs vs n := by
  intro k qs
  induction qs generalizing k with
  | nil =>
    intro vs n hlen _ hnot
    cases vs with
    | nil =>
      simp only [Ix.Kernel.Level.subst.go, Ix.Kernel.Level.subst]
      exact hnot (by simp)
    | cons _ _ => simp at hlen
  | cons q qs ih =>
    intro vs n hlen hget hnot
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      have hfn : ((fun j => Ix.Kernel.Level.param (j + k)) ∘ Nat.succ) =
          (fun j => Ix.Kernel.Level.param (j + (k + 1))) := by
        funext x; simp [Function.comp]; omega
      rw [hfn, Nat.zero_add]
      simp only [Ix.Kernel.Level.subst.go]
      by_cases hqn : q = n
      · simp only [hqn, ↓reduceIte, Ix.Kernel.Level.subst]
        simpa using hget 0 (by simp)
      · simp only [hqn, ↓reduceIte]
        refine ih (k + 1) vs n (by simpa using hlen) ?_ ?_
        · intro j hj
          have hj' : j + 1 < (v :: vs).length := by simp; omega
          have heq : j + (k + 1) = (j + 1) + k := by omega
          rw [heq, hget (j + 1) hj']
          rfl
        · intro hn_qs
          exact hnot (fun hm => by
            rcases List.mem_cons.mp hm with rfl | h
            · exact hqn rfl
            · exact hn_qs h)

theorem subst_go_posLevels_perm {ps : List Ix.Kernel.LevelParam} {us : List KLevel}
    (hperm : ps.Perm (List.range ps.length)) (hlen : us.length = ps.length)
    (n : Ix.Kernel.LevelParam) :
    Ix.Kernel.Level.subst (List.range us.length) us
      (Ix.Kernel.Level.subst.go ps (posLevels ps) n) =
      Ix.Kernel.Level.subst.go ps us n := by
  have hpos : posLevels ps = (List.range ps.length).map (fun j => .param (j + 0)) := by
    simp [posLevels]
  rw [hpos]
  refine subst_go_posLevels_aux 0 ps us n hlen ?_ ?_
  · intro j hj
    rw [Nat.add_zero, subst_go_range, dif_pos hj]
  · intro hn
    have hnr : n ∉ List.range ps.length := fun hr => hn (hperm.mem_iff.mpr hr)
    have hge : ¬(n < us.length) := by
      rw [hlen]
      simpa [List.mem_range] using hnr
    rw [subst_go_range, dif_neg hge]

theorem subst_posLevels_perm {ps : List Ix.Kernel.LevelParam} {us : List KLevel}
    (hperm : ps.Perm (List.range ps.length)) (hlen : us.length = ps.length) :
    ∀ u : KLevel,
      Ix.Kernel.Level.subst (List.range us.length) us
        (Ix.Kernel.Level.subst ps (posLevels ps) u) =
        Ix.Kernel.Level.subst ps us u := by
  intro u
  induction u with
  | zero => rfl
  | succ u ih => simp [Ix.Kernel.Level.subst, ih]
  | max a b iha ihb => simp [Ix.Kernel.Level.subst, iha, ihb]
  | imax a b iha ihb => simp [Ix.Kernel.Level.subst, iha, ihb]
  | param n => exact subst_go_posLevels_perm hperm hlen n

theorem substPW_posLevels_perm {ps : List Ix.Kernel.LevelParam} {us : List KLevel}
    (hperm : ps.Perm (List.range ps.length)) (hlen : us.length = ps.length)
    (pw : Ix.Kernel.PropWhen) :
    Ix.Kernel.Level.substPW (List.range us.length) us
      (Ix.Kernel.Level.substPW ps (posLevels ps) pw) =
      Ix.Kernel.Level.substPW ps us pw := by
  apply Ix.Kernel.PropWhen.eq_of_holds
  intro φ
  rw [Ix.Kernel.Level.holds_substPW, Ix.Kernel.Level.holds_substPW, Ix.Kernel.Level.holds_substPW]
  have hfn : Ix.Kernel.Level.substFn (Ix.Kernel.Level.substFn φ (List.range us.length) us)
      ps (posLevels ps) = Ix.Kernel.Level.substFn φ ps us := by
    funext m
    rw [← Ix.Kernel.Level.eval_subst_go, ← Ix.Kernel.Level.eval_subst,
        subst_go_posLevels_perm hperm hlen m, Ix.Kernel.Level.eval_subst_go]
  rw [hfn]

theorem posOf_instantiateLevelParams_perm {ps : List Ix.Kernel.LevelParam} {us : List KLevel}
    (hperm : ps.Perm (List.range ps.length)) (hlen : us.length = ps.length) :
    ∀ e : KExpr,
      (posOf ps e).instantiateLevelParams (List.range us.length) us =
        e.instantiateLevelParams ps us := by
  intro e
  unfold posOf
  induction e with
  | bvar _ => rfl
  | fvar idx ty ih => simp [Ix.Kernel.Expr.instantiateLevelParams, ih]
  | sort u => simp [Ix.Kernel.Expr.instantiateLevelParams, subst_posLevels_perm hperm hlen]
  | const n ls =>
    simp [Ix.Kernel.Expr.instantiateLevelParams, List.map_map, Function.comp,
      subst_posLevels_perm hperm hlen]
  | app f a ihf iha => simp [Ix.Kernel.Expr.instantiateLevelParams, ihf, iha]
  | lam ty body m iht ihb =>
    simp [Ix.Kernel.Expr.instantiateLevelParams, iht, ihb, substPW_posLevels_perm hperm hlen]
  | forallE ty body m iht ihb =>
    simp [Ix.Kernel.Expr.instantiateLevelParams, iht, ihb, substPW_posLevels_perm hperm hlen]
  | letE ty val body m iht ihv ihb =>
    simp [Ix.Kernel.Expr.instantiateLevelParams, iht, ihv, ihb]
  | lit _ => rfl
  | proj s i e ih => simp [Ix.Kernel.Expr.instantiateLevelParams, ih]

theorem evalEqList_trans {φ : Ix.Kernel.LevelParam → Nat} :
    ∀ {xs ys zs : List KLevel},
      Ix.Kernel.Level.EvalEqList φ xs ys →
      Ix.Kernel.Level.EvalEqList φ ys zs →
      Ix.Kernel.Level.EvalEqList φ xs zs
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h1, hr1⟩, ⟨h2, hr2⟩ =>
    ⟨h1.trans h2, evalEqList_trans hr1 hr2⟩
  | [], _ :: _, _, h, _ => nomatch h
  | _ :: _, [], _, h, _ => nomatch h
  | _, [], _ :: _, _, h => nomatch h
  | _, _ :: _, [], _, h => nomatch h

theorem substFn_congr_evalEqList (φ : Ix.Kernel.LevelParam → Nat) :
    ∀ (ks : List Ix.Kernel.LevelParam) {us vs : List KLevel},
      Ix.Kernel.Level.EvalEqList φ us vs →
      Ix.Kernel.Level.substFn φ ks us = Ix.Kernel.Level.substFn φ ks vs
  | [], _, _, _ => rfl
  | _ :: _, [], [], _ => rfl
  | k :: ks, u :: us, v :: vs, ⟨huv, hrest⟩ => by
    funext n
    simp only [Ix.Kernel.Level.substFn]
    by_cases hkn : k = n
    · simp [hkn, huv]
    · simp [hkn, substFn_congr_evalEqList φ ks hrest]
  | _ :: _, [], _ :: _, h => nomatch h
  | _ :: _, _ :: _, [], h => nomatch h

theorem evalEqList_substLevelList (φ : Ix.Kernel.LevelParam → Nat)
    {ps : List Ix.Kernel.LevelParam} {usK ls_us : List KLevel}
    (hperm : ps.Perm (List.range ps.length)) (hlen : usK.length = ps.length)
    (h_us : LvEqList usK ls_us) :
    ∀ {lvls ls_ilvls : List KLevel},
      LvEqList (lvls.map (Ix.Kernel.Level.subst ps (posLevels ps))) ls_ilvls →
      Ix.Kernel.Level.EvalEqList φ (KernelLevels.substLevelList ls_ilvls ls_us)
        (lvls.map (Ix.Kernel.Level.subst ps usK))
  | [], [], _ => trivial
  | v :: lvls, l :: ls_ilvls, h_il => by
    have hlen_ls : ls_us.length = usK.length := (h_us φ).length_eq.symm
    have hhead : Ix.Kernel.Level.eval φ (KernelLevels.substLevel l ls_us) =
        Ix.Kernel.Level.eval φ (Ix.Kernel.Level.subst ps usK v) := by
      rw [KernelLevels.eval_substLevel_eq_subst, Ix.Kernel.Level.eval_subst]
      have hl_eq : ∀ ψ, Ix.Kernel.Level.eval ψ (Ix.Kernel.Level.subst ps (posLevels ps) v) =
          Ix.Kernel.Level.eval ψ l := fun ψ => (h_il ψ).1
      rw [← hl_eq, hlen_ls,
        ← substFn_congr_evalEqList φ (List.range usK.length) (h_us φ),
        ← Ix.Kernel.Level.eval_subst, subst_posLevels_perm hperm hlen v]
    exact ⟨hhead, evalEqList_substLevelList φ hperm hlen h_us (fun ψ => (h_il ψ).2)⟩
  | [], _ :: _, h => nomatch (h φ)
  | _ :: _, [], h => nomatch (h φ)

theorem lvEqList_subst_chain {ps : List Ix.Kernel.LevelParam}
    {usj ls_usj lvls ls_ilvls usK ls_us : List KLevel}
    (hperm : ps.Perm (List.range ps.length)) (hlen : usK.length = ps.length)
    (h_usj : LvEqList usj ls_usj)
    (h_eq : LvEqList ls_usj (KernelLevels.substLevelList ls_ilvls ls_us))
    (h_il : LvEqList (lvls.map (Ix.Kernel.Level.subst ps (posLevels ps))) ls_ilvls)
    (h_us : LvEqList usK ls_us) :
    LvEqList usj (lvls.map (Ix.Kernel.Level.subst ps usK)) :=
  fun φ => evalEqList_trans (h_usj φ)
    (evalEqList_trans (h_eq φ) (evalEqList_substLevelList φ hperm hlen h_us h_il))

/-! ## Structural lifting across `posOf` -/

theorem stripPis_of_posOf {ps : List Ix.Kernel.LevelParam} :
    ∀ (n : Nat) {e : KExpr} {bsPos : List (KExpr × Ix.Kernel.BinderMeta)} {BPos : KExpr},
      (posOf ps e).stripPis n = some (bsPos, BPos) →
      ∃ bs B, e.stripPis n = some (bs, B) ∧ BPos = posOf ps B
  | 0, e, bsPos, BPos, h => by
    simp only [Ix.Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨[], e, rfl, h.2.symm⟩
  | n + 1, e, bsPos, BPos, h => by
    cases e with
    | forallE dom body bm =>
      simp only [posOf, Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.stripPis,
        Option.map_eq_some_iff] at h
      rcases h with ⟨⟨bs', B'⟩, hstrip, -, rfl⟩
      obtain ⟨bs, B, hs, rfl⟩ := stripPis_of_posOf n hstrip
      exact ⟨(dom, bm) :: bs, B, by simp [Ix.Kernel.Expr.stripPis, hs], rfl⟩
    | _ => simp [posOf, Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.stripPis] at h

theorem forallE_of_posOf {ps : List Ix.Kernel.LevelParam} {B domPos bodyPos : KExpr}
    {bmPos : Ix.Kernel.BinderMeta}
    (h : posOf ps B = .forallE domPos bodyPos bmPos) :
    ∃ dom body bm, B = .forallE dom body bm ∧ domPos = posOf ps dom ∧
      bodyPos = posOf ps body := by
  cases B with
  | forallE dom body bm =>
    simp only [posOf, Ix.Kernel.Expr.instantiateLevelParams,
      Ix.Kernel.Expr.forallE.injEq] at h
    exact ⟨dom, body, bm, rfl, h.1.symm, h.2.1.symm⟩
  | _ => simp [posOf, Ix.Kernel.Expr.instantiateLevelParams] at h

theorem piDomAt_of_posOf {ps : List Ix.Kernel.LevelParam} :
    ∀ (n : Nat) {e domPos : KExpr},
      piDomAt n (posOf ps e) = some domPos →
      ∃ dom, piDomAt n e = some dom ∧ domPos = posOf ps dom
  | 0, e, domPos, h => by
    cases e with
    | forallE dom body bm =>
      simp only [posOf, Ix.Kernel.Expr.instantiateLevelParams, piDomAt,
        Option.some.injEq] at h
      exact ⟨dom, rfl, h.symm⟩
    | _ => simp [posOf, Ix.Kernel.Expr.instantiateLevelParams, piDomAt] at h
  | n + 1, e, domPos, h => by
    cases e with
    | forallE dom body bm =>
      simp only [posOf, Ix.Kernel.Expr.instantiateLevelParams, piDomAt] at h
      exact piDomAt_of_posOf n h
    | _ => simp [posOf, Ix.Kernel.Expr.instantiateLevelParams, piDomAt] at h

theorem const_of_posOf {ps : List Ix.Kernel.LevelParam} {fn : KExpr} {key : KKey}
    {lsPos : List KLevel} (h : posOf ps fn = .const key lsPos) :
    ∃ lvls, fn = .const key lvls ∧
      lsPos = lvls.map (Ix.Kernel.Level.subst ps (posLevels ps)) := by
  cases fn with
  | const k lvls =>
    simp only [posOf, Ix.Kernel.Expr.instantiateLevelParams,
      Ix.Kernel.Expr.const.injEq] at h
    exact ⟨lvls, by rw [h.1], h.2.symm⟩
  | _ => simp [posOf, Ix.Kernel.Expr.instantiateLevelParams] at h

theorem bvar_of_posOf {ps : List Ix.Kernel.LevelParam} {e : KExpr} {j : Nat}
    (h : posOf ps e = .bvar j) : e = .bvar j := by
  cases e <;> simp [posOf, Ix.Kernel.Expr.instantiateLevelParams] at h
  exact congrArg Ix.Kernel.Expr.bvar h

theorem map_posOf_bvar_inv {ps : List Ix.Kernel.LevelParam} :
    ∀ {xs : List KExpr} {js : List Nat},
      xs.map (posOf ps) = js.map Ix.Kernel.Expr.bvar →
      xs = js.map Ix.Kernel.Expr.bvar
  | [], [], _ => rfl
  | x :: xs, j :: js, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [bvar_of_posOf h.1, map_posOf_bvar_inv h.2]
    rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-! ## `openZero` / `closeZero` bridge and `lowerBVars` -/

def Γ₀ : Nat → KExpr := fun _ => .sort .zero

theorem ghostScoped_Γ₀ {d : Nat} : GhostScoped Γ₀ d :=
  fun _ _ => by simp [Γ₀, Ix.Kernel.Expr.wscopedB]

theorem hasFvar_liftLooseBVars {n : Nat} :
    ∀ {e : KExpr} {c : Nat}, e.hasFvar = false → (e.liftLooseBVars n c).hasFvar = false := by
  intro e
  induction e with
  | bvar i => intro c _; simp only [Ix.Kernel.Expr.liftLooseBVars]; split <;> rfl
  | fvar _ _ => intro _ h; simp [Ix.Kernel.Expr.hasFvar] at h
  | app f a ihf iha =>
    intro c h
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.liftLooseBVars, Ix.Kernel.Expr.hasFvar, ihf h.1, iha h.2]
  | lam ty body _ iht ihb =>
    intro c h
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.liftLooseBVars, Ix.Kernel.Expr.hasFvar, iht h.1, ihb h.2]
  | forallE ty body _ iht ihb =>
    intro c h
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.liftLooseBVars, Ix.Kernel.Expr.hasFvar, iht h.1, ihb h.2]
  | letE ty val body _ iht ihv ihb =>
    intro c h
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.liftLooseBVars, Ix.Kernel.Expr.hasFvar, iht h.1.1, ihv h.1.2, ihb h.2]
  | proj _ _ e ih =>
    intro c h; simpa [Ix.Kernel.Expr.liftLooseBVars, Ix.Kernel.Expr.hasFvar] using ih h
  | _ => intro _ _; rfl

theorem hasFvar_instantiate1Lift {v : KExpr} (hv : v.hasFvar = false) :
    ∀ {e : KExpr} {j : Nat}, e.hasFvar = false → (e.instantiate1Lift v j).hasFvar = false := by
  intro e
  induction e with
  | bvar i =>
    intro j _
    simp only [Ix.Kernel.Expr.instantiate1Lift]
    split
    · exact hasFvar_liftLooseBVars hv
    · split <;> rfl
  | fvar _ _ => intro _ h; simp [Ix.Kernel.Expr.hasFvar] at h
  | app f a ihf iha =>
    intro j h
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.instantiate1Lift, Ix.Kernel.Expr.hasFvar, ihf h.1, iha h.2]
  | lam ty body _ iht ihb =>
    intro j h
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.instantiate1Lift, Ix.Kernel.Expr.hasFvar, iht h.1, ihb h.2]
  | forallE ty body _ iht ihb =>
    intro j h
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.instantiate1Lift, Ix.Kernel.Expr.hasFvar, iht h.1, ihb h.2]
  | letE ty val body _ iht ihv ihb =>
    intro j h
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.instantiate1Lift, Ix.Kernel.Expr.hasFvar, iht h.1.1, ihv h.1.2, ihb h.2]
  | proj _ _ e ih =>
    intro j h; simpa [Ix.Kernel.Expr.instantiate1Lift, Ix.Kernel.Expr.hasFvar] using ih h
  | _ => intro _ _; rfl

theorem hasFvar_of_tm_zero {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F} (rep : Tm κ 0 Γ h k E p) :
    E.hasFvar = false := by
  induction rep with
  | bvarLocal => rfl
  | bvarFree _ _ _ hd => omega
  | sort => rfl
  | const => rfl
  | app _ _ _ ihf iha => simp [Ix.Kernel.Expr.hasFvar, ihf, iha]
  | lam _ _ _ _ iht ihb => simp [Ix.Kernel.Expr.hasFvar, iht, ihb]
  | forallE _ _ _ _ iht ihb => simp [Ix.Kernel.Expr.hasFvar, iht, ihb]
  | letE _ _ _ _ _ ihv ihb => exact hasFvar_instantiate1Lift ihv ihb
  | litNat => rfl
  | litStr => rfl
  | proj _ _ _ ihe => simpa [Ix.Kernel.Expr.hasFvar] using ihe

theorem wscopedB_instantiateLevelParams (ks : List Ix.Kernel.LevelParam) (us : List KLevel) :
    ∀ (e : KExpr) (d : Nat),
      (e.instantiateLevelParams ks us).wscopedB d = e.wscopedB d := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ =>
    intro d; simp [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.wscopedB]
  | fvar idx ty ih =>
    intro d
    rw [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.wscopedB, Ix.Kernel.Expr.wscopedB,
      ih idx]
  | app f a ihf iha =>
    intro d
    rw [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.wscopedB, Ix.Kernel.Expr.wscopedB,
      ihf d, iha d]
  | lam ty body m iht ihb =>
    intro d
    rw [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.wscopedB, Ix.Kernel.Expr.wscopedB,
      iht d, ihb d]
  | forallE ty body m iht ihb =>
    intro d
    rw [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.wscopedB, Ix.Kernel.Expr.wscopedB,
      iht d, ihb d]
  | letE ty val body m iht ihv ihb =>
    intro d
    rw [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.wscopedB, Ix.Kernel.Expr.wscopedB,
      iht d, ihv d, ihb d]
  | proj s i e ih =>
    intro d
    rw [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.wscopedB, Ix.Kernel.Expr.wscopedB,
      ih d]

def openZero (d : Nat) : Nat → KExpr → KExpr
  | k, .bvar i => if i < k then .bvar i else .fvar (d - 1 - (i - k)) (.sort .zero)
  | _, .fvar idx ty => .fvar idx ty
  | _, .sort u => .sort u
  | _, .const n us => .const n us
  | k, .app f a => .app (openZero d k f) (openZero d k a)
  | k, .lam ty body m => .lam (openZero d k ty) (openZero d (k + 1) body) m
  | k, .forallE ty body m => .forallE (openZero d k ty) (openZero d (k + 1) body) m
  | k, .letE ty val body m => .letE (openZero d k ty) (openZero d k val) (openZero d (k + 1) body) m
  | _, .lit l => .lit l
  | k, .proj s i e => .proj s i (openZero d k e)

theorem openZero_liftLooseBVars (d j : Nat) :
    ∀ (e : KExpr) (c k : Nat), c + j ≤ k →
      openZero d k (e.liftLooseBVars j c) = (openZero d (k - j) e).liftLooseBVars j c := by
  intro e
  induction e with
  | bvar i =>
    intro c k hck
    simp only [Ix.Kernel.Expr.liftLooseBVars, openZero]
    by_cases hic : i ≥ c
    · simp only [hic, ↓reduceIte]
      by_cases hik : i < k - j
      · have hij : i + j < k := by omega
        simp [hik, hij, Ix.Kernel.Expr.liftLooseBVars, hic]
      · have hij : ¬(i + j < k) := by omega
        have hsub : i + j - k = i - (k - j) := by omega
        simp [hik, hij, hsub, Ix.Kernel.Expr.liftLooseBVars]
    · have hik : i < k - j := by omega
      have hij : i < k := by omega
      simp [hic, hik, hij, Ix.Kernel.Expr.liftLooseBVars]
  | app f a ihf iha =>
    intro c k hck
    simp [Ix.Kernel.Expr.liftLooseBVars, openZero, ihf c k hck, iha c k hck]
  | lam ty body m iht ihb =>
    intro c k hck
    have hsub : k + 1 - j = k - j + 1 := by omega
    simp [Ix.Kernel.Expr.liftLooseBVars, openZero, iht c k hck, ihb (c + 1) (k + 1) (by omega),
      hsub]
  | forallE ty body m iht ihb =>
    intro c k hck
    have hsub : k + 1 - j = k - j + 1 := by omega
    simp [Ix.Kernel.Expr.liftLooseBVars, openZero, iht c k hck, ihb (c + 1) (k + 1) (by omega),
      hsub]
  | letE ty val body m iht ihv ihb =>
    intro c k hck
    have hsub : k + 1 - j = k - j + 1 := by omega
    simp [Ix.Kernel.Expr.liftLooseBVars, openZero, iht c k hck, ihv c k hck,
      ihb (c + 1) (k + 1) (by omega), hsub]
  | proj s i e ih =>
    intro c k hck
    simp [Ix.Kernel.Expr.liftLooseBVars, openZero, ih c k hck]
  | _ => intro c k _; simp [Ix.Kernel.Expr.liftLooseBVars, openZero]

theorem openZero_instantiate1Lift (d : Nat) (V : KExpr) :
    ∀ (B : KExpr) (j k : Nat), j ≤ k →
      openZero d k (B.instantiate1Lift V j) =
        (openZero d (k + 1) B).instantiate1Lift (openZero d (k - j) V) j := by
  intro B
  induction B with
  | bvar i =>
    intro j k hjk
    simp only [Ix.Kernel.Expr.instantiate1Lift, openZero]
    by_cases hij : i = j
    · subst hij
      have hlt : i < k + 1 := by omega
      simp [hlt, Ix.Kernel.Expr.instantiate1Lift, openZero_liftLooseBVars d i V 0 k (by omega)]
    · simp only [hij, ↓reduceIte]
      by_cases hgt : i > j
      · simp only [hgt, ↓reduceIte, openZero]
        by_cases hik : i < k + 1
        · have hik' : i - 1 < k := by omega
          simp [hik, hik', Ix.Kernel.Expr.instantiate1Lift, hij, hgt]
        · have hik' : ¬(i - 1 < k) := by omega
          have hsub : i - 1 - k = i - (k + 1) := by omega
          simp [hik, hik', hsub, Ix.Kernel.Expr.instantiate1Lift]
      · have hik : i < k + 1 := by omega
        have hik' : i < k := by omega
        simp [hgt, hik, hik', openZero, Ix.Kernel.Expr.instantiate1Lift, hij]
  | app f a ihf iha =>
    intro j k hjk
    simp [Ix.Kernel.Expr.instantiate1Lift, openZero, ihf j k hjk, iha j k hjk]
  | lam ty body m iht ihb =>
    intro j k hjk
    have hsub : k + 1 - (j + 1) = k - j := by omega
    simp [Ix.Kernel.Expr.instantiate1Lift, openZero, iht j k hjk,
      ihb (j + 1) (k + 1) (by omega), hsub]
  | forallE ty body m iht ihb =>
    intro j k hjk
    have hsub : k + 1 - (j + 1) = k - j := by omega
    simp [Ix.Kernel.Expr.instantiate1Lift, openZero, iht j k hjk,
      ihb (j + 1) (k + 1) (by omega), hsub]
  | letE ty val body m iht ihv ihb =>
    intro j k hjk
    have hsub : k + 1 - (j + 1) = k - j := by omega
    simp [Ix.Kernel.Expr.instantiate1Lift, openZero, iht j k hjk, ihv j k hjk,
      ihb (j + 1) (k + 1) (by omega), hsub]
  | proj s i e ih =>
    intro j k hjk
    simp [Ix.Kernel.Expr.instantiate1Lift, openZero, ih j k hjk]
  | _ => intro j k _; simp [Ix.Kernel.Expr.instantiate1Lift, openZero]

theorem tm_openZero {κ : _root_.Address → KKey} {h : Heap F} {d : Nat}
    {k' : Nat} {E : KExpr} {p : SourceValue F} (rep : Tm κ 0 Γ₀ h k' E p) :
    ∀ k, k' = k + d → Tm κ d Γ₀ h k (openZero d k E) p := by
  induction rep with
  | @bvarLocal k₁ addr i cell hs hi =>
    intro k hk
    subst hk
    simp only [openZero]
    by_cases hik : ZMod.val i < k
    · simp only [hik, ↓reduceIte]
      exact .bvarLocal cell hs hik
    · simp only [hik, ↓reduceIte]
      exact .bvarFree cell hs (by omega) (by omega)
  | bvarFree _ _ _ hd => omega
  | sort cell rl hu => intro k _; exact .sort cell rl hu
  | const cell ra rls hus => intro k _; exact .const cell ra rls hus
  | app cell _ _ ihf iha =>
    intro k hk; exact .app cell (ihf k hk) (iha k hk)
  | lam cell _ _ rl iht ihb =>
    intro k hk; exact .lam cell (iht k hk) (ihb (k + 1) (by omega)) rl
  | forallE cell _ _ rl iht ihb =>
    intro k hk; exact .forallE cell (iht k hk) (ihb (k + 1) (by omega)) rl
  | @letE k₁ addr tp vp bp T V B cell _ _ _ iht ihv ihb =>
    intro k hk
    have hcomm := openZero_instantiate1Lift d V B 0 k (Nat.zero_le k)
    simp only [Nat.sub_zero] at hcomm
    rw [show instShift V 0 B = B.instantiate1Lift V 0 from rfl, hcomm]
    exact .letE cell (iht k hk) (ihv k hk) (ihb (k + 1) (by omega))
  | litNat cell rl hc => intro k _; exact .litNat cell rl hc
  | litStr cell rb hs => intro k _; exact .litStr cell rb hs
  | proj cell ra _ ihe =>
    intro k hk; exact .proj cell ra (ihe k hk)

theorem openZero_posOf (ps : List Ix.Kernel.LevelParam) (d : Nat) :
    ∀ (e : KExpr) (k : Nat),
      openZero d k (posOf ps e) = posOf ps (openZero d k e) := by
  intro e
  unfold posOf
  induction e with
  | bvar i =>
    intro k
    simp only [Ix.Kernel.Expr.instantiateLevelParams, openZero]
    split <;> rfl
  | fvar idx ty _ => intro k; rfl
  | sort _ | const _ _ | lit _ => intro k; rfl
  | app f a ihf iha =>
    intro k; simp [Ix.Kernel.Expr.instantiateLevelParams, openZero, ihf k, iha k]
  | lam ty body m iht ihb =>
    intro k; simp [Ix.Kernel.Expr.instantiateLevelParams, openZero, iht k, ihb (k + 1)]
  | forallE ty body m iht ihb =>
    intro k; simp [Ix.Kernel.Expr.instantiateLevelParams, openZero, iht k, ihb (k + 1)]
  | letE ty val body m iht ihv ihb =>
    intro k; simp [Ix.Kernel.Expr.instantiateLevelParams, openZero, iht k, ihv k, ihb (k + 1)]
  | proj s i e ih =>
    intro k; simp [Ix.Kernel.Expr.instantiateLevelParams, openZero, ih k]

def closeZero (d : Nat) : Nat → KExpr → KExpr
  | k, .fvar idx _ => .bvar (k + (d - 1 - idx))
  | _, .bvar i => .bvar i
  | _, .sort u => .sort u
  | _, .const n us => .const n us
  | k, .app f a => .app (closeZero d k f) (closeZero d k a)
  | k, .lam ty body m => .lam (closeZero d k ty) (closeZero d (k + 1) body) m
  | k, .forallE ty body m => .forallE (closeZero d k ty) (closeZero d (k + 1) body) m
  | k, .letE ty val body m => .letE (closeZero d k ty) (closeZero d k val) (closeZero d (k + 1) body) m
  | _, .lit l => .lit l
  | k, .proj s i e => .proj s i (closeZero d k e)

theorem closeZero_liftLooseBVars (d j : Nat) :
    ∀ (e : KExpr) (c k : Nat), c + j ≤ k →
      closeZero d k (e.liftLooseBVars j c) = (closeZero d (k - j) e).liftLooseBVars j c := by
  intro e
  induction e with
  | bvar i =>
    intro c k _
    simp only [Ix.Kernel.Expr.liftLooseBVars, closeZero]
    split <;> rfl
  | fvar idx ty =>
    intro c k hck
    have hge : k - j + (d - 1 - idx) ≥ c := by omega
    have hadd : k - j + (d - 1 - idx) + j = k + (d - 1 - idx) := by omega
    simp [Ix.Kernel.Expr.liftLooseBVars, closeZero, hge, hadd]
  | app f a ihf iha =>
    intro c k hck
    simp [Ix.Kernel.Expr.liftLooseBVars, closeZero, ihf c k hck, iha c k hck]
  | lam ty body m iht ihb =>
    intro c k hck
    have hsub : k + 1 - j = k - j + 1 := by omega
    simp [Ix.Kernel.Expr.liftLooseBVars, closeZero, iht c k hck,
      ihb (c + 1) (k + 1) (by omega), hsub]
  | forallE ty body m iht ihb =>
    intro c k hck
    have hsub : k + 1 - j = k - j + 1 := by omega
    simp [Ix.Kernel.Expr.liftLooseBVars, closeZero, iht c k hck,
      ihb (c + 1) (k + 1) (by omega), hsub]
  | letE ty val body m iht ihv ihb =>
    intro c k hck
    have hsub : k + 1 - j = k - j + 1 := by omega
    simp [Ix.Kernel.Expr.liftLooseBVars, closeZero, iht c k hck, ihv c k hck,
      ihb (c + 1) (k + 1) (by omega), hsub]
  | proj s i e ih =>
    intro c k hck
    simp [Ix.Kernel.Expr.liftLooseBVars, closeZero, ih c k hck]
  | _ => intro c k _; simp [Ix.Kernel.Expr.liftLooseBVars, closeZero]

theorem closeZero_instantiate1Lift (d : Nat) (V : KExpr) :
    ∀ (B : KExpr) (j k : Nat), j ≤ k →
      closeZero d k (B.instantiate1Lift V j) =
        (closeZero d (k + 1) B).instantiate1Lift (closeZero d (k - j) V) j := by
  intro B
  induction B with
  | bvar i =>
    intro j k hjk
    simp only [Ix.Kernel.Expr.instantiate1Lift, closeZero]
    by_cases hij : i = j
    · subst hij
      simp [closeZero_liftLooseBVars d i V 0 k (by omega)]
    · simp only [hij, ↓reduceIte]
      split <;> rfl
  | fvar idx ty =>
    intro j k hjk
    have hne : k + 1 + (d - 1 - idx) ≠ j := by omega
    have hgt : k + 1 + (d - 1 - idx) > j := by omega
    have hsub : k + 1 + (d - 1 - idx) - 1 = k + (d - 1 - idx) := by omega
    simp [Ix.Kernel.Expr.instantiate1Lift, closeZero, hne, hgt, hsub]
  | app f a ihf iha =>
    intro j k hjk
    simp [Ix.Kernel.Expr.instantiate1Lift, closeZero, ihf j k hjk, iha j k hjk]
  | lam ty body m iht ihb =>
    intro j k hjk
    have hsub : k + 1 - (j + 1) = k - j := by omega
    simp [Ix.Kernel.Expr.instantiate1Lift, closeZero, iht j k hjk,
      ihb (j + 1) (k + 1) (by omega), hsub]
  | forallE ty body m iht ihb =>
    intro j k hjk
    have hsub : k + 1 - (j + 1) = k - j := by omega
    simp [Ix.Kernel.Expr.instantiate1Lift, closeZero, iht j k hjk,
      ihb (j + 1) (k + 1) (by omega), hsub]
  | letE ty val body m iht ihv ihb =>
    intro j k hjk
    have hsub : k + 1 - (j + 1) = k - j := by omega
    simp [Ix.Kernel.Expr.instantiate1Lift, closeZero, iht j k hjk, ihv j k hjk,
      ihb (j + 1) (k + 1) (by omega), hsub]
  | proj s i e ih =>
    intro j k hjk
    simp [Ix.Kernel.Expr.instantiate1Lift, closeZero, ih j k hjk]
  | _ => intro j k _; simp [Ix.Kernel.Expr.instantiate1Lift, closeZero]

theorem tm_closeZero {κ : _root_.Address → KKey} {h : Heap F} {d : Nat}
    {k : Nat} {E : KExpr} {p : SourceValue F} (rep : Tm κ d Γ₀ h k E p) :
    Tm κ 0 Γ₀ h (k + d) (closeZero d k E) p := by
  induction rep with
  | bvarLocal cell hs hi =>
    exact .bvarLocal cell hs (by omega)
  | @bvarFree k₁ addr i cell hs hk hd =>
    have hidx : k₁ + (d - 1 - fvIdx d k₁ (ZMod.val i)) = ZMod.val i := by
      unfold fvIdx; omega
    simp only [closeZero, hidx]
    exact .bvarLocal cell hs (by omega)
  | sort cell rl hu => exact .sort cell rl hu
  | const cell ra rls hus => exact .const cell ra rls hus
  | app cell _ _ ihf iha => exact .app cell ihf iha
  | lam cell _ _ rl iht ihb =>
    exact .lam cell iht (by rwa [show k + d + 1 = k + 1 + d by omega]) rl
  | forallE cell _ _ rl iht ihb =>
    exact .forallE cell iht (by rwa [show k + d + 1 = k + 1 + d by omega]) rl
  | @letE k₁ addr tp vp bp T V B cell _ _ _ iht ihv ihb =>
    have hcomm := closeZero_instantiate1Lift d V B 0 k₁ (Nat.zero_le k₁)
    simp only [Nat.sub_zero] at hcomm
    rw [show instShift V 0 B = B.instantiate1Lift V 0 from rfl, hcomm]
    exact .letE cell iht ihv (by rwa [show k₁ + d + 1 = k₁ + 1 + d by omega])
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | proj cell ra _ ihe => exact .proj cell ra ihe

theorem posOf_lowerBVars (ps : List Ix.Kernel.LevelParam) (amt : Nat) :
    ∀ (e : KExpr) (cut : Nat),
      posOf ps (e.lowerBVars amt cut) = (posOf ps e).lowerBVars amt cut := by
  intro e
  unfold posOf
  induction e with
  | bvar i =>
    intro cut
    simp only [Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.instantiateLevelParams]
    split <;> rfl
  | fvar idx ty ih =>
    intro cut; simp [Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.instantiateLevelParams]
  | sort _ | const _ _ | lit _ =>
    intro cut; simp [Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.instantiateLevelParams]
  | app f a ihf iha =>
    intro cut
    simp [Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.instantiateLevelParams, ihf cut, iha cut]
  | lam ty body m iht ihb =>
    intro cut
    simp [Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.instantiateLevelParams, iht cut, ihb (cut + 1)]
  | forallE ty body m iht ihb =>
    intro cut
    simp [Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.instantiateLevelParams, iht cut, ihb (cut + 1)]
  | letE ty val body m iht ihv ihb =>
    intro cut
    simp [Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.instantiateLevelParams,
      iht cut, ihv cut, ihb (cut + 1)]
  | proj s i e ih =>
    intro cut
    simp [Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.instantiateLevelParams, ih cut]

theorem lowerBVars_of_openZero_wscopedB {rP nI : Nat} :
    ∀ (e : KExpr) (k : Nat),
      e.hasFvar = false →
      e.looseBVarsBounded (k + rP + nI) = true →
      (openZero (rP + nI) k e).wscopedB rP = true →
      closeZero rP k (openZero (rP + nI) k e) = e.lowerBVars nI k ∧
      (e.lowerBVars nI k).liftLooseBVars nI k = e ∧
      (e.lowerBVars nI k).hasFvar = false ∧
      (e.lowerBVars nI k).looseBVarsBounded (k + rP) = true := by
  intro e
  induction e with
  | bvar i =>
    intro k _ hbnd hwsc
    simp only [Ix.Kernel.Expr.looseBVarsBounded, decide_eq_true_eq] at hbnd
    by_cases hik : i < k
    · have hge : ¬(i ≥ k + nI) := by omega
      have hgek : ¬(i ≥ k) := by omega
      have hlt : i < k + rP := by omega
      simp [openZero, closeZero, Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.liftLooseBVars,
        Ix.Kernel.Expr.hasFvar, Ix.Kernel.Expr.looseBVarsBounded, hik, hge, hgek, hlt]
    · simp only [openZero, hik, ↓reduceIte] at hwsc ⊢
      rw [Ix.Kernel.Expr.wscopedB] at hwsc
      simp only [Ix.Kernel.Expr.wscopedB, Bool.and_true, decide_eq_true_eq] at hwsc
      have hge : i ≥ k + nI := by omega
      have hgek : i - nI ≥ k := by omega
      have hlt : i - nI < k + rP := by omega
      have hclose : k + (rP - 1 - (rP + nI - 1 - (i - k))) = i - nI := by omega
      have hround : i - nI + nI = i := by omega
      simp [closeZero, Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.liftLooseBVars,
        Ix.Kernel.Expr.hasFvar, Ix.Kernel.Expr.looseBVarsBounded,
        hge, hgek, hlt, hclose, hround]
  | fvar _ _ =>
    intro _ hfv _ _; simp [Ix.Kernel.Expr.hasFvar] at hfv
  | sort _ | const _ _ | lit _ =>
    intro k _ _ _
    simp [openZero, closeZero, Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.liftLooseBVars,
      Ix.Kernel.Expr.hasFvar, Ix.Kernel.Expr.looseBVarsBounded]
  | app f a ihf iha =>
    intro k hfv hbnd hwsc
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at hbnd
    rw [openZero, Ix.Kernel.Expr.wscopedB] at hwsc
    simp only [Bool.and_eq_true] at hwsc
    obtain ⟨cf, lf, ff, bf⟩ := ihf k hfv.1 hbnd.1 hwsc.1
    obtain ⟨ca, la, fa, ba⟩ := iha k hfv.2 hbnd.2 hwsc.2
    simp [openZero, closeZero, Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.liftLooseBVars,
      Ix.Kernel.Expr.hasFvar, Ix.Kernel.Expr.looseBVarsBounded, cf, lf, ff, bf, ca, la, fa, ba]
  | lam ty body m iht ihb =>
    intro k hfv hbnd hwsc
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at hbnd
    rw [openZero, Ix.Kernel.Expr.wscopedB] at hwsc
    simp only [Bool.and_eq_true] at hwsc
    obtain ⟨ct, lt, ft, bt⟩ := iht k hfv.1 hbnd.1 hwsc.1
    obtain ⟨cb, lb, fb, bb⟩ := ihb (k + 1) hfv.2
      (by rwa [show k + 1 + rP + nI = k + rP + nI + 1 by omega]) hwsc.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [openZero, closeZero, Ix.Kernel.Expr.lowerBVars, ct, cb]
    · simp [Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.liftLooseBVars, lt, lb]
    · simp [Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.hasFvar, ft, fb]
    · simp only [Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨bt, by rwa [show k + rP + 1 = k + 1 + rP by omega]⟩
  | forallE ty body m iht ihb =>
    intro k hfv hbnd hwsc
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at hbnd
    rw [openZero, Ix.Kernel.Expr.wscopedB] at hwsc
    simp only [Bool.and_eq_true] at hwsc
    obtain ⟨ct, lt, ft, bt⟩ := iht k hfv.1 hbnd.1 hwsc.1
    obtain ⟨cb, lb, fb, bb⟩ := ihb (k + 1) hfv.2
      (by rwa [show k + 1 + rP + nI = k + rP + nI + 1 by omega]) hwsc.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [openZero, closeZero, Ix.Kernel.Expr.lowerBVars, ct, cb]
    · simp [Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.liftLooseBVars, lt, lb]
    · simp [Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.hasFvar, ft, fb]
    · simp only [Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨bt, by rwa [show k + rP + 1 = k + 1 + rP by omega]⟩
  | letE ty val body m iht ihv ihb =>
    intro k hfv hbnd hwsc
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at hbnd
    rw [openZero, Ix.Kernel.Expr.wscopedB] at hwsc
    simp only [Bool.and_eq_true] at hwsc
    obtain ⟨ct, lt, ft, bt⟩ := iht k hfv.1.1 hbnd.1.1 hwsc.1.1
    obtain ⟨cv, lv, fv, bv⟩ := ihv k hfv.1.2 hbnd.1.2 hwsc.1.2
    obtain ⟨cb, lb, fb, bb⟩ := ihb (k + 1) hfv.2
      (by rwa [show k + 1 + rP + nI = k + rP + nI + 1 by omega]) hwsc.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [openZero, closeZero, Ix.Kernel.Expr.lowerBVars, ct, cv, cb]
    · simp [Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.liftLooseBVars, lt, lv, lb]
    · simp [Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.hasFvar, ft, fv, fb]
    · simp only [Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨⟨bt, bv⟩, by rwa [show k + rP + 1 = k + 1 + rP by omega]⟩
  | proj s i e ih =>
    intro k hfv hbnd hwsc
    rw [openZero, Ix.Kernel.Expr.wscopedB] at hwsc
    obtain ⟨ce, le, fe, be⟩ := ih k
      (by simpa [Ix.Kernel.Expr.hasFvar] using hfv)
      (by simpa [Ix.Kernel.Expr.looseBVarsBounded] using hbnd) hwsc
    simp [openZero, closeZero, Ix.Kernel.Expr.lowerBVars, Ix.Kernel.Expr.liftLooseBVars,
      Ix.Kernel.Expr.hasFvar, Ix.Kernel.Expr.looseBVarsBounded, ce, le, fe, be]

theorem nestedPins_of_parts {tyA dom body : KExpr}
    {bs : List (KExpr × Ix.Kernel.BinderMeta)} {bm : Ix.Kernel.BinderMeta}
    {key : KKey} {lvls : List KLevel} {mI rP cnP : Nat} {pins : List KExpr}
    (hle : rP ≤ mI)
    (hstrip : tyA.stripPis mI = some (bs, .forallE dom body bm))
    (hfn : dom.getAppFn = .const key lvls)
    (hlen : dom.getAppArgs.length = cnP + (mI - rP))
    (hdrop : dom.getAppArgs.drop cnP =
      (List.range (mI - rP)).map (fun i => .bvar (mI - rP - 1 - i)))
    (hpins : pins = (dom.getAppArgs.take cnP).map (Ix.Kernel.Expr.lowerBVars (mI - rP) 0))
    (hlift : ∀ x ∈ dom.getAppArgs.take cnP,
      (x.lowerBVars (mI - rP) 0).liftLooseBVars (mI - rP) 0 = x ∧
      (x.lowerBVars (mI - rP) 0).hasFvar = false ∧
      (x.lowerBVars (mI - rP) 0).looseBVarsBounded rP = true) :
    pins.length = cnP ∧
      Ix.Kernel.Tier.nestedPins tyA mI rP pins.length = some (lvls, pins) := by
  have hplen : pins.length = cnP := by
    rw [hpins, List.length_map, List.length_take, hlen]
    omega
  refine ⟨hplen, ?_⟩
  rw [hplen]
  unfold Ix.Kernel.Tier.nestedPins
  rw [if_pos hle, hstrip, hfn]
  have htake_eq : dom.getAppArgs.take cnP =
      ((dom.getAppArgs.take cnP).map (Ix.Kernel.Expr.lowerBVars (mI - rP) 0)).map
        (Ix.Kernel.Expr.liftLooseBVars (mI - rP) 0) := by
    rw [List.map_map]
    conv => lhs; rw [← List.map_id (dom.getAppArgs.take cnP)]
    refine List.map_congr_left ?_
    intro x hx
    exact (hlift x hx).1.symm
  have hall : (((dom.getAppArgs.take cnP).map (Ix.Kernel.Expr.lowerBVars (mI - rP) 0)).all
      (fun p => !p.hasFvar && p.looseBVarsBounded rP)) = true := by
    rw [List.all_eq_true]
    intro p hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    obtain ⟨-, hfv, hbnd⟩ := hlift x hx
    simp [hfv, hbnd]
  dsimp only
  rw [← hpins] at htake_eq hall ⊢
  have hc1 : (dom.getAppArgs.length == cnP + (mI - rP)) = true := beq_iff_eq.mpr hlen
  have hc2 : (dom.getAppArgs.take cnP == pins.map (Ix.Kernel.Expr.liftLooseBVars (mI - rP) 0)) =
      true := beq_iff_eq.mpr htake_eq
  have hc3 : (dom.getAppArgs.drop cnP ==
      (List.range (mI - rP)).map (fun i => Ix.Kernel.Expr.bvar (mI - rP - 1 - i))) = true :=
    beq_iff_eq.mpr hdrop
  rw [hc1, hc2, hc3, hall]
  simp

theorem instSpine_eq_instantiateList_all {As : List KExpr} {rP : Nat} (hle : rP ≤ As.length)
    (e : KExpr) :
    e.instantiateList (As.take rP).reverse 0 =
      Ix.Kernel.Expr.instSpine (As.take rP) (rP - 1) e := by
  cases rP with
  | zero =>
    simp [Ix.Kernel.Expr.instSpine, Ix.Kernel.Expr.instantiateList_nil]
  | succ t =>
    have htlen : (As.take (t + 1)).length = t + 1 := by
      rw [List.length_take]; omega
    exact (Ix.Kernel.Expr.instSpine_eq_instantiateList (As.take (t + 1)) t e htlen).symm

end IxVM.Refinement.Core.FireAux
