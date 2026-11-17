import IxVMRefinement.Assembly.TypingRecLateKStored
import IxVMRefinement.Decl.NativeRec
import IxC.Kernel.Verify.Denote.TeleOpen
import IxC.Kernel.Model.Inductives.StructRecKit2
import IxC.Kernel.Model.Inductives.StructBits

/-! # The field sorts of a large eliminator at a propositional family, at the arm

At a large eliminator of a propositional family the circuit's `is_large_eliminator` walks the
single constructor's fields (`check_large_prop_ctor` → `check_large_walk_fields`): each field's
domain has its sort checked (`k_ensure_sort`), a field whose sort is not zero is data, and every
data field must be an index argument of the residual. This module ports the legacy walk
(`Decl/NativeRec.lean`, stated over `Core S₀`) to the scoped core:

* `scoped_large_walk_fields_go`, `scoped_large_prop_ctor_go`: the walk's specification under
  `ScopedCoreFacts` (`scoped_core_ensure_sort` for each domain; the level comparison's soundness
  `levelEqual_eq_true_sound`, no `Levels` hypothesis).
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (ConstantInfo ConstantVal Declaration Expr Level LevelParam RecRule)
open Ix.Kernel.Rules (Red DefEq Infer)
open Ix.Kernel.Semantics (FieldSortsJ)
open Ix.Kernel.Model (rulesJ)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ## The bvar checks and a count, below `2^57` (the legacy forms are stated below `2^39`) -/

theorem succ_field_ne_zero57 {m : Nat} (hm : m + 1 < 144115188075855872) :
    (.field ((m + 1 : Nat) : F) : SourceValue F) ≠ .field 0 := by
  intro h
  have h' : (.field ((m + 1 : Nat) : F) : SourceValue F) = .field ((0 : Nat) : F) := by
    simpa using h
  have := nat_eq_of_field_eq_bounded (by omega) (by decide) h'
  omega

theorem args_contain_bvar_one_spec57 {κ : _root_.Address → KKey} {d : Nat}
    {Γ : Nat → KExpr} {h : Heap F} :
    ∀ {args : List KExpr} {pargs : SourceValue F} {target : Nat} {h' : Heap F} {cs : List (Call F)},
      target < d →
      target < 144115188075855872 →
      RepList kexprListEnum (fun h E p => Tm κ d Γ h 0 E p) h args pargs →
      ObsFn W "KernelCheck::args_contain_bvar" [pargs, .field (target : F)] h (.field 1) h' cs →
      Expr.fvar (fvIdx d 0 target) (Γ (fvIdx d 0 target)) ∈ args ∧ h' = h
  | _, _, target, _, _, ht1, ht2, hrep, ev => by
    match Obs.«KernelCheck::args_contain_bvar».obs ev with
    | .Nil (he20 := he) .. =>
      exact absurd (Value.field.inj he) one_ne_zero
    | .Cons_BVar_n0 (x_a := xa) (x_rest := xrest) (x_i := xi)
        (ld12 := ld12) (ld51 := ld51) (op80 := op80) (he88 := he88) .. =>
      obtain ⟨A, rest, rfl, hA, _⟩ := RepList.cons_of_load hrep ld12
      obtain ⟨i_f, rfl, _, hbvar⟩ := hA.bvar_of_load ld51
      simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
        Except.ok.injEq, Value.field.injEq] at op80
      have hif : i_f = (target : F) := sub_eq_zero.mp op80
      have hval : ZMod.val i_f = target := by
        rw [hif]
        exact ZMod.val_natCast_of_lt (Nat.lt_trans ht2 (by decide))
      rcases hbvar with ⟨hlt0, _⟩ | ⟨_, _, rfl⟩
      · omega
      · rw [hval]
        exact ⟨List.mem_cons_self, he88⟩
    | .Cons_BVar_other (x_rest := xrest) (cs97 := cs97)
        (ld12 := ld12) (ev99 := ev99) .. =>
      obtain ⟨A, rest, rfl, _, hrest⟩ := RepList.cons_of_load hrep ld12
      obtain ⟨hmem, hh⟩ := args_contain_bvar_one_spec57 ht1 ht2 hrest ev99
      exact ⟨List.mem_cons_of_mem _ hmem, hh⟩
    | .Cons_other (x_rest := xrest) (cs124 := cs124)
        (ld12 := ld12) (ev126 := ev126) .. =>
      obtain ⟨A, rest, rfl, _, hrest⟩ := RepList.cons_of_load hrep ld12
      obtain ⟨hmem, hh⟩ := args_contain_bvar_one_spec57 ht1 ht2 hrest ev126
      exact ⟨List.mem_cons_of_mem _ hmem, hh⟩

theorem all_bvars_in_args_one_spec57 {κ : _root_.Address → KKey} {d : Nat}
    {Γ : Nat → KExpr} {args : List KExpr} :
    ∀ {targets : List Nat} {pbvars pargs : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      (∀ tgt ∈ targets, tgt < d ∧ tgt < 144115188075855872) →
      RepList byteListEnum (fun _ (n : Nat) v => v = .field (n : F)) h targets pbvars →
      RepList kexprListEnum (fun h E p => Tm κ d Γ h 0 E p) h args pargs →
      ObsFn W "KernelCheck::all_bvars_in_args" [pbvars, pargs] h (.field 1) h' cs →
      ∀ tgt ∈ targets, Expr.fvar (fvIdx d 0 tgt) (Γ (fvIdx d 0 tgt)) ∈ args
  | _, _, _, _, _, _, htgt, hbvars, hargs, ev => by
    match Obs.«KernelCheck::all_bvars_in_args».obs ev with
    | .Nil (ld12 := ld12) .. =>
      obtain rfl := RepList.nil_of_load hbvars ld12
      intro _ hm; exact nomatch hm
    | .Cons_n0 (he75 := he) .. =>
      exact absurd (Value.field.inj he) one_ne_zero
    | .Cons_other (x_b := xb) (x_rest := xrest) (v40 := v40) (m41 := m41)
        (cs52 := cs52) (cs85 := cs85)
        (ld12 := ld12) (ev54 := ev54) (hne78 := hne78) (ev87 := ev87) .. =>
      obtain ⟨t0, rest, rfl, rfl, hrest⟩ := RepList.cons_of_load hbvars ld12
      obtain ⟨ht0_d, ht0_lt⟩ := htgt t0 List.mem_cons_self
      have hv40 : v40 = .field 1 := by
        rcases args_contain_bvar_01 ev54 with he0 | he1
        · exact absurd he0 hne78
        · exact he1
      rw [hv40] at ev54
      obtain ⟨hmem0, rfl⟩ := args_contain_bvar_one_spec57 ht0_d ht0_lt hargs ev54
      have ih_rest := all_bvars_in_args_one_spec57
        (fun t ht => htgt t (List.mem_cons_of_mem _ ht)) hrest hargs ev87
      intro tgt htgt_mem
      rcases List.mem_cons.mp htgt_mem with rfl | hmem_tl
      · exact hmem0
      · exact ih_rest tgt hmem_tl

/-! ## The walk, scoped -/

theorem scoped_large_walk_fields_go {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {T : KKey} {lps : List LevelParam} {nP nF : Nat} {fvsP : List KExpr}
    (hnPF_lt : nP + nF < 144115188075855872)
    (hfvsP_not : ∀ k, nP ≤ k → ∀ e ∈ fvsP, ∀ fty, e ≠ .fvar k fty) :
    ∀ (rem field_idx : Nat) {Γ : Nat → KExpr} {cur_ty : KExpr} {xFvs idxArgs : List KExpr}
      {data_idxs : List Nat}
      {rc xty ptypes pbvars : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      rem + field_idx = nF →
      Ix.Kernel.openPisAtFvars rem cur_ty (nP + field_idx) =
        some (xFvs, Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs)) →
      CoreGood c cs →
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h (nP + field_idx) ptypes →
      GhostScoped Γ (nP + field_idx) →
      Tm c.κ (nP + field_idx) Γ h 0 cur_ty xty →
      (∀ idx ∈ data_idxs, idx < field_idx) →
      RepList byteListEnum (fun _ (n : Nat) v => v = .field (n : F)) h
        (data_idxs.map (fun idx => (nF - 1) - idx)) pbvars →
      ObsFn W "KernelCheck::check_large_walk_fields"
        [rc, xty, .field (nF : F), .field (field_idx : F), ptypes, pbvars] h (.field 1) h' cs →
      ∃ sorts_rem : List KLevel,
        sorts_rem.length = rem ∧
        (∀ idx ∈ data_idxs,
          idxArgs.contains (.fvar (nP + idx) (Γ (nP + idx))) = true) ∧
        ∀ i < rem, ∃ fv ty u,
          xFvs[i]? = some fv ∧
          sorts_rem[i]? = some u ∧
          Infer c.env .full (nP + field_idx + i) fv.fvarTypeD ty ∧
          Red c.env (nP + field_idx + i) ty (.sort u) ∧
          ((∀ φ, Level.eval φ u = 0) ∨ idxArgs.contains fv = true)
  | 0, field_idx, Γ, cur_ty, xFvs, idxArgs, data_idxs, rc, xty, ptypes, pbvars, h, h', cs,
      hsum, hop, hgood, _, _, _, hcur, hdata_lt, hbvars, ev => by
    have hfi_eq : field_idx = nF := by omega
    subst hfi_eq
    simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    match Obs.«KernelCheck::check_large_walk_fields».obs ev with
    | .other_Forall (op17 := op17) (hne88 := hne88) .. =>
      simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
        Except.ok.injEq, sub_self] at op17
      exact absurd op17.symm hne88
    | .other_other (he389 := he) .. =>
      exact absurd (Value.field.inj he) one_ne_zero
    | .n0 (m25 := m25) (cs36 := cs36) (w53 := w53) (x_args := xargs) (cs67 := cs67)
        (ev38 := ev38) (ev69 := ev69) (hc86 := hc86) .. =>
      subst hc86
      have hbnd36 : IxVM.Consistency.Bounded cs36 :=
        RomBound.bounded_mono hgood.bounded (fun z hz => by simp [hz])
      obtain ⟨hd, sp, H, As, hpair, _, hAs, heq_app⟩ :=
        SubstAux.gall c.κ .collect_spine _ _ _ _ _ ev38 xty rfl hbnd36 (nP + field_idx) Γ 0 _ hcur
      injection hpair with hlist; injection hlist with _ hlist; injection hlist with hsp _
      subst hsp
      have hAs_sub : ∀ e ∈ As, e ∈ fvsP ++ idxArgs := by
        have h1 : (Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs)).getAppArgs =
            fvsP ++ idxArgs := by
          rw [nat_getAppArgs_mkAppN]; rfl
        have h2 : (Expr.mkAppN H As).getAppArgs = H.getAppArgs ++ As := nat_getAppArgs_mkAppN As H
        have h3 : fvsP ++ idxArgs = H.getAppArgs ++ As := by
          rw [← h1, ← h2, heq_app]
        intro e he
        rw [h3]
        exact List.mem_append_right _ he
      have htgt : ∀ tgt ∈ data_idxs.map (fun idx => (field_idx - 1) - idx),
          tgt < nP + field_idx ∧ tgt < 144115188075855872 := by
        intro tgt htgt_mem
        obtain ⟨idx, hidx_mem, rfl⟩ := List.mem_map.mp htgt_mem
        have := hdata_lt idx hidx_mem
        exact ⟨by omega, by omega⟩
      have e1 := ev38.heap_extends
      have hbvars' : RepList byteListEnum (fun _ (n : Nat) v => v = .field (n : F)) m25
          (data_idxs.map (fun idx => (field_idx - 1) - idx)) pbvars :=
        repList_heapMono₂ byteListEnum (fun _ _ _ _ _ hv => hv) e1 hbvars
      have hall := all_bvars_in_args_one_spec57 htgt hbvars' hAs ev69
      refine ⟨[], rfl, ?_, fun _ hlt => nomatch hlt⟩
      intro idx hidx_mem
      have hidx_lt : idx < field_idx := hdata_lt idx hidx_mem
      have htgt_mem : (field_idx - 1) - idx ∈ data_idxs.map (fun idx => (field_idx - 1) - idx) :=
        List.mem_map.mpr ⟨idx, hidx_mem, rfl⟩
      have hmem_As := hall ((field_idx - 1) - idx) htgt_mem
      have hfv_eq : fvIdx (nP + field_idx) 0 ((field_idx - 1) - idx) = nP + idx := by
        unfold fvIdx; omega
      rw [hfv_eq] at hmem_As
      rcases List.mem_append.mp (hAs_sub _ hmem_As) with hmem_P | hmem_I
      · exact absurd rfl (hfvsP_not (nP + idx) (by omega) _ hmem_P _)
      · exact List.contains_iff_mem.mpr hmem_I
  | m + 1, field_idx, Γ, cur_ty, xFvs, idxArgs, data_idxs, rc, xty, ptypes, pbvars, h, h', cs,
      hsum, hop, hgood, hrc, htypes, hsc, hcur, hdata_lt, hbvars, ev => by
    match Obs.«KernelCheck::check_large_walk_fields».obs ev with
    | .n0 (op17 := op17) .. =>
      have hsub := evalBinOp_sub_nat (by omega : field_idx ≤ nF) op17
      rw [show nF - field_idx = m + 1 by omega] at hsub
      exact absurd hsub.symm (succ_field_ne_zero57 (by omega))
    | .other_other (he389 := he) .. =>
      exact absurd (Value.field.inj he) one_ne_zero
    | .other_Forall (x_dom := x_dom) (x_body := x_body) (w111 := w111)
        (v127 := v127) (m128 := m128) (cs138 := cs138)
        (v165 := v165) (m166 := m166) (y174 := y174) (cs184 := cs184)
        (m197 := m197) (v209 := v209) (x217 := x217)
        (v282 := v282) (m283 := m283) (cs285 := cs285)
        (m292 := m292) (cs325 := cs325) (v331 := v331)
        (ld103 := ld103) (ev140 := ev140) (hm205 := hm205) (ev186 := ev186)
        (op180 := op180) (op232 := op232) (op224 := op224) (sg290 := sg290)
        (hm302 := hm302) (op368 := op368) (ev327 := ev327) (hc384 := hc384) .. =>
      subst hc384
      obtain ⟨dom, body, _, rfl, hdom, hbody, _⟩ := hcur.forallE_of_load ld103
      obtain ⟨xFvs_tl, rfl, hop_tl⟩ := openPisAtFvars_succ_forallE hop
      rw [show nP + field_idx + 1 = nP + (field_idx + 1) by omega] at hop_tl
      have hg_es : CoreGood c cs138 := hgood.sub (fun z hz => by simp [hz])
      obtain ⟨ty₀, u₀, ℓ₀, hinf₀, hred₀, hℓ₀, hu₀⟩ :=
        scoped_core_ensure_sort hrc htypes hsc hc.env hc.loads hg_es ev140 hdom
      have e_es := ev140.heap_extends
      have e_zero : Heap.Extends m128 m197 := by rw [hm205]; exact Heap.Extends.snoc m128 _
      have hzero_rep : RepKLevel m197 .zero
          (.ptr (.enum "KernelTypes::KLevelNode") m128.length) := .zero (by rw [hm205]; simp)
      have hbnd184 : IxVM.Consistency.Bounded cs184 :=
        RomBound.bounded_mono hgood.bounded (fun z hz => by simp [hz])
      obtain ⟨hy174, e_eq⟩ := IxVM.Refinement.Levels.levelEqual_obs ev186 hbnd184
        (repKLevel_heapMono₂ e_zero hℓ₀) hzero_rep
      rw [evalBinOp_sub_nat (by omega : 1 ≤ nF) op232] at op224
      have hv209 : v209 = .field (((nF - 1) - field_idx : Nat) : F) :=
        evalBinOp_sub_nat (by omega : field_idx ≤ nF - 1) op224
      have hv331 : v331 = .field ((field_idx + 1 : Nat) : F) :=
        evalBinOp_add_nat field_idx 1 op368
      rw [hv331] at ev327
      have e_pre := e_es.trans (e_zero.trans e_eq)
      cases heq_lvl : IxVM.Refinement.KernelLevels.levelEqual ℓ₀ .zero with
      | true =>
        rw [heq_lvl] at hy174
        rw [hy174] at ev186 op180
        have hℓ_zero := IxVM.Refinement.KernelLevels.levelEqual_eq_true_sound heq_lvl
        have hu₀_zero : ∀ φ, Level.eval φ u₀ = 0 := fun φ => by
          rw [hu₀ φ, hℓ_zero φ]; rfl
        have hv165 : v165 = .field 0 := by
          simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
            Except.ok.injEq, sub_self] at op180
          exact op180.symm
        match sg290 with
        | .other (hne253 := hne) .. => exact absurd hv165 hne
        | .n0 (he250 := hv282) (he251 := hm283) (hc252 := hcs285) .. =>
          subst v282 m283 cs285
          obtain ⟨e_push, htypes', hsc'⟩ :=
            push_binder_types (hdom.mono e_pre) (htypes.mono e_pre) hsc
          rw [hm302] at ev327
          have htypes'' : TypesRep c.κ (Ghost.extend Γ (nP + field_idx) dom)
              (m166 ++ [.construct kexprListEnum "Cons" [x_dom, ptypes]])
              (nP + (field_idx + 1)) (.ptr (.enum kexprListEnum) m166.length) := by
            rw [show nP + (field_idx + 1) = nP + field_idx + 1 by omega]
            exact htypes'
          have hsc'' : GhostScoped (Ghost.extend Γ (nP + field_idx) dom)
              (nP + (field_idx + 1)) := by
            rw [show nP + (field_idx + 1) = nP + field_idx + 1 by omega]
            exact hsc'
          have hbody_open : Tm c.κ (nP + (field_idx + 1)) (Ghost.extend Γ (nP + field_idx) dom)
              (m166 ++ [.construct kexprListEnum "Cons" [x_dom, ptypes]]) 0
              (body.instantiate1 (.fvar (nP + field_idx) dom)) x_body := by
            rw [show nP + (field_idx + 1) = nP + field_idx + 1 by omega]
            exact (hbody.mono (e_pre.trans e_push)).open_body
              (Ghost.extend_at _ _ _) (Ghost.extend_below _ _ _)
          have hbvars' : RepList byteListEnum (fun _ (n : Nat) v => v = .field (n : F))
              (m166 ++ [.construct kexprListEnum "Cons" [x_dom, ptypes]])
              (data_idxs.map (fun idx => (nF - 1) - idx)) pbvars :=
            repList_heapMono₂ byteListEnum (fun _ _ _ _ _ hv => hv) (e_pre.trans e_push) hbvars
          have hg_rec : CoreGood c cs325 := hgood.sub (fun z hz => by simp [hz])
          obtain ⟨sorts_tl, hlen_tl, hdata_tl, hfields_tl⟩ :=
            scoped_large_walk_fields_go hc hnPF_lt hfvsP_not
              m (field_idx + 1) (by omega) hop_tl hg_rec
              (hrc.mono (e_pre.trans e_push)) htypes'' hsc'' hbody_open
              (fun idx hidx => Nat.lt_succ_of_lt (hdata_lt idx hidx)) hbvars' ev327
          refine ⟨u₀ :: sorts_tl, by simp [hlen_tl], ?_, ?_⟩
          · intro idx hidx
            have hlt_i := hdata_lt idx hidx
            have hmem_ext := hdata_tl idx hidx
            rwa [Ghost.extend_below _ _ _ _ (by omega)] at hmem_ext
          · intro i hi
            cases i with
            | zero =>
              exact ⟨.fvar (nP + field_idx) dom, ty₀, u₀, rfl, rfl,
                by simpa [Expr.fvarTypeD] using hinf₀, by simpa using hred₀, Or.inl hu₀_zero⟩
            | succ k =>
              obtain ⟨fv, ty, u, hfv, hu, hinf_k, hred_k, hor_k⟩ := hfields_tl k (by omega)
              rw [show nP + (field_idx + 1) + k = nP + field_idx + (k + 1) by omega] at hinf_k hred_k
              exact ⟨fv, ty, u, hfv, hu, hinf_k, hred_k, hor_k⟩
      | false =>
        rw [heq_lvl] at hy174
        rw [hy174] at op180
        have hv165 : v165 = .field 1 := by
          simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
            Except.ok.injEq, sub_zero] at op180
          exact op180.symm
        match sg290 with
        | .n0 (hv248 := hv0) .. =>
          exact absurd (Value.field.inj (hv165.symm.trans hv0)) one_ne_zero
        | .other (he261 := hv282) (hm260 := hm283) (hc281 := hcs285) .. =>
          subst hv282 hcs285
          have e_cons_bvar : Heap.Extends m166 m283 := by
            rw [hm283]; exact Heap.Extends.snoc m166 _
          have hbvars_m283 : RepList byteListEnum (fun _ (n : Nat) v => v = .field (n : F)) m283
              ((field_idx :: data_idxs).map (fun idx => (nF - 1) - idx))
              (.ptr (.enum byteListEnum) m166.length) :=
            RepLinkedList.cons (by rw [hm283]; simp) hv209
              (repList_heapMono₂ byteListEnum (fun _ _ _ _ _ hv => hv)
                (e_pre.trans e_cons_bvar) hbvars)
          have e_pre2 := e_pre.trans e_cons_bvar
          obtain ⟨e_push, htypes', hsc'⟩ :=
            push_binder_types (hdom.mono e_pre2) (htypes.mono e_pre2) hsc
          rw [hm302] at ev327
          have htypes'' : TypesRep c.κ (Ghost.extend Γ (nP + field_idx) dom)
              (m283 ++ [.construct kexprListEnum "Cons" [x_dom, ptypes]])
              (nP + (field_idx + 1)) (.ptr (.enum kexprListEnum) m283.length) := by
            rw [show nP + (field_idx + 1) = nP + field_idx + 1 by omega]
            exact htypes'
          have hsc'' : GhostScoped (Ghost.extend Γ (nP + field_idx) dom)
              (nP + (field_idx + 1)) := by
            rw [show nP + (field_idx + 1) = nP + field_idx + 1 by omega]
            exact hsc'
          have hbody_open : Tm c.κ (nP + (field_idx + 1)) (Ghost.extend Γ (nP + field_idx) dom)
              (m283 ++ [.construct kexprListEnum "Cons" [x_dom, ptypes]]) 0
              (body.instantiate1 (.fvar (nP + field_idx) dom)) x_body := by
            rw [show nP + (field_idx + 1) = nP + field_idx + 1 by omega]
            exact (hbody.mono (e_pre2.trans e_push)).open_body
              (Ghost.extend_at _ _ _) (Ghost.extend_below _ _ _)
          have hbvars_m292 : RepList byteListEnum (fun _ (n : Nat) v => v = .field (n : F))
              (m283 ++ [.construct kexprListEnum "Cons" [x_dom, ptypes]])
              ((field_idx :: data_idxs).map (fun idx => (nF - 1) - idx))
              (.ptr (.enum byteListEnum) m166.length) :=
            repList_heapMono₂ byteListEnum (fun _ _ _ _ _ hv => hv) e_push hbvars_m283
          have hg_rec : CoreGood c cs325 := hgood.sub (fun z hz => by simp [hz])
          have hdata_lt' : ∀ idx ∈ field_idx :: data_idxs, idx < field_idx + 1 := by
            intro idx hidx
            rcases List.mem_cons.mp hidx with rfl | hmem
            · omega
            · exact Nat.lt_succ_of_lt (hdata_lt idx hmem)
          obtain ⟨sorts_tl, hlen_tl, hdata_tl, hfields_tl⟩ :=
            scoped_large_walk_fields_go hc hnPF_lt hfvsP_not
              m (field_idx + 1) (by omega) hop_tl hg_rec
              (hrc.mono (e_pre2.trans e_push)) htypes'' hsc'' hbody_open
              hdata_lt' hbvars_m292 ev327
          have hcur_in_idx : idxArgs.contains (.fvar (nP + field_idx) dom) = true := by
            have hmem_head := hdata_tl field_idx List.mem_cons_self
            rwa [Ghost.extend_at] at hmem_head
          refine ⟨u₀ :: sorts_tl, by simp [hlen_tl], ?_, ?_⟩
          · intro idx hidx
            have hlt_i := hdata_lt idx hidx
            have hmem_ext := hdata_tl idx (List.mem_cons_of_mem _ hidx)
            rwa [Ghost.extend_below _ _ _ _ (by omega)] at hmem_ext
          · intro i hi
            cases i with
            | zero =>
              exact ⟨.fvar (nP + field_idx) dom, ty₀, u₀, rfl, rfl,
                by simpa [Expr.fvarTypeD] using hinf₀, by simpa using hred₀, Or.inr hcur_in_idx⟩
            | succ k =>
              obtain ⟨fv, ty, u, hfv, hu, hinf_k, hred_k, hor_k⟩ := hfields_tl k (by omega)
              rw [show nP + (field_idx + 1) + k = nP + field_idx + (k + 1) by omega] at hinf_k hred_k
              exact ⟨fv, ty, u, hfv, hu, hinf_k, hred_k, hor_k⟩

theorem scoped_large_prop_ctor_go {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {T : KKey} {lps : List LevelParam} {nP nF : Nat}
    {fvsP crest : KExpr → Prop}
    {fvsP_full xFvs idxArgs : List KExpr} {crest₀ : KExpr}
    (hnPF_lt : nP + nF < 144115188075855872)
    (hfvsP_not : ∀ k, nP ≤ k → ∀ e ∈ fvsP_full, ∀ fty, e ≠ .fvar k fty)
    (hopF : Ix.Kernel.openPisAtFvars nF crest₀ nP =
      some (xFvs, Expr.mkAppN (.const T (lps.map .param)) (fvsP_full ++ idxArgs))) :
    ∀ (remP off : Nat) {Γ : Nat → KExpr} {cur_ty : KExpr} {fvsP_rem : List KExpr}
      {rc xty ptypes : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      remP + off = nP →
      Ix.Kernel.openPisAtFvars remP cur_ty off = some (fvsP_rem, crest₀) →
      CoreGood c cs →
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h off ptypes →
      GhostScoped Γ off →
      Tm c.κ off Γ h 0 cur_ty xty →
      ObsFn W "KernelCheck::check_large_prop_ctor"
        [rc, xty, .field (remP : F), .field (nF : F), ptypes] h (.field 1) h' cs →
      ∃ sorts : List KLevel,
        FieldSortsJ rulesJ c.env true true .zero nP xFvs idxArgs nF sorts
  | 0, off, Γ, cur_ty, fvsP_rem, rc, xty, ptypes, h, h', cs,
      hsum, hopP, hgood, hrc, htypes, hsc, hcur, ev => by
    have hoff_eq : off = nP := by omega
    subst hoff_eq
    simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hopP
    obtain ⟨rfl, rfl⟩ := hopP
    match Obs.«KernelCheck::check_large_prop_ctor».obs ev with
    | .other_Forall (hne75 := hne) .. => exact absurd rfl hne
    | .other_other (he204 := he) .. => exact absurd (Value.field.inj he) one_ne_zero
    | .n0 (cs18 := cs18) (m62 := m62) (hm70 := hm70) (ev20 := ev20) (hc74 := hc74) .. =>
      subst hc74
      have e_nil : Heap.Extends h m62 := by rw [hm70]; exact Heap.Extends.snoc h _
      have hbvars_nil : RepList byteListEnum (fun _ (n : Nat) v => v = .field (n : F)) m62
          (([] : List Nat).map (fun idx => (nF - 1) - idx))
          (.ptr (.enum byteListEnum) h.length) :=
        RepLinkedList.nil (by rw [hm70]; simp)
      have hg_walk : CoreGood c cs18 := hgood.sub (fun z hz => by simp [hz])
      obtain ⟨sorts, hlen, _, hfields⟩ :=
        scoped_large_walk_fields_go hc hnPF_lt hfvsP_not
          nF 0 (by omega) (by simpa using hopF) hg_walk
          (hrc.mono e_nil) (by simpa using htypes.mono e_nil) (by simpa using hsc)
          (by simpa using hcur.mono e_nil) (by intro _ hm; cases hm) hbvars_nil ev20
      refine ⟨sorts, hlen, ?_⟩
      intro i hi
      obtain ⟨fv, ty, u, hfv, hu, hinf, hred, hor⟩ := hfields i hi
      rw [show off + 0 + i = off + i by omega] at hinf hred
      exact ⟨fv, ty, u, hfv, hu, hinf, hred, (fun h => nomatch h), (fun _ _ => hor)⟩
  | m + 1, off, Γ, cur_ty, fvsP_rem, rc, xty, ptypes, h, h', cs,
      hsum, hopP, hgood, hrc, htypes, hsc, hcur, ev => by
    match Obs.«KernelCheck::check_large_prop_ctor».obs ev with
    | .n0 (hv14 := hv) .. =>
      exact absurd hv (succ_field_ne_zero57 (by omega))
    | .other_other (he204 := he) .. =>
      exact absurd (Value.field.inj he) one_ne_zero
    | .other_Forall (x_dom := x_dom) (x_body := x_body) (m115 := m115)
        (cs148 := cs148) (v153 := v153)
        (ld90 := ld90) (hm125 := hm125) (op183 := op183) (ev150 := ev150) (hc199 := hc199) .. =>
      subst hc199
      obtain ⟨dom, body, _, rfl, hdom, hbody, _⟩ := hcur.forallE_of_load ld90
      obtain ⟨fvsP_tl, rfl, hopP_tl⟩ := openPisAtFvars_succ_forallE hopP
      obtain ⟨e_push, htypes', hsc'⟩ := push_binder_types hdom htypes hsc
      rw [evalBinOp_sub_succ m op183, hm125] at ev150
      have hbody_open : Tm c.κ (off + 1) (Ghost.extend Γ off dom)
          (h ++ [.construct kexprListEnum "Cons" [x_dom, ptypes]]) 0
          (body.instantiate1 (.fvar off dom)) x_body :=
        (hbody.mono e_push).open_body (Ghost.extend_at _ _ _) (Ghost.extend_below _ _ _)
      have hg_rec : CoreGood c cs148 := hgood.sub (fun z hz => by simp [hz])
      exact scoped_large_prop_ctor_go (fvsP := fvsP) (crest := crest)
        hc hnPF_lt hfvsP_not hopF m (off + 1) (by omega) hopP_tl hg_rec
        (hrc.mono e_push) htypes' hsc' hbody_open ev150

/-! ## A stored constructor, opened -/

/-- **An opening of `n + m` binders is the two openings in turn.** -/
theorem openPisAtFvars_split_some : ∀ (n : Nat) {m : Nat} {e : KExpr} {d : Nat}
    {fvs : List KExpr} {o : KExpr},
    Ix.Kernel.openPisAtFvars (n + m) e d = some (fvs, o) →
    ∃ fvs₁ o₁ fvs₂, Ix.Kernel.openPisAtFvars n e d = some (fvs₁, o₁) ∧
      Ix.Kernel.openPisAtFvars m o₁ (d + n) = some (fvs₂, o) ∧ fvs = fvs₁ ++ fvs₂
  | 0, m, e, d, fvs, o, h => by
    refine ⟨[], e, fvs, rfl, ?_, rfl⟩
    simpa using h
  | n + 1, m, e, d, fvs, o, h => by
    rw [show n + 1 + m = (n + m) + 1 by omega] at h
    match e, h with
    | .forallE dom body bi, h =>
      obtain ⟨fvs_tl, rfl, htl⟩ := openPisAtFvars_succ_forallE h
      obtain ⟨fvs₁, o₁, fvs₂, h₁, h₂, rfl⟩ := openPisAtFvars_split_some n htl
      refine ⟨.fvar d dom :: fvs₁, o₁, fvs₂, ?_, ?_, rfl⟩
      · simp only [Ix.Kernel.openPisAtFvars, h₁]
      · rw [show d + (n + 1) = d + 1 + n by omega]
        exact h₂
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Ix.Kernel.openPisAtFvars] at h

/-- **A stored constructor's type, opened at its parameters and then at its fields**: the
residual is the family applied to the parameters' variables, then the index arguments. -/
theorem ctor_open_residual {ty : KExpr} {nP nF : Nat}
    {cbs : List (KExpr × Ix.Kernel.BinderMeta)} {T : KKey} {us : List KLevel} {es : List KExpr}
    (hst : ty.stripPis (nP + nF) =
      some (cbs, Expr.mkAppN (.const T us) (Ix.Kernel.structPsAt nF nP ++ es))) :
    ∃ (fvsP : List KExpr) (crest : KExpr) (xFvs idxArgs : List KExpr),
      Ix.Kernel.openPisAtFvars nP ty 0 = some (fvsP, crest) ∧
      Ix.Kernel.openPisAtFvars nF crest nP =
        some (xFvs, Expr.mkAppN (.const T us) (fvsP ++ idxArgs)) ∧
      fvsP.length = nP := by
  obtain ⟨fvs, o, hop⟩ := Ix.Kernel.Model.openPisAtFvars_of_stripPis_isSome (nP + nF)
    (e := ty) 0 (by simp [hst])
  have hbody := Ix.Kernel.Verify.openPisAtFvars_instSeq (nP + nF) hop hst
  obtain ⟨-, -, -, hlen, hIdx, -⟩ := Ix.Kernel.Verify.openPisAtFvars_stripPis (nP + nF) hop
  have hfvsB : ∀ a ∈ fvs, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨j, hjlt, rfl⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨fty, hfj⟩ := hIdx j (by rw [← hlen]; exact hjlt)
    rw [List.getElem?_eq_getElem hjlt] at hfj
    rw [Option.some.inj hfj]
    rfl
  obtain ⟨fvsP, crest, xFvs, hopP, hopF, rfl⟩ := openPisAtFvars_split_some nP hop
  have hlenP : fvsP.length = nP := Ix.Kernel.Model.openPisAtFvars_length nP hopP
  have hps : (Ix.Kernel.structPsAt nF nP).map
      (fun x => Expr.instSeq (fvsP ++ xFvs) (nP + nF - 1) x) = fvsP := by
    apply List.ext_getElem
    · simp [Ix.Kernel.structPsAt, hlenP]
    · intro k h1 h2
      have hk : k < nP := by rw [← hlenP]; exact h2
      simp only [List.getElem_map, Ix.Kernel.structPsAt, List.getElem_range]
      have hb := Ix.Kernel.Expr.instSeq_bvar (fvsP ++ xFvs) (nP + nF - 1) (nF + nP - 1 - k)
        hfvsB (by omega) (by rw [hlen]; omega)
      rw [show nP + nF - 1 - (nF + nP - 1 - k) = k by omega,
        List.getElem?_append_left (by omega), List.getElem?_eq_getElem h2] at hb
      exact (Option.some.inj hb).symm
  rw [Ix.Kernel.Expr.instSeq_mkAppN,
    Ix.Kernel.Expr.instSeq_eq_self (fvsP ++ xFvs) (nP + nF - 1) (e := Expr.const T us) rfl,
    List.map_append, hps] at hbody
  refine ⟨fvsP, crest, xFvs, es.map (fun x => Expr.instSeq (fvsP ++ xFvs) (nP + nF - 1) x),
    hopP, ?_, hlenP⟩
  rw [Nat.zero_add] at hopF
  rw [hopF, hbody]

end IxVM.Refinement.Decl

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (NativeFam NativeFamStored FieldSortsJ)
open Ix.Kernel.Model (rulesJ)

universe u

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

/-! ## The field sorts at the arm -/

/-- **The field sorts of the late relation at the tied parent**: at a large eliminator of a
propositional family, every stored constructor (there is at most one, by the elimination
restriction) opened at its parameters and fields has its fields' sorts, each a proposition at
every assignment or an index argument of the residual, at the step's environment. From the
canonical comparison's `is_large_eliminator` run: its arm that walks the constructor loaded by
`get_ci_cprj(block, idx, 0)` (the stored constructor under the prefix keying, read at positions
that are its own level parameters, the registry's `L1`), the scoped walk, and the stored
constructor's opened residual. -/
theorem rec_field_sorts_of_arm {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {bAddr A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor} {n : Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc) (hlim : lim = some n)
    (hnat : NativeRecArm calls bAddr t A n) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} {cm : Ixon.Constant}
    (hcm : Ix.Cert.recordAt E P = some cm) (hcmi : cm.info = .iPrj ip)
    (htie : RecMajorTie t E₀ A c rc P)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hcb : Ix.Cert.recordAt E ip.block = some cb) (hms : cb.info = .muts ms)
    (hind : ms[ip.idx.toNat]? = some (.indc ind))
    {fam : NativeFam .anon} (hm : MatchedAt t E env P ip fam) :
    decide (rc.lvls.toNat = ind.lvls.toNat + 1) = true → fam.p.isProp = true →
      ∀ (j : Nat) (cA : ConstantVal .anon × Nat), fam.ctorsA[j]? = some cA →
        ∃ (fvsP : List Core.KExpr) (crest : Core.KExpr) (xFvs : List Core.KExpr)
          (xrest : Core.KExpr) (sorts : List Core.KLevel),
          Ix.Kernel.openPisAtFvars fam.p.nP cA.1.type 0 = some (fvsP, crest) ∧
          Ix.Kernel.openPisAtFvars cA.2 crest fam.p.nP = some (xFvs, xrest) ∧
          FieldSortsJ rulesJ env true true fam.p.resSort fam.p.nP xFvs
            (xrest.getAppArgs.drop fam.p.nP) cA.2 sorts := by
  intro hlarge hprop j cA hcA
  have hlarge' : rc.lvls.toNat = ind.lvls.toNat + 1 := of_decide_eq_true hlarge
  obtain ⟨hat, hname, cb', ms', ind', hcb', hms', hind', hnP, hnI, hlenC, hnames⟩ := hm
  have hcbE : cb' = cb := Option.some.inj (hcb'.symm.trans hcb)
  subst hcbE
  have hmsE : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hms)
  subst hmsE
  have hindE : ind' = ind := Ixon.MutConst.indc.inj (Option.some.inj (hind'.symm.trans hind))
  subst hindE
  -- the result sort is zero, so there is one constructor
  have hiso : Ix.Kernel.Level.isEquiv fam.p.resSort .zero = some true := by
    have h := hat.isProp
    rw [hprop] at h
    simpa using h.symm
  have hz : ∀ φ, Ix.Kernel.Level.eval φ fam.p.resSort = 0 := fun φ =>
    (Ix.Kernel.Level.isEquiv_sound hiso φ).trans rfl
  have helim := rec_elim_of_arm ht hS hst hc hinfo hlim hnat hinert hcover hstep hcm hcmi htie
    hcb' hms' hind' hat hname hnP hnI hlenC hlarge
  have hlen2 : fam.ctorsA.length < 2 := by
    rcases helim with h | h
    · exact absurd (hz (fun _ => 0)) (h (fun _ => 0))
    · exact h
  have hjlt : j < fam.ctorsA.length := (List.getElem?_eq_some_iff.mp hcA).1
  have hj : j = 0 := by omega
  subst hj
  have hsz1 : ind.ctors.size = 1 := by omega
  -- the stored constructor, opened
  obtain ⟨hfindC, hlpsC, cbs, es, hresC, -⟩ := hat.stored.ctor 0 cA hcA
  obtain ⟨fvsP, crest, xFvs, idxArgs, hopP, hopF, hlenP⟩ := Decl.ctor_open_residual hresC
  have hxa : ∀ us : List Ix.Kernel.Level,
      ((Ix.Kernel.Expr.mkAppN (Ix.Kernel.Expr.const fam.p.cvT.name us) (fvsP ++ idxArgs) :
        Core.KExpr).getAppArgs).drop fam.p.nP = idxArgs := by
    intro us
    have hga : ((Ix.Kernel.Expr.mkAppN (Ix.Kernel.Expr.const fam.p.cvT.name us)
        (fvsP ++ idxArgs) : Core.KExpr).getAppArgs) = fvsP ++ idxArgs := by
      rw [Decl.nat_getAppArgs_mkAppN]
      rfl
    rw [hga, ← hlenP]
    exact List.drop_left
  by_cases h0 : cA.2 = 0
  · refine ⟨fvsP, crest, xFvs, _, [], hopP, hopF, by simp [h0], fun i hi => ?_⟩
    exact absurd hi (by omega)
  -- the circuit's walk
  obtain ⟨-, hL1⟩ := hat.logic_lvls ht hname hcm hcmi hcb' hms' hind'
  obtain ⟨rcv, apv, parentV, tyPtr, rulesPtr, blkPtr, tyPtrP, unsP, blkPtrP, kTarget, result,
    pointer, bA, bR, bT, bP, blobs, tree, scanHeap, loadedHeap, kHeap, kAfter, canonHeap, final,
    loadCalls, kCalls, canonCalls, hrc, hbA, hbA', hbR, hbR', hbT, hbT', hbP, hbP', hblob, rty,
    hrulesTr, hrules_lt, hidx56, hlvR, hlvP, hpP, hiP, hcP, eSL, evLoad, hsLoad, hldP, eK, evK,
    hsK, hkEq, eC, evCanon, hsCanon⟩ :=
    rec_arm_of_arm ht hS hst hc hinfo hlim hnat hinert hcover hstep hcm hcmi htie hcb' hms' hind'
  subst hlim
  let cS : Core.ScopedCtx := Core.Ctx.stored ⟨E, env, t, some n⟩
  have hcS : Core.ScopedCoreFacts cS := hstep.inv.scopedCoreFacts
  -- the parent's type, as the stored former's
  have hformer : env.find? (Core.keyOf t P) =
      some (.indInfo fam.cvS (Ix.Kernel.nativeCaps fam.p)) := by
    rw [LoadedReads.keyOf_eq, ← hname]
    exact hat.stored.former
  have hκP : cS.κ P = Core.keyOf t P :=
    Core.Ctx.stored_key_of_find (c := ⟨E, env, t, some n⟩) hformer
  have hgL : Core.Good ⟨E, env, t, some n⟩ loadCalls := (hst.good env (some n)).sub hsLoad
  obtain ⟨ci, hfind, hptr⟩ := Core.get_ci_step cS hcS evLoad parentV bT rfl trivial
    (by rw [hbT', hκP]; exact Core.Resolved.ne)
    (Core.CoreGood.ofRaw hgL (fun _ _ => trivial)) hbT
  rw [hbT', hκP] at hfind
  have hci : ci = .indInfo fam.cvS (Ix.Kernel.nativeCaps fam.p) :=
    Option.some.inj (hfind.symm.trans hformer)
  subst hci
  obtain ⟨v, hv, hrep⟩ := hptr
  rw [hldP] at hv
  injection hv with hv
  subst hv
  obtain ⟨cv, caps, hcv, hval⟩ := ciRep_induct_fields hrep
  obtain ⟨hcvEq, -⟩ := Ix.Kernel.ConstantInfo.indInfo.inj hcv
  subst hcvEq
  obtain ⟨-, -, hperm, htm⟩ := hval
  obtain ⟨bs, hsort⟩ := hat.sort
  rw [hat.tele, hnP, hnI] at hsort
  have hpos : ∃ bs', (Core.posOf fam.cvS.levelParams fam.cvS.type).stripPis
      (ind.params.toNat + ind.indices.toNat) =
      some (bs', .sort (Ix.Kernel.Level.subst fam.cvS.levelParams
        (Core.posLevels fam.cvS.levelParams) fam.p.resSort)) :=
    ⟨_, by
      unfold Core.posOf
      rw [Decl.stripPis_instantiateLevelParams_full, hsort]
      rfl⟩
  obtain ⟨bs', hpos⟩ := hpos
  -- the canonical comparison
  have hgC : Core.Good ⟨E, env, t, some n⟩ canonCalls := (hst.good env (some n)).sub hsCanon
  have hsub : ∀ {cs : List (Call F)}, (∀ x ∈ cs, x ∈ canonCalls) → Core.CoreGood cS cs :=
    fun h => Core.CoreGood.ofRaw (hgC.sub h) (fun _ _ => trivial)
  match Obs.«KernelCheck::check_recursor_canonical_full».obs evCanon with
  | .other (hne568 := hne) .. =>
    exact absurd rfl (hne [_, _, _, _, _, _, _, _] rfl)
  | .Induct (m272 := m272) (m329 := m329) (m281 := m281) (m389 := m389) (v280 := resLvl)
      (v296 := nsum) (v341 := univ) (v271 := single) (cs291 := cs291) (sg279 := seg)
      (op325 := hsumOp) (hm337 := hm337) (ev293 := sortRun) (ev399 := soloRun)
      (ev354 := largeRun) (ev518 := natRun) (hc567 := children) (hv86 := parentShape) .. =>
    injection parentShape with _ _ parentFields
    simp only [List.cons.injEq, and_true] at parentFields
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := parentFields
    match seg with
    | .other (hne203 := hne) .. =>
      exact absurd (by simp [hsz1]) hne
    | .n1 (v143 := v143) (m144 := m144) (p151 := p151) (cs157 := cs157) (ev159 := cprjRun)
        (ld153 := ldC) (he187 := hsingle) (he201 := hh) (hc202 := hcs) .. =>
      -- the loaded constructor is the stored one
      have hfindK := hfindC
      rw [hnames 0 cA hcA, ← LoadedReads.keyOf_eq] at hfindK
      have hκC : cS.κ (Core.cprjAddr ip.block ip.idx.toNat 0) =
          Core.keyOf t (Core.cprjAddr ip.block ip.idx.toNat 0) :=
        Core.Ctx.stored_key_of_find (c := ⟨E, env, t, some n⟩) hfindK
      have hidx : ZMod.val ((ip.idx.toNat : Nat) : F) = ip.idx.toNat :=
        ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
      have hfindC' : cS.env.find? (cS.κ (Core.cprjAddr (Core.ixAddr bP)
          (ZMod.val ((ip.idx.toNat : Nat) : F)) (ZMod.val (0 : F)))) =
          some (.ctorInfo cA.1 fam.p.nP cA.2) := by
        rw [hbP', hidx, ZMod.val_zero, hκC]
        exact hfindK
      obtain ⟨-, hctor⟩ := Core.get_ci_cprj_step cS hcS cprjRun _
        ((ip.idx.toNat : Nat) : F) (0 : F) bP rfl trivial (Or.inr ⟨_, _, _, _, hfindC'⟩)
        (hsub (fun x hx => by rw [children, hcs]; simp [hx]))
        (Bytes.repAddressRef_heapMono₂ Core.addrTy eC hbP)
      obtain ⟨w, hw, hrepC⟩ := hctor _ _ _ hfindC'
      rw [ldC] at hw
      injection hw with hw
      rw [← hw] at hrepC
      -- heaps
      have e1 : Heap.Extends canonHeap m272 := by
        rw [hh]
        exact cprjRun.heap_extends
      have e2 : Heap.Extends canonHeap m329 := e1.trans (ext_of_eq_snoc hm337)
      -- the result level is the family's sort
      have hnsum : nsum = .field ((ind.params.toNat + ind.indices.toNat : Nat) : F) :=
        Decl.evalBinOp_add_nat _ _ hsumOp
      rw [hnsum] at sortRun
      have htys : Core.TypesRep cS.κ (fun _ => default) m329 0
          (.ptr (.enum Core.kexprListEnum) m272.length) := by
        rw [hm337]
        exact Decl.typesRep_alloc_nil _ _ _
      obtain ⟨ℓ, hℓ, hlv⟩ := Decl.get_result_sort_level_any_spec
        (ind.params.toNat + ind.indices.toNat) (by omega)
        (((hrc.mono eC).toRCRep).mono e2) htys (Decl.ghostScoped_zero _) hcS.env hcS.loads
        (hsub (fun x hx => by rw [children]; simp [hx]))
        ((htm.mono (eC.trans e2)) 0 (fun _ => default)) sortRun
      have hsℓ := hlv bs' _ hpos
      have huniv : univ = .field 1 := by
        rw [evalBinOp_add_inv (nat_rec_check_levels natRun), hlarge']
        congr 1
        push_cast
        ring
      rw [huniv] at largeRun
      have hℓ' : IxVM.Refinement.KernelLevels.RepKLevel m389 ℓ resLvl :=
        IxVM.Refinement.KernelLevels.repKLevel_heapMono₂ soloRun.heap_extends hℓ
      match Obs.«KernelCheck::is_large_eliminator».obs largeRun with
      | .n1 (ev15 := e15) .. =>
        exfalso
        obtain ⟨hr1, -⟩ := IxVM.Refinement.Levels.levelIsNotZero_step e15 resLvl rfl ℓ hℓ'
        have hnz : ℓ.isNeverZero = true := by
          cases hz' : ℓ.isNeverZero
          · rw [hz'] at hr1
            exact absurd (Value.field.inj hr1) one_ne_zero
          · rfl
        have hne := eval_ne_zero_of_posOf hperm (fun φ => by
          rw [hsℓ φ]
          exact Ix.Kernel.Level.isNeverZero_sound φ ℓ hnz)
        exact hne (fun _ => 0) (hz _)
      | .other_n0 (he49 := he) .. => exact absurd (Value.field.inj he) one_ne_zero
      | .other_other_n0 (hv69 := hv) .. =>
        exfalso
        have := field_nat_eq_zero (by omega) hv
        omega
      | .other_other_n1_n0 (he118 := he) .. => exact absurd (Value.field.inj he) one_ne_zero
      | .other_other_n1_other_other (he264 := he) .. =>
        exact absurd (Value.field.inj he) one_ne_zero
      | .other_other_other (he272 := he) .. => exact absurd (Value.field.inj he) one_ne_zero
      | .other_other_n1_other_Ctor_n0 (hv92 := hv92) .. =>
        exfalso
        rw [hsingle] at hv92
        injection hv92 with hl
        simp only [List.cons.injEq, and_true] at hl
        obtain ⟨-, hvC⟩ := hl
        rw [hvC] at hrepC
        obtain ⟨cv', nP', nF', hciC, -, -, hnf', ⟨-, hnF56⟩, -⟩ := Core.CIRep.ctor_fields hrepC
        obtain ⟨-, -, rfl⟩ := Ix.Kernel.ConstantInfo.ctorInfo.inj hciC
        exact h0 (field_nat_eq_zero (by omega) hnf'.symm)
      | .other_other_n1_other_Ctor_other (v1 := v1) (m2 := m2) (cs13 := cs13)
          (x_ctor_ty := xcty) (x_n_params := xnp) (x_n_fields := xnf) (cs210 := cs210)
          (m247 := m247) (ev15 := e15) (hv92 := hv92) (hm255 := hm255) (ev212 := walkRun)
          (hc259 := hcl) .. =>
        rw [hsingle] at hv92
        injection hv92 with hl
        simp only [List.cons.injEq, and_true] at hl
        obtain ⟨-, hvC⟩ := hl
        rw [hvC] at hrepC
        obtain ⟨cv', nP', nF', hciC, hvr, hnp', hnf', ⟨hnP56, hnF56⟩, -⟩ :=
          Core.CIRep.ctor_fields hrepC
        obtain ⟨rfl, rfl, rfl⟩ := Ix.Kernel.ConstantInfo.ctorInfo.inj hciC
        obtain ⟨-, -, -, htmC⟩ := hvr
        rw [hlpsC, hL1, Decl.posOf_range] at htmC
        subst hnp' hnf'
        have e247 : Heap.Extends m144 m247 := by
          rw [← hh]
          exact (ext_of_eq_snoc hm337).trans (sortRun.heap_extends.trans
            (soloRun.heap_extends.trans (e15.heap_extends.trans (ext_of_eq_snoc hm255))))
        have hrcv : Core.RCRep cS.t cS.lim m247 rcv :=
          ((hrc.mono eC).toRCRep).mono (e1.trans (by rw [hh]; exact e247))
        have htypes : Core.TypesRep cS.κ (fun _ => default) m247 0
            (.ptr (.enum Core.kexprListEnum) m2.length) := by
          rw [hm255]
          exact Decl.typesRep_alloc_nil _ _ _
        obtain ⟨sorts, hfs⟩ := Decl.scoped_large_prop_ctor_go (fvsP := fun _ => True)
          (crest := fun _ => True) hcS (by omega : fam.p.nP + cA.2 < 144115188075855872)
          (Decl.fvar_not_in_fvsP hopP (by omega)) hopF fam.p.nP 0 (by omega) hopP
          (hsub (fun x hx => by rw [children, hcl]; simp [hx])) hrcv htypes
          (Decl.ghostScoped_zero _) ((htmC.mono e247) 0 (fun _ => default)) walkRun
        refine ⟨fvsP, crest, xFvs, _, sorts, hopP, hopF, ?_⟩
        rw [hxa]
        exact Decl.fieldSortsJ_isProp_true_set_sort hfs

end IxVM.Refinement.Typing
