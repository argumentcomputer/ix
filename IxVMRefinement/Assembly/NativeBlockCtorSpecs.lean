import IxVMRefinement.Decl.NativeFront
import IxVMRefinement.Decl.NativeShape

/-! # Typed helper specifications of the native constructor loop at any keying

The constructor loop of a native block calls `get_result_sort_level`, `check_param_agreement` and
`check_field_universes` on terms typed against the constructor stage, whose keying resolves the
addresses its environment stores and no other (`Decl.ctorStage`). Their specifications in
`Decl/NativeFront.lean` are stated at a table-keyed context, but the keying assumption is only
passed through: every step uses the scoped core (`scoped_core_whnf`, `scoped_core_defeq`,
`scoped_core_ensure_sort`) at the context's own keying. The specifications below are the same
proofs at any scoped context:

* `get_result_sort_level_staged_bounded_spec`, and `NativeShapeCalls.resultSort_staged` (the
  result sort the loop compares the fields against);
* `check_param_agreement_staged_spec` (the parameter domains of a constructor agree with the
  former's);
* `check_field_universes_staged_spec` (the sorts of the fields).
-/

universe u

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (ConstantInfo ConstantVal Declaration Expr Level LevelParam)
open Ix.Kernel.Rules (Red DefEq Infer)
open Ix.Kernel.Semantics (Judgements ConstantValRunJ ConstantValCheckJ DeclRunJ IndRoutesJ
  SumIndRunJ FormerStoredJ FormerReadJ SumCtorsRunJ SumCtorRunJ StructDomsJ FieldSortsJ
  DeclNativeNoRecRunJ nativePartsNoRec? nativeRecStub ctorZeroOk famDomOk famHead pwsAll)
open Ix.Kernel.Model (rulesJ)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ## The result sort -/

/-- `get_result_sort_level_scoped_bounded_spec` at any scoped context. -/
theorem get_result_sort_level_staged_bounded_spec {c : ScopedCtx} :
    ∀ (n : Nat) {d : Nat} {Γ : Nat → KExpr} {E : KExpr}
      {rc pe types r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 18446744069414584321 →
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h d types →
      GhostScoped Γ d →
      CoreEnvFacts c.toCtx →
      ScopedLoadFacts c →
      CoreGood c cs →
      Tm c.κ d Γ h 0 E pe →
      ObsFn W "KernelCheck::get_result_sort_level" [rc, pe, .field (n : F), types] h r h' cs →
      ∃ ℓ : KLevel, RepKLevel h' ℓ r ∧
        ∀ bs s, E.stripPis n = some (bs, .sort s) → LvEq s ℓ
  | 0, d, Γ, E, rc, pe, types, r, h, h', cs, _, hrc, hty, hsc, hef, hlf, hgood, hE, ev => by
    match Obs.«KernelCheck::get_result_sort_level».obs ev with
    | .n0 (cs12 := cs12) (ev14 := ev_w) (ld55 := ld) (he69 := hr) (he70 := hh) (hc71 := hc) .. =>
      subst hc hr hh
      have hg1 : CoreGood c cs12 := hgood.sub (fun x hx => by simp [hx])
      obtain ⟨E', hE', hrigid⟩ := Core.GuardData.head_rep ⟨hef, hlf⟩ hg1 hE ev_w
      obtain ⟨u, rfl, ℓ, hℓ, huℓ⟩ := hE'.sort_of_load ld
      refine ⟨ℓ, hℓ, fun bs s hst => ?_⟩
      simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
      obtain ⟨rfl, rfl⟩ := hst
      have hsort := hrigid rfl
      injection hsort with hsu
      subst hsu
      exact huℓ
    | .other (hne73 := hne) .. => exact absurd rfl hne
  | m + 1, d, Γ, E, rc, pe, types, r, h, h', cs, hlt, hrc, hty, hsc, hef, hlf, hgood, hE, ev => by
    match Obs.«KernelCheck::get_result_sort_level».obs ev with
    | .n0 (hv43 := hv) .. => exact absurd hv (succ_field_ne_zero_bounded hlt)
    | .other (cs12 := cs12) (x_body := xbody) (cs115 := cs2) (m152 := m3) (ev14 := ev_w)
        (ld88 := ld) (op149 := op) (hm160 := hm3) (ev117 := ev_rec) (hc180 := hc) .. =>
      subst hc
      have hg1 : CoreGood c cs12 := hgood.sub (fun x hx => by simp [hx])
      have hg2 : CoreGood c cs2 := hgood.sub (fun x hx => by simp [hx])
      obtain ⟨E', hE', hrigid⟩ := Core.GuardData.head_rep ⟨hef, hlf⟩ hg1 hE ev_w
      obtain ⟨T, B, _, rfl, hT, hB, _⟩ := hE'.forallE_of_load ld
      have ext_w := ev_w.heap_extends
      obtain ⟨ext_push, hty', hsc'⟩ := push_binder_types hT (hty.mono ext_w) hsc
      rw [← hm3] at ext_push hty'
      have hB_open : Tm c.κ (d + 1) (Ghost.extend Γ d T) m3 0 (B.instantiate1 (.fvar d T)) xbody :=
        (hB.open_body (Ghost.extend_at Γ d T) (Ghost.extend_below Γ d T)).mono ext_push
      rw [evalBinOp_sub_succ m op] at ev_rec
      obtain ⟨ℓ, hℓ, htele⟩ := get_result_sort_level_staged_bounded_spec m (by omega)
        (hrc.mono (ext_w.trans ext_push)) hty' hsc' hef hlf hg2 hB_open ev_rec
      refine ⟨ℓ, hℓ, fun bs s hst => ?_⟩
      cases E with
      | forallE dom₀ bo₀ m₀ =>
        obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (hrigid rfl)
        simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
        obtain ⟨⟨bs₁, body₁⟩, hst₁, hst⟩ := hst
        simp only [Prod.mk.injEq] at hst
        obtain ⟨rfl, rfl⟩ := hst
        obtain ⟨bs₂, hst₂⟩ := stripPis_instantiate1_sort m (v := .fvar d T) (k := 0) hst₁
        exact htele bs₂ s hst₂
      | _ => simp [Expr.stripPis] at hst

/-- **The result sort of the shape stage at any scoped context** whose load contract and
environment facts hold and which allows the result-sort run's children. -/
theorem NativeShapeCalls.resultSort_staged {c : ScopedCtx}
    {rc typePtr blockArg index safety : SourceValue F}
    {params indices count levels : Nat} {initial : Heap F} {calls : List (Call F)}
    (shape : NativeShapeCalls rc typePtr blockArg index safety params indices count levels initial
      calls)
    {type : KExpr} (bound : params + indices < 18446744069414584321)
    (roles : RCRep c.t c.lim initial rc)
    (represented : Tm c.κ 0 (fun _ => default) initial 0 type typePtr)
    (facts : CoreEnvFacts c.toCtx) (good : CoreGood c shape.sortCalls)
    (loads : ScopedLoadFacts c) :
    ∃ level : KLevel, RepKLevel shape.ctorBefore level shape.sortLevel ∧
      ∀ binders sort, type.stripPis (params + indices) = some (binders, .sort sort) →
        LvEq sort level := by
  have types : TypesRep c.κ (fun _ => default) shape.sortBefore 0
      (.ptr (.enum kexprListEnum) initial.length) := by
    rw [shape.nilTypes]
    exact typesRep_alloc_nil c.κ (fun _ => default) initial
  obtain ⟨level, levelRep, sameSort⟩ := get_result_sort_level_staged_bounded_spec
    (c := c) (params + indices) bound
    (roles.mono shape.initial_to_sort) types (ghostScoped_zero _) facts loads good
    (represented.mono shape.initial_to_sort) shape.sortRun
  exact ⟨level, repKLevel_heapMono₂
    (shape.guardRun.heap_extends.trans shape.guardToCtors) levelRep, sameSort⟩

/-! ## Parameter agreement -/

private theorem check_param_agreement_go_staged_spec {c : ScopedCtx} :
    ∀ (m : Nat) {d : Nat} {Γ : Nat → KExpr} {tfvs_pre : List KExpr}
      {ta_open tb_raw : KExpr} {rc pta ptb types r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      d + m < 144115188075855872 →
      tfvs_pre.length = d →
      (∀ v ∈ tfvs_pre, ∃ q ty, v = .fvar q ty) →
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h d types →
      GhostScoped Γ d →
      CoreEnvFacts c.toCtx →
      ScopedLoadFacts c →
      CoreGood c cs →
      Tm c.κ d Γ h 0 ta_open pta →
      Tm c.κ d Γ h 0 (instOpen tfvs_pre 0 tb_raw) ptb →
      ObsFn W "KernelCheck::check_param_agreement_go"
        [rc, pta, ptb, .field (m : F), types] h r h' cs →
      ∃ (tfvs_suf : List KExpr) (trest : KExpr)
        (cbs_suf : List (KExpr × Ix.Kernel.BinderMeta)) (cbody : KExpr),
        Ix.Kernel.openPisAtFvars m ta_open d = some (tfvs_suf, trest) ∧
        tb_raw.stripPis m = some (cbs_suf, cbody) ∧
        ∀ k < m, ∃ fv,
          tfvs_suf[k]? = some fv ∧
          DefEq c.env (d + k) fv.fvarTypeD
            (instOpen ((tfvs_pre ++ tfvs_suf).take (d + k)) 0 (cbs_suf.getD k default).1)
  | 0, _, _, _, ta_open, tb_raw, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ev => by
    match Obs.«KernelCheck::check_param_agreement_go».obs ev with
    | .n0 .. =>
      exact ⟨[], ta_open, [], tb_raw, rfl, rfl, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
    | .other (hne20 := hne) .. =>
      exact absurd rfl hne
  | m + 1, d, Γ, tfvs_pre, ta_open, tb_raw, rc, pta, ptb, types, r, h, h', cs,
      hdm, hlen, hvs_pre, hrc, hty, hsc, hef, hlf, hgood, hta, htb, ev => by
    match Obs.«KernelCheck::check_param_agreement_go».obs ev with
    | .n0 (hv14 := hv0) .. =>
      exact absurd hv0 (succ_field_ne_zero_bounded (by omega))
    | .other (x_da := xda) (x_ba := xba) (w43 := w43) (x_db := xdb) (x_bb := xbb)
        (w78 := w78) (v94 := v94) (m95 := m95) (cs105 := cs_de) (m168 := m168)
        (cs201 := cs_go) (v207 := v207) (ld35 := ld_a) (ld70 := ld_b)
        (ev107 := ev_de) (heq166 := hv94) (hm178 := hm168) (op243 := op_sub)
        (ev203 := ev_go) (hc252 := hc) .. =>
      subst hc hv94
      obtain ⟨Da, Ba, ℓa, rfl, hDa, hBa, _⟩ := hta.forallE_of_load ld_a
      obtain ⟨Db, Bb, ℓb, heq_tb, hDb, hBb, _⟩ := htb.forallE_of_load ld_b
      obtain ⟨db_raw, bb_raw, rfl, hDb_eq, hBb_eq⟩ := instOpen_forallE_inv hvs_pre heq_tb
      have hg_de : CoreGood c cs_de := hgood.sub (fun x hx => by simp [hx])
      have hg_go : CoreGood c cs_go := hgood.sub (fun x hx => by simp [hx])
      have hde : DefEq c.env d Da Db :=
        scoped_core_defeq hrc hty hsc hef hlf hg_de ev_de hDa hDb
      have ext_de := ev_de.heap_extends
      obtain ⟨ext_cons, hty', hsc'⟩ :=
        push_binder_types (hDa.mono ext_de) (hty.mono ext_de) hsc
      rw [← hm168] at ext_cons hty'
      have ext_all := ext_de.trans ext_cons
      let fv := Expr.fvar (md := .anon) d Da
      let Γ' := Ghost.extend Γ d Da
      have hBa_open : Tm c.κ (d + 1) Γ' m168 0 (Ba.instantiate1 fv) xba :=
        Tm.open_body (Ghost.extend_at Γ d Da) (Ghost.extend_below Γ d Da) (hBa.mono ext_all)
      have hBb_open₀ : Tm c.κ (d + 1) Γ' m168 0 (Bb.instantiate1 fv) xbb :=
        Tm.open_body (Ghost.extend_at Γ d Da) (Ghost.extend_below Γ d Da) (hBb.mono ext_all)
      have hBb_eq' : Bb.instantiate1 fv = instOpen (tfvs_pre ++ [fv]) 0 bb_raw := by
        rw [hBb_eq, instOpen_append]
        rfl
      rw [hBb_eq'] at hBb_open₀
      rw [evalBinOp_sub_succ m op_sub] at ev_go
      have hlen' : (tfvs_pre ++ [fv]).length = d + 1 := by simp [hlen]
      have hvs' : ∀ v ∈ tfvs_pre ++ [fv], ∃ q ty, v = .fvar q ty := by
        intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · exact hvs_pre v hv
        · simp only [List.mem_singleton] at hv
          exact ⟨d, Da, hv⟩
      obtain ⟨tfvs_suf, trest, cbs_suf, cbody, hop_suf, hst_suf, hdoms_suf⟩ :=
        check_param_agreement_go_staged_spec m (by omega) hlen' hvs'
          (hrc.mono ext_all) hty' hsc' hef hlf hg_go hBa_open hBb_open₀ ev_go
      refine ⟨fv :: tfvs_suf, trest, (db_raw, bmeta ℓb) :: cbs_suf, cbody, ?_, ?_, ?_⟩
      · simp [Ix.Kernel.openPisAtFvars, fv, hop_suf]
      · simp [Expr.stripPis, hst_suf]
      · intro k hk
        cases k with
        | zero =>
          refine ⟨fv, rfl, ?_⟩
          have htake : (tfvs_pre ++ fv :: tfvs_suf).take d = tfvs_pre :=
            List.take_left' hlen
          rw [Nat.add_zero, htake]
          simpa [fv, Expr.fvarTypeD, hDb_eq] using hde
        | succ k' =>
          obtain ⟨fv', hfv', hde'⟩ := hdoms_suf k' (by omega)
          refine ⟨fv', hfv', ?_⟩
          have happ : (tfvs_pre ++ [fv]) ++ tfvs_suf = tfvs_pre ++ fv :: tfvs_suf := by
            simp
          rw [happ, show d + 1 + k' = d + (k' + 1) by omega] at hde'
          exact hde'

/-- At any scoped context: `check_param_agreement` establishes `StructDomsShared c.env ta tb n`. -/
theorem check_param_agreement_staged_spec {c : ScopedCtx}
    {Γ : Nat → KExpr} {ta tb : KExpr} {n : Nat}
    {rc pta ptb r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hn : n < 144115188075855872)
    (hrc : RCRep c.t c.lim h rc)
    (hef : CoreEnvFacts c.toCtx)
    (hlf : ScopedLoadFacts c)
    (hgood : CoreGood c cs)
    (hta : Tm c.κ 0 Γ h 0 ta pta)
    (htb : Tm c.κ 0 Γ h 0 tb ptb)
    (ev : ObsFn W "KernelCheck::check_param_agreement" [rc, pta, ptb, .field (n : F)] h r h' cs) :
    StructDomsShared c.env ta tb n := by
  match Obs.«KernelCheck::check_param_agreement».obs ev with
  | .run (cs4 := cs_go) (m41 := m41) (hm49 := hm41) (ev6 := ev_go) (hc53 := hc) =>
    subst hc
    have ext : Heap.Extends h m41 := by rw [hm41]; exact Heap.Extends.snoc h _
    have hty : TypesRep c.κ Γ m41 0 (.ptr (.enum kexprListEnum) h.length) := by
      rw [hm41]; exact typesRep_alloc_nil c.κ Γ h
    have hg_go : CoreGood c cs_go := hgood.sub (fun x hx => by simp [hx])
    obtain ⟨tfvs, trest, cbs, cbody, hop, hst, hdoms⟩ :=
      check_param_agreement_go_staged_spec n (d := 0) (tfvs_pre := []) (tb_raw := tb)
        (by omega) rfl (fun _ hv => nomatch hv) (hrc.mono ext) hty (ghostScoped_zero Γ)
        hef hlf hg_go (hta.mono ext) (htb.mono ext) ev_go
    refine ⟨tfvs, trest, hop, fun i hi => ?_⟩
    obtain ⟨fv, hfv, hde⟩ := hdoms i hi
    rw [Nat.zero_add, List.nil_append] at hde
    exact ⟨cbs, cbody, fv, hst, hfv, hde⟩

/-! ## Field universes -/

private theorem check_field_universes_skip_params_staged_spec {c : ScopedCtx} :
    ∀ (m : Nat) {d : Nat} {Γ : Nat → KExpr} {nF : Nat}
      {cty_open : KExpr} {rc pcty pind types r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      d + m < 144115188075855872 →
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h d types →
      GhostScoped Γ d →
      Tm c.κ d Γ h 0 cty_open pcty →
      NoTopLetSpine (m + nF) h pcty →
      ObsFn W "KernelCheck::check_field_universes_skip_params"
        [rc, pcty, .field (m : F), pind, types] h r h' cs →
      ∃ (fvsP : List KExpr) (crest : KExpr) (Γ' : Nat → KExpr)
        (pcty' types' : SourceValue F) (h₁ : Heap F) (cs_in : List (Call F)),
        Ix.Kernel.openPisAtFvars m cty_open d = some (fvsP, crest) ∧
        Heap.Extends h h₁ ∧
        (∀ x ∈ cs_in, x ∈ cs) ∧
        RCRep c.t c.lim h₁ rc ∧
        TypesRep c.κ Γ' h₁ (d + m) types' ∧
        GhostScoped Γ' (d + m) ∧
        Tm c.κ (d + m) Γ' h₁ 0 crest pcty' ∧
        NoTopLetSpine nF h₁ pcty' ∧
        ObsFn W "KernelCheck::check_field_universes_inner"
          [rc, pcty', pind, types'] h₁ r h' cs_in
  | 0, d, Γ, nF, cty_open, rc, pcty, pind, types, r, h, h', cs,
      _, hrc, hty, hsc, hcty, hnt, ev => by
    match Obs.«KernelCheck::check_field_universes_skip_params».obs ev with
    | .n0 (cs18 := cs_in) (ev20 := ev_in) (hc53 := hc) .. =>
      subst hc
      rw [Nat.zero_add] at hnt
      rw [Nat.add_zero]
      exact ⟨[], cty_open, Γ, pcty, types, h, cs_in, rfl, Heap.Extends.refl h,
        (fun x hx => by simp [hx]), hrc, hty, hsc, hcty, hnt, ev_in⟩
    | .other (hne54 := hne) .. =>
      exact absurd rfl hne
  | m + 1, d, Γ, nF, cty_open, rc, pcty, pind, types, r, h, h', cs,
      hdm, hrc, hty, hsc, hcty, hnt, ev => by
    match Obs.«KernelCheck::check_field_universes_skip_params».obs ev with
    | .n0 (hv14 := hv0) .. =>
      exact absurd hv0 (succ_field_ne_zero_bounded (by omega))
    | .other (x_dom := xdom) (x_body := xbody) (w77 := w77) (cs96 := cs96)
        (v101 := v101) (m141 := m141) (ld69 := ld) (op131 := op_sub)
        (hm149 := hm141) (ev98 := ev_rec) (hc169 := hc) .. =>
      subst hc
      obtain ⟨D, B, ℓ, rfl, hD, hB, _⟩ := hcty.forallE_of_load ld
      rw [show m + 1 + nF = (m + nF) + 1 by omega] at hnt
      obtain ⟨_, bp, _, hv_nt, hnt_B⟩ := hnt.succ_forall ld
      injection hv_nt with _ _ hxs_nt; injection hxs_nt with _ hxs_nt
      injection hxs_nt with hxb_nt _; subst hxb_nt
      obtain ⟨ext_cons, hty', hsc'⟩ := push_binder_types hD hty hsc
      rw [← hm141] at ext_cons hty'
      let fv := Expr.fvar (md := .anon) d D
      let Γ₁ := Ghost.extend Γ d D
      have hB_open : Tm c.κ (d + 1) Γ₁ m141 0 (B.instantiate1 fv) xbody :=
        Tm.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D) (hB.mono ext_cons)
      rw [evalBinOp_sub_succ m op_sub] at ev_rec
      obtain ⟨fvsP', crest, Γ', pcty', types', h₁, cs_in, hop', ext', hsub',
          hrc', hty'', hsc'', hcrest, hnt', ev_in⟩ :=
        check_field_universes_skip_params_staged_spec m (d := d + 1) (by omega)
          (hrc.mono ext_cons) hty' hsc' hB_open (hnt_B.mono ext_cons) ev_rec
      rw [show d + 1 + m = d + (m + 1) by omega] at hty'' hsc'' hcrest
      refine ⟨fv :: fvsP', crest, Γ', pcty', types', h₁, cs_in, ?_, ext_cons.trans ext',
        (fun x hx => by simp [hsub' x hx]), hrc', hty'', hsc'', hcrest, hnt', ev_in⟩
      simp [Ix.Kernel.openPisAtFvars, fv, hop']

private theorem check_field_universes_inner_staged_spec (hLevels : IxVM.Consistency.Levels)
    {c : ScopedCtx} {T : KKey} {us : List KLevel}
    {resSort ind_lvl : KLevel} (hlveq : LvEq resSort ind_lvl) :
    ∀ (m : Nat) {d : Nat} {Γ : Nat → KExpr} {crest : KExpr} {xFvs args : List KExpr}
      {rc pty pind types r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      Ix.Kernel.openPisAtFvars m crest d = some (xFvs, Expr.mkAppN (.const T us) args) →
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h d types →
      GhostScoped Γ d →
      CoreEnvFacts c.toCtx →
      ScopedLoadFacts c →
      CoreGood c cs →
      RepKLevel h ind_lvl pind →
      Tm c.κ d Γ h 0 crest pty →
      NoTopLetSpine m h pty →
      ObsFn W "KernelCheck::check_field_universes_inner" [rc, pty, pind, types] h r h' cs →
      ∃ sorts : List KLevel,
        sorts.length = m ∧
        ∀ i < m, ∃ fv ty u,
          xFvs[i]? = some fv ∧ sorts[i]? = some u ∧
          Infer c.env .full (d + i) fv.fvarTypeD ty ∧
          Red c.env (d + i) ty (.sort u) ∧
          (∀ φ, Level.eval φ u ≤ Level.eval φ resSort)
  | 0, d, Γ, crest, xFvs, args, rc, pty, pind, types, r, h, h', cs,
      hop, _, _, _, _, _, _, _, hpty, _, ev => by
    simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    match Obs.«KernelCheck::check_field_universes_inner».obs ev with
    | .other .. =>
      exact ⟨[], rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
    | .Forall (ld12 := ld) .. =>
      obtain ⟨D, B, ℓ, heq, _⟩ := hpty.forallE_of_load ld
      exact absurd heq (mkAppN_const_not_forallE T us args D B (bmeta ℓ))
  | m + 1, d, Γ, crest, xFvs, args, rc, pty, pind, types, r, h, h', cs,
      hop, hrc, hty, hsc, hef, hlf, hgood, hpind, hpty, hnt, ev => by
    match Obs.«KernelCheck::check_field_universes_inner».obs ev with
    | .other (ld12 := ld) (hne183 := hne) .. =>
      exact (hnt.succ_not_other ld hne).elim
    | .Forall (x_dom := xdom) (x_body := xbody) (w20 := w20) (v36 := v36) (m37 := m37)
        (cs47 := cs_es) (v85 := v85) (m88 := m88) (cs96 := cs_leq) (cs125 := cs_in)
        (m154 := m154) (ld12 := ld) (ev49 := ev_es) (ev98 := ev_leq) (heq121 := hv85)
        (hm162 := hm154) (ev127 := ev_in) (hc182 := hc) =>
      subst hc hv85
      obtain ⟨D, B, ℓ, rfl, hD, hB, _⟩ := hpty.forallE_of_load ld
      simp only [Ix.Kernel.openPisAtFvars] at hop
      rcases hop' : Ix.Kernel.openPisAtFvars m (B.instantiate1 (.fvar d D)) (d + 1) with
        _ | ⟨xFvs', o'⟩ <;> rw [hop'] at hop
      · exact nomatch hop
      · simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        have hg_es : CoreGood c cs_es := hgood.sub (fun x hx => by simp [hx])
        have hg_leq : CoreGood c cs_leq := hgood.sub (fun x hx => by simp [hx])
        have hg_in : CoreGood c cs_in := hgood.sub (fun x hx => by simp [hx])
        obtain ⟨sdom, u₀, ℓ_dom, hinf_d, hred_d, hrep_dom, hlveq_dom⟩ :=
          scoped_core_ensure_sort hrc hty hsc hef hlf hg_es ev_es hD
        have e1 := ev_es.heap_extends
        have e2 := ev_leq.heap_extends
        have hleq_lvl := levels_leq_one hLevels ev_leq hg_leq.2 hrep_dom
          (repKLevel_heapMono₂ e1 hpind)
        have hleq_u : ∀ φ, Level.eval φ u₀ ≤ Level.eval φ resSort := by
          intro φ
          rw [hlveq_dom φ, hlveq φ]
          exact hleq_lvl φ
        obtain ⟨ext_cons, hty', hsc'⟩ :=
          push_binder_types (hD.mono (e1.trans e2)) (hty.mono (e1.trans e2)) hsc
        rw [← hm154] at ext_cons hty'
        have ext_all := e1.trans (e2.trans ext_cons)
        let fv := Expr.fvar (md := .anon) d D
        let Γ' := Ghost.extend Γ d D
        have hB_open : Tm c.κ (d + 1) Γ' m154 0 (B.instantiate1 fv) xbody :=
          Tm.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D) (hB.mono ext_all)
        obtain ⟨_, bp, _, hv_nt, hnt_B₀⟩ := hnt.succ_forall ld
        injection hv_nt with _ _ hxs_nt; injection hxs_nt with _ hxs_nt
        injection hxs_nt with hxb_nt _; subst hxb_nt
        have hnt_B : NoTopLetSpine m m154 xbody := hnt_B₀.mono ext_all
        obtain ⟨sorts', hlen', hsorts'⟩ :=
          check_field_universes_inner_staged_spec hLevels hlveq m hop'
            (hrc.mono ext_all) hty' hsc' hef hlf hg_in
            (repKLevel_heapMono₂ ext_all hpind) hB_open hnt_B ev_in
        refine ⟨u₀ :: sorts', by simp [hlen'], fun i hi => ?_⟩
        cases i with
        | zero =>
          rw [Nat.add_zero]
          exact ⟨fv, sdom, u₀, rfl, rfl, hinf_d, hred_d, hleq_u⟩
        | succ i' =>
          obtain ⟨fv', ty', u', hfv', hu', hinf', hred', hleq'⟩ := hsorts' i' (by omega)
          rw [show d + 1 + i' = d + (i' + 1) by omega] at hinf' hred'
          exact ⟨fv', ty', u', hfv', hu', hinf', hred', hleq'⟩

/-- `check_field_universes` establishes `FieldSortsJ rulesJ c.env (Level.isEquiv resSort .zero) false`
for constructor fields `xFvs` at `large = false`. -/
theorem check_field_universes_staged_spec (hLevels : IxVM.Consistency.Levels)
    {c : ScopedCtx} {T : KKey} {us : List KLevel}
    {resSort ind_lvl : KLevel} {nP nF : Nat} {Γ : Nat → KExpr}
    {cty stype_cty crest : KExpr} {fvsP xFvs idxArgs : List KExpr}
    {rc pcty pind r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hnP : nP < 144115188075855872)
    (hlveq : LvEq resSort ind_lvl)
    (hinf_cty : Infer c.env .full 0 cty stype_cty)
    (hopP : Ix.Kernel.openPisAtFvars nP cty 0 = some (fvsP, crest))
    (hopF : Ix.Kernel.openPisAtFvars nF crest nP =
      some (xFvs, Expr.mkAppN (.const T us) (fvsP ++ idxArgs)))
    (hopAll : Ix.Kernel.openPisAtFvars (nP + nF) cty 0 =
      some (fvsP ++ xFvs, Expr.mkAppN (.const T us) (fvsP ++ idxArgs)))
    (hrc : RCRep c.t c.lim h rc)
    (hef : CoreEnvFacts c.toCtx)
    (hlf : ScopedLoadFacts c)
    (hgood : CoreGood c cs)
    (hpind : RepKLevel h ind_lvl pind)
    (hcty : Tm c.κ 0 Γ h 0 cty pcty)
    (hnt : NoTopLetSpine (nP + nF) h pcty)
    (ev : ObsFn W "KernelCheck::check_field_universes"
      [rc, pcty, .field (nP : F), pind] h r h' cs) :
    ∃ sorts : List KLevel,
      FieldSortsJ rulesJ c.env (Level.isEquiv resSort .zero == some true) false resSort
        nP xFvs idxArgs nF sorts := by
  match Obs.«KernelCheck::check_field_universes».obs ev with
  | .Zero (ld12 := ld_zero) .. =>
    have hind_zero : ind_lvl = .zero := by
      cases hpind with
      | zero _ => rfl
      | succ cell _ | max cell _ _ | imax cell _ _ | param _ cell =>
        exact (load_cell_ne cell ld_zero (by decide)).elim
    subst hind_zero
    have hisProp : (Level.isEquiv resSort .zero == some true) = true :=
      isEquiv_zero_of_eval_zero (fun φ => hlveq φ)
    have hfvsP_len : fvsP.length = nP := openPisAtFvars_len nP hopP
    have hall := infer_openPisAtFvars_sorts (nP + nF) hinf_cty hopAll
    have hfield : ∀ i : Fin nF, ∃ fv sdom u,
        xFvs[i.1]? = some fv ∧
        Infer c.env .full (nP + i.1) fv.fvarTypeD sdom ∧
        Red c.env (nP + i.1) sdom (.sort u) := by
      intro ⟨i, hi⟩
      obtain ⟨fv, sdom, u, hfv, hinf, hred⟩ := hall (nP + i) (by omega)
      rw [Nat.zero_add] at hinf hred
      rw [List.getElem?_append_right (by omega), hfvsP_len, Nat.add_sub_cancel_left] at hfv
      exact ⟨fv, sdom, u, hfv, hinf, hred⟩
    let sorts : List KLevel := (List.finRange nF).map fun i =>
      Classical.choose (Classical.choose_spec (Classical.choose_spec (hfield i)))
    refine ⟨sorts, by simp [sorts], fun i hi => ?_⟩
    let fi : Fin nF := ⟨i, hi⟩
    have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hfield fi)))
    have hs_get : sorts[i]? =
        some (Classical.choose (Classical.choose_spec (Classical.choose_spec (hfield fi)))) := by
      rw [List.getElem?_eq_getElem (by simp [sorts]; exact hi)]
      simp [sorts, fi]
    exact ⟨_, _, _, hspec.1, hs_get, hspec.2.1, hspec.2.2,
      (fun hfalse => by rw [hisProp] at hfalse; exact nomatch hfalse),
      (fun _ hlarge => nomatch hlarge)⟩
  | .other (cs32 := cs_sk) (m69 := m69) (hm77 := hm69) (ev34 := ev_sk) (hc81 := hc) .. =>
    subst hc
    have ext : Heap.Extends h m69 := by rw [hm69]; exact Heap.Extends.snoc h _
    have hty : TypesRep c.κ Γ m69 0 (.ptr (.enum kexprListEnum) h.length) := by
      rw [hm69]; exact typesRep_alloc_nil c.κ Γ h
    have hg_sk : CoreGood c cs_sk := hgood.sub (fun x hx => by simp [hx])
    obtain ⟨fvsP', crest', Γ', pcty', types', h₁, cs_in, hopP', ext', hsub',
        hrc', hty', hsc', hcrest', hnt', ev_in⟩ :=
      check_field_universes_skip_params_staged_spec (c := c) nP (d := 0) (by omega)
        (hrc.mono ext) hty (ghostScoped_zero Γ) (hcty.mono ext) (hnt.mono ext) ev_sk
    rw [Nat.zero_add] at hty' hsc' hcrest'
    rw [hopP] at hopP'
    simp only [Option.some.injEq, Prod.mk.injEq] at hopP'
    obtain ⟨rfl, rfl⟩ := hopP'
    obtain ⟨sorts, hlen, hsorts⟩ :=
      check_field_universes_inner_staged_spec hLevels hlveq nF hopF
        hrc' hty' hsc' hef hlf (hg_sk.sub hsub')
        (repKLevel_heapMono₂ (ext.trans ext') hpind) hcrest' hnt' ev_in
    refine ⟨sorts, hlen, fun i hi => ?_⟩
    obtain ⟨fv, ty, u, hfv, hu, hinf, hred, hleq⟩ := hsorts i hi
    exact ⟨fv, ty, u, hfv, hu, hinf, hred, (fun _ => hleq), (fun _ hlarge => nomatch hlarge)⟩

end IxVM.Refinement.Decl
