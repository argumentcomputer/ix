import IxVMRefinement.Decl.ModeledTele

/-! # The telescope checks of a modeled family's rules, on the scoped core

`check_iota_rule` and the member checks of a modeled family call four telescope helpers whose
every typing and conversion is a call of the core: `defeq_list_ok` (pairwise conversion),
`inst_params_typed` (each parameter typed against the domain it instantiates), `defeq_tele`
(the domains of two Π-telescopes convert) and `defeq_lam_tele` (a λ-telescope's domains convert
with a Π-telescope's). Their specifications in `Decl/ModeledTele.lean` read the core through the
public `Core S₀` and an unrestricted context. The specifications below are the same walks at a
scoped context (`ScopedCtx`), every core call read by the scoped registry (`scoped_core_defeq`,
`scoped_core_infer`) under `CoreEnvFacts`, `ScopedLoadFacts` and `CoreGood`; the store's closure
comes from `CoreEnvFacts`.

* `defeq_list_ok_scoped_spec`, `inst_params_typed_scoped_spec`, `defeq_tele_scoped_spec`,
  `defeq_lam_tele_scoped_spec`;
* `rawDefEqList_rulesJ`, `rawTypedList_rulesJ`: the raw lists they conclude are the lists of the
  derivation package `rulesJ` (`DefEqListJ`, `TypedListJ`), the form IxC's records state.

Provenance: the four proofs are those of `defeq_list_ok_spec`, `inst_params_typed_spec`,
`defeq_tele_spec`, `defeq_lam_tele_spec` (`Decl/ModeledTele.lean:3081-3771`) with `core_defeq`/
`core_infer` replaced by their scoped counterparts. -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.Core.Specs.Subst (IdxAll IdxLt NoIdx NoIdxF BVarIm idxBound)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (Expr Level LevelParam ConstantVal ConstantInfo Declaration RecRule IndCaps EnvExt)
open Ix.Kernel.Rules (Annot Red DefEq Infer)
open Ix.Kernel.Semantics (Judgements DefEqListJ TypedListJ)
open Ix.Kernel.Model (rulesJ)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

local macro "fam_sub_calls" : term =>
  `(fun _ hx => by simp [hx])

/-! ## The raw lists are the derivation package's -/

/-- A raw conversion list is a conversion list of the derivation package. -/
theorem rawDefEqList_rulesJ {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ {as bs : List KExpr}, RawDefEqList env d as bs → DefEqListJ rulesJ env d as bs
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h0, hrest⟩ => ⟨h0, rawDefEqList_rulesJ hrest⟩
  | [], _ :: _, h | _ :: _, [], h => nomatch h

/-- A raw typed list is a typed list of the derivation package. -/
theorem rawTypedList_rulesJ {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ {as bs : List KExpr}, RawTypedList env d as bs → TypedListJ rulesJ env d as bs
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨⟨ty, hinf, hde⟩, hrest⟩ => ⟨⟨ty, hinf, hde⟩, rawTypedList_rulesJ hrest⟩
  | [], _ :: _, h | _ :: _, [], h => nomatch h

/-! ## `defeq_list_ok` -/

/-- **Pairwise conversion, on the scoped core** (`defeq_list_ok_spec` at a scoped context). -/
theorem defeq_list_ok_scoped_spec {c : ScopedCtx}
    {Γ : Nat → KExpr} {d : Nat} {Xs : List KExpr} :
    ∀ {Ys : List KExpr} {rc xs_ptr ys_ptr types : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h d types →
      GhostScoped Γ d →
      CoreEnvFacts c.toCtx → ScopedLoadFacts c → CoreGood c cs →
      ObsFn W "KernelModeled::defeq_list_ok" [rc, xs_ptr, ys_ptr, types] h (.field 1) h' cs →
      RepList kexprListEnum (fun h X p => Tm c.κ d Γ h 0 X p) h Xs xs_ptr →
      RepList kexprListEnum (fun h Y p => Tm c.κ d Γ h 0 Y p) h Ys ys_ptr →
      RawDefEqList c.env d Xs Ys := by
  induction Xs with
  | nil =>
    intro Ys rc xs_ptr ys_ptr types h h' cs _ _ _ _ _ _ ev hxs hys
    match Obs.«KernelModeled::defeq_list_ok».obs ev with
    | .Nil_Nil (ld31 := ld_y) .. =>
      obtain rfl := Lib.rep_nil_of_load hys ld_y
      trivial
    | .Nil_other (he46 := hr) .. => injection hr with hf; exact absurd hf one_ne_zero
    | .Cons_Nil (ld12 := ld_x) .. | .Cons_Cons_n1 (ld12 := ld_x) ..
    | .Cons_Cons_other (ld12 := ld_x) .. =>
      obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hxs ld_x; cases he
  | cons X Xs ih =>
    intro Ys rc xs_ptr ys_ptr types h h' cs hrc hty hsc hef hlf hgood ev hxs hys
    match Obs.«KernelModeled::defeq_list_ok».obs ev with
    | .Nil_Nil (ld12 := ld_x) .. | .Nil_other (ld12 := ld_x) .. =>
      cases Lib.rep_nil_of_load hxs ld_x
    | .Cons_Nil (he85 := hr) .. | .Cons_Cons_other (he199 := hr) .. =>
      injection hr with hf; exact absurd hf one_ne_zero
    | .Cons_Cons_n1 (ld12 := ld_x) (ld77 := ld_y) (ev119 := ev_de) (ev161 := ev_rec)
        (hc194 := hc) .. =>
      subst hc
      obtain ⟨X', Xs', hx_eq, hX, hXs⟩ := Lib.rep_cons_of_load hxs ld_x
      obtain ⟨Y', Ys', hy_eq, hY, hYs⟩ := Lib.rep_cons_of_load hys ld_y
      injection hx_eq with h1 h2; subst h1 h2
      subst hy_eq
      have hde := scoped_core_defeq hrc hty hsc hef hlf
        (hgood.sub fam_sub_calls) ev_de hX hY
      have ext := ev_de.heap_extends
      refine ⟨hde, ih (hrc.mono ext) (hty.mono ext) hsc hef hlf
        (hgood.sub fun _ hx => by simp [hx]) ev_rec
        (RepLinkedList.mono tmE_heapMono₂ ext hXs)
        (RepLinkedList.mono tmE_heapMono₂ ext hYs)⟩

/-! ## `inst_params_typed` -/

/-- **Parameters typed against the domains they instantiate, on the scoped core**
(`inst_params_typed_spec` at a scoped context). -/
theorem inst_params_typed_scoped_spec {c : ScopedCtx}
    {Γ₁ Γ₂ : Nat → KExpr} {d₁ d₂ depth : Nat} (hle : d₁ ≤ depth) {Ps₁ : List KExpr} :
    ∀ {Ps₂ : List KExpr} {E₁ E₂ : KExpr} {rc e ps_ptr ctx r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ₁ h d₁ ctx →
      GhostScoped Γ₁ d₁ →
      CoreEnvFacts c.toCtx → ScopedLoadFacts c → CoreGood c cs →
      ObsFn W "KernelModeled::inst_params_typed" [rc, e, ps_ptr, ctx] h r h' cs →
      Tm c.κ d₁ Γ₁ h 0 E₁ e →
      Tm c.κ d₂ Γ₂ h 0 E₂ e →
      RepList kexprListEnum (fun h P p => Tm c.κ d₁ Γ₁ h 0 P p) h Ps₁ ps_ptr →
      RepList kexprListEnum (fun h P p => Tm c.κ d₂ Γ₂ h 0 P p) h Ps₂ ps_ptr →
      ∃ doms₁ rem₁ doms₂ rem₂,
        Expr.instPisAt Ps₁ E₁ = some (doms₁, rem₁) ∧
        Expr.instPisAt Ps₂ E₂ = some (doms₂, rem₂) ∧
        Tm c.κ d₁ Γ₁ h' 0 rem₁ r ∧
        Tm c.κ d₂ Γ₂ h' 0 rem₂ r ∧
        RawTypedList c.env depth Ps₁ doms₁ := by
  induction Ps₁ with
  | nil =>
    intro Ps₂ E₁ E₂ rc e ps_ptr ctx r h h' cs _ _ _ _ _ _ ev hE₁ hE₂ hps₁ hps₂
    match Obs.«KernelModeled::inst_params_typed».obs ev with
    | .Nil (ld12 := ld) (he21 := hr) (he22 := hh) .. =>
      subst hr hh
      obtain rfl := Lib.rep_nil_of_load hps₂ ld
      exact ⟨[], E₁, [], E₂, rfl, rfl, hE₁, hE₂, trivial⟩
    | .Cons (ld12 := ld) .. => obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hps₁ ld; cases he
  | cons P₁ Ps₁ ih =>
    intro Ps₂ E₁ E₂ rc e ps_ptr ctx r h h' cs hrc hty hsc hef hlf hgood ev hE₁ hE₂ hps₁ hps₂
    match Obs.«KernelModeled::inst_params_typed».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hps₁ ld
    | .Cons (ld12 := ld) (ld52 := ld_fa) (ev89 := ev_inf) (ev138 := ev_de)
        (heq177 := hv1) (ev206 := ev_inst) (ev183 := ev_rec) (hc244 := hc) .. =>
      subst hc hv1
      obtain ⟨P₁', Ps₁', he₁, hP₁, hPs₁⟩ := Lib.rep_cons_of_load hps₁ ld
      obtain ⟨P₂, Ps₂', he₂, hP₂, hPs₂⟩ := Lib.rep_cons_of_load hps₂ ld
      injection he₁ with h1 h2; subst h1 h2
      subst he₂
      obtain ⟨T₁, B₁, _, rfl, hT₁, hb₁, _⟩ := hE₁.forallE_of_load ld_fa
      obtain ⟨T₂, B₂, _, rfl, _, hb₂, _⟩ := hE₂.forallE_of_load ld_fa
      obtain ⟨tt, htt, hinf⟩ := scoped_core_infer hrc hty hsc hef hlf
        (hgood.sub fam_sub_calls) ev_inf hP₁
      have e_inf := ev_inf.heap_extends
      have hde := scoped_core_defeq (hrc.mono e_inf) (hty.mono e_inf) hsc hef hlf
        (hgood.sub fun _ hx => by simp [hx]) ev_de htt (hT₁.mono e_inf)
      have hinf_d := infer_lift_to hef.storeClosed hle hsc hP₁ htt hinf
      have hde_d := defEq_lift_to hef.storeClosed hle hsc htt (hT₁.mono e_inf) hde
      have e_de := e_inf.trans ev_de.heap_extends
      have hinst₁ := SubstAux.gall c.κ .expr_inst1 _ _ _ _ _ ev_inst _ _ _ rfl
        (bounded_sub (fun _ hx => by simp [hx]) hgood.bounded) d₁ Γ₁ B₁ P₁
        (by simpa [ZMod.val_zero] using hb₁.mono e_de) (hP₁.mono e_de)
      have hinst₂ := SubstAux.gall c.κ .expr_inst1 _ _ _ _ _ ev_inst _ _ _ rfl
        (bounded_sub (fun _ hx => by simp [hx]) hgood.bounded) d₂ Γ₂ B₂ P₂
        (by simpa [ZMod.val_zero] using hb₂.mono e_de) (hP₂.mono e_de)
      simp only [ZMod.val_zero] at hinst₁ hinst₂
      have e_all := e_de.trans ev_inst.heap_extends
      obtain ⟨ds₁, rem₁, ds₂, rem₂, hds₁, hds₂, hrem₁, hrem₂, htyped⟩ :=
        ih (hrc.mono e_all) (hty.mono e_all) hsc hef hlf
          (hgood.sub fun _ hx => by simp [hx]) ev_rec hinst₁ hinst₂
          (RepLinkedList.mono tmE_heapMono₂ e_all hPs₁)
          (RepLinkedList.mono tmE_heapMono₂ e_all hPs₂)
      exact ⟨T₁ :: ds₁, rem₁, T₂ :: ds₂, rem₂,
        by simp [Expr.instPisAt, hds₁], by simp [Expr.instPisAt, hds₂],
        hrem₁, hrem₂, ⟨⟨tt, hinf_d, hde_d⟩, htyped⟩⟩

/-! ## `defeq_tele` -/

/-- **Two Π-telescopes' domains convert, on the scoped core** (`defeq_tele_spec` at a scoped
context). -/
theorem defeq_tele_scoped_spec {c : ScopedCtx} (m : Nat) :
    ∀ {Γ : Nat → KExpr} {d depth : Nat} {Ea Eb : KExpr}
      {rc a b ctx r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val n = m →
      d + m ≤ depth →
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h d ctx →
      GhostScoped Γ d →
      CoreEnvFacts c.toCtx → ScopedLoadFacts c → CoreGood c cs →
      ObsFn W "KernelModeled::defeq_tele" [rc, a, b, .field n, ctx] h r h' cs →
      TmExact c.κ d Γ h 0 Ea a →
      Tm c.κ d Γ h 0 Eb b →
      ∃ fvs remA domsB remB,
        Ix.Kernel.openPisAtFvars m Ea d = some (fvs, remA) ∧
        Expr.instPisAt fvs Eb = some (domsB, remB) ∧
        RawDefEqList c.env depth (fvs.map Expr.fvarTypeD) domsB := by
  induction m with
  | zero =>
    intro Γ d depth Ea Eb rc a b ctx r n h h' cs hm _ _ _ _ _ _ _ ev _ _
    match Obs.«KernelModeled::defeq_tele».obs ev with
    | .n0 .. => exact ⟨[], Ea, [], Eb, rfl, rfl, trivial⟩
    | .other (hne20 := hne) .. =>
      have := Lib.val_sub_one (fun (e : n = 0) => hne (by rw [e])); omega
  | succ m ih =>
    intro Γ d depth Ea Eb rc a b ctx r n h h' cs hm hle hrc hty hsc hef hlf hgood ev hEa hEb
    match Obs.«KernelModeled::defeq_tele».obs ev with
    | .n0 (hv14 := hv) .. => injection hv with hn; subst hn; simp at hm
    | .other (x_da := xda) (x_ba := xba) (x_db := xdb) (x_bb := xbb) (m108 := m108)
        (hne20 := hne) (ld35 := ld_a) (ld70 := ld_b) (ev118 := ev_de) (heq157 := hv1)
        (op203 := op_sub) (hm214 := hm206) (ev163 := ev_rec) (hc234 := hc) .. =>
      subst hc hv1 hm206
      obtain rfl := Lib.sub_one_inv op_sub
      have hpred := Lib.val_sub_one (fun (e : n = 0) => hne (by rw [e]))
      obtain ⟨Ta, Ba, _, rfl, hTa, hBa, _⟩ := hEa.forallE_of_load ld_a
      obtain ⟨Tb, Bb, _, rfl, hTb, hBb, _⟩ := hEb.forallE_of_load ld_b
      have hde := scoped_core_defeq hrc hty hsc hef hlf
        (hgood.sub fam_sub_calls) ev_de hTa.toTm hTb
      have hde_d := defEq_lift_to (depth := depth) hef.storeClosed (by omega) hsc hTa.toTm hTb
        hde
      have e_de := ev_de.heap_extends
      have ext_cons := Heap.Extends.snoc m108 (.construct kexprListEnum "Cons" [xda, ctx])
      have e_all := e_de.trans ext_cons
      let Γ₁ := Ghost.extend Γ d Ta
      have hBa_open : TmExact c.κ (d + 1) Γ₁
          (m108 ++ [.construct kexprListEnum "Cons" [xda, ctx]]) 0
          (Ba.instantiate1 (.fvar d Ta)) xba :=
        (hBa.mono e_all).open_body (Ghost.extend_at Γ d Ta) (Ghost.extend_below Γ d Ta)
      have hBb_open : Tm c.κ (d + 1) Γ₁
          (m108 ++ [.construct kexprListEnum "Cons" [xda, ctx]]) 0
          (Bb.instantiate1 (.fvar d Ta)) xbb :=
        (hBb.mono e_all).open_body (Ghost.extend_at Γ d Ta) (Ghost.extend_below Γ d Ta)
      have hty₁ := typesRep_snoc_extend (hty.mono e_de) (hTa.toTm.mono e_de)
      have hsc₁ := hsc.extend (Tm.wscopedB hsc hTa.toTm)
      obtain ⟨fvs, remA, domsB, remB, hop, hinst, hlist⟩ :=
        ih (Γ := Γ₁) (d := d + 1) (depth := depth) (n := n - 1) (by omega) (by omega)
          (hrc.mono e_all) hty₁ hsc₁ hef hlf (hgood.sub fun _ hx => by simp [hx])
          ev_rec hBa_open hBb_open
      exact ⟨.fvar d Ta :: fvs, remA, Tb :: domsB, remB,
        by simp [Ix.Kernel.openPisAtFvars, hop],
        by simp [Expr.instPisAt, hinst],
        ⟨hde_d, hlist⟩⟩

/-! ## `defeq_lam_tele` -/

/-- **A λ-telescope's domains convert with a Π-telescope's, on the scoped core**
(`defeq_lam_tele_spec` at a scoped context). -/
theorem defeq_lam_tele_scoped_spec {c : ScopedCtx} (m : Nat) :
    ∀ {Γ : Nat → KExpr} {d depth : Nat} {El Ep : KExpr}
      {rc l p ctx r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val n = m →
      d + m ≤ depth →
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h d ctx →
      GhostScoped Γ d →
      CoreEnvFacts c.toCtx → ScopedLoadFacts c → CoreGood c cs →
      ObsFn W "KernelModeled::defeq_lam_tele" [rc, l, p, .field n, ctx] h r h' cs →
      Tm c.κ d Γ h 0 El l →
      Tm c.κ d Γ h 0 Ep p →
      ∃ r_l r_ctx Γ' lfvs remL domsP remP,
        r = .tuple [r_l, r_ctx] ∧
        openLamsAtFvars m El d = some (lfvs, remL) ∧
        Expr.instPisAt lfvs Ep = some (domsP, remP) ∧
        (∀ j < d, Γ' j = Γ j) ∧
        (∀ k (hk : k < lfvs.length), Γ' (d + k) = lfvs[k].fvarTypeD) ∧
        Tm c.κ (d + m) Γ' h' 0 remL r_l ∧
        TypesRep c.κ Γ' h' (d + m) r_ctx ∧
        GhostScoped Γ' (d + m) ∧
        RawDefEqList c.env depth (lfvs.map Expr.fvarTypeD) domsP := by
  induction m with
  | zero =>
    intro Γ d depth El Ep rc l p ctx r n h h' cs hm _ _ hty hsc _ _ _ ev hEl _
    match Obs.«KernelModeled::defeq_lam_tele».obs ev with
    | .n0 (he19 := hr) (he34 := hh) .. =>
      subst hr hh
      exact ⟨l, ctx, Γ, [], El, [], Ep, rfl, rfl, rfl, fun _ _ => rfl,
        fun _ hk => absurd hk (Nat.not_lt_zero _), by simpa using hEl, by simpa using hty,
        by simpa using hsc, trivial⟩
    | .other (hne36 := hne) .. =>
      have := Lib.val_sub_one (fun (e : n = 0) => hne (by rw [e])); omega
  | succ m ih =>
    intro Γ d depth El Ep rc l p ctx r n h h' cs hm hle hrc hty hsc hef hlf hgood ev hEl hEp
    match Obs.«KernelModeled::defeq_lam_tele».obs ev with
    | .n0 (hv14 := hv) .. => injection hv with hn; subst hn; simp at hm
    | .other (x_dl := xdl) (x_bl := xbl) (x_dp := xdp) (x_bp := xbp) (m124 := m124)
        (hne36 := hne) (ld51 := ld_l) (ld86 := ld_p) (ev134 := ev_de) (heq173 := hv1)
        (op219 := op_sub) (hm230 := hm222) (ev179 := ev_rec) (hc250 := hc) .. =>
      subst hc hv1 hm222
      obtain rfl := Lib.sub_one_inv op_sub
      have hpred := Lib.val_sub_one (fun (e : n = 0) => hne (by rw [e]))
      obtain ⟨Tl, Bl, _, rfl, hTl, hBl, _⟩ := hEl.lam_of_load ld_l
      obtain ⟨Tp, Bp, _, rfl, hTp, hBp, _⟩ := hEp.forallE_of_load ld_p
      have hde := scoped_core_defeq hrc hty hsc hef hlf
        (hgood.sub fam_sub_calls) ev_de hTl hTp
      have hde_d := defEq_lift_to (depth := depth) hef.storeClosed (by omega) hsc hTl hTp hde
      have e_de := ev_de.heap_extends
      have ext_cons := Heap.Extends.snoc m124 (.construct kexprListEnum "Cons" [xdl, ctx])
      have e_all := e_de.trans ext_cons
      let Γ₁ := Ghost.extend Γ d Tl
      have hBl_open : Tm c.κ (d + 1) Γ₁
          (m124 ++ [.construct kexprListEnum "Cons" [xdl, ctx]]) 0
          (Bl.instantiate1 (.fvar d Tl)) xbl :=
        (hBl.mono e_all).open_body (Ghost.extend_at Γ d Tl) (Ghost.extend_below Γ d Tl)
      have hBp_open : Tm c.κ (d + 1) Γ₁
          (m124 ++ [.construct kexprListEnum "Cons" [xdl, ctx]]) 0
          (Bp.instantiate1 (.fvar d Tl)) xbp :=
        (hBp.mono e_all).open_body (Ghost.extend_at Γ d Tl) (Ghost.extend_below Γ d Tl)
      have hty₁ := typesRep_snoc_extend (hty.mono e_de) (hTl.mono e_de)
      have hsc₁ := hsc.extend (Tm.wscopedB hsc hTl)
      obtain ⟨r_l, r_ctx, Γ', lfvs, remL, domsP, remP, hr_eq, hop, hinst, hΓ_lo, hΓ_hi,
          hremL, hty', hsc', hlist⟩ :=
        ih (Γ := Γ₁) (d := d + 1) (depth := depth) (n := n - 1) (by omega) (by omega)
          (hrc.mono e_all) hty₁ hsc₁ hef hlf (hgood.sub fun _ hx => by simp [hx])
          ev_rec hBl_open hBp_open
      rw [show d + 1 + m = d + (m + 1) by omega] at hremL hty' hsc'
      refine ⟨r_l, r_ctx, Γ', .fvar d Tl :: lfvs, remL, Tp :: domsP, remP, hr_eq,
        by simp [openLamsAtFvars, hop],
        by simp [Expr.instPisAt, hinst],
        fun j hj => (hΓ_lo j (by omega)).trans (Ghost.extend_below Γ d Tl j hj),
        ?_, hremL, hty', hsc', ⟨hde_d, hlist⟩⟩
      intro k hk
      cases k with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero, Expr.fvarTypeD]
        exact (hΓ_lo d (by omega)).trans (Ghost.extend_at Γ d Tl)
      | succ k' =>
        have hk' : k' < lfvs.length := by simp at hk; omega
        simpa [Nat.add_assoc, Nat.add_comm 1 k'] using hΓ_hi k' hk'

end IxVM.Refinement.Decl
