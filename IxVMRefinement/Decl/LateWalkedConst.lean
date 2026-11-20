import IxVMRefinement.Decl.DeclWalkedConst

/-! # The declaration step a walked value constant runs

`walkedConst_step` keeps the prefix invariant across a walked definition, theorem or opaque
constant, and forgets the declaration step it built on the way (`DeclRunJ rulesJ (IndRoutesJ
rulesJ env)`). `walkedConst_declRunJ` returns that step: from the same check evidence at the
prefix's keying, either the declaration installs nothing, or the constants it installs are
one declaration step over the derivation package. A clause of the fold that a declaration
step keeps but that does not follow from the stored constant alone (a model of the
environment that also keeps data about earlier constants) is kept along it.

The proof is the first half of each case of `walkedConst_step`; three private helpers of that
module are restated here.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Library Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel.Model
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal Declaration)
open Ix.Kernel.Rules (Annot Red DefEq Infer)

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u

private theorem tm_noLetExpr_w {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p : SourceValue F}
    (hΓ : ∀ j, j < d → noLetExpr (Γ j) = true)
    (rep : Tm κ d Γ h k E p) :
    noLetExpr E = true := by
  induction rep with
  | bvarLocal => rfl
  | @bvarFree k₀ _ i _ _ hk hd =>
    exact hΓ (fvIdx d k₀ (ZMod.val i)) (by unfold fvIdx; omega)
  | sort | const | litNat | litStr => rfl
  | app _ _ _ ihf iha => simp only [noLetExpr, ihf, iha]; rfl
  | lam _ _ _ _ iht ihb | forallE _ _ _ _ iht ihb =>
    simp only [noLetExpr, iht, ihb]; rfl
  | letE _ _ _ _ _ ihv ihb => exact noLetExpr_instShift ihv 0 ihb
  | proj _ _ _ ihe => exact ihe

private theorem tmC_closed_props_w {κ : _root_.Address → KKey} {h : Heap F}
    {e : KExpr} {p : SourceValue F} (rep : TmC κ h e p) :
    noLetExpr e = true ∧ e.hasFvar = false ∧ e.looseBVarsBounded 0 = true ∧
      Annot 0 e e := by
  have h0 : Tm κ 0 (fun _ => .sort .zero) h 0 e p := rep 0 (fun _ => .sort .zero)
  have hnl : noLetExpr e = true :=
    tm_noLetExpr_w (fun _ hlt => absurd hlt (Nat.not_lt_zero _)) h0
  have hfv : e.hasFvar = false := Tm.hasFvar_false h0
  have hbvs : e.looseBVarsBounded 0 = true := Tm.looseBVarsBounded h0
  exact ⟨hnl, hfv, hbvs, annot_refl_of_noLetExpr hnl hfv hbvs 0⟩

private def zeroGhostWalked_w : Nat → KExpr := fun _ => .sort .zero

private theorem typesRep_of_nil_eq_w (κ : _root_.Address → KKey) {m m_pre : Heap F}
    (hm : m = m_pre ++ [.construct kexprListEnum "Nil" []]) :
    TypesRep κ zeroGhostWalked_w m 0 (.ptr (.enum kexprListEnum) m_pre.length) := by
  rw [hm]
  exact typesRep_alloc_nil κ zeroGhostWalked_w m_pre

/-- **The declaration step of a walked value constant**: under the hypotheses of
`walkedConst_step`, the declaration installs nothing, or the constants it installs in front of
the prefix are one step of `DeclRunJ rulesJ (IndRoutesJ rulesJ env)`. -/
theorem walkedConst_declRunJ
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {E_core : Ixon.Env} {order_role : List _root_.Address} {lim : Nat}
    {env : Env .anon} {d d' : Declaration .anon}
    (hinv : PrefixInv.{u} E_core t (some lim) env)
    (hchk : CheckedConstOriginAt (Ctx.stored ⟨E_core, env, t, some lim⟩).κ lim calls t bAddr
      E_core order_role d d')
    (hgood : Good ⟨E_core, env, t, none⟩ calls)
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs d, env.find? ci₀.name = none)
    (hkey : ∀ ci₀ ∈ IxVM.Consistency.installs d, KeyFree ci₀.name)
    (hskipax : ∀ cv, d = .axiomDecl cv →
      cv.name = Ix.Kernel.quotSoundName ∨ IxVM.Consistency.inertKey cv.name = true) :
    IxVM.Consistency.installs d' = [] ∨
      ∃ d₀ : Declaration .anon, DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d₀
        ⟨IxVM.Consistency.installs d' ++ env.consts⟩ := by
  have hbound : IxVM.Consistency.Bounded calls := hgood.2
  cases hchk with
  | @axiomDecl a _ _ nlvls ty₀ ty' _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    let cv₀ : ConstantVal .anon := ⟨keyOf t a, List.range nlvls, ty₀⟩
    have hskip : cv₀.name = Ix.Kernel.quotSoundName ∨
        IxVM.Consistency.inertKey cv₀.name = true := hskipax cv₀ rfl
    have hempty' : IxVM.Consistency.installs
        (.axiomDecl ⟨keyOf t a, List.range nlvls, ty'⟩ : Declaration .anon) = [] :=
      ite_eq_left hskip
    exact Or.inl hempty'
  | @defnDecl a nlvls ty₀ val₀ ty' val' hn m_pre1 m_es m_es' m_pre2 m_kc m_kc'
      x_rc x_ty x_val v_sort r_kc cs_es cs_kc
      hnot_role _ _ hty_def _ hval_def hty_ann hval_ann hty'_def hval'_def
      hm_es hty_tmc_es hrc_es ev_es _ hsub_es
      _ hm_kc hty_tmc_kc hval_tmc_kc hrc_kc ev_kc _ hsub_kc =>
    let cv₀ : ConstantVal .anon := ⟨keyOf t a, List.range nlvls, ty₀⟩
    let cv' : ConstantVal .anon := ⟨keyOf t a, List.range nlvls, ty'⟩
    have hbase : isBaseKey cv₀.name = true := isBaseKey_keyOf t a
    have hfresh_cv : env.find? cv'.name = none :=
      hfresh (.defnInfo cv₀ val₀ hn) (List.mem_singleton.mpr rfl)
    let c : ScopedCtx := Ctx.stored ⟨E_core, env, t, some lim⟩
    have hgood_c : Good c.toCtx calls := hgood
    obtain ⟨hef, hlf⟩ := hinv.scopedCoreFacts
    have hty_tmc_es' : TmC c.κ m_es ty' x_ty := by
      have h := hty_tmc_es
      rwa [posOf_range nlvls ty'] at h
    have hty_tmc_kc' : TmC c.κ m_kc ty' x_ty := by
      have h := hty_tmc_kc
      rwa [posOf_range nlvls ty'] at h
    have hval_tmc_kc' : TmC c.κ m_kc val' x_val := by
      have h := hval_tmc_kc
      rwa [posOf_range nlvls val'] at h
    obtain ⟨_, hty'_nfv, hty'_bvs, hty'_ann⟩ := tmC_closed_props_w hty_tmc_es'
    obtain ⟨_, hval'_nfv, hval'_bvs, hval'_ann⟩ := tmC_closed_props_w hval_tmc_kc'
    obtain ⟨stype, u, _, hinf_ty, hred_ty, _, _⟩ :=
      scoped_core_ensure_sort (c := c) hrc_es.toRCRep (typesRep_of_nil_eq_w c.κ hm_es)
        (ghostScoped_zero zeroGhostWalked_w) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_es) (fun _ _ => trivial)) ev_es
        (hty_tmc_es' 0 zeroGhostWalked_w)
    obtain ⟨vtype, hinf_val, hde_val⟩ :=
      scoped_core_check (c := c) hrc_kc.toRCRep (typesRep_of_nil_eq_w c.κ hm_kc)
        (ghostScoped_zero zeroGhostWalked_w) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_kc) (fun _ _ => trivial)) ev_kc
        (hval_tmc_kc' 0 zeroGhostWalked_w) (hty_tmc_kc' 0 zeroGhostWalked_w)
    have hkf := hkey _ (List.mem_singleton.mpr rfl)
    have hres_name : Ix.Kernel.reservedBasisNames.contains cv'.name = false :=
      hkf.1
    have hnoprj : cv'.name.isProjFnShape = false := isProjFnShape_of_isBaseKey hbase
    have hcv_run : ConstantValRunJ rulesJ env cv' ty' :=
      ⟨by rw [hfresh_cv]; rfl, hres_name, hnoprj, levelParam_nodup_of_nodup List.nodup_range,
        hty'_bvs, hty'_nfv, hty'_ann, hty'_def,
        infer_constsResolve hinf_ty hef.store hty'_nfv, stype, u, hinf_ty, hred_ty⟩
    have hv_run : ValueFrontRunJ rulesJ env cv' val' ty' val' :=
      ⟨hval'_bvs, hval'_nfv, hval'_ann, hval'_def,
        infer_constsResolve hinf_val hef.store hval'_nfv, vtype, hinf_val, hde_val⟩
    have hnat_false : Ix.Kernel.natOpNames.contains cv'.name = false :=
      hkf.2.1
    have hdm_false : Ix.Kernel.natDivModNames.contains cv'.name = false :=
      hkf.2.2
    exact Or.inr ⟨.defnDecl cv' val' hn,
      ⟨ty', val', hcv_run, hv_run, rfl,
        (fun hc => by rw [hnat_false] at hc; exact nomatch hc),
        (fun hc => by rw [hdm_false] at hc; exact nomatch hc)⟩⟩
  | @thmDecl a nlvls ty₀ val₀ ty' val' m_pre1 m_es m_es' m_le m_le' m_pre2 m_kc m_kc'
      x_rc x_ty x_val v_sort r_kc cs_es cs_le cs_kc
      hnot_role _ _ hty_def _ hval_def hty_ann hval_ann hty'_def hval'_def
      hm_es hty_tmc_es hrc_es ev_es _ hsub_es
      hm_le ev_le _ hsub_le
      _ hm_kc hty_tmc_kc hval_tmc_kc hrc_kc ev_kc _ hsub_kc =>
    let cv₀ : ConstantVal .anon := ⟨keyOf t a, List.range nlvls, ty₀⟩
    let cv' : ConstantVal .anon := ⟨keyOf t a, List.range nlvls, ty'⟩
    have hbase : isBaseKey cv₀.name = true := isBaseKey_keyOf t a
    have hfresh_cv : env.find? cv'.name = none :=
      hfresh (.thmInfo cv₀ val₀) (List.mem_singleton.mpr rfl)
    let c : ScopedCtx := Ctx.stored ⟨E_core, env, t, some lim⟩
    have hgood_c : Good c.toCtx calls := hgood
    obtain ⟨hef, hlf⟩ := hinv.scopedCoreFacts
    have hty_tmc_es' : TmC c.κ m_es ty' x_ty := by
      have h := hty_tmc_es
      rwa [posOf_range nlvls ty'] at h
    have hty_tmc_kc' : TmC c.κ m_kc ty' x_ty := by
      have h := hty_tmc_kc
      rwa [posOf_range nlvls ty'] at h
    have hval_tmc_kc' : TmC c.κ m_kc val' x_val := by
      have h := hval_tmc_kc
      rwa [posOf_range nlvls val'] at h
    obtain ⟨_, hty'_nfv, hty'_bvs, hty'_ann⟩ := tmC_closed_props_w hty_tmc_es'
    obtain ⟨_, hval'_nfv, hval'_bvs, hval'_ann⟩ := tmC_closed_props_w hval_tmc_kc'
    obtain ⟨stype, u, ℓ, hinf_ty, hred_ty, hℓ, hu⟩ :=
      scoped_core_ensure_sort (c := c) hrc_es.toRCRep (typesRep_of_nil_eq_w c.κ hm_es)
        (ghostScoped_zero zeroGhostWalked_w) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_es) (fun _ _ => trivial)) ev_es
        (hty_tmc_es' 0 zeroGhostWalked_w)
    have hisZero : (rulesJ (md := .anon)).isZero u :=
      thm_isZero_of_level_equal Levels.levelsObligation
        (RomBound.bounded_mono hbound hsub_le) hℓ hu hm_le ev_le
    obtain ⟨vtype, hinf_val, hde_val⟩ :=
      scoped_core_check (c := c) hrc_kc.toRCRep (typesRep_of_nil_eq_w c.κ hm_kc)
        (ghostScoped_zero zeroGhostWalked_w) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_kc) (fun _ _ => trivial)) ev_kc
        (hval_tmc_kc' 0 zeroGhostWalked_w) (hty_tmc_kc' 0 zeroGhostWalked_w)
    have hkf := hkey _ (List.mem_singleton.mpr rfl)
    have hres_name : Ix.Kernel.reservedBasisNames.contains cv'.name = false :=
      hkf.1
    have hnoprj : cv'.name.isProjFnShape = false := isProjFnShape_of_isBaseKey hbase
    have hcv_run : ConstantValRunJ rulesJ env cv' ty' :=
      ⟨by rw [hfresh_cv]; rfl, hres_name, hnoprj, levelParam_nodup_of_nodup List.nodup_range,
        hty'_bvs, hty'_nfv, hty'_ann, hty'_def,
        infer_constsResolve hinf_ty hef.store hty'_nfv, stype, u, hinf_ty, hred_ty⟩
    have hv_run : ValueFrontRunJ rulesJ env cv' val' ty' val' :=
      ⟨hval'_bvs, hval'_nfv, hval'_ann, hval'_def,
        infer_constsResolve hinf_val hef.store hval'_nfv, vtype, hinf_val, hde_val⟩
    exact Or.inr ⟨.thmDecl cv' val',
      ⟨ty', val', hcv_run, ⟨stype, u, hinf_ty, hred_ty, hisZero⟩, hv_run, rfl⟩⟩
  | @opaqueDecl a nlvls ty₀ val₀ ty' val' m_pre1 m_es m_es' m_pre2 m_kc m_kc'
      x_rc x_ty x_val v_sort r_kc cs_es cs_kc
      hnot_role _ _ hty_def _ hval_def hty_ann hval_ann hty'_def hval'_def
      hm_es hty_tmc_es hrc_es ev_es _ hsub_es
      _ hm_kc hty_tmc_kc hval_tmc_kc hrc_kc ev_kc _ hsub_kc =>
    let cv₀ : ConstantVal .anon := ⟨keyOf t a, List.range nlvls, ty₀⟩
    let cv' : ConstantVal .anon := ⟨keyOf t a, List.range nlvls, ty'⟩
    have hbase : isBaseKey cv₀.name = true := isBaseKey_keyOf t a
    have hfresh_cv : env.find? cv'.name = none :=
      hfresh (.axiomInfo cv₀) (List.mem_singleton.mpr rfl)
    let c : ScopedCtx := Ctx.stored ⟨E_core, env, t, some lim⟩
    have hgood_c : Good c.toCtx calls := hgood
    obtain ⟨hef, hlf⟩ := hinv.scopedCoreFacts
    have hty_tmc_es' : TmC c.κ m_es ty' x_ty := by
      have h := hty_tmc_es
      rwa [posOf_range nlvls ty'] at h
    have hty_tmc_kc' : TmC c.κ m_kc ty' x_ty := by
      have h := hty_tmc_kc
      rwa [posOf_range nlvls ty'] at h
    have hval_tmc_kc' : TmC c.κ m_kc val' x_val := by
      have h := hval_tmc_kc
      rwa [posOf_range nlvls val'] at h
    obtain ⟨_, hty'_nfv, hty'_bvs, hty'_ann⟩ := tmC_closed_props_w hty_tmc_es'
    obtain ⟨_, hval'_nfv, hval'_bvs, hval'_ann⟩ := tmC_closed_props_w hval_tmc_kc'
    obtain ⟨stype, u, _, hinf_ty, hred_ty, _, _⟩ :=
      scoped_core_ensure_sort (c := c) hrc_es.toRCRep (typesRep_of_nil_eq_w c.κ hm_es)
        (ghostScoped_zero zeroGhostWalked_w) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_es) (fun _ _ => trivial)) ev_es
        (hty_tmc_es' 0 zeroGhostWalked_w)
    obtain ⟨vtype, hinf_val, hde_val⟩ :=
      scoped_core_check (c := c) hrc_kc.toRCRep (typesRep_of_nil_eq_w c.κ hm_kc)
        (ghostScoped_zero zeroGhostWalked_w) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_kc) (fun _ _ => trivial)) ev_kc
        (hval_tmc_kc' 0 zeroGhostWalked_w) (hty_tmc_kc' 0 zeroGhostWalked_w)
    have hkf := hkey _ (List.mem_singleton.mpr rfl)
    have hres_name : Ix.Kernel.reservedBasisNames.contains cv'.name = false :=
      hkf.1
    have hnoprj : cv'.name.isProjFnShape = false := isProjFnShape_of_isBaseKey hbase
    have hcv_run : ConstantValRunJ rulesJ env cv' ty' :=
      ⟨by rw [hfresh_cv]; rfl, hres_name, hnoprj, levelParam_nodup_of_nodup List.nodup_range,
        hty'_bvs, hty'_nfv, hty'_ann, hty'_def,
        infer_constsResolve hinf_ty hef.store hty'_nfv, stype, u, hinf_ty, hred_ty⟩
    have hv_run : ValueFrontRunJ rulesJ env cv' val' ty' val' :=
      ⟨hval'_bvs, hval'_nfv, hval'_ann, hval'_def,
        infer_constsResolve hinf_val hef.store hval'_nfv, vtype, hinf_val, hde_val⟩
    exact Or.inr ⟨.opaqueDecl cv' val', ⟨ty', val', hcv_run, hv_run, rfl⟩⟩

end IxVM.Refinement.Decl
