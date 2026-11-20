import IxVMRefinement.Claim.TopDefn

/-! # Definition, theorem and opaque records, and block members, at either role context

`Claim/TopDefn.lean` carries the check of a standalone definition of kind `defn` from the
observed check to the install with the role-context limit an `Option Nat`. This module does
the same for the two other kinds of a definition record (a theorem and an opaque constant)
and for a member of a block of definitions, so that a value step can be stated once for a
validating context (`some n`) and an assuming one (`none`).

* `Decl.CheckedValueAtLim`: the stored-key check evidence of a definition, a theorem or an
  opaque declaration at its actual role-context limit (the definition case is
  `Decl.CheckedDefnAtLim`).
* `Decl.walkedValue_step_lim_run`: such a declaration installs along one step of the
  declaration judgement, and the prefix invariant transports to every store and limit at which
  the installed constant reloads.
* `LoadedReads.checkedValue_scope_lim`, `LoadedReads.checkedValue_at_lim`: the scoping facts
  and the evidence, from the observed `KernelCheck::check_const` run, for every kind.
* `LoadedReads.memberCheckedLimAt_record`, `Typing.memberCheckedLimAt_checkedLimAt`: a block
  member checked at a limit has its projection record in the run's store and is checked at its
  constant address at the same limit.
* `Typing.checkedLimAt_value_step`, `Typing.memberCheckedLimAt_value_step`: the canonical
  reading, the check evidence and the reload, from the walk's check at its actual limit, for a
  standalone record and for a block member.
-/

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u

namespace IxVM.Refinement.Decl
open Aiur Aiur.Library Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel.Semantics Ix.Kernel.SetModel Ix.Kernel.Model
open Ix.Kernel (Env ConstantInfo ConstantVal Declaration)
open Ix.Kernel.Rules (Annot Red DefEq Infer)

private theorem tm_noLetExpr_v {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
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

private theorem tmC_closed_props_v {κ : _root_.Address → KKey} {h : Heap F}
    {e : KExpr} {p : SourceValue F} (rep : TmC κ h e p) :
    noLetExpr e = true ∧ e.hasFvar = false ∧ e.looseBVarsBounded 0 = true ∧
      Annot 0 e e := by
  have h0 : Tm κ 0 (fun _ => .sort .zero) h 0 e p := rep 0 (fun _ => .sort .zero)
  have hnl : noLetExpr e = true :=
    tm_noLetExpr_v (fun _ hlt => absurd hlt (Nat.not_lt_zero _)) h0
  have hfv : e.hasFvar = false := Tm.hasFvar_false h0
  have hbvs : e.looseBVarsBounded 0 = true := Tm.looseBVarsBounded h0
  exact ⟨hnl, hfv, hbvs, annot_refl_of_noLetExpr hnl hfv hbvs 0⟩

private def zeroGhostWalked_v : Nat → KExpr := fun _ => .sort .zero

private theorem typesRep_of_nil_eq_v (κ : _root_.Address → KKey) {m m_pre : Heap F}
    (hm : m = m_pre ++ [.construct kexprListEnum "Nil" []]) :
    TypesRep κ zeroGhostWalked_v m 0 (.ptr (.enum kexprListEnum) m_pre.length) := by
  rw [hm]
  exact typesRep_alloc_nil κ zeroGhostWalked_v m_pre

/-- **Stored-key evidence from the check of a definition, a theorem or an opaque declaration at
its actual role-context limit.** The definition case is `CheckedDefnAtLim`; the two others are
the corresponding cases of `CheckedConstOriginAt` with the role context read at an optional
limit (`Core.RCRep t lim`: a validating context at `some n`, an assuming one at `none`). -/
inductive CheckedValueAtLim (κ : _root_.Address → Core.KKey) (lim : Option Nat)
    (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (bAddr : _root_.Address)
    (E_core : Ixon.Env) (order_role : List _root_.Address) :
    Ix.Kernel.Declaration .anon → Ix.Kernel.Declaration .anon → Prop where
  | ofDefn
      {d d' : Ix.Kernel.Declaration .anon}
      (h : CheckedDefnAtLim κ lim calls t bAddr E_core order_role d d') :
      CheckedValueAtLim κ lim calls t bAddr E_core order_role d d'
  | thmDecl
      {a : _root_.Address} {nlvls : Nat} {ty₀ val₀ ty' val' : Core.KExpr}
      {m_pre1 m_es m_es' m_le m_le' m_pre2 m_kc m_kc' : Heap F}
      {x_rc x_ty x_val v_sort r_kc : SourceValue F}
      {cs_es cs_le cs_kc : List (Call F)}
      (hnot_role : a ∉ order_role)
      (hnlvls : nlvls < 4294967296)
      (hty_lbb : ty₀.looseBVarsBounded 0 = true)
      (hty_def : ty₀.allLevelParamsDefined (List.range nlvls) = true)
      (hval_lbb : val₀.looseBVarsBounded 0 = true)
      (hval_def : val₀.allLevelParamsDefined (List.range nlvls) = true)
      (hty_ann : IxVM.Consistency.Annotates ty' ty₀)
      (hval_ann : IxVM.Consistency.Annotates val' val₀)
      (hty_out_def : ty'.allLevelParamsDefined (List.range nlvls) = true)
      (hval_out_def : val'.allLevelParamsDefined (List.range nlvls) = true)
      (hm_es : m_es = m_pre1 ++
        [.construct IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []])
      (hty_tmc_es : Core.TmC κ m_es (Core.posOf (List.range nlvls) ty') x_ty)
      (hrc_es : Core.RCRep t lim m_es x_rc)
      (ev_es : ObsFn Core.W "KernelInfer::k_ensure_sort"
        [x_rc, x_ty, .ptr (.enum IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre1.length]
        m_es v_sort m_es' cs_es)
      (hcl_es : (⟨"KernelInfer::k_ensure_sort",
        [x_rc, x_ty, .ptr (.enum IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre1.length],
        m_es⟩ : Call F) ∈ calls)
      (hsub_es : ∀ cl ∈ cs_es, cl ∈ calls)
      (hm_le : m_le = m_es' ++ [.construct "KernelTypes::KLevelNode" "Zero" []])
      (ev_le : ObsFn Core.W "KernelLevels::level_equal"
        [v_sort, .ptr (.enum "KernelTypes::KLevelNode") m_es'.length]
        m_le (.field 1) m_le' cs_le)
      (hcl_le : (⟨"KernelLevels::level_equal",
        [v_sort, .ptr (.enum "KernelTypes::KLevelNode") m_es'.length],
        m_le⟩ : Call F) ∈ calls)
      (hsub_le : ∀ cl ∈ cs_le, cl ∈ calls)
      (hext_kc : Heap.Extends m_le' m_kc)
      (hm_kc : m_kc = m_pre2 ++
        [.construct IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []])
      (hty_tmc_kc : Core.TmC κ m_kc (Core.posOf (List.range nlvls) ty') x_ty)
      (hval_tmc_kc : Core.TmC κ m_kc (Core.posOf (List.range nlvls) val') x_val)
      (hrc_kc : Core.RCRep t lim m_kc x_rc)
      (ev_kc : ObsFn Core.W "KernelInfer::k_check"
        [x_rc, x_val, x_ty,
         .ptr (.enum IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre2.length]
        m_kc r_kc m_kc' cs_kc)
      (hcl_kc : (⟨"KernelInfer::k_check",
        [x_rc, x_val, x_ty,
         .ptr (.enum IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre2.length],
        m_kc⟩ : Call F) ∈ calls)
      (hsub_kc : ∀ cl ∈ cs_kc, cl ∈ calls) :
      CheckedValueAtLim κ lim calls t bAddr E_core order_role
        (.thmDecl ⟨Core.keyOf t a, List.range nlvls, ty₀⟩ val₀)
        (.thmDecl ⟨Core.keyOf t a, List.range nlvls, ty'⟩ val')
  | opaqueDecl
      {a : _root_.Address} {nlvls : Nat} {ty₀ val₀ ty' val' : Core.KExpr}
      {m_pre1 m_es m_es' m_pre2 m_kc m_kc' : Heap F}
      {x_rc x_ty x_val v_sort r_kc : SourceValue F}
      {cs_es cs_kc : List (Call F)}
      (hnot_role : a ∉ order_role)
      (hnlvls : nlvls < 4294967296)
      (hty_lbb : ty₀.looseBVarsBounded 0 = true)
      (hty_def : ty₀.allLevelParamsDefined (List.range nlvls) = true)
      (hval_lbb : val₀.looseBVarsBounded 0 = true)
      (hval_def : val₀.allLevelParamsDefined (List.range nlvls) = true)
      (hty_ann : IxVM.Consistency.Annotates ty' ty₀)
      (hval_ann : IxVM.Consistency.Annotates val' val₀)
      (hty_out_def : ty'.allLevelParamsDefined (List.range nlvls) = true)
      (hval_out_def : val'.allLevelParamsDefined (List.range nlvls) = true)
      (hm_es : m_es = m_pre1 ++
        [.construct IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []])
      (hty_tmc_es : Core.TmC κ m_es (Core.posOf (List.range nlvls) ty') x_ty)
      (hrc_es : Core.RCRep t lim m_es x_rc)
      (ev_es : ObsFn Core.W "KernelInfer::k_ensure_sort"
        [x_rc, x_ty, .ptr (.enum IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre1.length]
        m_es v_sort m_es' cs_es)
      (hcl_es : (⟨"KernelInfer::k_ensure_sort",
        [x_rc, x_ty, .ptr (.enum IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre1.length],
        m_es⟩ : Call F) ∈ calls)
      (hsub_es : ∀ cl ∈ cs_es, cl ∈ calls)
      (hext_kc : Heap.Extends m_es' m_kc)
      (hm_kc : m_kc = m_pre2 ++
        [.construct IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []])
      (hty_tmc_kc : Core.TmC κ m_kc (Core.posOf (List.range nlvls) ty') x_ty)
      (hval_tmc_kc : Core.TmC κ m_kc (Core.posOf (List.range nlvls) val') x_val)
      (hrc_kc : Core.RCRep t lim m_kc x_rc)
      (ev_kc : ObsFn Core.W "KernelInfer::k_check"
        [x_rc, x_val, x_ty,
         .ptr (.enum IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre2.length]
        m_kc r_kc m_kc' cs_kc)
      (hcl_kc : (⟨"KernelInfer::k_check",
        [x_rc, x_val, x_ty,
         .ptr (.enum IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre2.length],
        m_kc⟩ : Call F) ∈ calls)
      (hsub_kc : ∀ cl ∈ cs_kc, cl ∈ calls) :
      CheckedValueAtLim κ lim calls t bAddr E_core order_role
        (.opaqueDecl ⟨Core.keyOf t a, List.range nlvls, ty₀⟩ val₀)
        (.opaqueDecl ⟨Core.keyOf t a, List.range nlvls, ty'⟩ val')

/-- **A walked definition, theorem or opaque constant installs along one step of the
declaration judgement, at the limit of its own check, and the prefix invariant is kept at every
store and every limit.** The check is read at the store and the limit of its own run (`hinv`,
`hchk`), a validating context or an assuming one; the conclusion gives the declaration step
that installs the constant, and transports the invariant for any store `E'` and limit `lim'`
at which the new record reloads as the constant stored (`ReloadsAs`). -/
theorem walkedValue_step_lim_run
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {E_core : Ixon.Env} {order_role : List _root_.Address} {lim : Option Nat}
    {env : Env .anon} {d d' : Declaration .anon}
    (hinv : PrefixInv.{u} E_core t lim env)
    (hchk : CheckedValueAtLim (Ctx.stored ⟨E_core, env, t, lim⟩).κ lim calls t bAddr
      E_core order_role d d')
    (hgood : Good ⟨E_core, env, t, none⟩ calls)
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs d, env.find? ci₀.name = none)
    (hkey : ∀ ci₀ ∈ IxVM.Consistency.installs d, KeyFree ci₀.name) :
    (∃ d₀, DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d₀
      ⟨IxVM.Consistency.installs d' ++ env.consts⟩) ∧
    CleanInstallStep env d ⟨IxVM.Consistency.installs d' ++ env.consts⟩ ∧
      ∀ (E' : Ixon.Env) (lim' : Option Nat),
        (∀ cn ∈ IxVM.Consistency.installs d', ReloadsAs E' t ⟨cn :: env.consts⟩ cn) →
        PrefixInv.{u} E' t lim' env →
          PrefixInv.{u} E' t lim' ⟨IxVM.Consistency.installs d' ++ env.consts⟩ := by
  have hbound : IxVM.Consistency.Bounded calls := hgood.2
  cases hchk with
  | ofDefn h => exact walkedDefn_step_lim_run hinv h hgood hfresh hkey
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
    have hstored : IxVM.Consistency.StoredAs (.thmInfo cv' val') (.thmInfo cv₀ val₀) :=
      ⟨⟨rfl, rfl, hty_ann⟩, hval_ann⟩
    have hclean : CleanInstallStep env (.thmDecl cv₀ val₀) ⟨.thmInfo cv' val' :: env.consts⟩ :=
      CleanInstallStep.single rfl hstored hfresh_cv hbase
    let c : ScopedCtx := Ctx.stored ⟨E_core, env, t, lim⟩
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
    obtain ⟨_, hty'_nfv, hty'_bvs, hty'_ann⟩ := tmC_closed_props_v hty_tmc_es'
    obtain ⟨_, hval'_nfv, hval'_bvs, hval'_ann⟩ := tmC_closed_props_v hval_tmc_kc'
    obtain ⟨stype, u, ℓ, hinf_ty, hred_ty, hℓ, hu⟩ :=
      scoped_core_ensure_sort (c := c) hrc_es (typesRep_of_nil_eq_v c.κ hm_es)
        (ghostScoped_zero zeroGhostWalked_v) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_es) (fun _ _ => trivial)) ev_es
        (hty_tmc_es' 0 zeroGhostWalked_v)
    have hisZero : (rulesJ (md := .anon)).isZero u :=
      thm_isZero_of_level_equal Levels.levelsObligation
        (RomBound.bounded_mono hbound hsub_le) hℓ hu hm_le ev_le
    obtain ⟨vtype, hinf_val, hde_val⟩ :=
      scoped_core_check (c := c) hrc_kc (typesRep_of_nil_eq_v c.κ hm_kc)
        (ghostScoped_zero zeroGhostWalked_v) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_kc) (fun _ _ => trivial)) ev_kc
        (hval_tmc_kc' 0 zeroGhostWalked_v) (hty_tmc_kc' 0 zeroGhostWalked_v)
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
    have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.thmDecl cv' val')
        ⟨.thmInfo cv' val' :: env.consts⟩ :=
      ⟨ty', val', hcv_run, ⟨stype, u, hinf_ty, hred_ty, hisZero⟩, hv_run, rfl⟩
    exact ⟨⟨.thmDecl cv' val', hdecl⟩, hclean, fun E' lim' hrel hinv' =>
      hinv'.cons_value (cn := .thmInfo cv' val') (a₀ := a) rfl hfresh_cv
      (fun _ => ne_projTableName_of_isBaseKey hbase) (fun _ _ e => nomatch e)
      (fun _ _ _ e => nomatch e) (fun _ _ _ _ e => nomatch e) (fun _ e => nomatch e)
      (FullDeclInv.step_of_foldInv_clean hclean
        (foldInv_step_declRunJ (d := .thmDecl cv' val') (fun _ _ heq => nomatch heq) hdecl))
      (foldStoreInv_step_declRunJ (d := .thmDecl cv' val') hinv.store (fun _ _ heq => nomatch heq) hdecl)
      (hrel _ (List.mem_singleton.mpr rfl))⟩
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
    have hstored : IxVM.Consistency.StoredAs (.axiomInfo cv') (.axiomInfo cv₀) :=
      ⟨⟨rfl, rfl, hty_ann⟩, trivial⟩
    have hclean : CleanInstallStep env (.opaqueDecl cv₀ val₀) ⟨.axiomInfo cv' :: env.consts⟩ :=
      CleanInstallStep.single rfl hstored hfresh_cv hbase
    let c : ScopedCtx := Ctx.stored ⟨E_core, env, t, lim⟩
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
    obtain ⟨_, hty'_nfv, hty'_bvs, hty'_ann⟩ := tmC_closed_props_v hty_tmc_es'
    obtain ⟨_, hval'_nfv, hval'_bvs, hval'_ann⟩ := tmC_closed_props_v hval_tmc_kc'
    obtain ⟨stype, u, _, hinf_ty, hred_ty, _, _⟩ :=
      scoped_core_ensure_sort (c := c) hrc_es (typesRep_of_nil_eq_v c.κ hm_es)
        (ghostScoped_zero zeroGhostWalked_v) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_es) (fun _ _ => trivial)) ev_es
        (hty_tmc_es' 0 zeroGhostWalked_v)
    obtain ⟨vtype, hinf_val, hde_val⟩ :=
      scoped_core_check (c := c) hrc_kc (typesRep_of_nil_eq_v c.κ hm_kc)
        (ghostScoped_zero zeroGhostWalked_v) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_kc) (fun _ _ => trivial)) ev_kc
        (hval_tmc_kc' 0 zeroGhostWalked_v) (hty_tmc_kc' 0 zeroGhostWalked_v)
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
    have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.opaqueDecl cv' val')
        ⟨.axiomInfo cv' :: env.consts⟩ :=
      ⟨ty', val', hcv_run, hv_run, rfl⟩
    exact ⟨⟨.opaqueDecl cv' val', hdecl⟩, hclean, fun E' lim' hrel hinv' =>
      hinv'.cons_value (cn := .axiomInfo cv') (a₀ := a) rfl hfresh_cv
      (fun _ => ne_projTableName_of_isBaseKey hbase) (fun _ _ e => nomatch e)
      (fun _ _ _ e => nomatch e) (fun _ _ _ _ e => nomatch e) (fun _ e => nomatch e)
      (FullDeclInv.step_of_foldInv_clean hclean
        (foldInv_step_declRunJ (d := .opaqueDecl cv' val') (fun _ _ heq => nomatch heq) hdecl))
      (foldStoreInv_step_declRunJ (d := .opaqueDecl cv' val') hinv.store (fun _ _ heq => nomatch heq) hdecl)
      (hrel _ (List.mem_singleton.mpr rfl))⟩

end IxVM.Refinement.Decl

namespace IxVM.Refinement.LoadedReads
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Obs
open IxVM.Consistency

private theorem mem_sublist_of_cons_left_v {α : Type} {x : α} {ys cs : List α}
    (h : ∀ c ∈ x :: ys, c ∈ cs) : ∀ c ∈ ys, c ∈ cs :=
  fun c hm => h c (List.mem_cons_of_mem _ hm)

private theorem mem_sublist_of_append_right_v {α : Type} {xs ys cs : List α}
    (h : ∀ c ∈ xs ++ ys, c ∈ cs) : ∀ c ∈ ys, c ∈ cs :=
  fun c hm => h c (List.mem_append_right _ hm)

/-- `KernelCheck::is_unsafe_ci` on a theorem or opaque payload in Lean's logic returns `0` and
leaves the heap unchanged. -/
private theorem is_unsafe_ci_thmOpaqueShape_safe {d : Ixon.Definition}
    {tyPtr valPtr hint v1 : SourceValue F} {h m2 : Heap F} {cs : List (Call F)}
    (hsafe : Ix.Kernel.Reader.safetyDecline d = none) (hkind : d.kind ≠ .defn)
    (ev : ObsFn Core.W "KernelCheck::is_unsafe_ci"
      [Ingress.defnValShape d tyPtr valPtr hint] h v1 m2 cs) :
    v1 = .field 0 ∧ m2 = h := by
  cases hk : d.kind with
  | defn => exact absurd hk hkind
  | opaq =>
    have hns : (d.safety == .unsaf) = false := by
      simpa [Ix.Kernel.Reader.safetyDecline, Ix.Kernel.Reader.safetyDeclineOf, hk] using hsafe
    simp only [Ingress.defnValShape, hk, hns] at ev
    cases «KernelCheck::is_unsafe_ci».obs ev with
    | Opaque _ _ _ _ _ _ _ hv he hr _ =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rcases hv with ⟨_, _, _, _, _, hu_eq⟩
      rw [← hu_eq] at he
      exact ⟨he, hr⟩
    | Axiom _ _ _ hv | Defn_Safe _ _ _ _ _ hv | Defn_other _ _ _ _ _ _ hv
    | Thm _ _ _ _ _ hv | Quot _ _ _ _ _ _ _ hv
    | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv
    | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv =>
      simp [Core.kciEnum] at hv
  | thm =>
    simp only [Ingress.defnValShape, hk] at ev
    cases «KernelCheck::is_unsafe_ci».obs ev with
    | Thm _ _ _ _ _ _ he hr _ => exact ⟨he, hr⟩
    | Axiom _ _ _ hv | Defn_Safe _ _ _ _ _ hv | Defn_other _ _ _ _ _ _ hv
    | Opaque _ _ _ _ _ _ _ hv | Quot _ _ _ _ _ _ _ hv
    | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv
    | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv =>
      simp [Core.kciEnum] at hv

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)}

/-- **The roots of a checked definition, theorem or opaque payload are scoped**, at either kind
of role context: `checkedDefn_scope_lim` for every kind of a definition record. -/
theorem checkedValue_scope_lim (ht : t.check = .ok ()) (hbound : Bounded calls)
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant} {d : Ixon.Definition}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {ty₀ val₀ : Ix.Kernel.Expr .anon}
    (hsafe_decl : Ix.Kernel.Reader.safetyDecline d = none)
    {m_chk h'_chk : Heap F} {rc ap v r_chk : SourceValue F}
    {cs_chk : List (Call F)} {blobs : List (_root_.Address × ByteArray)}
    (hblob : ∀ x bs, (x, bs) ∈ blobs → blob x = some bs)
    (hraw_d : Ingress.RawDefnValRep src.refs.toList [] src.univs.toList src.sharing.toList blobs
      m_chk d v)
    (hty : (exprReader t blob src id self).read d.typ = .ok ty₀)
    (hval : (exprReader t blob src id self).read d.value = .ok val₀)
    (ev_chk : ObsFn Core.W "KernelCheck::check_const" [rc, v, ap] m_chk r_chk h'_chk cs_chk)
    (hsub_chk : ∀ cl ∈ cs_chk, cl ∈ calls) :
    ty₀.looseBVarsBounded 0 = true ∧
    ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true ∧
    val₀.looseBVarsBounded 0 = true ∧
    val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true := by
  by_cases hkd : d.kind = .defn
  · exact checkedDefn_scope_lim ht hbound hkd hsafe_decl hblob hraw_d hty hval ev_chk hsub_chk
  obtain ⟨hnlvls, tyPtr, valPtr, hintVal, rfl, raw_ty, raw_val⟩ := hraw_d
  cases hk : d.kind with
  | defn => exact absurd hk hkd
  | thm =>
    have hv_shape : Ingress.defnValShape d tyPtr valPtr hintVal =
        .construct Core.kciEnum "Thm" [.field (d.lvls.toNat : F), tyPtr, valPtr] := by
      simp [Ingress.defnValShape, hk]
    cases «KernelCheck::check_const».obs ev_chk with
    | Axiom_n1 | Axiom_other_n0 | Axiom_other_other | Defn
    | Opaque | Quot
    | Induct_n0 | Induct_other_n0 | Induct_other_other
    | Ctor_n0_n0 | Ctor_n0_other | Ctor_other_n0 | Ctor_other_other
    | Rec_n0 | Rec_other =>
      simp_all [Ingress.defnValShape, Core.kciEnum]
    | Thm v1 m2 cs12 x_nlvls x_ty x_val _ m544 cs554 _ m581 cs591 v617 m618 cs628 m649
        v672 m675 cs683 m696 _ m716 cs726 _ m746 cs756 cs778 m807
        ev14 _ _ hv526 ev556 ev593 hm657 ev630 hm704 ev685 heq714 ev728 ev758 hm815 ev780 hc819 =>
      obtain ⟨hv1, hm2⟩ := is_unsafe_ci_thmOpaqueShape_safe hsafe_decl hkd ev14
      subst v1; subst m2
      subst v672
      rw [hv_shape] at hv526
      simp only [Core.kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv526
      obtain ⟨hxn, hxt, hxv⟩ := hv526
      subst x_nlvls; subst x_ty; subst x_val
      have hs1 := mem_sublist_of_append_right_v (mem_sublist_of_cons_left_v (by rwa [hc819] at hsub_chk))
      have hcl_v1 := hs1 _ List.mem_cons_self
      have hs2 := mem_sublist_of_append_right_v (mem_sublist_of_cons_left_v hs1)
      have hcl_v2 := hs2 _ List.mem_cons_self
      obtain ⟨_, hty_lbb, hty_def⟩ :=
        Assembly.validate_expr_well_scoped_spec (cx := readCtx t blob) (self := self) hbound
          hnlvls raw_ty (Heap.Extends.refl m_chk) hty ev556 hcl_v1
      obtain ⟨_, hval_lbb, hval_def⟩ :=
        Assembly.validate_expr_well_scoped_spec (cx := readCtx t blob) (self := self) hbound
          hnlvls raw_val ev556.heap_extends hval ev593 hcl_v2
      exact ⟨hty_lbb, hty_def, hval_lbb, hval_def⟩
  | opaq =>
    have hv_shape : Ingress.defnValShape d tyPtr valPtr hintVal =
        .construct Core.kciEnum "Opaque"
          [.field (d.lvls.toNat : F), tyPtr, valPtr, Ingress.repBoolField (d.safety == .unsaf)] := by
      simp [Ingress.defnValShape, hk]
    cases «KernelCheck::check_const».obs ev_chk with
    | Axiom_n1 | Axiom_other_n0 | Axiom_other_other | Defn | Thm
    | Quot
    | Induct_n0 | Induct_other_n0 | Induct_other_other
    | Ctor_n0_n0 | Ctor_n0_other | Ctor_other_n0 | Ctor_other_other
    | Rec_n0 | Rec_other =>
      simp_all [Ingress.defnValShape, Core.kciEnum]
    | Opaque v1 m2 cs12 x_nlvls x_ty x_val _ _ m849 cs859 _ m886 cs896 v922 m923 cs933 m954
        _ m967 cs977 _ m997 cs1007 cs1029 m1058
        ev14 _ _ _ hv825 ev861 ev898 hm962 ev935 ev979 ev1009 hm1066 ev1031 hc1070 =>
      obtain ⟨hv1, hm2⟩ := is_unsafe_ci_thmOpaqueShape_safe hsafe_decl hkd ev14
      subst v1; subst m2
      rw [hv_shape] at hv825
      simp only [Core.kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv825
      obtain ⟨hxn, hxt, hxv, -⟩ := hv825
      subst x_nlvls; subst x_ty; subst x_val
      have hs1 := mem_sublist_of_append_right_v (mem_sublist_of_cons_left_v (by rwa [hc1070] at hsub_chk))
      have hcl_v1 := hs1 _ List.mem_cons_self
      have hs2 := mem_sublist_of_append_right_v (mem_sublist_of_cons_left_v hs1)
      have hcl_v2 := hs2 _ List.mem_cons_self
      obtain ⟨_, hty_lbb, hty_def⟩ :=
        Assembly.validate_expr_well_scoped_spec (cx := readCtx t blob) (self := self) hbound
          hnlvls raw_ty (Heap.Extends.refl m_chk) hty ev861 hcl_v1
      obtain ⟨_, hval_lbb, hval_def⟩ :=
        Assembly.validate_expr_well_scoped_spec (cx := readCtx t blob) (self := self) hbound
          hnlvls raw_val ev861.heap_extends hval ev898 hcl_v2
      exact ⟨hty_lbb, hty_def, hval_lbb, hval_def⟩

/-- **The check evidence of a loaded definition, theorem or opaque payload at its actual
role-context limit**, for a named stored declaration: `checkedDefn_at_lim` for every kind of a
definition record. -/
theorem checkedValue_at_lim {κ : _root_.Address → Core.KKey}
    {E : Ixon.Env} {bAddr decl_addr : _root_.Address} {order_role : List _root_.Address}
    {d : Ixon.Definition} {ty₀ val₀ ty' val' : Ix.Kernel.Expr .anon}
    (hdecl_not_role : decl_addr ∉ order_role)
    (hsafe_decl : Ix.Kernel.Reader.safetyDecline d = none)
    {lim : Option Nat} {m_chk h'_chk : Heap F} {rc ap r_chk tyPtr valPtr hintVal : SourceValue F}
    {cs_chk : List (Call F)}
    (hrc_m : Core.RCRep t lim m_chk rc)
    (hnlvls : d.lvls.toNat < 4294967296)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true)
    (hval_lbb : val₀.looseBVarsBounded 0 = true)
    (hval_def : val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true)
    (hty_ann : Annotates ty' ty₀) (hval_ann : Annotates val' val₀)
    (hty_tmc_m : Core.TmC κ m_chk (Core.posOf (List.range d.lvls.toNat) ty') tyPtr)
    (hval_tmc_m : Core.TmC κ m_chk (Core.posOf (List.range d.lvls.toNat) val') valPtr)
    (ev_chk : ObsFn Core.W "KernelCheck::check_const"
      [rc, Ingress.defnValShape d tyPtr valPtr hintVal, ap] m_chk r_chk h'_chk cs_chk)
    (hsub_chk : ∀ cl ∈ cs_chk, cl ∈ calls) :
    ∀ hn : Ix.Kernel.ReducibilityHint,
      Decl.CheckedValueAtLim κ lim calls t bAddr E order_role
        (defnDecl d.kind ⟨Core.keyOf t decl_addr, List.range d.lvls.toNat, ty₀⟩ val₀ hn)
        (defnDecl d.kind ⟨Core.keyOf t decl_addr, List.range d.lvls.toNat, ty'⟩ val' hn) := by
  by_cases hkd : d.kind = .defn
  · intro hn
    exact .ofDefn (checkedDefn_at_lim hdecl_not_role hkd hsafe_decl hrc_m hnlvls hty_lbb
      hty_def hval_lbb hval_def hty_ann hval_ann hty_tmc_m hval_tmc_m ev_chk hsub_chk hn)
  cases hk : d.kind with
  | defn => exact absurd hk hkd
  | thm =>
    have hv_shape : Ingress.defnValShape d tyPtr valPtr hintVal =
        .construct Core.kciEnum "Thm" [.field (d.lvls.toNat : F), tyPtr, valPtr] := by
      simp [Ingress.defnValShape, hk]
    cases «KernelCheck::check_const».obs ev_chk with
    | Axiom_n1 | Axiom_other_n0 | Axiom_other_other | Defn
    | Opaque | Quot
    | Induct_n0 | Induct_other_n0 | Induct_other_other
    | Ctor_n0_n0 | Ctor_n0_other | Ctor_other_n0 | Ctor_other_other
    | Rec_n0 | Rec_other =>
      simp_all [Ingress.defnValShape, Core.kciEnum]
    | Thm v1 m2 cs12 x_nlvls x_ty x_val _ m544 cs554 _ m581 cs591 v617 m618 cs628 m649
        v672 m675 cs683 m696 _ m716 cs726 _ m746 cs756 cs778 m807
        ev14 _ _ hv526 ev556 ev593 hm657 ev630 hm704 ev685 heq714 ev728 ev758 hm815 ev780 hc819 =>
      obtain ⟨hv1, hm2⟩ := is_unsafe_ci_thmOpaqueShape_safe hsafe_decl hkd ev14
      subst v1; subst m2
      subst v672
      rw [hv_shape] at hv526
      simp only [Core.kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv526
      obtain ⟨hxn, hxt, hxv⟩ := hv526
      subst x_nlvls; subst x_ty; subst x_val
      have hs1 := mem_sublist_of_append_right_v (mem_sublist_of_cons_left_v (by rwa [hc819] at hsub_chk))
      have hcl_v1 := hs1 _ List.mem_cons_self
      have hs2 := mem_sublist_of_append_right_v (mem_sublist_of_cons_left_v hs1)
      have hcl_v2 := hs2 _ List.mem_cons_self
      have hs3 := mem_sublist_of_append_right_v (mem_sublist_of_cons_left_v hs2)
      have hcl_es := hs3 _ List.mem_cons_self
      have hsub_es : ∀ cl ∈ cs628, cl ∈ calls :=
        fun cl hm => (mem_sublist_of_cons_left_v hs3) cl (List.mem_append_left _ hm)
      have hs4 := mem_sublist_of_append_right_v (mem_sublist_of_cons_left_v hs3)
      have hcl_le := hs4 _ List.mem_cons_self
      have hsub_le : ∀ cl ∈ cs683, cl ∈ calls :=
        fun cl hm => (mem_sublist_of_cons_left_v hs4) cl (List.mem_append_left _ hm)
      have hs5 := mem_sublist_of_append_right_v (mem_sublist_of_cons_left_v hs4)
      have hs6 := mem_sublist_of_append_right_v (mem_sublist_of_cons_left_v hs5)
      have hs7 := mem_sublist_of_append_right_v (mem_sublist_of_cons_left_v hs6)
      have hcl_kc := hs7 _ List.mem_cons_self
      have hsub_kc := mem_sublist_of_cons_left_v hs7
      obtain ⟨cs_sr1, ev_sr1, hcs726⟩ := Assembly.assert_safety_zero_spec ev728
      obtain ⟨cs_sr2, ev_sr2, hcs756⟩ := Assembly.assert_safety_zero_spec ev758
      have ext_581_649 : Heap.Extends m581 m649 := by rw [hm657]; exact Heap.Extends.snoc _ _
      have ext_618_696 : Heap.Extends m618 m696 := by rw [hm704]; exact Heap.Extends.snoc _ _
      have ext_746_807 : Heap.Extends m746 m807 := by rw [hm815]; exact Heap.Extends.snoc _ _
      have ext_m_649 : Heap.Extends m_chk m649 :=
        ev556.heap_extends.trans (ev593.heap_extends.trans ext_581_649)
      have ext_649_675 : Heap.Extends m649 m675 :=
        ev630.heap_extends.trans (ext_618_696.trans ev685.heap_extends)
      have ext_675_807 : Heap.Extends m675 m807 :=
        ev_sr1.heap_extends.trans (ev_sr2.heap_extends.trans ext_746_807)
      have ext_649_807 : Heap.Extends m649 m807 := ext_649_675.trans ext_675_807
      have ext_m_807 : Heap.Extends m_chk m807 := ext_m_649.trans ext_649_807
      have hty_out_def := Core.Scope.validatedAnnotation_positional
        hnlvls hty_tmc_m hty_ann hty_def ev556
      have hval_out_def := Core.Scope.validatedAnnotation_positional
        hnlvls (Core.TmC.mono ev556.heap_extends hval_tmc_m) hval_ann hval_def ev593
      have hty_tmc_649 := Core.TmC.mono ext_m_649 hty_tmc_m
      have hval_tmc_807 := Core.TmC.mono ext_m_807 hval_tmc_m
      intro hn
      exact .thmDecl hdecl_not_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann
          hty_out_def hval_out_def
          hm657 hty_tmc_649 (Core.RCRep.mono ext_m_649 hrc_m) ev630 hcl_es hsub_es
          hm704 ev685 hcl_le hsub_le
          ext_675_807 hm815 (Core.TmC.mono ext_649_807 hty_tmc_649) hval_tmc_807
          (Core.RCRep.mono ext_m_807 hrc_m) ev780 hcl_kc hsub_kc
  | opaq =>
    have hv_shape : Ingress.defnValShape d tyPtr valPtr hintVal =
        .construct Core.kciEnum "Opaque"
          [.field (d.lvls.toNat : F), tyPtr, valPtr, Ingress.repBoolField (d.safety == .unsaf)] := by
      simp [Ingress.defnValShape, hk]
    cases «KernelCheck::check_const».obs ev_chk with
    | Axiom_n1 | Axiom_other_n0 | Axiom_other_other | Defn | Thm
    | Quot
    | Induct_n0 | Induct_other_n0 | Induct_other_other
    | Ctor_n0_n0 | Ctor_n0_other | Ctor_other_n0 | Ctor_other_other
    | Rec_n0 | Rec_other =>
      simp_all [Ingress.defnValShape, Core.kciEnum]
    | Opaque v1 m2 cs12 x_nlvls x_ty x_val _ _ m849 cs859 _ m886 cs896 v922 m923 cs933 m954
        _ m967 cs977 _ m997 cs1007 cs1029 m1058
        ev14 _ _ _ hv825 ev861 ev898 hm962 ev935 ev979 ev1009 hm1066 ev1031 hc1070 =>
      obtain ⟨hv1, hm2⟩ := is_unsafe_ci_thmOpaqueShape_safe hsafe_decl hkd ev14
      subst v1; subst m2
      rw [hv_shape] at hv825
      simp only [Core.kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv825
      obtain ⟨hxn, hxt, hxv, -⟩ := hv825
      subst x_nlvls; subst x_ty; subst x_val
      have hs1 := mem_sublist_of_append_right_v (mem_sublist_of_cons_left_v (by rwa [hc1070] at hsub_chk))
      have hcl_v1 := hs1 _ List.mem_cons_self
      have hs2 := mem_sublist_of_append_right_v (mem_sublist_of_cons_left_v hs1)
      have hcl_v2 := hs2 _ List.mem_cons_self
      have hs3 := mem_sublist_of_append_right_v (mem_sublist_of_cons_left_v hs2)
      have hcl_es := hs3 _ List.mem_cons_self
      have hsub_es : ∀ cl ∈ cs933, cl ∈ calls :=
        fun cl hm => (mem_sublist_of_cons_left_v hs3) cl (List.mem_append_left _ hm)
      have hs4 := mem_sublist_of_append_right_v (mem_sublist_of_cons_left_v hs3)
      have hs5 := mem_sublist_of_append_right_v (mem_sublist_of_cons_left_v hs4)
      have hs6 := mem_sublist_of_append_right_v (mem_sublist_of_cons_left_v hs5)
      have hcl_kc := hs6 _ List.mem_cons_self
      have hsub_kc := mem_sublist_of_cons_left_v hs6
      obtain ⟨cs_sr1, ev_sr1, hcs977⟩ := Assembly.assert_safety_zero_spec ev979
      obtain ⟨cs_sr2, ev_sr2, hcs1007⟩ := Assembly.assert_safety_zero_spec ev1009
      have ext_886_954 : Heap.Extends m886 m954 := by rw [hm962]; exact Heap.Extends.snoc _ _
      have ext_997_1058 : Heap.Extends m997 m1058 := by rw [hm1066]; exact Heap.Extends.snoc _ _
      have ext_m_954 : Heap.Extends m_chk m954 :=
        ev861.heap_extends.trans (ev898.heap_extends.trans ext_886_954)
      have ext_923_1058 : Heap.Extends m923 m1058 :=
        ev_sr1.heap_extends.trans (ev_sr2.heap_extends.trans ext_997_1058)
      have ext_954_1058 : Heap.Extends m954 m1058 := ev935.heap_extends.trans ext_923_1058
      have ext_m_1058 : Heap.Extends m_chk m1058 := ext_m_954.trans ext_954_1058
      have hty_out_def := Core.Scope.validatedAnnotation_positional
        hnlvls hty_tmc_m hty_ann hty_def ev861
      have hval_out_def := Core.Scope.validatedAnnotation_positional
        hnlvls (Core.TmC.mono ev861.heap_extends hval_tmc_m) hval_ann hval_def ev898
      have hty_tmc_954 := Core.TmC.mono ext_m_954 hty_tmc_m
      have hval_tmc_1058 := Core.TmC.mono ext_m_1058 hval_tmc_m
      intro hn
      exact .opaqueDecl hdecl_not_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann
          hty_out_def hval_out_def
          hm962 hty_tmc_954 (Core.RCRep.mono ext_m_954 hrc_m) ev935 hcl_es hsub_es
          ext_923_1058 hm1066 (Core.TmC.mono ext_954_1058 hty_tmc_954) hval_tmc_1058
          (Core.RCRep.mono ext_m_1058 hrc_m) ev1031 hcl_kc hsub_kc

variable {E₀ : Ixon.Env}

/-- **A block member checked at a limit has its projection record in the run's store, at the
member's constant address**: `mutsMember_record` for a check at either kind of role context. -/
theorem memberCheckedLimAt_record (hbound : Bounded calls) (hS : RunStore calls E₀)
    (hcov : HashedRecordsStored calls E₀) {bAddr B : _root_.Address}
    {ms : Array Ixon.MutConst} {k : Nat} {mc : Ixon.MutConst} {lim : Option Nat}
    (hm : Claim.MemberCheckedLimAt calls bAddr t B ms k lim) (hk : ms[k]? = some mc) :
    k < UInt64.size ∧
      Ix.Cert.recordAt E₀ (memberAddr B k mc) = some (memberProjection B k mc) := by
  obtain ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmem, hblk, ev_pa, hcl_pa, hsub_pa,
    hrc_pre, hrc_m, ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hm
  have hlen : ms.toList.length < 2 ^ 39 :=
    RomBound.bounded_length_lt hbound hcl_pa (List.Mem.head _) hmem
  have hk_lt : k < ms.toList.length := by
    have hk_sz : k < ms.size := (Array.getElem?_eq_some_iff.mp hk).1
    simpa using hk_sz
  have hk_val : ((k : F)).val = k :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  obtain ⟨b', hb', rfl⟩ := hblk
  obtain ⟨-, -, -, mc', a', hget', ha', hproj, hhashed⟩ :=
    Ingress.projection_addr_hashed_spec hmem hb' ev_pa
  rw [hk_val] at hget' hproj hhashed
  have hget_list : ms.toList[k]? = some mc := by simpa using hk
  rw [hget_list] at hget'
  cases hget'
  have haddr : Core.BaseSeams.addr h_pre ap (memberAddr (Core.ixAddr b') k mc) :=
    ⟨a', ha', hproj.trans (memberAddr_eq_projAddr _ k mc).symm⟩
  obtain ⟨c, hrec⟩ := recordAt_of_get_ci hcov haddr ev_ld hsub_ld
  have hwf : (memberProjection (Core.ixAddr b') k mc).wireWF := by
    cases mc with
    | defn d => exact Ingress.projConstant_wireWF_dPrj k.toUInt64 b'
    | indc ind => exact Ingress.projConstant_wireWF_iPrj k.toUInt64 b'
    | recr rc => exact Ingress.projConstant_wireWF_rPrj k.toUInt64 b'
  have hdx := Ixon.Verify.deConstantExact_serConstant _ hwf
  have hhashed' : Hashed calls (Ixon.serConstant (memberProjection (Core.ixAddr b') k mc)) := by
    have hrun := Core.hashed_mono hsub_pa hhashed
    cases mc <;> exact hrun
  have hc_eq : memberProjection (Core.ixAddr b') k mc = c :=
    hS.record_eq hrec hhashed' rfl hdx
  rw [← hc_eq] at hrec
  refine ⟨?_, hrec⟩
  show k < 18446744073709551616
  omega

end IxVM.Refinement.LoadedReads

namespace IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Obs
open IxVM.Consistency

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E₀ : Ixon.Env}

private theorem toUInt64_toNat_v {n : Nat} (hn : n < UInt64.size) : n.toUInt64.toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

/-- **A block member checked at a limit is checked at its constant address, at the same
limit**, at either kind of role context. -/
theorem memberCheckedLimAt_checkedLimAt (hbound : Bounded calls) {bAddr B : _root_.Address}
    {ms : Array Ixon.MutConst} {k : Nat} {mc : Ixon.MutConst} {lim : Option Nat}
    (hm : Claim.MemberCheckedLimAt calls bAddr t B ms k lim) (hk : ms[k]? = some mc) :
    Claim.CheckedLimAt calls bAddr t (memberAddr B k mc) lim := by
  obtain ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmem, hblk, ev_pa, hcl_pa, hsub_pa,
    hrc_pre, hrc_m, ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hm
  have hlen : ms.toList.length < 2 ^ 39 :=
    RomBound.bounded_length_lt hbound hcl_pa (List.Mem.head _) hmem
  have hk_lt : k < ms.toList.length := by
    have hk_sz : k < ms.size := (Array.getElem?_eq_some_iff.mp hk).1
    simpa using hk_sz
  have hk_val : ((k : F)).val = k :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  obtain ⟨b', hb', rfl⟩ := hblk
  obtain ⟨-, -, -, mc', a', hget', ha', hproj, hhashed⟩ :=
    Ingress.projection_addr_hashed_spec hmem hb' ev_pa
  rw [hk_val] at hget' hproj hhashed
  have hget_list : ms.toList[k]? = some mc := by simpa using hk
  rw [hget_list] at hget'
  cases hget'
  have haddr : Core.BaseSeams.addr h_pre ap (memberAddr (Core.ixAddr b') k mc) :=
    ⟨a', ha', hproj.trans (LoadedReads.memberAddr_eq_projAddr _ k mc).symm⟩
  exact ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    hrc_pre, hrc_m, haddr, Core.BaseSeams.addr_mono ev_ld.heap_extends haddr,
    ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩

/-- **A checked standalone definition, theorem or opaque record, at the actual limit of its
check**: the canonical reading, the check evidence and the reload, from the walk's check at
either kind of role context. `checkedLimAt_defn_step` for every kind of a definition record. -/
theorem checkedLimAt_value_step (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) {bAddr a : _root_.Address}
    {order_role : List _root_.Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (hrec : Ix.Cert.recordAt E₀ a = some c) (hinfo : c.info = .defn d) (hlogic : InLogic c)
    (hnot_role : a ∉ order_role) {lim : Option Nat}
    (hchk : Claim.CheckedLimAt calls bAddr t a lim)
    (Ecore : Ixon.Env) {env : Ix.Kernel.Env .anon} (hstored : Decl.UsedRefsStored t env c) :
    ∃ (ty₀ val₀ ty' val' : Ix.Kernel.Expr .anon),
      Annotates ty' ty₀ ∧ Annotates val' val₀ ∧
      ∀ hn : Ix.Kernel.ReducibilityHint,
        Decl.CheckedValueAtLim (Core.Ctx.stored ⟨Ecore, env, t, lim⟩).κ lim calls t
          bAddr Ecore order_role
          (LoadedReads.defnDecl d.kind ⟨Core.keyOf t a, List.range d.lvls.toNat, ty₀⟩ val₀ hn)
          (LoadedReads.defnDecl d.kind ⟨Core.keyOf t a, List.range d.lvls.toNat, ty'⟩ val'
            hn) ∧
        Reads t E₀ a
          (LoadedReads.defnConst d.kind ⟨keyOf t a, List.range d.lvls.toNat, ty₀⟩ val₀ hn) ∧
        ∀ E' : Ixon.Env, recordOf E' a = some c →
          (∀ x b, E₀.blobs.get? x = some b → E'.blobs.get? x = some b) →
          ∀ cn ∈ IxVM.Consistency.installs
              (LoadedReads.defnDecl d.kind ⟨Core.keyOf t a, List.range d.lvls.toNat, ty'⟩ val'
                hn),
            Decl.ReloadsAs E' t ⟨cn :: env.consts⟩ cn := by
  have hsafe : Ix.Kernel.Reader.safetyDecline d = none := by
    have hl := hlogic
    unfold InLogic at hl
    rw [hinfo] at hl
    exact hl
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    hrc_pre, hrc_m, ha_pre, ha_m, ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hchk
  obtain ⟨a', ha'_ref, rfl⟩ := ha_pre
  obtain ⟨rawBytes, c', hh, hba, hex, hres⟩ := Ingress.get_ci_trace_spec ha'_ref ev_ld
  have hc : c = c' := (hS.record_eq hrec (Core.hashed_mono hsub_ld hh) hba hex).symm
  subst hc
  unfold Ingress.GetCITraceResult at hres
  rw [hinfo] at hres
  obtain ⟨blobs, tree, v', hhp, built, hld', htr⟩ := hres
  rw [hld] at hld'
  injection hld' with hvv
  subst hvv
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hhx' : Hashed cs_load bs := hhx
    have hxa' : Address.blake3Pure bs = x := hxa
    have hrun := hS.blobs bs (Core.hashed_mono hsub_ld hhx')
    rw [hxa'] at hrun
    exact hrun
  obtain ⟨raw', ty₀, val₀, hty, hval, hreads, -⟩ :=
    LoadedReads.defn_reading (store := recordOf E₀) (blob := fun x => E₀.blobs.get? x) ht
      (hS.recordOf_of_recordAt hrec) hinfo hlogic hblob htr.toRaw
  obtain ⟨h1, h2, h3, h4⟩ :=
    LoadedReads.checkedValue_scope_lim ht hbound hsafe hblob raw' hty hval ev_chk hsub_chk
  have hrecur : Ingress.defnRecurAddrs d (Core.ixAddr a') = [] := by
    have hf := (Ingress.defnIsUnsafeCI_eq_false_iff d).mpr hsafe
    simp [Ingress.defnRecurAddrs, hf]
  rw [hrecur] at htr
  obtain ⟨hnlvls, tyPtr, valPtr, hint, planT, planV, hv, rty, rval, hpT, hpV, hlT, hlV⟩ := htr
  subst hv
  have hagree : Ingress.BlobReadAgreement (readCtx t (fun x => E₀.blobs.get? x)).blob blobs :=
    Ingress.BlobReadAgreement.of_mem hblob
  obtain ⟨ty', hcT, hannT, htmT⟩ :=
    LoadedReads.annotation_canon ht hnlvls hagree rty built hpT hlT hty h1 h2
  obtain ⟨val', hcV, hannV, htmV⟩ :=
    LoadedReads.annotation_canon ht hnlvls hagree rval built hpV hlV hval h3 h4
  have heT : ∀ i, i ∈ exprRefIdxs d.typ → i ∈ usedRefIdxs c := by
    intro i hi
    unfold usedRefIdxs
    rw [hinfo]
    exact List.mem_append_right _ (List.mem_append_left _ hi)
  have heV : ∀ i, i ∈ exprRefIdxs d.value → i ∈ usedRefIdxs c := by
    intro i hi
    unfold usedRefIdxs
    rw [hinfo]
    exact List.mem_append_right _ (List.mem_append_right _ hi)
  have htmT' := Decl.tmC_stored_of_usedRefs (E₀ := Ecore) (lim := lim) rty heT hstored htmT
  have htmV' := Decl.tmC_stored_of_usedRefs (E₀ := Ecore) (lim := lim) rval heV hstored htmV
  refine ⟨ty₀, val₀, ty', val', hannT, hannV, fun hn => ⟨?_, hreads hn, ?_⟩⟩
  · exact LoadedReads.checkedValue_at_lim (E := Ecore) (order_role := order_role)
      (decl_addr := Core.ixAddr a') hnot_role hsafe hrc_m.toRCRep hnlvls h1 h2 h3 h4 hannT
      hannV htmT' htmV' ev_chk hsub_chk hn
  · intro E' hrec' hblobs cn hcn
    rw [LoadedReads.installs_defnDecl] at hcn
    have hcn' : cn = LoadedReads.defnConst d.kind
        ⟨Core.keyOf t (Core.ixAddr a'), List.range d.lvls.toNat, ty'⟩ val' hn :=
      List.mem_singleton.mp hcn
    subst hcn'
    exact LoadedReads.reloadsAs_defn_cons ht hrec' hinfo hlogic hblobs hty hval h1 h2 h3 h4
      hstored (LoadedReads.canonDefn_eq hcT hcV)

/-- **A checked member of a definition block, at the actual limit of its check**: the canonical
reading, the check evidence and the reload, from the walk's check of member `k` at either kind
of role context. `mutsMemberAt_defn_step` with the limit an `Option Nat`. -/
theorem memberCheckedLimAt_value_step (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hcov : LoadedReads.HashedRecordsStored calls E₀)
    {bAddr B : _root_.Address} {order_role : List _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {k : Nat} {d : Ixon.Definition}
    (hrecB : Ix.Cert.recordAt E₀ B = some cb) (hmuts : cb.info = .muts ms)
    (hk : ms[k]? = some (.defn d)) (hlogic : InLogic cb)
    (hnot_role : memberAddr B k (.defn d) ∉ order_role) {lim : Option Nat}
    (hm : Claim.MemberCheckedLimAt calls bAddr t B ms k lim)
    (Ecore : Ixon.Env) {env : Ix.Kernel.Env .anon} (hstored : Decl.UsedRefsStored t env cb) :
    ∃ (ty₀ val₀ ty' val' : Ix.Kernel.Expr .anon),
      Annotates ty' ty₀ ∧ Annotates val' val₀ ∧
      ∀ hn : Ix.Kernel.ReducibilityHint,
        Decl.CheckedValueAtLim (Core.Ctx.stored ⟨Ecore, env, t, lim⟩).κ lim calls t
          bAddr Ecore order_role
          (LoadedReads.defnDecl d.kind
            ⟨Core.keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty₀⟩ val₀ hn)
          (LoadedReads.defnDecl d.kind
            ⟨Core.keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty'⟩ val' hn) ∧
        Reads t E₀ (memberAddr B k (.defn d))
          (LoadedReads.defnConst d.kind
            ⟨keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty₀⟩ val₀ hn) ∧
        ∀ E' : Ixon.Env,
          recordOf E' (memberAddr B k (.defn d)) = some (memberProjection B k (.defn d)) →
          recordOf E' B = some cb →
          (∀ x b, E₀.blobs.get? x = some b → E'.blobs.get? x = some b) →
          ∀ cn ∈ IxVM.Consistency.installs
              (LoadedReads.defnDecl d.kind
                ⟨Core.keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty'⟩ val'
                hn),
            Decl.ReloadsAs E' t ⟨cn :: env.consts⟩ cn := by
  obtain ⟨hk64, hrec⟩ := LoadedReads.memberCheckedLimAt_record hbound hS hcov hm hk
  have hchk := memberCheckedLimAt_checkedLimAt hbound hm hk
  have hmem' : Ixon.MutConst.defn d ∈ ms.toList :=
    List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hk)
  have hsafe : Ix.Kernel.Reader.safetyDecline d = none := by
    have hl := hlogic
    unfold InLogic at hl
    rw [hmuts] at hl
    exact hl (.defn d) hmem'
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    hrc_pre, hrc_m, ha_pre, ha_m, ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hchk
  obtain ⟨a', ha'_ref, haddr⟩ := ha_pre
  obtain ⟨rawBytes, c', hh, hba, hex, hres⟩ := Ingress.get_ci_trace_spec ha'_ref ev_ld
  have hc : memberProjection B k (.defn d) = c' :=
    (hS.record_eq hrec (Core.hashed_mono hsub_ld hh) (hba.trans haddr) hex).symm
  subst hc
  have hinfo : (memberProjection B k (.defn d)).info = .dPrj ⟨k.toUInt64, B⟩ := rfl
  unfold Ingress.GetCITraceResult at hres
  rw [hinfo] at hres
  obtain ⟨hidx, blkBytes, cb', ms', d', blobs, tree, v', hhB, haB, hexB, hcb, hms, hhp, built,
    hld', htr⟩ := hres
  have hcb_eq : cb = cb' :=
    (hS.record_eq hrecB (Core.hashed_mono hsub_ld hhB) haB hexB).symm
  subst hcb_eq
  have hms_eq : ms = ms' := Ixon.ConstantInfo.muts.inj (hmuts.symm.trans hcb)
  subst hms_eq
  have hms' : ms[k.toUInt64.toNat]? = some (.defn d') := by
    rw [← Array.getElem?_toList]
    exact hms
  rw [toUInt64_toNat_v hk64] at hms'
  have hd : d = d' := Ixon.MutConst.defn.inj (Option.some.inj (hk.symm.trans hms'))
  subst hd
  rw [hld] at hld'
  injection hld' with hvv
  subst hvv
  have htr' : Ingress.DefnTraceRep cb.refs.toList (Ingress.defnMemberRecurAddrs d B ms.toList)
      cb.univs.toList cb.sharing.toList blobs tree
      ((Ingress.mutsRootOffset ms.toList k.toUInt64.toNat : Nat) : F) m_chk d v := htr
  rw [toUInt64_toNat_v hk64] at htr'
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hhx' : Hashed cs_load bs := hhx
    have hxa' : Address.blake3Pure bs = x := hxa
    have hrun := hS.blobs bs (Core.hashed_mono hsub_ld hhx')
    rw [hxa'] at hrun
    exact hrun
  obtain ⟨raw', ty₀, val₀, hty, hval, hreads, -⟩ :=
    LoadedReads.dprj_reading (store := recordOf E₀) (blob := fun x => E₀.blobs.get? x) ht hk64
      (hS.recordOf_of_recordAt hrecB) hmuts hk hlogic (hS.recordOf_of_recordAt hrec) hblob
      htr'.toRaw
  obtain ⟨h1, h2, h3, h4⟩ :=
    LoadedReads.checkedValue_scope_lim ht hbound hsafe hblob raw' hty hval ev_chk hsub_chk
  have hrecur : Ingress.defnMemberRecurAddrs d B ms.toList = [] := by
    have hf := (Ingress.defnIsUnsafeCI_eq_false_iff d).mpr hsafe
    simp [Ingress.defnMemberRecurAddrs, hf]
  rw [hrecur] at htr'
  obtain ⟨hnlvls, tyPtr, valPtr, hint, planT, planV, hv, rty, rval, hpT, hpV, hlT, hlV⟩ := htr'
  subst hv
  have hagree : Ingress.BlobReadAgreement (readCtx t (fun x => E₀.blobs.get? x)).blob blobs :=
    Ingress.BlobReadAgreement.of_mem hblob
  obtain ⟨ty', hcT, hannT, htmT⟩ :=
    LoadedReads.annotation_canon ht hnlvls hagree rty built hpT hlT hty h1 h2
  obtain ⟨val', hcV, hannV, htmV⟩ :=
    LoadedReads.annotation_canon ht hnlvls hagree rval built hpV hlV hval h3 h4
  have hused : ∀ i, i ∈ exprRefIdxs d.typ ++ exprRefIdxs d.value → i ∈ usedRefIdxs cb := by
    intro i hi
    unfold usedRefIdxs
    rw [hmuts]
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨.defn d, hmem', hi⟩)
  have htmT' := Decl.tmC_stored_of_usedRefs (E₀ := Ecore) (lim := lim) rty
    (fun i hi => hused i (List.mem_append_left _ hi)) hstored htmT
  have htmV' := Decl.tmC_stored_of_usedRefs (E₀ := Ecore) (lim := lim) rval
    (fun i hi => hused i (List.mem_append_right _ hi)) hstored htmV
  refine ⟨ty₀, val₀, ty', val', hannT, hannV, fun hn => ⟨?_, hreads hn, ?_⟩⟩
  · exact LoadedReads.checkedValue_at_lim (E := Ecore) (order_role := order_role)
      (decl_addr := memberAddr B k (.defn d)) hnot_role hsafe hrc_m.toRCRep hnlvls h1 h2 h3 h4
      hannT hannV htmT' htmV' ev_chk hsub_chk hn
  · intro E' hproj' hblock' hblobs cn hcn
    rw [LoadedReads.installs_defnDecl] at hcn
    have hcn' : cn = LoadedReads.defnConst d.kind
        ⟨Core.keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty'⟩ val' hn :=
      List.mem_singleton.mp hcn
    subst hcn'
    exact LoadedReads.reloadsAs_member_cons ht hk64 hproj' hblock' hmuts hk hlogic hblobs hty
      hval h1 h2 h3 h4 hstored (LoadedReads.canonDefn_eq hcT hcV)

end IxVM.Refinement.Typing
