import IxVMRefinement.Decl.DeclSpecs
import IxVMRefinement.Assembly.Bridge
import IxVMRefinement.Assembly.LoadGlue
import IxVMRefinement.Assembly.RoleFacts

/-!
# Walked Constant Declaration Steps (`DeclWalkedConst.lean`)

Proves one-step advancement of `FullDeclInv` and `CleanInstallStep` (hence
`IxVM.Consistency.InstallStep`) across walked non-role constant declarations
(`Assembly.CheckedConstOrigin`: `.axiomDecl`, `.defnDecl`, `.thmDecl`, `.opaqueDecl`) as well as
quotient, basis, and pinned inductive declarations (`.quotDecl`, `.basisDecl`, `.indDecl`),
parameterized over the context-facts bundle `FoldContextFacts E_core t env`, together with a
total structural zeta-erasure fallback `dummyInstallStep` for vacuous-invariant prefixes.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Library Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel
open Ix.Kernel.Model
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal Declaration
  BasisKind QuotKind ReducibilityHint LevelParam)
open Ix.Kernel.Rules (Annot Red DefEq Infer)

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u

/-! ## Store and Role-Table Context Bundle for Walked Steps -/

/-- Minimal store and role-table context invariant bundle supplying `Core.EnvFacts` (via
`FoldEnvCompanions`) and `Core.LoadFacts` on `⟨E_core, env, t, lim⟩` whenever `FoldStoreInv env`
holds. -/
structure FoldContextFacts (E_core : Ixon.Env) (t : Ix.Kernel.RoleTable)
    (env : Env .anon) : Prop where
  tableWf : t.wf = true
  envCompanions : FoldStoreInv env → ∀ lim : Option Nat,
    FoldEnvCompanions ⟨E_core, env, t, lim⟩
  loadFacts : FoldStoreInv env → ∀ lim : Option Nat,
    LoadFacts ⟨E_core, env, t, lim⟩

/-- Assemble `Core.EnvFacts ⟨E_core, env, t, lim⟩` from `FoldContextFacts` and `FoldStoreInv`. -/
theorem FoldContextFacts.envFacts {E_core : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {env : Env .anon} (hctx : FoldContextFacts E_core t env) (hS : FoldStoreInv env)
    (lim : Option Nat) :
    EnvFacts ⟨E_core, env, t, lim⟩ :=
  hS.toEnvFacts hctx.tableWf (hctx.envCompanions hS lim)

/-- Assemble `CoreFacts ⟨E_core, env, t, lim⟩` from `FoldContextFacts` and `FoldStoreInv`. -/
theorem FoldContextFacts.coreFacts {E_core : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {env : Env .anon} (hctx : FoldContextFacts E_core t env) (hS : FoldStoreInv env)
    (lim : Option Nat) :
    CoreFacts ⟨E_core, env, t, lim⟩ :=
  ⟨hctx.envFacts hS lim, hctx.loadFacts hS lim⟩

/-! ## Non-role Key Facts (`a ∉ order_role`) -/

private def isNonCompilerTrustRole : KKey → Bool
  | .role r => !IxVM.Refinement.compilerTrust r
  | _ => false

private theorem contains_false_of_all_nonCompilerTrust :
    ∀ (L : List KKey), L.all isNonCompilerTrustRole = true →
      ∀ {k : KKey}, (∀ r : Ix.Kernel.Role, IxVM.Refinement.compilerTrust r = false → k ≠ .role r) →
      L.contains k = false
  | [], _, _, _ => rfl
  | x :: xs, hall, k, hne => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    simp only [List.contains, List.elem]
    cases hbeq : (k == x) with
    | true =>
      have hk : k = x := beq_iff_eq.mp hbeq
      subst hk
      cases k with
      | role r =>
        simp only [isNonCompilerTrustRole, Bool.not_eq_true'] at hall
        exact absurd rfl (hne r hall.1)
      | id _ => exact nomatch hall.1
      | aux _ _ => exact nomatch hall.1
    | false =>
      exact contains_false_of_all_nonCompilerTrust xs hall.2 hne

private theorem reservedBasisNames_all_nonCompilerTrust :
    (Ix.Kernel.reservedBasisNames : List KKey).all isNonCompilerTrustRole = true := by
  decide

private theorem natOpNames_all_nonCompilerTrust :
    (Ix.Kernel.natOpNames : List KKey).all isNonCompilerTrustRole = true := by
  decide

private theorem natDivModNames_all_nonCompilerTrust :
    (Ix.Kernel.natDivModNames : List KKey).all isNonCompilerTrustRole = true := by
  decide

theorem reservedBasisNames_false_of_ne_nonTrustRole {k : KKey}
    (hne : ∀ r : Ix.Kernel.Role, IxVM.Refinement.compilerTrust r = false → k ≠ .role r) :
    Ix.Kernel.reservedBasisNames.contains k = false :=
  contains_false_of_all_nonCompilerTrust _ reservedBasisNames_all_nonCompilerTrust hne

theorem natOpNames_false_of_ne_nonTrustRole {k : KKey}
    (hne : ∀ r : Ix.Kernel.Role, IxVM.Refinement.compilerTrust r = false → k ≠ .role r) :
    Ix.Kernel.natOpNames.contains k = false :=
  contains_false_of_all_nonCompilerTrust _ natOpNames_all_nonCompilerTrust hne

theorem natDivModNames_false_of_ne_nonTrustRole {k : KKey}
    (hne : ∀ r : Ix.Kernel.Role, IxVM.Refinement.compilerTrust r = false → k ≠ .role r) :
    Ix.Kernel.natDivModNames.contains k = false :=
  contains_false_of_all_nonCompilerTrust _ natDivModNames_all_nonCompilerTrust hne

/-! ## Closed Term Representation -/

private theorem tm_noLetExpr {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
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

private theorem tmC_closed_props {κ : _root_.Address → KKey} {h : Heap F}
    {e : KExpr} {p : SourceValue F} (rep : TmC κ h e p) :
    noLetExpr e = true ∧ e.hasFvar = false ∧ e.looseBVarsBounded 0 = true ∧
      Annot 0 e e := by
  have h0 : Tm κ 0 (fun _ => .sort .zero) h 0 e p := rep 0 (fun _ => .sort .zero)
  have hnl : noLetExpr e = true :=
    tm_noLetExpr (fun _ hlt => absurd hlt (Nat.not_lt_zero _)) h0
  have hfv : e.hasFvar = false := Tm.hasFvar_false h0
  have hbvs : e.looseBVarsBounded 0 = true := Tm.looseBVarsBounded h0
  exact ⟨hnl, hfv, hbvs, annot_refl_of_noLetExpr hnl hfv hbvs 0⟩

private theorem rcFullRep_axiomsNil {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Nat} {h : Heap F} {rc : SourceValue F}
    (hrc : Claim.RCFullRep t bAddr lim h rc) :
    RCAxiomsNil h rc := by
  obtain ⟨_, tbl, hl, _⟩ := hrc
  exact ⟨_, hl, Or.inl ⟨tbl, .field (lim : F), rfl⟩⟩

private def zeroGhostWalked : Nat → KExpr := fun _ => .sort .zero

private theorem typesRep_of_nil_eq (κ : _root_.Address → KKey) {m m_pre : Heap F}
    (hm : m = m_pre ++ [.construct kexprListEnum "Nil" []]) :
    TypesRep κ zeroGhostWalked m 0 (.ptr (.enum kexprListEnum) m_pre.length) := by
  rw [hm]
  exact typesRep_alloc_nil κ zeroGhostWalked m_pre

/-! ## Walked Constant Step (`CheckedConstOrigin`) -/

/-- One-step advancement of `CleanInstallStep` and `FullDeclInv` across a walked constant
declaration `d` (`Assembly.CheckedConstOrigin`). -/
theorem checkedConstOrigin_step
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {E_core : Ixon.Env} {order_role : List _root_.Address}
    {env : Env .anon} {d : Declaration .anon}
    (hchk : Assembly.CheckedConstOrigin calls t bAddr E_core order_role d)
    (hctx : FoldContextFacts E_core t env)
    (hgood : Good ⟨E_core, env, t, none⟩ calls)
    (hbound : IxVM.Consistency.Bounded calls)
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs d, env.find? ci₀.name = none)
    (hne_role : ∀ a, a ∉ order_role →
      ∀ r : Ix.Kernel.Role, IxVM.Refinement.compilerTrust r = false → keyOf t a ≠ .role r) :
    ∃ env₂, CleanInstallStep env d env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], FullDeclInv V env → FullDeclInv V env₂ := by
  cases hchk with
  | @axiomDecl a _ _ nlvls ty₀ ty' lim _ _ _ m_ax _ x_rc _ x_addr _ v_ax _ cs_ax
      hnot_role _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrc_ax ha_ax ev_ax hne_ax _ hsub_ax =>
    let cv₀ : ConstantVal .anon := ⟨keyOf t a, List.range nlvls, ty₀⟩
    by_cases hskip : cv₀.name = Ix.Kernel.quotSoundName ∨ IxVM.Consistency.inertKey cv₀.name = true
    · have hempty : IxVM.Consistency.installs (.axiomDecl cv₀) = [] := ite_eq_left hskip
      exact ⟨env, CleanInstallStep.empty hempty, fun _ _ h => h⟩
    · obtain ⟨a', ha'_ref, heq_a⟩ := ha_ax
      let c : Ctx := ⟨E_core, env, t, some lim⟩
      have hgood_c : Good c calls := hgood
      obtain ⟨ro, hro_addr, _, hrole⟩ :=
        axiom_standing_spec rolesSpec (hgood_c.sub hsub_ax) hctx.tableWf
          hrc_ax.toRCRep (rcFullRep_axiomsNil hrc_ax) ha'_ref ev_ax hne_ax
      have hk : keyOf t a = .role ro := by
        have hk0 := keyOf_of_addressOf hctx.tableWf hro_addr
        rwa [heq_a] at hk0
      have hct : IxVM.Refinement.compilerTrust ro = false := by
        rcases hrole with rfl | rfl | rfl | hinert
        · rfl
        · rfl
        · rfl
        · exact False.elim (hskip (Or.inr (by
            show IxVM.Consistency.inertKey (keyOf t a) = true
            rw [hk]
            exact hinert)))
      exact False.elim (hne_role a hnot_role ro hct hk)
  | @defnDecl a nlvls ty₀ val₀ ty' val' hn lim m_pre1 m_es m_es' m_pre2 m_kc m_kc'
      x_rc x_ty x_val v_sort r_kc cs_es cs_kc
      hnot_role _ _ hty_def _ hval_def hty_ann hval_ann hty'_def hval'_def
      hm_es hty_tmc_es hrc_es ev_es _ hsub_es
      _ hm_kc hty_tmc_kc hval_tmc_kc hrc_kc ev_kc _ hsub_kc =>
    let cv₀ : ConstantVal .anon := ⟨keyOf t a, List.range nlvls, ty₀⟩
    let cv' : ConstantVal .anon := ⟨keyOf t a, List.range nlvls, ty'⟩
    have hbase : isBaseKey cv₀.name = true := isBaseKey_keyOf t a
    have hfresh_cv : env.find? cv'.name = none :=
      hfresh (.defnInfo cv₀ val₀ hn) (List.mem_singleton.mpr rfl)
    have hstored : IxVM.Consistency.StoredAs (.defnInfo cv' val' hn) (.defnInfo cv₀ val₀ hn) :=
      ⟨⟨rfl, rfl, hty_ann⟩, hval_ann, rfl⟩
    have hclean : CleanInstallStep env (.defnDecl cv₀ val₀ hn) ⟨.defnInfo cv' val' hn :: env.consts⟩ :=
      CleanInstallStep.single rfl hstored hfresh_cv hbase
    refine ⟨⟨.defnInfo cv' val' hn :: env.consts⟩, hclean, fun V _ hInv => ?_⟩
    have hS : FoldStoreInv env := hInv.toFoldStoreInv
    let c : Ctx := ⟨E_core, env, t, some lim⟩
    have hgood_c : Good c calls := hgood
    have hef : EnvFacts c := hctx.envFacts hS (some lim)
    have hlf : LoadFacts c := hctx.loadFacts hS (some lim)
    have hty_tmc_es' : TmC c.κ m_es ty' x_ty := by
      have h := hty_tmc_es
      rwa [posOf_range nlvls ty'] at h
    have hty_tmc_kc' : TmC c.κ m_kc ty' x_ty := by
      have h := hty_tmc_kc
      rwa [posOf_range nlvls ty'] at h
    have hval_tmc_kc' : TmC c.κ m_kc val' x_val := by
      have h := hval_tmc_kc
      rwa [posOf_range nlvls val'] at h
    obtain ⟨_, hty'_nfv, hty'_bvs, hty'_ann⟩ := tmC_closed_props hty_tmc_es'
    obtain ⟨_, hval'_nfv, hval'_bvs, hval'_ann⟩ := tmC_closed_props hval_tmc_kc'
    obtain ⟨stype, u, _, hinf_ty, hred_ty, _, _⟩ :=
      core_ensure_sort Core.core_S₀ hrc_es.toRCRep (typesRep_of_nil_eq c.κ hm_es)
        (ghostScoped_zero zeroGhostWalked) hef hlf (hgood_c.sub hsub_es) ev_es
        (hty_tmc_es' 0 zeroGhostWalked)
    obtain ⟨vtype, hinf_val, hde_val⟩ :=
      core_check Core.core_S₀ hrc_kc.toRCRep (typesRep_of_nil_eq c.κ hm_kc)
        (ghostScoped_zero zeroGhostWalked) hef hlf (hgood_c.sub hsub_kc) ev_kc
        (hval_tmc_kc' 0 zeroGhostWalked) (hty_tmc_kc' 0 zeroGhostWalked)
    have hnrole := hne_role a hnot_role
    have hres : Ix.Kernel.reservedBasisNames.contains cv'.name = false :=
      reservedBasisNames_false_of_ne_nonTrustRole hnrole
    have hnoprj : cv'.name.isProjFnShape = false := isProjFnShape_of_isBaseKey hbase
    have hcv_run : ConstantValRunJ rulesJ env cv' ty' :=
      ⟨by rw [hfresh_cv]; rfl, hres, hnoprj, levelParam_nodup_of_nodup List.nodup_range,
        hty'_bvs, hty'_nfv, hty'_ann, hty'_def,
        infer_constsResolve hinf_ty hef.store hty'_nfv, stype, u, hinf_ty, hred_ty⟩
    have hv_run : ValueFrontRunJ rulesJ env cv' val' ty' val' :=
      ⟨hval'_bvs, hval'_nfv, hval'_ann, hval'_def,
        infer_constsResolve hinf_val hef.store hval'_nfv, vtype, hinf_val, hde_val⟩
    have hnat_false : Ix.Kernel.natOpNames.contains cv'.name = false :=
      natOpNames_false_of_ne_nonTrustRole hnrole
    have hdm_false : Ix.Kernel.natDivModNames.contains cv'.name = false :=
      natDivModNames_false_of_ne_nonTrustRole hnrole
    have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.defnDecl cv' val' hn)
        ⟨.defnInfo cv' val' hn :: env.consts⟩ :=
      ⟨ty', val', hcv_run, hv_run, rfl,
        (fun hc => by rw [hnat_false] at hc; exact nomatch hc),
        (fun hc => by rw [hdm_false] at hc; exact nomatch hc)⟩
    exact FullDeclInv.step_of_foldInv_clean hclean
      (foldInv_step_declRunJ (d := .defnDecl cv' val' hn) (fun _ _ heq => nomatch heq) hdecl) V hInv
  | @thmDecl a nlvls ty₀ val₀ ty' val' lim m_pre1 m_es m_es' m_le m_le' m_pre2 m_kc m_kc'
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
    refine ⟨⟨.thmInfo cv' val' :: env.consts⟩, hclean, fun V _ hInv => ?_⟩
    have hS : FoldStoreInv env := hInv.toFoldStoreInv
    let c : Ctx := ⟨E_core, env, t, some lim⟩
    have hgood_c : Good c calls := hgood
    have hef : EnvFacts c := hctx.envFacts hS (some lim)
    have hlf : LoadFacts c := hctx.loadFacts hS (some lim)
    have hty_tmc_es' : TmC c.κ m_es ty' x_ty := by
      have h := hty_tmc_es
      rwa [posOf_range nlvls ty'] at h
    have hty_tmc_kc' : TmC c.κ m_kc ty' x_ty := by
      have h := hty_tmc_kc
      rwa [posOf_range nlvls ty'] at h
    have hval_tmc_kc' : TmC c.κ m_kc val' x_val := by
      have h := hval_tmc_kc
      rwa [posOf_range nlvls val'] at h
    obtain ⟨_, hty'_nfv, hty'_bvs, hty'_ann⟩ := tmC_closed_props hty_tmc_es'
    obtain ⟨_, hval'_nfv, hval'_bvs, hval'_ann⟩ := tmC_closed_props hval_tmc_kc'
    obtain ⟨stype, u, ℓ, hinf_ty, hred_ty, hℓ, hu⟩ :=
      core_ensure_sort Core.core_S₀ hrc_es.toRCRep (typesRep_of_nil_eq c.κ hm_es)
        (ghostScoped_zero zeroGhostWalked) hef hlf (hgood_c.sub hsub_es) ev_es
        (hty_tmc_es' 0 zeroGhostWalked)
    have hisZero : (rulesJ (md := .anon)).isZero u :=
      thm_isZero_of_level_equal Levels.l2
        (RomBound.bounded_mono hbound hsub_le) hℓ hu hm_le ev_le
    obtain ⟨vtype, hinf_val, hde_val⟩ :=
      core_check Core.core_S₀ hrc_kc.toRCRep (typesRep_of_nil_eq c.κ hm_kc)
        (ghostScoped_zero zeroGhostWalked) hef hlf (hgood_c.sub hsub_kc) ev_kc
        (hval_tmc_kc' 0 zeroGhostWalked) (hty_tmc_kc' 0 zeroGhostWalked)
    have hnrole := hne_role a hnot_role
    have hres : Ix.Kernel.reservedBasisNames.contains cv'.name = false :=
      reservedBasisNames_false_of_ne_nonTrustRole hnrole
    have hnoprj : cv'.name.isProjFnShape = false := isProjFnShape_of_isBaseKey hbase
    have hcv_run : ConstantValRunJ rulesJ env cv' ty' :=
      ⟨by rw [hfresh_cv]; rfl, hres, hnoprj, levelParam_nodup_of_nodup List.nodup_range,
        hty'_bvs, hty'_nfv, hty'_ann, hty'_def,
        infer_constsResolve hinf_ty hef.store hty'_nfv, stype, u, hinf_ty, hred_ty⟩
    have hv_run : ValueFrontRunJ rulesJ env cv' val' ty' val' :=
      ⟨hval'_bvs, hval'_nfv, hval'_ann, hval'_def,
        infer_constsResolve hinf_val hef.store hval'_nfv, vtype, hinf_val, hde_val⟩
    have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.thmDecl cv' val')
        ⟨.thmInfo cv' val' :: env.consts⟩ :=
      ⟨ty', val', hcv_run, ⟨stype, u, hinf_ty, hred_ty, hisZero⟩, hv_run, rfl⟩
    exact FullDeclInv.step_of_foldInv_clean hclean
      (foldInv_step_declRunJ (d := .thmDecl cv' val') (fun _ _ heq => nomatch heq) hdecl) V hInv
  | @opaqueDecl a nlvls ty₀ val₀ ty' val' lim m_pre1 m_es m_es' m_pre2 m_kc m_kc'
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
    refine ⟨⟨.axiomInfo cv' :: env.consts⟩, hclean, fun V _ hInv => ?_⟩
    have hS : FoldStoreInv env := hInv.toFoldStoreInv
    let c : Ctx := ⟨E_core, env, t, some lim⟩
    have hgood_c : Good c calls := hgood
    have hef : EnvFacts c := hctx.envFacts hS (some lim)
    have hlf : LoadFacts c := hctx.loadFacts hS (some lim)
    have hty_tmc_es' : TmC c.κ m_es ty' x_ty := by
      have h := hty_tmc_es
      rwa [posOf_range nlvls ty'] at h
    have hty_tmc_kc' : TmC c.κ m_kc ty' x_ty := by
      have h := hty_tmc_kc
      rwa [posOf_range nlvls ty'] at h
    have hval_tmc_kc' : TmC c.κ m_kc val' x_val := by
      have h := hval_tmc_kc
      rwa [posOf_range nlvls val'] at h
    obtain ⟨_, hty'_nfv, hty'_bvs, hty'_ann⟩ := tmC_closed_props hty_tmc_es'
    obtain ⟨_, hval'_nfv, hval'_bvs, hval'_ann⟩ := tmC_closed_props hval_tmc_kc'
    obtain ⟨stype, u, _, hinf_ty, hred_ty, _, _⟩ :=
      core_ensure_sort Core.core_S₀ hrc_es.toRCRep (typesRep_of_nil_eq c.κ hm_es)
        (ghostScoped_zero zeroGhostWalked) hef hlf (hgood_c.sub hsub_es) ev_es
        (hty_tmc_es' 0 zeroGhostWalked)
    obtain ⟨vtype, hinf_val, hde_val⟩ :=
      core_check Core.core_S₀ hrc_kc.toRCRep (typesRep_of_nil_eq c.κ hm_kc)
        (ghostScoped_zero zeroGhostWalked) hef hlf (hgood_c.sub hsub_kc) ev_kc
        (hval_tmc_kc' 0 zeroGhostWalked) (hty_tmc_kc' 0 zeroGhostWalked)
    have hnrole := hne_role a hnot_role
    have hres : Ix.Kernel.reservedBasisNames.contains cv'.name = false :=
      reservedBasisNames_false_of_ne_nonTrustRole hnrole
    have hnoprj : cv'.name.isProjFnShape = false := isProjFnShape_of_isBaseKey hbase
    have hcv_run : ConstantValRunJ rulesJ env cv' ty' :=
      ⟨by rw [hfresh_cv]; rfl, hres, hnoprj, levelParam_nodup_of_nodup List.nodup_range,
        hty'_bvs, hty'_nfv, hty'_ann, hty'_def,
        infer_constsResolve hinf_ty hef.store hty'_nfv, stype, u, hinf_ty, hred_ty⟩
    have hv_run : ValueFrontRunJ rulesJ env cv' val' ty' val' :=
      ⟨hval'_bvs, hval'_nfv, hval'_ann, hval'_def,
        infer_constsResolve hinf_val hef.store hval'_nfv, vtype, hinf_val, hde_val⟩
    have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.opaqueDecl cv' val')
        ⟨.axiomInfo cv' :: env.consts⟩ :=
      ⟨ty', val', hcv_run, hv_run, rfl⟩
    exact FullDeclInv.step_of_foldInv_clean hclean
      (foldInv_step_declRunJ (d := .opaqueDecl cv' val') (fun _ _ heq => nomatch heq) hdecl) V hInv

/-! ## Quotient, Basis, and Pinned Inductive Steps in `FullDeclInv` -/

/-- Step preservation for `.quotDecl k cv` in `FullDeclInv`. -/
theorem quotDecl_step_full {env : Env .anon} {k : QuotKind} {cv : ConstantVal .anon}
    (heq_stored : k = .type → env.find? Ix.Kernel.eqName = some (Ix.Kernel.eqA (md := .anon)))
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs (.quotDecl k cv), env.find? ci₀.name = none) :
    ∃ env₂, CleanInstallStep env (.quotDecl k cv) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], FullDeclInv V env → FullDeclInv V env₂ := by
  cases k with
  | type =>
    obtain ⟨hrun, hinst⟩ := basis_step_of_fresh (d := .quotDecl .type cv) .quotK rfl
      (fun _ => heq_stored rfl) hfresh
    have hbase : ∀ ci ∈ (BasisKind.quotK.declsA (md := .anon)).reverse, isBaseKey ci.name = true := by
      intro ci hci
      exact List.all_eq_true.mp (basis_declsA_isBaseKey .quotK) ci (List.mem_reverse.mp hci)
    have hclean : CleanInstallStep env (.quotDecl .type cv)
        ⟨BasisKind.quotK.declsA.reverse ++ env.consts⟩ :=
      CleanInstallStep.of_baseList hinst hbase
    have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.quotDecl .type cv)
        ⟨BasisKind.quotK.declsA.reverse ++ env.consts⟩ := hrun
    exact ⟨⟨BasisKind.quotK.declsA.reverse ++ env.consts⟩, hclean,
      fun V _ hInv => FullDeclInv.step_of_foldInv_clean hclean
        (foldInv_step_declRunJ (d := .quotDecl .type cv) (fun _ _ heq => nomatch heq) hdecl) V hInv⟩
  | ctor => exact ⟨env, CleanInstallStep.empty rfl, fun _ _ h => h⟩
  | lift => exact ⟨env, CleanInstallStep.empty rfl, fun _ _ h => h⟩
  | ind => exact ⟨env, CleanInstallStep.empty rfl, fun _ _ h => h⟩
  | sound => exact ⟨env, CleanInstallStep.empty rfl, fun _ _ h => h⟩

/-- Step preservation for `.basisDecl kind` in `FullDeclInv`. -/
theorem basisDecl_step_full {env : Env .anon} {kind : BasisKind}
    (heq_stored : kind = .quotK → env.find? Ix.Kernel.eqName = some (Ix.Kernel.eqA (md := .anon)))
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs (.basisDecl kind), env.find? ci₀.name = none) :
    ∃ env₂, CleanInstallStep env (.basisDecl kind) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], FullDeclInv V env → FullDeclInv V env₂ := by
  obtain ⟨hrun, hinst⟩ := basis_step_of_fresh (d := .basisDecl kind) kind rfl heq_stored hfresh
  have hbase : ∀ ci ∈ (kind.declsA (md := .anon)).reverse, isBaseKey ci.name = true := by
    intro ci hci
    exact List.all_eq_true.mp (basis_declsA_isBaseKey kind) ci (List.mem_reverse.mp hci)
  have hclean : CleanInstallStep env (.basisDecl kind)
      ⟨kind.declsA.reverse ++ env.consts⟩ :=
    CleanInstallStep.of_baseList hinst hbase
  have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.basisDecl kind)
      ⟨kind.declsA.reverse ++ env.consts⟩ := hrun
  exact ⟨⟨kind.declsA.reverse ++ env.consts⟩, hclean,
    fun V _ hInv => FullDeclInv.step_of_foldInv_clean hclean
      (foldInv_step_declRunJ (d := .basisDecl kind) (fun _ _ heq => nomatch heq) hdecl) V hInv⟩

/-- Step preservation for pinned `.indDecl block nP` (`basisPinHit block = some kind`) in
`FullDeclInv`. -/
theorem pinnedIndDecl_step_full {env : Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat} {kind : BasisKind}
    (hpin : Ix.Kernel.basisPinHit block = some kind)
    (heq_stored : kind = .quotK → env.find? Ix.Kernel.eqName = some (Ix.Kernel.eqA (md := .anon)))
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs (.indDecl block nP), env.find? ci₀.name = none) :
    ∃ env₂, CleanInstallStep env (.indDecl block nP) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], FullDeclInv V env → FullDeclInv V env₂ := by
  have hinst_eq : IxVM.Consistency.installs (.indDecl block nP) = kind.declsA := by
    simp [IxVM.Consistency.installs, hpin]
  have hfresh' : ∀ ci₀ ∈ kind.declsA (md := .anon), env.find? ci₀.name = none := by
    intro ci₀ hci₀
    apply hfresh ci₀
    rw [hinst_eq]
    exact hci₀
  obtain ⟨hrun, hinst⟩ := basis_step_of_fresh (d := .indDecl block nP) kind hinst_eq
    heq_stored hfresh'
  have hbase : ∀ ci ∈ (kind.declsA (md := .anon)).reverse, isBaseKey ci.name = true := by
    intro ci hci
    exact List.all_eq_true.mp (basis_declsA_isBaseKey kind) ci (List.mem_reverse.mp hci)
  have hclean : CleanInstallStep env (.indDecl block nP)
      ⟨kind.declsA.reverse ++ env.consts⟩ :=
    CleanInstallStep.of_baseList hinst hbase
  have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.indDecl block nP)
      ⟨kind.declsA.reverse ++ env.consts⟩ := by
    simp only [DeclRunJ, hpin]
    exact hrun
  exact ⟨⟨kind.declsA.reverse ++ env.consts⟩, hclean,
    fun V _ hInv => FullDeclInv.step_of_foldInv_clean hclean
      (foldInv_step_declRunJ
        (fun _ _ heq hp => by cases heq; rw [hpin] at hp; exact nomatch hp) hdecl) V hInv⟩

/-! ## Structural Zeta-Erasure Fallback (`dummyInstallStep`) -/

/-- Bottom-up structural zeta-erasure of let-bindings, witnessing `IxVM.Consistency.Annotates`
on any expression without fuel or termination measures. -/
def zetaErase : KExpr → KExpr
  | .bvar i => .bvar i
  | .fvar i ty => .fvar i (zetaErase ty)
  | .sort l => .sort l
  | .const n us => .const n us
  | .lit l => .lit l
  | .app f a => .app (zetaErase f) (zetaErase a)
  | .lam ty b m => .lam (zetaErase ty) (zetaErase b) m
  | .forallE ty b m => .forallE (zetaErase ty) (zetaErase b) m
  | .proj s i e => .proj s i (zetaErase e)
  | .letE _ v b _ => (zetaErase b).instantiate1Lift (zetaErase v)

theorem annotates_zetaErase : ∀ (e : KExpr), IxVM.Consistency.Annotates (zetaErase e) e
  | .bvar _ => .bvar
  | .fvar _ ty => .fvar (annotates_zetaErase ty)
  | .sort _ => .sort
  | .const _ _ => .const
  | .lit _ => .lit
  | .app f a => .app (annotates_zetaErase f) (annotates_zetaErase a)
  | .lam ty b _ => .lam (annotates_zetaErase ty) (annotates_zetaErase b)
  | .forallE ty b _ => .forallE (annotates_zetaErase ty) (annotates_zetaErase b)
  | .proj _ _ e => .proj (annotates_zetaErase e)
  | .letE _ v b _ =>
    .letE (IxVM.Refinement.L1.annotates_instantiate1Lift
      (annotates_zetaErase b) (annotates_zetaErase v) 0)

private def zetaEraseCV (cv : ConstantVal .anon) : ConstantVal .anon :=
  ⟨cv.name, cv.levelParams, zetaErase cv.type⟩

private def zetaEraseRule (rl : Ix.Kernel.RecRule .anon) : Ix.Kernel.RecRule .anon :=
  { rl with rhs := zetaErase rl.rhs }

private def zetaEraseCI : ConstantInfo .anon → ConstantInfo .anon
  | .axiomInfo cv => .axiomInfo (zetaEraseCV cv)
  | .defnInfo cv v h => .defnInfo (zetaEraseCV cv) (zetaErase v) h
  | .thmInfo cv v => .thmInfo (zetaEraseCV cv) (zetaErase v)
  | .indInfo cv caps => .indInfo (zetaEraseCV cv) caps
  | .ctorInfo cv nP nF => .ctorInfo (zetaEraseCV cv) nP nF
  | .recInfo cv mI rP rules => .recInfo (zetaEraseCV cv) mI rP (rules.map zetaEraseRule)
  | .projInfo tbl => .projInfo tbl

private theorem zetaEraseCI_name (ci : ConstantInfo .anon) : (zetaEraseCI ci).name = ci.name := by
  cases ci <;> rfl

private theorem forall₂_ruleStored_zetaErase :
    ∀ (rules : List (Ix.Kernel.RecRule .anon)),
      List.Forall₂ IxVM.Consistency.RuleStored (rules.map zetaEraseRule) rules
  | [] => .nil
  | rl :: rest =>
    .cons ⟨rfl, rfl, annotates_zetaErase rl.rhs⟩ (forall₂_ruleStored_zetaErase rest)

private theorem storedAs_zetaEraseCI {ci₀ : ConstantInfo .anon}
    (hnproj : ∀ tbl, ci₀ ≠ .projInfo tbl) :
    IxVM.Consistency.StoredAs (zetaEraseCI ci₀) ci₀ := by
  cases ci₀ with
  | axiomInfo cv => exact ⟨⟨rfl, rfl, annotates_zetaErase cv.type⟩, trivial⟩
  | defnInfo cv v _ =>
    exact ⟨⟨rfl, rfl, annotates_zetaErase cv.type⟩, annotates_zetaErase v, rfl⟩
  | thmInfo cv v =>
    exact ⟨⟨rfl, rfl, annotates_zetaErase cv.type⟩, annotates_zetaErase v⟩
  | indInfo cv _ => exact ⟨⟨rfl, rfl, annotates_zetaErase cv.type⟩, trivial⟩
  | ctorInfo cv _ _ => exact ⟨⟨rfl, rfl, annotates_zetaErase cv.type⟩, rfl, rfl⟩
  | recInfo cv _ _ rules =>
    exact ⟨⟨rfl, rfl, annotates_zetaErase cv.type⟩, rfl, rfl, forall₂_ruleStored_zetaErase rules⟩
  | projInfo tbl => exact False.elim (hnproj tbl rfl)

/-- Unconditional `InstallStep` witness for any declaration `d` whose installed keys are distinct,
fresh in `env`, and non-`.aux` (used when the model-side invariant is vacuous). -/
theorem dummyInstallStep {env : Env .anon} {d : Declaration .anon}
    (hnd : ((IxVM.Consistency.installs d).map (·.name)).Nodup)
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs d, env.find? ci₀.name = none)
    (hna : ∀ ci₀ ∈ IxVM.Consistency.installs d, NonAuxKey ci₀.name) :
    ∃ env₂, IxVM.Consistency.InstallStep env d env₂ := by
  let new := (IxVM.Consistency.installs d).map zetaEraseCI
  have hmap_names : new.map (·.name) = (IxVM.Consistency.installs d).map (·.name) := by
    simp [new, List.map_map, Function.comp, zetaEraseCI_name]
  refine ⟨⟨new ++ env.consts⟩, new, rfl, ?_, ?_, ?_, ?_⟩
  · rwa [hmap_names]
  · intro ci hci
    obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hci
    rw [zetaEraseCI_name]
    exact hfresh ci₀ hci₀
  · intro ci₀ hci₀
    refine ⟨zetaEraseCI ci₀, List.mem_map.mpr ⟨ci₀, hci₀, rfl⟩, storedAs_zetaEraseCI ?_⟩
    intro tbl rfl
    exact hna (.projInfo tbl) hci₀ tbl.structName .projTable rfl
  · intro ci hci
    obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hci
    exact Or.inl ⟨ci₀, hci₀, (zetaEraseCI_name ci₀).symm⟩

end IxVM.Refinement.Decl
