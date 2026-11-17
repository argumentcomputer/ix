import IxVMRefinement.Decl.DeclSpecs
import IxVMRefinement.Assembly.Bridge
import IxVMRefinement.Assembly.LoadGlue
import IxVMRefinement.Assembly.RoleFacts
import IxVMRefinement.Decl.PrefixLoads
import IxVMRefinement.Decl.PrefixInv

/-!
# Walked Constant Declaration Steps (`DeclWalkedConst.lean`)

Proves one-step advancement of `FullDeclInv` and `CleanInstallStep` (hence
`IxVM.Consistency.InstallStep`) across walked non-role constant declarations
(`Assembly.CheckedConstOrigin`: `.axiomDecl`, `.defnDecl`, `.thmDecl`, `.opaqueDecl`) as well as
quotient, basis, and pinned inductive declarations (`.quotDecl`, `.basisDecl`, `.indDecl`),
parameterized over the context-facts bundle `FoldContextFacts E_core t env`, together with a
total structural zeta-erasure fallback `dummyInstallStep` for vacuous-invariant prefixes.

`checkedConstOrigin_step` is stated over the historical unrestricted load contract.
`checkedConstOrigin_step_scoped` is the same step over the scoped core: it reads the prefix
through `PrefixContextFacts`, which mentions no call, and the resolution of the loader calls of
the selected list (`ScopeResolved`).
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

/-! ## Walked Constant Step over the Scoped Core -/

/-- **The context of a walked step at a prefix**, with no assumption about the calls of any run:
the table is well formed, and under the store invariant the companions of the scoped core's
environment facts and the prefix load contract hold at every group limit. -/
structure PrefixContextFacts (E_core : Ixon.Env) (t : Ix.Kernel.RoleTable)
    (env : Env .anon) : Prop where
  tableWf : t.wf = true
  companions : FoldStoreInv env → ∀ lim : Option Nat, CoreCompanions ⟨E_core, env, t, lim⟩
  loads : FoldStoreInv env → ∀ lim : Option Nat, PrefixLoadFacts ⟨E_core, env, t, lim⟩

/-- **The prefix context is inhabited at the start of a fold**: at the empty environment, for
decoded records and a well-formed table that binds no role (with a bound role in force the
role's constants would have to be stored first). -/
theorem prefixContextFacts_empty {E_core : Ixon.Env} (hdec : L1.EnvDecoded E_core)
    {t : Ix.Kernel.RoleTable} (htwf : t.wf = true) (hnb : ∀ r, t.addressOf? r = none) :
    PrefixContextFacts E_core t Ix.Kernel.Env.empty where
  tableWf := htwf
  companions := fun _ lim => coreCompanions_of_empty (fun _ => rfl) (fun r h => by
    have hb : (t.addressOf? r).isSome = true := h.1
    rw [hnb r] at hb
    cases hb)
  loads := fun _ lim => prefixLoadFacts_empty hdec t lim

/-- The scoped core's facts at the calls of a selected list, from the prefix context and the
resolution of that list's loader calls. -/
theorem PrefixContextFacts.scopedCoreFacts {E_core : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {env : Env .anon} (hctx : PrefixContextFacts E_core t env) (hS : FoldStoreInv env)
    {calls : List (Call F)} (hres : ScopeResolved t env (fun cl => cl ∈ calls))
    (lim : Option Nat) :
    ScopedCoreFacts { toCtx := ⟨E_core, env, t, lim⟩, allowed := fun cl => cl ∈ calls } :=
  ⟨FoldStoreInv.toCoreEnvFacts (c := ⟨E_core, env, t, lim⟩) hS hctx.tableWf
      (hctx.companions hS lim),
    scopedLoadFacts_of_prefix (c := ⟨E_core, env, t, lim⟩) (hctx.loads hS lim) hres⟩

/-- **A walked constant declaration installs and keeps the invariant, over the scoped core.**
`calls` is the list the check evidence is stated over: it holds the typed runs of this
declaration with their calls. The step reads the prefix through `PrefixContextFacts` (which
mentions no call) and `ScopeResolved` (every loader call of `calls` targets a stored key); it
uses neither the unrestricted load contract nor the public core seam. -/
theorem checkedConstOrigin_step_scoped
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {E_core : Ixon.Env} {order_role : List _root_.Address}
    {env : Env .anon} {d : Declaration .anon}
    (hchk : Assembly.CheckedConstOrigin calls t bAddr E_core order_role d)
    (hctx : PrefixContextFacts E_core t env)
    (hres : ScopeResolved t env (fun cl => cl ∈ calls))
    (hgood : Good ⟨E_core, env, t, none⟩ calls)
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs d, env.find? ci₀.name = none)
    (hne_role : ∀ a, a ∉ order_role →
      ∀ r : Ix.Kernel.Role, IxVM.Refinement.compilerTrust r = false → keyOf t a ≠ .role r) :
    ∃ env₂, CleanInstallStep env d env₂ ∧
      (∀ (V : Type u) [Ix.Kernel.SetTheory V], FullDeclInv V env → FullDeclInv V env₂) ∧
      ∀ lim : Option Nat, CoreCompanions ⟨E_core, env, t, lim⟩ →
        CoreCompanions ⟨E_core, env₂, t, lim⟩ := by
  have hbound : IxVM.Consistency.Bounded calls := hgood.2
  cases hchk with
  | @axiomDecl a _ _ nlvls ty₀ ty' lim _ _ _ m_ax _ x_rc _ x_addr _ v_ax _ cs_ax
      hnot_role _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrc_ax ha_ax ev_ax hne_ax _ hsub_ax =>
    let cv₀ : ConstantVal .anon := ⟨keyOf t a, List.range nlvls, ty₀⟩
    by_cases hskip : cv₀.name = Ix.Kernel.quotSoundName ∨ IxVM.Consistency.inertKey cv₀.name = true
    · have hempty : IxVM.Consistency.installs (.axiomDecl cv₀) = [] := ite_eq_left hskip
      exact ⟨env, CleanInstallStep.empty hempty, fun _ _ h => h, fun _ h => h⟩
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
    refine ⟨⟨.defnInfo cv' val' hn :: env.consts⟩, hclean, fun V _ hInv => ?_, fun lim hC =>
      hC.cons_value (ci := .defnInfo cv' val' hn) hfresh_cv (fun _ => ne_projTableName_of_isBaseKey hbase)
        (fun _ _ _ _ e => nomatch e) (fun _ _ _ e => nomatch e)⟩
    have hS : FoldStoreInv env := hInv.toFoldStoreInv
    let c : ScopedCtx :=
      { toCtx := ⟨E_core, env, t, some lim⟩, allowed := fun cl => cl ∈ calls }
    have hgood_c : Good c.toCtx calls := hgood
    obtain ⟨hef, hlf⟩ := hctx.scopedCoreFacts hS hres (some lim)
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
      scoped_core_ensure_sort (c := c) hrc_es.toRCRep (typesRep_of_nil_eq c.κ hm_es)
        (ghostScoped_zero zeroGhostWalked) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_es) hsub_es) ev_es
        (hty_tmc_es' 0 zeroGhostWalked)
    obtain ⟨vtype, hinf_val, hde_val⟩ :=
      scoped_core_check (c := c) hrc_kc.toRCRep (typesRep_of_nil_eq c.κ hm_kc)
        (ghostScoped_zero zeroGhostWalked) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_kc) hsub_kc) ev_kc
        (hval_tmc_kc' 0 zeroGhostWalked) (hty_tmc_kc' 0 zeroGhostWalked)
    have hnrole := hne_role a hnot_role
    have hres_name : Ix.Kernel.reservedBasisNames.contains cv'.name = false :=
      reservedBasisNames_false_of_ne_nonTrustRole hnrole
    have hnoprj : cv'.name.isProjFnShape = false := isProjFnShape_of_isBaseKey hbase
    have hcv_run : ConstantValRunJ rulesJ env cv' ty' :=
      ⟨by rw [hfresh_cv]; rfl, hres_name, hnoprj, levelParam_nodup_of_nodup List.nodup_range,
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
    refine ⟨⟨.thmInfo cv' val' :: env.consts⟩, hclean, fun V _ hInv => ?_, fun lim hC =>
      hC.cons_value (ci := .thmInfo cv' val') hfresh_cv (fun _ => ne_projTableName_of_isBaseKey hbase)
        (fun _ _ _ _ e => nomatch e) (fun _ _ _ e => nomatch e)⟩
    have hS : FoldStoreInv env := hInv.toFoldStoreInv
    let c : ScopedCtx :=
      { toCtx := ⟨E_core, env, t, some lim⟩, allowed := fun cl => cl ∈ calls }
    have hgood_c : Good c.toCtx calls := hgood
    obtain ⟨hef, hlf⟩ := hctx.scopedCoreFacts hS hres (some lim)
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
      scoped_core_ensure_sort (c := c) hrc_es.toRCRep (typesRep_of_nil_eq c.κ hm_es)
        (ghostScoped_zero zeroGhostWalked) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_es) hsub_es) ev_es
        (hty_tmc_es' 0 zeroGhostWalked)
    have hisZero : (rulesJ (md := .anon)).isZero u :=
      thm_isZero_of_level_equal Levels.l2
        (RomBound.bounded_mono hbound hsub_le) hℓ hu hm_le ev_le
    obtain ⟨vtype, hinf_val, hde_val⟩ :=
      scoped_core_check (c := c) hrc_kc.toRCRep (typesRep_of_nil_eq c.κ hm_kc)
        (ghostScoped_zero zeroGhostWalked) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_kc) hsub_kc) ev_kc
        (hval_tmc_kc' 0 zeroGhostWalked) (hty_tmc_kc' 0 zeroGhostWalked)
    have hnrole := hne_role a hnot_role
    have hres_name : Ix.Kernel.reservedBasisNames.contains cv'.name = false :=
      reservedBasisNames_false_of_ne_nonTrustRole hnrole
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
    refine ⟨⟨.axiomInfo cv' :: env.consts⟩, hclean, fun V _ hInv => ?_, fun lim hC =>
      hC.cons_value (ci := .axiomInfo cv') hfresh_cv (fun _ => ne_projTableName_of_isBaseKey hbase)
        (fun _ _ _ _ e => nomatch e) (fun _ _ _ e => nomatch e)⟩
    have hS : FoldStoreInv env := hInv.toFoldStoreInv
    let c : ScopedCtx :=
      { toCtx := ⟨E_core, env, t, some lim⟩, allowed := fun cl => cl ∈ calls }
    have hgood_c : Good c.toCtx calls := hgood
    obtain ⟨hef, hlf⟩ := hctx.scopedCoreFacts hS hres (some lim)
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
      scoped_core_ensure_sort (c := c) hrc_es.toRCRep (typesRep_of_nil_eq c.κ hm_es)
        (ghostScoped_zero zeroGhostWalked) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_es) hsub_es) ev_es
        (hty_tmc_es' 0 zeroGhostWalked)
    obtain ⟨vtype, hinf_val, hde_val⟩ :=
      scoped_core_check (c := c) hrc_kc.toRCRep (typesRep_of_nil_eq c.κ hm_kc)
        (ghostScoped_zero zeroGhostWalked) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_kc) hsub_kc) ev_kc
        (hval_tmc_kc' 0 zeroGhostWalked) (hty_tmc_kc' 0 zeroGhostWalked)
    have hnrole := hne_role a hnot_role
    have hres_name : Ix.Kernel.reservedBasisNames.contains cv'.name = false :=
      reservedBasisNames_false_of_ne_nonTrustRole hnrole
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
    exact FullDeclInv.step_of_foldInv_clean hclean
      (foldInv_step_declRunJ (d := .opaqueDecl cv' val') (fun _ _ heq => nomatch heq) hdecl) V hInv

/-- The step as the public `InstallStep`: the declared constant is stored, the fold invariant
and the companions of the core's environment facts are kept, and every stored key stays stored
(so a scope resolved before the step is resolved after it, `ScopeResolved.mono`). -/
theorem checkedConstOrigin_installStep_scoped
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {E_core : Ixon.Env} {order_role : List _root_.Address}
    {env : Env .anon} {d : Declaration .anon}
    (hchk : Assembly.CheckedConstOrigin calls t bAddr E_core order_role d)
    (hctx : PrefixContextFacts E_core t env)
    (hres : ScopeResolved t env (fun cl => cl ∈ calls))
    (hgood : Good ⟨E_core, env, t, none⟩ calls)
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs d, env.find? ci₀.name = none)
    (hne_role : ∀ a, a ∉ order_role →
      ∀ r : Ix.Kernel.Role, IxVM.Refinement.compilerTrust r = false → keyOf t a ≠ .role r) :
    ∃ env₂, IxVM.Consistency.InstallStep env d env₂ ∧
      (∀ (V : Type u) [Ix.Kernel.SetTheory V], FullDeclInv V env → FullDeclInv V env₂) ∧
      (∀ lim : Option Nat, CoreCompanions ⟨E_core, env, t, lim⟩ →
        CoreCompanions ⟨E_core, env₂, t, lim⟩) ∧
      ∀ k : KKey, (env.find? k).isSome = true → (env₂.find? k).isSome = true := by
  obtain ⟨env₂, hclean, hstep, hcomp⟩ :=
    checkedConstOrigin_step_scoped hchk hctx hres hgood hfresh hne_role
  exact ⟨env₂, hclean.step, hstep, hcomp, hclean.monoSome⟩

/-- **The scoped step at the start of a fold.** At the empty environment, for decoded records and
a table that binds no role, the context hypotheses of the scoped step hold outright
(`prefixContextFacts_empty`), and the scope is resolved as soon as the selected calls load no
constant (`ScopeResolved.of_no_loads`): what remains is the check evidence itself. So the
hypotheses of `checkedConstOrigin_installStep_scoped` are jointly satisfiable by a declaration
whose type and value name no constant. -/
theorem checkedConstOrigin_installStep_empty
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {E_core : Ixon.Env} {order_role : List _root_.Address} {d : Declaration .anon}
    (hchk : Assembly.CheckedConstOrigin calls t bAddr E_core order_role d)
    (hdec : L1.EnvDecoded E_core) (htwf : t.wf = true) (hnb : ∀ r, t.addressOf? r = none)
    (hno : ∀ cl ∈ calls, cl.name ≠ "Ingress::get_ci" ∧ cl.name ≠ "Ingress::get_ci_iprj" ∧
      cl.name ≠ "Ingress::get_ci_cprj" ∧ cl.name ≠ "KernelModeled::proj_ctor")
    (hgood : Good ⟨E_core, Ix.Kernel.Env.empty, t, none⟩ calls)
    (hne_role : ∀ a, a ∉ order_role →
      ∀ r : Ix.Kernel.Role, IxVM.Refinement.compilerTrust r = false → keyOf t a ≠ .role r) :
    ∃ env₂, IxVM.Consistency.InstallStep Ix.Kernel.Env.empty d env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], FullDeclInv V env₂ := by
  obtain ⟨env₂, hstep, hinv, _, _⟩ :=
    checkedConstOrigin_installStep_scoped hchk (prefixContextFacts_empty hdec htwf hnb)
      (ScopeResolved.of_no_loads fun cl hcl => hno cl hcl) hgood (fun _ _ => rfl) hne_role
  exact ⟨env₂, hstep, fun V _ => hinv V (FullDeclInv.empty V)⟩

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


/-! ## Walked constant step over the prefix context -/

/-- **The check evidence of a walked constant, under a keying and at a group limit.** The same
evidence as `Assembly.CheckedConstOrigin`, with the heap terms of the declaration's type and value
represented under the keying `κ` instead of the table's, and with the group limit of its role
context and the declaration as it is stored (`d'`: the annotated type and value the heap terms
represent) exposed. At the keying of a prefix (`Ctx.stored`) the representation says that every
constant and projection cell of the declaration's own terms has a stored address: this is the
form in which a step reads "the references the record uses are stored". -/
inductive CheckedConstOriginAt (κ : _root_.Address → Core.KKey) (lim : Nat)
    (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (bAddr : _root_.Address)
    (E_core : Ixon.Env) (order_role : List _root_.Address) :
    Ix.Kernel.Declaration .anon → Ix.Kernel.Declaration .anon → Prop where
  | axiomDecl
      {a : _root_.Address} {c : Ixon.Constant} {ax : Ixon.Axiom}
      {nlvls : Nat} {ty₀ ty' : Core.KExpr}
      {m_pre m_es m_es' m_ax m_ax' : Heap F}
      {x_rc x_ty x_addr v_sort v_ax : SourceValue F}
      {cs_es cs_ax : List (Call F)}
      (hnot_role : a ∉ order_role)
      (hrec : Ix.Cert.recordAt E_core a = some c)
      (hinfo : c.info = .axio ax)
      (hsafe : ax.isUnsafe = false)
      (hnlvls : nlvls < 4294967296)
      (hty_lbb : ty₀.looseBVarsBounded 0 = true)
      (hty_def : ty₀.allLevelParamsDefined (List.range nlvls) = true)
      (hty_ann : IxVM.Consistency.Annotates ty' ty₀)
      (hm_es : m_es = m_pre ++
        [.construct IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []])
      (hty_tmc : Core.TmC κ m_es (Core.posOf (List.range nlvls) ty') x_ty)
      (hrc_es : Claim.RCFullRep t bAddr lim m_es x_rc)
      (ev_es : ObsFn Core.W "KernelInfer::k_ensure_sort"
        [x_rc, x_ty, .ptr (.enum IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre.length]
        m_es v_sort m_es' cs_es)
      (hcl_es : (⟨"KernelInfer::k_ensure_sort",
        [x_rc, x_ty, .ptr (.enum IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre.length],
        m_es⟩ : Call F) ∈ calls)
      (hsub_es : ∀ cl ∈ cs_es, cl ∈ calls)
      (hext_ax : Heap.Extends m_es' m_ax)
      (hrc_ax : Claim.RCFullRep t bAddr lim m_ax x_rc)
      (ha_ax : Core.S0.addr m_ax x_addr a)
      (ev_ax : ObsFn Core.W "KernelRoles::axiom_standing" [x_rc, x_addr] m_ax v_ax m_ax' cs_ax)
      (hne_ax : v_ax ≠ .field 0)
      (hcl_ax : (⟨"KernelRoles::axiom_standing", [x_rc, x_addr], m_ax⟩ : Call F) ∈ calls)
      (hsub_ax : ∀ cl ∈ cs_ax, cl ∈ calls) :
      CheckedConstOriginAt κ lim calls t bAddr E_core order_role
        (.axiomDecl ⟨Core.keyOf t a, List.range nlvls, ty₀⟩)
        (.axiomDecl ⟨Core.keyOf t a, List.range nlvls, ty'⟩)
  | defnDecl
      {a : _root_.Address} {nlvls : Nat} {ty₀ val₀ ty' val' : Core.KExpr}
      {hn : Ix.Kernel.ReducibilityHint}
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
      (hrc_es : Claim.RCFullRep t bAddr lim m_es x_rc)
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
      (hrc_kc : Claim.RCFullRep t bAddr lim m_kc x_rc)
      (ev_kc : ObsFn Core.W "KernelInfer::k_check"
        [x_rc, x_val, x_ty,
         .ptr (.enum IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre2.length]
        m_kc r_kc m_kc' cs_kc)
      (hcl_kc : (⟨"KernelInfer::k_check",
        [x_rc, x_val, x_ty,
         .ptr (.enum IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre2.length],
        m_kc⟩ : Call F) ∈ calls)
      (hsub_kc : ∀ cl ∈ cs_kc, cl ∈ calls) :
      CheckedConstOriginAt κ lim calls t bAddr E_core order_role
        (.defnDecl ⟨Core.keyOf t a, List.range nlvls, ty₀⟩ val₀ hn)
        (.defnDecl ⟨Core.keyOf t a, List.range nlvls, ty'⟩ val' hn)
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
      (hrc_es : Claim.RCFullRep t bAddr lim m_es x_rc)
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
      (hrc_kc : Claim.RCFullRep t bAddr lim m_kc x_rc)
      (ev_kc : ObsFn Core.W "KernelInfer::k_check"
        [x_rc, x_val, x_ty,
         .ptr (.enum IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre2.length]
        m_kc r_kc m_kc' cs_kc)
      (hcl_kc : (⟨"KernelInfer::k_check",
        [x_rc, x_val, x_ty,
         .ptr (.enum IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre2.length],
        m_kc⟩ : Call F) ∈ calls)
      (hsub_kc : ∀ cl ∈ cs_kc, cl ∈ calls) :
      CheckedConstOriginAt κ lim calls t bAddr E_core order_role
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
      (hrc_es : Claim.RCFullRep t bAddr lim m_es x_rc)
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
      (hrc_kc : Claim.RCFullRep t bAddr lim m_kc x_rc)
      (ev_kc : ObsFn Core.W "KernelInfer::k_check"
        [x_rc, x_val, x_ty,
         .ptr (.enum IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre2.length]
        m_kc r_kc m_kc' cs_kc)
      (hcl_kc : (⟨"KernelInfer::k_check",
        [x_rc, x_val, x_ty,
         .ptr (.enum IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre2.length],
        m_kc⟩ : Call F) ∈ calls)
      (hsub_kc : ∀ cl ∈ cs_kc, cl ∈ calls) :
      CheckedConstOriginAt κ lim calls t bAddr E_core order_role
        (.opaqueDecl ⟨Core.keyOf t a, List.range nlvls, ty₀⟩ val₀)
        (.opaqueDecl ⟨Core.keyOf t a, List.range nlvls, ty'⟩ val')


/-- The table-keyed evidence is the evidence at the table's own keying. -/
theorem CheckedConstOriginAt.ofTable {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {bAddr : _root_.Address} {E_core : Ixon.Env} {order_role : List _root_.Address}
    {d : Declaration .anon} (h : Assembly.CheckedConstOrigin calls t bAddr E_core order_role d) :
    ∃ lim d', CheckedConstOriginAt (keyOf t) lim calls t bAddr E_core order_role d d' := by
  cases h with
  | axiomDecl hnot_role hrec hinfo hsafe hnlvls hty_lbb hty_def hty_ann hm_es hty_tmc hrc_es ev_es hcl_es hsub_es hext_ax hrc_ax ha_ax ev_ax hne_ax hcl_ax hsub_ax =>
    exact ⟨_, _, .axiomDecl hnot_role hrec hinfo hsafe hnlvls hty_lbb hty_def hty_ann hm_es hty_tmc hrc_es ev_es hcl_es hsub_es hext_ax hrc_ax ha_ax ev_ax hne_ax hcl_ax hsub_ax⟩
  | defnDecl hnot_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann hty_out_def hval_out_def hm_es hty_tmc_es hrc_es ev_es hcl_es hsub_es hext_kc hm_kc hty_tmc_kc hval_tmc_kc hrc_kc ev_kc hcl_kc hsub_kc =>
    exact ⟨_, _, .defnDecl hnot_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann hty_out_def hval_out_def hm_es hty_tmc_es hrc_es ev_es hcl_es hsub_es hext_kc hm_kc hty_tmc_kc hval_tmc_kc hrc_kc ev_kc hcl_kc hsub_kc⟩
  | thmDecl hnot_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann hty_out_def hval_out_def hm_es hty_tmc_es hrc_es ev_es hcl_es hsub_es hm_le ev_le hcl_le hsub_le hext_kc hm_kc hty_tmc_kc hval_tmc_kc hrc_kc ev_kc hcl_kc hsub_kc =>
    exact ⟨_, _, .thmDecl hnot_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann hty_out_def hval_out_def hm_es hty_tmc_es hrc_es ev_es hcl_es hsub_es hm_le ev_le hcl_le hsub_le hext_kc hm_kc hty_tmc_kc hval_tmc_kc hrc_kc ev_kc hcl_kc hsub_kc⟩
  | opaqueDecl hnot_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann hty_out_def hval_out_def hm_es hty_tmc_es hrc_es ev_es hcl_es hsub_es hext_kc hm_kc hty_tmc_kc hval_tmc_kc hrc_kc ev_kc hcl_kc hsub_kc =>
    exact ⟨_, _, .opaqueDecl hnot_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann hty_out_def hval_out_def hm_es hty_tmc_es hrc_es ev_es hcl_es hsub_es hext_kc hm_kc hty_tmc_kc hval_tmc_kc hrc_kc ev_kc hcl_kc hsub_kc⟩

/-- **A heap term a typed run takes as an argument**: the term of a `k_ensure_sort` call, or the
value or the type of a `k_check` call, among `calls`. -/
def RunTerm (calls : List (Call F)) (h : Heap F) (p : SourceValue F) : Prop :=
  (∃ rc types, (⟨"KernelInfer::k_ensure_sort", [rc, p, types], h⟩ : Call F) ∈ calls) ∨
  (∃ rc ty types, (⟨"KernelInfer::k_check", [rc, p, ty, types], h⟩ : Call F) ∈ calls) ∨
  (∃ rc val types, (⟨"KernelInfer::k_check", [rc, val, p, types], h⟩ : Call F) ∈ calls)

/-- **The evidence under another keying**: one that agrees with the first on the cell addresses of
the heap terms the typed runs of `calls` take. -/
theorem CheckedConstOriginAt.rekey {κ₁ κ₂ : _root_.Address → Core.KKey} {lim : Nat}
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {E_core : Ixon.Env} {order_role : List _root_.Address} {d d' : Declaration .anon}
    (h : CheckedConstOriginAt κ₁ lim calls t bAddr E_core order_role d d')
    (agree : ∀ (hp : Heap F) (p : SourceValue F) (a : Bytes.Address), RunTerm calls hp p →
      AddrIn hp p a → κ₂ (ixAddr a) = κ₁ (ixAddr a)) :
    CheckedConstOriginAt κ₂ lim calls t bAddr E_core order_role d d' := by
  cases h with
  | axiomDecl hnot_role hrec hinfo hsafe hnlvls hty_lbb hty_def hty_ann hm_es hty_tmc hrc_es ev_es hcl_es hsub_es hext_ax hrc_ax ha_ax ev_ax hne_ax hcl_ax hsub_ax =>
    exact .axiomDecl hnot_role hrec hinfo hsafe hnlvls hty_lbb hty_def hty_ann hm_es 
      (Core.TmC.rekey hty_tmc fun a m => agree _ _ a (Or.inl ⟨_, _, hcl_es⟩) m) hrc_es ev_es hcl_es hsub_es hext_ax hrc_ax ha_ax ev_ax hne_ax hcl_ax hsub_ax
  | defnDecl hnot_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann hty_out_def hval_out_def hm_es hty_tmc_es hrc_es ev_es hcl_es hsub_es hext_kc hm_kc hty_tmc_kc hval_tmc_kc hrc_kc ev_kc hcl_kc hsub_kc =>
    exact .defnDecl hnot_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann hty_out_def hval_out_def hm_es 
      (Core.TmC.rekey hty_tmc_es fun a m => agree _ _ a (Or.inl ⟨_, _, hcl_es⟩) m) hrc_es ev_es hcl_es hsub_es hext_kc hm_kc 
      (Core.TmC.rekey hty_tmc_kc fun a m => agree _ _ a (Or.inr (Or.inr ⟨_, _, _, hcl_kc⟩)) m) 
      (Core.TmC.rekey hval_tmc_kc fun a m => agree _ _ a (Or.inr (Or.inl ⟨_, _, _, hcl_kc⟩)) m) hrc_kc ev_kc hcl_kc hsub_kc
  | thmDecl hnot_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann hty_out_def hval_out_def hm_es hty_tmc_es hrc_es ev_es hcl_es hsub_es hm_le ev_le hcl_le hsub_le hext_kc hm_kc hty_tmc_kc hval_tmc_kc hrc_kc ev_kc hcl_kc hsub_kc =>
    exact .thmDecl hnot_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann hty_out_def hval_out_def hm_es 
      (Core.TmC.rekey hty_tmc_es fun a m => agree _ _ a (Or.inl ⟨_, _, hcl_es⟩) m) hrc_es ev_es hcl_es hsub_es hm_le ev_le hcl_le hsub_le hext_kc hm_kc 
      (Core.TmC.rekey hty_tmc_kc fun a m => agree _ _ a (Or.inr (Or.inr ⟨_, _, _, hcl_kc⟩)) m) 
      (Core.TmC.rekey hval_tmc_kc fun a m => agree _ _ a (Or.inr (Or.inl ⟨_, _, _, hcl_kc⟩)) m) hrc_kc ev_kc hcl_kc hsub_kc
  | opaqueDecl hnot_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann hty_out_def hval_out_def hm_es hty_tmc_es hrc_es ev_es hcl_es hsub_es hext_kc hm_kc hty_tmc_kc hval_tmc_kc hrc_kc ev_kc hcl_kc hsub_kc =>
    exact .opaqueDecl hnot_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann hty_out_def hval_out_def hm_es 
      (Core.TmC.rekey hty_tmc_es fun a m => agree _ _ a (Or.inl ⟨_, _, hcl_es⟩) m) hrc_es ev_es hcl_es hsub_es hext_kc hm_kc 
      (Core.TmC.rekey hty_tmc_kc fun a m => agree _ _ a (Or.inr (Or.inr ⟨_, _, _, hcl_kc⟩)) m) 
      (Core.TmC.rekey hval_tmc_kc fun a m => agree _ _ a (Or.inr (Or.inl ⟨_, _, _, hcl_kc⟩)) m) hrc_kc ev_kc hcl_kc hsub_kc

/-- **The evidence at a prefix, from the table-keyed evidence**: when every cell address of the
heap terms the typed runs take is stored. The table-keyed evidence is what the record layer
produces (`Assembly.CheckedConstOrigin`); the storedness of the cells is the step's input about
the references the record uses. -/
theorem CheckedConstOriginAt.stored_of_table {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {bAddr : _root_.Address} {E_core : Ixon.Env} {order_role : List _root_.Address}
    {env : Env .anon} {d : Declaration .anon}
    (h : Assembly.CheckedConstOrigin calls t bAddr E_core order_role d)
    (hcells : ∀ (hp : Heap F) (p : SourceValue F) (a : Bytes.Address), RunTerm calls hp p →
      AddrIn hp p a → ∃ ci, env.find? (keyOf t (ixAddr a)) = some ci) :
    ∃ lim d', CheckedConstOriginAt (Ctx.stored ⟨E_core, env, t, some lim⟩).κ lim calls t bAddr
      E_core order_role d d' := by
  obtain ⟨lim, d', h'⟩ := CheckedConstOriginAt.ofTable h
  refine ⟨lim, d', h'.rekey fun hp p a hr m => ?_⟩
  obtain ⟨ci, hci⟩ := hcells hp p a hr m
  exact Ctx.stored_key_of_find (c := ⟨E_core, env, t, some lim⟩) hci

/-- **A walked definition, theorem, opaque constant or axiom installs and keeps the prefix
invariant.** The step reads the prefix through `PrefixInv` alone. Its inputs about the record
being folded are: the check evidence at the prefix's keying (`hchk`: the declaration's own heap
terms mention stored addresses only), the freshness of the declared key (`hfresh`), that the
declared name is no key of a role outside compiler trust (`hnr`), and the reload of the record
as the constant stored (`hreload`). It uses neither the unrestricted load contract, nor the
public core seam, nor a hypothesis about which calls a run makes. -/
theorem walkedConst_step
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {E_core : Ixon.Env} {order_role : List _root_.Address} {lim : Nat}
    {env : Env .anon} {d d' : Declaration .anon}
    (hinv : PrefixInv.{u} E_core t lim env)
    (hchk : CheckedConstOriginAt (Ctx.stored ⟨E_core, env, t, some lim⟩).κ lim calls t bAddr
      E_core order_role d d')
    (hgood : Good ⟨E_core, env, t, none⟩ calls)
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs d, env.find? ci₀.name = none)
    (hnr : ∀ ci₀ ∈ IxVM.Consistency.installs d, ∀ r : Ix.Kernel.Role,
      IxVM.Refinement.compilerTrust r = false → ci₀.name ≠ .role r)
    (hreload : ∀ cn ∈ IxVM.Consistency.installs d',
      ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address),
        ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → Good ⟨E_core, env, t, some lim⟩ cs →
        Bytes.RepAddressRef addrTy h a addr → keyOf t (ixAddr a) = cn.name →
        CIPtrRep (Ctx.stored ⟨E_core, ⟨cn :: env.consts⟩, t, some lim⟩).κ h' ptr cn) :
    CleanInstallStep env d ⟨IxVM.Consistency.installs d' ++ env.consts⟩ ∧
      PrefixInv.{u} E_core t lim ⟨IxVM.Consistency.installs d' ++ env.consts⟩ := by
  have hbound : IxVM.Consistency.Bounded calls := hgood.2
  cases hchk with
  | @axiomDecl a _ _ nlvls ty₀ ty' _ _ _ m_ax _ x_rc _ x_addr _ v_ax _ cs_ax
      hnot_role _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrc_ax ha_ax ev_ax hne_ax _ hsub_ax =>
    let cv₀ : ConstantVal .anon := ⟨keyOf t a, List.range nlvls, ty₀⟩
    by_cases hskip : cv₀.name = Ix.Kernel.quotSoundName ∨ IxVM.Consistency.inertKey cv₀.name = true
    · have hempty : IxVM.Consistency.installs (.axiomDecl cv₀) = [] := ite_eq_left hskip
      have hempty' : IxVM.Consistency.installs
          (.axiomDecl ⟨keyOf t a, List.range nlvls, ty'⟩ : Declaration .anon) = [] :=
        ite_eq_left hskip
      rw [hempty']
      exact ⟨CleanInstallStep.empty hempty, hinv⟩
    · obtain ⟨a', ha'_ref, heq_a⟩ := ha_ax
      let c : Ctx := ⟨E_core, env, t, some lim⟩
      have hgood_c : Good c calls := hgood
      obtain ⟨ro, hro_addr, _, hrole⟩ :=
        axiom_standing_spec rolesSpec (hgood_c.sub hsub_ax) hinv.tableWf
          hrc_ax.toRCRep (rcFullRep_axiomsNil hrc_ax) ha'_ref ev_ax hne_ax
      have hk : keyOf t a = .role ro := by
        have hk0 := keyOf_of_addressOf hinv.tableWf hro_addr
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
      have hmem : (ConstantInfo.axiomInfo cv₀) ∈ IxVM.Consistency.installs (.axiomDecl cv₀) := by
        rw [show IxVM.Consistency.installs (.axiomDecl cv₀) = [.axiomInfo cv₀] from ite_eq_right hskip]
        exact List.mem_singleton.mpr rfl
      exact False.elim (hnr (.axiomInfo cv₀) hmem ro hct hk)
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
    have hstored : IxVM.Consistency.StoredAs (.defnInfo cv' val' hn) (.defnInfo cv₀ val₀ hn) :=
      ⟨⟨rfl, rfl, hty_ann⟩, hval_ann, rfl⟩
    have hclean : CleanInstallStep env (.defnDecl cv₀ val₀ hn) ⟨.defnInfo cv' val' hn :: env.consts⟩ :=
      CleanInstallStep.single rfl hstored hfresh_cv hbase
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
    obtain ⟨_, hty'_nfv, hty'_bvs, hty'_ann⟩ := tmC_closed_props hty_tmc_es'
    obtain ⟨_, hval'_nfv, hval'_bvs, hval'_ann⟩ := tmC_closed_props hval_tmc_kc'
    obtain ⟨stype, u, _, hinf_ty, hred_ty, _, _⟩ :=
      scoped_core_ensure_sort (c := c) hrc_es.toRCRep (typesRep_of_nil_eq c.κ hm_es)
        (ghostScoped_zero zeroGhostWalked) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_es) (fun _ _ => trivial)) ev_es
        (hty_tmc_es' 0 zeroGhostWalked)
    obtain ⟨vtype, hinf_val, hde_val⟩ :=
      scoped_core_check (c := c) hrc_kc.toRCRep (typesRep_of_nil_eq c.κ hm_kc)
        (ghostScoped_zero zeroGhostWalked) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_kc) (fun _ _ => trivial)) ev_kc
        (hval_tmc_kc' 0 zeroGhostWalked) (hty_tmc_kc' 0 zeroGhostWalked)
    have hnrole : ∀ r : Ix.Kernel.Role, IxVM.Refinement.compilerTrust r = false →
        keyOf t a ≠ .role r := hnr _ (List.mem_singleton.mpr rfl)
    have hres_name : Ix.Kernel.reservedBasisNames.contains cv'.name = false :=
      reservedBasisNames_false_of_ne_nonTrustRole hnrole
    have hnoprj : cv'.name.isProjFnShape = false := isProjFnShape_of_isBaseKey hbase
    have hcv_run : ConstantValRunJ rulesJ env cv' ty' :=
      ⟨by rw [hfresh_cv]; rfl, hres_name, hnoprj, levelParam_nodup_of_nodup List.nodup_range,
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
    exact ⟨hclean, hinv.cons_value (cn := .defnInfo cv' val' hn) (a₀ := a) rfl hfresh_cv
      (fun _ => ne_projTableName_of_isBaseKey hbase) (fun _ _ e => nomatch e)
      (fun _ _ _ e => nomatch e) (fun _ _ _ _ e => nomatch e) (fun _ e => nomatch e)
      (FullDeclInv.step_of_foldInv_clean hclean
        (foldInv_step_declRunJ (d := .defnDecl cv' val' hn) (fun _ _ heq => nomatch heq) hdecl))
      (foldStoreInv_step_declRunJ (d := .defnDecl cv' val' hn) hinv.store (fun _ _ heq => nomatch heq) hdecl)
      (hreload _ (List.mem_singleton.mpr rfl))⟩
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
    obtain ⟨_, hty'_nfv, hty'_bvs, hty'_ann⟩ := tmC_closed_props hty_tmc_es'
    obtain ⟨_, hval'_nfv, hval'_bvs, hval'_ann⟩ := tmC_closed_props hval_tmc_kc'
    obtain ⟨stype, u, ℓ, hinf_ty, hred_ty, hℓ, hu⟩ :=
      scoped_core_ensure_sort (c := c) hrc_es.toRCRep (typesRep_of_nil_eq c.κ hm_es)
        (ghostScoped_zero zeroGhostWalked) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_es) (fun _ _ => trivial)) ev_es
        (hty_tmc_es' 0 zeroGhostWalked)
    have hisZero : (rulesJ (md := .anon)).isZero u :=
      thm_isZero_of_level_equal Levels.l2
        (RomBound.bounded_mono hbound hsub_le) hℓ hu hm_le ev_le
    obtain ⟨vtype, hinf_val, hde_val⟩ :=
      scoped_core_check (c := c) hrc_kc.toRCRep (typesRep_of_nil_eq c.κ hm_kc)
        (ghostScoped_zero zeroGhostWalked) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_kc) (fun _ _ => trivial)) ev_kc
        (hval_tmc_kc' 0 zeroGhostWalked) (hty_tmc_kc' 0 zeroGhostWalked)
    have hnrole : ∀ r : Ix.Kernel.Role, IxVM.Refinement.compilerTrust r = false →
        keyOf t a ≠ .role r := hnr _ (List.mem_singleton.mpr rfl)
    have hres_name : Ix.Kernel.reservedBasisNames.contains cv'.name = false :=
      reservedBasisNames_false_of_ne_nonTrustRole hnrole
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
    exact ⟨hclean, hinv.cons_value (cn := .thmInfo cv' val') (a₀ := a) rfl hfresh_cv
      (fun _ => ne_projTableName_of_isBaseKey hbase) (fun _ _ e => nomatch e)
      (fun _ _ _ e => nomatch e) (fun _ _ _ _ e => nomatch e) (fun _ e => nomatch e)
      (FullDeclInv.step_of_foldInv_clean hclean
        (foldInv_step_declRunJ (d := .thmDecl cv' val') (fun _ _ heq => nomatch heq) hdecl))
      (foldStoreInv_step_declRunJ (d := .thmDecl cv' val') hinv.store (fun _ _ heq => nomatch heq) hdecl)
      (hreload _ (List.mem_singleton.mpr rfl))⟩
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
    obtain ⟨_, hty'_nfv, hty'_bvs, hty'_ann⟩ := tmC_closed_props hty_tmc_es'
    obtain ⟨_, hval'_nfv, hval'_bvs, hval'_ann⟩ := tmC_closed_props hval_tmc_kc'
    obtain ⟨stype, u, _, hinf_ty, hred_ty, _, _⟩ :=
      scoped_core_ensure_sort (c := c) hrc_es.toRCRep (typesRep_of_nil_eq c.κ hm_es)
        (ghostScoped_zero zeroGhostWalked) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_es) (fun _ _ => trivial)) ev_es
        (hty_tmc_es' 0 zeroGhostWalked)
    obtain ⟨vtype, hinf_val, hde_val⟩ :=
      scoped_core_check (c := c) hrc_kc.toRCRep (typesRep_of_nil_eq c.κ hm_kc)
        (ghostScoped_zero zeroGhostWalked) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_kc) (fun _ _ => trivial)) ev_kc
        (hval_tmc_kc' 0 zeroGhostWalked) (hty_tmc_kc' 0 zeroGhostWalked)
    have hnrole : ∀ r : Ix.Kernel.Role, IxVM.Refinement.compilerTrust r = false →
        keyOf t a ≠ .role r := hnr _ (List.mem_singleton.mpr rfl)
    have hres_name : Ix.Kernel.reservedBasisNames.contains cv'.name = false :=
      reservedBasisNames_false_of_ne_nonTrustRole hnrole
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
    exact ⟨hclean, hinv.cons_value (cn := .axiomInfo cv') (a₀ := a) rfl hfresh_cv
      (fun _ => ne_projTableName_of_isBaseKey hbase) (fun _ _ e => nomatch e)
      (fun _ _ _ e => nomatch e) (fun _ _ _ _ e => nomatch e) (fun _ e => nomatch e)
      (FullDeclInv.step_of_foldInv_clean hclean
        (foldInv_step_declRunJ (d := .opaqueDecl cv' val') (fun _ _ heq => nomatch heq) hdecl))
      (foldStoreInv_step_declRunJ (d := .opaqueDecl cv' val') hinv.store (fun _ _ heq => nomatch heq) hdecl)
      (hreload _ (List.mem_singleton.mpr rfl))⟩


/-- **The step at the start of a fold.** At the empty environment under the group limit `0` the
prefix invariant holds (`prefixInv_empty`) and every key is fresh, so the step's hypotheses are
the inputs about the record alone: the invariant and the freshness hypotheses of
`walkedConst_step` are jointly satisfiable, and its conclusion is the invariant of the next
step. -/
theorem walkedConst_step_empty
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {E_core : Ixon.Env} {order_role : List _root_.Address} {d d' : Declaration .anon}
    (hdec : L1.EnvDecoded E_core) (htwf : t.wf = true)
    (hchk : CheckedConstOriginAt (Ctx.stored ⟨E_core, Ix.Kernel.Env.empty, t, some 0⟩).κ 0 calls
      t bAddr E_core order_role d d')
    (hgood : Good ⟨E_core, Ix.Kernel.Env.empty, t, none⟩ calls)
    (hnr : ∀ ci₀ ∈ IxVM.Consistency.installs d, ∀ r : Ix.Kernel.Role,
      IxVM.Refinement.compilerTrust r = false → ci₀.name ≠ .role r)
    (hreload : ∀ cn ∈ IxVM.Consistency.installs d',
      ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address),
        ObsFn W "Ingress::get_ci" [addr] h ptr h' cs →
        Good ⟨E_core, Ix.Kernel.Env.empty, t, some 0⟩ cs →
        Bytes.RepAddressRef addrTy h a addr → keyOf t (ixAddr a) = cn.name →
        CIPtrRep (Ctx.stored ⟨E_core, ⟨cn :: Ix.Kernel.Env.empty.consts⟩, t, some 0⟩).κ h' ptr
          cn) :
    CleanInstallStep Ix.Kernel.Env.empty d
        ⟨IxVM.Consistency.installs d' ++ Ix.Kernel.Env.empty.consts⟩ ∧
      PrefixInv.{u} E_core t 0 ⟨IxVM.Consistency.installs d' ++ Ix.Kernel.Env.empty.consts⟩ :=
  walkedConst_step (prefixInv_empty hdec htwf) hchk hgood (fun _ _ => rfl) hnr hreload

end IxVM.Refinement.Decl
