import IxVMRefinement.Decl.DeclSpecs
import IxVMRefinement.Assembly.Bridge
import IxVMRefinement.Assembly.LoadGlue
import IxVMRefinement.Assembly.RoleFacts

/-!
# Walked Constant Declaration Steps (`DeclWalkedConst.lean`)

Proves one-step advancement of `FullDeclInv` and `CleanInstallStep` (hence
`IxVM.Consistency.InstallStep`) across walked non-role constant declarations
(`Assembly.CheckedConstOrigin`: `.axiomDecl`, `.defnDecl`, `.thmDecl`, `.opaqueDecl`) as well as
quotient and basis declarations (`.quotDecl`, `.basisDecl`), parameterized over the context-facts
bundle `FoldContextFacts E_core t env`.
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
    ModeledRules.CoreFacts ⟨E_core, env, t, lim⟩ :=
  ⟨hctx.envFacts hS lim, hctx.loadFacts hS lim⟩

/-! ## Non-role Key Facts (`a ∉ order_role`) -/

/-- Any address bound in an admitted role table `t` belongs to `order_role`; hence an address
`a ∉ order_role` has `t.roleOf? a = none` and `Core.keyOf t a ≠ .role r` for every `r`. -/
theorem keyOf_ne_role_of_not_order_role
    {V_view : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} {E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order_role : List _root_.Address} {envA : Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    (hadm : Assembly.TableAdmittedAt V_view b t E_role limits order_role envA pre st_role decls_role)
    {a : _root_.Address} (hnot : a ∉ order_role) :
    ∀ r : Ix.Kernel.Role, keyOf t a ≠ .role r := by
  have htwf : t.wf = true := Assembly.tableWf_of_admitBinding hadm.admitBinding
  intro r heq
  unfold keyOf at heq
  cases hro : t.roleOf? a with
  | none =>
    rw [hro] at heq
    exact nomatch heq
  | some r' =>
    rw [hro] at heq
    injection heq with hr_eq
    subst hr_eq
    have hadr : t.addressOf? r = some a := ((Ix.Kernel.RoleTable.wf_iff.mp htwf).2 r a).mpr hro
    have hseed : IxVM.Refinement.BindingSeeds t a := Or.inl ⟨r, hadr⟩
    have hin : a ∈ order_role := hadm.closureOrder.seeds_mem a hseed (hadm.seeds_in a hseed)
    exact hnot hin

theorem reservedBasisNames_false_of_ne_role {k : KKey}
    (hne : ∀ r : Ix.Kernel.Role, k ≠ .role r) :
    Ix.Kernel.reservedBasisNames.contains k = false := by
  cases k with
  | role r => exact absurd rfl (hne r)
  | id _ => decide
  | name _ => decide
  | aux _ _ => decide

theorem natOpNames_false_of_ne_role {k : KKey}
    (hne : ∀ r : Ix.Kernel.Role, k ≠ .role r) :
    Ix.Kernel.natOpNames.contains k = false := by
  cases k with
  | role r => exact absurd rfl (hne r)
  | id _ => decide
  | name _ => decide
  | aux _ _ => decide

theorem natDivModNames_false_of_ne_role {k : KKey}
    (hne : ∀ r : Ix.Kernel.Role, k ≠ .role r) :
    Ix.Kernel.natDivModNames.contains k = false := by
  cases k with
  | role r => exact absurd rfl (hne r)
  | id _ => decide
  | name _ => decide
  | aux _ _ => decide

/-! ## Level-Parameter and Term Representation Helpers -/

private theorem allLevelParamsDefined_liftLooseBVars {lps : List LevelParam} (n : Nat) :
    ∀ (e : KExpr) (c : Nat),
      e.allLevelParamsDefined lps = true →
      (e.liftLooseBVars n c).allLevelParamsDefined lps = true
  | .bvar _, _, _ => rfl
  | .fvar i ty, c, h => by
    simp only [Expr.allLevelParamsDefined] at h
    simp only [Expr.liftLooseBVars, Expr.allLevelParamsDefined]
    exact allLevelParamsDefined_liftLooseBVars n ty c h
  | .sort _, _, h => h
  | .const _ _, _, h => h
  | .lit _, _, _ => rfl
  | .app f a, c, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨allLevelParamsDefined_liftLooseBVars n f c h.1,
      allLevelParamsDefined_liftLooseBVars n a c h.2⟩
  | .lam ty b _, c, h | .forallE ty b _, c, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨allLevelParamsDefined_liftLooseBVars n ty c h.1,
      allLevelParamsDefined_liftLooseBVars n b (c + 1) h.2⟩
  | .letE ty v b _, c, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨allLevelParamsDefined_liftLooseBVars n ty c h.1.1,
      allLevelParamsDefined_liftLooseBVars n v c h.1.2⟩,
      allLevelParamsDefined_liftLooseBVars n b (c + 1) h.2⟩
  | .proj _ _ e, c, h => by
    simp only [Expr.allLevelParamsDefined] at h
    simp only [Expr.liftLooseBVars, Expr.allLevelParamsDefined]
    exact allLevelParamsDefined_liftLooseBVars n e c h

private theorem allLevelParamsDefined_instantiate1Lift {lps : List LevelParam} {v : KExpr}
    (hv : v.allLevelParamsDefined lps = true) :
    ∀ (b : KExpr) (j : Nat),
      b.allLevelParamsDefined lps = true →
      (b.instantiate1Lift v j).allLevelParamsDefined lps = true
  | .bvar idx, j, _ => by
    simp only [Expr.instantiate1Lift]
    split
    · exact allLevelParamsDefined_liftLooseBVars j v 0 hv
    · split <;> rfl
  | .fvar i ty, j, hb => by
    simp only [Expr.allLevelParamsDefined] at hb
    simp only [Expr.instantiate1Lift, Expr.allLevelParamsDefined]
    exact allLevelParamsDefined_instantiate1Lift hv ty j hb
  | .sort _, _, hb => hb
  | .const _ _, _, hb => hb
  | .lit _, _, _ => rfl
  | .app f a, j, hb => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1Lift, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨allLevelParamsDefined_instantiate1Lift hv f j hb.1,
      allLevelParamsDefined_instantiate1Lift hv a j hb.2⟩
  | .lam ty b _, j, hb | .forallE ty b _, j, hb => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1Lift, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨allLevelParamsDefined_instantiate1Lift hv ty j hb.1,
      allLevelParamsDefined_instantiate1Lift hv b (j + 1) hb.2⟩
  | .letE ty val b _, j, hb => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1Lift, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨allLevelParamsDefined_instantiate1Lift hv ty j hb.1.1,
      allLevelParamsDefined_instantiate1Lift hv val j hb.1.2⟩,
      allLevelParamsDefined_instantiate1Lift hv b (j + 1) hb.2⟩
  | .proj _ _ e, j, hb => by
    simp only [Expr.allLevelParamsDefined] at hb
    simp only [Expr.instantiate1Lift, Expr.allLevelParamsDefined]
    exact allLevelParamsDefined_instantiate1Lift hv e j hb

theorem annotates_allLevelParamsDefined {lps : List LevelParam} {e' e₀ : KExpr}
    (hann : IxVM.Consistency.Annotates e' e₀)
    (hdef : e₀.allLevelParamsDefined lps = true) :
    e'.allLevelParamsDefined lps = true := by
  induction hann with
  | bvar | sort | const | lit => exact hdef
  | fvar _ ih =>
    simp only [Expr.allLevelParamsDefined] at hdef ⊢
    exact ih hdef
  | app _ _ ihf iha =>
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef ⊢
    exact ⟨ihf hdef.1, iha hdef.2⟩
  | lam _ _ ihty ihb | forallE _ _ ihty ihb =>
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef ⊢
    exact ⟨ihty hdef.1, ihb hdef.2⟩
  | proj _ ihe =>
    simp only [Expr.allLevelParamsDefined] at hdef ⊢
    exact ihe hdef
  | letE _ ih =>
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef
    exact ih (allLevelParamsDefined_instantiate1Lift hdef.1.2 _ 0 hdef.2)

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
    (hne_role : ∀ a, a ∉ order_role → ∀ r : Ix.Kernel.Role, keyOf t a ≠ .role r) :
    ∃ env₂, CleanInstallStep env d env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], FullDeclInv V env → FullDeclInv V env₂ := by
  cases hchk with
  | @axiomDecl a _ _ nlvls ty₀ ty' lim _ _ _ m_ax _ x_rc _ x_addr _ v_ax _ cs_ax
      hnot_role _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrc_ax ha_ax ev_ax hne_ax _ hsub_ax =>
    obtain ⟨a', ha'_ref, heq_a⟩ := ha_ax
    let c : Ctx := ⟨E_core, env, t, some lim⟩
    have hgood_c : Good c calls := hgood
    obtain ⟨ro, hro_addr, _, _⟩ :=
      axiom_standing_spec rolesSpec (hgood_c.sub hsub_ax) hctx.tableWf
        hrc_ax.toRCRep (rcFullRep_axiomsNil hrc_ax) ha'_ref ev_ax hne_ax
    have hk : keyOf t a = .role ro := by
      have hk0 := keyOf_of_addressOf hctx.tableWf hro_addr
      rwa [heq_a] at hk0
    exact False.elim (hne_role a hnot_role ro hk)
  | @defnDecl a nlvls ty₀ val₀ ty' val' hn lim m_pre1 m_es m_es' m_pre2 m_kc m_kc'
      x_rc x_ty x_val v_sort r_kc cs_es cs_kc
      hnot_role _ _ hty_def _ hval_def hty_ann hval_ann
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
    have hty'_def : ty'.allLevelParamsDefined (List.range nlvls) = true :=
      annotates_allLevelParamsDefined hty_ann hty_def
    have hval'_def : val'.allLevelParamsDefined (List.range nlvls) = true :=
      annotates_allLevelParamsDefined hval_ann hval_def
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
      reservedBasisNames_false_of_ne_role hnrole
    have hnoprj : cv'.name.isProjFnShape = false := isProjFnShape_of_isBaseKey hbase
    have hcv_run : ConstantValRunJ rulesJ env cv' ty' :=
      ⟨by rw [hfresh_cv]; rfl, hres, hnoprj, List.nodup_range,
        hty'_bvs, hty'_nfv, hty'_ann, hty'_def,
        infer_constsResolve hinf_ty hef.store hty'_nfv, stype, u, hinf_ty, hred_ty⟩
    have hv_run : ValueFrontRunJ rulesJ env cv' val' ty' val' :=
      ⟨hval'_bvs, hval'_nfv, hval'_ann, hval'_def,
        infer_constsResolve hinf_val hef.store hval'_nfv, vtype, hinf_val, hde_val⟩
    have hnat_false : Ix.Kernel.natOpNames.contains cv'.name = false :=
      natOpNames_false_of_ne_role hnrole
    have hdm_false : Ix.Kernel.natDivModNames.contains cv'.name = false :=
      natDivModNames_false_of_ne_role hnrole
    have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.defnDecl cv' val' hn)
        ⟨.defnInfo cv' val' hn :: env.consts⟩ :=
      ⟨ty', val', hcv_run, hv_run, rfl,
        fun hc => by rw [hnat_false] at hc; exact nomatch hc,
        fun hc => by rw [hdm_false] at hc; exact nomatch hc⟩
    exact fullDeclInv_step_declRunJ (fun _ _ heq => nomatch heq) hdecl V hInv
  | @thmDecl a nlvls ty₀ val₀ ty' val' lim m_pre1 m_es m_es' m_le m_le' m_pre2 m_kc m_kc'
      x_rc x_ty x_val v_sort r_kc cs_es cs_le cs_kc
      hnot_role _ _ hty_def _ hval_def hty_ann hval_ann
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
    have hty'_def : ty'.allLevelParamsDefined (List.range nlvls) = true :=
      annotates_allLevelParamsDefined hty_ann hty_def
    have hval'_def : val'.allLevelParamsDefined (List.range nlvls) = true :=
      annotates_allLevelParamsDefined hval_ann hval_def
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
      reservedBasisNames_false_of_ne_role hnrole
    have hnoprj : cv'.name.isProjFnShape = false := isProjFnShape_of_isBaseKey hbase
    have hcv_run : ConstantValRunJ rulesJ env cv' ty' :=
      ⟨by rw [hfresh_cv]; rfl, hres, hnoprj, List.nodup_range,
        hty'_bvs, hty'_nfv, hty'_ann, hty'_def,
        infer_constsResolve hinf_ty hef.store hty'_nfv, stype, u, hinf_ty, hred_ty⟩
    have hv_run : ValueFrontRunJ rulesJ env cv' val' ty' val' :=
      ⟨hval'_bvs, hval'_nfv, hval'_ann, hval'_def,
        infer_constsResolve hinf_val hef.store hval'_nfv, vtype, hinf_val, hde_val⟩
    have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.thmDecl cv' val')
        ⟨.thmInfo cv' val' :: env.consts⟩ :=
      ⟨ty', val', hcv_run, ⟨stype, u, hinf_ty, hred_ty, hisZero⟩, hv_run, rfl⟩
    exact fullDeclInv_step_declRunJ (fun _ _ heq => nomatch heq) hdecl V hInv
  | @opaqueDecl a nlvls ty₀ val₀ ty' val' lim m_pre1 m_es m_es' m_pre2 m_kc m_kc'
      x_rc x_ty x_val v_sort r_kc cs_es cs_kc
      hnot_role _ _ hty_def _ hval_def hty_ann hval_ann
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
    have hty'_def : ty'.allLevelParamsDefined (List.range nlvls) = true :=
      annotates_allLevelParamsDefined hty_ann hty_def
    have hval'_def : val'.allLevelParamsDefined (List.range nlvls) = true :=
      annotates_allLevelParamsDefined hval_ann hval_def
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
      reservedBasisNames_false_of_ne_role hnrole
    have hnoprj : cv'.name.isProjFnShape = false := isProjFnShape_of_isBaseKey hbase
    have hcv_run : ConstantValRunJ rulesJ env cv' ty' :=
      ⟨by rw [hfresh_cv]; rfl, hres, hnoprj, List.nodup_range,
        hty'_bvs, hty'_nfv, hty'_ann, hty'_def,
        infer_constsResolve hinf_ty hef.store hty'_nfv, stype, u, hinf_ty, hred_ty⟩
    have hv_run : ValueFrontRunJ rulesJ env cv' val' ty' val' :=
      ⟨hval'_bvs, hval'_nfv, hval'_ann, hval'_def,
        infer_constsResolve hinf_val hef.store hval'_nfv, vtype, hinf_val, hde_val⟩
    have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.opaqueDecl cv' val')
        ⟨.axiomInfo cv' :: env.consts⟩ :=
      ⟨ty', val', hcv_run, hv_run, rfl⟩
    exact fullDeclInv_step_declRunJ (fun _ _ heq => nomatch heq) hdecl V hInv

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
    have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.quotDecl .type cv)
        ⟨BasisKind.quotK.declsA.reverse ++ env.consts⟩ := hrun
    exact ⟨⟨BasisKind.quotK.declsA.reverse ++ env.consts⟩,
      CleanInstallStep.of_baseList hinst hbase,
      fun V _ hInv => fullDeclInv_step_declRunJ (fun _ _ heq => nomatch heq) hdecl V hInv⟩
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
  have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.basisDecl kind)
      ⟨kind.declsA.reverse ++ env.consts⟩ := hrun
  exact ⟨⟨kind.declsA.reverse ++ env.consts⟩,
    CleanInstallStep.of_baseList hinst hbase,
    fun V _ hInv => fullDeclInv_step_declRunJ (fun _ _ heq => nomatch heq) hdecl V hInv⟩

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
  have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.indDecl block nP)
      ⟨kind.declsA.reverse ++ env.consts⟩ := by
    simp only [DeclRunJ, hpin]
    exact hrun
  exact ⟨⟨kind.declsA.reverse ++ env.consts⟩,
    CleanInstallStep.of_baseList hinst hbase,
    fun V _ hInv =>
      fullDeclInv_step_declRunJ (fun _ _ _ hp => by rw [hpin] at hp; exact nomatch hp) hdecl V hInv⟩

end IxVM.Refinement.Decl
