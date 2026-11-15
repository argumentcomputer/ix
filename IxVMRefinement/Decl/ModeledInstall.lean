import IxVMRefinement.Decl.ModeledAux
import IxC.Kernel.Model.IndCons
import IxC.Kernel.Model.Inductives.StructCaps
import IxC.Kernel.Model.Swap
import IxC.Kernel.Semantics.IndRecsCore
import IxC.Kernel.Semantics.IndBlockFacts
import IxC.Kernel.Verify.Denote.OpenVars

/-!
# Unpositionalized 4-Phase Modeled Block Installation (`ModeledInstall.lean`)

This module completes the semantic and store-invariant installation of a VM-checked modeled
inductive block at its original level-parameter lists `lps` (`lps.Perm (List.range lps.length)`):

1. **`CleanInstallStep` and `DeclInvM` step combinators**:
   Packages `InstallStep` together with `AuxRootSynced` preservation, `NoNewProjForOld`, and
   `isSome` monotonicity, lifting `Value.lean`'s standalone and advice declaration steps to
   `DeclInvM`.
2. **Unpositionalization (`UnposEntry`, `UnposAgree`, `denoteMeta_unpos_eq`)**:
   Proves exact `denoteMeta` agreement between a real prefix environment `E_real` (storing new
   block constants at `lps`) and its positional counterpart `E_pos` (storing new block constants at
   `List.range lps.length`), while keeping pre-existing `env` constants identical.
3. **Lockstep `EnvModelM` and `DeclStoreInv` steps**:
   Steps `(E_real, mp_real)` and `(E_pos, mp_pos)` in lockstep across non-recursor members and
   provisional rule-empty recursors, then unpositionalizes `RecRuleLaw`, `RuleFacts`, and
   `RuleFactsS` across the final rule swap (`envSelf_real → env₂_base`).
4. **Dummy `.model` companions and `modeledBlock_install_step`**:
   Prepends well-typed dummy `.model` definitions (`dummyModelCI r` via `DeclDefnRunJ rulesJ`) for
   each new recursor `r` so `HasModel env₂ r` holds while keeping `InstallStep` valid (since
   `InstallStep` permits `.aux` companions), discharging `RecK`, `RecShape`, `AuxRootSynced`, and
   `DeclInvM` in full.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Library Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel
open Ix.Kernel.Model
open Ix.Kernel.Open (StoreInv)
open Ix.Kernel.Term Ix.Kernel.Verify Ix.Kernel.SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal BinderMeta RecRule
  RecRuleFire IndCaps BasisKind Declaration LevelParam EnvExt ReducibilityHint Derived SwapShList
  openPisAtFvars eqName eqA auxKey projTableName nestedRuleShape recRuleBits recRuleKOf
  recRuleEtaOf isEqHead hasFvar_renameConsts swapSh_find?_corr)
open Ix.Kernel.Rules (Annot Red DefEq Infer)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u

/-! ## `CleanInstallStep` and `DeclInvM` Step Combinators -/

/-- `InstallStep` paired with `AuxRootSynced` preservation, `NoNewProjForOld`, and `isSome`
monotonicity (needed both along the main `L5` fold and across advice steps). -/
structure CleanInstallStep (env : Env .anon) (d : Declaration .anon) (env₂ : Env .anon) : Prop where
  step : IxVM.Consistency.InstallStep env d env₂
  auxSynced : AuxRootSynced env → AuxRootSynced env₂
  noNewProj : NoNewProjForOld env env₂
  monoSome : ∀ k : KKey, (env.find? k).isSome = true → (env₂.find? k).isSome = true

theorem CleanInstallStep.empty {env : Env .anon} {d : Declaration .anon}
    (hempty : IxVM.Consistency.installs d = []) :
    CleanInstallStep env d env where
  step := installStep_empty hempty
  auxSynced h := h
  noNewProj := NoNewProjForOld.refl env
  monoSome _ hk := hk

theorem CleanInstallStep.of_baseList {env : Env .anon} {d : Declaration .anon}
    {new : List (ConstantInfo .anon)}
    (hstep : IxVM.Consistency.InstallStep env d ⟨new ++ env.consts⟩)
    (hbase : ∀ ci ∈ new, isBaseKey ci.name = true) :
    CleanInstallStep env d ⟨new ++ env.consts⟩ where
  step := hstep
  auxSynced h := h.of_prepend fun ci hci => by
    rw [base_of_isBaseKey (hbase ci hci)]
    exact env_find?_isSome_of_mem_prefix hci
  noNewProj := NoNewProjForOld.prepend_nonProjTable fun ci hci T =>
    ne_projTableName_of_isBaseKey (hbase ci hci)
  monoSome _ hk := env_find?_isSome_of_tail hk

theorem CleanInstallStep.single {env : Env .anon} {d : Declaration .anon}
    {ci ci₀ : ConstantInfo .anon}
    (hinst : IxVM.Consistency.installs d = [ci₀])
    (hstored : IxVM.Consistency.StoredAs ci ci₀)
    (hfresh : env.find? ci.name = none)
    (hbase : isBaseKey ci₀.name = true) :
    CleanInstallStep env d ⟨ci :: env.consts⟩ :=
  CleanInstallStep.of_baseList (new := [ci])
    (installStep_single hinst hstored hfresh)
    (fun c hc => by
      rw [List.mem_singleton.mp hc, hstored.name_eq]
      exact hbase)

theorem basis_declsA_isBaseKey (kind : BasisKind) :
    (kind.declsA (md := .anon)).all (fun ci => isBaseKey ci.name) = true := by
  cases kind <;> decide

theorem s0Checked_installs_isBaseKey {calls : List (Call F)} {env : Env .anon}
    {d : Declaration .anon} (hchk : S0.Checked calls env d) :
    ∀ ci₀ ∈ IxVM.Consistency.installs d, isBaseKey ci₀.name = true := by
  obtain ⟨_, t, _, _, _, hall⟩ := hchk
  intro ci₀ hmem
  obtain ⟨_, _, _, _, _, _, _, a, _, _, _, _, hkey, _, _⟩ := hall ci₀ hmem
  rw [← hkey]
  exact isBaseKey_keyOf t a

theorem cleanInstallStep_of_checked_fresh {calls : List (Call F)} {env : Env .anon}
    {d : Declaration .anon} (hchk : S0.Checked calls env d)
    (hnd : ((IxVM.Consistency.installs d).map (·.name)).Nodup)
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs d, env.find? ci₀.name = none) :
    ∃ env₀, CleanInstallStep env d env₀ := by
  have hbase₀ := s0Checked_installs_isBaseKey hchk
  obtain ⟨_, _, _, _, _, hall⟩ := hchk
  have hex : ∀ ci₀ ∈ IxVM.Consistency.installs d, ∃ ci, IxVM.Consistency.StoredAs ci ci₀ := by
    intro ci₀ h
    obtain ⟨_, _, _, _, _, _, _, _, ci, _, _, _, _, _, hs⟩ := hall ci₀ h
    exact ⟨ci, hs⟩
  have hlist : ∀ (l : List (ConstantInfo .anon)),
      (∀ ci₀ ∈ l, ∃ ci, IxVM.Consistency.StoredAs ci ci₀) →
      ∃ new : List (ConstantInfo .anon),
        new.map (·.name) = l.map (·.name) ∧
        (∀ ci₀ ∈ l, ∃ ci ∈ new, IxVM.Consistency.StoredAs ci ci₀) ∧
        (∀ ci ∈ new, ∃ ci₀ ∈ l, ci₀.name = ci.name) := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨[], rfl, (fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    | cons c₀ tl ih =>
      intro h
      obtain ⟨c, hc⟩ := h c₀ List.mem_cons_self
      obtain ⟨rest, hnm, hcov, hex'⟩ := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
      refine ⟨c :: rest, by simp [hc.name_eq, hnm], ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hxtl
        · exact ⟨c, List.mem_cons_self, hc⟩
        · obtain ⟨c', hm, hs⟩ := hcov x hxtl
          exact ⟨c', List.mem_cons_of_mem _ hm, hs⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hytl
        · exact ⟨c₀, List.mem_cons_self, hc.name_eq.symm⟩
        · obtain ⟨x, hm, hn⟩ := hex' y hytl
          exact ⟨x, List.mem_cons_of_mem _ hm, hn⟩
  obtain ⟨new, hnames, hcov, hextra⟩ := hlist (IxVM.Consistency.installs d) hex
  have hstep : IxVM.Consistency.InstallStep env d ⟨new ++ env.consts⟩ := by
    refine ⟨new, rfl, hnames ▸ hnd, ?_, hcov, fun ci hci => Or.inl (hextra ci hci)⟩
    intro ci hci
    obtain ⟨ci₀, hm, hneq⟩ := hextra ci hci
    rw [← hneq]
    exact hfresh ci₀ hm
  refine ⟨⟨new ++ env.consts⟩, CleanInstallStep.of_baseList hstep fun ci hci => ?_⟩
  obtain ⟨ci₀, hm, hneq⟩ := hextra ci hci
  rw [← hneq]
  exact hbase₀ ci₀ hm

/-- Lift a store-assumed `CleanInstallStep` + `DeclRunJ` step to `DeclInvM`. -/
theorem declsM_step_of_store {calls : List (Call F)} {env : Env .anon}
    {d : Declaration .anon} (hchk : S0.Checked calls env d)
    (hnd : ((IxVM.Consistency.installs d).map (·.name)).Nodup)
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs d, env.find? ci₀.name = none)
    (hstep : DeclStoreInv env →
      ∃ env₂, CleanInstallStep env d env₂ ∧
        DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂) :
    ∃ env₂, CleanInstallStep env d env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInvM V env → DeclInvM V env₂ := by
  by_cases hS : DeclStoreInv env
  · obtain ⟨env₂, hclean, hrun⟩ := hstep hS
    exact ⟨env₂, hclean, fun _ _ hInvM =>
      ⟨hInvM.inv.step_declRunJ hrun, hclean.auxSynced hInvM.auxSynced⟩⟩
  · obtain ⟨env₀, hclean⟩ := cleanInstallStep_of_checked_fresh hchk hnd hfresh
    exact ⟨env₀, hclean, fun _ _ hInvM => absurd hInvM.inv.store hS⟩

/-- Step preservation for standalone `.defnDecl` in `DeclInvM` (also used for advice definitions). -/
theorem defnDecl_step_M (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Env .anon}
    {cv : ConstantVal .anon} {value : KExpr} {hint : ReducibilityHint}
    (hchk : S0.Checked calls env (.defnDecl cv value hint))
    (hx : DeclValueExtraFacts calls env (.defnDecl cv value hint)) :
    ∃ env₂, CleanInstallStep env (.defnDecl cv value hint) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInvM V env → DeclInvM V env₂ := by
  have hinst_eq : IxVM.Consistency.installs (.defnDecl cv value hint) =
      [.defnInfo cv value hint] := rfl
  have hbase_cv : isBaseKey cv.name = true :=
    s0Checked_installs_isBaseKey hchk (.defnInfo cv value hint) (List.mem_singleton.mpr rfl)
  refine declsM_step_of_store hchk hx.installsNodup hx.installsFresh fun hS => ?_
  obtain ⟨E, t, htwf, hloads, hgood, hall⟩ := hchk
  have hmem : ConstantInfo.defnInfo cv value hint ∈
      IxVM.Consistency.installs (.defnDecl cv value hint) := List.mem_singleton.mpr rfl
  obtain ⟨cl, hcl, hname, rc, v, ap, lim, a, ci, hargs, hrc, hadr, hkey, hci, hstored⟩ :=
    hall (.defnInfo cv value hint) hmem
  obtain ⟨hR_fn, hsafe, -, hres, hcv_bvs, hcv_nfv, hrange,
    ⟨r_cl, h'_cl, subcalls, ev_chk, hsub⟩, -, hdefn_exact, -, -⟩ :=
    hx.checkedValue E t cl rc v ap lim a ci (.defnInfo cv value hint) htwf hgood hcl hname hargs
      hrc hadr hkey hci hstored hmem
  obtain ⟨hval_bvs, hval_nfv, hexact⟩ := hdefn_exact cv value hint rfl
  cases ci with
  | axiomInfo _ | thmInfo _ _ | indInfo _ _ | ctorInfo _ _ _ | recInfo _ _ _ _
  | projInfo _ => cases hstored.2
  | defnInfo cvA value' hint' =>
    have ⟨⟨hcv_name, hcv_lps, hann_ty⟩, hann_val, hhint_eq⟩ := hstored
    change hint' = hint at hhint_eq
    subst hint'
    change cvA.name = cv.name at hcv_name
    change cvA.levelParams = cv.levelParams at hcv_lps
    change cv.levelParams = List.range cv.levelParams.length at hrange
    cases hexact with
    | quot _ hk =>
      rcases hk with ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;>
        cases h
    | defn hval hV =>
      rename_i nl ty val sf hn_v
      have hsf0 : sf = .construct "Ixon::DefinitionSafety" "Safe" [] := hsafe rfl
      subst hsf0
      let c : Ctx := ⟨E, env, t, lim⟩
      have hgood_c : Good c calls := hgood
      have hef : EnvFacts c := hS.toEnvFacts htwf (hR_fn hS)
      have hlf : LoadFacts c := hloads.withLim
      have hfresh_cv : env.find? cv.name = none := hx.installsFresh (.defnInfo cv value hint) hmem
      have hnoprj : cv.name.isProjFnShape = false := isProjFnShape_of_isBaseKey hbase_cv
      have hcvA_eq : cvA = ⟨cv.name, cv.levelParams, cvA.type⟩ := by
        cases cvA; cases hcv_name; cases hcv_lps; rfl
      have hval_cv : ValRepExact c.κ cl.heap nl ty ⟨cv.name, cv.levelParams, cvA.type⟩ :=
        hcvA_eq ▸ hval
      obtain ⟨v298, v335, v372, v416, v446, m299, m336, m373, m404, m417, m447, m508,
        cs309, cs346, cs383, cs427, cs457, cs479,
        ev311, ev348, hm404, ev385, ev429, ev459, hm508, ev481,
        _, hcs346, hcs383, hcs479⟩ :=
        check_const_defn_inv ev_chk
      have e_sc1 := ObsFn.heap_extends ev311
      have e_sc2 := ObsFn.heap_extends ev348
      obtain ⟨rfl, hnl, hperm, hty_rep0⟩ := hval_cv
      have hty_pos : posOf cv.levelParams cvA.type = cvA.type := by
        conv => lhs; rw [hrange]; exact posOf_range cv.levelParams.length cvA.type
      have hval_pos : posOf cvA.levelParams value' = value' := by
        rw [hcv_lps]; conv => lhs; rw [hrange]; exact posOf_range cv.levelParams.length value'
      rw [hty_pos] at hty_rep0
      rw [hval_pos] at hV
      let zg : Nat → KExpr := fun _ => .sort .zero
      have hlvl_ty0 : cvA.type.allLevelParamsDefined (List.range cv.levelParams.length) = true :=
        validate_expr_well_scoped_spec hnl (hty_rep0 0 zg) ev311
      have hlvl_ty : cvA.type.allLevelParamsDefined cv.levelParams = true := by
        rw [← hrange] at hlvl_ty0; exact hlvl_ty0
      have e_m404 : Heap.Extends cl.heap m404 :=
        hm404 ▸ (e_sc1.trans e_sc2).trans (heap_extends_append m336 _)
      have htypes404 : TypesRep c.κ zg m404 0 (.ptr (.enum kexprListEnum) m336.length) :=
        hm404 ▸ typesRep_alloc_nil c.κ zg m336
      obtain ⟨stype, u, _, hinf_ty, hred_ty, _, _⟩ :=
        core_ensure_sort hCore (hrc.mono e_m404) htypes404 (ghostScoped_zero zg) hef hlf
          (hgood_c.sub fun x hx => hsub x (hcs383 x hx)) ev385
          ((hty_rep0 0 zg).toTm.mono e_m404)
      have hty'_nfv : cvA.type.hasFvar = false := Tm.hasFvar_false (hty_rep0 0 zg).toTm
      have hcv_run : ConstantValRunJ rulesJ env cv cvA.type :=
        ⟨by rw [hfresh_cv]; rfl, hres, hnoprj, levelParam_nodup_of_perm_range hperm,
          hcv_bvs, hcv_nfv, annot_of_annotates hann_ty hcv_nfv hcv_bvs 0, hlvl_ty,
          infer_constsResolve hinf_ty hS.store hty'_nfv, stype, u, hinf_ty, hred_ty⟩
      have e_pre_chk : Heap.Extends cl.heap m447 :=
        e_m404.trans ((ObsFn.heap_extends ev385).trans
          ((ObsFn.heap_extends ev429).trans (ObsFn.heap_extends ev459)))
      have hv_run : ValueFrontRunJ rulesJ env cv value cvA.type value' :=
        valueFrontRunJ_of_front hCore hrange hval_bvs hval_nfv rfl hnl hty_rep0 hV hann_val
          e_sc1 e_pre_chk hrc hef hlf
          (hgood_c.sub fun x hx => hsub x (hcs346 x hx))
          (hgood_c.sub fun x hx => hsub x (hcs479 x hx))
          ev348 hm508 ev481
      obtain ⟨hop, hdm⟩ := hx.defnOpCertified cv value hint cvA.type value' rfl hS hcv_run hv_run
      have hfresh_ci : env.find? (ConstantInfo.defnInfo cvA value' hint).name = none := by
        show env.find? cvA.name = none; rw [hcv_name]; exact hfresh_cv
      refine ⟨⟨.defnInfo cvA value' hint :: env.consts⟩,
        CleanInstallStep.single hinst_eq hstored hfresh_ci hbase_cv, ?_⟩
      show DeclDefnRunJ rulesJ env cv value hint ⟨.defnInfo cvA value' hint :: env.consts⟩
      rw [hcvA_eq]
      exact ⟨cvA.type, value', hcv_run, hv_run, rfl, hop, hdm⟩

/-- Step preservation for standalone `.thmDecl` in `DeclInvM` (also used for advice theorems). -/
theorem thmDecl_step_M (hLevels : IxVM.Consistency.Levels) (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Env .anon}
    {cv : ConstantVal .anon} {value : KExpr}
    (hchk : S0.Checked calls env (.thmDecl cv value))
    (hx : DeclValueExtraFacts calls env (.thmDecl cv value)) :
    ∃ env₂, CleanInstallStep env (.thmDecl cv value) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInvM V env → DeclInvM V env₂ := by
  have hinst_eq : IxVM.Consistency.installs (.thmDecl cv value) = [.thmInfo cv value] := rfl
  have hbase_cv : isBaseKey cv.name = true :=
    s0Checked_installs_isBaseKey hchk (.thmInfo cv value) (List.mem_singleton.mpr rfl)
  refine declsM_step_of_store hchk hx.installsNodup hx.installsFresh fun hS => ?_
  obtain ⟨E, t, htwf, hloads, hgood, hall⟩ := hchk
  have hmem : ConstantInfo.thmInfo cv value ∈
      IxVM.Consistency.installs (.thmDecl cv value) := List.mem_singleton.mpr rfl
  obtain ⟨cl, hcl, hname, rc, v, ap, lim, a, ci, hargs, hrc, hadr, hkey, hci, hstored⟩ :=
    hall (.thmInfo cv value) hmem
  obtain ⟨hR_fn, -, -, hres, hcv_bvs, hcv_nfv, hrange,
    ⟨r_cl, h'_cl, subcalls, ev_chk, hsub⟩, -, -, hthm_exact, -⟩ :=
    hx.checkedValue E t cl rc v ap lim a ci (.thmInfo cv value) htwf hgood hcl hname hargs
      hrc hadr hkey hci hstored hmem
  obtain ⟨hval_bvs, hval_nfv, hexact⟩ := hthm_exact cv value rfl
  cases ci with
  | axiomInfo _ | defnInfo _ _ _ | indInfo _ _ | ctorInfo _ _ _ | recInfo _ _ _ _
  | projInfo _ => cases hstored.2
  | thmInfo cvA value' =>
    have ⟨⟨hcv_name, hcv_lps, hann_ty⟩, hann_val⟩ := hstored
    change cvA.name = cv.name at hcv_name
    change cvA.levelParams = cv.levelParams at hcv_lps
    change cv.levelParams = List.range cv.levelParams.length at hrange
    cases hexact with
    | quot _ hk =>
      rcases hk with ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;>
        cases h
    | thm hval hV =>
      rename_i nl ty val
      let c : Ctx := ⟨E, env, t, lim⟩
      have hgood_c : Good c calls := hgood
      have hef : EnvFacts c := hS.toEnvFacts htwf (hR_fn hS)
      have hlf : LoadFacts c := hloads.withLim
      have hfresh_cv : env.find? cv.name = none := hx.installsFresh (.thmInfo cv value) hmem
      have hnoprj : cv.name.isProjFnShape = false := isProjFnShape_of_isBaseKey hbase_cv
      have hcvA_eq : cvA = ⟨cv.name, cv.levelParams, cvA.type⟩ := by
        cases cvA; cases hcv_name; cases hcv_lps; rfl
      have hval_cv : ValRepExact c.κ cl.heap nl ty ⟨cv.name, cv.levelParams, cvA.type⟩ :=
        hcvA_eq ▸ hval
      obtain ⟨v543, v580, v617, v715, v745,
        m544, m581, m618, m649, m675, m696, m716, m746, m807,
        cs554, cs591, cs628, cs683, cs726, cs756, cs778,
        ev556, ev593, hm649, ev630, hm696, ev685, ev728, ev758, hm807, ev780,
        _, hcs591, hcs628, hcs683, hcs778⟩ :=
        check_const_thm_inv ev_chk
      have e_sc1 := ObsFn.heap_extends ev556
      have e_sc2 := ObsFn.heap_extends ev593
      obtain ⟨rfl, hnl, hperm, hty_rep0⟩ := hval_cv
      have hty_pos : posOf cv.levelParams cvA.type = cvA.type := by
        conv => lhs; rw [hrange]; exact posOf_range cv.levelParams.length cvA.type
      have hval_pos : posOf cvA.levelParams value' = value' := by
        rw [hcv_lps]; conv => lhs; rw [hrange]; exact posOf_range cv.levelParams.length value'
      rw [hty_pos] at hty_rep0
      rw [hval_pos] at hV
      let zg : Nat → KExpr := fun _ => .sort .zero
      have hlvl_ty0 : cvA.type.allLevelParamsDefined (List.range cv.levelParams.length) = true :=
        validate_expr_well_scoped_spec hnl (hty_rep0 0 zg) ev556
      have hlvl_ty : cvA.type.allLevelParamsDefined cv.levelParams = true := by
        rw [← hrange] at hlvl_ty0; exact hlvl_ty0
      have e_m649 : Heap.Extends cl.heap m649 :=
        hm649 ▸ (e_sc1.trans e_sc2).trans (heap_extends_append m581 _)
      have htypes649 : TypesRep c.κ zg m649 0 (.ptr (.enum kexprListEnum) m581.length) :=
        hm649 ▸ typesRep_alloc_nil c.κ zg m581
      obtain ⟨stype, u, ℓ, hinf_ty, hred_ty, hℓ, hu⟩ :=
        core_ensure_sort hCore (hrc.mono e_m649) htypes649 (ghostScoped_zero zg) hef hlf
          (hgood_c.sub fun x hx => hsub x (hcs628 x hx)) ev630
          ((hty_rep0 0 zg).toTm.mono e_m649)
      have hisZero : (rulesJ (md := .anon)).isZero u :=
        thm_isZero_of_level_equal hLevels
          (bounded_sub (fun x hx => hsub x (hcs683 x hx)) hgood.2)
          hℓ hu hm696 ev685
      have hty'_nfv : cvA.type.hasFvar = false := Tm.hasFvar_false (hty_rep0 0 zg).toTm
      have hcv_run : ConstantValRunJ rulesJ env cv cvA.type :=
        ⟨by rw [hfresh_cv]; rfl, hres, hnoprj, levelParam_nodup_of_perm_range hperm,
          hcv_bvs, hcv_nfv, annot_of_annotates hann_ty hcv_nfv hcv_bvs 0, hlvl_ty,
          infer_constsResolve hinf_ty hS.store hty'_nfv, stype, u, hinf_ty, hred_ty⟩
      have e_m696 : Heap.Extends m618 m696 := hm696 ▸ heap_extends_append m618 _
      have e_pre_chk : Heap.Extends cl.heap m746 :=
        e_m649.trans ((ObsFn.heap_extends ev630).trans
          (e_m696.trans ((ObsFn.heap_extends ev685).trans
            ((ObsFn.heap_extends ev728).trans (ObsFn.heap_extends ev758)))))
      have hv_run : ValueFrontRunJ rulesJ env cv value cvA.type value' :=
        valueFrontRunJ_of_front hCore hrange hval_bvs hval_nfv rfl hnl hty_rep0 hV hann_val
          e_sc1 e_pre_chk hrc hef hlf
          (hgood_c.sub fun x hx => hsub x (hcs591 x hx))
          (hgood_c.sub fun x hx => hsub x (hcs778 x hx))
          ev593 hm807 ev780
      have hfresh_ci : env.find? (ConstantInfo.thmInfo cvA value').name = none := by
        show env.find? cvA.name = none; rw [hcv_name]; exact hfresh_cv
      refine ⟨⟨.thmInfo cvA value' :: env.consts⟩,
        CleanInstallStep.single hinst_eq hstored hfresh_ci hbase_cv, ?_⟩
      show DeclThmRunJ rulesJ env cv value ⟨.thmInfo cvA value' :: env.consts⟩
      refine ⟨cvA.type, value', hcv_run, ⟨stype, u, hinf_ty, hred_ty, hisZero⟩, hv_run, ?_⟩
      rw [← hcvA_eq]; rfl

/-- Step preservation for `.axiomDecl` in `DeclInvM`. -/
theorem axiomDecl_step_M (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Env .anon} {cv : ConstantVal .anon}
    (hchk : S0.Checked calls env (.axiomDecl cv))
    (hx : DeclValueExtraFacts calls env (.axiomDecl cv)) :
    ∃ env₂, CleanInstallStep env (.axiomDecl cv) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInvM V env → DeclInvM V env₂ := by
  by_cases hskip : cv.name = Ix.Kernel.quotSoundName ∨ IxVM.Consistency.inertKey cv.name = true
  · have hempty : IxVM.Consistency.installs (.axiomDecl cv) = [] := by
      simp only [IxVM.Consistency.installs]
      exact ite_eq_left hskip
    exact ⟨env, CleanInstallStep.empty hempty, fun _ _ h => h⟩
  · have hinst_eq : IxVM.Consistency.installs (.axiomDecl cv) = [.axiomInfo cv] := by
      simp only [IxVM.Consistency.installs]
      exact ite_eq_right hskip
    have hmem : ConstantInfo.axiomInfo cv ∈ IxVM.Consistency.installs (.axiomDecl cv) := by
      rw [hinst_eq]; exact List.mem_singleton.mpr rfl
    have hbase_cv : isBaseKey cv.name = true :=
      s0Checked_installs_isBaseKey hchk (.axiomInfo cv) hmem
    refine declsM_step_of_store hchk hx.installsNodup hx.installsFresh fun hS => ?_
    obtain ⟨E, t, htwf, hloads, hgood, hall⟩ := hchk
    obtain ⟨cl, hcl, hname, rc, v, ap, lim, a, ci, hargs, hrc, hadr, hkey, hci, hstored⟩ :=
      hall (.axiomInfo cv) hmem
    obtain ⟨hR_fn, hsafe, hnil, hres, hcv_bvs, hcv_nfv, hrange,
      ⟨r_cl, h'_cl, subcalls, ev_chk, hsub⟩, hax_shape, -, -, -⟩ :=
      hx.checkedValue E t cl rc v ap lim a ci (.axiomInfo cv) htwf hgood hcl hname hargs
        hrc hadr hkey hci hstored hmem
    obtain ⟨nl, ty, u, rfl, hval⟩ := hax_shape cv rfl
    have hu0 : u = .field 0 := hsafe rfl
    subst hu0
    cases ci with
    | defnInfo _ _ _ | thmInfo _ _ | indInfo _ _ | ctorInfo _ _ _ | recInfo _ _ _ _
    | projInfo _ => cases hstored.2
    | axiomInfo cvA =>
      have ⟨⟨hcv_name, hcv_lps, hann_ty⟩, _⟩ := hstored
      change cvA.name = cv.name at hcv_name
      change cvA.levelParams = cv.levelParams at hcv_lps
      dsimp only [ConstantInfo.toConstantVal] at hval
      let c : Ctx := ⟨E, env, t, lim⟩
      have hgood_c : Good c calls := hgood
      have hef : EnvFacts c := hS.toEnvFacts htwf (hR_fn hS)
      have hlf : LoadFacts c := hloads.withLim
      have hfresh_cv : env.find? cv.name = none := hx.installsFresh (.axiomInfo cv) hmem
      have hnoprj : cv.name.isProjFnShape = false := isProjFnShape_of_isBaseKey hbase_cv
      have hcvA_eq : cvA = ⟨cv.name, cv.levelParams, cvA.type⟩ := by
        cases cvA; cases hcv_name; cases hcv_lps; rfl
      have hval_cv : ValRepExact c.κ cl.heap nl ty ⟨cv.name, cv.levelParams, cvA.type⟩ :=
        hcvA_eq ▸ hval
      obtain ⟨v55, v92, v136, v189, m56, m93, m124, m137, m190,
        cs66, cs103, cs147, cs201,
        ev68, hm132, ev105, ev149, ev203, hne255, hcs66, hcs103, _, hcs201⟩ :=
        check_const_axiom_inv ev_chk
      obtain ⟨hcv_run, _⟩ :=
        constantValRunJ_of_front hCore hfresh_cv hres hnoprj hrange hcv_bvs hcv_nfv rfl hval_cv
          hann_ty hrc hef hlf
          (hgood_c.sub fun x hx => hsub x (hcs66 x hx))
          (hgood_c.sub fun x hx => hsub x (hcs103 x hx))
          ev68 hm132 ev105
      obtain ⟨a', ha', heq_a⟩ := hadr
      have e_to_m137 : Heap.Extends cl.heap m137 :=
        (ObsFn.heap_extends ev68).trans
          ((hm132 ▸ heap_extends_append m56 _).trans
            ((ObsFn.heap_extends ev105).trans (ObsFn.heap_extends ev149)))
      obtain ⟨ro, hro_addr, hin, hro_cases⟩ :=
        axiom_standing_spec hx.rolesSpec (hgood_c.sub fun x hx => hsub x (hcs201 x hx))
          htwf (hrc.mono e_to_m137) (hnil.mono e_to_m137)
          (Bytes.repAddressRef_heapMono₂ addrTy e_to_m137 ha') ev203 hne255
      have hkey_ro : cv.name = .role ro := by
        have hk := keyOf_of_addressOf htwf hro_addr
        rw [heq_a, hkey] at hk
        exact hk
      have hro_std : ro = .propext ∨ ro = .choice := by
        rcases hro_cases with rfl | rfl | rfl | hinert
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd (Or.inl hkey_ro) hskip
        · have : IxVM.Consistency.inertKey cv.name = true := by
            rw [hkey_ro]; exact hinert
          exact absurd (Or.inr this) hskip
      have hstd : Ix.Kernel.stdAxiomOk env ⟨cv.name, cv.levelParams, cvA.type⟩ = true :=
        hx.stdAxiomPinned E t lim ro _ hS htwf hin hro_std hkey_ro
      have hfresh_ci : env.find? (ConstantInfo.axiomInfo cvA).name = none := by
        show env.find? cvA.name = none; rw [hcv_name]; exact hfresh_cv
      refine ⟨⟨.axiomInfo cvA :: env.consts⟩,
        CleanInstallStep.single hinst_eq hstored hfresh_ci hbase_cv, ?_⟩
      show DeclAxiomRunJ rulesJ env cv ⟨.axiomInfo cvA :: env.consts⟩
      refine Or.inr ⟨cvA.type, hcv_run, Or.inl ⟨hstd, ?_⟩⟩
      rw [← hcvA_eq]

/-- Step preservation for `.opaqueDecl` in `DeclInvM`. -/
theorem opaqueDecl_step_M (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Env .anon}
    {cv : ConstantVal .anon} {value : KExpr}
    (hchk : S0.Checked calls env (.opaqueDecl cv value))
    (hx : DeclValueExtraFacts calls env (.opaqueDecl cv value)) :
    ∃ env₂, CleanInstallStep env (.opaqueDecl cv value) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInvM V env → DeclInvM V env₂ := by
  have hinst_eq : IxVM.Consistency.installs (.opaqueDecl cv value) = [.axiomInfo cv] := rfl
  have hmem : ConstantInfo.axiomInfo cv ∈ IxVM.Consistency.installs (.opaqueDecl cv value) :=
    List.mem_singleton.mpr rfl
  have hbase_cv : isBaseKey cv.name = true :=
    s0Checked_installs_isBaseKey hchk (.axiomInfo cv) hmem
  refine declsM_step_of_store hchk hx.installsNodup hx.installsFresh fun hS => ?_
  obtain ⟨E, t, htwf, hloads, hgood, hall⟩ := hchk
  obtain ⟨cl, hcl, hname, rc, v, ap, lim, a, ci, hargs, hrc, hadr, hkey, hci, hstored⟩ :=
    hall (.axiomInfo cv) hmem
  obtain ⟨hR_fn, hsafe, -, hres, hcv_bvs, hcv_nfv, hrange,
    ⟨r_cl, h'_cl, subcalls, ev_chk, hsub⟩, -, -, -, hopaq_shape⟩ :=
    hx.checkedValue E t cl rc v ap lim a ci (.axiomInfo cv) htwf hgood hcl hname hargs
      hrc hadr hkey hci hstored hmem
  obtain ⟨hval_bvs, hval_nfv, nl, ty, val, u, value', rfl, hval, hV, hann_val⟩ :=
    hopaq_shape cv value rfl
  have hu0 : u = .field 0 := hsafe rfl
  subst hu0
  cases ci with
  | defnInfo _ _ _ | thmInfo _ _ | indInfo _ _ | ctorInfo _ _ _ | recInfo _ _ _ _
  | projInfo _ => cases hstored.2
  | axiomInfo cvA =>
    have ⟨⟨hcv_name, hcv_lps, hann_ty⟩, _⟩ := hstored
    change cvA.name = cv.name at hcv_name
    change cvA.levelParams = cv.levelParams at hcv_lps
    change cv.levelParams = List.range cv.levelParams.length at hrange
    dsimp only [ConstantInfo.toConstantVal] at hval hV
    let c : Ctx := ⟨E, env, t, lim⟩
    have hgood_c : Good c calls := hgood
    have hef : EnvFacts c := hS.toEnvFacts htwf (hR_fn hS)
    have hlf : LoadFacts c := hloads.withLim
    have hfresh_cv : env.find? cv.name = none := hx.installsFresh (.axiomInfo cv) hmem
    have hnoprj : cv.name.isProjFnShape = false := isProjFnShape_of_isBaseKey hbase_cv
    have hcvA_eq : cvA = ⟨cv.name, cv.levelParams, cvA.type⟩ := by
      cases cvA; cases hcv_name; cases hcv_lps; rfl
    have hval_cv : ValRepExact c.κ cl.heap nl ty ⟨cv.name, cv.levelParams, cvA.type⟩ :=
      hcvA_eq ▸ hval
    obtain ⟨v848, v885, v922, v966, v996, m849, m886, m923, m954, m967, m997, m1058,
      cs859, cs896, cs933, cs977, cs1007, cs1029,
      ev861, ev898, hm954, ev935, ev979, ev1009, hm1058, ev1031,
      _, hcs896, hcs933, hcs1029⟩ :=
      check_const_opaque_inv ev_chk
    have e_sc1 := ObsFn.heap_extends ev861
    have e_sc2 := ObsFn.heap_extends ev898
    obtain ⟨rfl, hnl, hperm, hty_rep0⟩ := hval_cv
    have hty_pos : posOf cv.levelParams cvA.type = cvA.type := by
      conv => lhs; rw [hrange]; exact posOf_range cv.levelParams.length cvA.type
    have hval_pos : posOf cvA.levelParams value' = value' := by
      rw [hcv_lps]; conv => lhs; rw [hrange]; exact posOf_range cv.levelParams.length value'
    rw [hty_pos] at hty_rep0
    rw [hval_pos] at hV
    let zg : Nat → KExpr := fun _ => .sort .zero
    have hlvl_ty0 : cvA.type.allLevelParamsDefined (List.range cv.levelParams.length) = true :=
      validate_expr_well_scoped_spec hnl (hty_rep0 0 zg) ev861
    have hlvl_ty : cvA.type.allLevelParamsDefined cv.levelParams = true := by
      rw [← hrange] at hlvl_ty0; exact hlvl_ty0
    have e_m954 : Heap.Extends cl.heap m954 :=
      hm954 ▸ (e_sc1.trans e_sc2).trans (heap_extends_append m886 _)
    have htypes954 : TypesRep c.κ zg m954 0 (.ptr (.enum kexprListEnum) m886.length) :=
      hm954 ▸ typesRep_alloc_nil c.κ zg m886
    obtain ⟨stype, u, _, hinf_ty, hred_ty, _, _⟩ :=
      core_ensure_sort hCore (hrc.mono e_m954) htypes954 (ghostScoped_zero zg) hef hlf
        (hgood_c.sub fun x hx => hsub x (hcs933 x hx)) ev935
        ((hty_rep0 0 zg).toTm.mono e_m954)
    have hty'_nfv : cvA.type.hasFvar = false := Tm.hasFvar_false (hty_rep0 0 zg).toTm
    have hcv_run : ConstantValRunJ rulesJ env cv cvA.type :=
      ⟨by rw [hfresh_cv]; rfl, hres, hnoprj, levelParam_nodup_of_perm_range hperm,
        hcv_bvs, hcv_nfv, annot_of_annotates hann_ty hcv_nfv hcv_bvs 0, hlvl_ty,
        infer_constsResolve hinf_ty hS.store hty'_nfv, stype, u, hinf_ty, hred_ty⟩
    have e_pre_chk : Heap.Extends cl.heap m997 :=
      e_m954.trans ((ObsFn.heap_extends ev935).trans
        ((ObsFn.heap_extends ev979).trans (ObsFn.heap_extends ev1009)))
    have hv_run : ValueFrontRunJ rulesJ env cv value cvA.type value' :=
      valueFrontRunJ_of_front hCore hrange hval_bvs hval_nfv rfl hnl hty_rep0 hV hann_val
        e_sc1 e_pre_chk hrc hef hlf
        (hgood_c.sub fun x hx => hsub x (hcs896 x hx))
        (hgood_c.sub fun x hx => hsub x (hcs1029 x hx))
        ev898 hm1058 ev1031
    have hfresh_ci : env.find? (ConstantInfo.axiomInfo cvA).name = none := by
      show env.find? cvA.name = none; rw [hcv_name]; exact hfresh_cv
    refine ⟨⟨.axiomInfo cvA :: env.consts⟩,
      CleanInstallStep.single hinst_eq hstored hfresh_ci hbase_cv, ?_⟩
    show DeclOpaqueRunJ rulesJ env cv value ⟨.axiomInfo cvA :: env.consts⟩
    refine ⟨cvA.type, value', hcv_run, hv_run, ?_⟩
    rw [← hcvA_eq]

/-- Step preservation for `.quotDecl` in `DeclInvM`. -/
theorem quotDecl_step_M {calls : List (Call F)} {env : Env .anon}
    {k : Ix.Kernel.QuotKind} {cv : ConstantVal .anon}
    (hx : DeclValueExtraFacts calls env (.quotDecl k cv)) :
    ∃ env₂, CleanInstallStep env (.quotDecl k cv) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInvM V env → DeclInvM V env₂ := by
  cases k with
  | type =>
    obtain ⟨hrun, hinst⟩ := basis_step_of_fresh (d := .quotDecl .type cv) .quotK rfl
      (fun _ => hx.quotEqStored (Or.inl ⟨cv, rfl⟩)) hx.installsFresh
    have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.quotDecl .type cv)
        ⟨BasisKind.quotK.declsA.reverse ++ env.consts⟩ := hrun
    have hclean := CleanInstallStep.of_baseList hinst fun ci hci =>
      List.all_eq_true.mp (basis_declsA_isBaseKey .quotK) ci (List.mem_reverse.mp hci)
    exact ⟨⟨BasisKind.quotK.declsA.reverse ++ env.consts⟩, hclean,
      fun _ _ hInvM => ⟨hInvM.inv.step_declRunJ hdecl, hclean.auxSynced hInvM.auxSynced⟩⟩
  | ctor => exact ⟨env, CleanInstallStep.empty rfl, fun _ _ h => h⟩
  | lift => exact ⟨env, CleanInstallStep.empty rfl, fun _ _ h => h⟩
  | ind => exact ⟨env, CleanInstallStep.empty rfl, fun _ _ h => h⟩
  | sound => exact ⟨env, CleanInstallStep.empty rfl, fun _ _ h => h⟩

/-- Step preservation for `.basisDecl` in `DeclInvM`. -/
theorem basisDecl_step_M {calls : List (Call F)} {env : Env .anon} {kind : BasisKind}
    (hx : DeclValueExtraFacts calls env (.basisDecl kind)) :
    ∃ env₂, CleanInstallStep env (.basisDecl kind) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInvM V env → DeclInvM V env₂ := by
  obtain ⟨hrun, hinst⟩ := basis_step_of_fresh (d := .basisDecl kind) kind rfl
    (fun hk => hx.quotEqStored (Or.inr (Or.inl (hk ▸ rfl)))) hx.installsFresh
  have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.basisDecl kind)
      ⟨kind.declsA.reverse ++ env.consts⟩ := hrun
  have hclean := CleanInstallStep.of_baseList hinst fun ci hci =>
    List.all_eq_true.mp (basis_declsA_isBaseKey kind) ci (List.mem_reverse.mp hci)
  exact ⟨⟨kind.declsA.reverse ++ env.consts⟩, hclean,
    fun _ _ hInvM => ⟨hInvM.inv.step_declRunJ hdecl, hclean.auxSynced hInvM.auxSynced⟩⟩

/-- Step preservation for pinned `.indDecl` in `DeclInvM`. -/
theorem pinnedIndDecl_step_M {calls : List (Call F)} {env : Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat} {kind : BasisKind}
    (hpin : Ix.Kernel.basisPinHit block = some kind)
    (hx : DeclValueExtraFacts calls env (.indDecl block nP)) :
    ∃ env₂, CleanInstallStep env (.indDecl block nP) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInvM V env → DeclInvM V env₂ := by
  have hinst_eq : IxVM.Consistency.installs (.indDecl block nP) = kind.declsA := by
    simp [IxVM.Consistency.installs, hpin]
  obtain ⟨hrun, hinst⟩ := basis_step_of_fresh (d := .indDecl block nP) kind hinst_eq
    (fun hk => hx.quotEqStored (Or.inr (Or.inr ⟨block, nP, rfl, hk ▸ hpin⟩)))
    (hinst_eq ▸ hx.installsFresh)
  have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.indDecl block nP)
      ⟨kind.declsA.reverse ++ env.consts⟩ := by
    simp only [DeclRunJ, hpin]; exact hrun
  have hclean := CleanInstallStep.of_baseList hinst fun ci hci =>
    List.all_eq_true.mp (basis_declsA_isBaseKey kind) ci (List.mem_reverse.mp hci)
  exact ⟨⟨kind.declsA.reverse ++ env.consts⟩, hclean,
    fun _ _ hInvM => ⟨hInvM.inv.step_declRunJ hdecl, hclean.auxSynced hInvM.auxSynced⟩⟩

/-- Unified `DeclInvM` step preservation across all non-inductive and pinned declarations. -/
theorem valueOrPinnedDecl_step_M (hLevels : IxVM.Consistency.Levels)
    (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Env .anon} {d : Declaration .anon}
    (hchk : S0.Checked calls env d)
    (hx : DeclValueExtraFacts calls env d)
    (hind : ∀ block nP, d = .indDecl block nP → Ix.Kernel.basisPinHit block = none →
      ∃ env₂, CleanInstallStep env (.indDecl block nP) env₂ ∧
        ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInvM V env → DeclInvM V env₂) :
    ∃ env₂, CleanInstallStep env d env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInvM V env → DeclInvM V env₂ := by
  cases d with
  | axiomDecl cv => exact axiomDecl_step_M hCore hchk hx
  | defnDecl cv value hint => exact defnDecl_step_M hCore hchk hx
  | thmDecl cv value => exact thmDecl_step_M hLevels hCore hchk hx
  | opaqueDecl cv value => exact opaqueDecl_step_M hCore hchk hx
  | quotDecl k cv => exact quotDecl_step_M hx
  | basisDecl kind => exact basisDecl_step_M hx
  | indDecl block nP =>
    cases hpin : Ix.Kernel.basisPinHit block with
    | some kind => exact pinnedIndDecl_step_M hpin hx
    | none => exact hind block nP rfl hpin

/-! ## Level-Parameter Permutation Algebra (`posVal`, `perm_range_eq_of_le_one`) -/

theorem perm_range_eq_of_le_one {ps : List LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (hle : ps.length ≤ 1) :
    ps = List.range ps.length := by
  cases ps with
  | nil => rfl
  | cons p rest =>
    cases rest with
    | nil =>
      have hm : p ∈ List.range 1 := hperm.mem_iff.mp List.mem_cons_self
      have hp0 : p = 0 := by simpa using hm
      subst hp0
      rfl
    | cons _ _ => simp at hle

theorem posVal_range_id (n : Nat) (φ : LevelParam → Nat) :
    posVal (List.range n) φ = φ := by
  unfold posVal
  rw [List.length_range]
  exact Level.substFn_param_self φ (List.range n)

private theorem subst_go_getElem_local :
    ∀ (ks : List LevelParam) (vs : List KLevel) (i : Nat) (hnd : ks.Nodup)
      (hlen : vs.length = ks.length) (hi : i < ks.length),
      Level.subst.go ks vs ks[i] = vs[i]'(hlen ▸ hi)
  | [], _, _, _, _, hi => nomatch hi
  | _ :: _, [], _, _, hlen, _ => nomatch hlen
  | k :: ks, v :: _, 0, _, _, _ => by
    show (if k = k then v else Level.subst.go ks _ k) = v
    exact ite_eq_left rfl
  | k :: ks, v :: vs, i + 1, hnd, hlen, hi => by
    obtain ⟨hk_nm, hnd'⟩ := List.nodup_cons.mp hnd
    have hi' : i < ks.length := Nat.lt_of_succ_lt_succ hi
    have hlen' : vs.length = ks.length := Nat.succ.inj hlen
    have hne : k ≠ ks[i] := fun heq => hk_nm (heq ▸ List.getElem_mem hi')
    show (if k = ks[i] then v else Level.subst.go ks vs ks[i]) = vs[i]'(hlen' ▸ hi')
    rw [ite_eq_right hne]
    exact subst_go_getElem_local ks vs i hnd' hlen' hi'

theorem posVal_apply_lt {ps : List LevelParam} {φ : LevelParam → Nat} {i : Nat}
    (hi : i < ps.length) :
    posVal ps φ i = φ ps[i] := by
  unfold posVal
  rw [← Level.eval_subst_go]
  have hi_len : i < (ps.map Level.param).length := by rw [List.length_map]; exact hi
  have hget := InferAux.getElem?_eq_subst_go_range (us := ps.map Level.param) hi_len
  rw [List.length_map, List.getElem?_map, List.getElem?_eq_getElem hi] at hget
  rw [← Option.some.inj hget]
  rfl

theorem posVal_congr_mem {ps : List LevelParam} {ψ₁ ψ₂ : LevelParam → Nat}
    (h : ∀ q ∈ ps, ψ₁ q = ψ₂ q) :
    ∀ i ∈ List.range ps.length, posVal ps ψ₁ i = posVal ps ψ₂ i := by
  intro i hi
  have hlt : i < ps.length := List.mem_range.mp hi
  rw [posVal_apply_lt hlt, posVal_apply_lt hlt]
  exact h ps[i] (List.getElem_mem hlt)

theorem posVal_substFn_eq {ps : List LevelParam} {us : List KLevel}
    (hperm : ps.Perm (List.range ps.length)) (hus : us.length = ps.length)
    (φ : LevelParam → Nat) :
    posVal ps (Level.substFn φ ps us) = Level.substFn φ (List.range ps.length) us := by
  have hnd : ps.Nodup := hperm.nodup_iff.mpr List.nodup_range
  funext i
  by_cases hi : i < ps.length
  · rw [posVal_apply_lt hi, ← Level.eval_subst_go, subst_go_getElem_local ps us i hnd hus hi]
    have hi_us : i < us.length := hus ▸ hi
    have hget := InferAux.getElem?_eq_subst_go_range (us := us) hi_us
    rw [hus, List.getElem?_eq_getElem hi_us] at hget
    rw [Option.some.inj hget, Level.eval_subst_go]
  · have hi_range : i ∉ List.range ps.length := by rw [List.mem_range]; exact hi
    have hi_ps : i ∉ ps := fun hm => hi_range (hperm.mem_iff.mp hm)
    unfold posVal
    rw [← Level.eval_subst_go, ← Level.eval_subst_go,
      InferAux.subst_go_of_not_mem hi_range, InferAux.subst_go_of_not_mem hi_range]
    show Level.substFn φ ps us i = Level.eval φ (.param i)
    rw [← Level.eval_subst_go, InferAux.subst_go_of_not_mem hi_ps]

theorem subst_posLevels_comp {ps : List LevelParam} {us : List KLevel}
    (hperm : ps.Perm (List.range ps.length)) (hus : us.length = ps.length)
    (u : KLevel) :
    Level.subst (List.range ps.length) us (Level.subst ps (posLevels ps) u) =
      Level.subst ps us u := by
  have heq := InferAux.posOf_instantiateLevelParams_perm hperm hus (T := .sort u)
  rw [hus] at heq
  exact Expr.sort.inj heq

theorem constsResolve_openRev {env : Env .anon} (d : Nat) :
    ∀ (n : Nat) {e : KExpr}, e.constsResolve env = true →
      (openRev d n e).constsResolve env = true
  | 0, _, h => h
  | n + 1, _, h => by
    simp only [openRev]
    exact Expr.constsResolve_instantiate1 (d := d + n) (ty := .sort .zero) rfl 0
      (constsResolve_openRev d n h)

/-! ## Unpositionalization (`UnposEntry`, `UnposAgree`, `denoteMeta_unpos_eq`) -/

/-- Positional counterpart of a `ConstantVal`. -/
def posCV (cv : ConstantVal .anon) : ConstantVal .anon :=
  ⟨cv.name, List.range cv.levelParams.length, posOf cv.levelParams cv.type⟩

/-- Positional counterpart of a non-recursor or provisional-recursor `ConstantInfo`. -/
def posCI : ConstantInfo .anon → ConstantInfo .anon
  | .indInfo cv caps => .indInfo (posCV cv) caps
  | .ctorInfo cv nP nF => .ctorInfo (posCV cv) nP nF
  | .recInfo cv mI rP [] => .recInfo (posCV cv) mI rP []
  | ci => ci

/-- Constructor-tag and payload agreement between a real constant `ci_r` and its positional
counterpart `ci_p`. -/
def UnposTagMatch (ci_r ci_p : ConstantInfo .anon) : Prop :=
  match ci_r, ci_p with
  | .indInfo _ caps_r, .indInfo _ caps_p => caps_p = caps_r
  | .ctorInfo _ a_r b_r, .ctorInfo _ a_p b_p => a_p = a_r ∧ b_p = b_r
  | .indInfo _ _, _ | _, .indInfo _ _ | .ctorInfo _ _ _, _ | _, .ctorInfo _ _ _ => False
  | _, _ => True

/-- Relationship between a constant stored in a real prefix `E_r` and its entry in the
positionalized prefix `E_p`: either pre-existing (identical constant and leaf) or a new block
constant whose `E_p` entry is positionalized via `posCV` and `posVal`. -/
def UnposEntry (ac_r : KKey → (LevelParam → Nat) → AnnotTerm) (ci_r : ConstantInfo .anon)
    (ac_p : KKey → (LevelParam → Nat) → AnnotTerm) (ci_p : ConstantInfo .anon)
    (k : KKey) : Prop :=
  (ci_p = ci_r ∧ ac_p k = ac_r k) ∨
  (let lps := ci_r.toConstantVal.levelParams
   lps.Perm (List.range lps.length) ∧
   ci_p.toConstantVal = posCV ci_r.toConstantVal ∧
   (∀ ψ, ac_r k ψ = ac_p k (posVal lps ψ)) ∧
   UnposTagMatch ci_r ci_p)

theorem UnposEntry.le_one_eq {ac_r ac_p : KKey → (LevelParam → Nat) → AnnotTerm}
    {ci_r ci_p : ConstantInfo .anon} {k : KKey}
    (h : UnposEntry ac_r ci_r ac_p ci_p k)
    (hle : ci_r.toConstantVal.levelParams.length ≤ 1 ∨ ci_p.toConstantVal.levelParams.length ≤ 1) :
    ci_p.toConstantVal = ci_r.toConstantVal ∧ ac_p k = ac_r k ∧
    (∀ cv_r caps_r, ci_r = .indInfo cv_r caps_r → ci_p = .indInfo cv_r caps_r) ∧
    (∀ cv_p caps_p, ci_p = .indInfo cv_p caps_p → ci_r = .indInfo cv_p caps_p) ∧
    (∀ cv_r a b, ci_r = .ctorInfo cv_r a b → ci_p = .ctorInfo cv_r a b) ∧
    (∀ cv_p a b, ci_p = .ctorInfo cv_p a b → ci_r = .ctorInfo cv_p a b) := by
  rcases h with ⟨rfl, hac⟩ | ⟨hperm, hcv, hac, htag⟩
  · exact ⟨rfl, hac, fun _ _ h => h, fun _ _ h => h, fun _ _ _ h => h, fun _ _ _ h => h⟩
  · have hlen_eq : ci_p.toConstantVal.levelParams.length = ci_r.toConstantVal.levelParams.length := by
      rw [hcv]; simp [posCV]
    have hle_r : ci_r.toConstantVal.levelParams.length ≤ 1 := by
      rcases hle with h1 | h2
      · exact h1
      · omega
    have hrange := perm_range_eq_of_le_one hperm hle_r
    have hty_pos : posOf ci_r.toConstantVal.levelParams ci_r.toConstantVal.type =
        ci_r.toConstantVal.type := by
      conv => lhs; rw [hrange]
      exact posOf_range _ _
    have hcv_eq : ci_p.toConstantVal = ci_r.toConstantVal := by
      rw [hcv]
      unfold posCV
      rw [hty_pos, ← hrange]
    have hac_eq : ac_p k = ac_r k := by
      funext ψ
      rw [hac ψ]
      have hpv : posVal ci_r.toConstantVal.levelParams ψ = ψ := by
        conv => lhs; rw [hrange]
        exact posVal_range_id _ ψ
      rw [hpv]
    refine ⟨hcv_eq, hac_eq, ?_, ?_, ?_, ?_⟩
    · intro cv_r caps_r hr
      subst hr
      cases ci_p with
      | indInfo cv_p caps_p =>
        dsimp only [ConstantInfo.toConstantVal, UnposTagMatch] at hcv_eq htag
        rw [hcv_eq, htag]
      | _ => exact nomatch htag
    · intro cv_p caps_p hp
      subst hp
      cases ci_r with
      | indInfo cv_r caps_r =>
        dsimp only [ConstantInfo.toConstantVal, UnposTagMatch] at hcv_eq htag
        rw [← hcv_eq, ← htag]
      | _ => exact nomatch htag
    · intro cv_r a b hr
      subst hr
      cases ci_p with
      | ctorInfo cv_p a_p b_p =>
        dsimp only [ConstantInfo.toConstantVal, UnposTagMatch] at hcv_eq htag
        rw [hcv_eq, htag.1, htag.2]
      | _ => exact nomatch htag
    · intro cv_p a b hp
      subst hp
      cases ci_r with
      | ctorInfo cv_r a_r b_r =>
        dsimp only [ConstantInfo.toConstantVal, UnposTagMatch] at hcv_eq htag
        rw [← hcv_eq, ← htag.1, ← htag.2]
      | _ => exact nomatch htag

/-- Agreement invariant between `(ac_r, E_r)` and `(ac_p, E_p)`. -/
structure UnposAgree (ac_r : KKey → (LevelParam → Nat) → AnnotTerm) (E_r : Env .anon)
    (ac_p : KKey → (LevelParam → Nat) → AnnotTerm) (E_p : Env .anon) : Prop where
  entry : ∀ k ci_r, E_r.find? k = some ci_r →
    ∃ ci_p, E_p.find? k = some ci_p ∧ UnposEntry ac_r ci_r ac_p ci_p k
  projEq : ∀ sn, (E_r.find? sn).isSome = true → ∀ i, E_p.findProj? sn i = E_r.findProj? sn i

theorem UnposAgree.of_base
    {ac_r : KKey → (LevelParam → Nat) → AnnotTerm} {E_r : Env .anon}
    {ac_p : KKey → (LevelParam → Nat) → AnnotTerm} {E_p : Env .anon}
    (hfind : ∀ k ci, E_r.find? k = some ci → E_p.find? k = some ci)
    (hac : ∀ k, (E_r.find? k).isSome = true → ac_p k = ac_r k)
    (hnnp : NoNewProjForOld E_r E_p) :
    UnposAgree ac_r E_r ac_p E_p where
  entry k ci_r hf :=
    ⟨ci_r, hfind k ci_r hf, Or.inl ⟨rfl, hac k (by rw [hf]; rfl)⟩⟩
  projEq sn hsn i := hnnp.findProj?_eq hsn i

theorem UnposAgree.cons_pair
    {ac_r : KKey → (LevelParam → Nat) → AnnotTerm} {E_r : Env .anon}
    {ac_p : KKey → (LevelParam → Nat) → AnnotTerm} {E_p : Env .anon}
    (h : UnposAgree ac_r E_r ac_p E_p)
    {c_r c_p : ConstantInfo .anon} {A_r A_p : (LevelParam → Nat) → AnnotTerm}
    (hname : c_p.name = c_r.name)
    (hfresh_r : E_r.find? c_r.name = none)
    (hfresh_p : E_p.find? c_p.name = none)
    (hnpt_r : ∀ T, c_r.name ≠ projTableName T)
    (hperm : c_r.toConstantVal.levelParams.Perm (List.range c_r.toConstantVal.levelParams.length))
    (hcv : c_p.toConstantVal = posCV c_r.toConstantVal)
    (hA : ∀ ψ, A_r ψ = A_p (posVal c_r.toConstantVal.levelParams ψ))
    (htag : UnposTagMatch c_r c_p)
    (hproj_self : E_p.find? (projTableName c_r.name) = E_r.find? (projTableName c_r.name)) :
    UnposAgree (acvalWith ac_r c_r.name A_r) ⟨c_r :: E_r.consts⟩
      (acvalWith ac_p c_p.name A_p) ⟨c_p :: E_p.consts⟩ where
  entry k ci_r hf := by
    rw [Env.find?_cons] at hf
    by_cases heq : c_r.name = k
    · rw [ite_eq_left heq] at hf
      obtain rfl := Option.some.inj hf
      subst heq
      have hf_p : (⟨c_p :: E_p.consts⟩ : Env .anon).find? c_r.name = some c_p := by
        rw [Env.find?_cons, ite_eq_left hname]
      refine ⟨c_p, hf_p, Or.inr ⟨hperm, hcv, ?_, htag⟩⟩
      intro ψ
      rw [hname, acvalWith_self, acvalWith_self]
      exact hA ψ
    · rw [ite_eq_right heq] at hf
      obtain ⟨ci_p, hf_p, hent⟩ := h.entry k ci_r hf
      have heq_p : c_p.name ≠ k := fun hh => heq (hname.symm.trans hh)
      have hf_p' : (⟨c_p :: E_p.consts⟩ : Env .anon).find? k = some ci_p := by
        rw [Env.find?_cons, ite_eq_right heq_p]; exact hf_p
      have hne_r : k ≠ c_r.name := Ne.symm heq
      have hne_p : k ≠ c_p.name := Ne.symm heq_p
      refine ⟨ci_p, hf_p', ?_⟩
      rcases hent with ⟨rfl, hac⟩ | ⟨hp, hc, hac, ht⟩
      · left
        refine ⟨rfl, ?_⟩
        funext ψ
        rw [acvalWith_ne hne_p, acvalWith_ne hne_r, hac]
      · right
        refine ⟨hp, hc, ?_, ht⟩
        intro ψ
        rw [acvalWith_ne hne_r, acvalWith_ne hne_p]
        exact hac ψ
  projEq sn hsn i := by
    have hnpt_p : ∀ T, c_p.name ≠ projTableName T := fun T => hname ▸ hnpt_r T
    unfold Env.findProj?
    rw [EnvExt.find?_cons_ne (hnpt_p sn), EnvExt.find?_cons_ne (hnpt_r sn)]
    rw [Env.find?_cons] at hsn
    by_cases heq : c_r.name = sn
    · subst heq
      rw [hproj_self]
    · rw [ite_eq_right heq] at hsn
      exact h.projEq sn hsn i

private theorem natIndOk_false_of_gt_one {ci : ConstantInfo .anon}
    (h : 1 < ci.toConstantVal.levelParams.length) :
    Ix.Kernel.natIndOk (some ci) = false := by
  cases ci with
  | indInfo cv _ =>
    have he : cv.levelParams.isEmpty = false := by
      cases hl : cv.levelParams with
      | nil => simp [ConstantInfo.toConstantVal, hl] at h
      | cons _ _ => rfl
    simp [Ix.Kernel.natIndOk, he]
  | _ => rfl

private theorem natZeroOk_false_of_gt_one {ci : ConstantInfo .anon}
    (h : 1 < ci.toConstantVal.levelParams.length) :
    Ix.Kernel.natZeroOk (some ci) = false := by
  cases ci with
  | ctorInfo cv _ _ =>
    have he : cv.levelParams.isEmpty = false := by
      cases hl : cv.levelParams with
      | nil => simp [ConstantInfo.toConstantVal, hl] at h
      | cons _ _ => rfl
    simp [Ix.Kernel.natZeroOk, he]
  | _ => rfl

private theorem natSuccOk_false_of_gt_one {ci : ConstantInfo .anon}
    (h : 1 < ci.toConstantVal.levelParams.length) :
    Ix.Kernel.natSuccOk (some ci) = false := by
  cases ci with
  | ctorInfo cv _ _ =>
    have he : cv.levelParams.isEmpty = false := by
      cases hl : cv.levelParams with
      | nil => simp [ConstantInfo.toConstantVal, hl] at h
      | cons _ _ => rfl
    simp [Ix.Kernel.natSuccOk, he]
  | _ => rfl

private theorem natIndOk_unpos {ac_r ac_p : KKey → (LevelParam → Nat) → AnnotTerm}
    {ci_r ci_p : ConstantInfo .anon} {k : KKey}
    (h : UnposEntry ac_r ci_r ac_p ci_p k) :
    Ix.Kernel.natIndOk (some ci_r) = Ix.Kernel.natIndOk (some ci_p) := by
  by_cases hle : ci_r.toConstantVal.levelParams.length ≤ 1 ∨ ci_p.toConstantVal.levelParams.length ≤ 1
  · obtain ⟨_, _, hi1, hi2, _, _⟩ := h.le_one_eq hle
    cases ci_r with
    | indInfo cv caps => rw [hi1 cv caps rfl]
    | _ =>
      cases hp : ci_p with
      | indInfo cv_p caps_p => exact absurd (hi2 cv_p caps_p hp) nofun
      | _ => rfl
  · rw [natIndOk_false_of_gt_one (by omega), natIndOk_false_of_gt_one (by omega)]

private theorem natZeroOk_unpos {ac_r ac_p : KKey → (LevelParam → Nat) → AnnotTerm}
    {ci_r ci_p : ConstantInfo .anon} {k : KKey}
    (h : UnposEntry ac_r ci_r ac_p ci_p k) :
    Ix.Kernel.natZeroOk (some ci_r) = Ix.Kernel.natZeroOk (some ci_p) := by
  by_cases hle : ci_r.toConstantVal.levelParams.length ≤ 1 ∨ ci_p.toConstantVal.levelParams.length ≤ 1
  · obtain ⟨_, _, _, _, hc1, hc2⟩ := h.le_one_eq hle
    cases ci_r with
    | ctorInfo cv a b => rw [hc1 cv a b rfl]
    | _ =>
      cases hp : ci_p with
      | ctorInfo cv_p a b => exact absurd (hc2 cv_p a b hp) nofun
      | _ => rfl
  · rw [natZeroOk_false_of_gt_one (by omega), natZeroOk_false_of_gt_one (by omega)]

private theorem natSuccOk_unpos {ac_r ac_p : KKey → (LevelParam → Nat) → AnnotTerm}
    {ci_r ci_p : ConstantInfo .anon} {k : KKey}
    (h : UnposEntry ac_r ci_r ac_p ci_p k) :
    Ix.Kernel.natSuccOk (some ci_r) = Ix.Kernel.natSuccOk (some ci_p) := by
  by_cases hle : ci_r.toConstantVal.levelParams.length ≤ 1 ∨ ci_p.toConstantVal.levelParams.length ≤ 1
  · obtain ⟨_, _, _, _, hc1, hc2⟩ := h.le_one_eq hle
    cases ci_r with
    | ctorInfo cv a b => rw [hc1 cv a b rfl]
    | _ =>
      cases hp : ci_p with
      | ctorInfo cv_p a b => exact absurd (hc2 cv_p a b hp) nofun
      | _ => rfl
  · rw [natSuccOk_false_of_gt_one (by omega), natSuccOk_false_of_gt_one (by omega)]

private theorem cvPred_le_one_unpos (P : ConstantVal .anon → Bool)
    (hfalse : ∀ cv : ConstantVal .anon, 1 < cv.levelParams.length → P cv = false)
    {ac_r ac_p : KKey → (LevelParam → Nat) → AnnotTerm}
    {ci_r ci_p : ConstantInfo .anon} {k : KKey}
    (h : UnposEntry ac_r ci_r ac_p ci_p k) :
    P ci_r.toConstantVal = P ci_p.toConstantVal := by
  by_cases hle : ci_r.toConstantVal.levelParams.length ≤ 1 ∨ ci_p.toConstantVal.levelParams.length ≤ 1
  · rw [(h.le_one_eq hle).1]
  · rw [hfalse _ (by omega), hfalse _ (by omega)]

private theorem ac_eq_of_isEmpty_lps {ac_r ac_p : KKey → (LevelParam → Nat) → AnnotTerm}
    {ci_r ci_p : ConstantInfo .anon} {k : KKey}
    (h : UnposEntry ac_r ci_r ac_p ci_p k)
    (hle : ci_r.toConstantVal.levelParams.length ≤ 1) :
    ac_p k = ac_r k :=
  (h.le_one_eq (Or.inl hle)).2.1

private theorem natLitSupported_unpos {ac_r ac_p : KKey → (LevelParam → Nat) → AnnotTerm}
    {E_r E_p : Env .anon} (h : UnposAgree ac_r E_r ac_p E_p)
    (hn1 : (E_r.find? Ix.Kernel.natName).isSome = true)
    (hn2 : (E_r.find? Ix.Kernel.natZeroName).isSome = true)
    (hn3 : (E_r.find? Ix.Kernel.natSuccName).isSome = true) :
    Ix.Kernel.natLitSupported E_r = Ix.Kernel.natLitSupported E_p ∧
    (Ix.Kernel.natLitSupported E_r = true →
      ac_r Ix.Kernel.natZeroName = ac_p Ix.Kernel.natZeroName ∧
      ac_r Ix.Kernel.natSuccName = ac_p Ix.Kernel.natSuccName) := by
  obtain ⟨c1_r, hf1_r⟩ := Option.isSome_iff_exists.mp hn1
  obtain ⟨c2_r, hf2_r⟩ := Option.isSome_iff_exists.mp hn2
  obtain ⟨c3_r, hf3_r⟩ := Option.isSome_iff_exists.mp hn3
  obtain ⟨c1_p, hf1_p, he1⟩ := h.entry _ _ hf1_r
  obtain ⟨c2_p, hf2_p, he2⟩ := h.entry _ _ hf2_r
  obtain ⟨c3_p, hf3_p, he3⟩ := h.entry _ _ hf3_r
  have hsup : Ix.Kernel.natLitSupported E_r = Ix.Kernel.natLitSupported E_p := by
    unfold Ix.Kernel.natLitSupported
    rw [hf1_r, hf2_r, hf3_r, hf1_p, hf2_p, hf3_p,
      natIndOk_unpos he1, natZeroOk_unpos he2, natSuccOk_unpos he3]
  refine ⟨hsup, fun hok => ?_⟩
  unfold Ix.Kernel.natLitSupported at hok
  rw [hf1_r, hf2_r, hf3_r] at hok
  simp only [Bool.and_eq_true] at hok
  have hle2 : c2_r.toConstantVal.levelParams.length ≤ 1 := by
    cases c2_r with
    | ctorInfo cv _ _ =>
      simp only [Ix.Kernel.natZeroOk, Bool.and_eq_true, List.isEmpty_iff] at hok
      simp [ConstantInfo.toConstantVal, hok.1.2.1]
    | _ => exact nomatch hok.1.2
  have hle3 : c3_r.toConstantVal.levelParams.length ≤ 1 := by
    cases c3_r with
    | ctorInfo cv _ _ =>
      simp only [Ix.Kernel.natSuccOk, Bool.and_eq_true, List.isEmpty_iff] at hok
      simp [ConstantInfo.toConstantVal, hok.2.1]
    | _ => exact nomatch hok.2
  exact ⟨(ac_eq_of_isEmpty_lps he2 hle2).symm, (ac_eq_of_isEmpty_lps he3 hle3).symm⟩

private theorem strLitSupported_unpos {ac_r ac_p : KKey → (LevelParam → Nat) → AnnotTerm}
    {E_r E_p : Env .anon} (h : UnposAgree ac_r E_r ac_p E_p) {s : String}
    (hcr : (Expr.lit (.strVal s)).constsResolve E_r = true) :
    Ix.Kernel.strLitSupported E_r = Ix.Kernel.strLitSupported E_p ∧
    (Ix.Kernel.strLitSupported E_r = true →
      ac_r Ix.Kernel.stringOfListName = ac_p Ix.Kernel.stringOfListName ∧
      ac_r Ix.Kernel.listNilName = ac_p Ix.Kernel.listNilName ∧
      ac_r Ix.Kernel.listConsName = ac_p Ix.Kernel.listConsName ∧
      ac_r Ix.Kernel.charName = ac_p Ix.Kernel.charName ∧
      ac_r Ix.Kernel.charOfNatName = ac_p Ix.Kernel.charOfNatName ∧
      ac_r Ix.Kernel.natZeroName = ac_p Ix.Kernel.natZeroName ∧
      ac_r Ix.Kernel.natSuccName = ac_p Ix.Kernel.natSuccName ∧
      levelParamsAt E_r Ix.Kernel.listNilName =
        levelParamsAt E_p Ix.Kernel.listNilName ∧
      levelParamsAt E_r Ix.Kernel.listConsName =
        levelParamsAt E_p Ix.Kernel.listConsName) := by
  simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hn1, hn2⟩, hn3⟩, hs1⟩, hs2⟩, hl1⟩, hl2⟩, hl3⟩, hc1⟩, hc2⟩ := hcr
  obtain ⟨hnat_eq, hnat_ac⟩ := natLitSupported_unpos h hn1 hn2 hn3
  obtain ⟨cs1_r, hfs1_r⟩ := Option.isSome_iff_exists.mp hs1
  obtain ⟨cs2_r, hfs2_r⟩ := Option.isSome_iff_exists.mp hs2
  obtain ⟨cl1_r, hfl1_r⟩ := Option.isSome_iff_exists.mp hl1
  obtain ⟨cl2_r, hfl2_r⟩ := Option.isSome_iff_exists.mp hl2
  obtain ⟨cl3_r, hfl3_r⟩ := Option.isSome_iff_exists.mp hl3
  obtain ⟨cc1_r, hfc1_r⟩ := Option.isSome_iff_exists.mp hc1
  obtain ⟨cc2_r, hfc2_r⟩ := Option.isSome_iff_exists.mp hc2
  obtain ⟨cs1_p, hfs1_p, hes1⟩ := h.entry _ _ hfs1_r
  obtain ⟨cs2_p, hfs2_p, hes2⟩ := h.entry _ _ hfs2_r
  obtain ⟨cl1_p, hfl1_p, hel1⟩ := h.entry _ _ hfl1_r
  obtain ⟨cl2_p, hfl2_p, hel2⟩ := h.entry _ _ hfl2_r
  obtain ⟨cl3_p, hfl3_p, hel3⟩ := h.entry _ _ hfl3_r
  obtain ⟨cc1_p, hfc1_p, hec1⟩ := h.entry _ _ hfc1_r
  obtain ⟨cc2_p, hfc2_p, hec2⟩ := h.entry _ _ hfc2_r
  have hp_s1 : Ix.Kernel.stringTyOk (some cs1_r) = Ix.Kernel.stringTyOk (some cs1_p) :=
    cvPred_le_one_unpos (fun cv => cv.levelParams.isEmpty && cv.type == .sort (.succ .zero))
      (fun cv hgt => by cases hl : cv.levelParams <;> simp_all) hes1
  have hp_s2 : Ix.Kernel.stringOfListTyOk (some cs2_r) = Ix.Kernel.stringOfListTyOk (some cs2_p) :=
    cvPred_le_one_unpos (fun cv => Ix.Kernel.stringOfListTyOk (some (.axiomInfo cv)))
      (fun cv hgt => by
        have he : cv.levelParams.isEmpty = false := by cases hl : cv.levelParams <;> simp_all
        simp [Ix.Kernel.stringOfListTyOk, ConstantInfo.toConstantVal, he]) hes2
  have hp_l1 : Ix.Kernel.listTyOk (some cl1_r) = Ix.Kernel.listTyOk (some cl1_p) :=
    cvPred_le_one_unpos (fun cv => Ix.Kernel.listTyOk (some (.axiomInfo cv)))
      (fun cv hgt => by
        cases hl : cv.levelParams with
        | nil => simp [hl] at hgt
        | cons _ tl =>
          cases tl with
          | nil => simp [hl] at hgt
          | cons _ _ => simp [Ix.Kernel.listTyOk, ConstantInfo.toConstantVal, hl]) hel1
  have hp_l2 : Ix.Kernel.listNilTyOk (some cl2_r) = Ix.Kernel.listNilTyOk (some cl2_p) :=
    cvPred_le_one_unpos (fun cv => Ix.Kernel.listNilTyOk (some (.axiomInfo cv)))
      (fun cv hgt => by
        cases hl : cv.levelParams with
        | nil => simp [hl] at hgt
        | cons _ tl =>
          cases tl with
          | nil => simp [hl] at hgt
          | cons _ _ => simp [Ix.Kernel.listNilTyOk, ConstantInfo.toConstantVal, hl]) hel2
  have hp_l3 : Ix.Kernel.listConsTyOk (some cl3_r) = Ix.Kernel.listConsTyOk (some cl3_p) :=
    cvPred_le_one_unpos (fun cv => Ix.Kernel.listConsTyOk (some (.axiomInfo cv)))
      (fun cv hgt => by
        cases hl : cv.levelParams with
        | nil => simp [hl] at hgt
        | cons _ tl =>
          cases tl with
          | nil => simp [hl] at hgt
          | cons _ _ => simp [Ix.Kernel.listConsTyOk, ConstantInfo.toConstantVal, hl]) hel3
  have hp_c1 : Ix.Kernel.charTyOk (some cc1_r) = Ix.Kernel.charTyOk (some cc1_p) :=
    cvPred_le_one_unpos (fun cv => cv.levelParams.isEmpty && cv.type == .sort (.succ .zero))
      (fun cv hgt => by cases hl : cv.levelParams <;> simp_all) hec1
  have hp_c2 : Ix.Kernel.charOfNatTyOk (some cc2_r) = Ix.Kernel.charOfNatTyOk (some cc2_p) :=
    cvPred_le_one_unpos (fun cv => Ix.Kernel.charOfNatTyOk (some (.axiomInfo cv)))
      (fun cv hgt => by
        have he : cv.levelParams.isEmpty = false := by cases hl : cv.levelParams <;> simp_all
        simp [Ix.Kernel.charOfNatTyOk, ConstantInfo.toConstantVal, he]) hec2
  have hsup : Ix.Kernel.strLitSupported E_r = Ix.Kernel.strLitSupported E_p := by
    unfold Ix.Kernel.strLitSupported
    rw [hnat_eq, hfs1_r, hfs2_r, hfl1_r, hfl2_r, hfl3_r, hfc1_r, hfc2_r,
      hfs1_p, hfs2_p, hfl1_p, hfl2_p, hfl3_p, hfc1_p, hfc2_p,
      hp_s1, hp_s2, hp_l1, hp_l2, hp_l3, hp_c1, hp_c2]
  refine ⟨hsup, fun hok => ?_⟩
  unfold Ix.Kernel.strLitSupported at hok
  rw [hfs1_r, hfs2_r, hfl1_r, hfl2_r, hfl3_r, hfc1_r, hfc2_r] at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hok_nat, _⟩, hok_s2⟩, _⟩, hok_l2⟩, hok_l3⟩, hok_c1⟩, hok_c2⟩ := hok
  obtain ⟨hac_nz, hac_ns⟩ := hnat_ac hok_nat
  have hle_s2 : cs2_r.toConstantVal.levelParams.length ≤ 1 := by
    simp only [Ix.Kernel.stringOfListTyOk, Bool.and_eq_true, List.isEmpty_iff] at hok_s2
    simp [hok_s2.1]
  have hle_l2 : cl2_r.toConstantVal.levelParams.length ≤ 1 := by
    cases hl : cl2_r.toConstantVal.levelParams with
    | nil => simp [Ix.Kernel.listNilTyOk, hl] at hok_l2
    | cons _ tl =>
      cases tl with
      | nil => simp
      | cons _ _ => simp [Ix.Kernel.listNilTyOk, hl] at hok_l2
  have hle_l3 : cl3_r.toConstantVal.levelParams.length ≤ 1 := by
    cases hl : cl3_r.toConstantVal.levelParams with
    | nil => simp [Ix.Kernel.listConsTyOk, hl] at hok_l3
    | cons _ tl =>
      cases tl with
      | nil => simp
      | cons _ _ => simp [Ix.Kernel.listConsTyOk, hl] at hok_l3
  have hle_c1 : cc1_r.toConstantVal.levelParams.length ≤ 1 := by
    simp only [Ix.Kernel.charTyOk, Bool.and_eq_true, List.isEmpty_iff] at hok_c1
    simp [hok_c1.1]
  have hle_c2 : cc2_r.toConstantVal.levelParams.length ≤ 1 := by
    simp only [Ix.Kernel.charOfNatTyOk, Bool.and_eq_true, List.isEmpty_iff] at hok_c2
    simp [hok_c2.1]
  have hl2_eq := hel2.le_one_eq (Or.inl hle_l2)
  have hl3_eq := hel3.le_one_eq (Or.inl hle_l3)
  refine ⟨(ac_eq_of_isEmpty_lps hes2 hle_s2).symm,
    hl2_eq.2.1.symm, hl3_eq.2.1.symm,
    (ac_eq_of_isEmpty_lps hec1 hle_c1).symm,
    (ac_eq_of_isEmpty_lps hec2 hle_c2).symm,
    hac_nz, hac_ns, ?_, ?_⟩
  · unfold levelParamsAt
    rw [hfl2_r, hfl2_p]
    dsimp only
    exact (congrArg ConstantVal.levelParams hl2_eq.1).symm
  · unfold levelParamsAt
    rw [hfl3_r, hfl3_p]
    dsimp only
    exact (congrArg ConstantVal.levelParams hl3_eq.1).symm

/-- **Master `denoteMeta` unpositionalization equality**: any expression whose constants resolve
in `E_r` denotes identically in `(ac_r, E_r)` and `(ac_p, E_p)`. -/
theorem denoteMeta_unpos_eq {ac_r ac_p : KKey → (LevelParam → Nat) → AnnotTerm}
    {E_r E_p : Env .anon} (h : UnposAgree ac_r E_r ac_p E_p) (φ : LevelParam → Nat) :
    ∀ (e : KExpr) (d : Nat), e.constsResolve E_r = true →
      denoteMeta ac_r E_r φ d e = denoteMeta ac_p E_p φ d e
  | .bvar _, _, _ => by rw [denoteMeta.eq_def, denoteMeta.eq_def]
  | .sort _, _, _ => by rw [denoteMeta, denoteMeta]
  | .fvar _ _, _, _ => by rw [denoteMeta, denoteMeta]
  | .letE _ _ _ _, _, _ => by rw [denoteMeta, denoteMeta]
  | .const k us, _, hcr => by
    simp only [Expr.constsResolve] at hcr
    obtain ⟨ci_r, hf_r⟩ := Option.isSome_iff_exists.mp hcr
    obtain ⟨ci_p, hf_p, hent⟩ := h.entry k ci_r hf_r
    rw [denoteMeta, hf_r, denoteMeta, hf_p]
    dsimp only
    rcases hent with ⟨rfl, hac⟩ | ⟨hperm, hcv, hac, _⟩
    · rw [hac]
    · have hlen_p : ci_p.toConstantVal.levelParams.length =
          ci_r.toConstantVal.levelParams.length := by
        rw [hcv]; simp [posCV]
      by_cases hlen : us.length = ci_r.toConstantVal.levelParams.length
      · rw [ite_eq_left hlen, ite_eq_left (hlen.trans hlen_p.symm)]
        have hlps_p : ci_p.toConstantVal.levelParams =
            List.range ci_r.toConstantVal.levelParams.length := by
          rw [hcv]; rfl
        rw [hac, posVal_substFn_eq hperm hlen φ, hlps_p]
      · rw [ite_eq_right hlen, ite_eq_right (fun hh => hlen (hh.trans hlen_p))]
  | .app f a, d, hcr => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    rw [denoteMeta, denoteMeta,
      denoteMeta_unpos_eq h φ f d hcr.1,
      denoteMeta_unpos_eq h φ a d hcr.2]
  | .lam ty bo m, d, hcr => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    have hb' : (bo.instantiate1 (.fvar d ty)).constsResolve E_r = true :=
      Expr.constsResolve_instantiate1 (d := d) hcr.1 0 hcr.2
    rw [denoteMeta, denoteMeta,
      denoteMeta_unpos_eq h φ ty d hcr.1,
      denoteMeta_unpos_eq h φ (bo.instantiate1 (.fvar d ty)) (d + 1) hb']
  | .forallE ty bo m, d, hcr => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    have hb' : (bo.instantiate1 (.fvar d ty)).constsResolve E_r = true :=
      Expr.constsResolve_instantiate1 (d := d) hcr.1 0 hcr.2
    rw [denoteMeta, denoteMeta,
      denoteMeta_unpos_eq h φ ty d hcr.1,
      denoteMeta_unpos_eq h φ (bo.instantiate1 (.fvar d ty)) (d + 1) hb']
  | .proj sn i sub, d, hcr => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    rw [denoteMeta, denoteMeta,
      denoteMeta_unpos_eq h φ sub d hcr.2,
      h.projEq sn hcr.1 i]
  | .lit (.natVal n), _, hcr => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hcr
    obtain ⟨hsup, hac⟩ := natLitSupported_unpos h hn1 hn2 hn3
    rw [denoteMeta, denoteMeta]
    by_cases hs : Ix.Kernel.natLitSupported E_r = true
    · obtain ⟨hz, hsu⟩ := hac hs
      rw [ite_eq_left hs, ite_eq_left (hsup ▸ hs), hz, hsu]
    · rw [ite_eq_right hs, ite_eq_right (hsup ▸ hs)]
  | .lit (.strVal s), _, hcr => by
    obtain ⟨hsup, hac⟩ := strLitSupported_unpos h hcr
    rw [denoteMeta, denoteMeta]
    by_cases hs : Ix.Kernel.strLitSupported E_r = true
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7, hl1, hl2⟩ := hac hs
      rw [ite_eq_left hs, ite_eq_left (hsup ▸ hs), h1, h2, h3, h4, h5, h6, h7, hl1, hl2]
    · rw [ite_eq_right hs, ite_eq_right (hsup ▸ hs)]
  termination_by e => e.sizeB
  decreasing_by
    all_goals
      simp [Expr.sizeB]
      try rw [Expr.sizeB_instantiate1 _ rfl]
      try omega

/-! ## Lockstep `EnvModelM` and `DeclStoreInv` Steps (Non-Recursors & Provisional Recursors) -/

/-- Step `DeclStoreInv` on a real prefix `E_r` by one non-recursor member (`indInfo cv {}` or
`ctorInfo cv nP nF`). -/
theorem DeclStoreInv.cons_nonrec {E_r : Env .anon} (hS : DeclStoreInv E_r)
    {c_r : ConstantInfo .anon}
    (hfresh : E_r.find? c_r.name = none)
    (hnpt : ∀ T, c_r.name ≠ projTableName T)
    (hknd : (∃ cv, c_r = .indInfo cv {}) ∨ ∃ cv nP nF, c_r = .ctorInfo cv nP nF)
    (htf : c_r.toConstantVal.type.hasFvar = false)
    (htp : c_r.toConstantVal.type.allLevelParamsDefined c_r.toConstantVal.levelParams = true)
    (htr : c_r.toConstantVal.type.constsResolve E_r = true)
    (htb : c_r.toConstantVal.type.looseBVarsBounded 0 = true) :
    DeclStoreInv ⟨c_r :: E_r.consts⟩ := by
  have hext : EnvExt E_r ⟨c_r :: E_r.consts⟩ := envExt_cons_fresh hfresh hnpt
  have hwf_c : Ix.Kernel.ConstWF ⟨c_r :: E_r.consts⟩ c_r := by
    refine Ix.Kernel.structConstWF htf htp (Ix.Kernel.Expr.constsResolve_mono htr) htb
      (fun _ _ _ heq => by rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch heq)
      (fun _ _ _ _ heq => by rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch heq)
      (fun _ heq => by rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch heq)
      (fun _ caps heq => by
        rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩
        · obtain ⟨_, rfl⟩ := ConstantInfo.indInfo.inj heq
          exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
        · exact nomatch heq)
  have hnotRec : NotRec c_r := fun _ _ _ _ heq => by
    rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch heq
  have hstore' : StoreInv ⟨c_r :: E_r.consts⟩ :=
    ⟨Ix.Kernel.EnvWF.cons hS.store.wf hwf_c,
     Ix.Kernel.RecCtorsStored.cons hS.store.rec_ctors hfresh (fun _ _ _ _ heq =>
       absurd heq (hnotRec _ _ _ _)),
     Ix.Kernel.Verify.ProjOkT.cons hS.store.proj_ok hfresh
       (fun _ heq => by rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch heq)⟩
  refine
    { store := hstore'
      thmTyped := thmTyped_step_noThm hext hS.thmTyped
        (NewSat.cons fun _ _ heq => by
          rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch heq)
      recK := recK_step_noRec hS.store hS.recK hext.find (NewSat.cons hnotRec)
      etaTowers := etaTowers_step_noEta hext hS.etaTowers
        (NewSat.cons fun _ caps heq he => by
          rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩
          · obtain ⟨_, rfl⟩ := ConstantInfo.indInfo.inj heq; exact nomatch he
          · exact nomatch heq)
      tableBodies := tableBodies_step_noProj hext.find hS.tableBodies
        (NewSat.cons fun _ heq => by
          rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch heq)
      recShape := recShape_step_noRec hS.store hS.recShape hext.find (NewSat.cons hnotRec) }

/-- Step `DeclStoreInv` on a real prefix `E_r` by one provisional rule-empty recursor. -/
theorem DeclStoreInv.cons_rec_prov {E_r : Env .anon} (hS : DeclStoreInv E_r)
    {cv : ConstantVal .anon} {mI rP : Nat}
    (hfresh : E_r.find? cv.name = none)
    (hnpt : ∀ T, cv.name ≠ projTableName T)
    (htf : cv.type.hasFvar = false)
    (htp : cv.type.allLevelParamsDefined cv.levelParams = true)
    (htr : cv.type.constsResolve E_r = true)
    (htb : cv.type.looseBVarsBounded 0 = true) :
    DeclStoreInv ⟨.recInfo cv mI rP [] :: E_r.consts⟩ := by
  let c_r : ConstantInfo .anon := .recInfo cv mI rP []
  have hfr_cr : E_r.find? c_r.name = none := hfresh
  have hext : EnvExt E_r ⟨c_r :: E_r.consts⟩ := envExt_cons_fresh hfr_cr hnpt
  have hwf_c : Ix.Kernel.ConstWF ⟨c_r :: E_r.consts⟩ c_r :=
    Ix.Kernel.structConstWF htf htp (Ix.Kernel.Expr.constsResolve_mono htr) htb
      (fun _ _ _ heq => nomatch heq)
      (fun _ _ _ _ heq _ hr => by
        obtain ⟨_, _, _, rfl⟩ := ConstantInfo.recInfo.inj heq
        exact nomatch hr)
      (fun _ heq => nomatch heq)
      (fun _ _ heq => nomatch heq)
  have hrc' : Ix.Kernel.RecCtorsStored ⟨c_r :: E_r.consts⟩ := by
    intro n cv' mI' rP' rules' hf r hr
    rw [Env.find?_cons] at hf
    by_cases heq : c_r.name = n
    · rw [ite_eq_left heq] at hf
      obtain ⟨_, _, _, rfl⟩ := ConstantInfo.recInfo.inj (Option.some.inj hf)
      exact nomatch hr
    · rw [ite_eq_right heq] at hf
      obtain ⟨hco, hk, he⟩ := hS.store.rec_ctors n cv' mI' rP' rules' hf r hr
      have hkeep : ∀ (m : KKey) (ci : ConstantInfo .anon),
          (∀ cv0 a b rs, ci ≠ .recInfo cv0 a b rs) →
          E_r.find? m = some ci → (⟨c_r :: E_r.consts⟩ : Env .anon).find? m = some ci :=
        fun _ _ _ hfm => Env.find?_cons_of_fresh hfr_cr hfm
      exact ⟨hco.mono hkeep,
        fun hb => Ix.Kernel.recRuleKOf_mono hkeep (hk hb),
        fun hb => Ix.Kernel.recRuleEtaOf_mono hkeep (he hb)⟩
  have hproj' : Ix.Kernel.ProjOkT ⟨c_r :: E_r.consts⟩ :=
    Ix.Kernel.Verify.ProjOkT.cons hS.store.proj_ok hfr_cr (fun _ heq => nomatch heq)
  have hstore' : StoreInv ⟨c_r :: E_r.consts⟩ :=
    ⟨Ix.Kernel.EnvWF.cons hS.store.wf hwf_c, hrc', hproj'⟩
  refine
    { store := hstore'
      thmTyped := thmTyped_step_noThm hext hS.thmTyped
        (NewSat.cons fun _ _ heq => nomatch heq)
      recK := recK_step hS.store hS.recK hext.find (by
        intro n cv' mI' rP' rules' hf hn0
        rw [Env.find?_cons] at hf
        by_cases heq : c_r.name = n
        · rw [ite_eq_left heq] at hf
          obtain ⟨_, _, _, rfl⟩ := ConstantInfo.recInfo.inj (Option.some.inj hf)
          exact ⟨(fun _ hr => nomatch hr), (fun _ _ hr => nomatch hr)⟩
        · rw [ite_eq_right heq] at hf
          rw [hf] at hn0; exact nomatch hn0)
      etaTowers := etaTowers_step_noEta hext hS.etaTowers
        (NewSat.cons fun _ _ heq => nomatch heq)
      tableBodies := tableBodies_step_noProj hext.find hS.tableBodies
        (NewSat.cons fun _ heq => nomatch heq)
      recShape := recShape_step hS.store hS.recShape hext.find (by
        intro n cv' mI' rP' rules' hf hn0
        rw [Env.find?_cons] at hf
        by_cases heq : c_r.name = n
        · rw [ite_eq_left heq] at hf
          obtain ⟨_, _, _, rfl⟩ := ConstantInfo.recInfo.inj (Option.some.inj hf)
          exact ⟨(fun _ hr => nomatch hr), (fun _ _ hr => nomatch hr),
            (fun _ _ hr => nomatch hr), (fun _ _ hr _ => nomatch hr)⟩
        · rw [ite_eq_right heq] at hf
          rw [hf] at hn0; exact nomatch hn0) }

/-- Lockstep `EnvModelM` + `UnposAgree` step for one non-recursor member (`indInfo cv {}` or
`ctorInfo cv nP nF`), given that its positional counterpart `posCI c_r` already stepped `E_p`. -/
theorem step_nonrec_unpos {V : Type u} [Ix.Kernel.SetTheory V]
    {E_r E_p : Env .anon}
    (mp_r : EnvModelM V .verified E_r)
    (mp_p' : EnvModelM V .verified ⟨posCI c_r :: E_p.consts⟩)
    {ac_p : KKey → (LevelParam → Nat) → AnnotTerm}
    {A_p : (LevelParam → Nat) → AnnotTerm}
    (hagree : UnposAgree mp_r.base2.acval E_r ac_p E_p)
    (hac_p' : mp_p'.base2.acval = acvalWith ac_p (posCI c_r).name A_p)
    (hA_p_src : ∃ k_m cvm mval hint,
      E_p.find? k_m = some (.defnInfo cvm mval hint) ∧
      cvm.levelParams = List.range c_r.toConstantVal.levelParams.length ∧
      A_p = ac_p k_m ∧
      (∀ ψ, Term.Closed ((A_p ψ).erase)) ∧
      (∀ ψ k, (A_p ψ).liftN 1 k = A_p ψ) ∧
      (∀ ψ₁ ψ₂, (∀ i ∈ List.range c_r.toConstantVal.levelParams.length, ψ₁ i = ψ₂ i) →
        A_p ψ₁ = A_p ψ₂) ∧
      (∀ ψ ρ, WellDenoted V ρ (A_p ψ)) ∧
      (∀ ψ ρ, AnnotValid V ρ (A_p ψ)))
    (hEta_r : Ix.Kernel.EtaFamiliesClosed E_r)
    (hbase : isBaseKey c_r.name = true)
    (hfresh_r : E_r.find? c_r.name = none)
    (hfresh_p : E_p.find? (posCI c_r).name = none)
    (hnres : Ix.Kernel.reservedBasisNames.contains c_r.name = false)
    (hperm : c_r.toConstantVal.levelParams.Perm (List.range c_r.toConstantVal.levelParams.length))
    (hknd : (∃ cv, c_r = .indInfo cv {}) ∨ ∃ cv nP nF, c_r = .ctorInfo cv nP nF)
    (htf : c_r.toConstantVal.type.hasFvar = false)
    (htp : c_r.toConstantVal.type.allLevelParamsDefined c_r.toConstantVal.levelParams = true)
    (htr : c_r.toConstantVal.type.constsResolve E_r = true)
    (htb : c_r.toConstantVal.type.looseBVarsBounded 0 = true)
    (hproj_self : E_p.find? (projTableName c_r.name) = E_r.find? (projTableName c_r.name)) :
    ∃ mp_r' : EnvModelM V .verified ⟨c_r :: E_r.consts⟩,
      Ix.Kernel.EtaFamiliesClosed ⟨c_r :: E_r.consts⟩ ∧
      ModelExt mp_r mp_r' ∧
      UnposAgree mp_r'.base2.acval ⟨c_r :: E_r.consts⟩
        mp_p'.base2.acval ⟨posCI c_r :: E_p.consts⟩ := by
  let lps := c_r.toConstantVal.levelParams
  let A_r : (LevelParam → Nat) → AnnotTerm := fun ψ => A_p (posVal lps ψ)
  obtain ⟨k_m, cvm, mval, hint, _, _, _, hAclL, hAcl, hApar, hAwd, hAval⟩ := hA_p_src
  have hname_p : (posCI c_r).name = c_r.name := by
    rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
  have hcv_p : (posCI c_r).toConstantVal = posCV c_r.toConstantVal := by
    rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
  have htag_p : UnposTagMatch c_r (posCI c_r) := by
    rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩
    · rfl
    · exact ⟨rfl, rfl⟩
  have hnpt_r : ∀ T, c_r.name ≠ projTableName T := fun T => ne_projTableName_of_isBaseKey hbase
  have hshape_r : c_r.name.isProjFnShape = false := isProjFnShape_of_isBaseKey hbase
  have hagree' : UnposAgree (acvalWith mp_r.base2.acval c_r.name A_r) ⟨c_r :: E_r.consts⟩
      mp_p'.base2.acval ⟨posCI c_r :: E_p.consts⟩ := by
    rw [hac_p']
    exact hagree.cons_pair hname_p hfresh_r hfresh_p hnpt_r hperm hcv_p (fun _ => rfl)
      htag_p hproj_self
  have hmem_p' : posCI c_r ∈ (⟨posCI c_r :: E_p.consts⟩ : Env .anon).consts := List.mem_cons_self
  have htr_r' : c_r.toConstantVal.type.constsResolve ⟨c_r :: E_r.consts⟩ = true :=
    Ix.Kernel.Expr.constsResolve_mono htr
  have hden_link : ∀ ψ : LevelParam → Nat,
      denoteMeta (acvalWith mp_r.base2.acval c_r.name A_r) ⟨c_r :: E_r.consts⟩
        ψ 0 c_r.toConstantVal.type =
      denoteMeta mp_p'.base2.acval ⟨posCI c_r :: E_p.consts⟩
        (posVal lps ψ) 0 (posCI c_r).toConstantVal.type := by
    intro ψ
    rw [denoteMeta_unpos_eq hagree' ψ c_r.toConstantVal.type 0 htr_r', hcv_p]
    unfold posCV
    dsimp only
    exact (denoteMeta_posOf mp_p'.base2 hperm ψ 0 c_r.toConstantVal.type).symm
  have hwf_c : Ix.Kernel.ConstWF ⟨c_r :: E_r.consts⟩ c_r := by
    refine Ix.Kernel.structConstWF htf htp htr_r' htb
      (fun _ _ _ heq => by rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch heq)
      (fun _ _ _ _ heq => by rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch heq)
      (fun _ heq => by rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch heq)
      (fun _ caps heq => by
        rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩
        · obtain ⟨_, rfl⟩ := ConstantInfo.indInfo.inj heq
          exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
        · exact nomatch heq)
  have hh : ConsHead E_r c_r A_r :=
    ConsHead.ofFresh (Ix.Kernel.EnvWF.cons mp_r.base2.wf hwf_c)
      (fun ψ => hAclL (posVal lps ψ)) hnres
      (fun _ heq => by rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch heq)
      (fun _ _ _ _ heq => by rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch heq)
  have hknd_full : (∃ cv caps, c_r = .indInfo cv caps) ∨ ∃ cv nP nF, c_r = .ctorInfo cv nP nF := by
    rcases hknd with ⟨cv, rfl⟩ | ⟨cv, nP, nF, rfl⟩
    · exact Or.inl ⟨cv, {}, rfl⟩
    · exact Or.inr ⟨cv, nP, nF, rfl⟩
  have hstep : ∃ mp_r' : EnvModelM V .verified ⟨c_r :: E_r.consts⟩,
      mp_r'.base2.acval = acvalWith mp_r.base2.acval c_r.name A_r := by
    refine declStep_preserves_of_ind_member_cons mp_r hfresh_r hnres hknd_full hh
      (fun ψ k => hAcl (posVal lps ψ) k)
      (fun ψ₁ ψ₂ hp => hApar _ _ (posVal_congr_mem hp))
      (fun ψ ρ => hAwd (posVal lps ψ) ρ)
      (fun ψ ρ => hAval (posVal lps ψ) ρ)
      ?_ ?_ ?_ ?_
    · intro ψ
      obtain ⟨ta, hta⟩ := mp_p'.type_reads _ hmem_p' (posVal lps ψ)
      rw [← hden_link ψ] at hta
      exact ⟨ta, hta⟩
    · intro ψ ta hta ρ
      rw [hden_link ψ] at hta
      exact mp_p'.type_wellDenotedV _ hmem_p' (posVal lps ψ) ta hta ρ
    · intro ψ ta hta ρ
      rw [hden_link ψ] at hta
      have hm := mp_p'.mem_type _ hmem_p' (posVal lps ψ) ta hta ρ
      have hlhs : mp_p'.base2.acval (posCI c_r).name (posVal lps ψ) = A_r ψ := by
        rw [hac_p', acvalWith_self]
      rwa [hlhs] at hm
    · intro m₂ hm₂
      refine capsOk_cons_native mp_r (T := c_r.name) hfresh_r hh.projTower hshape_r
        (by
          rcases hknd with ⟨cv, rfl⟩ | ⟨cv, nP, nF, rfl⟩
          · exact Or.inl ⟨cv, {}, rfl, rfl⟩
          · exact Or.inr fun _ _ h => nomatch h)
        (fun T' cvT' caps' hfT' _ hres' hcape' => hEta_r T' cvT' caps' hfT' hcape' hres')
        m₂ hm₂ ?_
      intro cvT caps hfT _
      rw [Env.find?_cons, ite_eq_left rfl] at hfT
      rcases hknd with ⟨cv, rfl⟩ | ⟨cv, nP, nF, rfl⟩
      · obtain ⟨_, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hfT)
        exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
      · exact nomatch hfT
  obtain ⟨mp_r', hac_r'⟩ := hstep
  have hEta_r' : Ix.Kernel.EtaFamiliesClosed ⟨c_r :: E_r.consts⟩ := by
    rcases hknd with ⟨cv, rfl⟩ | ⟨cv, nP, nF, rfl⟩
    · exact (hEta_r.except cv.name).cons hfresh_r (fun _ caps heq he => by
        obtain ⟨_, rfl⟩ := ConstantInfo.indInfo.inj heq
        exact nomatch he) |>.closed fun _ caps hf he _ => by
          have hf0 := Env.find?_cons_self (.indInfo cv {}) E_r
          dsimp only [ConstantInfo.name, ConstantInfo.toConstantVal] at hf0 hf
          rw [hf0] at hf
          obtain ⟨_, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hf)
          exact nomatch he
    · exact Ix.Kernel.EtaFamiliesClosed.cons_nonind hEta_r hfresh_r fun _ _ h => nomatch h
  have hext_r : ModelExt mp_r mp_r' :=
    ModelExt.step .refl hfresh_r
      (fun _ _ _ => ConsCrossAt.ofNtc
        (fun _ heq => by rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch heq))
      (fun _ _ heq => by rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch heq)
      hac_r'
  exact ⟨mp_r', hEta_r', hext_r, hac_r' ▸ hagree'⟩

/-- Lockstep `EnvModelM` + `UnposAgree` step for one provisional rule-empty recursor. -/
theorem step_rec_prov_unpos {V : Type u} [Ix.Kernel.SetTheory V]
    {E_r E_p : Env .anon} {cv : ConstantVal .anon} {mI rP : Nat}
    (mp_r : EnvModelM V .verified E_r)
    (mp_p' : EnvModelM V .verified ⟨.recInfo (posCV cv) mI rP [] :: E_p.consts⟩)
    {ac_p : KKey → (LevelParam → Nat) → AnnotTerm}
    {A_p : (LevelParam → Nat) → AnnotTerm}
    (hagree : UnposAgree mp_r.base2.acval E_r ac_p E_p)
    (hac_p' : mp_p'.base2.acval = acvalWith ac_p cv.name A_p)
    (hA_p_src :
      (∀ ψ, Term.Closed ((A_p ψ).erase)) ∧
      (∀ ψ k, (A_p ψ).liftN 1 k = A_p ψ) ∧
      (∀ ψ₁ ψ₂, (∀ i ∈ List.range cv.levelParams.length, ψ₁ i = ψ₂ i) →
        A_p ψ₁ = A_p ψ₂) ∧
      (∀ ψ ρ, WellDenoted V ρ (A_p ψ)) ∧
      (∀ ψ ρ, AnnotValid V ρ (A_p ψ)))
    (hEta_r : Ix.Kernel.EtaFamiliesClosed E_r)
    (hbase : isBaseKey cv.name = true)
    (hfresh_r : E_r.find? cv.name = none)
    (hfresh_p : E_p.find? cv.name = none)
    (hnres : Ix.Kernel.reservedBasisNames.contains cv.name = false)
    (hperm : cv.levelParams.Perm (List.range cv.levelParams.length))
    (htf : cv.type.hasFvar = false)
    (htp : cv.type.allLevelParamsDefined cv.levelParams = true)
    (htr : cv.type.constsResolve E_r = true)
    (htb : cv.type.looseBVarsBounded 0 = true)
    (hproj_self : E_p.find? (projTableName cv.name) = E_r.find? (projTableName cv.name)) :
    let c_r : ConstantInfo .anon := .recInfo cv mI rP []
    let c_p : ConstantInfo .anon := .recInfo (posCV cv) mI rP []
    ∃ mp_r' : EnvModelM V .verified ⟨c_r :: E_r.consts⟩,
      Ix.Kernel.EtaFamiliesClosed ⟨c_r :: E_r.consts⟩ ∧
      ModelExt mp_r mp_r' ∧
      UnposAgree mp_r'.base2.acval ⟨c_r :: E_r.consts⟩
        mp_p'.base2.acval ⟨c_p :: E_p.consts⟩ := by
  let c_r : ConstantInfo .anon := .recInfo cv mI rP []
  let c_p : ConstantInfo .anon := .recInfo (posCV cv) mI rP []
  let A_r : (LevelParam → Nat) → AnnotTerm := fun ψ => A_p (posVal cv.levelParams ψ)
  obtain ⟨hAclL, hAcl, hApar, hAwd, hAval⟩ := hA_p_src
  have hnpt_r : ∀ T, cv.name ≠ projTableName T := fun T => ne_projTableName_of_isBaseKey hbase
  have hshape_r : cv.name.isProjFnShape = false := isProjFnShape_of_isBaseKey hbase
  have hfr_cr : E_r.find? c_r.name = none := hfresh_r
  have hfr_cp : E_p.find? c_p.name = none := hfresh_p
  have hagree' : UnposAgree (acvalWith mp_r.base2.acval c_r.name A_r) ⟨c_r :: E_r.consts⟩
      mp_p'.base2.acval ⟨c_p :: E_p.consts⟩ := by
    rw [hac_p']
    exact hagree.cons_pair (c_r := c_r) (c_p := c_p) rfl hfr_cr hfr_cp hnpt_r hperm rfl
      (fun _ => rfl) trivial hproj_self
  have hmem_p' : c_p ∈ (⟨c_p :: E_p.consts⟩ : Env .anon).consts := List.mem_cons_self
  have htr_r' : cv.type.constsResolve ⟨c_r :: E_r.consts⟩ = true :=
    Ix.Kernel.Expr.constsResolve_mono htr
  have hden_link : ∀ ψ : LevelParam → Nat,
      denoteMeta (acvalWith mp_r.base2.acval c_r.name A_r) ⟨c_r :: E_r.consts⟩ ψ 0 cv.type =
      denoteMeta mp_p'.base2.acval ⟨c_p :: E_p.consts⟩
        (posVal cv.levelParams ψ) 0 (posOf cv.levelParams cv.type) := by
    intro ψ
    rw [denoteMeta_unpos_eq hagree' ψ cv.type 0 htr_r']
    exact (denoteMeta_posOf mp_p'.base2 hperm ψ 0 cv.type).symm
  have hwf_c : Ix.Kernel.ConstWF ⟨c_r :: E_r.consts⟩ c_r :=
    Ix.Kernel.structConstWF htf htp htr_r' htb
      (fun _ _ _ heq => nomatch heq)
      (fun _ _ _ _ heq _ hr => by
        obtain ⟨_, _, _, rfl⟩ := ConstantInfo.recInfo.inj heq
        exact nomatch hr)
      (fun _ heq => nomatch heq)
      (fun _ _ heq => nomatch heq)
  have hh : ConsHead E_r c_r A_r :=
    ConsHead.ofFresh (Ix.Kernel.EnvWF.cons mp_r.base2.wf hwf_c)
      (fun ψ => hAclL (posVal cv.levelParams ψ)) hnres
      (fun _ heq => nomatch heq)
      (fun _ _ _ _ heq _ hr => by
        obtain ⟨_, _, _, rfl⟩ := ConstantInfo.recInfo.inj heq
        exact nomatch hr)
  have hstep : ∃ mp_r' : EnvModelM V .verified ⟨c_r :: E_r.consts⟩,
      mp_r'.base2.acval = acvalWith mp_r.base2.acval c_r.name A_r := by
    refine declStep_preserves_of_ind_rec_cons mp_r (c₀ := c_r) (A := A_r) hfr_cr hnres
      ⟨cv, mI, rP, [], rfl⟩ hh
      (fun ψ k => hAcl (posVal cv.levelParams ψ) k)
      (fun ψ₁ ψ₂ hp => hApar _ _ (posVal_congr_mem hp))
      (fun ψ ρ => hAwd (posVal cv.levelParams ψ) ρ)
      (fun ψ ρ => hAval (posVal cv.levelParams ψ) ρ)
      ?_ ?_ ?_
      (fun m₂ hm₂ => capsOk_cons_rec_nonproj mp_r (cvR := cv) (mI := mI) (rP := rP)
        (rules := []) hfresh_r hshape_r m₂ hm₂)
      (fun m₂ hm₂ φ => recRules_cons_fresh mp_r (c₀ := c_r) (A := A_r) hfr_cr hh.projTower
        (fun _ _ _ _ heq => by
          obtain ⟨_, _, _, rfl⟩ := ConstantInfo.recInfo.inj heq
          rfl) m₂ hm₂ φ)
    · intro ψ
      obtain ⟨ta, hta⟩ := mp_p'.type_reads _ hmem_p' (posVal cv.levelParams ψ)
      change denoteMeta mp_p'.base2.acval ⟨c_p :: E_p.consts⟩
        (posVal cv.levelParams ψ) 0 (posOf cv.levelParams cv.type) = some ta at hta
      rw [← hden_link ψ] at hta
      exact ⟨ta, hta⟩
    · intro ψ ta hta ρ
      dsimp only [c_r, ConstantInfo.toConstantVal] at hta
      rw [hden_link ψ] at hta
      exact mp_p'.type_wellDenotedV _ hmem_p' (posVal cv.levelParams ψ) ta hta ρ
    · intro ψ ta hta ρ
      dsimp only [c_r, ConstantInfo.toConstantVal] at hta
      rw [hden_link ψ] at hta
      have hm := mp_p'.mem_type _ hmem_p' (posVal cv.levelParams ψ) ta hta ρ
      have hlhs : mp_p'.base2.acval c_p.name (posVal cv.levelParams ψ) = A_r ψ := by
        change mp_p'.base2.acval cv.name (posVal cv.levelParams ψ) = A_r ψ
        rw [hac_p', acvalWith_self]
      rwa [hlhs] at hm
  obtain ⟨mp_r', hac_r'⟩ := hstep
  have hEta_r' : Ix.Kernel.EtaFamiliesClosed ⟨c_r :: E_r.consts⟩ :=
    Ix.Kernel.EtaFamiliesClosed.cons_nonind hEta_r hfr_cr fun _ _ h => nomatch h
  have hext_r : ModelExt mp_r mp_r' :=
    ModelExt.step .refl hfr_cr
      (fun _ _ _ => ConsCrossAt.ofNtc (fun _ heq => nomatch heq))
      (fun _ _ heq => nomatch heq) hac_r'
  exact ⟨mp_r', hEta_r', hext_r, hac_r' ▸ hagree'⟩

/-! ## Unpositionalizing `RecRuleLaw`, `RuleFacts`, and `RuleFactsS` -/

/-- Unpositionalize `RecRuleLaw` from `mpSelf_p.base2` (`posCheckedRule`) to `mpSelf_r.base2`
(`realCheckedRule`) at the exact same universe valuation `φ`. -/
theorem unpos_recRuleLaw {V : Type u} [Ix.Kernel.SetTheory V]
    {E_r E_p : Env .anon}
    (mp_r : EnvModelM V .verified E_r)
    (mp_p : EnvModelM V .verified E_p)
    (hagree : UnposAgree mp_r.base2.acval E_r mp_p.base2.acval E_p)
    {findM_r findM_p : KKey → Option (ConstantInfo .anon)}
    {cv : ConstantVal .anon} {mI rP cnP_ind : Nat}
    {lvls_lps : List KLevel} {pins_lps : List KExpr} {r : RecRule .anon}
    (hperm : cv.levelParams.Perm (List.range cv.levelParams.length))
    (hrec_ac : ∀ ψ, mp_r.base2.acval cv.name ψ =
      mp_p.base2.acval cv.name (posVal cv.levelParams ψ))
    (hty_cr : cv.type.constsResolve E_r = true)
    (hrhs_cr : r.rhs.constsResolve E_r = true)
    (hpins_len : pins_lps.length = cnP_ind)
    (hpins_cr : ∀ p ∈ pins_lps, p.constsResolve E_r = true)
    (hlvls_ctor : ∀ cvj cnP cnF, E_r.find? r.ctor = some (.ctorInfo cvj cnP cnF) →
      lvls_lps.length = cvj.levelParams.length)
    (hctor_cr : ∀ cvj cnP cnF, E_r.find? r.ctor = some (.ctorInfo cvj cnP cnF) →
      cvj.type.constsResolve E_r = true)
    {φ : LevelParam → Nat}
    (hlaw_p : RecRuleLaw mp_p.base2 φ cv.name (posCV cv) mI rP
      (posCheckedRule findM_p cv.name cv.levelParams cnP_ind lvls_lps pins_lps r)) :
    RecRuleLaw mp_r.base2 φ cv.name cv mI rP
      (realCheckedRule findM_r cv.name cnP_ind lvls_lps pins_lps r) := by
  let lps := cv.levelParams
  let rl_p := posCheckedRule findM_p cv.name lps cnP_ind lvls_lps pins_lps r
  let rl_r := realCheckedRule findM_r cv.name cnP_ind lvls_lps pins_lps r
  let lvls_p := lvls_lps.map (Level.subst lps (posLevels lps))
  let pins_p := pins_lps.map (posOf lps)
  obtain ⟨hrPmI, hbody_p⟩ := hlaw_p
  refine ⟨hrPmI, fun us hus => ?_⟩
  have hus_p : us.length = (posCV cv).levelParams.length := by
    simp [posCV, lps, hus]
  obtain ⟨Ra, hRa_p, hRa_wd, hpins_law_p, hmain_p⟩ := hbody_p us hus_p
  have hrhs_inst_eq : rl_p.rhs.instantiateLevelParams (posCV cv).levelParams us =
      rl_r.rhs.instantiateLevelParams lps us := by
    show (posOf lps r.rhs).instantiateLevelParams (List.range lps.length) us =
      r.rhs.instantiateLevelParams lps us
    rw [← hus]
    exact InferAux.posOf_instantiateLevelParams_perm hperm hus (T := r.rhs)
  have hrhs_inst_cr : (rl_r.rhs.instantiateLevelParams lps us).constsResolve E_r = true := by
    show (r.rhs.instantiateLevelParams lps us).constsResolve E_r = true
    rw [constsResolve_instantiateLevelParams]
    exact hrhs_cr
  have hRa_r : denoteMeta mp_r.base2.acval E_r φ 0
      (rl_r.rhs.instantiateLevelParams lps us) = some Ra := by
    rw [denoteMeta_unpos_eq hagree φ _ 0 hrhs_inst_cr, ← hrhs_inst_eq]
    exact hRa_p
  have hty_inst_eq : (posCV cv).type.instantiateLevelParams (posCV cv).levelParams us =
      cv.type.instantiateLevelParams lps us := by
    show (posOf lps cv.type).instantiateLevelParams (List.range lps.length) us =
      cv.type.instantiateLevelParams lps us
    rw [← hus]
    exact InferAux.posOf_instantiateLevelParams_perm hperm hus (T := cv.type)
  have hty_inst_cr : (cv.type.instantiateLevelParams lps us).constsResolve E_r = true := by
    rw [constsResolve_instantiateLevelParams]
    exact hty_cr
  have hpin_open_eq : ∀ i, i < cnP_ind →
      openRev 0 rP ((pins_p.getD i default).instantiateLevelParams (posCV cv).levelParams us) =
      openRev 0 rP ((pins_lps.getD i default).instantiateLevelParams lps us) ∧
      (openRev 0 rP ((pins_lps.getD i default).instantiateLevelParams lps us)).constsResolve E_r =
        true := by
    intro i hi
    have hi_len : i < pins_lps.length := hpins_len ▸ hi
    have hgd : pins_p.getD i default = posOf lps (pins_lps.getD i default) := by
      simp [pins_p, List.getD, List.getElem?_eq_getElem hi_len, List.getElem?_map]
    have hinst : (pins_p.getD i default).instantiateLevelParams (posCV cv).levelParams us =
        (pins_lps.getD i default).instantiateLevelParams lps us := by
      rw [hgd]
      show (posOf lps (pins_lps.getD i default)).instantiateLevelParams (List.range lps.length) us =
        (pins_lps.getD i default).instantiateLevelParams lps us
      rw [← hus]
      exact InferAux.posOf_instantiateLevelParams_perm hperm hus
    have hp_mem : pins_lps.getD i default ∈ pins_lps := by
      simp [List.getD, List.getElem?_eq_getElem hi_len]
    have hp_cr : ((pins_lps.getD i default).instantiateLevelParams lps us).constsResolve E_r =
        true := by
      rw [constsResolve_instantiateLevelParams]
      exact hpins_cr _ hp_mem
    exact ⟨congrArg (openRev 0 rP) hinst, constsResolve_openRev 0 rP hp_cr⟩
  refine ⟨Ra, hRa_r, hRa_wd, ?_, ?_⟩
  · intro lvls₀ pins₀ hfire₀ i hi
    have hfr : rl_r.fire = .nested lvls_lps pins_lps := rfl
    rw [hfr] at hfire₀
    obtain ⟨rfl, rfl⟩ := RecRuleFire.nested.inj hfire₀
    have hi_ind : i < cnP_ind := hi
    obtain ⟨vpa, hvpa_p, hvpa_wd⟩ := hpins_law_p lvls_p pins_p rfl i hi_ind
    obtain ⟨hop_eq, hop_cr⟩ := hpin_open_eq i hi_ind
    have hvpa_r : denoteMeta mp_r.base2.acval E_r φ rP
        (openRev 0 rP ((pins_lps.getD i default).instantiateLevelParams lps us)) = some vpa := by
      rw [denoteMeta_unpos_eq hagree φ _ rP hop_cr, ← hop_eq]
      exact hvpa_p
    refine ⟨vpa, hvpa_r, fun ρ zs TVa restR hzs hzs_wd hTVa_r hfit => ?_⟩
    have hTVa_p : denoteMeta mp_p.base2.acval E_p φ 0
        ((posCV cv).type.instantiateLevelParams (posCV cv).levelParams us) = some TVa := by
      rw [hty_inst_eq, ← denoteMeta_unpos_eq hagree φ _ 0 hty_inst_cr]
      exact hTVa_r
    exact hvpa_wd ρ zs TVa restR hzs hzs_wd hTVa_p hfit
  · intro cvj cnP cnF hfc_r usj ρ xs ys TVa TVja restR restC
      hxs hys husj hlev hparP hparN hidx hTVa_r hTVja_r hfitR hfitC
    have hctor_eq : rl_r.ctor = r.ctor := rfl
    rw [hctor_eq] at hfc_r
    obtain ⟨ci_p, hfc_p0, hent_j⟩ := hagree.entry r.ctor (.ctorInfo cvj cnP cnF) hfc_r
    have hTVa_p : denoteMeta mp_p.base2.acval E_p φ 0
        ((posCV cv).type.instantiateLevelParams (posCV cv).levelParams us) = some TVa := by
      rw [hty_inst_eq, ← denoteMeta_unpos_eq hagree φ _ 0 hty_inst_cr]
      exact hTVa_r
    have hparP_p : rl_p.paramsBlind = false → rl_p.fire = .plain →
        ∀ i, i < rl_p.ctorParams → i < mI →
          interp V ρ (ys.getD i default) = interp V ρ (xs.getD i default) := by
      intro _ hfp
      exact nomatch hfp
    have hparN_p : ∀ lvls₀ pins₀, rl_p.fire = .nested lvls₀ pins₀ →
        ∀ i, i < rl_p.ctorParams → ∀ vpa : AnnotTerm,
          denoteMeta mp_p.base2.acval E_p φ rP
            (openRev 0 rP ((pins₀.getD i default).instantiateLevelParams (posCV cv).levelParams us)) =
            some vpa →
          interp V ρ (ys.getD i default) =
            interp V ρ (AnnotTerm.instRevChain (xs.take rP) vpa) := by
      intro lvls₀ pins₀ hfn₀ i hi vpa hvpa_p
      have hfp : rl_p.fire = .nested lvls_p pins_p := rfl
      rw [hfp] at hfn₀
      obtain ⟨rfl, rfl⟩ := RecRuleFire.nested.inj hfn₀
      obtain ⟨hop_eq, hop_cr⟩ := hpin_open_eq i hi
      have hvpa_r : denoteMeta mp_r.base2.acval E_r φ rP
          (openRev 0 rP ((pins_lps.getD i default).instantiateLevelParams lps us)) = some vpa := by
        rw [denoteMeta_unpos_eq hagree φ _ rP hop_cr, ← hop_eq]
        exact hvpa_p
      exact hparN lvls_lps pins_lps rfl i hi vpa hvpa_r
    have hcomp_eq : (Ix.Kernel.recFireComparands rl_p (posCV cv).levelParams us [] [] rP).1 =
        (Ix.Kernel.recFireComparands rl_r lps us [] [] rP).1 := by
      show lvls_p.map (Level.subst (List.range lps.length) us) = lvls_lps.map (Level.subst lps us)
      simp only [lvls_p, List.map_map]
      apply List.map_congr_left
      intro u _
      exact subst_posLevels_comp hperm hus u
    have hrec_leaf : mp_r.base2.acval cv.name (Level.substFn φ lps us) =
        mp_p.base2.acval cv.name (Level.substFn φ (posCV cv).levelParams us) := by
      rw [hrec_ac, posVal_substFn_eq hperm hus φ]; rfl
    have hcvj_cr : (cvj.type.instantiateLevelParams cvj.levelParams usj).constsResolve E_r = true := by
      rw [constsResolve_instantiateLevelParams]
      exact hctor_cr cvj cnP cnF hfc_r
    rcases hent_j with ⟨rfl, hac_j⟩ | ⟨hperm_j, hcv_j, hac_j, htag_j⟩
    · have hTVja_p : denoteMeta mp_p.base2.acval E_p φ 0
          (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVja := by
        rw [← denoteMeta_unpos_eq hagree φ _ 0 hcvj_cr]
        exact hTVja_r
      have hlev_p : Level.substFn φ cvj.levelParams usj =
          Level.substFn φ cvj.levelParams
            (Ix.Kernel.recFireComparands rl_p (posCV cv).levelParams us cvj.levelParams [] rP).1 := by
        have hc1 : (Ix.Kernel.recFireComparands rl_p (posCV cv).levelParams us cvj.levelParams [] rP).1 =
            (Ix.Kernel.recFireComparands rl_r lps us cvj.levelParams [] rP).1 := hcomp_eq
        rw [hc1]; exact hlev
      have hfitR_p : TeleFitPA V ρ TVa
          (xs ++ [AnnotTerm.mkAppN
            (mp_p.base2.acval rl_p.ctor (Level.substFn φ cvj.levelParams usj)) ys]) restR := by
        change TeleFitPA V ρ TVa
          (xs ++ [AnnotTerm.mkAppN
            (mp_p.base2.acval r.ctor (Level.substFn φ cvj.levelParams usj)) ys]) restR
        rw [hac_j]; exact hfitR
      obtain ⟨heq_p, hwd_p⟩ := hmain_p cvj cnP cnF hfc_p0 usj ρ xs ys TVa TVja restR restC
        hxs hys husj hlev_p hparP_p hparN_p hidx hTVa_p hTVja_p hfitR_p hfitC
      refine ⟨?_, hwd_p⟩
      change interp V ρ
          (AnnotTerm.mkAppN (mp_r.base2.acval cv.name (Level.substFn φ lps us))
            (xs ++ [AnnotTerm.mkAppN
              (mp_r.base2.acval r.ctor (Level.substFn φ cvj.levelParams usj)) ys])) = _
      rw [hrec_leaf, ← hac_j]
      exact heq_p
    · cases ci_p with
      | ctorInfo cvj_p cnP_p cnF_p =>
        dsimp only [ConstantInfo.toConstantVal, UnposTagMatch] at hperm_j hcv_j hac_j htag_j
        obtain ⟨rfl, rfl⟩ := htag_j
        have hcvj_inst_eq : cvj_p.type.instantiateLevelParams cvj_p.levelParams usj =
            cvj.type.instantiateLevelParams cvj.levelParams usj := by
          rw [hcv_j]
          dsimp only [posCV]
          rw [← husj]
          exact InferAux.posOf_instantiateLevelParams_perm hperm_j husj (T := cvj.type)
        have hTVja_p : denoteMeta mp_p.base2.acval E_p φ 0
            (cvj_p.type.instantiateLevelParams cvj_p.levelParams usj) = some TVja := by
          rw [hcvj_inst_eq, ← denoteMeta_unpos_eq hagree φ _ 0 hcvj_cr]
          exact hTVja_r
        have husj_p : usj.length = cvj_p.levelParams.length := by
          rw [hcv_j]; simp [posCV, husj]
        have hws_len : (Ix.Kernel.recFireComparands rl_r lps us cvj.levelParams [] rP).1.length =
            cvj.levelParams.length := by
          show (lvls_lps.map (Level.subst lps us)).length = cvj.levelParams.length
          rw [List.length_map]
          exact hlvls_ctor cvj cnP_p cnF_p hfc_r
        have hlev_p : Level.substFn φ cvj_p.levelParams usj =
            Level.substFn φ cvj_p.levelParams
              (Ix.Kernel.recFireComparands rl_p (posCV cv).levelParams us cvj_p.levelParams [] rP).1 := by
          have hlps_jp : cvj_p.levelParams = List.range cvj.levelParams.length := by
            rw [hcv_j]; rfl
          have hc1 : (Ix.Kernel.recFireComparands rl_p (posCV cv).levelParams us cvj_p.levelParams [] rP).1 =
              (Ix.Kernel.recFireComparands rl_r lps us cvj.levelParams [] rP).1 := hcomp_eq
          rw [hc1, hlps_jp, ← posVal_substFn_eq hperm_j husj φ,
            ← posVal_substFn_eq hperm_j hws_len φ, hlev]
        have hctor_leaf : mp_r.base2.acval r.ctor (Level.substFn φ cvj.levelParams usj) =
            mp_p.base2.acval r.ctor (Level.substFn φ cvj_p.levelParams usj) := by
          have hlps_jp : cvj_p.levelParams = List.range cvj.levelParams.length := by
            rw [hcv_j]; rfl
          rw [hac_j, posVal_substFn_eq hperm_j husj φ, hlps_jp]
        have hfitR_p : TeleFitPA V ρ TVa
            (xs ++ [AnnotTerm.mkAppN
              (mp_p.base2.acval rl_p.ctor (Level.substFn φ cvj_p.levelParams usj)) ys]) restR := by
          change TeleFitPA V ρ TVa
            (xs ++ [AnnotTerm.mkAppN
              (mp_p.base2.acval r.ctor (Level.substFn φ cvj_p.levelParams usj)) ys]) restR
          rw [← hctor_leaf]; exact hfitR
        obtain ⟨heq_p, hwd_p⟩ := hmain_p cvj_p cnP_p cnF_p hfc_p0 usj ρ xs ys TVa TVja restR restC
          hxs hys husj_p hlev_p hparP_p hparN_p hidx hTVa_p hTVja_p hfitR_p hfitC
        refine ⟨?_, hwd_p⟩
        change interp V ρ
            (AnnotTerm.mkAppN (mp_r.base2.acval cv.name (Level.substFn φ lps us))
              (xs ++ [AnnotTerm.mkAppN
                (mp_r.base2.acval r.ctor (Level.substFn φ cvj.levelParams usj)) ys])) = _
        rw [hrec_leaf, hctor_leaf]
        exact heq_p
      | _ => exact nomatch htag_j

theorem ruleFactsS_of_ruleFacts {envSelf : Env .anon} {cval : TConstVal .anon}
    {cv : ConstantVal .anon} {mI rP : Nat} {rl : RecRule .anon}
    (h : RuleFacts envSelf cval cv mI rP rl) :
    RuleFactsS envSelf cv mI rP rl :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2⟩

/-! ## Rooted `CleanInstallStep` and `ModelExtStep` Combinators -/

/-- `CleanInstallStep` for any `InstallStep` whose newly prepended entries are either installed base
constants of `d` or `.aux` companions rooted at installed base constants of `d` (covering both
native structure projection tables and modeled recursor `.model` companions). -/
theorem CleanInstallStep.of_rootedList {env : Env .anon} {d : Declaration .anon}
    {new : List (ConstantInfo .anon)}
    (hstep : IxVM.Consistency.InstallStep env d ⟨new ++ env.consts⟩)
    (hbase₀ : ∀ ci₀ ∈ IxVM.Consistency.installs d, isBaseKey ci₀.name = true)
    (hfresh₀ : ∀ ci₀ ∈ IxVM.Consistency.installs d, env.find? ci₀.name = none)
    (hrooted : ∀ ci ∈ new,
      (∃ ci₀ ∈ IxVM.Consistency.installs d, ci.name = ci₀.name) ∨
      (∃ ci₀ ∈ IxVM.Consistency.installs d, ∃ t, ci.name = .aux ci₀.name t)) :
    CleanInstallStep env d ⟨new ++ env.consts⟩ where
  step := hstep
  auxSynced h := h.of_prepend fun ci hci => by
    obtain ⟨new', heq_env, _, _, hcov, _⟩ := hstep
    rcases hrooted ci hci with ⟨ci₀, hm₀, hnm⟩ | ⟨ci₀, hm₀, t, hnm⟩
    · obtain ⟨c', hc', hs'⟩ := hcov ci₀ hm₀
      rw [hnm, base_of_isBaseKey (hbase₀ ci₀ hm₀), ← hs'.name_eq, heq_env]
      exact env_find?_isSome_of_mem_prefix hc'
    · obtain ⟨c', hc', hs'⟩ := hcov ci₀ hm₀
      have hb : (Key.aux ci₀.name t).base = ci₀.name := base_of_isBaseKey (hbase₀ ci₀ hm₀)
      rw [hnm, hb, ← hs'.name_eq, heq_env]
      exact env_find?_isSome_of_mem_prefix hc'
  noNewProj := by
    intro T hT
    have hne : ∀ ci ∈ new, ci.name ≠ projTableName T := by
      intro ci hci heq
      rcases hrooted ci hci with ⟨ci₀, hm₀, hnm⟩ | ⟨ci₀, hm₀, t, hnm⟩
      · have hb := hbase₀ ci₀ hm₀
        rw [← hnm, heq] at hb
        exact nomatch hb
      · rw [hnm] at heq
        injection heq with hroot _
        rw [← hroot, hfresh₀ ci₀ hm₀] at hT
        exact nomatch hT
    unfold Env.find?
    rw [List.find?_append,
      List.find?_eq_none.mpr (fun ci hci hbeq => hne ci hci (eq_of_beq hbeq)),
      Option.none_or]
  monoSome _ hk := env_find?_isSome_of_tail hk

/-- Environment extension step that preserves `DeclStoreInv` and `AuxRootSynced`, keeps old
projection tables untouched, and extends any `EnvModelM` (with `ThmValOk`) along `ModelExt`. -/
structure ModelExtStep (env env₂ : Env .anon) : Prop where
  ext : EnvExt env env₂
  noNewProj : NoNewProjForOld env env₂
  storeStep : DeclStoreInv env → DeclStoreInv env₂
  auxStep : AuxRootSynced env → AuxRootSynced env₂
  modelStep : ∀ (V : Type u) [Ix.Kernel.SetTheory V]
    (mp : EnvModelM V .verified env),
    ThmValOk mp → Ix.Kernel.EtaFamiliesClosed env →
    Ix.Kernel.EtaFamiliesClosed env₂ ∧
    ∃ mp₂ : EnvModelM V .verified env₂, ModelExt mp mp₂

theorem ModelExtStep.refl (env : Env .anon) : ModelExtStep.{u} env env where
  ext := EnvExt.refl env
  noNewProj := NoNewProjForOld.refl env
  storeStep := id
  auxStep := id
  modelStep _ _ mp _ hE := ⟨hE, mp, .refl⟩

theorem ModelExtStep.trans {e₁ e₂ e₃ : Env .anon}
    (h₁₂ : ModelExtStep.{u} e₁ e₂) (h₂₃ : ModelExtStep.{u} e₂ e₃) :
    ModelExtStep.{u} e₁ e₃ where
  ext := h₁₂.ext.trans h₂₃.ext
  noNewProj := h₁₂.noNewProj.trans h₂₃.noNewProj fun k hk => by
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hk
    rw [h₁₂.ext.find hci]; rfl
  storeStep hS := h₂₃.storeStep (h₁₂.storeStep hS)
  auxStep hA := h₂₃.auxStep (h₁₂.auxStep hA)
  modelStep V _ mp hT hE := by
    obtain ⟨hE₂, mp₂, hext₁⟩ := h₁₂.modelStep V mp hT hE
    obtain ⟨hE₃, mp₃, hext₂⟩ := h₂₃.modelStep V mp₂ (hT.of_ext hext₁) hE₂
    exact ⟨hE₃, mp₃, hext₁.trans hext₂⟩

theorem ModelExtStep.of_declRunJ {env env₂ : Env .anon} {d : Declaration .anon}
    (hclean : CleanInstallStep env d env₂)
    (hrun : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂) :
    ModelExtStep.{u} env env₂ where
  ext := Ix.Kernel.Model.declRunJ_envExt_routes hrun
  noNewProj := hclean.noNewProj
  storeStep hS := hS.step hrun
  auxStep := hclean.auxSynced
  modelStep _ _ mp hT hE :=
    Ix.Kernel.Model.declStep_preservesJ (fun _ _ => rfl) mp
      (Ix.Kernel.Model.judgeSound_rulesJ_of mp)
      (Ix.Kernel.Model.axiomBits_rulesJ env) hE
      (fun h => by
        rcases h with ⟨p₀, hdp, hN⟩ | hM | ⟨p₀, hdp, hN⟩ | hT'
        · exact Ix.Kernel.Model.nativeStep_rulesJ mp hT hE hdp hN
        · exact Ix.Kernel.Model.modeledStep_rulesJ mp hE hM
        · exact Ix.Kernel.Model.nativeNoRecStep_rulesJ mp hT hE hdp hN
        · exact Ix.Kernel.Model.twinStep_rulesJ mp hE hT')
      hrun

theorem ModelExtStep.toDeclInvM {env env₂ : Env .anon} (h : ModelExtStep.{u} env env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInvM V env → DeclInvM V env₂ := by
  intro V _ ⟨⟨⟨⟨mp, hT⟩, hE⟩, hS⟩, hA⟩
  obtain ⟨hE₂, mp₂, hext⟩ := h.modelStep V mp hT hE
  exact ⟨⟨⟨⟨mp₂, hT.of_ext hext⟩, hE₂⟩, h.storeStep hS⟩, h.auxStep hA⟩

/-! ## Lookup, `recRuleKOf`, `recRuleEtaOf`, and `realRuleFacts` Helpers -/

theorem find?_prepend_of_fresh {new : List (ConstantInfo .anon)} {E : Env .anon}
    (hfresh : ∀ c ∈ new, E.find? c.name = none) :
    ∀ {k : KKey} {x : ConstantInfo .anon},
      E.find? k = some x → Env.find? ⟨new ++ E.consts⟩ k = some x := by
  intro k x hx
  unfold Env.find? at hx ⊢
  rw [List.find?_append]
  cases hm : new.find? (fun c : ConstantInfo .anon => c.name == k) with
  | none => exact hx
  | some c =>
    have hc_mem : c ∈ new := List.mem_of_find?_eq_some hm
    have hbeq : (c.name == k) = true :=
      List.find?_some (p := fun x : ConstantInfo .anon => x.name == k) hm
    have hc_eq : c.name = k := eq_of_beq hbeq
    have h0 := hfresh c hc_mem
    rw [hc_eq] at h0
    unfold Env.find? at h0
    rw [h0] at hx
    exact nomatch hx

theorem find?_prepend_new_or_old {new : List (ConstantInfo .anon)} {E : Env .anon}
    {k : KKey} {x : ConstantInfo .anon}
    (hf : Env.find? ⟨new ++ E.consts⟩ k = some x) :
    (∃ c ∈ new, c = x ∧ c.name = k) ∨ E.find? k = some x := by
  unfold Env.find? at hf
  rw [List.find?_append] at hf
  cases hm : new.find? (fun c : ConstantInfo .anon => c.name == k) with
  | none =>
    rw [hm, Option.none_or] at hf
    exact Or.inr hf
  | some c =>
    rw [hm, Option.some_or] at hf
    obtain rfl := Option.some.inj hf
    have hbeq : (c.name == k) = true :=
      List.find?_some (p := fun y : ConstantInfo .anon => y.name == k) hm
    exact Or.inl ⟨c, List.mem_of_find?_eq_some hm, rfl, eq_of_beq hbeq⟩

theorem recRuleKOf_prepend_nonInd {new : List (ConstantInfo .anon)} {E : Env .anon}
    (hfresh : ∀ c ∈ new, E.find? c.name = none)
    (hni : ∀ c ∈ new, Ix.Kernel.Model.NotInd c)
    {ctor : KKey} {cvj : ConstantVal .anon} {a b : Nat}
    (hc : E.find? ctor = some (.ctorInfo cvj a b)) :
    recRuleKOf E.find? ctor = recRuleKOf (Env.find? ⟨new ++ E.consts⟩) ctor := by
  refine Ix.Kernel.Model.recRuleKOf_ext (find?_prepend_of_fresh hfresh) hc fun T _ _ => Or.inr ?_
  intro x hg hf
  rcases find?_prepend_new_or_old hg with ⟨c, hc_mem, rfl, -⟩ | hold
  · exact hni c hc_mem
  · rw [hold] at hf; exact nomatch hf

theorem recRuleEtaOf_prepend_nonInd {new : List (ConstantInfo .anon)} {E : Env .anon}
    (hfresh : ∀ c ∈ new, E.find? c.name = none)
    (hni : ∀ c ∈ new, Ix.Kernel.Model.NotInd c)
    {n ctor : KKey} {cvj : ConstantVal .anon} {a b : Nat}
    (hc : E.find? ctor = some (.ctorInfo cvj a b)) :
    recRuleEtaOf E.find? n ctor = recRuleEtaOf (Env.find? ⟨new ++ E.consts⟩) n ctor := by
  refine Ix.Kernel.Model.recRuleEtaOf_ext (find?_prepend_of_fresh hfresh) hc fun T _ _ => Or.inr ?_
  intro x hg hf
  rcases find?_prepend_new_or_old hg with ⟨c, hc_mem, rfl, -⟩ | hold
  · exact hni c hc_mem
  · rw [hold] at hf; exact nomatch hf

private theorem stripPis_body_wf_local {env : Env .anon} {ps : List LevelParam}
    (k d : Nat) {e : KExpr} {bs : List (KExpr × BinderMeta)} {body : KExpr}
    (h : e.stripPis k = some (bs, body))
    (hf : e.hasFvar = false)
    (hb : e.looseBVarsBounded d = true)
    (hcr : e.constsResolve env = true)
    (hlps : e.allLevelParamsDefined ps = true) :
    body.hasFvar = false ∧
    body.looseBVarsBounded (d + k) = true ∧
    body.constsResolve env = true ∧
    body.allLevelParamsDefined ps = true := by
  induction k generalizing d e bs body with
  | zero =>
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    simpa using ⟨hf, hb, hcr, hlps⟩
  | succ k ih =>
    cases e with
    | forallE ty b _ =>
      simp only [Expr.stripPis] at h
      cases hsb : b.stripPis k with
      | none => rw [hsb] at h; exact nomatch h
      | some p =>
        rw [hsb] at h
        obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
        simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
        simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hlps
        have hrec := ih (d + 1) hsb hf.2 hb.2 hcr.2 hlps.1.2
        rwa [show d + 1 + k = d + (k + 1) by omega] at hrec
    | _ => exact nomatch h

private theorem app_spine_wf_local {env : Env .anon} {ps : List LevelParam} {d : Nat} :
    ∀ (e : KExpr),
      e.hasFvar = false →
      e.looseBVarsBounded d = true →
      e.constsResolve env = true →
      e.allLevelParamsDefined ps = true →
      e.getAppFn.allLevelParamsDefined ps = true ∧
      e.getAppFn.constsResolve env = true ∧
      ∀ a ∈ e.getAppArgs,
        a.hasFvar = false ∧
        a.looseBVarsBounded d = true ∧
        a.constsResolve env = true ∧
        a.allLevelParamsDefined ps = true := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro hf hb hcr hlps
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hlps
    obtain ⟨hfn_lp, hfn_cr, hargs⟩ := ihf hf.1 hb.1 hcr.1 hlps.1
    have hfn_eq : (Expr.app f a).getAppFn = f.getAppFn := rfl
    have hargs_eq : (Expr.app f a).getAppArgs = f.getAppArgs ++ [a] := rfl
    refine ⟨hfn_eq ▸ hfn_lp, hfn_eq ▸ hfn_cr, fun x hx => ?_⟩
    rw [hargs_eq] at hx
    rcases List.mem_append.mp hx with hxf | hxa
    · exact hargs x hxf
    · rw [List.mem_singleton.mp hxa]
      exact ⟨hf.2, hb.2, hcr.2, hlps.2⟩
  | bvar _ | fvar _ _ | sort _ | const _ _ | lam _ _ _ | forallE _ _ _ | letE _ _ _ _
  | lit _ | proj _ _ _ =>
    intro _ _ hcr hlps
    exact ⟨hlps, hcr, fun _ hm => nomatch hm⟩

/-- Assemble `RuleFacts` on `(envSelf_r, mpSelf_r)` for one real checked rule from its unpositionalized
`RecRuleLaw` together with the recursor major-premise pins and constructor arity/telescope facts. -/
theorem realRuleFacts {V : Type u} [Ix.Kernel.SetTheory V]
    {envM_r envSelf_r : Env .anon}
    (mpSelf_r : EnvModelM V .verified envSelf_r)
    {new_recs : List (ConstantInfo .anon)}
    (hself_eq : envSelf_r = ⟨new_recs ++ envM_r.consts⟩)
    (hfresh_recs : ∀ c ∈ new_recs, envM_r.find? c.name = none)
    (hni_recs : ∀ c ∈ new_recs, Ix.Kernel.Model.NotInd c)
    {cv : ConstantVal .anon} {mI rP cnP_ind : Nat}
    {indKey : KKey} {lvls_lps : List KLevel} {pins_lps : List KExpr}
    {pre : List (KExpr × BinderMeta)} {dom body : KExpr} {bm : BinderMeta}
    {r : RecRule .anon} {cvj : ConstantVal .anon}
    (hrp_le : rP ≤ mI)
    (hty_wf :
      cv.type.hasFvar = false ∧
      cv.type.looseBVarsBounded 0 = true ∧
      cv.type.constsResolve envSelf_r = true ∧
      cv.type.allLevelParamsDefined cv.levelParams = true)
    (hstrip_ty : cv.type.stripPis mI = some (pre, .forallE dom body bm))
    (hdom_fn : dom.getAppFn = .const indKey lvls_lps)
    (hdom_len : dom.getAppArgs.length = cnP_ind + (mI - rP))
    (hdom_nli : ∀ p ∈ dom.getAppArgs.take cnP_ind, noLooseIn 0 (mI - rP) p = true)
    (hdom_drop : dom.getAppArgs.drop cnP_ind =
      (List.range (mI - rP)).map (fun i => Expr.bvar (mI - rP - 1 - i)))
    (hpins_def : pins_lps = (dom.getAppArgs.take cnP_ind).map (Expr.lowerBVars (mI - rP) 0))
    (hrhs_wf :
      r.rhs.hasFvar = false ∧
      r.rhs.allLevelParamsDefined cv.levelParams = true ∧
      r.rhs.constsResolve envSelf_r = true ∧
      r.rhs.looseBVarsBounded 0 = true)
    (hctor_M : envM_r.find? r.ctor = some (.ctorInfo cvj cnP_ind r.nfields))
    (hctor_strip : ∃ bsC0 cbody0 Dc usc,
      cvj.type.stripPis (cnP_ind + r.nfields) = some (bsC0, cbody0) ∧
      cbody0.getAppFn = .const Dc usc)
    (hlaw_r : ∀ φ : LevelParam → Nat,
      RecRuleLaw mpSelf_r.base2 φ cv.name cv mI rP
        (realCheckedRule envM_r.find? cv.name cnP_ind lvls_lps pins_lps r)) :
    RuleFacts envSelf_r mpSelf_r.base2.cvalE cv mI rP
      (realCheckedRule envM_r.find? cv.name cnP_ind lvls_lps pins_lps r) := by
  let rl_r := realCheckedRule envM_r.find? cv.name cnP_ind lvls_lps pins_lps r
  have hforall_wf := stripPis_body_wf_local mI 0 hstrip_ty
    hty_wf.1 hty_wf.2.1 hty_wf.2.2.1 hty_wf.2.2.2
  simp only [Expr.hasFvar, Bool.or_eq_false_iff, Expr.looseBVarsBounded,
    Expr.constsResolve, Expr.allLevelParamsDefined, Bool.and_eq_true] at hforall_wf
  obtain ⟨hfn_lp, _, hargs_wf⟩ := app_spine_wf_local dom
    hforall_wf.1.1 (by simpa using hforall_wf.2.1.1) hforall_wf.2.2.1.1 hforall_wf.2.2.2.1.1
  rw [hdom_fn] at hfn_lp
  have hlvls_def : ∀ l ∈ lvls_lps, l.allParamsDefined cv.levelParams = true :=
    List.all_eq_true.mp hfn_lp
  have hpins_len : pins_lps.length = cnP_ind := by
    rw [hpins_def, List.length_map, List.length_take, hdom_len]
    omega
  have hpins_wf : ∀ pin ∈ pins_lps,
      pin.hasFvar = false ∧
      pin.allLevelParamsDefined cv.levelParams = true ∧
      pin.constsResolve envSelf_r = true ∧
      pin.looseBVarsBounded rP = true := by
    intro pin hpin
    rw [hpins_def] at hpin
    obtain ⟨arg, harg_tk, rfl⟩ := List.mem_map.mp hpin
    obtain ⟨haf, hab, hacr, halp⟩ := hargs_wf arg (List.mem_of_mem_take harg_tk)
    have hnli : noLooseIn 0 (mI - rP) arg = true := hdom_nli arg harg_tk
    have hab' : arg.looseBVarsBounded (rP + 0 + (mI - rP)) = true := by
      rwa [show rP + 0 + (mI - rP) = mI by omega]
    exact ⟨by rw [hasFvar_lowerBVars, haf],
      by rw [allLevelParamsDefined_lowerBVars]; exact halp,
      by rw [constsResolve_lowerBVars]; exact hacr,
      looseBVarsBounded_lowerBVars (rp := rP) hnli hab'⟩
  have hdom_args_eq : dom.getAppArgs =
      pins_lps.map (Expr.liftLooseBVars (mI - rP) 0) ++
        (List.range (mI - rP)).map (fun i => Expr.bvar (mI - rP - 1 - i)) := by
    have htk : pins_lps.map (Expr.liftLooseBVars (mI - rP) 0) =
        dom.getAppArgs.take cnP_ind := by
      rw [hpins_def, List.map_map]
      conv => rhs; rw [← List.map_id (dom.getAppArgs.take cnP_ind)]
      apply List.map_congr_left
      intro p hp
      exact liftLooseBVars_lowerBVars_of_noLooseIn (hdom_nli p hp)
    rw [htk, ← hdom_drop, List.take_append_drop]
  have hctor_self : envSelf_r.find? r.ctor = some (.ctorInfo cvj cnP_ind r.nfields) := by
    rw [hself_eq]
    exact find?_prepend_of_fresh hfresh_recs hctor_M
  refine ⟨hrhs_wf.1, hrhs_wf.2.1, hrhs_wf.2.2.1, hrhs_wf.2.2.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro lvls pins hfn
    have hfr : rl_r.fire = .nested lvls_lps pins_lps := rfl
    rw [hfr] at hfn
    obtain ⟨rfl, rfl⟩ := RecRuleFire.nested.inj hfn
    exact ⟨hrp_le, hlvls_def, hpins_wf,
      ⟨pre, dom, body, bm, indKey, hstrip_ty, hdom_fn, hdom_args_eq⟩⟩
  · refine ⟨cvj, hctor_self, (fun hp => nomatch hp), (fun lvls pins hfn => ?_),
      (fun hfn => nomatch hfn), ?_⟩
    · have hfr : rl_r.fire = .nested lvls_lps pins_lps := rfl
      rw [hfr] at hfn
      obtain ⟨_, rfl⟩ := RecRuleFire.nested.inj hfn
      exact hpins_len
    · obtain ⟨bsC0, cbody0, Dc, usc, hsC, hh⟩ := hctor_strip
      exact Ix.Kernel.Expr.ctorTeleOk_of hsC hh
  · intro _
    refine ⟨hrp_le, fun φ => ?_⟩
    obtain ⟨Ra, hRa, -⟩ := (hlaw_r φ).2 (cv.levelParams.map .param) (List.length_map ..)
    have hinst_self : rl_r.rhs.instantiateLevelParams cv.levelParams (cv.levelParams.map .param) =
        rl_r.rhs := instantiateLevelParams_self cv.levelParams rl_r.rhs
    rw [hinst_self] at hRa
    exact ⟨Ra.erase, denoteMeta_erase mpSelf_r.base2.acval_erase 0 rl_r.rhs hRa⟩
  · intro hk
    have hk_eq : rl_r.k = recRuleKOf envM_r.find? r.ctor := rfl
    rw [hk_eq, recRuleKOf_prepend_nonInd hfresh_recs hni_recs hctor_M, ← hself_eq] at hk
    exact hk
  · intro he
    have he_eq : rl_r.eta = recRuleEtaOf envM_r.find? cv.name r.ctor := rfl
    rw [he_eq, recRuleEtaOf_prepend_nonInd hfresh_recs hni_recs hctor_M, ← hself_eq] at he
    exact he

/-! ## Positional Model Steps (`step_pos_nonrec`, `step_pos_rec_prov`) and Lockstep Folds -/

private theorem renameConsts_id_eq : ∀ e : KExpr, e.renameConsts id = e
  | .bvar _ | .sort _ | .const _ _ | .lit _ => rfl
  | .fvar i ty => congrArg (Expr.fvar i) (renameConsts_id_eq ty)
  | .app f a => by simp only [Expr.renameConsts, renameConsts_id_eq f, renameConsts_id_eq a]
  | .lam ty b m => by simp only [Expr.renameConsts, renameConsts_id_eq ty, renameConsts_id_eq b]
  | .forallE ty b m => by simp only [Expr.renameConsts, renameConsts_id_eq ty, renameConsts_id_eq b]
  | .letE ty v b m => by
    simp only [Expr.renameConsts, renameConsts_id_eq ty, renameConsts_id_eq v, renameConsts_id_eq b]
  | .proj s i e => congrArg (Expr.proj s i) (renameConsts_id_eq e)

/-- Fold-left environment prepend (`pushList cs E = ⟨cs.reverse ++ E.consts⟩`). -/
def pushList : List (ConstantInfo .anon) → Env .anon → Env .anon
  | [], E => E
  | c :: rest, E => pushList rest ⟨c :: E.consts⟩

theorem pushList_consts :
    ∀ (cs : List (ConstantInfo .anon)) (E : Env .anon),
      (pushList cs E).consts = cs.reverse ++ E.consts
  | [], E => rfl
  | c :: rest, E => by
    simp only [pushList, pushList_consts rest ⟨c :: E.consts⟩, List.reverse_cons,
      List.append_assoc, List.singleton_append]

theorem pushList_eq (cs : List (ConstantInfo .anon)) (E : Env .anon) :
    pushList cs E = ⟨cs.reverse ++ E.consts⟩ := by
  cases h : pushList cs E
  have hc := pushList_consts cs E
  rw [h] at hc
  exact congrArg Env.mk hc

/-- Prefix invariant linking every constant already stored in `E_r` to its `f_id` image in `E_p`. -/
def PosPrefixLinked {V : Type u} [Ix.Kernel.SetTheory V]
    (E_r E_p : Env .anon) (mp_p : EnvModelM V .verified E_p)
    (f_id : KKey → KKey) : Prop :=
  ∀ k : KKey, (E_r.find? k).isSome = true →
    (E_p.find? k).map (·.toConstantVal.levelParams) =
      (E_p.find? (f_id k)).map (·.toConstantVal.levelParams) ∧
    mp_p.base2.acval k = mp_p.base2.acval (f_id k)

theorem PosPrefixLinked.of_base {V : Type u} [Ix.Kernel.SetTheory V]
    {env E_p : Env .anon} (mp_p : EnvModelM V .verified E_p)
    {blockNames : List KKey} {f_id : KKey → KKey}
    (hf_out : ∀ k, blockNames.contains k = false → f_id k = k)
    (hbn_fresh : ∀ k, blockNames.contains k = true → env.find? k = none) :
    PosPrefixLinked env E_p mp_p f_id := by
  intro k hk
  cases hc : blockNames.contains k with
  | false =>
    rw [hf_out k hc]
    exact ⟨rfl, rfl⟩
  | true =>
    rw [hbn_fresh k hc] at hk
    exact nomatch hk

theorem PosPrefixLinked.step_pair {V : Type u} [Ix.Kernel.SetTheory V]
    {E_r E_p : Env .anon} {mp_r : EnvModelM V .verified E_r}
    {mp_p : EnvModelM V .verified E_p}
    {c_r c_p : ConstantInfo .anon}
    {mp_p' : EnvModelM V .verified ⟨c_p :: E_p.consts⟩}
    {f_id : KKey → KKey} {cvm_f : ConstantVal .anon} {mval_f : KExpr} {hint_f : ReducibilityHint}
    (hlink : PosPrefixLinked E_r E_p mp_p f_id)
    (hagree : UnposAgree mp_r.base2.acval E_r mp_p.base2.acval E_p)
    (hname_p : c_p.name = c_r.name)
    (hfresh_p : E_p.find? c_r.name = none)
    (hlps_p : c_p.toConstantVal.levelParams = List.range c_r.toConstantVal.levelParams.length)
    (hsrc_f : E_p.find? (f_id c_r.name) = some (.defnInfo cvm_f mval_f hint_f))
    (hlps_f : cvm_f.levelParams = List.range c_r.toConstantVal.levelParams.length)
    (hac_p' : mp_p'.base2.acval =
      acvalWith mp_p.base2.acval c_r.name (mp_p.base2.acval (f_id c_r.name))) :
    PosPrefixLinked ⟨c_r :: E_r.consts⟩ ⟨c_p :: E_p.consts⟩ mp_p' f_id := by
  intro k hk
  rw [Env.find?_cons] at hk
  by_cases heq : c_r.name = k
  · subst heq
    have hne_self : c_p.name ≠ f_id c_r.name := by
      intro h
      rw [hname_p] at h
      rw [← h, hfresh_p] at hsrc_f
      exact nomatch hsrc_f
    have hne_ac : f_id c_r.name ≠ c_r.name := fun h => hne_self (hname_p.trans h.symm)
    have hf_self : (⟨c_p :: E_p.consts⟩ : Env .anon).find? c_r.name = some c_p := by
      rw [← hname_p]; exact Env.find?_cons_self c_p E_p
    have hf_img : (⟨c_p :: E_p.consts⟩ : Env .anon).find? (f_id c_r.name) =
        some (.defnInfo cvm_f mval_f hint_f) := by
      rw [EnvExt.find?_cons_ne hne_self]; exact hsrc_f
    refine ⟨?_, ?_⟩
    · rw [hf_self, hf_img, Option.map_some, Option.map_some]
      exact congrArg some (hlps_p.trans hlps_f.symm)
    · rw [hac_p', acvalWith_self, acvalWith_ne hne_ac]
  · rw [ite_eq_right heq] at hk
    obtain ⟨hl_old, hac_old⟩ := hlink k hk
    obtain ⟨ci_r, hci_r⟩ := Option.isSome_iff_exists.mp hk
    obtain ⟨ci_p, hci_p, -⟩ := hagree.entry k ci_r hci_r
    have hs_fk : (E_p.find? (f_id k)).isSome = true := by
      rw [hci_p, Option.map_some] at hl_old
      cases hfk : E_p.find? (f_id k) with
      | none => rw [hfk] at hl_old; exact nomatch hl_old
      | some _ => rfl
    have hne_fk : c_p.name ≠ f_id k := by
      intro h
      rw [hname_p] at h
      rw [← h, hfresh_p] at hs_fk
      exact nomatch hs_fk
    have hne_cp : c_p.name ≠ k := hname_p ▸ heq
    have hne_k : k ≠ c_r.name := fun h => heq h.symm
    have hne_fk' : f_id k ≠ c_r.name := fun h => hne_fk (hname_p.trans h.symm)
    refine ⟨?_, ?_⟩
    · rw [EnvExt.find?_cons_ne hne_cp, EnvExt.find?_cons_ne hne_fk]
      exact hl_old
    · rw [hac_p', acvalWith_ne hne_k, acvalWith_ne hne_fk']
      exact hac_old

/-- Step `(E_p, mp_p)` by one positional non-recursor `posCI c_r` using advice model `f_id c_r.name`. -/
theorem step_pos_nonrec {V : Type u} [Ix.Kernel.SetTheory V]
    {E_r E_p : Env .anon} {c_r : ConstantInfo .anon}
    (mp_p : EnvModelM V .verified E_p)
    (hEta_p : Ix.Kernel.EtaFamiliesClosed E_p)
    {f_id : KKey → KKey}
    (hlink : PosPrefixLinked E_r E_p mp_p f_id)
    {cvm_f : ConstantVal .anon} {mval_f : KExpr} {hint_f : ReducibilityHint}
    (hbase : isBaseKey c_r.name = true)
    (hfresh_p : E_p.find? (posCI c_r).name = none)
    (hnres : Ix.Kernel.reservedBasisNames.contains c_r.name = false)
    (hknd : (∃ cv, c_r = .indInfo cv {}) ∨ ∃ cv nP nF, c_r = .ctorInfo cv nP nF)
    (htr_r : c_r.toConstantVal.type.constsResolve E_r = true)
    (hsrc_f : E_p.find? (f_id c_r.name) = some (.defnInfo cvm_f mval_f hint_f))
    (hlps_f : cvm_f.levelParams = List.range c_r.toConstantVal.levelParams.length)
    (hty_f : cvm_f.type = (posCI c_r).toConstantVal.type.renameConsts f_id) :
    let c_p := posCI c_r
    let A_p := mp_p.base2.acval (f_id c_r.name)
    ∃ mp_p' : EnvModelM V .verified ⟨c_p :: E_p.consts⟩,
      mp_p'.base2.acval = acvalWith mp_p.base2.acval c_p.name A_p ∧
      Ix.Kernel.EtaFamiliesClosed ⟨c_p :: E_p.consts⟩ ∧
      ModelExt mp_p mp_p' := by
  let c_p := posCI c_r
  let A_p := mp_p.base2.acval (f_id c_r.name)
  have hname_p : c_p.name = c_r.name := by
    rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
  have hlps_p : c_p.toConstantVal.levelParams = List.range c_r.toConstantVal.levelParams.length := by
    rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
  have hty_p_eq : c_p.toConstantVal.type =
      posOf c_r.toConstantVal.levelParams c_r.toConstantVal.type := by
    rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
  have hnres_p : Ix.Kernel.reservedBasisNames.contains c_p.name = false := hname_p ▸ hnres
  have hshape_p : c_p.name.isProjFnShape = false := hname_p ▸ isProjFnShape_of_isBaseKey hbase
  have hmem_f : ConstantInfo.defnInfo cvm_f mval_f hint_f ∈ E_p.consts :=
    Ix.Kernel.Semantics.Env.find?_mem hsrc_f
  have hnm_f : cvm_f.name = f_id c_r.name := Ix.Kernel.Semantics.Env.find?_name hsrc_f
  have hwf_f := mp_p.base2.wf _ hmem_f
  have hcr_pos_r : c_p.toConstantVal.type.constsResolve E_r = true := by
    rw [hty_p_eq, constsResolve_posOf]; exact htr_r
  have hnames_ty : ConstNamesIn (fun k => (E_r.find? k).isSome = true) c_p.toConstantVal.type :=
    constNamesIn_of_constsResolve hcr_pos_r
  have P_lps : ∀ k, (E_r.find? k).isSome = true →
      (E_p.find? (id k)).map (·.toConstantVal.levelParams) =
      (E_p.find? (f_id k)).map (·.toConstantVal.levelParams) :=
    fun k hk => (hlink k hk).1
  have P_some : ∀ k, (E_r.find? k).isSome = true →
      (E_p.find? (id k)).isSome = (E_p.find? (f_id k)).isSome := by
    intro k hk
    have hl := P_lps k hk
    cases hf1 : E_p.find? (id k) <;> cases hf2 : E_p.find? (f_id k) <;>
      rw [hf1, hf2] at hl <;> first | rfl | exact nomatch hl
  have P_ac : ∀ k, (E_r.find? k).isSome = true →
      mp_p.base2.acval (id k) = mp_p.base2.acval (f_id k) :=
    fun k hk => (hlink k hk).2
  have htf_p : c_p.toConstantVal.type.hasFvar = false := by
    have h1 : (c_p.toConstantVal.type.renameConsts f_id).hasFvar = false := hty_f ▸ hwf_f.1
    rwa [hasFvar_renameConsts] at h1
  have htp_p : c_p.toConstantVal.type.allLevelParamsDefined c_p.toConstantVal.levelParams = true := by
    have h1 : (c_p.toConstantVal.type.renameConsts f_id).allLevelParamsDefined
        c_p.toConstantVal.levelParams = true := by
      rw [hlps_p, ← hlps_f, ← hty_f]; exact hwf_f.2.1
    rwa [allLevelParamsDefined_renameConsts] at h1
  have htr_p : c_p.toConstantVal.type.constsResolve E_p = true := by
    rw [← renameConsts_id_eq c_p.toConstantVal.type,
      constsResolve_renameConsts_congr P_some hnames_ty, ← hty_f]
    exact hwf_f.2.2.1
  have htb_p : c_p.toConstantVal.type.looseBVarsBounded 0 = true := by
    have h1 : (c_p.toConstantVal.type.renameConsts f_id).looseBVarsBounded 0 = true :=
      hty_f ▸ hwf_f.2.2.2.1
    rwa [looseBVarsBounded_renameConsts] at h1
  have hcbT : ConstsBound E_p c_p.toConstantVal.type := constsBound_of_constsResolve _ htr_p
  have hcomp : ∀ (ψ : LevelParam → Nat) {ea : AnnotTerm},
      denoteMeta mp_p.base2.acval E_p ψ 0 c_p.toConstantVal.type = some ea →
      denoteMeta (acvalWith mp_p.base2.acval c_p.name A_p) ⟨c_p :: E_p.consts⟩
        ψ 0 c_p.toConstantVal.type = some ea :=
    fun ψ {ea} h =>
      denoteMeta_cons_fresh_mono (c₀ := c_p) (A := A_p) hfresh_p
        (fun _ h => by rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch h)
        ψ 0 _ hcbT h
  have hty_den_eq : ∀ ψ : LevelParam → Nat,
      denoteMeta mp_p.base2.acval E_p ψ 0 c_p.toConstantVal.type =
      denoteMeta mp_p.base2.acval E_p ψ 0 cvm_f.type := by
    intro ψ
    conv => lhs; rw [← renameConsts_id_eq c_p.toConstantVal.type]
    rw [hty_f]
    exact denoteMeta_renameConsts_congr P_lps P_ac c_p.toConstantVal.type 0 hnames_ty
  have hwf_cp : Ix.Kernel.ConstWF ⟨c_p :: E_p.consts⟩ c_p := by
    refine Ix.Kernel.structConstWF htf_p htp_p (Ix.Kernel.Expr.constsResolve_mono htr_p) htb_p
      (fun _ _ _ heq => by rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch heq)
      (fun _ _ _ _ heq => by rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch heq)
      (fun _ heq => by rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch heq)
      (fun _ caps heq => by
        rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩
        · obtain ⟨_, rfl⟩ := ConstantInfo.indInfo.inj heq
          exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
        · exact nomatch heq)
  have hh : ConsHead E_p c_p A_p :=
    ConsHead.ofFresh (Ix.Kernel.EnvWF.cons mp_p.base2.wf hwf_cp)
      (fun ψ => mp_p.base2.cval_closedL (f_id c_r.name) ψ) hnres_p
      (fun _ heq => by rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch heq)
      (fun _ _ _ _ heq => by rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch heq)
  have hknd_p : (∃ cv caps, c_p = .indInfo cv caps) ∨ ∃ cv nP nF, c_p = .ctorInfo cv nP nF := by
    rcases hknd with ⟨cv, rfl⟩ | ⟨cv, nP, nF, rfl⟩
    · exact Or.inl ⟨posCV cv, {}, rfl⟩
    · exact Or.inr ⟨posCV cv, nP, nF, rfl⟩
  have hstep : ∃ mp_p' : EnvModelM V .verified ⟨c_p :: E_p.consts⟩,
      mp_p'.base2.acval = acvalWith mp_p.base2.acval c_p.name A_p := by
    refine declStep_preserves_of_ind_member_cons mp_p hfresh_p hnres_p hknd_p hh
      (fun ψ k => mp_p.base2.acval_closed (f_id c_r.name) ψ k)
      (fun ψ₁ ψ₂ hp => mp_p.base2.acval_params (f_id c_r.name) _ hsrc_f ψ₁ ψ₂
        (hlps_f ▸ hlps_p ▸ hp))
      (fun ψ ρ => mp_p.base2.acval_wellDenoted (f_id c_r.name) ψ ρ)
      (fun ψ ρ => mp_p.acval_validV (f_id c_r.name) ψ ρ)
      ?_ ?_ ?_ ?_
    · intro ψ
      obtain ⟨ta, hta⟩ := mp_p.type_reads _ hmem_f ψ
      dsimp only [ConstantInfo.toConstantVal] at hta
      rw [← hty_den_eq ψ] at hta
      exact ⟨ta, hcomp ψ hta⟩
    · intro ψ ta hta ρ
      obtain ⟨ta₀, hta₀⟩ := mp_p.type_reads _ hmem_f ψ
      have hta₀' : denoteMeta mp_p.base2.acval E_p ψ 0 c_p.toConstantVal.type = some ta₀ := by
        rw [hty_den_eq ψ]; exact hta₀
      have htaEq : ta = ta₀ := Option.some.inj (hta.symm.trans (hcomp ψ hta₀'))
      rw [htaEq]
      exact mp_p.type_wellDenotedV _ hmem_f ψ ta₀ hta₀ ρ
    · intro ψ ta hta ρ
      obtain ⟨ta₀, hta₀⟩ := mp_p.type_reads _ hmem_f ψ
      have hta₀' : denoteMeta mp_p.base2.acval E_p ψ 0 c_p.toConstantVal.type = some ta₀ := by
        rw [hty_den_eq ψ]; exact hta₀
      have htaEq : ta = ta₀ := Option.some.inj (hta.symm.trans (hcomp ψ hta₀'))
      have hm := mp_p.mem_type _ hmem_f ψ ta₀ hta₀ ρ
      change interp V ρ (mp_p.base2.acval cvm_f.name ψ) ∈ˢ interp V ρ ta₀ at hm
      rw [hnm_f] at hm
      rwa [htaEq]
    · intro m₂ hm₂
      refine capsOk_cons_native mp_p (T := c_p.name) hfresh_p hh.projTower hshape_p
        (by
          rcases hknd with ⟨cv, rfl⟩ | ⟨cv, nP, nF, rfl⟩
          · exact Or.inl ⟨posCV cv, {}, rfl, rfl⟩
          · exact Or.inr fun _ _ h => nomatch h)
        (fun T' cvT' caps' hfT' _ hres' hcape' => hEta_p T' cvT' caps' hfT' hcape' hres')
        m₂ hm₂ ?_
      intro cvT caps hfT _
      rw [Env.find?_cons, ite_eq_left rfl] at hfT
      rcases hknd with ⟨cv, rfl⟩ | ⟨cv, nP, nF, rfl⟩
      · obtain ⟨_, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hfT)
        exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
      · exact nomatch hfT
  obtain ⟨mp_p', hac_p'⟩ := hstep
  have hEta_p' : Ix.Kernel.EtaFamiliesClosed ⟨c_p :: E_p.consts⟩ := by
    rcases hknd with ⟨cv, rfl⟩ | ⟨cv, nP, nF, rfl⟩
    · exact (hEta_p.except cv.name).cons hfresh_p (fun _ caps heq he => by
        obtain ⟨_, rfl⟩ := ConstantInfo.indInfo.inj heq
        exact nomatch he) |>.closed fun _ caps hf he _ => by
          have hf0 := Env.find?_cons_self c_p E_p
          dsimp only [c_p, posCI, posCV, ConstantInfo.name, ConstantInfo.toConstantVal] at hf0 hf
          rw [hf0] at hf
          obtain ⟨_, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hf)
          exact nomatch he
    · exact Ix.Kernel.EtaFamiliesClosed.cons_nonind hEta_p hfresh_p fun _ _ h => nomatch h
  have hext_p : ModelExt mp_p mp_p' :=
    ModelExt.step .refl hfresh_p
      (fun _ _ _ => ConsCrossAt.ofNtc
        (fun _ heq => by rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch heq))
      (fun _ _ heq => by rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact nomatch heq)
      hac_p'
  exact ⟨mp_p', hac_p', hEta_p', hext_p⟩

/-- Step `(E_p, mp_p)` by one positional provisional recursor `.recInfo (posCV cv) mI rP []`. -/
theorem step_pos_rec_prov {V : Type u} [Ix.Kernel.SetTheory V]
    {E_r E_p : Env .anon} {cv : ConstantVal .anon} {mI rP : Nat}
    (mp_p : EnvModelM V .verified E_p)
    (hEta_p : Ix.Kernel.EtaFamiliesClosed E_p)
    {f_id : KKey → KKey}
    (hlink : PosPrefixLinked E_r E_p mp_p f_id)
    {cvm_f : ConstantVal .anon} {mval_f : KExpr} {hint_f : ReducibilityHint}
    (hbase : isBaseKey cv.name = true)
    (hfresh_p : E_p.find? cv.name = none)
    (hnres : Ix.Kernel.reservedBasisNames.contains cv.name = false)
    (htr_r : cv.type.constsResolve E_r = true)
    (hsrc_f : E_p.find? (f_id cv.name) = some (.defnInfo cvm_f mval_f hint_f))
    (hlps_f : cvm_f.levelParams = List.range cv.levelParams.length)
    (hty_f : cvm_f.type = (posOf cv.levelParams cv.type).renameConsts f_id) :
    let c_p : ConstantInfo .anon := .recInfo (posCV cv) mI rP []
    let A_p := mp_p.base2.acval (f_id cv.name)
    ∃ mp_p' : EnvModelM V .verified ⟨c_p :: E_p.consts⟩,
      mp_p'.base2.acval = acvalWith mp_p.base2.acval cv.name A_p ∧
      Ix.Kernel.EtaFamiliesClosed ⟨c_p :: E_p.consts⟩ ∧
      ModelExt mp_p mp_p' := by
  let c_p : ConstantInfo .anon := .recInfo (posCV cv) mI rP []
  let A_p := mp_p.base2.acval (f_id cv.name)
  have hshape_p : cv.name.isProjFnShape = false := isProjFnShape_of_isBaseKey hbase
  have hmem_f : ConstantInfo.defnInfo cvm_f mval_f hint_f ∈ E_p.consts :=
    Ix.Kernel.Semantics.Env.find?_mem hsrc_f
  have hnm_f : cvm_f.name = f_id cv.name := Ix.Kernel.Semantics.Env.find?_name hsrc_f
  have hwf_f := mp_p.base2.wf _ hmem_f
  have hcr_pos_r : (posOf cv.levelParams cv.type).constsResolve E_r = true := by
    rw [constsResolve_posOf]; exact htr_r
  have hnames_ty : ConstNamesIn (fun k => (E_r.find? k).isSome = true)
      (posOf cv.levelParams cv.type) :=
    constNamesIn_of_constsResolve hcr_pos_r
  have P_lps : ∀ k, (E_r.find? k).isSome = true →
      (E_p.find? (id k)).map (·.toConstantVal.levelParams) =
      (E_p.find? (f_id k)).map (·.toConstantVal.levelParams) :=
    fun k hk => (hlink k hk).1
  have P_some : ∀ k, (E_r.find? k).isSome = true →
      (E_p.find? (id k)).isSome = (E_p.find? (f_id k)).isSome := by
    intro k hk
    have hl := P_lps k hk
    cases hf1 : E_p.find? (id k) <;> cases hf2 : E_p.find? (f_id k) <;>
      rw [hf1, hf2] at hl <;> first | rfl | exact nomatch hl
  have P_ac : ∀ k, (E_r.find? k).isSome = true →
      mp_p.base2.acval (id k) = mp_p.base2.acval (f_id k) :=
    fun k hk => (hlink k hk).2
  have htf_p : (posOf cv.levelParams cv.type).hasFvar = false := by
    have h1 : ((posOf cv.levelParams cv.type).renameConsts f_id).hasFvar = false :=
      hty_f ▸ hwf_f.1
    rwa [hasFvar_renameConsts] at h1
  have htp_p : (posOf cv.levelParams cv.type).allLevelParamsDefined
      (List.range cv.levelParams.length) = true := by
    have h1 : ((posOf cv.levelParams cv.type).renameConsts f_id).allLevelParamsDefined
        (List.range cv.levelParams.length) = true :=
      hlps_f ▸ hty_f ▸ hwf_f.2.1
    rwa [allLevelParamsDefined_renameConsts] at h1
  have htr_p : (posOf cv.levelParams cv.type).constsResolve E_p = true := by
    rw [← renameConsts_id_eq (posOf cv.levelParams cv.type),
      constsResolve_renameConsts_congr P_some hnames_ty, ← hty_f]
    exact hwf_f.2.2.1
  have htb_p : (posOf cv.levelParams cv.type).looseBVarsBounded 0 = true := by
    have h1 : ((posOf cv.levelParams cv.type).renameConsts f_id).looseBVarsBounded 0 = true :=
      hty_f ▸ hwf_f.2.2.2.1
    rwa [looseBVarsBounded_renameConsts] at h1
  have hcbT : ConstsBound E_p (posOf cv.levelParams cv.type) :=
    constsBound_of_constsResolve _ htr_p
  have hcomp : ∀ (ψ : LevelParam → Nat) {ea : AnnotTerm},
      denoteMeta mp_p.base2.acval E_p ψ 0 (posOf cv.levelParams cv.type) = some ea →
      denoteMeta (acvalWith mp_p.base2.acval cv.name A_p) ⟨c_p :: E_p.consts⟩
        ψ 0 (posOf cv.levelParams cv.type) = some ea :=
    fun ψ {ea} h =>
      denoteMeta_cons_fresh_mono (c₀ := c_p) (A := A_p) hfresh_p
        (fun _ h => nomatch h) ψ 0 _ hcbT h
  have hty_den_eq : ∀ ψ : LevelParam → Nat,
      denoteMeta mp_p.base2.acval E_p ψ 0 (posOf cv.levelParams cv.type) =
      denoteMeta mp_p.base2.acval E_p ψ 0 cvm_f.type := by
    intro ψ
    conv => lhs; rw [← renameConsts_id_eq (posOf cv.levelParams cv.type)]
    rw [hty_f]
    exact denoteMeta_renameConsts_congr P_lps P_ac _ 0 hnames_ty
  have hwf_cp : Ix.Kernel.ConstWF ⟨c_p :: E_p.consts⟩ c_p :=
    Ix.Kernel.structConstWF htf_p htp_p (Ix.Kernel.Expr.constsResolve_mono htr_p) htb_p
      (fun _ _ _ heq => nomatch heq)
      (fun _ _ _ _ heq _ hr => by
        obtain ⟨_, _, _, rfl⟩ := ConstantInfo.recInfo.inj heq
        exact nomatch hr)
      (fun _ heq => nomatch heq)
      (fun _ _ heq => nomatch heq)
  have hh : ConsHead E_p c_p A_p :=
    ConsHead.ofFresh (Ix.Kernel.EnvWF.cons mp_p.base2.wf hwf_cp)
      (fun ψ => mp_p.base2.cval_closedL (f_id cv.name) ψ) hnres
      (fun _ heq => nomatch heq)
      (fun _ _ _ _ heq _ hr => by
        obtain ⟨_, _, _, rfl⟩ := ConstantInfo.recInfo.inj heq
        exact nomatch hr)
  have hfr_cp : E_p.find? c_p.name = none := hfresh_p
  have hstep : ∃ mp_p' : EnvModelM V .verified ⟨c_p :: E_p.consts⟩,
      mp_p'.base2.acval = acvalWith mp_p.base2.acval cv.name A_p := by
    refine declStep_preserves_of_ind_rec_cons mp_p (c₀ := c_p) (A := A_p) hfr_cp hnres
      ⟨posCV cv, mI, rP, [], rfl⟩ hh
      (fun ψ k => mp_p.base2.acval_closed (f_id cv.name) ψ k)
      (fun ψ₁ ψ₂ hp => mp_p.base2.acval_params (f_id cv.name) _ hsrc_f ψ₁ ψ₂ (hlps_f ▸ hp))
      (fun ψ ρ => mp_p.base2.acval_wellDenoted (f_id cv.name) ψ ρ)
      (fun ψ ρ => mp_p.acval_validV (f_id cv.name) ψ ρ)
      ?_ ?_ ?_
      (fun m₂ hm₂ => capsOk_cons_rec_nonproj mp_p (cvR := posCV cv) (mI := mI) (rP := rP)
        (rules := []) hfresh_p hshape_p m₂ hm₂)
      (fun m₂ hm₂ φ => recRules_cons_fresh mp_p (c₀ := c_p) (A := A_p) hfr_cp hh.projTower
        (fun _ _ _ _ heq => by
          obtain ⟨_, _, _, rfl⟩ := ConstantInfo.recInfo.inj heq
          rfl) m₂ hm₂ φ)
    · intro ψ
      obtain ⟨ta, hta⟩ := mp_p.type_reads _ hmem_f ψ
      dsimp only [ConstantInfo.toConstantVal] at hta
      rw [← hty_den_eq ψ] at hta
      exact ⟨ta, hcomp ψ hta⟩
    · intro ψ ta hta ρ
      obtain ⟨ta₀, hta₀⟩ := mp_p.type_reads _ hmem_f ψ
      have hta₀' : denoteMeta mp_p.base2.acval E_p ψ 0 (posOf cv.levelParams cv.type) = some ta₀ := by
        rw [hty_den_eq ψ]; exact hta₀
      have htaEq : ta = ta₀ := Option.some.inj (hta.symm.trans (hcomp ψ hta₀'))
      rw [htaEq]
      exact mp_p.type_wellDenotedV _ hmem_f ψ ta₀ hta₀ ρ
    · intro ψ ta hta ρ
      obtain ⟨ta₀, hta₀⟩ := mp_p.type_reads _ hmem_f ψ
      have hta₀' : denoteMeta mp_p.base2.acval E_p ψ 0 (posOf cv.levelParams cv.type) = some ta₀ := by
        rw [hty_den_eq ψ]; exact hta₀
      have htaEq : ta = ta₀ := Option.some.inj (hta.symm.trans (hcomp ψ hta₀'))
      have hm := mp_p.mem_type _ hmem_f ψ ta₀ hta₀ ρ
      change interp V ρ (mp_p.base2.acval cvm_f.name ψ) ∈ˢ interp V ρ ta₀ at hm
      rw [hnm_f] at hm
      rwa [htaEq]
  obtain ⟨mp_p', hac_p'⟩ := hstep
  have hEta_p' : Ix.Kernel.EtaFamiliesClosed ⟨c_p :: E_p.consts⟩ :=
    Ix.Kernel.EtaFamiliesClosed.cons_nonind hEta_p hfr_cp fun _ _ h => nomatch h
  have hext_p : ModelExt mp_p mp_p' :=
    ModelExt.step .refl hfr_cp
      (fun _ _ _ => ConsCrossAt.ofNtc (fun _ heq => nomatch heq))
      (fun _ _ heq => nomatch heq) hac_p'
  exact ⟨mp_p', hac_p', hEta_p', hext_p⟩

/-- Sequential well-formedness & advice-model matching for non-recursor members (`indInfo _ {}` and
`ctorInfo _ _ _`) along the real/positional prefixes. -/
def NonRecChain (E_r E_p₀ : Env .anon) (f_id : KKey → KKey) :
    List (ConstantInfo .anon) → Prop
  | [] => True
  | c_r :: rest =>
    E_r.find? c_r.name = none ∧
    E_p₀.find? c_r.name = none ∧
    isBaseKey c_r.name = true ∧
    Ix.Kernel.reservedBasisNames.contains c_r.name = false ∧
    c_r.toConstantVal.levelParams.Perm (List.range c_r.toConstantVal.levelParams.length) ∧
    ((∃ cv, c_r = .indInfo cv {}) ∨ ∃ cv nP nF, c_r = .ctorInfo cv nP nF) ∧
    c_r.toConstantVal.type.hasFvar = false ∧
    c_r.toConstantVal.type.allLevelParamsDefined c_r.toConstantVal.levelParams = true ∧
    c_r.toConstantVal.type.constsResolve E_r = true ∧
    c_r.toConstantVal.type.looseBVarsBounded 0 = true ∧
    (∃ cvm_f mval_f hint_f,
      E_p₀.find? (f_id c_r.name) = some (.defnInfo cvm_f mval_f hint_f) ∧
      cvm_f.levelParams = List.range c_r.toConstantVal.levelParams.length ∧
      cvm_f.type = (posCI c_r).toConstantVal.type.renameConsts f_id) ∧
    NonRecChain ⟨c_r :: E_r.consts⟩ ⟨posCI c_r :: E_p₀.consts⟩ f_id rest

theorem declStoreInv_push_nonrecs :
    ∀ (nonrecs : List (ConstantInfo .anon)) {E_r E_p₀ : Env .anon} {f_id : KKey → KKey},
      DeclStoreInv E_r →
      NonRecChain E_r E_p₀ f_id nonrecs →
      DeclStoreInv (pushList nonrecs E_r)
  | [], _, _, _, hS, _ => hS
  | c_r :: rest, _, _, _, hS,
      ⟨hfr_r, _, hbase, _, _, hknd, htf, htp, htr, htb, _, hrest⟩ =>
    declStoreInv_push_nonrecs rest
      (hS.cons_nonrec hfr_r (fun T => ne_projTableName_of_isBaseKey hbase) hknd htf htp htr htb)
      hrest

/-- For any fresh base key `T`, its structure projection table `projTableName T` is also absent. -/
def FreshBaseProjTable (E : Env .anon) : Prop :=
  ∀ {T : KKey}, isBaseKey T = true → E.find? T = none → E.find? (projTableName T) = none

theorem FreshBaseProjTable.of_auxSynced {E : Env .anon} (h : AuxRootSynced E) :
    FreshBaseProjTable E :=
  fun hb hf => h.fresh_projTable hb hf

theorem FreshBaseProjTable.cons_base {E : Env .anon} {c : ConstantInfo .anon}
    (h : FreshBaseProjTable E) (hbase : isBaseKey c.name = true) :
    FreshBaseProjTable ⟨c :: E.consts⟩ := by
  intro T hbT hfT
  have hne_pt : c.name ≠ projTableName T := ne_projTableName_of_isBaseKey hbase
  have hne_T : c.name ≠ T := fun heq => by
    rw [← heq, Env.find?_cons_self] at hfT
    exact nomatch hfT
  rw [EnvExt.find?_cons_ne hne_T] at hfT
  rw [EnvExt.find?_cons_ne hne_pt]
  exact h hbT hfT

/-- Lockstep fold across `nonrecs` on `(E_r, mp_r)` and `(E_p, mp_p)`. -/
theorem lockstep_nonrecs {V : Type u} [Ix.Kernel.SetTheory V] {f_id : KKey → KKey} :
    ∀ (nonrecs : List (ConstantInfo .anon)) {E_r E_p : Env .anon}
      (mp_r : EnvModelM V .verified E_r) (mp_p : EnvModelM V .verified E_p),
      Ix.Kernel.EtaFamiliesClosed E_r →
      Ix.Kernel.EtaFamiliesClosed E_p →
      FreshBaseProjTable E_r →
      FreshBaseProjTable E_p →
      UnposAgree mp_r.base2.acval E_r mp_p.base2.acval E_p →
      PosPrefixLinked E_r E_p mp_p f_id →
      NonRecChain E_r E_p f_id nonrecs →
      ∃ (mp_r' : EnvModelM V .verified (pushList nonrecs E_r))
        (mp_p' : EnvModelM V .verified (pushList (nonrecs.map posCI) E_p)),
        Ix.Kernel.EtaFamiliesClosed (pushList nonrecs E_r) ∧
        Ix.Kernel.EtaFamiliesClosed (pushList (nonrecs.map posCI) E_p) ∧
        FreshBaseProjTable (pushList nonrecs E_r) ∧
        FreshBaseProjTable (pushList (nonrecs.map posCI) E_p) ∧
        ModelExt mp_r mp_r' ∧
        ModelExt mp_p mp_p' ∧
        UnposAgree mp_r'.base2.acval (pushList nonrecs E_r)
          mp_p'.base2.acval (pushList (nonrecs.map posCI) E_p) ∧
        PosPrefixLinked (pushList nonrecs E_r) (pushList (nonrecs.map posCI) E_p) mp_p' f_id
  | [], _, _, mp_r, mp_p, hEr, hEp, hAr, hAp, hagree, hlink, _ =>
    ⟨mp_r, mp_p, hEr, hEp, hAr, hAp, .refl, .refl, hagree, hlink⟩
  | c_r :: rest, E_r, E_p, mp_r, mp_p, hEr, hEp, hAr, hAp, hagree, hlink,
      ⟨hfr_r, hfr_p0, hbase, hnres, hperm, hknd, htf, htp, htr, htb,
       ⟨cvm_f, mval_f, hint_f, hsrc_f, hlps_f, hty_f⟩, hrest⟩ => by
    have hname_p : (posCI c_r).name = c_r.name := by
      rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
    have hlps_p : (posCI c_r).toConstantVal.levelParams =
        List.range c_r.toConstantVal.levelParams.length := by
      rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
    have hfr_p : E_p.find? (posCI c_r).name = none := hname_p ▸ hfr_p0
    obtain ⟨mp_p₁, hac_p₁, hEp₁, hext_p₁⟩ :=
      step_pos_nonrec mp_p hEp hlink hbase hfr_p hnres hknd htr hsrc_f hlps_f hty_f
    have hproj_self : E_p.find? (projTableName c_r.name) = E_r.find? (projTableName c_r.name) := by
      rw [hAp hbase hfr_p0, hAr hbase hfr_r]
    have hA_src : ∃ k_m cvm mval hint,
        E_p.find? k_m = some (.defnInfo cvm mval hint) ∧
        cvm.levelParams = List.range c_r.toConstantVal.levelParams.length ∧
        mp_p.base2.acval (f_id c_r.name) = mp_p.base2.acval k_m ∧
        (∀ ψ, Term.Closed ((mp_p.base2.acval (f_id c_r.name) ψ).erase)) ∧
        (∀ ψ k, (mp_p.base2.acval (f_id c_r.name) ψ).liftN 1 k =
          mp_p.base2.acval (f_id c_r.name) ψ) ∧
        (∀ ψ₁ ψ₂, (∀ i ∈ List.range c_r.toConstantVal.levelParams.length, ψ₁ i = ψ₂ i) →
          mp_p.base2.acval (f_id c_r.name) ψ₁ = mp_p.base2.acval (f_id c_r.name) ψ₂) ∧
        (∀ ψ ρ, WellDenoted V ρ (mp_p.base2.acval (f_id c_r.name) ψ)) ∧
        (∀ ψ ρ, AnnotValid V ρ (mp_p.base2.acval (f_id c_r.name) ψ)) :=
      ⟨f_id c_r.name, cvm_f, mval_f, hint_f, hsrc_f, hlps_f, rfl,
        fun ψ => mp_p.base2.cval_closedL _ ψ,
        fun ψ k => mp_p.base2.acval_closed _ ψ k,
        fun ψ₁ ψ₂ hp => mp_p.base2.acval_params _ _ hsrc_f ψ₁ ψ₂ (hlps_f ▸ hp),
        fun ψ ρ => mp_p.base2.acval_wellDenoted _ ψ ρ,
        fun ψ ρ => mp_p.acval_validV _ ψ ρ⟩
    obtain ⟨mp_r₁, hEr₁, hext_r₁, hagree₁⟩ :=
      step_nonrec_unpos mp_r mp_p₁ hagree hac_p₁ hA_src hEr hbase hfr_r hfr_p hnres hperm hknd
        htf htp htr htb hproj_self
    have hlink₁ : PosPrefixLinked ⟨c_r :: E_r.consts⟩ ⟨posCI c_r :: E_p.consts⟩ mp_p₁ f_id :=
      hlink.step_pair hagree hname_p hfr_p0 hlps_p hsrc_f hlps_f (hname_p ▸ hac_p₁)
    have hAr₁ : FreshBaseProjTable ⟨c_r :: E_r.consts⟩ := hAr.cons_base hbase
    have hAp₁ : FreshBaseProjTable ⟨posCI c_r :: E_p.consts⟩ :=
      hAp.cons_base (hname_p.symm ▸ hbase)
    obtain ⟨mp_r', mp_p', hEr', hEp', hAr', hAp', hext_r₂, hext_p₂, hagree', hlink'⟩ :=
      lockstep_nonrecs rest mp_r₁ mp_p₁ hEr₁ hEp₁ hAr₁ hAp₁ hagree₁ hlink₁ hrest
    exact ⟨mp_r', mp_p', hEr', hEp', hAr', hAp',
      hext_r₁.trans hext_r₂, hext_p₁.trans hext_p₂, hagree', hlink'⟩

/-- Per-recursor specification for a modeled inductive block. -/
structure RecInstallEntry where
  cv : ConstantVal .anon
  mI : Nat
  rP : Nat
  cnP_ind : Nat
  indKey : KKey
  lvls_lps : List KLevel
  pins_lps : List KExpr
  pre : List (KExpr × BinderMeta)
  dom : KExpr
  body : KExpr
  bm : BinderMeta
  rawRules : List (RecRule .anon)

def RecInstallEntry.prov_r (w : RecInstallEntry) : ConstantInfo .anon :=
  .recInfo w.cv w.mI w.rP []

def RecInstallEntry.prov_p (w : RecInstallEntry) : ConstantInfo .anon :=
  .recInfo (posCV w.cv) w.mI w.rP []

def RecInstallEntry.rules_r (find? : KKey → Option (ConstantInfo .anon))
    (w : RecInstallEntry) : List (RecRule .anon) :=
  w.rawRules.map (realCheckedRule find? w.cv.name w.cnP_ind w.lvls_lps w.pins_lps)

def RecInstallEntry.checked_r (find? : KKey → Option (ConstantInfo .anon))
    (w : RecInstallEntry) : ConstantInfo .anon :=
  .recInfo w.cv w.mI w.rP (w.rules_r find?)

/-- Sequential well-formedness & advice-model matching for provisional recursors. -/
def RecProvChain (E_r E_p₀ : Env .anon) (f_id : KKey → KKey) :
    List RecInstallEntry → Prop
  | [] => True
  | w :: rest =>
    E_r.find? w.cv.name = none ∧
    E_p₀.find? w.cv.name = none ∧
    isBaseKey w.cv.name = true ∧
    Ix.Kernel.reservedBasisNames.contains w.cv.name = false ∧
    w.cv.levelParams.Perm (List.range w.cv.levelParams.length) ∧
    w.cv.type.hasFvar = false ∧
    w.cv.type.allLevelParamsDefined w.cv.levelParams = true ∧
    w.cv.type.constsResolve E_r = true ∧
    w.cv.type.looseBVarsBounded 0 = true ∧
    (∃ cvm_f mval_f hint_f,
      E_p₀.find? (f_id w.cv.name) = some (.defnInfo cvm_f mval_f hint_f) ∧
      cvm_f.levelParams = List.range w.cv.levelParams.length ∧
      cvm_f.type = (posOf w.cv.levelParams w.cv.type).renameConsts f_id) ∧
    RecProvChain ⟨w.prov_r :: E_r.consts⟩ ⟨w.prov_p :: E_p₀.consts⟩ f_id rest

theorem declStoreInv_push_recs_prov :
    ∀ (recs : List RecInstallEntry) {E_r E_p₀ : Env .anon} {f_id : KKey → KKey},
      DeclStoreInv E_r →
      RecProvChain E_r E_p₀ f_id recs →
      DeclStoreInv (pushList (recs.map (·.prov_r)) E_r)
  | [], _, _, _, hS, _ => hS
  | w :: rest, _, _, _, hS,
      ⟨hfr_r, _, hbase, _, _, htf, htp, htr, htb, _, hrest⟩ =>
    declStoreInv_push_recs_prov rest
      (hS.cons_rec_prov hfr_r (fun T => ne_projTableName_of_isBaseKey hbase) htf htp htr htb)
      hrest

/-- Lockstep fold across provisional recursors `recs` on `(E_r, mp_r)` and `(E_p, mp_p)`. -/
theorem lockstep_recs_prov {V : Type u} [Ix.Kernel.SetTheory V] {f_id : KKey → KKey} :
    ∀ (recs : List RecInstallEntry) {E_r E_p : Env .anon}
      (mp_r : EnvModelM V .verified E_r) (mp_p : EnvModelM V .verified E_p),
      Ix.Kernel.EtaFamiliesClosed E_r →
      Ix.Kernel.EtaFamiliesClosed E_p →
      FreshBaseProjTable E_r →
      FreshBaseProjTable E_p →
      UnposAgree mp_r.base2.acval E_r mp_p.base2.acval E_p →
      PosPrefixLinked E_r E_p mp_p f_id →
      RecProvChain E_r E_p f_id recs →
      ∃ (mp_r' : EnvModelM V .verified (pushList (recs.map (·.prov_r)) E_r))
        (mp_p' : EnvModelM V .verified (pushList (recs.map (·.prov_p)) E_p)),
        Ix.Kernel.EtaFamiliesClosed (pushList (recs.map (·.prov_r)) E_r) ∧
        Ix.Kernel.EtaFamiliesClosed (pushList (recs.map (·.prov_p)) E_p) ∧
        ModelExt mp_r mp_r' ∧
        ModelExt mp_p mp_p' ∧
        UnposAgree mp_r'.base2.acval (pushList (recs.map (·.prov_r)) E_r)
          mp_p'.base2.acval (pushList (recs.map (·.prov_p)) E_p) ∧
        PosPrefixLinked (pushList (recs.map (·.prov_r)) E_r)
          (pushList (recs.map (·.prov_p)) E_p) mp_p' f_id
  | [], _, _, mp_r, mp_p, hEr, hEp, _, _, hagree, hlink, _ =>
    ⟨mp_r, mp_p, hEr, hEp, .refl, .refl, hagree, hlink⟩
  | w :: rest, E_r, E_p, mp_r, mp_p, hEr, hEp, hAr, hAp, hagree, hlink,
      ⟨hfr_r, hfr_p, hbase, hnres, hperm, htf, htp, htr, htb,
       ⟨cvm_f, mval_f, hint_f, hsrc_f, hlps_f, hty_f⟩, hrest⟩ => by
    obtain ⟨mp_p₁, hac_p₁, hEp₁, hext_p₁⟩ :=
      step_pos_rec_prov mp_p hEp hlink hbase hfr_p hnres htr hsrc_f hlps_f hty_f
    have hproj_self :
        E_p.find? (projTableName w.cv.name) = E_r.find? (projTableName w.cv.name) := by
      rw [hAp hbase hfr_p, hAr hbase hfr_r]
    have hA_src :
        (∀ ψ, Term.Closed ((mp_p.base2.acval (f_id w.cv.name) ψ).erase)) ∧
        (∀ ψ k, (mp_p.base2.acval (f_id w.cv.name) ψ).liftN 1 k =
          mp_p.base2.acval (f_id w.cv.name) ψ) ∧
        (∀ ψ₁ ψ₂, (∀ i ∈ List.range w.cv.levelParams.length, ψ₁ i = ψ₂ i) →
          mp_p.base2.acval (f_id w.cv.name) ψ₁ = mp_p.base2.acval (f_id w.cv.name) ψ₂) ∧
        (∀ ψ ρ, WellDenoted V ρ (mp_p.base2.acval (f_id w.cv.name) ψ)) ∧
        (∀ ψ ρ, AnnotValid V ρ (mp_p.base2.acval (f_id w.cv.name) ψ)) :=
      ⟨fun ψ => mp_p.base2.cval_closedL _ ψ,
        fun ψ k => mp_p.base2.acval_closed _ ψ k,
        fun ψ₁ ψ₂ hp => mp_p.base2.acval_params _ _ hsrc_f ψ₁ ψ₂ (hlps_f ▸ hp),
        fun ψ ρ => mp_p.base2.acval_wellDenoted _ ψ ρ,
        fun ψ ρ => mp_p.acval_validV _ ψ ρ⟩
    obtain ⟨mp_r₁, hEr₁, hext_r₁, hagree₁⟩ :=
      step_rec_prov_unpos mp_r mp_p₁ hagree hac_p₁ hA_src hEr hbase hfr_r hfr_p hnres hperm
        htf htp htr htb hproj_self
    have hlink₁ : PosPrefixLinked ⟨w.prov_r :: E_r.consts⟩ ⟨w.prov_p :: E_p.consts⟩ mp_p₁ f_id :=
      hlink.step_pair hagree rfl hfr_p rfl hsrc_f hlps_f hac_p₁
    have hAr₁ : FreshBaseProjTable ⟨w.prov_r :: E_r.consts⟩ := hAr.cons_base (c := w.prov_r) hbase
    have hAp₁ : FreshBaseProjTable ⟨w.prov_p :: E_p.consts⟩ := hAp.cons_base (c := w.prov_p) hbase
    obtain ⟨mp_r', mp_p', hEr', hEp', hext_r₂, hext_p₂, hagree', hlink'⟩ :=
      lockstep_recs_prov rest mp_r₁ mp_p₁ hEr₁ hEp₁ hAr₁ hAp₁ hagree₁ hlink₁ hrest
    exact ⟨mp_r', mp_p', hEr', hEp', hext_r₁.trans hext_r₂, hext_p₁.trans hext_p₂,
      hagree', hlink'⟩

theorem renameOk_of_posPrefixLinked {V : Type u} [Ix.Kernel.SetTheory V]
    {E_r E_p : Env .anon} {mp_r : EnvModelM V .verified E_r}
    {mp_p : EnvModelM V .verified E_p}
    {blockNames : List KKey} {f_id : KKey → KKey}
    (hf_out : ∀ n, blockNames.contains n = false → f_id n = n)
    (hall_r : ∀ n, blockNames.contains n = true → (E_r.find? n).isSome = true)
    (hagree : UnposAgree mp_r.base2.acval E_r mp_p.base2.acval E_p)
    (hlink : PosPrefixLinked E_r E_p mp_p f_id) :
    RenameOk mp_p.base2.acval E_p f_id := by
  refine ⟨?_, ?_, ?_⟩
  · intro n ciS hfS
    cases hc : blockNames.contains n with
    | false =>
      rw [hf_out n hc]
      exact ⟨ciS, hfS, rfl⟩
    | true =>
      have hl := (hlink n (hall_r n hc)).1
      rw [hfS, Option.map_some] at hl
      cases hff : E_p.find? (f_id n) with
      | none => rw [hff] at hl; exact nomatch hl
      | some ciF =>
        rw [hff, Option.map_some] at hl
        exact ⟨ciF, rfl, (Option.some.inj hl).symm⟩
  · intro n hfS
    cases hc : blockNames.contains n with
    | false =>
      rw [hf_out n hc]
      exact hfS
    | true =>
      obtain ⟨ci_r, hci_r⟩ := Option.isSome_iff_exists.mp (hall_r n hc)
      obtain ⟨_, hci_p, -⟩ := hagree.entry n ci_r hci_r
      rw [hfS] at hci_p
      exact nomatch hci_p
  · intro n ψ
    cases hc : blockNames.contains n with
    | false => rw [hf_out n hc]
    | true => exact congrFun (hlink n (hall_r n hc)).2.symm ψ

/-! ## Multi-Recursor `.iota` Theorem Installation, Phase 3 Swap, and Phase 4 Dummy `.model`s -/

/-- Install `.iota j` theorem copies across all recursors in `recs` onto `(E, mpE)`. -/
theorem installAllRecIotaThms {V : Type u} [Ix.Kernel.SetTheory V]
    {c_pub c_rhs c_adv : Ctx}
    {blockNames : List KKey} {f_id : KKey → KKey} {advSet : Bytes.Address → Prop} :
    ∀ (recs : List RecInstallEntry) {E : Env .anon}
      (mpE : EnvModelM V .verified E)
      (hEE : Ix.Kernel.EtaFamiliesClosed E)
      (hfind_adv : ∀ k ci, c_adv.env.find? k = some ci → E.find? k = some ci)
      (hnd : (recs.map (·.cv.name)).Nodup)
      (hfresh : ∀ w ∈ recs, ∀ j, E.find? (auxKey (auxKey w.cv.name .model) (.iota j)) = none)
      (hraws : ∀ w ∈ recs, RawIotaRulesVmRun c_pub c_rhs c_adv blockNames f_id advSet
        w.cv.name w.cv.levelParams w.cv.type w.mI w.rP w.lvls_lps w.pins_lps 0 w.rawRules),
      ∃ (E' : Env .anon) (mp' : EnvModelM V .verified E'),
        Ix.Kernel.EtaFamiliesClosed E' ∧
        EnvExt E E' ∧
        (∀ k, (E.find? k).isSome = true → mp'.base2.acval k = mpE.base2.acval k) ∧
        (∀ k, (∀ w ∈ recs, ∀ j, k ≠ auxKey (auxKey w.cv.name .model) (.iota j)) →
          E'.find? k = E.find? k) ∧
        (∀ w ∈ recs, IotaRulesReady E' c_pub c_rhs c_adv blockNames f_id advSet
          w.cv.name w.cv.levelParams w.cv.type w.mI w.rP w.lvls_lps w.pins_lps 0 w.rawRules)
  | [], E, mpE, hEE, _, _, _, _ =>
    ⟨E, mpE, hEE, EnvExt.refl E, fun _ _ => rfl, fun _ _ => rfl, fun _ h => nomatch h⟩
  | w :: rest, E, mpE, hEE, hfind_adv, hnd, hfresh, hraws => by
    obtain ⟨hw_nin, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨E₁, mp₁, hEE₁, hext₁, hac₁, hout₁, hready_w⟩ :=
      installRecIotaThms w.rawRules 0 mpE hEE hfind_adv
        (fun j _ => hfresh w List.mem_cons_self j)
        (hraws w List.mem_cons_self)
    have hfresh_rest : ∀ w' ∈ rest, ∀ j,
        E₁.find? (auxKey (auxKey w'.cv.name .model) (.iota j)) = none := by
      intro w' hw' j
      rw [hout₁ _ (fun j' _ heq => by
        injection heq with h1 _
        injection h1 with h2 _
        have hmem : w'.cv.name ∈ rest.map (·.cv.name) := List.mem_map_of_mem hw'
        rw [h2] at hmem
        exact hw_nin hmem)]
      exact hfresh w' (List.mem_cons_of_mem w hw') j
    obtain ⟨E₂, mp₂, hEE₂, hext₂, hac₂, hout₂, hready_rest⟩ :=
      installAllRecIotaThms rest mp₁ hEE₁
        (fun k ci hk => hext₁.find (hfind_adv k ci hk))
        hnd' hfresh_rest
        (fun w' hw' => hraws w' (List.mem_cons_of_mem w hw'))
    refine ⟨E₂, mp₂, hEE₂, hext₁.trans hext₂, ?_, ?_, ?_⟩
    · intro k hk
      have hk₁ : (E₁.find? k).isSome = true := by
        obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hk
        rw [hext₁.find hci]; rfl
      rw [hac₂ k hk₁, hac₁ k hk]
    · intro k hk_ne
      rw [hout₂ k (fun w' hw' j => hk_ne w' (List.mem_cons_of_mem w hw') j),
        hout₁ k (fun j _ => hk_ne w List.mem_cons_self j)]
    · intro w' hw'
      rcases List.mem_cons.mp hw' with rfl | hw'_tl
      · exact hready_w.mono (fun _ _ => hext₂.find)
      · exact hready_rest w' hw'_tl

/-- Build `SwapShList`, `SwapNResS`, and per-recursor lookup correspondence across `pushList` of
`recs` when replacing `[]` with `w.rules_r find?`. -/
theorem swap_pushList_recs
    {find? : KKey → Option (ConstantInfo .anon)}
    {envSelf : Env .anon}
    (RF : ConstantVal .anon → Nat → Nat → RecRule .anon → Prop) :
    ∀ (recs : List RecInstallEntry) {E₁ E₂ : Env .anon},
      SwapShList E₁.consts E₂.consts →
      SwapNResS E₁ E₂ →
      (∀ c ∈ E₂.consts, c ∈ envSelf.consts ∨
        ∃ (cv : ConstantVal .anon) (mI rP : Nat) (rules : List (RecRule .anon)),
          c = .recInfo cv mI rP rules ∧
          (∀ (rl : RecRule .anon), rl ∈ rules → RF cv mI rP rl)) →
      (∀ (n : KKey) (cv : ConstantVal .anon) (mI rP : Nat) (rules : List (RecRule .anon)),
        E₂.find? n = some (.recInfo cv mI rP rules) →
        envSelf.find? n = some (.recInfo cv mI rP rules) ∨
        (∀ (rl : RecRule .anon), rl ∈ rules → RF cv mI rP rl)) →
      (∀ w ∈ recs, Ix.Kernel.reservedBasisNames.contains w.cv.name = false ∧
        (∀ (rl : RecRule .anon), rl ∈ w.rules_r find? → RF w.cv w.mI w.rP rl)) →
      SwapShList (pushList (recs.map (·.prov_r)) E₁).consts
        (pushList (recs.map (·.checked_r find?)) E₂).consts ∧
      SwapNResS (pushList (recs.map (·.prov_r)) E₁)
        (pushList (recs.map (·.checked_r find?)) E₂) ∧
      (∀ c ∈ (pushList (recs.map (·.checked_r find?)) E₂).consts, c ∈ envSelf.consts ∨
        ∃ (cv : ConstantVal .anon) (mI rP : Nat) (rules : List (RecRule .anon)),
          c = .recInfo cv mI rP rules ∧
          (∀ (rl : RecRule .anon), rl ∈ rules → RF cv mI rP rl)) ∧
      (∀ (n : KKey) (cv : ConstantVal .anon) (mI rP : Nat) (rules : List (RecRule .anon)),
        (pushList (recs.map (·.checked_r find?)) E₂).find? n = some (.recInfo cv mI rP rules) →
        envSelf.find? n = some (.recInfo cv mI rP rules) ∨
        (∀ (rl : RecRule .anon), rl ∈ rules → RF cv mI rP rl))
  | [], _, _, hsw, hnres, hents, hentF, _ => ⟨hsw, hnres, hents, hentF⟩
  | w :: rest, E₁, E₂, hsw, hnres, hents, hentF, hw_all => by
    obtain ⟨hres_w, hrf_w⟩ := hw_all w List.mem_cons_self
    have hsw' : SwapShList (Env.consts ⟨w.prov_r :: E₁.consts⟩)
        (Env.consts ⟨w.checked_r find? :: E₂.consts⟩) :=
      SwapShList.cons (Or.inr ⟨w.cv, w.mI, w.rP, w.rules_r find?, rfl, rfl⟩) hsw
    have hnres' : SwapNResS ⟨w.prov_r :: E₁.consts⟩ ⟨w.checked_r find? :: E₂.consts⟩ := by
      intro n cv mI₀ rP₀ rules₀ h₀ h₃
      rw [Env.find?_cons] at h₀ h₃
      by_cases hn : w.cv.name = n
      · rw [show w.prov_r.name = w.cv.name from rfl, ite_eq_left hn] at h₀
        obtain ⟨rfl, -, -, -⟩ := ConstantInfo.recInfo.inj (Option.some.inj h₀)
        exact Or.inr (hn ▸ hres_w)
      · rw [show w.prov_r.name = w.cv.name from rfl, ite_eq_right hn] at h₀
        rw [show (w.checked_r find?).name = w.cv.name from rfl, ite_eq_right hn] at h₃
        exact hnres n cv mI₀ rP₀ rules₀ h₀ h₃
    have hents' : ∀ c ∈ (Env.consts ⟨w.checked_r find? :: E₂.consts⟩),
        c ∈ envSelf.consts ∨
        ∃ (cv : ConstantVal .anon) (mI rP : Nat) (rules : List (RecRule .anon)),
          c = .recInfo cv mI rP rules ∧
          (∀ (rl : RecRule .anon), rl ∈ rules → RF cv mI rP rl) := by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact Or.inr ⟨w.cv, w.mI, w.rP, w.rules_r find?, rfl, hrf_w⟩
      · exact hents c hc'
    have hentF' : ∀ (n : KKey) (cv : ConstantVal .anon) (mI rP : Nat)
        (rules : List (RecRule .anon)),
        Env.find? ⟨w.checked_r find? :: E₂.consts⟩ n = some (.recInfo cv mI rP rules) →
        envSelf.find? n = some (.recInfo cv mI rP rules) ∨
        (∀ (rl : RecRule .anon), rl ∈ rules → RF cv mI rP rl) := by
      intro n cv mI rP rules hfx
      rw [Env.find?_cons] at hfx
      by_cases hn : (w.checked_r find?).name = n
      · rw [ite_eq_left hn] at hfx
        obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj (Option.some.inj hfx)
        exact Or.inr hrf_w
      · rw [ite_eq_right hn] at hfx
        exact hentF n cv mI rP rules hfx
    exact swap_pushList_recs RF rest hsw' hnres' hents' hentF'
      (fun w' hw' => hw_all w' (List.mem_cons_of_mem w hw'))

theorem etaFamiliesClosed_of_swap {E₁ E₂ : Env .anon}
    (hcg : Ix.Kernel.SwapCongr E₁ E₂)
    (hEta : Ix.Kernel.EtaFamiliesClosed E₁) :
    Ix.Kernel.EtaFamiliesClosed E₂ := by
  intro T cvT caps hfT hcape hres
  have hfT₁ : E₁.find? T = some (.indInfo cvT caps) :=
    hcg.findDown T _ hfT (fun _ _ _ _ h => nomatch h)
  obtain ⟨C, cvC, hC, hfC₁⟩ := hEta T cvT caps hfT₁ hcape hres
  exact ⟨C, cvC, hC, hcg.findUp C _ hfC₁ (fun _ _ _ _ h => nomatch h)⟩

/-- Closed well-typed dummy `.model` definition stored alongside each modeled recursor `r` in
`env₂` so `HasModel env₂ r` holds while `InstallStep` accepts `.aux r .model`. -/
def dummyModelCV (r : KKey) : ConstantVal .anon :=
  ⟨auxKey r .model, [], .sort (.succ .zero)⟩

def dummyModelCI (r : KKey) : ConstantInfo .anon :=
  .defnInfo (dummyModelCV r) (.sort .zero) .abbrev

theorem dummyModel_declDefnRunJ {E : Env .anon} {r : KKey}
    (hfresh : E.find? (auxKey r .model) = none) :
    DeclDefnRunJ rulesJ E (dummyModelCV r) (.sort .zero) .abbrev ⟨dummyModelCI r :: E.consts⟩ := by
  have hcv : ConstantValRunJ rulesJ E (dummyModelCV r) (.sort (.succ .zero)) :=
    ⟨by show (E.find? (auxKey r .model)).isNone = true; rw [hfresh]; rfl,
      Ix.Kernel.reservedBasisNames_contains_auxKey r .model,
      rfl, rfl, rfl, rfl, Annot.sort, rfl, rfl,
      .sort (.succ (.succ .zero)), .succ (.succ .zero), Infer.sort, Red.refl⟩
  have hv : ValueFrontRunJ rulesJ E (dummyModelCV r) (.sort .zero)
      (.sort (.succ .zero)) (.sort .zero) :=
    ⟨rfl, rfl, Annot.sort, rfl, rfl, .sort (.succ .zero), Infer.sort, DefEq.refl⟩
  exact ⟨.sort (.succ .zero), .sort .zero, hcv, hv, rfl,
    fun hm => absurd (List.mem_of_elem_eq_true hm) (auxKey_not_mem_natOpNames r .model),
    fun hm => absurd (List.mem_of_elem_eq_true hm) (auxKey_not_mem_natDivModNames r .model)⟩

theorem installDummyModels {V : Type u} [Ix.Kernel.SetTheory V] :
    ∀ (rnames : List KKey) {E : Env .anon}
      (mp : EnvModelM V .verified E)
      (hS : StoreInv E)
      (hEta : Ix.Kernel.EtaFamiliesClosed E)
      (hnd : rnames.Nodup)
      (hfresh : ∀ r ∈ rnames, E.find? (auxKey r .model) = none),
      ∃ mp' : EnvModelM V .verified ⟨rnames.map dummyModelCI ++ E.consts⟩,
        ModelExt mp mp' ∧
        StoreInv ⟨rnames.map dummyModelCI ++ E.consts⟩ ∧
        Ix.Kernel.EtaFamiliesClosed ⟨rnames.map dummyModelCI ++ E.consts⟩
  | [], _, mp, hS, hEta, _, _ => ⟨mp, .refl, hS, hEta⟩
  | r :: rest, E, mp, hS, hEta, hnd, hfresh => by
    obtain ⟨hr_nin, hnd'⟩ := List.nodup_cons.mp hnd
    have hfresh_rest : ∀ r' ∈ rest, E.find? (auxKey r' .model) = none :=
      fun r' hr' => hfresh r' (List.mem_cons_of_mem r hr')
    obtain ⟨mp₁, hext₁, hS₁, hEta₁⟩ := installDummyModels rest mp hS hEta hnd' hfresh_rest
    let E₁ : Env .anon := ⟨rest.map dummyModelCI ++ E.consts⟩
    have hfresh_r : E₁.find? (auxKey r .model) = none := by
      unfold Env.find?
      rw [List.find?_append]
      have hnone_pre : (rest.map dummyModelCI).find?
          (fun c : ConstantInfo .anon => c.name == auxKey r .model) = none := by
        refine List.find?_eq_none.mpr fun c hc hbeq => ?_
        obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hc
        have heq : auxKey r' .model = auxKey r .model := eq_of_beq hbeq
        injection heq with hrr _
        exact hr_nin (hrr ▸ hr')
      rw [hnone_pre, Option.none_or]
      exact hfresh r List.mem_cons_self
    have hrun := dummyModel_declDefnRunJ hfresh_r
    obtain ⟨mp₂, hext₂⟩ :=
      Ix.Kernel.Model.harvestDefnJ mp₁ (Ix.Kernel.Model.judgeSound_rulesJ_of mp₁) hrun
    have hS₂ : StoreInv ⟨dummyModelCI r :: E₁.consts⟩ :=
      Ix.Kernel.Model.storeInv_consTyped hS₁ hfresh_r ⟨rfl, rfl, rfl, rfl⟩
        (fun _ _ _ heq => by
          obtain ⟨_, rfl, _⟩ := ConstantInfo.defnInfo.inj heq
          exact ⟨rfl, rfl, rfl, rfl⟩)
        (fun _ _ _ _ heq => nomatch heq)
        (fun _ heq => nomatch heq)
        (fun _ _ heq => nomatch heq)
    have hEta₂ : Ix.Kernel.EtaFamiliesClosed ⟨dummyModelCI r :: E₁.consts⟩ :=
      Ix.Kernel.EtaFamiliesClosed.cons_nonind hEta₁ hfresh_r (fun _ _ heq => nomatch heq)
    exact ⟨mp₂, hext₁.trans hext₂, hS₂, hEta₂⟩

/-! ## `ModeledBlockWitness` and `modeledBlock_install_step` -/

/-- Complete `V`-independent witness extracted from `KernelModeled::check_modeled_block` +
`KernelCheck::check_const` for a modeled inductive declaration `.indDecl block₀ nP`. -/
structure ModeledBlockWitness (env : Env .anon) (block₀ : List (ConstantInfo .anon))
    (nP : Nat) where
  c_pub : Ctx
  c_rhs : Ctx
  c_adv : Ctx
  f_id : KKey → KKey
  advSet : Bytes.Address → Prop
  nonrecs : List (ConstantInfo .anon)
  recs : List RecInstallEntry
  /-- Advice records step `env` to `c_adv.env` via `ModelExtStep`. -/
  hadv_step : ModelExtStep.{u} env c_adv.env
  /-- `blockNames := nonrecs.map (·.name) ++ recs.map (·.cv.name)` are pairwise distinct, fresh in
  `c_adv.env`, and cover `installs (.indDecl block₀ nP) = block₀` via `StoredAs`. -/
  hnames_nodup : ((nonrecs.map (·.name)) ++ (recs.map (·.cv.name))).Nodup
  hnames_fresh_adv : ∀ k ∈ (nonrecs.map (·.name)) ++ (recs.map (·.cv.name)),
    c_adv.env.find? k = none
  hcov_installs : ∀ ci₀ ∈ IxVM.Consistency.installs (.indDecl block₀ nP),
    (∃ c ∈ nonrecs, IxVM.Consistency.StoredAs c ci₀) ∨
    (∃ w ∈ recs,
      IxVM.Consistency.StoredAs
        (w.checked_r (pushList nonrecs env).find?) ci₀)
  hin_installs_nonrec : ∀ c ∈ nonrecs,
    ∃ ci₀ ∈ IxVM.Consistency.installs (.indDecl block₀ nP), ci₀.name = c.name
  hin_installs_rec : ∀ w ∈ recs,
    ∃ ci₀ ∈ IxVM.Consistency.installs (.indDecl block₀ nP), ci₀.name = w.cv.name
  hf_out : ∀ k, ((nonrecs.map (·.name)) ++ (recs.map (·.cv.name))).contains k = false →
    f_id k = k
  /-- Non-recursor and provisional-recursor chains over `(env, env_iota)` for every `env_iota`
  extending `c_adv.env` that keeps non-`.iota` lookups identical to `c_adv.env`. -/
  hchains : ∀ (env_iota : Env .anon),
    EnvExt c_adv.env env_iota →
    (∀ k, (∀ w ∈ recs, ∀ j, k ≠ auxKey (auxKey w.cv.name .model) (.iota j)) →
      env_iota.find? k = c_adv.env.find? k) →
    NonRecChain env env_iota f_id nonrecs ∧
    RecProvChain (pushList nonrecs env) (pushList (nonrecs.map posCI) env_iota) f_id recs
  /-- Per-recursor telescope/pin facts, `RawIotaRulesVmRun` certificates, and `c_pub` / `c_rhs`
  environment bridges. -/
  hctor_pub_wf : ∀ (ck : KKey) cvj cnP cnF,
    c_pub.env.find? ck = some (.ctorInfo cvj cnP cnF) →
    cvj.type.allLevelParamsDefined cvj.levelParams = true ∧
    (pushList nonrecs env).find? ck = some (.ctorInfo cvj cnP cnF) ∧
    (∃ bsC0 cbody0 Dc usc,
      cvj.type.stripPis (cnP + cnF) = some (bsC0, cbody0) ∧
      cbody0.getAppFn = .const Dc usc)
  hfind_pub_M : ∀ (env_iota : Env .anon),
    EnvExt c_adv.env env_iota →
    (∀ k ci, c_pub.env.find? k = some ci →
      (pushList (nonrecs.map posCI) env_iota).find? k = some ci) ∧
    EnvExt c_pub.env
      (pushList (recs.map (·.prov_p)) (pushList (nonrecs.map posCI) env_iota))
  hrecs_rules : ∀ w ∈ recs,
    w.rP ≤ w.mI ∧
    w.cv.type.stripPis w.mI = some (w.pre, .forallE w.dom w.body w.bm) ∧
    w.dom.getAppFn = .const w.indKey w.lvls_lps ∧
    w.dom.getAppArgs.length = w.cnP_ind + (w.mI - w.rP) ∧
    (∀ p ∈ w.dom.getAppArgs.take w.cnP_ind, noLooseIn 0 (w.mI - w.rP) p = true) ∧
    w.dom.getAppArgs.drop w.cnP_ind =
      (List.range (w.mI - w.rP)).map (fun m => .bvar (w.mI - w.rP - 1 - m)) ∧
    w.pins_lps = (w.dom.getAppArgs.take w.cnP_ind).map (Expr.lowerBVars (w.mI - w.rP) 0) ∧
    (∀ r ∈ w.rawRules,
      noLetExpr (posOf w.cv.levelParams r.rhs) = true ∧
      r.rhs.constsResolve (pushList (recs.map (·.prov_r)) (pushList nonrecs env)) = true) ∧
    (∀ (env_iota : Env .anon), EnvExt c_adv.env env_iota →
      ∀ r ∈ w.rawRules, ∀ t', posRulesJ.infer c_rhs.env 0 r.rhs t' →
        ∃ t'', posRulesJ.infer
          (pushList (recs.map (·.prov_p)) (pushList (nonrecs.map posCI) env_iota))
          0 (posOf w.cv.levelParams r.rhs) t'') ∧
    RawIotaRulesVmRun c_pub c_rhs c_adv
      ((nonrecs.map (·.name)) ++ (recs.map (·.cv.name)))
      f_id advSet w.cv.name w.cv.levelParams w.cv.type w.mI w.rP w.lvls_lps w.pins_lps
      0 w.rawRules

private theorem envExt_prepend_fresh :
    ∀ (new : List (ConstantInfo .anon)) {E : Env .anon},
      (new.map (·.name)).Nodup →
      (∀ c ∈ new, E.find? c.name = none) →
      (∀ c ∈ new, ∀ T, c.name ≠ projTableName T) →
      EnvExt E ⟨new ++ E.consts⟩
  | [], _, _, _, _ => EnvExt.refl _
  | c :: rest, E, hnd, hfresh, hnpt => by
    obtain ⟨hc_nin, hnd'⟩ := List.nodup_cons.mp hnd
    have hext₁ : EnvExt E ⟨rest ++ E.consts⟩ :=
      envExt_prepend_fresh rest hnd'
        (fun x hx => hfresh x (List.mem_cons_of_mem c hx))
        (fun x hx => hnpt x (List.mem_cons_of_mem c hx))
    have hc_fresh : (⟨rest ++ E.consts⟩ : Env .anon).find? c.name = none := by
      unfold Env.find?
      rw [List.find?_append,
        List.find?_eq_none.mpr (fun (x : ConstantInfo .anon) hx hbeq => by
          have hmem : x.name ∈ rest.map (·.name) := List.mem_map_of_mem hx
          rw [eq_of_beq hbeq] at hmem
          exact hc_nin hmem),
        Option.none_or]
      exact hfresh c List.mem_cons_self
    exact hext₁.trans (envExt_cons_fresh hc_fresh (hnpt c List.mem_cons_self))

private theorem recProvChain_wf {E_p₀ : Env .anon} {f_id : KKey → KKey} :
    ∀ (recs : List RecInstallEntry) {E_r : Env .anon},
      RecProvChain E_r E_p₀ f_id recs →
      ∀ w ∈ recs,
        w.cv.levelParams.Perm (List.range w.cv.levelParams.length) ∧
        Ix.Kernel.reservedBasisNames.contains w.cv.name = false ∧
        w.cv.type.hasFvar = false ∧
        w.cv.type.allLevelParamsDefined w.cv.levelParams = true ∧
        w.cv.type.constsResolve (pushList (recs.map (·.prov_r)) E_r) = true ∧
        w.cv.type.looseBVarsBounded 0 = true
  | [], _, _, _, hm => nomatch hm
  | w₀ :: rest, E_r,
      ⟨hfr_r, _, _, hnres, hperm, htf, htp, htr, htb, _, hrest⟩, w, hm => by
    have hmono_rest : ∀ (k : KKey),
        (Env.find? ⟨w₀.prov_r :: E_r.consts⟩ k).isSome = true →
        ((pushList (rest.map (·.prov_r)) ⟨w₀.prov_r :: E_r.consts⟩).find? k).isSome = true := by
      intro k hk
      rw [pushList_eq]
      exact env_find?_isSome_of_tail hk
    rcases List.mem_cons.mp hm with rfl | htl
    · exact ⟨hperm, hnres, htf, htp,
        Ix.Kernel.Expr.constsResolve_le hmono_rest (Ix.Kernel.Expr.constsResolve_mono htr),
        htb⟩
    · exact recProvChain_wf rest hrest w htl

private theorem nonRecChain_kinds :
    ∀ (nonrecs : List (ConstantInfo .anon)) {E_r E_p₀ : Env .anon} {f_id : KKey → KKey},
      NonRecChain E_r E_p₀ f_id nonrecs →
      ∀ c ∈ nonrecs, (∃ cv, c = .indInfo cv {}) ∨ ∃ cv nP nF, c = .ctorInfo cv nP nF
  | [], _, _, _, _, _, hm => nomatch hm
  | c₀ :: rest, _, _, _, ⟨_, _, _, _, _, hknd, _, _, _, _, _, hrest⟩, c, hm => by
    rcases List.mem_cons.mp hm with rfl | htl
    · exact hknd
    · exact nonRecChain_kinds rest hrest c htl

private theorem find?_of_mem_nodup_prefix {tail : List (ConstantInfo .anon)}
    (new : List (ConstantInfo .anon)) {c : ConstantInfo .anon}
    (hnd : (new.map (·.name)).Nodup) (hm : c ∈ new) :
    Env.find? ⟨new ++ tail⟩ c.name = some c := by
  induction new with
  | nil => exact nomatch hm
  | cons c₀ rest ih =>
    obtain ⟨hc₀_nin, hnd'⟩ := List.nodup_cons.mp hnd
    change Env.find? ⟨c₀ :: (rest ++ tail)⟩ c.name = some c
    rcases List.mem_cons.mp hm with rfl | htl
    · exact Env.find?_cons_self c ⟨rest ++ tail⟩
    · have hne : c₀.name ≠ c.name := fun heq => by
        have hmem : c.name ∈ rest.map (·.name) := List.mem_map_of_mem htl
        rw [← heq] at hmem
        exact hc₀_nin hmem
      rw [EnvExt.find?_cons_ne hne]
      exact ih hnd' htl

private theorem rawIotaRules_mem {c_pub c_rhs c_adv : Ctx}
    {blockNames : List KKey} {f_id : KKey → KKey} {advSet : Bytes.Address → Prop}
    {cvName : KKey} {lps : List LevelParam} {tyA : KExpr} {mI rP : Nat}
    {lvls_lps : List KLevel} {pins_lps : List KExpr} :
    ∀ {j : Nat} {rls : List (RecRule .anon)},
      RawIotaRulesVmRun c_pub c_rhs c_adv blockNames f_id advSet cvName lps tyA mI rP
        lvls_lps pins_lps j rls →
      ∀ r ∈ rls, ∃ j', Nonempty (RawIotaRuleVmRun c_pub c_rhs c_adv blockNames f_id advSet
        cvName lps tyA mI rP lvls_lps pins_lps j' r)
  | _, [], _, _, hm => nomatch hm
  | j, _ :: _, ⟨hraw, hrest⟩, r, hm => by
    rcases List.mem_cons.mp hm with rfl | htl
    · exact ⟨j, hraw⟩
    · exact rawIotaRules_mem hrest r htl

private theorem modelExt_isSome_acval {V : Type u} [Ix.Kernel.SetTheory V]
    {e₁ e₂ : Env .anon} {mp₁ : EnvModelM V .verified e₁} {mp₂ : EnvModelM V .verified e₂}
    (hext : ModelExt mp₁ mp₂) :
    ∀ k : KKey, (e₁.find? k).isSome = true →
      (e₂.find? k).isSome = true ∧ mp₂.base2.acval k = mp₁.base2.acval k := by
  induction hext with
  | refl => exact fun _ hk => ⟨hk, rfl⟩
  | @step E₂ m₂ c₀ A m₃ _ hfresh _ _ hac ih =>
    intro k hk
    obtain ⟨hk₂, hac₂⟩ := ih k hk
    have hne : k ≠ c₀.name := fun heq => by rw [heq, hfresh] at hk₂; exact nomatch hk₂
    refine ⟨?_, ?_⟩
    · rw [EnvExt.find?_cons_ne hne.symm]; exact hk₂
    · rw [hac, acvalWith_ne hne, hac₂]
  | swap _ hsome _ _ hac ih =>
    intro k hk
    obtain ⟨hk₂, hac₂⟩ := ih k hk
    exact ⟨hsome k hk₂, (congrFun hac k).trans hac₂⟩

set_option maxHeartbeats 6400000 in
/-- **Main 4-Phase Modeled Block Installation Theorem**: turns `ModeledBlockWitness` into
`CleanInstallStep env (.indDecl block₀ nP) env₂` and `∀ V [SetTheory V], DeclInvM V env → DeclInvM V env₂`. -/
theorem modeledBlock_install_step {calls : List (Call F)} {env : Env .anon}
    {block₀ : List (ConstantInfo .anon)} {nP : Nat}
    (hchk : S0.Checked calls env (.indDecl block₀ nP))
    (hnodup : ((IxVM.Consistency.installs (.indDecl block₀ nP)).map (·.name)).Nodup)
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs (.indDecl block₀ nP), env.find? ci₀.name = none)
    (hwit : DeclStoreInv env → AuxRootSynced env →
      Nonempty (ModeledBlockWitness.{u} env block₀ nP)) :
    ∃ env₂, CleanInstallStep env (.indDecl block₀ nP) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInvM V env → DeclInvM V env₂ := by
  by_cases hSA : DeclStoreInv env ∧ AuxRootSynced env
  · obtain ⟨hS₀, hAux₀⟩ := hSA
    have hbase₀ := s0Checked_installs_isBaseKey hchk
    obtain ⟨W⟩ := hwit hS₀ hAux₀
    let blockNames := (W.nonrecs.map (·.name)) ++ (W.recs.map (·.cv.name))
    let envM_r := pushList W.nonrecs env
    let envSelf_r := pushList (W.recs.map (·.prov_r)) envM_r
    let env₂_base := pushList (W.recs.map (·.checked_r envM_r.find?)) envM_r
    let dummyNames := W.recs.map (·.cv.name)
    let dummyModels := dummyNames.map dummyModelCI
    let new_base := (W.recs.map (·.checked_r envM_r.find?)).reverse ++ W.nonrecs.reverse
    let new_all := dummyModels ++ new_base
    let env₂ : Env .anon := ⟨new_all ++ env.consts⟩
    have henv₂_eq : env₂ = ⟨dummyModels ++ env₂_base.consts⟩ := by
      dsimp only [env₂, new_all, new_base, env₂_base, envM_r]
      rw [pushList_consts, pushList_consts]
      simp only [List.append_assoc]
    have henv₂_M_eq : env₂ =
        ⟨(dummyModels ++ (W.recs.map (·.checked_r envM_r.find?)).reverse) ++ envM_r.consts⟩ := by
      show Env.mk (new_all ++ env.consts) = _
      rw [pushList_consts]
      simp only [new_all, new_base, List.append_assoc]
    -- Base-key and freshness properties of `W.nonrecs`, `W.recs`, and `dummyModels`
    have hbase_nonrec : ∀ c ∈ W.nonrecs, isBaseKey c.name = true := by
      intro c hc
      obtain ⟨ci₀, hm₀, hnm⟩ := W.hin_installs_nonrec c hc
      rw [← hnm]; exact hbase₀ ci₀ hm₀
    have hbase_rec : ∀ w ∈ W.recs, isBaseKey w.cv.name = true := by
      intro w hw
      obtain ⟨ci₀, hm₀, hnm⟩ := W.hin_installs_rec w hw
      rw [← hnm]; exact hbase₀ ci₀ hm₀
    have hfresh_nonrec : ∀ c ∈ W.nonrecs, env.find? c.name = none := by
      intro c hc
      obtain ⟨ci₀, hm₀, hnm⟩ := W.hin_installs_nonrec c hc
      rw [← hnm]; exact hfresh ci₀ hm₀
    have hfresh_rec : ∀ w ∈ W.recs, env.find? w.cv.name = none := by
      intro w hw
      obtain ⟨ci₀, hm₀, hnm⟩ := W.hin_installs_rec w hw
      rw [← hnm]; exact hfresh ci₀ hm₀
    have hfresh_dummy_env : ∀ r ∈ dummyNames, env.find? (auxKey r .model) = none := by
      intro r hr
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
      exact hAux₀.fresh_auxKey (hbase_rec w hw) (hfresh_rec w hw) .model
    have hnd_nonrec : (W.nonrecs.map (·.name)).Nodup :=
      (List.nodup_append.mp W.hnames_nodup).1
    have hnd_rec : dummyNames.Nodup :=
      (List.nodup_append.mp W.hnames_nodup).2.1
    have hdisj_nr : ∀ x ∈ W.nonrecs.map (·.name), x ∉ dummyNames :=
      fun x hx hy => (List.nodup_append.mp W.hnames_nodup).2.2 x hx x hy rfl
    have hnd_new_base : (new_base.map (·.name)).Nodup := by
      have hmap : new_base.map (·.name) =
          dummyNames.reverse ++ (W.nonrecs.map (·.name)).reverse := by
        simp only [new_base, dummyNames, List.map_append, ← List.map_reverse, List.map_map]
        rfl
      rw [hmap, List.nodup_append]
      refine ⟨List.nodup_reverse.mpr hnd_rec, List.nodup_reverse.mpr hnd_nonrec, ?_⟩
      intro x hx y hy hxy
      subst hxy
      exact hdisj_nr x (List.mem_reverse.mp hy) (List.mem_reverse.mp hx)
    have hnd_dummy : (dummyModels.map (·.name)).Nodup := by
      have hmap : dummyModels.map (·.name) = dummyNames.map (fun r => auxKey r .model) := by
        dsimp only [dummyModels]
        rw [List.map_map]
        rfl
      rw [hmap]
      refine List.Nodup.map ?_ hnd_rec
      intro r₁ r₂ heq
      injection heq
    have hnd_new_all : (new_all.map (·.name)).Nodup := by
      simp only [new_all, List.map_append, List.nodup_append]
      refine ⟨hnd_dummy, hnd_new_base, ?_⟩
      intro x hx y hy hxy
      subst hxy
      obtain ⟨c_d, hc_d, rfl⟩ := List.mem_map.mp hx
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hc_d
      obtain ⟨c_b, hc_b, heq_b⟩ := List.mem_map.mp hy
      have hb_true : isBaseKey c_b.name = true := by
        rcases List.mem_append.mp hc_b with hrc | hnr
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hrc)
          exact hbase_rec w hw
        · exact hbase_nonrec c_b (List.mem_reverse.mp hnr)
      rw [heq_b] at hb_true
      exact nomatch hb_true
    have hfresh_new_all : ∀ ci ∈ new_all, env.find? ci.name = none := by
      intro ci hci
      rcases List.mem_append.mp hci with hd | hb
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hd
        exact hfresh_dummy_env r hr
      · rcases List.mem_append.mp hb with hrc | hnr
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hrc)
          exact hfresh_rec w hw
        · exact hfresh_nonrec ci (List.mem_reverse.mp hnr)
    have hrooted_all : ∀ ci ∈ new_all,
        (∃ ci₀ ∈ IxVM.Consistency.installs (.indDecl block₀ nP), ci.name = ci₀.name) ∨
        (∃ ci₀ ∈ IxVM.Consistency.installs (.indDecl block₀ nP), ∃ t, ci.name = .aux ci₀.name t) := by
      intro ci hci
      rcases List.mem_append.mp hci with hd | hb
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hd
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
        obtain ⟨ci₀, hm₀, hnm⟩ := W.hin_installs_rec w hw
        exact Or.inr ⟨ci₀, hm₀, .model, by show auxKey w.cv.name .model = _; rw [hnm]; rfl⟩
      · rcases List.mem_append.mp hb with hrc | hnr
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hrc)
          obtain ⟨ci₀, hm₀, hnm⟩ := W.hin_installs_rec w hw
          exact Or.inl ⟨ci₀, hm₀, hnm.symm⟩
        · obtain ⟨ci₀, hm₀, hnm⟩ := W.hin_installs_nonrec ci (List.mem_reverse.mp hnr)
          exact Or.inl ⟨ci₀, hm₀, hnm.symm⟩
    have hstep_inst : IxVM.Consistency.InstallStep env (.indDecl block₀ nP) env₂ := by
      refine ⟨new_all, rfl, hnd_new_all, hfresh_new_all, ?_, ?_⟩
      · intro ci₀ hm₀
        rcases W.hcov_installs ci₀ hm₀ with ⟨c, hc, hs⟩ | ⟨w, hw, hs⟩
        · exact ⟨c, List.mem_append_right _ (List.mem_append_right _ (List.mem_reverse.mpr hc)), hs⟩
        · exact ⟨w.checked_r envM_r.find?,
            List.mem_append_right _ (List.mem_append_left _
              (List.mem_reverse.mpr (List.mem_map_of_mem hw))), hs⟩
      · intro ci hci
        rcases hrooted_all ci hci with ⟨ci₀, hm₀, hnm⟩ | ⟨ci₀, _, t, hnm⟩
        · exact Or.inl ⟨ci₀, hm₀, hnm.symm⟩
        · exact Or.inr ⟨ci₀.name, t, hnm⟩
    have hclean : CleanInstallStep env (.indDecl block₀ nP) env₂ :=
      CleanInstallStep.of_rootedList hstep_inst hbase₀ hfresh hrooted_all
    refine ⟨env₂, hclean, fun V _ hInvM => ?_⟩
    obtain ⟨⟨⟨⟨mp_0, hT_0⟩, hEta_0⟩, _⟩, _⟩ := hInvM
    -- Phase 0: Step `(env, mp_0)` across advice records to `(c_adv.env, mp_adv)`
    have hAux_adv : AuxRootSynced W.c_adv.env := W.hadv_step.auxStep hAux₀
    obtain ⟨hEta_adv, mp_adv, hext_adv⟩ := W.hadv_step.modelStep V mp_0 hT_0 hEta_0
    -- Phase 1: Install `.iota j` theorem copies onto `(c_adv.env, mp_adv)` -> `(env_iota, mp_iota)`
    have hfresh_iota_adv : ∀ w ∈ W.recs, ∀ j,
        W.c_adv.env.find? (auxKey (auxKey w.cv.name .model) (.iota j)) = none := by
      intro w hw j
      exact hAux_adv.fresh_auxKey2 (hbase_rec w hw)
        (W.hnames_fresh_adv w.cv.name (List.mem_append_right _ (List.mem_map_of_mem hw)))
        .model (.iota j)
    obtain ⟨env_iota, mp_iota, hEta_iota, hext_iota, hac_iota, hout_iota, hready_all⟩ :=
      installAllRecIotaThms W.recs mp_adv hEta_adv (fun _ _ h => h) hnd_rec hfresh_iota_adv
        (fun w hw => (W.hrecs_rules w hw).2.2.2.2.2.2.2.2.2)
    have hFPT_iota : FreshBaseProjTable env_iota := by
      intro T hbT hfT
      have hne_iota : ∀ w ∈ W.recs, ∀ j,
          projTableName T ≠ auxKey (auxKey w.cv.name .model) (.iota j) := by
        intro w _ j heq
        change auxKey T .projTable = auxKey (auxKey w.cv.name .model) (.iota j) at heq
        injection heq with _ htag
        exact nomatch htag
      have hfT_adv : W.c_adv.env.find? T = none := by
        cases hfa : W.c_adv.env.find? T with
        | none => rfl
        | some ci =>
          rw [hext_iota.find hfa] at hfT
          exact nomatch hfT
      rw [hout_iota _ hne_iota]
      exact hAux_adv.fresh_projTable hbT hfT_adv
    have hext_0_iota : EnvExt env env_iota := W.hadv_step.ext.trans hext_iota
    have hnnp_iota : NoNewProjForOld W.c_adv.env env_iota := by
      intro T _
      refine hout_iota _ fun w _ j heq => ?_
      change auxKey T .projTable = auxKey (auxKey w.cv.name .model) (.iota j) at heq
      injection heq with _ htag
      exact nomatch htag
    have hnnp_0_iota : NoNewProjForOld env env_iota :=
      W.hadv_step.noNewProj.trans hnnp_iota fun k hk => by
        obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hk
        rw [W.hadv_step.ext.find hci]; rfl
    have hagree_0 : UnposAgree mp_0.base2.acval env mp_iota.base2.acval env_iota :=
      UnposAgree.of_base (fun _ _ hf => hext_0_iota.find hf)
        (fun k hk => by
          obtain ⟨hk_adv, hac_0⟩ := modelExt_isSome_acval hext_adv k hk
          exact (hac_iota k hk_adv).trans hac_0)
        hnnp_0_iota
    have hbn_fresh_0 : ∀ k, blockNames.contains k = true → env.find? k = none := by
      intro k hk
      rcases List.mem_append.mp (List.contains_iff_mem.mp hk) with hnr | hrc
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hnr
        exact hfresh_nonrec c hc
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hrc
        exact hfresh_rec w hw
    have hlink_0 : PosPrefixLinked env env_iota mp_iota W.f_id :=
      PosPrefixLinked.of_base mp_iota W.hf_out hbn_fresh_0
    obtain ⟨hchain_nr, hchain_rec⟩ := W.hchains env_iota hext_iota hout_iota
    -- Phase 2: Lockstep model + store folds across `W.nonrecs` and `W.recs`
    let envM_p := pushList (W.nonrecs.map posCI) env_iota
    let envSelf_p := pushList (W.recs.map (·.prov_p)) envM_p
    obtain ⟨mpM_r, mpM_p, hEtaM_r, hEtaM_p, hFPT_M_r, hFPT_M_p, hextM_r, _, hagreeM, hlinkM⟩ :=
      lockstep_nonrecs W.nonrecs mp_0 mp_iota hEta_0 hEta_iota
        (FreshBaseProjTable.of_auxSynced hAux₀) hFPT_iota hagree_0 hlink_0 hchain_nr
    obtain ⟨mpSelf_r, mpSelf_p, hEtaSelf_r, _, hextSelf_r, _, hagreeSelf, hlinkSelf⟩ :=
      lockstep_recs_prov W.recs mpM_r mpM_p hEtaM_r hEtaM_p hFPT_M_r hFPT_M_p
        hagreeM hlinkM hchain_rec
    have hStoreM_r : DeclStoreInv envM_r := declStoreInv_push_nonrecs W.nonrecs hS₀ hchain_nr
    have hStoreSelf_r : DeclStoreInv envSelf_r :=
      declStoreInv_push_recs_prov W.recs hStoreM_r hchain_rec
    -- Prefix extension & lookup properties on `envM_r`, `envSelf_r`, `envM_p`, `envSelf_p`
    have hkinds_nr := nonRecChain_kinds W.nonrecs hchain_nr
    have hposCI_name : ∀ c ∈ W.nonrecs, (posCI c).name = c.name := by
      intro c hc
      rcases hkinds_nr c hc with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
    have hfresh_recs_M_r : ∀ c ∈ (W.recs.map (·.prov_r)).reverse, envM_r.find? c.name = none := by
      intro c hc
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
      show (pushList W.nonrecs env).find? w.cv.name = none
      rw [pushList_eq]
      unfold Env.find?
      rw [List.find?_append,
        List.find?_eq_none.mpr (fun (x : ConstantInfo .anon) hx hbeq => by
          have hmem_x : x.name ∈ W.nonrecs.map (·.name) :=
            List.mem_map_of_mem (List.mem_reverse.mp hx)
          have hmem_w : w.cv.name ∈ dummyNames := List.mem_map_of_mem hw
          rw [← eq_of_beq hbeq] at hmem_w
          exact hdisj_nr x.name hmem_x hmem_w),
        Option.none_or]
      exact hfresh_rec w hw
    have hext_M_Self_r : EnvExt envM_r envSelf_r := by
      change EnvExt envM_r (pushList (W.recs.map (·.prov_r)) envM_r)
      rw [pushList_eq]
      have hnd_pr : ((W.recs.map (·.prov_r)).reverse.map (·.name)).Nodup := by
        rw [List.map_reverse, List.nodup_reverse, List.map_map]; exact hnd_rec
      exact envExt_prepend_fresh _ hnd_pr hfresh_recs_M_r fun c hc T => by
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
        exact ne_projTableName_of_isBaseKey (hbase_rec w hw)
    have hfresh_nr_iota : ∀ c ∈ (W.nonrecs.map posCI).reverse, env_iota.find? c.name = none := by
      intro c hc
      obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
      rw [hposCI_name c₀ hc₀]
      rw [hout_iota _ (fun w _ j heq => by
        have hb := hbase_nonrec c₀ hc₀
        rw [heq] at hb; exact nomatch hb)]
      exact W.hnames_fresh_adv c₀.name (List.mem_append_left _ (List.mem_map_of_mem hc₀))
    have hext_iota_M_p : EnvExt env_iota envM_p := by
      change EnvExt env_iota (pushList (W.nonrecs.map posCI) env_iota)
      rw [pushList_eq]
      have hnd_np : ((W.nonrecs.map posCI).reverse.map (·.name)).Nodup := by
        rw [List.map_reverse, List.nodup_reverse, List.map_map]
        have heq_map : W.nonrecs.map ((·.name) ∘ posCI) = W.nonrecs.map (·.name) :=
          List.map_congr_left hposCI_name
        rw [heq_map]; exact hnd_nonrec
      exact envExt_prepend_fresh _ hnd_np hfresh_nr_iota fun c hc T => by
        obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
        rw [hposCI_name c₀ hc₀]
        exact ne_projTableName_of_isBaseKey (hbase_nonrec c₀ hc₀)
    have hfresh_recs_M_p : ∀ c ∈ (W.recs.map (·.prov_p)).reverse, envM_p.find? c.name = none := by
      intro c hc
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
      show (pushList (W.nonrecs.map posCI) env_iota).find? w.cv.name = none
      rw [pushList_eq]
      unfold Env.find?
      rw [List.find?_append,
        List.find?_eq_none.mpr (fun (x : ConstantInfo .anon) hx hbeq => by
          have heq : x.name = w.cv.name := eq_of_beq hbeq
          obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hx)
          rw [hposCI_name c₀ hc₀] at heq
          have hmem_c : c₀.name ∈ W.nonrecs.map (·.name) := List.mem_map_of_mem hc₀
          have hmem_w : w.cv.name ∈ dummyNames := List.mem_map_of_mem hw
          rw [← heq] at hmem_w
          exact hdisj_nr c₀.name hmem_c hmem_w),
        Option.none_or]
      change env_iota.find? w.cv.name = none
      rw [hout_iota _ (fun _ _ _ heq => by
        have hb := hbase_rec w hw
        rw [heq] at hb; exact nomatch hb)]
      exact W.hnames_fresh_adv w.cv.name (List.mem_append_right _ (List.mem_map_of_mem hw))
    have hext_M_Self_p : EnvExt envM_p envSelf_p := by
      change EnvExt envM_p (pushList (W.recs.map (·.prov_p)) envM_p)
      rw [pushList_eq]
      have hnd_pp : ((W.recs.map (·.prov_p)).reverse.map (·.name)).Nodup := by
        rw [List.map_reverse, List.nodup_reverse, List.map_map]; exact hnd_rec
      exact envExt_prepend_fresh _ hnd_pp hfresh_recs_M_p fun c hc T => by
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
        exact ne_projTableName_of_isBaseKey (hbase_rec w hw)
    have hall_r : ∀ n, blockNames.contains n = true → (envSelf_r.find? n).isSome = true := by
      intro n hn
      rcases List.mem_append.mp (List.contains_iff_mem.mp hn) with hnr | hrc
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hnr
        have hs_M : (envM_r.find? c.name).isSome = true := by
          change ((pushList W.nonrecs env).find? c.name).isSome = true
          rw [pushList_eq]
          exact env_find?_isSome_of_mem_prefix (List.mem_reverse.mpr hc)
        obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hs_M
        rw [hext_M_Self_r.find hci]; rfl
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hrc
        change ((pushList (W.recs.map (·.prov_r)) envM_r).find? w.cv.name).isSome = true
        rw [pushList_eq]
        exact env_find?_isSome_of_mem_prefix
          (ci := w.prov_r) (List.mem_reverse.mpr (List.mem_map_of_mem hw))
    have hro_p : RenameOk mpSelf_p.base2.acval envSelf_p W.f_id :=
      renameOk_of_posPrefixLinked W.hf_out hall_r hagreeSelf hlinkSelf
    have hsome_r_to_p : ∀ k, (envSelf_r.find? k).isSome = true →
        (envSelf_p.find? k).isSome = true := by
      intro k hk
      obtain ⟨ci_r, hfr⟩ := Option.isSome_iff_exists.mp hk
      obtain ⟨ci_p, hfp, -⟩ := hagreeSelf.entry k ci_r hfr
      rw [hfp]; rfl
    -- Per-recursor rule laws and `RuleFacts` on `(envSelf_r, mpSelf_r)`
    have hw_rf_laws : ∀ w ∈ W.recs,
        Ix.Kernel.reservedBasisNames.contains w.cv.name = false ∧
        ∀ rl ∈ w.rules_r envM_r.find?,
          RuleFacts envSelf_r mpSelf_r.base2.cvalE w.cv w.mI w.rP rl ∧
          (∀ φ : LevelParam → Nat, RecRuleLaw mpSelf_r.base2 φ w.cv.name w.cv w.mI w.rP rl) := by
      intro w hw
      obtain ⟨hw_perm, hw_nres, hw_tf, hw_tp, hw_tr, hw_tb⟩ := recProvChain_wf W.recs hchain_rec w hw
      obtain ⟨hrp_le, hstrip_ty, hdom_fn, hdom_len, hdom_nli, hdom_drop, hpins_def,
          hr_nolet_cr, hr_inf_self, hraws_w⟩ := W.hrecs_rules w hw
      refine ⟨hw_nres, ?_⟩
      -- Lookup of `w.prov_p` in `envSelf_p` and `w.prov_r` in `envSelf_r`
      have hfind_self_p : envSelf_p.find? (posCV w.cv).name =
          some (.recInfo (posCV w.cv) w.mI w.rP []) := by
        change (pushList (W.recs.map (·.prov_p)) envM_p).find? w.prov_p.name = some w.prov_p
        rw [pushList_eq]
        have hnd_pp : ((W.recs.map (·.prov_p)).reverse.map (·.name)).Nodup := by
          rw [List.map_reverse, List.nodup_reverse, List.map_map]; exact hnd_rec
        exact find?_of_mem_nodup_prefix _ hnd_pp (List.mem_reverse.mpr (List.mem_map_of_mem hw))
      have hfind_self_r : envSelf_r.find? w.cv.name = some w.prov_r := by
        change (pushList (W.recs.map (·.prov_r)) envM_r).find? w.prov_r.name = some w.prov_r
        rw [pushList_eq]
        have hnd_pr : ((W.recs.map (·.prov_r)).reverse.map (·.name)).Nodup := by
          rw [List.map_reverse, List.nodup_reverse, List.map_map]; exact hnd_rec
        exact find?_of_mem_nodup_prefix _ hnd_pr (List.mem_reverse.mpr (List.mem_map_of_mem hw))
      have hrec_ac : ∀ ψ, mpSelf_r.base2.acval w.cv.name ψ =
          mpSelf_p.base2.acval w.cv.name (posVal w.cv.levelParams ψ) := by
        obtain ⟨ci_p, hfp, hent⟩ := hagreeSelf.entry w.cv.name w.prov_r hfind_self_r
        have hci_eq : ci_p = w.prov_p := Option.some.inj (hfp.symm.trans hfind_self_p)
        rcases hent with ⟨heq_pr, hac_eq⟩ | ⟨_, _, hac, -⟩
        · intro ψ
          have hcv_eq : posCV w.cv = w.cv := by
            have h1 : w.prov_p = w.prov_r := hci_eq.symm.trans heq_pr
            exact (ConstantInfo.recInfo.inj h1).1
          have hlps_eq : w.cv.levelParams = List.range w.cv.levelParams.length := by
            have h2 := congrArg ConstantVal.levelParams hcv_eq
            exact h2.symm
          have hpv : posVal w.cv.levelParams ψ = ψ := by
            conv => lhs; rw [hlps_eq]
            exact posVal_range_id _ ψ
          rw [hpv, ← congrFun hac_eq ψ]
        · exact hac
      have hty_pos_wf :
          (posOf w.cv.levelParams w.cv.type).hasFvar = false ∧
          (posOf w.cv.levelParams w.cv.type).looseBVarsBounded 0 = true ∧
          (posOf w.cv.levelParams w.cv.type).constsResolve envSelf_p = true ∧
          (posOf w.cv.levelParams w.cv.type).allLevelParamsDefined
            (List.range w.cv.levelParams.length) = true := by
        refine ⟨?_, ?_, ?_, allLevelParamsDefined_posOf hw_tp⟩
        · show (w.cv.type.instantiateLevelParams _ _).hasFvar = false
          rw [hasFvar_instantiateLevelParams]; exact hw_tf
        · show (w.cv.type.instantiateLevelParams _ _).looseBVarsBounded 0 = true
          rw [looseBVarsBounded_instantiateLevelParams]; exact hw_tb
        · show (w.cv.type.instantiateLevelParams _ _).constsResolve envSelf_p = true
          rw [constsResolve_instantiateLevelParams]
          exact Ix.Kernel.Expr.constsResolve_le hsome_r_to_p hw_tr
      obtain ⟨hfind_pub_Mp, hext_pub_Sp⟩ := W.hfind_pub_M env_iota hext_iota
      have hext_adv_Sp : EnvExt W.c_adv.env envSelf_p :=
        hext_iota.trans (hext_iota_M_p.trans hext_M_Self_p)
      have hiot_p := rawIotaRules_to_posNVmRun hw_perm hrp_le hty_pos_wf
        (fun ck cvj cnP cnF hfc => (W.hctor_pub_wf ck cvj cnP cnF hfc).1)
        hstrip_ty hdom_fn hdom_len hdom_nli hdom_drop hpins_def
        hfind_pub_Mp hext_pub_Sp hext_adv_Sp
        (fun r hr => (hr_nolet_cr r hr).1)
        (fun r hr =>
          ⟨by show (r.rhs.instantiateLevelParams _ _).constsResolve envSelf_p = true
              rw [constsResolve_instantiateLevelParams]
              exact Ix.Kernel.Expr.constsResolve_le hsome_r_to_p (hr_nolet_cr r hr).2,
           hr_inf_self env_iota hext_iota r hr⟩)
        ((hready_all w hw).mono fun _ _ hf => hext_iota_M_p.find hf)
      have heq_Mp : (w.rawRules.map fun r =>
          RecRule.mk r.ctor r.nfields r.ctorParams r.fire
            (posOf w.cv.levelParams r.rhs) r.k r.eta r.paramsBlind) ≠ [] →
          envM_p.find? eqName = some eqA := by
        intro hne
        cases hrr : w.rawRules with
        | nil => simp [hrr] at hne
        | cons r₀ rest₀ =>
          have hraws' := hrr ▸ hraws_w
          obtain ⟨⟨hraw₀⟩, _⟩ := hraws'
          exact (hext_iota.trans hext_iota_M_p).find (eqA_of_rawRule mp_adv hw_perm hraw₀)
      have hlaws_p := iotaRules_vmF mpSelf_p (judgeSound_posRulesJ_of mpSelf_p) hro_p
        (fun _ _ hf => Or.inl (hext_M_Self_p.find hf)) hfind_self_p
        0 _ _ heq_Mp hiot_p
      have hpins_len : w.pins_lps.length = w.cnP_ind := by
        rw [hpins_def, List.length_map, List.length_take, hdom_len]; omega
      have hpins_cr : ∀ p ∈ w.pins_lps, p.constsResolve envSelf_r = true := by
        have hforall_wf := stripPis_body_wf_local w.mI 0 hstrip_ty hw_tf hw_tb hw_tr hw_tp
        simp only [Expr.hasFvar, Bool.or_eq_false_iff, Expr.looseBVarsBounded,
          Expr.constsResolve, Expr.allLevelParamsDefined, Bool.and_eq_true] at hforall_wf
        obtain ⟨_, _, hargs_wf⟩ := app_spine_wf_local w.dom
          hforall_wf.1.1 (by simpa using hforall_wf.2.1.1) hforall_wf.2.2.1.1 hforall_wf.2.2.2.1.1
        intro p hp
        rw [hpins_def] at hp
        obtain ⟨arg, harg_tk, rfl⟩ := List.mem_map.mp hp
        rw [constsResolve_lowerBVars]
        exact (hargs_wf arg (List.mem_of_mem_take harg_tk)).2.2.1
      -- Now prove `RuleFacts` and `RecRuleLaw` for each `rl ∈ w.rules_r envM_r.find?`
      intro rl hrl
      obtain ⟨r, hr_mem, rfl⟩ := List.mem_map.mp hrl
      obtain ⟨_, ⟨hraw_r⟩⟩ := rawIotaRules_mem hraws_w r hr_mem
      obtain ⟨_, hctor_M_r, hctor_strip⟩ :=
        W.hctor_pub_wf r.ctor hraw_r.cvj hraw_r.cnP hraw_r.cnF hraw_r.hfind_ctor
      have hcnp_eq : hraw_r.cnP = w.cnP_ind := hraw_r.hpins_len.symm.trans hpins_len
      have hctor_M_r' : envM_r.find? r.ctor = some (.ctorInfo hraw_r.cvj w.cnP_ind r.nfields) := by
        rw [← hcnp_eq, hraw_r.hnfields]; exact hctor_M_r
      have hlvls_ctor : ∀ cvj cnP cnF,
          envSelf_r.find? r.ctor = some (.ctorInfo cvj cnP cnF) →
          w.lvls_lps.length = cvj.levelParams.length := by
        intro cvj cnP cnF hfc_s
        have hfc_s0 : envSelf_r.find? r.ctor =
            some (.ctorInfo hraw_r.cvj w.cnP_ind r.nfields) :=
          hext_M_Self_r.find hctor_M_r'
        obtain ⟨rfl, -, -⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj (hfc_s.symm.trans hfc_s0))
        exact hraw_r.hlvls_len
      have hctor_cr : ∀ cvj cnP cnF,
          envSelf_r.find? r.ctor = some (.ctorInfo cvj cnP cnF) →
          cvj.type.constsResolve envSelf_r = true := by
        intro cvj _ _ hfc_s
        exact (mpSelf_r.base2.wf _ (Ix.Kernel.Semantics.Env.find?_mem hfc_s)).2.2.1
      have hlaw_r : ∀ φ : LevelParam → Nat,
          RecRuleLaw mpSelf_r.base2 φ w.cv.name w.cv w.mI w.rP
            (realCheckedRule envM_r.find? w.cv.name w.cnP_ind w.lvls_lps w.pins_lps r) := by
        intro φ
        have hlaw_p := hlaws_p
          (posCheckedRule envM_p.find? w.cv.name w.cv.levelParams w.cnP_ind w.lvls_lps w.pins_lps r)
          (List.mem_map_of_mem hr_mem) (fun hh => nomatch hh) φ
        exact unpos_recRuleLaw mpSelf_r mpSelf_p hagreeSelf hw_perm hrec_ac hw_tr
          (hr_nolet_cr r hr_mem).2 hpins_len hpins_cr hlvls_ctor hctor_cr hlaw_p
      have hrf_r : RuleFacts envSelf_r mpSelf_r.base2.cvalE w.cv w.mI w.rP
          (realCheckedRule envM_r.find? w.cv.name w.cnP_ind w.lvls_lps w.pins_lps r) :=
        realRuleFacts mpSelf_r (pushList_eq _ _) hfresh_recs_M_r
          (fun c hc => by
            obtain ⟨w', _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
            exact fun _ _ hh => nomatch hh)
          hrp_le ⟨hw_tf, hw_tb, hw_tr, hw_tp⟩ hstrip_ty hdom_fn hdom_len hdom_nli hdom_drop
          hpins_def ⟨hraw_r.hrhs_nofvar, hraw_r.hrhs_lvls, (hr_nolet_cr r hr_mem).2,
            hraw_r.hrhs_bvars⟩
          hctor_M_r'
          (by rw [← hcnp_eq, hraw_r.hnfields]; exact hctor_strip)
          hlaw_r
      exact ⟨hrf_r, hlaw_r⟩
    -- Phase 3: Swap rule-empty recursors `envSelf_r` -> `env₂_base`
    let RF := fun (cv : ConstantVal .anon) (mI rP : Nat) (rl : RecRule .anon) =>
      RuleFacts envSelf_r mpSelf_r.base2.cvalE cv mI rP rl ∧
      (∀ φ : LevelParam → Nat, RecRuleLaw mpSelf_r.base2 φ cv.name cv mI rP rl)
    obtain ⟨hswR, hnresR, hentR_both, hentFR_both⟩ :=
      swap_pushList_recs (find? := envM_r.find?) (envSelf := envSelf_r) RF
        W.recs (SwapShList.of_eq envM_r.consts) (SwapNResS.of_eq envM_r)
        (fun c hc => Or.inl (by
          change c ∈ (pushList (W.recs.map (·.prov_r)) envM_r).consts
          rw [pushList_consts]
          exact List.mem_append_right _ hc))
        (fun _ _ _ _ _ hf => Or.inl (hext_M_Self_r.find hf))
        hw_rf_laws
    have hcg : Ix.Kernel.SwapCongr envSelf_r env₂_base := SwapShList.congr hswR
    have hentR_rf : ∀ c ∈ env₂_base.consts, c ∈ envSelf_r.consts ∨
        ∃ (cv : ConstantVal .anon) (mI rP : Nat) (rules : List (RecRule .anon)),
          c = .recInfo cv mI rP rules ∧
          (∀ (rl : RecRule .anon), rl ∈ rules →
            RuleFacts envSelf_r mpSelf_r.base2.cvalE cv mI rP rl) := by
      intro c hc
      rcases hentR_both c hc with h1 | ⟨cv, mI, rP, rules, h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨cv, mI, rP, rules, h1, fun rl hrl => (h2 rl hrl).1⟩
    have hentFR_rf : ∀ (n : KKey) (cv : ConstantVal .anon) (mI rP : Nat)
        (rules : List (RecRule .anon)),
        env₂_base.find? n = some (.recInfo cv mI rP rules) →
        envSelf_r.find? n = some (.recInfo cv mI rP rules) ∨
        (∀ (rl : RecRule .anon), rl ∈ rules →
          RuleFacts envSelf_r mpSelf_r.base2.cvalE cv mI rP rl) := by
      intro n cv mI rP rules hf
      rcases hentFR_both n cv mI rP rules hf with h1 | h2
      · exact Or.inl h1
      · exact Or.inr fun rl hrl => (h2 rl hrl).1
    have hS_base : StoreInv env₂_base :=
      swapStoreInv hStoreSelf_r.store hswR
        (fun c hc => (hentR_rf c hc).imp_right fun ⟨cv, mI, rP, rules, h1, h2⟩ =>
          ⟨cv, mI, rP, rules, h1, fun rl hrl => ruleFactsS_of_ruleFacts (h2 rl hrl)⟩)
        (fun n cv mI rP rules hf => (hentFR_rf n cv mI rP rules hf).imp_right
          fun h2 rl hrl => ruleFactsS_of_ruleFacts (h2 rl hrl))
    have hrecP : ∀ m₃ : EnvModel V env₂_base, m₃.acval = mpSelf_r.base2.acval →
        ∀ φ : LevelParam → Nat, RecRules m₃ φ := by
      intro m₃ hac φ n cv mI rP rules hf rl hrl hfire
      rcases hentFR_both n cv mI rP rules hf with hfS | hlaws
      · exact RecRuleLaw.swapP hcg hac (mpSelf_r.rec_rules φ n cv mI rP rules hfS rl hrl hfire)
      · rw [← Ix.Kernel.Semantics.Env.find?_name hf]
        exact RecRuleLaw.swapP hcg hac ((hlaws rl hrl).2 φ)
    obtain ⟨hwf₃, hctors₃, hbp₃, hproj₃⟩ :=
      swapEnvFacts mpSelf_r.base2.wf mpSelf_r.base2.rec_ctors mpSelf_r.base2.basis_pinned
        mpSelf_r.base2.proj_ok hswR hnresR hentR_rf hentFR_rf
    obtain ⟨mp₂_base, hacc_base, _⟩ :=
      EnvModelM.swapP mpSelf_r hswR hwf₃ hctors₃ hbp₃ hproj₃ hrecP
    have hEta_base : Ix.Kernel.EtaFamiliesClosed env₂_base :=
      etaFamiliesClosed_of_swap hcg hEtaSelf_r
    have hext_base : ModelExt mp_0 mp₂_base :=
      ModelExt.swap (hextM_r.trans hextSelf_r)
        (fun n hn => by rw [← hcg.isSomeEq n]; exact hn)
        (fun cv v hmem => by
          rcases hentR_rf _ hmem with h | ⟨_, _, _, _, heq, -⟩
          · exact h
          · exact nomatch heq)
        (fun ψ d e => denoteMeta_swap hcg ψ d e) hacc_base
    -- Phase 4: Install dummy `.model` definitions and close `DeclStoreInv env₂` + `DeclInvM V env₂`
    have hfresh_dummy_base : ∀ r ∈ dummyNames, env₂_base.find? (auxKey r .model) = none := by
      intro r hr
      have hbase_eq : env₂_base = ⟨new_base ++ env.consts⟩ := by
        show pushList (W.recs.map (·.checked_r envM_r.find?)) (pushList W.nonrecs env) = _
        rw [pushList_eq, pushList_eq]
        simp only [new_base, List.append_assoc]
      rw [hbase_eq]
      unfold Env.find?
      rw [List.find?_append,
        List.find?_eq_none.mpr (fun (c : ConstantInfo .anon) hc hbeq => by
          have heq : c.name = auxKey r .model := eq_of_beq hbeq
          have hb : isBaseKey c.name = true := by
            rcases List.mem_append.mp hc with hrc | hnr
            · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hrc)
              exact hbase_rec w hw
            · exact hbase_nonrec c (List.mem_reverse.mp hnr)
          rw [heq] at hb; exact nomatch hb),
        Option.none_or]
      exact hfresh_dummy_env r hr
    obtain ⟨mp₂', hext_dm, hS_env₂', hEta_env₂'⟩ :=
      installDummyModels dummyNames mp₂_base hS_base hEta_base hnd_rec hfresh_dummy_base
    -- Transport along `henv₂_eq : env₂ = ⟨dummyModels ++ env₂_base.consts⟩`
    have hext_0_2 : EnvExt env env₂ :=
      envExt_prepend_fresh new_all hnd_new_all hfresh_new_all fun c hc T => by
        rcases List.mem_append.mp hc with hd | hb
        · obtain ⟨r, _, rfl⟩ := List.mem_map.mp hd
          exact ne_projTableName_auxKey_model r T
        · rcases List.mem_append.mp hb with hrc | hnr
          · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hrc)
            exact ne_projTableName_of_isBaseKey (hbase_rec w hw)
          · exact ne_projTableName_of_isBaseKey (hbase_nonrec c (List.mem_reverse.mp hnr))
    let top_recs := dummyModels ++ (W.recs.map (·.checked_r envM_r.find?)).reverse
    have hfresh_top_M : ∀ c ∈ top_recs, envM_r.find? c.name = none := by
      intro c hc
      change (pushList W.nonrecs env).find? c.name = none
      rw [pushList_eq]
      rcases List.mem_append.mp hc with hd | hrc
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hd
        unfold Env.find?
        rw [List.find?_append,
          List.find?_eq_none.mpr (fun (x : ConstantInfo .anon) hx hbeq => by
            have heq : x.name = auxKey r .model := eq_of_beq hbeq
            have hb := hbase_nonrec x (List.mem_reverse.mp hx)
            rw [heq] at hb; exact nomatch hb),
          Option.none_or]
        exact hfresh_dummy_env r hr
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hrc)
        unfold Env.find?
        rw [List.find?_append,
          List.find?_eq_none.mpr (fun (x : ConstantInfo .anon) hx hbeq => by
            have hmem_x : x.name ∈ W.nonrecs.map (·.name) :=
              List.mem_map_of_mem (List.mem_reverse.mp hx)
            have hmem_w : w.cv.name ∈ dummyNames := List.mem_map_of_mem hw
            have heq : x.name = w.cv.name := eq_of_beq hbeq
            rw [← heq] at hmem_w
            exact hdisj_nr x.name hmem_x hmem_w),
          Option.none_or]
        exact hfresh_rec w hw
    have hni_top : ∀ c ∈ top_recs, Ix.Kernel.Model.NotInd c := by
      intro c hc
      rcases List.mem_append.mp hc with hd | hrc
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hd
        exact fun _ _ hh => nomatch hh
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hrc)
        exact fun _ _ hh => nomatch hh
    have hnew_rec_inv : ∀ n cv mI rP rules,
        env₂.find? n = some (.recInfo cv mI rP rules) →
        env.find? n = none →
        ∃ w ∈ W.recs, n = w.cv.name ∧ cv = w.cv ∧ mI = w.mI ∧ rP = w.rP ∧
          rules = w.rules_r envM_r.find? := by
      intro n cv mI rP rules hf hn0
      rcases find?_prepend_new_or_old hf with ⟨c, hc_all, heq_c, hnm_c⟩ | hold
      · rcases List.mem_append.mp hc_all with hd | hb
        · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hd
          exact nomatch heq_c
        · rcases List.mem_append.mp hb with hrc | hnr
          · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hrc)
            obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj heq_c
            exact ⟨w, hw, hnm_c.symm, rfl, rfl, rfl, rfl⟩
          · rcases hkinds_nr c (List.mem_reverse.mp hnr) with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
              exact nomatch heq_c
      · rw [hold] at hn0; exact nomatch hn0
    have hhasModel_rec : ∀ w ∈ W.recs, HasModel env₂ w.cv.name := by
      intro w hw
      have hm_dm : dummyModelCI w.cv.name ∈ new_all :=
        List.mem_append_left _ (List.mem_map_of_mem (List.mem_map_of_mem hw))
      have hf_dm : env₂.find? (auxKey w.cv.name .model) = some (dummyModelCI w.cv.name) :=
        find?_of_mem_nodup_prefix new_all hnd_new_all hm_dm
      exact ⟨dummyModelCV w.cv.name, .sort .zero, .abbrev, hf_dm⟩
    have hS_env₂ : StoreInv env₂ := henv₂_eq ▸ hS_env₂'
    have hDeclStore_env₂ : DeclStoreInv env₂ :=
      { store := hS_env₂
        thmTyped := thmTyped_step_noThm hext_0_2 hS₀.thmTyped fun n x hf => by
          rcases find?_prepend_new_or_old hf with ⟨c, hc_all, rfl, -⟩ | hold
          · right
            rcases List.mem_append.mp hc_all with hd | hb
            · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hd; exact fun _ _ hh => nomatch hh
            · rcases List.mem_append.mp hb with hrc | hnr
              · obtain ⟨_, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hrc)
                exact fun _ _ hh => nomatch hh
              · rcases hkinds_nr c (List.mem_reverse.mp hnr) with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
                  exact fun _ _ hh => nomatch hh
          · exact Or.inl hold
        recK := recK_step hS₀.store hS₀.recK hext_0_2.find fun n cv mI rP rules hf hn0 => by
          obtain ⟨w, hw, rfl, rfl, rfl, rfl, rfl⟩ := hnew_rec_inv n cv mI rP rules hf hn0
          refine ⟨fun rl hrl => ?_, fun hm => absurd (hhasModel_rec w hw) hm⟩
          obtain ⟨r, hr_mem, rfl⟩ := List.mem_map.mp hrl
          obtain ⟨_, ⟨hraw_r⟩⟩ := rawIotaRules_mem
            (W.hrecs_rules w hw).2.2.2.2.2.2.2.2.2 r hr_mem
          obtain ⟨_, hctor_M_r, _⟩ :=
            W.hctor_pub_wf r.ctor hraw_r.cvj hraw_r.cnP hraw_r.cnF hraw_r.hfind_ctor
          show recRuleKOf envM_r.find? r.ctor = recRuleKOf env₂.find? r.ctor
          rw [henv₂_M_eq]
          exact recRuleKOf_prepend_nonInd hfresh_top_M hni_top hctor_M_r
        etaTowers := etaTowers_step_noEta hext_0_2 hS₀.etaTowers fun n x hf => by
          rcases find?_prepend_new_or_old hf with ⟨c, hc_all, rfl, -⟩ | hold
          · right
            rcases List.mem_append.mp hc_all with hd | hb
            · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hd; exact fun _ _ hh => nomatch hh
            · rcases List.mem_append.mp hb with hrc | hnr
              · obtain ⟨_, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hrc)
                exact fun _ _ hh => nomatch hh
              · rcases hkinds_nr c (List.mem_reverse.mp hnr) with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩
                · intro _ caps heq he
                  obtain ⟨_, rfl⟩ := ConstantInfo.indInfo.inj heq
                  exact nomatch he
                · exact fun _ _ hh => nomatch hh
          · exact Or.inl hold
        tableBodies := tableBodies_step_noProj hext_0_2.find hS₀.tableBodies fun n x hf => by
          rcases find?_prepend_new_or_old hf with ⟨c, hc_all, rfl, -⟩ | hold
          · right
            rcases List.mem_append.mp hc_all with hd | hb
            · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hd; exact fun _ hh => nomatch hh
            · rcases List.mem_append.mp hb with hrc | hnr
              · obtain ⟨_, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hrc)
                exact fun _ hh => nomatch hh
              · rcases hkinds_nr c (List.mem_reverse.mp hnr) with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
                  exact fun _ hh => nomatch hh
          · exact Or.inl hold
        recShape := recShape_step hS₀.store hS₀.recShape hext_0_2.find
          fun n cv mI rP rules hf hn0 => by
            obtain ⟨w, hw, rfl, rfl, rfl, rfl, rfl⟩ := hnew_rec_inv n cv mI rP rules hf hn0
            refine ⟨fun rl hrl => ?_,
              fun hm => absurd (hhasModel_rec w hw) hm,
              fun hm => absurd (hhasModel_rec w hw) hm,
              fun hm => absurd (hhasModel_rec w hw) hm⟩
            obtain ⟨r, hr_mem, rfl⟩ := List.mem_map.mp hrl
            obtain ⟨_, ⟨hraw_r⟩⟩ := rawIotaRules_mem
              (W.hrecs_rules w hw).2.2.2.2.2.2.2.2.2 r hr_mem
            obtain ⟨_, hctor_M_r, _⟩ :=
              W.hctor_pub_wf r.ctor hraw_r.cvj hraw_r.cnP hraw_r.cnF hraw_r.hfind_ctor
            show recRuleEtaOf envM_r.find? w.cv.name r.ctor =
              recRuleEtaOf env₂.find? w.cv.name r.ctor
            rw [henv₂_M_eq]
            exact recRuleEtaOf_prepend_nonInd hfresh_top_M hni_top hctor_M_r }
    -- Assemble `DeclInvM V env₂`
    have hInvM_2' : DeclInvM V ⟨dummyModels ++ env₂_base.consts⟩ :=
      ⟨⟨⟨⟨mp₂', hT_0.of_ext (hext_base.trans hext_dm)⟩, hEta_env₂'⟩,
        henv₂_eq ▸ hDeclStore_env₂⟩,
       henv₂_eq ▸ hclean.auxSynced hAux₀⟩
    rwa [← henv₂_eq] at hInvM_2'
  · obtain ⟨env₀, hclean⟩ := cleanInstallStep_of_checked_fresh hchk hnodup hfresh
    exact ⟨env₀, hclean, fun _ _ hInvM => absurd ⟨hInvM.inv.store, hInvM.auxSynced⟩ hSA⟩

end IxVM.Refinement.Decl

