import IxVMRefinement.Claim.TopBase
import IxVMRefinement.Assembly.TypingDefnStep

/-! # Standalone definitions in validating and assumed table contexts

The role-context limit stays an `Option Nat` from the observed check to the install.
In particular, `none` retains the actual `Assumed` context throughout. The stored-key
check evidence has a producer from `CheckedLimAt`, and the install preserves the prefix
invariant at every store and limit where the canonical constant reloads.

This module covers safe standalone definition records (`kind = .defn`). The existing
freshness, free-key, reference-cover and extra-invariant premises remain explicit.
-/

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u

namespace IxVM.Refinement.Claim
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Core
open IxVM (F)

/-- Forget the full table encoding, preserving the actual context and its limit. -/
theorem RCLimRep.toRCRep {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} {h : Heap F} {rc : SourceValue F}
    (hrc : RCLimRep t bAddr lim h rc) : Core.RCRep t lim h rc := by
  cases lim with
  | some n => exact RCFullRep.toRCRep hrc
  | none =>
    obtain ⟨tbl, hl, htbl⟩ := hrc
    exact ⟨tbl, .construct addrMapEnum "Nil" [], _, hl, .inr ⟨rfl, rfl⟩, htbl.toTableRep⟩
end IxVM.Refinement.Claim

namespace IxVM.Refinement.Decl
open Aiur Aiur.Library Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel.Semantics Ix.Kernel.SetModel Ix.Kernel.Model
open Ix.Kernel (Env ConstantInfo ConstantVal Declaration)
open Ix.Kernel.Rules (Annot Red DefEq Infer)
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

private def zeroGhostWalked : Nat → KExpr := fun _ => .sort .zero

private theorem typesRep_of_nil_eq (κ : _root_.Address → KKey) {m m_pre : Heap F}
    (hm : m = m_pre ++ [.construct kexprListEnum "Nil" []]) :
    TypesRep κ zeroGhostWalked m 0 (.ptr (.enum kexprListEnum) m_pre.length) := by
  rw [hm]
  exact typesRep_alloc_nil κ zeroGhostWalked m_pre

/-- Stored-key evidence from a definition check at its actual role-context limit. -/
inductive CheckedDefnAtLim (κ : _root_.Address → Core.KKey) (lim : Option Nat)
    (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (bAddr : _root_.Address)
    (E_core : Ixon.Env) (order_role : List _root_.Address) :
    Ix.Kernel.Declaration .anon → Ix.Kernel.Declaration .anon → Prop where
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
      CheckedDefnAtLim κ lim calls t bAddr E_core order_role
        (.defnDecl ⟨Core.keyOf t a, List.range nlvls, ty₀⟩ val₀ hn)
        (.defnDecl ⟨Core.keyOf t a, List.range nlvls, ty'⟩ val' hn)

/-- A definition installs using the observed limit; its invariant transports on reload. -/
theorem walkedDefn_step_lim_run
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {E_core : Ixon.Env} {order_role : List _root_.Address} {lim : Option Nat}
    {env : Env .anon} {d d' : Declaration .anon}
    (hinv : PrefixInv.{u} E_core t lim env)
    (hchk : CheckedDefnAtLim (Ctx.stored ⟨E_core, env, t, lim⟩).κ lim calls t bAddr
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
    obtain ⟨_, hty'_nfv, hty'_bvs, hty'_ann⟩ := tmC_closed_props hty_tmc_es'
    obtain ⟨_, hval'_nfv, hval'_bvs, hval'_ann⟩ := tmC_closed_props hval_tmc_kc'
    obtain ⟨stype, u, _, hinf_ty, hred_ty, _, _⟩ :=
      scoped_core_ensure_sort (c := c) hrc_es (typesRep_of_nil_eq c.κ hm_es)
        (ghostScoped_zero zeroGhostWalked) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_es) (fun _ _ => trivial)) ev_es
        (hty_tmc_es' 0 zeroGhostWalked)
    obtain ⟨vtype, hinf_val, hde_val⟩ :=
      scoped_core_check (c := c) hrc_kc (typesRep_of_nil_eq c.κ hm_kc)
        (ghostScoped_zero zeroGhostWalked) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_kc) (fun _ _ => trivial)) ev_kc
        (hval_tmc_kc' 0 zeroGhostWalked) (hty_tmc_kc' 0 zeroGhostWalked)
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
    have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.defnDecl cv' val' hn)
        ⟨.defnInfo cv' val' hn :: env.consts⟩ :=
      ⟨ty', val', hcv_run, hv_run, rfl,
        (fun hc => by rw [hnat_false] at hc; exact nomatch hc),
        (fun hc => by rw [hdm_false] at hc; exact nomatch hc)⟩
    exact ⟨⟨.defnDecl cv' val' hn, hdecl⟩, hclean, fun E' lim' hrel hinv' => hinv'.cons_value (cn := .defnInfo cv' val' hn) (a₀ := a) rfl hfresh_cv
      (fun _ => ne_projTableName_of_isBaseKey hbase) (fun _ _ e => nomatch e)
      (fun _ _ _ e => nomatch e) (fun _ _ _ _ e => nomatch e) (fun _ e => nomatch e)
      (FullDeclInv.step_of_foldInv_clean hclean
        (foldInv_step_declRunJ (d := .defnDecl cv' val' hn) (fun _ _ heq => nomatch heq) hdecl))
      (foldStoreInv_step_declRunJ (d := .defnDecl cv' val' hn) hinv.store (fun _ _ heq => nomatch heq) hdecl)
      (hrel _ (List.mem_singleton.mpr rfl))⟩

/-- The invariant-only projection of the definition's checked declaration step. -/
theorem walkedDefn_step_lim
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {E_core : Ixon.Env} {order_role : List _root_.Address} {lim : Option Nat}
    {env : Env .anon} {d d' : Declaration .anon}
    (hinv : PrefixInv.{u} E_core t lim env)
    (hchk : CheckedDefnAtLim (Ctx.stored ⟨E_core, env, t, lim⟩).κ lim calls t bAddr
      E_core order_role d d')
    (hgood : Good ⟨E_core, env, t, none⟩ calls)
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs d, env.find? ci₀.name = none)
    (hkey : ∀ ci₀ ∈ IxVM.Consistency.installs d, KeyFree ci₀.name) :
    CleanInstallStep env d ⟨IxVM.Consistency.installs d' ++ env.consts⟩ ∧
      ∀ (E' : Ixon.Env) (lim' : Option Nat),
        (∀ cn ∈ IxVM.Consistency.installs d', ReloadsAs E' t ⟨cn :: env.consts⟩ cn) →
        PrefixInv.{u} E' t lim' env →
          PrefixInv.{u} E' t lim' ⟨IxVM.Consistency.installs d' ++ env.consts⟩ :=
  (walkedDefn_step_lim_run hinv hchk hgood hfresh hkey).2

end IxVM.Refinement.Decl

namespace IxVM.Refinement.LoadedReads
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Obs
open IxVM.Consistency
private theorem mem_sublist_of_cons_left_c {α : Type} {x : α} {ys cs : List α}
    (h : ∀ c ∈ x :: ys, c ∈ cs) : ∀ c ∈ ys, c ∈ cs :=
  fun c hm => h c (List.mem_cons_of_mem _ hm)

private theorem mem_sublist_of_append_right_c {α : Type} {xs ys cs : List α}
    (h : ∀ c ∈ xs ++ ys, c ∈ cs) : ∀ c ∈ ys, c ∈ cs :=
  fun c hm => h c (List.mem_append_right _ hm)

/-- `KernelCheck::is_unsafe_ci` on a definition in Lean's logic returns `0` and leaves the
heap unchanged. -/
private theorem is_unsafe_ci_defnValShape_safe_c {d : Ixon.Definition}
    {tyPtr valPtr hint v1 : SourceValue F} {h m2 : Heap F} {cs : List (Call F)}
    (hsafe : Ix.Kernel.Reader.safetyDecline d = none)
    (ev : ObsFn Core.W "KernelCheck::is_unsafe_ci"
      [Ingress.defnValShape d tyPtr valPtr hint] h v1 m2 cs) :
    v1 = .field 0 ∧ m2 = h := by
  cases hk : d.kind with
  | defn =>
    have hs : d.safety = .safe := by
      rw [Ix.Kernel.Reader.safetyDecline, hk] at hsafe
      cases hds : d.safety with
      | safe => rfl
      | unsaf => rw [hds] at hsafe; exact absurd hsafe (by decide)
      | part => rw [hds] at hsafe; exact absurd hsafe (by decide)
    simp only [Ingress.defnValShape, hk, hs] at ev
    cases «KernelCheck::is_unsafe_ci».obs ev with
    | Defn_Safe _ _ _ _ _ _ he hr _ => exact ⟨he, hr⟩
    | Defn_other _ _ _ _ _ _ hv hne _ _ _ =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rcases hv with ⟨_, _, _, _, _, hs_eq, _⟩
      exact (hne [] rfl (by simpa [Ingress.repDefSafetyVal] using hs_eq.symm)).elim
    | Axiom _ _ _ hv | Thm _ _ _ _ _ hv | Opaque _ _ _ _ _ _ _ hv | Quot _ _ _ _ _ _ _ hv
    | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv
    | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv =>
      simp [Core.kciEnum] at hv
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

/-- The roots of a checked safe definition are scoped at either kind of role context. -/
theorem checkedDefn_scope_lim (ht : t.check = .ok ()) (hbound : Bounded calls)
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant} {d : Ixon.Definition}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {ty₀ val₀ : Ix.Kernel.Expr .anon}
    (hkind : d.kind = .defn)
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
  obtain ⟨hnlvls, tyPtr, valPtr, hintVal, rfl, raw_ty, raw_val⟩ := hraw_d
  have hkeyAt := readCtx_keyAt_inv ht blob
  have hrd_ty_rp : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t blob) src
      (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat)) self).read d.typ = .ok ty₀ := by
    rw [Assembly.recParam_range]
    exact hty
  have hrd_val_rp : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t blob) src
      (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat)) self).read d.value = .ok val₀ := by
    rw [Assembly.recParam_range]
    exact hval
  have hk := hkind
  have hv_shape : Ingress.defnValShape d tyPtr valPtr hintVal =
      .construct Core.kciEnum "Defn"
        [.field (d.lvls.toNat : F), tyPtr, valPtr, Ingress.repDefSafetyVal d.safety, hintVal] := by
    simp [Ingress.defnValShape, hk]
  cases «KernelCheck::check_const».obs ev_chk with
  | Axiom_n1 | Axiom_other_n0 | Axiom_other_other
  | Thm | Opaque | Quot
  | Induct_n0 | Induct_other_n0 | Induct_other_other
  | Ctor_n0_n0 | Ctor_n0_other | Ctor_other_n0 | Ctor_other_other
  | Rec_n0 | Rec_other =>
    simp_all [Ingress.defnValShape, Core.kciEnum]
  | Defn v1 m2 cs12 x_nlvls x_ty x_val _ _ _ m299 cs309 _ m336 cs346 v372 m373 cs383 m404
      _ m417 cs427 _ m447 cs457 cs479 m508
      ev14 _ hv269 ev311 ev348 hm412 ev385 ev429 ev459 hm516 ev481 hc520 =>
    obtain ⟨hv1, hm2⟩ := is_unsafe_ci_defnValShape_safe_c hsafe_decl ev14
    subst v1; subst m2
    rw [hv_shape] at hv269
    simp only [Core.kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv269
    obtain ⟨hxn, hxt, hxv, -, -⟩ := hv269
    subst x_nlvls; subst x_ty; subst x_val
    have hs1 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c (by rwa [hc520] at hsub_chk))
    have hcl_v1 := hs1 _ List.mem_cons_self
    have hs2 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs1)
    have hcl_v2 := hs2 _ List.mem_cons_self
    have hs3 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs2)
    have hcl_es := hs3 _ List.mem_cons_self
    have hsub_es : ∀ cl ∈ cs383, cl ∈ calls :=
      fun cl hm => (mem_sublist_of_cons_left_c hs3) cl (List.mem_append_left _ hm)
    have hs4 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs3)
    have hs5 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs4)
    have hs6 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs5)
    have hcl_kc := hs6 _ List.mem_cons_self
    have hsub_kc := mem_sublist_of_cons_left_c hs6
    obtain ⟨cs_sr1, ev_sr1, hcs427⟩ := Assembly.assert_safety_zero_spec ev429
    obtain ⟨cs_sr2, ev_sr2, hcs457⟩ := Assembly.assert_safety_zero_spec ev459
    have ext_336_404 : Heap.Extends m336 m404 := by rw [hm412]; exact Heap.Extends.snoc _ _
    have ext_447_508 : Heap.Extends m447 m508 := by rw [hm516]; exact Heap.Extends.snoc _ _
    obtain ⟨_, hty_lbb, hty_def⟩ :=
      Assembly.validate_expr_well_scoped_spec (cx := readCtx t blob) (self := self) hbound
        hnlvls raw_ty (Heap.Extends.refl m_chk) hty ev311 hcl_v1
    obtain ⟨_, hval_lbb, hval_def⟩ :=
      Assembly.validate_expr_well_scoped_spec (cx := readCtx t blob) (self := self) hbound
        hnlvls raw_val ev311.heap_extends hval ev348 hcl_v2
    have ext_m_404 : Heap.Extends m_chk m404 :=
      ev311.heap_extends.trans (ev348.heap_extends.trans ext_336_404)
    have ext_373_508 : Heap.Extends m373 m508 :=
      ev_sr1.heap_extends.trans (ev_sr2.heap_extends.trans ext_447_508)
    have ext_404_508 : Heap.Extends m404 m508 := ev385.heap_extends.trans ext_373_508
    have ext_m_508 : Heap.Extends m_chk m508 := ext_m_404.trans ext_404_508
    obtain ⟨ty', hty_ann, hty_tmc_m⟩ :=
      raw_ty.toTmC
        (recurAddrs := []) (κ := Core.keyOf t) (ps := List.range d.lvls.toNat)
        (by simp) (by simpa using hnlvls) hkeyAt
        (fun _ _ _ _ h => nomatch h) hblob hrd_ty_rp hty_lbb hty_def
    obtain ⟨val', hval_ann, hval_tmc_m⟩ :=
      raw_val.toTmC
        (recurAddrs := []) (κ := Core.keyOf t) (ps := List.range d.lvls.toNat)
        (by simp) (by simpa using hnlvls) hkeyAt
        (fun _ _ _ _ h => nomatch h) hblob hrd_val_rp hval_lbb hval_def
    have hty_out_def := Core.Scope.validatedAnnotation_positional
      hnlvls hty_tmc_m hty_ann hty_def ev311
    have hval_out_def := Core.Scope.validatedAnnotation_positional
      hnlvls (Core.TmC.mono ev311.heap_extends hval_tmc_m) hval_ann hval_def ev348
    have hty_tmc_404 := Core.TmC.mono ext_m_404 hty_tmc_m
    have hval_tmc_508 := Core.TmC.mono ext_m_508 hval_tmc_m
    exact ⟨hty_lbb, hty_def, hval_lbb, hval_def⟩

/-- Extract the actual core checks of canonical definition annotations. -/
theorem checkedDefn_at_lim {κ : _root_.Address → Core.KKey}
    {E : Ixon.Env} {bAddr decl_addr : _root_.Address} {order_role : List _root_.Address}
    {d : Ixon.Definition} {ty₀ val₀ ty' val' : Ix.Kernel.Expr .anon}
    (hdecl_not_role : decl_addr ∉ order_role)
    (hkind : d.kind = .defn)
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
      Decl.CheckedDefnAtLim κ lim calls t bAddr E order_role
        (defnDecl d.kind ⟨Core.keyOf t decl_addr, List.range d.lvls.toNat, ty₀⟩ val₀ hn)
        (defnDecl d.kind ⟨Core.keyOf t decl_addr, List.range d.lvls.toNat, ty'⟩ val' hn) := by
  have hk := hkind
  have hv_shape : Ingress.defnValShape d tyPtr valPtr hintVal =
      .construct Core.kciEnum "Defn"
        [.field (d.lvls.toNat : F), tyPtr, valPtr, Ingress.repDefSafetyVal d.safety, hintVal] := by
    simp [Ingress.defnValShape, hk]
  cases «KernelCheck::check_const».obs ev_chk with
  | Axiom_n1 | Axiom_other_n0 | Axiom_other_other
  | Thm | Opaque | Quot
  | Induct_n0 | Induct_other_n0 | Induct_other_other
  | Ctor_n0_n0 | Ctor_n0_other | Ctor_other_n0 | Ctor_other_other
  | Rec_n0 | Rec_other =>
    simp_all [Ingress.defnValShape, Core.kciEnum]
  | Defn v1 m2 cs12 x_nlvls x_ty x_val _ _ _ m299 cs309 _ m336 cs346 v372 m373 cs383 m404
      _ m417 cs427 _ m447 cs457 cs479 m508
      ev14 _ hv269 ev311 ev348 hm412 ev385 ev429 ev459 hm516 ev481 hc520 =>
    obtain ⟨hv1, hm2⟩ := is_unsafe_ci_defnValShape_safe_c hsafe_decl ev14
    subst v1; subst m2
    rw [hv_shape] at hv269
    simp only [Core.kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv269
    obtain ⟨hxn, hxt, hxv, -, -⟩ := hv269
    subst x_nlvls; subst x_ty; subst x_val
    have hs1 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c (by rwa [hc520] at hsub_chk))
    have hcl_v1 := hs1 _ List.mem_cons_self
    have hs2 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs1)
    have hcl_v2 := hs2 _ List.mem_cons_self
    have hs3 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs2)
    have hcl_es := hs3 _ List.mem_cons_self
    have hsub_es : ∀ cl ∈ cs383, cl ∈ calls :=
      fun cl hm => (mem_sublist_of_cons_left_c hs3) cl (List.mem_append_left _ hm)
    have hs4 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs3)
    have hs5 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs4)
    have hs6 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs5)
    have hcl_kc := hs6 _ List.mem_cons_self
    have hsub_kc := mem_sublist_of_cons_left_c hs6
    obtain ⟨cs_sr1, ev_sr1, hcs427⟩ := Assembly.assert_safety_zero_spec ev429
    obtain ⟨cs_sr2, ev_sr2, hcs457⟩ := Assembly.assert_safety_zero_spec ev459
    have ext_336_404 : Heap.Extends m336 m404 := by rw [hm412]; exact Heap.Extends.snoc _ _
    have ext_447_508 : Heap.Extends m447 m508 := by rw [hm516]; exact Heap.Extends.snoc _ _
    have ext_m_404 : Heap.Extends m_chk m404 :=
      ev311.heap_extends.trans (ev348.heap_extends.trans ext_336_404)
    have ext_373_508 : Heap.Extends m373 m508 :=
      ev_sr1.heap_extends.trans (ev_sr2.heap_extends.trans ext_447_508)
    have ext_404_508 : Heap.Extends m404 m508 := ev385.heap_extends.trans ext_373_508
    have ext_m_508 : Heap.Extends m_chk m508 := ext_m_404.trans ext_404_508
    have hty_out_def := Core.Scope.validatedAnnotation_positional
      hnlvls hty_tmc_m hty_ann hty_def ev311
    have hval_out_def := Core.Scope.validatedAnnotation_positional
      hnlvls (Core.TmC.mono ev311.heap_extends hval_tmc_m) hval_ann hval_def ev348
    have hty_tmc_404 := Core.TmC.mono ext_m_404 hty_tmc_m
    have hval_tmc_508 := Core.TmC.mono ext_m_508 hval_tmc_m
    intro hn
    simp only [defnDecl, hkind]
    exact .defnDecl hdecl_not_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann
        hty_out_def hval_out_def
        hm412 hty_tmc_404 (Core.RCRep.mono ext_m_404 hrc_m) ev385 hcl_es hsub_es
        ext_373_508 hm516 (Core.TmC.mono ext_404_508 hty_tmc_404) hval_tmc_508
        (Core.RCRep.mono ext_m_508 hrc_m) ev481 hcl_kc hsub_kc

end IxVM.Refinement.LoadedReads

namespace IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Obs
open IxVM.Consistency
variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E₀ : Ixon.Env}
/-- Canonical reading, check evidence and reload from the walk at its actual limit. -/
theorem checkedLimAt_defn_step (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) {bAddr a : _root_.Address}
    {order_role : List _root_.Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (hrec : Ix.Cert.recordAt E₀ a = some c) (hinfo : c.info = .defn d) (hlogic : InLogic c)
    (hkind : d.kind = .defn)
    (hnot_role : a ∉ order_role) {lim : Option Nat} (hchk : Claim.CheckedLimAt calls bAddr t a lim)
    (Ecore : Ixon.Env) {env : Ix.Kernel.Env .anon} (hstored : Decl.UsedRefsStored t env c) :
    ∃ (ty₀ val₀ ty' val' : Ix.Kernel.Expr .anon),
      Annotates ty' ty₀ ∧ Annotates val' val₀ ∧
      ∀ hn : Ix.Kernel.ReducibilityHint,
        Decl.CheckedDefnAtLim (Core.Ctx.stored ⟨Ecore, env, t, lim⟩).κ lim calls t
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
    LoadedReads.checkedDefn_scope_lim ht hbound hkind hsafe hblob raw' hty hval ev_chk
      hsub_chk
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
  · exact LoadedReads.checkedDefn_at_lim (E := Ecore) (order_role := order_role)
      (decl_addr := Core.ixAddr a') hnot_role hkind hsafe hrc_m.toRCRep hnlvls h1 h2 h3 h4 hannT hannV htmT'
      htmV' ev_chk hsub_chk hn
  · intro E' hrec' hblobs cn hcn
    rw [LoadedReads.installs_defnDecl] at hcn
    have hcn' : cn = LoadedReads.defnConst d.kind
        ⟨Core.keyOf t (Core.ixAddr a'), List.range d.lvls.toNat, ty'⟩ val' hn :=
      List.mem_singleton.mp hcn
    subst hcn'
    exact LoadedReads.reloadsAs_defn_cons ht hrec' hinfo hlogic hblobs hty hval h1 h2 h3 h4
      hstored (LoadedReads.canonDefn_eq hcT hcV)


/-- The definition unit step at either validating or assumed table context. -/
theorem unitStep_defn_lim {X : Ix.Kernel.Env .anon → Prop} {calls : List (Call F)}
    {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    {lim : Option Nat} {bAddr A : _root_.Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .defn d) (hlogic : InLogic c)
    (hkind : d.kind = .defn)
    (hchk : Claim.CheckedLimAt calls bAddr t A lim)
    (hkey : Decl.KeyFree (keyOf t A))
    (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    (hX : KeepsValues X) :
    UnitStep.{u} X t envT E₀ E lim A c := by
  intro env hext hnd hinv hXe href hfresh
  have hbound : Bounded calls := (hst.good env none).2
  have hrec₀ : Ix.Cert.recordAt E₀ A = some c := (hS.recordOf_eq_recordAt A).symm.trans hc
  have hstored : Decl.UsedRefsStored t env c :=
    usedRefsStored_of_cover (hcover env ⟨hext, href, hfresh⟩) hinert
  obtain ⟨ty₀, val₀, ty', val', hannT, hannV, hall⟩ :=
    checkedLimAt_defn_step (order_role := []) ht hbound hS hrec₀ hinfo hlogic hkind
      List.not_mem_nil hchk E hstored
  obtain ⟨hev, hreads, hreload⟩ := hall (.regular 0)
  have hown : ConstAddrOf A c A := Or.inl ⟨rfl, Or.inl ⟨d, hinfo⟩⟩
  have hfreshA : env.find? (keyOf t A) = none := hfresh A hown
  have hfreshD : ∀ ci₀ ∈ IxVM.Consistency.installs (LoadedReads.defnDecl d.kind
      ⟨Core.keyOf t A, List.range d.lvls.toNat, ty₀⟩ val₀ (.regular 0)),
      env.find? ci₀.name = none := by
    intro ci₀ hci
    rw [LoadedReads.installs_defnDecl] at hci
    rw [List.mem_singleton.mp hci, LoadedReads.defnConst_name]
    exact hfreshA
  have hkeyD : ∀ ci₀ ∈ IxVM.Consistency.installs (LoadedReads.defnDecl d.kind
      ⟨Core.keyOf t A, List.range d.lvls.toNat, ty₀⟩ val₀ (.regular 0)),
      Decl.KeyFree ci₀.name := by
    intro ci₀ hci
    rw [LoadedReads.installs_defnDecl] at hci
    rw [List.mem_singleton.mp hci, LoadedReads.defnConst_name]
    exact hkey
  obtain ⟨-, htrans⟩ := Decl.walkedDefn_step_lim hinv hev (hst.good env none) hfreshD hkeyD
  have hinv' := htrans E lim (hreload E (hst.held hc) hst.runBlob) hinv
  rw [LoadedReads.installs_defnDecl] at hinv'
  have hname : (LoadedReads.defnConst d.kind ⟨keyOf t A, List.range d.lvls.toNat, ty'⟩ val'
      (.regular 0)).name = keyOf t A :=
    LoadedReads.defnConst_name _ _ _ _
  refine ⟨[LoadedReads.defnConst d.kind ⟨keyOf t A, List.range d.lvls.toNat, ty'⟩ val'
      (.regular 0)], List.nodup_singleton _, ?_, hinv', ?_, ?_, ?_⟩
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    rw [hname]
    exact hfreshA
  · exact hX env (LoadedReads.defnConst d.kind ⟨keyOf t A, List.range d.lvls.toNat, ty'⟩ val'
      (.regular 0)) hXe (by rw [hname]; exact hfreshA) (isValueConst_defnConst _ _ _ _)
  · intro x hx
    rcases hx with ⟨hxA, -⟩ | ⟨ms, i, m, hms, -, -⟩
    · rw [hxA]
      exact ⟨_, List.mem_singleton_self _, _, hname, hreads,
        storedAs_defnConst _ _ _ _ hannT hannV⟩
    · have h := hinfo.symm.trans hms
      cases h
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    exact Or.inl ⟨A, hown, hname⟩


end IxVM.Refinement.Typing
