/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Kernel.Verify.Audit.AxiomAudit
import Ix.Theory.Named.Verify.TypeChecker.Reduce

open Ix.Theory (VLevel)

open Ix.Theory.Named

namespace Ix.Theory.Named.TypeChecker.Inner
open Lean hiding Environment Exception
open Kernel

theorem ensureForallCore.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (ensureForallCore e e₀) fun e1 _ => c.FVarsBelow e e1 ∧
      c.TrExpr e1 e' ∧ ∃ name ty body bi, e1 = .forallE name ty body bi := by
  simp [ensureForallCore]; split
  · let .forallE .. := e
    exact .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf, _, _, _, _, rfl⟩
  refine (whnf.WF he).bind fun e _ _ ⟨hb, he⟩ => ?_; split
  · let .forallE .. := e
    exact .pure ⟨hb, he, _, _, _, _, rfl⟩
  exact .getEnv <| .getLCtx .throw

theorem ensureForallCore.WF' {c : VContext} {s : VState} (he : c.TrExpr e e') :
    RecM.WF c s (ensureForallCore e e₀) fun e1 _ => c.FVarsBelow e e1 ∧
      c.TrExpr e1 e' ∧ ∃ name ty body bi, e1 = .forallE name ty body bi :=
  let ⟨_, he, eq⟩ := he
  (ensureForallCore.WF he).mono fun _ _ _ ⟨h1, h2, h3⟩ =>
    ⟨h1, h2.defeq c.Ewf c.Δwf eq, h3⟩

theorem checkLevel.WF {c : VContext} (H : l.hasMVar' = false) :
    (checkLevel c.toContext l).WF fun _ => ∃ u', VLevel.ofLevel c.lparams l = some u' := by
  simp [checkLevel]; split <;> [exact .throw; refine .pure ?_]
  exact Level.getUndefParam_none H (by rename_i h; simpa using h)

theorem inferFVar.WF {c : VContext} :
    (inferFVar c.toContext name).WF fun ty => ∃ e' ty', c.TrTyping (.fvar name) ty e' ty' := by
  simp [inferFVar, ← c.lctx_eq]; split <;> [refine .pure ?_; exact .throw]
  rename_i decl h
  rw [c.trlctx.1.find?_eq_find?_toList] at h
  have := List.find?_some h; simp at this; subst this
  let ⟨e', ty', h1, _, h2, _, h3⟩ :=
    c.trlctx.find?_of_mem c.Ewf (List.mem_of_find?_eq_some h)
  exact ⟨_, _, h2, .fvar h1, h3, c.Δwf.find?_wf c.Ewf h1⟩

theorem inferConstant.WF {c : VContext}
    (H : ∀ l ∈ ls, l.hasMVar' = false)
    (hinf : inferOnly = true → ∃ e', c.TrExprS (.const name ls) e') :
    (inferConstant c.toContext name ls inferOnly).WF fun ty =>
      ∃ e' ty', c.TrTyping (.const name ls) ty e' ty' := by
  simp [inferConstant]; refine envGet.WF.bind fun ci eq1 => ?_
  have : (ls.foldlM (fun b a => checkLevel c.toContext a) PUnit.unit).WF fun _ =>
      ∃ ls', ls.Forall₂ (VLevel.ofLevel c.lparams · = some ·) ls' := by
    clear hinf
    induction ls with
    | nil => exact .pure ⟨_, .nil⟩
    | cons l ls ih =>
      simp at H
      refine (checkLevel.WF H.1).bind fun ⟨⟩ ⟨_, h1⟩ => ?_
      exact (ih H.2).le fun _ ⟨_, h2⟩ => ⟨_, .cons h1 h2⟩
  split <;> [rename_i h1; exact .throw]
  have main {e'} (he : c.TrExprS (.const name ls) e') : ∃ e' ty',
      c.TrTyping (.const name ls) (ci.instantiateTypeLevelParams ls) e' ty' := by
    let .const h4 H' eq := id he
    have ⟨_, _, h5, h6⟩ := c.trenv.find?_uniq eq1 h4
    have H := List.mapM_eq_some.1 H'
    have s0 := h6.instL c.Ewf (Δ := []) trivial H' (h5.trans eq.symm)
    have s1 := s0.weakFV c.Ewf (.from_nil c.mlctx.noBV) c.Δwf
    rw [(c.Ewf.ordered.closedC h4).instL.liftN_eq (Nat.le_refl _)] at s1
    have ⟨_, s1, s2⟩ := s1
    refine ⟨_, _, ?_, he, s1, .defeqU_r c.Ewf c.Δwf s2.symm ?_⟩
    · intro _ _ _; exact s0.fvarsIn.mono nofun
    · exact .const h4 (.of_mapM_ofLevel H') (H.length_eq.symm.trans eq)
  split
  · split <;> [exact .throw; rename_i h2]
    generalize eq1 : _ <$> (_ : Except Exception _) = F
    generalize eq2 : (fun ty : Expr => _) = P
    suffices ci.isPartial = false ∨ c.safety ≠ .safe → F.WF P by
      split <;> [skip; exact this (.inl (ConstantInfo.isPartial.eq_2 _ ‹_›))]
      split <;> [exact .throw; apply this]
      rename_i h; simpa [Decidable.or_iff_not_imp_left, ConstantInfo.isPartial] using h
    subst eq1 eq2; intro h3
    refine this.map fun _ ⟨_, H⟩ => ?_
    have ⟨_, h4, _, h5, h6⟩ := c.trenv.find? eq1 <| by
      revert h2 h3
      simp [ConstantInfo.safety]
      split <;> simp +contextual [*]
      split <;> simp [DefinitionSafety.le_safe, *]
      cases c.safety <;> decide
    have eq := h1.symm.trans h5
    exact main (.const h4 (List.mapM_eq_some.2 H) eq)
  · simp_all; let ⟨_, h⟩ := hinf; refine .pure (main h)

theorem inferLambda.loop.WF {c : VContext} {e₀ : Expr}
    {m} [mwf : c.MLCWF m] {n} (hn : n ≤ m.length)
    (hdrop : m.dropN n hn = c.mlctx)
    (harr : arr.toList.reverse = (m.fvarRevList n hn).map .fvar)
    (he₀ : e₀ = m.mkLambda n hn ei)
    (hei : e.instantiateList ((m.fvarRevList n hn).map .fvar) = ei)
    (hbelow : ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P e₀ →
      IsFVarUpSet (AllAbove c.vlctx P) m.vlctx ∧ FVarsIn (AllAbove c.vlctx P) ei ∧
      ∀ ty, FVarsIn (AllAbove c.vlctx P) ty → FVarsIn (AllAbove c.vlctx P) (m.mkForall n hn ty))
    (hr : e.FVarsIn (· ∈ m.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', (c.withMLC m).TrExprS ei e') :
    (inferLambda.loop inferOnly arr e).WF (c.withMLC m) s fun ty _ =>
      ∃ e' ty', c.TrTyping e₀ ty e' ty' := by
  unfold inferLambda.loop
  generalize eqfvs : (m.fvarRevList n hn).map Expr.fvar = fvs at *
  simp [harr, -bind_pure_comp]; split
  · rename_i name dom body bi
    generalize eqF : withLocalDecl (m := RecM) _ _ _ _ = F
    generalize eqP : (fun ty x => ∃ _, _) = P
    rw [Expr.instantiateList_lam] at hei; subst ei
    have main {s₁} (le₁ : s ≤ s₁) {dom'}
        (domty : (c.withMLC m).venv.IsType
          (c.withMLC m).lparams.length (c.withMLC m).vlctx.toCtx dom')
        (hdom : (c.withMLC m).TrExprS (dom.instantiateList fvs) dom')
        (hbody : inferOnly = true → ∃ body',
          TrExprS c.venv c.lparams ((none, .vlam dom') :: m.vlctx)
            (body.instantiateList fvs 1) body') :
        F.WF (c.withMLC m) s₁ P := by
      refine .stateWF fun wf => ?_
      have hdom' := hdom.trExpr c.Ewf mwf.1.tr.wf
      subst eqF eqP
      refine .withLocalDecl hdom domty le₁ fun a mwf' s' le₂ res => ?_
      have eq := @Expr.instantiateList_instantiate1_comm body fvs (.fvar a) (by trivial)
      refine inferLambda.loop.WF (Nat.succ_le_succ hn) (by simp [hdrop])
        (by simp [← eqfvs, harr]) ?_ (by simp; rfl) ?_ (hr.2.mono fun _ => .tail _) ?_
      · rw [he₀, eqfvs, ← eq]; simp; congr 2
        refine (FVarsIn.abstract_instantiate1 ((hr.2.instantiateList ?_ _).mono ?_)).symm
        · simp [← eqfvs, FVarsIn]; exact m.fvarRevList_prefix.subset
        · rintro _ h rfl; exact (mwf'.1.tr.wf.2.1 _ _ rfl).1 h
      · intro P hP he
        have ⟨h1, h2, h3⟩ := hbelow _ hP he
        refine ⟨⟨h1, fun _ => (fvarsIn_iff.1 h2.1).1⟩, ?_, fun ty hty => h3 _ ⟨h2.1, hty.abstract1⟩⟩
        rw [eqfvs, ← eq]
        refine h2.2.instantiate1 fun h => ?_
        exact res.elim (wf.ngen_wf _ (m.dropN_fvars_subset n hn (hdrop ▸ h)))
      · intro h; let ⟨_, hbody⟩ := hbody h
        exact eqfvs.symm ▸ eq ▸ ⟨_, hbody.inst_fvar c.Ewf.ordered mwf'.1.tr.wf⟩
    split
    · subst inferOnly
      refine (checkType.WF ?_).bind fun uv _ le ⟨dom', uv', _, h1, h2, h3⟩ => ?_
      · apply hr.1.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
      refine (ensureSortCore.WF h2).bind_le le fun _ _ le ⟨h4, h5, _⟩ => ?_
      obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort _, h5⟩ := h5
      have domty := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx h5.symm
      have domty' : (c.withMLC m).IsType dom' := ⟨_, domty⟩
      exact main le domty' h1 nofun
    · simp_all; let ⟨_, h1⟩ := hinf
      have .lam (ty' := dom') (body' := body') domty hdom hbody := h1
      exact main .rfl domty hdom _ hbody
  · subst ei
    refine (inferType.WF' ?_ hinf).bind fun ty _ _ ⟨e', ty', hb, h1, h2, h3⟩ => ?_
    · apply hr.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
    refine .stateWF fun wf => .getLCtx <| .pure ?_
    have ⟨_, h2', e2⟩ := h2.trExpr c.Ewf.ordered wf.trctx.wf
      |>.cheapBetaReduce c.Ewf wf.trctx.wf m.noBV
    have h3 := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx e2.symm
    let ⟨h1', h2''⟩ := mwf.1.mkLambda_trS c.Ewf h1 h3 n hn
    have h3' := (mwf.1.mkForall_trS c.Ewf h2' (h3.isType c.Ewf mwf.1.tr.wf.toCtx) n hn).1
    simp [hdrop] at h1' h2'' h3'
    refine mwf.1.mkForall_eq _ _ (eqfvs ▸ harr) ▸
      ⟨_, _, fun P hP he => ?_, he₀ ▸ h1', h3', h2''⟩
    have ⟨c1, c2, c3⟩ := hbelow _ hP he
    have := c3 _ <| FVarsBelow.cheapBetaReduce (m.noBV ▸ h2.closed) _ c1 <| hb _ c1 c2
    exact this.mp (fun _ => id) h3'.fvarsIn

theorem inferLambda.WF
    (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferLambda e inferOnly).WF c s fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty' := by
  refine .stateWF fun wf => ?_
  refine (c.withMLC_self ▸ inferLambda.loop.WF (Nat.zero_le _) rfl rfl rfl rfl ?_ h1) hinf
  exact fun P hP he => ⟨(AllAbove.wf wf.trctx.wf.fvwf).2 hP, he.mono fun _ h _ => h, fun _ => id⟩

theorem inferForall.loop.WF {c : VContext} {e₀ : Expr}
    {m} [mwf : c.MLCWF m] {n} (hn : n ≤ m.length)
    (hdrop : m.dropN n hn = c.mlctx)
    (harr : arr.toList.reverse = (m.fvarRevList n hn).map .fvar)
    (he₀ : e₀ = m.mkForall n hn ei)
    (hei : e.instantiateList ((m.fvarRevList n hn).map .fvar) = ei)
    (hr : e.FVarsIn (· ∈ m.vlctx.fvars))
    (hus : us.toList.reverse.Forall₂ (VLevel.ofLevel c.lparams · = some ·) us')
    (hΔ : m.vlctx.SortList c.venv c.lparams.length us')
    (hlen : us'.length = n)
    (hinf : inferOnly = true → ∃ e', (c.withMLC m).TrExprS ei e') :
    (inferForall.loop inferOnly arr us e).WF (c.withMLC m) s fun ty _ =>
      ∃ e' u, c.TrTyping e₀ ty e' (.sort u) := by
  unfold inferForall.loop
  generalize eqfvs : (m.fvarRevList n hn).map Expr.fvar = fvs at *
  simp [harr, -bind_pure_comp]; split
  · rename_i name dom body bi
    rw [Expr.instantiateList_forallE] at hei; subst ei
    refine (inferType.WF' ?_ ?_).bind fun uv _ le ⟨dom', uv', _, h1, h2, h3⟩ => ?_
    · apply hr.1.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
    · intro h; let ⟨_, .forallE _ _ h _⟩ := hinf h; exact ⟨_, h⟩
    refine (ensureSortCore.WF h2).bind_le le fun _ _ le ⟨h4, h5, _⟩ => ?_
    obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort h4, h5⟩ := h5
    refine .stateWF fun wf => ?_
    have domty := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx h5.symm
    have domty' : (c.withMLC m).IsType dom' := ⟨_, domty⟩
    refine .withLocalDecl h1 domty' le fun a mwf' s' le₂ res => ?_
    have eq := @Expr.instantiateList_instantiate1_comm body fvs (.fvar a) (by trivial)
    refine inferForall.loop.WF (Nat.succ_le_succ hn) (by simp [hdrop])
      (by simp [eqfvs, harr]) ?_ (by simp [eqfvs]; rfl) (hr.2.mono fun _ => .tail _)
      (by simpa using ⟨h4, hus⟩) (.cons hΔ domty) (by simp [hlen]) ?_
    · simp [he₀, ← eq]; congr 2
      refine (FVarsIn.abstract_instantiate1 ((hr.2.instantiateList ?_ _).mono ?_)).symm
      · simp [← eqfvs, FVarsIn]; exact m.fvarRevList_prefix.subset
      · rintro _ h rfl; exact (mwf'.1.tr.wf.2.1 _ _ rfl).1 h
    · intro h; let ⟨_, .forallE (body' := body') _ _ hdom₁ hbody₁⟩ := hinf h
      refine have hΔ := .refl c.Ewf mwf.1.tr.wf; have H := hdom₁.uniq c.Ewf hΔ h1; ?_
      have H := H.of_r c.Ewf mwf.1.tr.wf.toCtx domty
      have ⟨_, hbody₂⟩ := hbody₁.defeqDFC c.Ewf <| .cons hΔ (ofv := none) nofun (.vlam H)
      exact eq ▸ ⟨_, hbody₂.inst_fvar c.Ewf.ordered mwf'.1.tr.wf⟩
  · subst ei; refine (inferType.WF' ?_ hinf).bind fun ty _ _ ⟨e', ty', _, h1, h2, h3⟩ => ?_
    · apply hr.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
    refine (ensureSortCore.WF h2).bind fun _ _ le₂ ⟨h4, h5, _⟩ => ?_
    obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort (u' := u') h4, h5⟩ := h5
    obtain ⟨us, rfl⟩ : ∃ l, ⟨List.reverse l⟩ = us := ⟨us.toList.reverse, by simp⟩
    simp [Expr.sortLevel!] at hus ⊢
    have h3 := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx h5.symm
    let ⟨h1', h2'⟩ := mwf.1.mkForall_trS c.Ewf h1 ⟨_, h3⟩ n hn
    have ⟨_, h3', h4'⟩ := mkForall_hasType hus hΔ h4 h3 n hn (hus.length_eq.trans hlen)
    simp [hdrop] at h1' h2' h4'
    refine have h := .sort h3'; .pure ⟨_, _, fun _ _ _ => h.fvarsIn, he₀ ▸ h1', h, h4'⟩

theorem inferForall.WF
    (hr : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferForall e inferOnly).WF c s fun ty _ => ∃ e' u, c.TrTyping e ty e' (.sort u) :=
  (c.withMLC_self ▸ inferForall.loop.WF (Nat.zero_le _) rfl rfl rfl rfl hr .nil .nil rfl) hinf

theorem inferApp.loop.WF {c : VContext} {s : VState}
    {ll lm lr : List _}
    (stk : AppStack c.venv c.lparams c.vlctx (.mkAppRevList e lm) e' lr)
    (hbelow : FVarsBelow c.vlctx e fType)
    (hfty : c.TrExpr (fType.instantiateList lm) fty') (hety : c.HasType e' fty')
    (hargs : args = ll ++ lm.reverse ++ lr)
    (hj : j = ll.length) (hi : i = ll.length + lm.length) :
    RecM.WF c s (inferApp.loop e₀ ⟨args⟩ fType j i) fun ty _ =>
      ∃ e₁' ty', c.TrTyping (e.mkAppRevList lm |>.mkAppList lr) ty e₁' ty' := by
  subst i j; rw [inferApp.loop.eq_def]
  simp [hargs, Expr.instantiateList_reverse]
  have henv := c.Ewf; have hΔ := c.Δwf
  cases lr with simp
  | cons a lr =>
    let .app hf' ha' hf ha stk := stk
    have uf := hf'.uniqU henv hΔ hety
    split
    · rw [Expr.instantiateList_forallE] at hfty
      let ⟨_, .forallE _ _ hty hbody, h3⟩ := hfty
      have ⟨⟨_, uA⟩, _, uB⟩ := h3.trans henv hΔ uf.symm |>.forallE_inv henv hΔ
      refine inferApp.loop.WF (lm := a::lm) stk ?_ ?_ (.app hf' ha') (by simp) rfl rfl
      · exact fun _ hP he => (hbelow _ hP he).2
      have ha0 := c.mlctx.noBV ▸ ha.closed
      simp [← Expr.instantiateList_instantiate1_comm ha0.looseBVarRange_zero]
      exact .inst henv hΔ (ha'.defeqU_r henv hΔ ⟨_, uA.symm⟩) ⟨_, hbody, _, uB⟩ (ha.trExpr henv hΔ)
    · simp [Nat.add_sub_cancel_left, Expr.instantiateRevList_reverse]
      refine (ensureForallCore.WF' hfty).bind fun _ _ _ ⟨hb, ⟨_, h2, h3⟩, eq⟩ => ?_
      obtain ⟨name, ty, body, bi, rfl⟩ := eq; simp [Expr.bindingBody!]
      let .forallE _ _ hty hbody := h2
      have ⟨⟨_, uA⟩, _, uB⟩ := h3.trans henv hΔ uf.symm |>.forallE_inv henv hΔ
      refine inferApp.loop.WF (ll := ll ++ lm.reverse) (lm := [a]) stk ?_ ?_
        (.app hf' ha') (by simp) (by simp) (by simp)
      · intro _ hP he
        have ⟨he, hlm⟩ := FVarsIn.appRevList.1 he
        exact (hb _ hP <| (hbelow _ hP he).instantiateList hlm).2
      exact .inst henv hΔ (ha'.defeqU_r henv hΔ ⟨_, uA.symm⟩) ⟨_, hbody, _, uB⟩ (ha.trExpr henv hΔ)
  | nil =>
    rw [← List.length_reverse, List.take_length, Expr.instantiateRevList_reverse]
    have ⟨_, hfty, h2⟩ := hfty
    refine .pure ⟨_, _, fun _ hP he => ?_, stk.tr, hfty, hety.defeqU_r henv hΔ h2.symm⟩
    have ⟨he, hlm⟩ := FVarsIn.appRevList.1 he
    exact (hbelow _ hP he).instantiateList hlm

theorem inferApp.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (inferApp e) fun ty _ => ∃ ty', c.TrTyping e ty e' ty' := by
  rw [inferApp, Expr.withApp_eq, Expr.getAppArgs_eq]
  have ⟨_, he'⟩ := AppStack.build <| e.mkAppList_getAppArgsList ▸ he
  refine (inferType.WF he'.tr).bind fun ty _ _ ⟨ty', hb, _, hty', ety⟩ => ?_
  have henv := c.Ewf; have hΔ := c.Δwf
  refine (inferApp.loop.WF (ll := []) (lm := []) he' hb
      (hty'.trExpr henv hΔ) ety rfl rfl rfl).le
    fun _ _ _ ⟨_, _, hb, h1, h2, h3⟩ => ?_
  have := (e.mkAppList_getAppArgsList ▸ h1).uniq henv (.refl henv hΔ) he
  exact ⟨_, e.mkAppList_getAppArgsList ▸ hb, he, h2, h3.defeqU_l henv hΔ this⟩

theorem inferLet.loop.WF {c : VContext} {e₀ : Expr}
    {m} [mwf : c.MLCWF m] {n} (hn : n ≤ m.length) (nds hnds)
    (hdrop : m.dropN n hn = c.mlctx)
    (harr : arr.toList.reverse = (m.fvarRevList n hn).map .fvar)
    (he₀ : e₀ = m.mkLet n hn nds hnds ei)
    (hei : e.instantiateList ((m.fvarRevList n hn).map .fvar) = ei)
    (hbelow : ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P e₀ →
      IsFVarUpSet (AllAbove c.vlctx P) m.vlctx ∧ FVarsIn (AllAbove c.vlctx P) ei ∧
      ∀ ty, FVarsIn (AllAbove c.vlctx P) ty → FVarsIn (AllAbove c.vlctx P) (m.mkForall n hn ty))
    (hr : e.FVarsIn (· ∈ m.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', (c.withMLC m).TrExprS ei e') :
    (inferLet.loop inferOnly arr e).WF (c.withMLC m) s fun ty _ =>
      ∃ e' ty', c.TrTyping e₀ ty e' ty' := by
  generalize eqfvs : (m.fvarRevList n hn).map Expr.fvar = fvs at *
  unfold inferLet.loop
  simp [harr, -bind_pure_comp]; split
  · rename_i name dom val body nd
    generalize eqF : withLetDecl (m := RecM) _ _ _ _ = F
    generalize eqP : (fun ty x => ∃ _, _) = P
    rw [Expr.instantiateList_letE] at hei; subst ei
    have main {s₁} (le₁ : s ≤ s₁) {dom' val'}
        (hdom : (c.withMLC m).TrExprS (dom.instantiateList fvs) dom')
        (hval : (c.withMLC m).TrExprS (val.instantiateList fvs) val')
        (valty : (c.withMLC m).venv.HasType
          (c.withMLC m).lparams.length (c.withMLC m).vlctx.toCtx val' dom')
        (hbody : inferOnly = true → ∃ body',
          TrExprS c.venv c.lparams ((none, .vlet dom' val') :: m.vlctx)
            (body.instantiateList fvs 1) body') :
        F.WF (c.withMLC m) s₁ P := by
      refine .stateWF fun wf => ?_
      have hdom' := hdom.trExpr c.Ewf mwf.1.tr.wf
      subst eqF eqP
      refine .withLetDecl hdom hval valty le₁ fun a mwf' s' le₂ res => ?_
      have eq := @Expr.instantiateList_instantiate1_comm body fvs (.fvar a) (by trivial)
      refine inferLet.loop.WF (Nat.succ_le_succ hn) (some nd :: nds)
        (by simp [hnds]) (by simp [hdrop]) (by simp [← eqfvs, harr])
        ?_ (by simp; rfl) ?_ (hr.2.2.mono fun _ => .tail _) ?_
      · rw [he₀, eqfvs, ← eq]; simp [MLCtx.mkLetArg]; congr 2
        refine (FVarsIn.abstract_instantiate1 ((hr.2.2.instantiateList ?_ _).mono ?_)).symm
        · simp [← eqfvs, FVarsIn]; exact m.fvarRevList_prefix.subset
        · rintro _ h rfl; exact (mwf'.1.tr.wf.2.1 _ _ rfl).1 h
      · intro P hP he
        have ⟨h1, h2, h3⟩ := hbelow _ hP he
        refine ⟨⟨h1, fun _ => ?_⟩, ?_, fun ty hty => h3 _ ?_⟩
        · simp [or_imp, forall_and]
          exact ⟨(fvarsIn_iff.1 h2.1).1, (fvarsIn_iff.1 h2.2.1).1⟩
        · rw [eqfvs, ← eq]
          refine h2.2.2.instantiate1 fun h => ?_
          exact res.elim (wf.ngen_wf _ (m.dropN_fvars_subset n hn (hdrop ▸ h)))
        · simp; split <;> rename_i h
          · exact ⟨h2.1, h2.2.1, hty.abstract1⟩
          · rw [Expr.lowerLooseBVars_eq_instantiate (v := .sort .zero) (by simpa using h)]
            exact hty.abstract1.instantiate1 rfl
      · intro h; let ⟨_, hbody⟩ := hbody h
        exact eqfvs.symm ▸ eq ▸ ⟨_, hbody.inst_fvar c.Ewf.ordered mwf'.1.tr.wf⟩
    split
    · subst inferOnly
      refine (checkType.WF ?_).bind fun uv _ le ⟨dom', uv', _, h1, h2, h3⟩ => ?_
      · apply hr.1.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
      refine (ensureSortCore.WF h2).bind
        fun _ _ le₂ ⟨h4, h5, _⟩ => ?_
      obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort _, h5⟩ := h5; have le := le.trans le₂
      refine (checkType.WF ?_).bind_le le fun ty _ le ⟨val', ty', _, h4, h5, h6⟩ => ?_
      · apply hr.2.1.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
      refine (isDefEq.WF h5 h1).bind_le le fun b _ le h7 => ?_
      cases b <;> simp
      · exact .getEnv <| .getLCtx .throw
      have valty := h6.defeqU_r c.Ewf mwf.1.tr.wf.toCtx (h7 rfl)
      exact main le h1 h4 valty nofun
    · simp_all; let ⟨_, h1⟩ := hinf
      have .letE (ty' := dom') (body' := body') valty hdom hval hbody := h1
      exact main .rfl hdom hval valty _ hbody
  · subst ei; refine (inferType.WF' ?_ hinf).bind fun ty _ _ ⟨e', ty', hb, h1, h2, h3⟩ => ?_
    · apply hr.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
    refine .stateWF fun wf => .getLCtx <| .pure ?_
    have ⟨_, hty, e2⟩ := h2.trExpr c.Ewf.ordered wf.trctx.wf
      |>.cheapBetaReduce c.Ewf wf.trctx.wf m.noBV
    have h3 := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx e2.symm
    let ⟨h1', h2'⟩ := mwf.1.mkLet_trS c.Ewf h1 h3 n hn nds hnds
    have h3' := (mwf.1.mkForall_trS c.Ewf hty (h3.isType c.Ewf mwf.1.tr.wf.toCtx) n hn).1
    simp [hdrop] at h1' h2' h3'
    erw [mwf.1.mkForall_eq _ _ (eqfvs ▸ harr)]
    refine ⟨_, _, fun P hP he => ?_, he₀ ▸ h1', h3', h2'⟩
    have ⟨c1, c2, c3⟩ := hbelow _ hP he
    have := c3 _ <| FVarsBelow.cheapBetaReduce (m.noBV ▸ h2.closed) _ c1 <| hb _ c1 c2
    refine this.mp (fun _ => id) h3'.fvarsIn
termination_by e

theorem inferLet.WF
    (hr : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferLet e inferOnly).WF c s fun ty _ =>
      ∃ e' ty', c.TrTyping e ty e' ty' := by
  refine .stateWF fun wf => ?_
  refine (c.withMLC_self ▸ inferLet.loop.WF (Nat.zero_le _) [] rfl rfl rfl rfl rfl ?_ hr) hinf
  exact fun P hP he => ⟨(AllAbove.wf wf.trctx.wf.fvwf).2 hP, he.mono fun _ h _ => h, fun _ => id⟩

theorem AppStack.toSpineWF {c : VContext}
    (H : AppStack c.venv c.lparams c.vlctx f f' args)
    (hf : c.HasType f' (VExpr.forallN As C))
    (hlen : args.length = As.length) :
    ∃ args', args.Forall₂ (c.TrExprS · ·) args' ∧
      c.venv.SpineWF c.lparams.length c.vlctx.toCtx
        (VExpr.forallN As C) args' (VExpr.instRev C args') ∧
      c.TrExprS (f.mkAppList args) (VExpr.appN f' args') := by
  induction args generalizing f f' As C with
  | nil =>
      cases As with
      | nil =>
          let .head hfull := H
          exact ⟨[], .nil, .nil, by simpa⟩
      | cons _ _ => simp at hlen
  | cons arg args ih =>
      cases As with
      | nil => simp at hlen
      | cons A As =>
        let .app hfun harg hf' harg' Hrest := H
        have htypes := hf.uniqU c.Ewf c.Δwf hfun
        have ⟨⟨_, hA⟩, _⟩ := htypes.forallE_inv c.Ewf c.Δwf
        have hargA := harg.defeqU_r c.Ewf c.Δwf ⟨_, hA.symm⟩
        have hlen' : args.length = As.length := by simpa using hlen
        have htailType : c.HasType (.app f' _) ((VExpr.forallN As C).inst _) :=
          hf.app hargA
        rw [VExpr.instN_forallN] at htailType
        obtain ⟨args', hargs', hspine, hfull⟩ :=
          ih Hrest htailType (by simpa [VExpr.instTelN_length] using hlen')
        refine ⟨_ :: args', .cons harg' hargs', .cons hargA ?_, ?_⟩
        have hlenArgsAs : args'.length = As.length :=
          hargs'.length_eq.symm.trans hlen'
        rw [VExpr.instN_forallN]
        simpa [VExpr.instRev, hlenArgsAs] using hspine
        simpa [Expr.mkAppList, VExpr.appN] using hfull

theorem invalidProj.WF {c : VContext} {s : VState} :
    (invalidProj e : RecM α).WF c s Q := by
  unfold invalidProj
  exact .getEnv <| .getLCtx .throw

theorem inferProjParams.WF {c : VContext} {s : VState}
    (hargs : args.Forall₂ (c.TrExprS · ·) args')
    (hrBelow : c.FVarsBelow proj r)
    (hargsBelow : ∀ arg ∈ args, c.FVarsBelow proj arg)
    (hr : c.TrExpr r R)
    (hspine : c.venv.SpineWF c.lparams.length c.vlctx.toCtx
      R args' T) :
    (inferProjParams proj args r).WF c s fun out _ =>
      c.FVarsBelow proj out ∧ c.TrExpr out T := by
  induction hargs generalizing r R s with
  | nil =>
      simp [inferProjParams] at hspine ⊢
      exact hspine.nil_inv ▸ .pure ⟨hrBelow, hr⟩
  | @cons arg arg' args args' harg hargs ih =>
      simp only [inferProjParams]
      have hargBelow := hargsBelow arg (by simp)
      have hargsBelow' : ∀ arg ∈ args, c.FVarsBelow proj arg := by
        intro arg harg
        exact hargsBelow arg (by simp [harg])
      obtain ⟨A, B, rfl, hargType, hrest⟩ := hspine.cons_inv
      obtain ⟨r', hrS, hrEq⟩ := hr
      refine (whnf.WF hrS).bind fun out s' _
        ⟨houtBelow, ⟨out', hout, houtEq⟩⟩ => ?_
      have houtEq := houtEq.trans c.Ewf c.Δwf hrEq
      cases out with
      | forallE name dom body bi =>
        let .forallE hdomTy hbodyTy hdom hbody := hout
        have hforallEq := houtEq.forallE_inv c.Ewf c.Δwf
        obtain ⟨⟨_, hdomEq⟩, _, hbodyEq⟩ := hforallEq
        have hargType' := hargType.defeqU_r c.Ewf c.Δwf
          ⟨_, hdomEq.symm⟩
        have hnext : c.TrExpr (body.instantiate1 arg) (B.inst arg') := by
          simpa only [Expr.instantiate1_eq] using
            (.inst c.Ewf c.Δwf hargType'
              ⟨_, hbody, _, hbodyEq⟩ (harg.trExpr c.Ewf c.Δwf))
        have hnextBelow : c.FVarsBelow proj (body.instantiate1 arg) := by
          intro P hP hproj
          have houtFVars := (hrBelow.trans houtBelow) P hP hproj
          simpa only [Expr.instantiate1_eq] using
            houtFVars.2.instantiate1 (hargBelow P hP hproj)
        exact ih hnextBelow hargsBelow' hnext hrest
      | bvar | fvar | mvar | sort | const | app | lam | letE | lit |
          mdata | proj => exact invalidProj.WF

theorem inferProjFields.WF {c : VContext} {s : VState}
    {view : VStructureView} {levels : List VLevel}
    {params : List VExpr} {major : VExpr} {tailResult cursor : VExpr}
    (hstruct : c.TrExprS struct major)
    (hview : view.WF c.venv)
    (hlevels : ∀ level ∈ levels, level.WF c.lparams.length)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      c.venv.SpineWF c.lparams.length c.vlctx.toCtx
        (view.familyType.instL levels) params (.sort resultLevel))
    (hprograms : view.ProgramsWF c.venv)
    (hname : view.name = typeName)
    (hmajor : c.HasType major (view.structureType levels params))
    (hrBelow : c.FVarsBelow proj r)
    (hstructBelow : c.FVarsBelow proj struct)
    (hbound : fieldIdx + count <
      (view.specializedFields levels params).length)
    (hr : c.TrExpr r cursor)
    (hcursor : VExpr.consumeForalls?
      (VExpr.forallN (view.specializedFields levels params) tailResult)
      (view.projectionArgs levels params fieldIdx major) = some cursor) :
    (inferProjFields proj typeName struct maybePropType fieldIdx count r).WF
      c s fun out _ =>
        ∃ cursor',
          VExpr.consumeForalls?
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.projectionArgs levels params (fieldIdx + count) major) =
              some cursor' ∧
          c.FVarsBelow proj out ∧ c.TrExpr out cursor' := by
  induction count generalizing s r cursor fieldIdx with
  | zero =>
      simp only [inferProjFields, Nat.add_zero]
      exact .pure ⟨cursor, hcursor, hrBelow, hr⟩
  | succ count ih =>
      simp only [inferProjFields]
      have hfieldIdx : fieldIdx <
          (view.specializedFields levels params).length := by omega
      have hcodeIdx : fieldIdx <
          (view.projectionCodes levels params).length := by
        simpa using hfieldIdx
      let code := (view.projectionCodes levels params)[fieldIdx]
      have hcode :
          (view.projectionCodes levels params)[fieldIdx]? = some code :=
        List.getElem?_eq_getElem hcodeIdx
      have hargsLength :
          (view.projectionArgs levels params fieldIdx major).length =
            fieldIdx :=
        view.projectionArgs_length levels params fieldIdx major
          (Nat.le_of_lt hcodeIdx)
      obtain ⟨field, semanticBody, hfield, hconsume⟩ :=
        VExpr.consumeForalls?_forallN_domain
          (view.specializedFields levels params) tailResult
          (view.projectionArgs levels params fieldIdx major)
          (by simpa [hargsLength] using hfieldIdx)
      rw [hargsLength] at hfield
      have hcursorShape : cursor =
          .forallE
            (field.instRevAt
              (view.projectionArgs levels params fieldIdx major) 0)
            semanticBody :=
        Option.some.inj (hcursor.symm.trans hconsume)
      subst cursor
      obtain ⟨field', typeBody, hfield', htypeFn,
          hprojectorField⟩ :=
        hprograms.projector_hasType_field c.Ewf c.Δwf hlevels
          hlevelsLength hparamsLength hparamsSpine hcode hmajor
      have hfieldEq : field' = field :=
        Option.some.inj (hfield'.symm.trans hfield)
      subst field'
      have hprojector := hprograms c.Δwf hlevels hlevelsLength
        hparamsLength hparamsSpine hcode
      have hprojSem : c.venv.TrProj c.lparams.length c.vlctx.toCtx
          view levels params fieldIdx major (.app code.projector major) := {
        viewWF := hview
        levelsWF := hlevels
        levels_length := hlevelsLength
        params_length := hparamsLength
        paramsSpine := hparamsSpine
        majorType := hmajor
        program := ⟨code, hcode, rfl, hprojector⟩ }
      have hprojStrict : c.TrExprS (.proj typeName fieldIdx struct)
          (.app code.projector major) :=
        .proj hstruct ⟨view, levels, params, hname, hprojSem⟩
      obtain ⟨r', hrS, hrEq⟩ := hr
      refine (whnf.WF hrS).bind fun out nextState _
        ⟨houtBelow, ⟨out', hout, houtEq⟩⟩ => ?_
      have houtEq := houtEq.trans c.Ewf c.Δwf hrEq
      cases out with
      | forallE name dom body bi =>
        let .forallE hdomTy hbodyTy hdom hbody := hout
        have hforallEq := houtEq.forallE_inv c.Ewf c.Δwf
        obtain ⟨⟨_, hdomEq⟩, _, hbodyEq⟩ := hforallEq
        have hprojectorField' := hprojectorField.defeqU_r
          c.Ewf c.Δwf ⟨_, hdomEq.symm⟩
        have hnext : c.TrExpr
            (body.instantiate1 (.proj typeName fieldIdx struct))
            (semanticBody.inst (.app code.projector major)) := by
          simpa only [Expr.instantiate1_eq] using
            (.inst c.Ewf c.Δwf hprojectorField'
              ⟨_, hbody, _, hbodyEq⟩
              (hprojStrict.trExpr c.Ewf.ordered c.Δwf))
        have hnextBelow : c.FVarsBelow proj
            (body.instantiate1 (.proj typeName fieldIdx struct)) := by
          intro P hP hproj
          have houtFVars := (hrBelow.trans houtBelow) P hP hproj
          have hfieldProj : FVarsIn P
              (.proj typeName fieldIdx struct) := by
            simpa [FVarsIn] using hstructBelow P hP hproj
          simpa only [Expr.instantiate1_eq] using
            houtFVars.2.instantiate1 hfieldProj
        have hconsumeNext : VExpr.consumeForalls?
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.projectionArgs levels params (fieldIdx + 1) major) =
              some (semanticBody.inst (.app code.projector major)) := by
          rw [view.projectionArgs_succ levels params fieldIdx major hcode]
          rw [VExpr.consumeForalls?_append, hconsume]
          rfl
        have hbound' : fieldIdx + 1 + count <
            (view.specializedFields levels params).length := by omega
        have hrec (recState : VState) :=
          ih (s := recState) hnextBelow hbound' hnext hconsumeNext
        simp only
        split
        · refine (isProp.WF hdom).bind fun _ propState _ _ => ?_
          split
          · exact invalidProj.WF
          · simpa only [pure_bind, Nat.add_assoc, Nat.add_left_comm,
              Nat.add_comm] using hrec propState
        · simpa only [pure_bind, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using hrec nextState
      | bvar | fvar | mvar | sort | const | app | lam | letE | lit |
          mdata | proj => exact invalidProj.WF

theorem inferProj.WF
    (heBelow : c.FVarsBelow e ety)
    (he : c.TrExprS e e') (hty : c.TrExprS ety ety')
    (hasty : c.HasType e' ety') :
    (inferProj st i e ety).WF c s fun ty _ =>
      ∃ proj' ty', c.TrTyping (.proj st i e) ty proj' ty' := by
  unfold inferProj
  refine (whnf.WF hty).bind fun type _ _ ⟨htypeBelow, htype⟩ => ?_
  have hprojBelowType : c.FVarsBelow (.proj st i e) type := by
    intro P hP hproj
    exact htypeBelow P hP (heBelow P hP (by simpa [FVarsIn] using hproj))
  obtain ⟨type', htypeS, htypeEq⟩ := htype
  rw [Expr.withApp_eq]
  have ⟨family', hstack⟩ := AppStack.build
    (type.mkAppList_getAppArgsList ▸ htypeS)
  simp only
  split
  · rename_i familyName familyLevels hfamilyShape
    refine .getEnv ?_
    split
    · exact invalidProj.WF
    · rename_i hname
      refine (M.WF.liftExcept envGet.WF).lift.bind fun ci _ _ hfind => ?_
      split
      · rename_i info
        split
        · rename_i constructor hctors
          split
          · rename_i hready
            split
            · exact invalidProj.WF
            · rename_i hargs
              obtain ⟨artifact⟩ :=
                c.projectionReady.infer familyName info hfind hready
              have hhead := hstack.tr
              rw [hfamilyShape] at hhead
              let .const (us' := levels') hfamilyConst hlevelsMap
                hlevelsLength := hhead
              have hviewFamily := artifact.viewWF.family
              rw [artifact.name_eq] at hviewFamily
              rw [hviewFamily] at hfamilyConst
              cases hfamilyConst
              have hlevelsWF : ∀ level ∈ levels',
                  level.WF c.lparams.length :=
                VLevel.WF.of_mapM_ofLevel hlevelsMap
              have hlevelsSourceLength : levels'.length =
                  artifact.view.generation.block.sourceType.uvars :=
                (List.mapM_eq_some.1 hlevelsMap).length_eq.symm.trans
                  hlevelsLength
              have hlevelsLength' : levels'.length = artifact.view.uvars := by
                exact hlevelsSourceLength.trans
                    artifact.view.generation.block.sourceType_uvars_eq
              have hargsSize : type.getAppArgs.size =
                  info.numParams + info.numIndices := by
                simpa using hargs
              have hargsLength : type.getAppArgsList.length =
                  artifact.view.nparams := by
                rw [← Expr.getAppArgs_toList]
                simp [hargsSize,
                  artifact.numParams_eq, artifact.numIndices_eq]
              have hfamilyType : c.HasType (.const familyName levels')
                  (artifact.view.familyType.instL levels') := by
                exact VEnv.HasType.const hviewFamily hlevelsWF
                  hlevelsSourceLength
              have hfamilyTypeShape : c.HasType (.const familyName levels')
                  (VExpr.forallN
                    (artifact.view.generation.block.rawParams.map
                      (VExpr.instL levels'))
                    (artifact.view.generation.block.rawResult.instL
                      levels')) := by
                simpa [VStructureView.familyType,
                  VInductDecl.NormalizedChecked.rawType_eq,
                  artifact.view.raw_indices_eq,
                  VExpr.instL_forallN, VExpr.forallN] using hfamilyType
              have hargsRawLength : type.getAppArgsList.length =
                  (artifact.view.generation.block.rawParams.map
                    (VExpr.instL levels')).length := by
                simpa [artifact.view.generation.shape.1] using hargsLength
              obtain ⟨params', hparamsTr, hparamsSpineRaw, htypeFull⟩ :=
                AppStack.toSpineWF hstack hfamilyTypeShape hargsRawLength
              rw [type.mkAppList_getAppArgsList] at htypeFull
              have htypeAppliedEq := htypeFull.uniq c.Ewf
                (.refl c.Ewf c.Δwf) htypeS
              have hmajorType : c.HasType e'
                  (artifact.view.structureType levels' params') := by
                apply hasty.defeqU_r c.Ewf c.Δwf
                have := (htypeAppliedEq.trans c.Ewf c.Δwf htypeEq).symm
                simpa [VStructureView.structureType,
                  artifact.name_eq] using this
              have hparamsLength : params'.length =
                  artifact.view.nparams :=
                hparamsTr.length_eq.symm.trans hargsLength
              have hparamsRawLength : params'.length =
                  (artifact.view.generation.block.rawParams.map
                    (VExpr.instL levels')).length :=
                hparamsTr.length_eq.symm.trans hargsRawLength
              have hparamsSpine : ∃ resultLevel,
                  c.venv.SpineWF c.lparams.length c.vlctx.toCtx
                    (artifact.view.familyType.instL levels') params'
                    (.sort resultLevel) := by
                obtain ⟨resultLevel, hresultLevel⟩ := artifact.rawResult_sort
                refine ⟨resultLevel.inst levels', ?_⟩
                rw [hresultLevel] at hparamsSpineRaw
                rw [VExpr.instRev_closedN params' (by trivial)] at hparamsSpineRaw
                simpa [VStructureView.familyType,
                  VInductDecl.NormalizedChecked.rawType_eq,
                  artifact.view.raw_indices_eq, hresultLevel,
                  VExpr.instL_forallN, VExpr.forallN,
                  VExpr.instRev, VExpr.instL] using hparamsSpineRaw
              have hconstructorName :
                  constructor = artifact.view.constructorName := by
                have := hctors.symm.trans artifact.ctors_eq
                simpa using this
              refine (M.WF.liftExcept envGet.WF).lift.bind
                fun c_info _ _ hctorFind => ?_
              cases c_info with
              | ctorInfo ctorInfo =>
                simp only
                split
                · rename_i hidxHost
                  have hctorInfoEq :
                      ctorInfo = artifact.constructorInfo := by
                    rw [hconstructorName, artifact.constructor_find] at hctorFind
                    exact ConstantInfo.ctorInfo.inj
                      (Option.some.inj hctorFind.symm)
                  have hiFields : i <
                      (artifact.view.specializedFields levels' params').length := by
                    rw [hctorInfoEq,
                      artifact.constructor_numFields_eq] at hidxHost
                    simpa [VStructureView.specializedFields,
                      VStructureView.fields] using hidxHost
                  have hviewConstructor : c.venv.constants constructor =
                      some artifact.view.constructor.raw.toVConstant := by
                    simpa [hconstructorName] using
                      artifact.viewWF.toRegistered.constructor
                  obtain ⟨_, hctorTr⟩ :=
                    c.trenv.find?_uniq hctorFind hviewConstructor
                  have hrawCtorUvars :
                      artifact.view.constructor.raw.uvars =
                        artifact.view.uvars := by
                    exact artifact.view.generation.ctor_uvars_eq
                      (by simp [artifact.view.constructor_eq])
                  have hctorLevelLength :
                      ctorInfo.levelParams.length = familyLevels.length :=
                    hctorTr.2.1.trans <| hrawCtorUvars.trans <|
                      hlevelsLength'.symm.trans
                        (List.mapM_eq_some.1 hlevelsMap).length_eq.symm
                  have hctorType₀ := hctorTr.2.2.instL c.Ewf
                    (Us := c.lparams) (ls' := levels') (Δ := [])
                    trivial hlevelsMap hctorLevelLength
                  have hctorType := hctorType₀.weakFV c.Ewf
                    (.from_nil c.mlctx.noBV) c.Δwf
                  rw [(c.Ewf.ordered.closedC
                    hviewConstructor).instL.liftN_eq
                      (Nat.le_refl _)] at hctorType
                  let ctorTail := VExpr.forallN
                    (artifact.view.fields.map (VExpr.instL levels'))
                    ((artifact.view.constructor.rawResult
                      artifact.view.nparams).instL levels')
                  rw [artifact.view.constructor.rawType_eq] at hctorType
                  have hinstantiate :
                      ((.ctorInfo ctorInfo : ConstantInfo)
                        |>.instantiateTypeLevelParams familyLevels) =
                      ctorInfo.type.instantiateLevelParams
                        ctorInfo.levelParams familyLevels := rfl
                  have hctorTypeShape : c.TrExpr
                      ((.ctorInfo ctorInfo : ConstantInfo)
                        |>.instantiateTypeLevelParams familyLevels)
                      (VExpr.forallN
                        (artifact.view.constructorParams.map
                          (VExpr.instL levels')) ctorTail) := by
                    simpa [ConstantInfo.instantiateTypeLevelParams,
                      ConstantVal.instantiateTypeLevelParams,
                      ConstantInfo.type, ConstantInfo.toConstantVal, ctorTail,
                      VInductDecl.NormalizedCtor.declaredBinders,
                      VStructureView.nparams,
                      VStructureView.constructorParams,
                      VStructureView.fields,
                      VExpr.instL_forallN, VExpr.forallN_append,
                      List.map_append] using hctorType
                  have hctorTypeBelow : c.FVarsBelow (.proj st i e)
                      ((.ctorInfo ctorInfo : ConstantInfo)
                        |>.instantiateTypeLevelParams familyLevels) := by
                    intro P _ _
                    simpa [ConstantInfo.instantiateTypeLevelParams,
                      ConstantVal.instantiateTypeLevelParams,
                      ConstantInfo.type, ConstantInfo.toConstantVal] using
                        hctorType₀.fvarsIn.mono nofun
                  have hparamArgsEq :
                      List.take info.numParams type.getAppArgs.toList =
                        type.getAppArgsList := by
                    simp [Expr.getAppArgs_toList, artifact.numParams_eq,
                      ← hargsLength]
                  have hparamArgsTr :
                      (List.take info.numParams
                        type.getAppArgs.toList).Forall₂
                        (c.TrExprS · ·) params' := by
                    simpa [hparamArgsEq] using hparamsTr
                  have hparamArgsBelow : ∀ arg ∈
                      List.take info.numParams type.getAppArgs.toList,
                      c.FVarsBelow (.proj st i e) arg := by
                    intro arg harg P hP hproj
                    apply FVarsIn.getAppArgsList
                      (hprojBelowType P hP hproj)
                    simpa [hparamArgsEq] using harg
                  have hctorParamsSpine :=
                    artifact.viewWF.constructorParamsSpine c.Ewf.ordered
                      levels' hlevelsWF hlevelsLength' params' hparamsLength
                      hparamsSpine ctorTail
                  refine (inferProjParams.WF hparamArgsTr hctorTypeBelow
                    hparamArgsBelow hctorTypeShape hctorParamsSpine).bind
                      fun r _ _ hr => ?_
                  obtain ⟨hrBelow, hr⟩ := hr
                  let tailResult :=
                    ((artifact.view.constructor.rawResult
                      artifact.view.nparams).instL levels').instRevAt
                        params' artifact.view.fields.length
                  have hctorTailInst : ctorTail.instRev params' =
                      VExpr.forallN
                        (artifact.view.specializedFields levels' params')
                        tailResult := by
                    simp [ctorTail, tailResult,
                      VExpr.instRev_forallN_projection,
                      VStructureView.specializedFields,
                      VExpr.instRevAt_map_instL_zipIdx]
                  rw [hctorTailInst] at hr
                  refine (getSortLevel.WF htypeS).bind
                    fun sortLevel nextState _ _ => ?_
                  have hstructBelow : c.FVarsBelow (.proj st i e) e := by
                    intro P _ hproj
                    simpa [FVarsIn] using hproj
                  have hcursorZero : VExpr.consumeForalls?
                      (VExpr.forallN
                        (artifact.view.specializedFields levels' params')
                        tailResult)
                      (artifact.view.projectionArgs levels' params' 0 e') =
                        some (VExpr.forallN
                          (artifact.view.specializedFields levels' params')
                          tailResult) := by
                    rfl
                  refine (inferProjFields.WF he artifact.viewWF hlevelsWF
                    hlevelsLength' hparamsLength hparamsSpine
                    artifact.programsWF artifact.name_eq hmajorType
                    hrBelow hstructBelow (by simpa using hiFields) hr
                    hcursorZero).bind
                      fun r _ _ hr => ?_
                  obtain ⟨cursor, hcursor, hrBelow, hr⟩ := hr
                  have hcursor' : VExpr.consumeForalls?
                      (VExpr.forallN
                        (artifact.view.specializedFields levels' params')
                        tailResult)
                      (artifact.view.projectionArgs levels' params' i e') =
                        some cursor := by
                    simpa using hcursor
                  have hcodeIdx : i <
                      (artifact.view.projectionCodes levels' params').length := by
                    simpa using hiFields
                  let code :=
                    (artifact.view.projectionCodes levels' params')[i]
                  have hcode :
                      (artifact.view.projectionCodes levels' params')[i]? =
                        some code :=
                    List.getElem?_eq_getElem hcodeIdx
                  have hprojectionArgsLength :
                      (artifact.view.projectionArgs levels' params' i e').length =
                        i :=
                    artifact.view.projectionArgs_length levels' params' i e'
                      (Nat.le_of_lt hcodeIdx)
                  obtain ⟨field, semanticBody, hfield, hconsume⟩ :=
                    VExpr.consumeForalls?_forallN_domain
                      (artifact.view.specializedFields levels' params')
                      tailResult
                      (artifact.view.projectionArgs levels' params' i e')
                      (by simpa [hprojectionArgsLength] using hiFields)
                  rw [hprojectionArgsLength] at hfield
                  have hcursorShape : cursor =
                      .forallE
                        (field.instRevAt
                          (artifact.view.projectionArgs levels' params' i e') 0)
                        semanticBody :=
                    Option.some.inj (hcursor'.symm.trans hconsume)
                  subst cursor
                  have hprograms : artifact.view.ProgramsWF c.venv :=
                    artifact.programsWF
                  obtain ⟨field', typeBody, hfield', htypeFn,
                      hprojectorField⟩ :=
                    hprograms.projector_hasType_field
                      c.Ewf c.Δwf hlevelsWF hlevelsLength' hparamsLength
                      hparamsSpine hcode hmajorType
                  have hfieldEq : field' = field :=
                    Option.some.inj (hfield'.symm.trans hfield)
                  subst field'
                  have hprojector := hprograms c.Δwf hlevelsWF
                    hlevelsLength' hparamsLength hparamsSpine hcode
                  have hprojSem : c.venv.TrProj c.lparams.length
                      c.vlctx.toCtx artifact.view levels' params' i e'
                      (.app code.projector e') := {
                    viewWF := artifact.viewWF
                    levelsWF := hlevelsWF
                    levels_length := hlevelsLength'
                    params_length := hparamsLength
                    paramsSpine := hparamsSpine
                    majorType := hmajorType
                    program := ⟨code, hcode, rfl, hprojector⟩ }
                  have hst : st = familyName := by
                    simpa using hname
                  have hprojStrict : c.TrExprS (.proj st i e)
                      (.app code.projector e') :=
                    .proj he ⟨artifact.view, levels', params',
                      artifact.name_eq.trans hst.symm, hprojSem⟩
                  obtain ⟨r', hrS, hrEq⟩ := hr
                  refine (whnf.WF hrS).bind fun out _ _
                    ⟨houtBelow, ⟨out', hout, houtEq⟩⟩ => ?_
                  have houtEq := houtEq.trans c.Ewf c.Δwf hrEq
                  cases out with
                  | forallE name dom body bi =>
                    let .forallE hdomTy hbodyTy hdom hbody := hout
                    have hforallEq := houtEq.forallE_inv c.Ewf c.Δwf
                    obtain ⟨⟨_, hdomEq⟩, _, hbodyEq⟩ := hforallEq
                    have hprojectorField' := hprojectorField.defeqU_r
                      c.Ewf c.Δwf ⟨_, hdomEq.symm⟩
                    have hdomBelow : c.FVarsBelow (.proj st i e) dom := by
                      intro P hP hproj
                      exact ((hrBelow.trans houtBelow) P hP hproj).1
                    have hresult : ∃ proj' ty',
                        c.TrTyping (.proj st i e) dom proj' ty' :=
                      ⟨.app code.projector e', _, hdomBelow, hprojStrict,
                        hdom, hprojectorField'⟩
                    simp only
                    split
                    · refine (isProp.WF hdom).bind fun _ _ _ _ => ?_
                      split
                      · exact invalidProj.WF
                      · exact .pure hresult
                    · exact .pure hresult
                  | bvar | fvar | mvar | sort | const | app | lam | letE |
                      lit | mdata | proj => exact invalidProj.WF
                · exact invalidProj.WF
              | axiomInfo | defnInfo | thmInfo | opaqueInfo | quotInfo |
                  inductInfo | recInfo => exact invalidProj.WF
          · exact invalidProj.WF
        · exact invalidProj.WF
      · exact invalidProj.WF
  · exact invalidProj.WF

theorem literal_is_primitive (H : n = ``Nat ∨ n = ``Char.ofNat ∨ n = ``String.ofList)  :
    Environment.primitives.contains n := by
  simp [Environment.primitives, NameSet.ofList]
  obtain rfl|rfl|rfl := H <;> simp +decide [NameSet.contains]

theorem infer_literal {c : VContext} (H : c.venv.ContainsLits l) :
    c.TrTyping (.lit l) l.type (.trLiteral l) (.const l.typeName []) := by
  refine
    have := TrExprS.trLiteral c.Ewf c.hasPrimitives l H
    ⟨fun _ _ _ => .litType, this.1, ?_, this.2⟩
  rw [← Literal.mkConst_typeName]
  have ⟨_, h⟩ := this.2.isType c.Ewf c.Δwf
  have ⟨_, h1, _, h3⟩  := h.const_inv c.Ewf c.Δwf
  exact .const h1 rfl h3

theorem infer_sort {c : VContext} (H : VLevel.ofLevel c.lparams u = some u') :
    c.TrTyping (.sort u) (.sort u.succ) (.sort u') (.sort u'.succ) := by
  refine ⟨fun _ _ _ => (?a).fvarsIn, .sort H, ?a, .sort (.of_ofLevel H)⟩
  exact .sort <| by simpa [VLevel.ofLevel]

theorem inferType'.WF
    (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferType' e inferOnly).WF c s fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty' := by
  unfold inferType'; lift_lets; intro F F1
  split <;> [exact .throw; refine .get <| .get ?_]
  split
  · rename_i h; refine .stateWF fun wf => .pure ?_
    generalize hic : cond .. = ic at h
    have : ic.WF c s := by
      subst ic; cases inferOnly <;> [exact wf.inferTypeC_wf; exact wf.inferTypeI_wf]
    exact (this h).2.2.2.2 h1
  generalize hP : (fun _ (_ : VState) => _) = P
  have hF {ty e' ty' s} (H : c.TrTyping e ty e' ty') : (F ty).WF c s P := by
    rintro _ mwf wf a s' ⟨⟩
    refine let s' := _; ⟨s', rfl, ?_⟩
    have hic {ic} (hic : InferCache.WF c s ic) : InferCache.WF c s (ic.insert e ty) := by
      intro _ _ h
      rw [Std.HashMap.getElem?_insert] at h; split at h <;> [cases h; exact hic h]
      rename_i eq
      refine .mk c.mlctx.noBV (.eqv H eq BEq.rfl) (.eqv eq ?_) ?_
      · exact H.2.1.fvarsIn.mono wf.ngen_wf
      · exact H.2.2.1.fvarsIn.mono wf.ngen_wf
    subst P; revert s'; cases inferOnly <;> (dsimp -zeta; intro s'; refine ⟨.rfl, ?_, _, _, H⟩)
    · exact { wf with inferTypeC_wf := hic wf.inferTypeC_wf }
    · exact { wf with inferTypeI_wf := hic wf.inferTypeI_wf }
  split
  · extract_lets G1
    refine (checkLitSize.WF (Q := fun _ s' => s' = _) rfl).bind fun _ _ _ h => ?_
    subst h; split <;> [split; skip]
    · refine .getEnv <| (M.WF.liftExcept envGet.WF).lift.bind fun _ _ _ h => ?_
      have ⟨_, h, _⟩ := c.trenv.find? h <|
        (c.safePrimitives h (literal_is_primitive (.inl rfl))).1 ▸ DefinitionSafety.le_safe
      exact hF (infer_literal ⟨_, h⟩)
    · refine .getEnv <| (M.WF.liftExcept envGet.WF).lift.bind fun _ _ _ h1 => ?_
      refine .getEnv <| (M.WF.liftExcept envGet.WF).lift.bind fun _ _ _ h2 => ?_
      have ⟨_, h1, _⟩ := c.trenv.find? h1 <|
        (c.safePrimitives h1 (literal_is_primitive (.inr (.inl rfl)))).1 ▸ DefinitionSafety.le_safe
      have ⟨_, h2, _⟩ := c.trenv.find? h2 <|
        (c.safePrimitives h2 (literal_is_primitive (.inr (.inr rfl)))).1 ▸ DefinitionSafety.le_safe
      exact hF (infer_literal ⟨⟨_, h1⟩, ⟨_, h2⟩⟩)
    · rename_i h; have ⟨_, h⟩ := hinf (by simpa using h)
      have := h.lit_has_type
      simp [G1]; exact hF (infer_literal this)
  · refine (inferType'.WF (by exact h1) ?_).bind fun _ _ _ ⟨_, _, hb, h1, h⟩ => ?_
    · exact fun h => let ⟨_, .mdata h⟩ := hinf h; ⟨_, h⟩
    exact hF ⟨hb, .mdata h1, h⟩
  · refine (inferType'.WF (by exact h1) ?_).bind fun _ _ _ ⟨_, _, hb, h1, h2, h3⟩ => ?_
    · exact fun h => let ⟨_, .proj h ..⟩ := hinf h; ⟨_, h⟩
    exact (inferProj.WF hb h1 h2 h3).bind fun ty _ _ ⟨_, ty', h⟩ => hF h
  · exact .readThe <| (M.WF.liftExcept inferFVar.WF).lift.bind fun _ _ _ ⟨_, _, h⟩ => hF h
  · exact .throw
  · rename_i h _; simp [Expr.hasLooseBVars, Expr.looseBVarRange'] at h
  · split <;> rename_i h
    · refine .readThe <| (M.WF.liftExcept (checkLevel.WF h1)).lift.bind fun _ _ _ ⟨_, h⟩ => ?_
      exact hF (infer_sort h)
    · let ⟨_, .sort h⟩ := hinf (by simpa using h)
      exact hF (infer_sort h)
  · refine .readThe <|
      (M.WF.liftExcept (inferConstant.WF h1 hinf)).lift.bind fun _ _ _ ⟨_, _, h⟩ => hF h
  · exact (inferLambda.WF h1 hinf).bind fun _ _ _ ⟨_, _, h⟩ => hF h
  · exact (inferForall.WF h1 hinf).bind fun _ _ _ ⟨_, _, h⟩ => hF h
  · split <;> rename_i h
    · let ⟨_, h⟩ := hinf h; exact (inferApp.WF h).bind fun _ _ _ ⟨_, h⟩ => hF h
    refine (inferType'.WF h1.1 ?_).bind fun _ _ _ ⟨_, _, hfb, hf1, hf2, hf3⟩ => ?_
    · exact fun h => let ⟨_, .app _ _ h _⟩ := hinf h; ⟨_, h⟩
    refine .stateWF fun wf => ?_
    refine (ensureForallCore.WF hf2).bind fun _ _ _ H => ?_
    obtain ⟨hb, h2, name, dType, body, bi, rfl⟩ := H
    let ⟨_, .forallE (ty' := dType') hl1 hl2 hl3 hl4, hl5⟩ := h2
    extract_lets _ G1
    refine (inferType'.WF h1.2 ?_).bind fun aType _ _ ⟨_, aType', hab, ha1, ha2, ha3⟩ => ?_
    · exact fun h => let ⟨_, .app _ _ _ h⟩ := hinf h; ⟨_, h⟩
    extract_lets G2
    suffices ∀ {s b} (H : b = true → c.IsDefEqU dType' aType'), RecM.WF c s (G2 b) P by
      split
      · refine .bind ?_ (Q := fun b _ => b = true → c.IsDefEqU dType' aType') fun b _ _ => this
        intro _ mwf wf _ _ eq
        let c' := { c with eagerReduce := true }
        have ⟨_, h1, h2, h3, h4⟩ := isDefEq.WF (c := c') hl3 ha2 _ mwf { wf with } _ _ eq
        exact ⟨_, h1, h2, { h3 with }, h4⟩
      · exact (isDefEq.WF hl3 ha2).bind fun b _ _ => this
    subst G2; dsimp; rintro s ⟨⟩ H
    · exact .getEnv <| .getLCtx .throw
    simp [G1, Expr.bindingBody!]
    have hf3 := hf3.defeqU_r c.Ewf c.Δwf hl5.symm
    have ha3 := ha3.defeqU_r c.Ewf c.Δwf (H rfl).symm
    subst hP; refine hF ⟨?_, .app hf3 ha3 hf1 ha1, hl4.inst c.Ewf ha3 ha1, .app hf3 ha3⟩
    exact fun _ hP he => (hfb.trans hb _ hP he.1).2.instantiate1 he.2
  · exact (inferLet.WF h1 hinf).bind fun _ _ _ ⟨_, _, h⟩ => hF h

#guard_named_axioms Ix.Theory.Named.TypeChecker.Inner.inferProj.WF [
  propext,
  sorryAx,
  Classical.choice,
  Quot.sound,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]
