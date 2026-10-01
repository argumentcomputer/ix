module

public import ConLeche.Verify.Cached.DiscC5

public section

/-!
# Cached body walks, part 6: annotation

Port of `ConLeche/Verify/DiscI6.lean` under the recipe (DESIGN.md,
task #163): the simulation walks for `isPropTypeI` and `annotateBodyI`
(`ConLeche/Cached/CoreC.lean`), whose bodies are character-identical to
their `ConLeche/Kernel/CoreI.lean` originals up to `EIdx → Expr` /
`CheckIM → CheckCM` (plus the two recorded `peelFuelM` deviation lines
in `annotateBodyI`'s binder clauses).  Task #175 wiring W5: the
projection elimination fallbacks (`projFieldDomI`,
`annotateProjRecI`, `annotateProjElimI`) and their walks are gone —
every supported projection is a tower table entry, and the
`.proj` clause's non-tower arms are verdicts.

One representation shrinkage simplifies the statements against the
interned originals: the structure/constructor names are plain `Name`s
(so the `NIdx` denotation premises vanish).  The pure comparand side
of every statement is byte-identical to the interned original's.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche.Cached

open ConLeche.Expr

variable {mode : CheckMode}

section Walks

variable {env : Env} {f : Nat}

end Walks

section Walks3

variable {env : Env} {f : Nat}

/-- Port of `annotateBodyI_sim`. -/
theorem annotateBodyC_sim (ih : SSimC mode env f) (_henv : EnvWF env)
    {d : Nat} {i : Expr} {ex : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelEC d)
      (annotateBodyI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (annotateBody (fueledFns mode env) env d ex) := by
  unfold annotateBodyI
  obtain rfl := hden
  have hden : RelC i i := rfl
  cases i with
  | bvar k =>
    dsimp only
    exact SimC.pure hs ⟨hden, hw⟩
  | sort u =>
    dsimp only
    exact SimC.pure hs ⟨hden, hw⟩
  | const nmN us =>
    dsimp only
    exact SimC.pure hs ⟨hden, hw⟩
  | letE t v b =>
    dsimp only
    have hwtvb : Expr.WScoped d t ∧ Expr.WScoped d v ∧
        Expr.WScoped d b := by
      have hw' : Expr.WScoped d
        (Expr.letE t v b) := hw
      simpa only [Expr.WScoped] using hw'
    unfold annotateBody
    try dsimp only
    refine SimC.bind (ih.annotate hs rfl hwtvb.1)
      (fun s₁ ty' ty'x hs₁ hP₁ => ?_)
    obtain ⟨hty'd, hwty'⟩ := hP₁
    refine SimC.bind (ih.infer hs₁ hty'd hwty')
      (fun s₂ tty ttyx hs₂ hP₂ => ?_)
    obtain ⟨httyd, hwtty⟩ := hP₂
    refine SimC.bind (ensureSortC_sim ih hs₂ httyd hwtty)
      (fun s₃ u lu hs₃ hPu => ?_)
    refine SimC.bind (ih.annotate hs₃ rfl hwtvb.2.1)
      (fun s₄ v' v'x hs₄ hP₄ => ?_)
    obtain ⟨hv'd, hwv'⟩ := hP₄
    refine SimC.bind (ih.infer hs₄ hv'd hwv')
      (fun s₅ tv tvx hs₅ hP₅ => ?_)
    obtain ⟨htvd, hwtv⟩ := hP₅
    refine SimC.bind (ih.defeq hs₅ htvd hty'd hwtv hwty')
      (fun s₆ ok ok' hs₆ hPb => ?_)
    obtain rfl : ok = ok' := hPb
    cases ok with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimC.throw_bind
    | true =>
      simp only [↓reduceIte]
      refine SimC.bind_left (inst1M_eff hs₆ rfl rfl)
        (fun s₇ ob hs₇ hQob => ?_)
      exact ih.annotate hs₇ hQob
        (Expr.WScoped.instantiate1_gen hwtvb.2.1 0 hwtvb.2.2)
  | fvar idx t =>
    dsimp only
    unfold annotateBody
    try dsimp only
    by_cases hidx : idx < d
    · rw [if_pos hidx, if_pos hidx]
      exact SimC.pure hs ⟨hden, hw⟩
    · rw [if_neg hidx, if_neg hidx]
      exact SimC.throw
  | lit l =>
    cases l with
    | natVal k =>
      dsimp only
      unfold annotateBody
      try dsimp only
      rw [natLitSupportedF_eq]
      by_cases hg : natLitSupported env
      · rw [if_pos hg, if_pos hg]
        exact SimC.pure hs ⟨hden, hw⟩
      · rw [if_neg hg, if_neg hg]
        exact SimC.throw
    | strVal str =>
      dsimp only
      unfold annotateBody
      try dsimp only
      rw [strLitSupportedF_eq]
      by_cases hg : strLitSupported env
      · rw [if_pos hg, if_pos hg]
        exact SimC.pure hs ⟨hden, hw⟩
      · rw [if_neg hg, if_neg hg]
        exact SimC.throw
  | app g' a =>
    dsimp only
    -- structural (task #100 stage 6: the application rule's checks
    -- moved to the driver's inference sweep, so the spine loop is
    -- gone and the clause annotates the two children)
    have hwga : Expr.WScoped d g' ∧ Expr.WScoped d a := by
      have hw' : Expr.WScoped d (Expr.app g' a) := hw
      simpa only [Expr.WScoped] using hw'
    unfold annotateBody
    try dsimp only
    refine SimC.bind (ih.annotate hs rfl hwga.1)
      (fun s₁ g'' g''x hs₁ hP₁ => ?_)
    obtain ⟨hg''d, hwg''⟩ := hP₁
    refine SimC.bind (ih.annotate hs₁ rfl hwga.2)
      (fun s₂ a'' a''x hs₂ hP₂ => ?_)
    obtain ⟨ha''d, hwa''⟩ := hP₂
    obtain ⟨hg''w, rfl⟩ := hg''d
    obtain ⟨ha''w, rfl⟩ := ha''d
    exact SimC.of_eff
      (pureC_eff hs₂ (x := Expr.app g'' a'')) _
      (fun r hQ => ⟨hQ, by
        simp only [Expr.WScoped]
        exact ⟨Expr.WScoped.mono (Nat.le_refl _) hwg'', hwa''⟩⟩)
  | forallE t b m =>
    dsimp only
    have hwtb : Expr.WScoped d t ∧ Expr.WScoped d b := by
      have hw' : Expr.WScoped d
        (Expr.forallE t b m) := hw
      simpa only [Expr.WScoped] using hw'
    unfold annotateBody
    try dsimp only
    refine SimC.bind (ih.annotate hs rfl hwtb.1)
      (fun s₁ ty' ty'x hs₁ hP => ?_)
    obtain ⟨hty'd, hwty'⟩ := hP
    obtain rfl := hty'd
    refine SimC.bind_left
      (pureC_eff hs₁ (x := Expr.fvar d ty'))
      (fun s₂ fv hs₂ hQfv => ?_)
    have hQfv' : RelC fv (Expr.fvar d ty') := hQfv
    refine SimC.bind_left (peelFuelM_eff hs₂)
      (fun s₃ fuel hs₃ _hQfuel => ?_)
    exact annotatePisC_tail_sim ih hs₃ rfl rfl rfl
      hQfv' hwty' hwtb.2
  | lam t b m =>
    dsimp only
    have hwtb : Expr.WScoped d t ∧ Expr.WScoped d b := by
      have hw' : Expr.WScoped d
        (Expr.lam t b m) := hw
      simpa only [Expr.WScoped] using hw'
    unfold annotateBody
    try dsimp only
    refine SimC.bind_left (bvarBoundM_eff hs)
      (fun sb bnd hsb hQb => ?_)
    by_cases hb0 : bnd = 0
    · rw [if_pos hb0]
      subst hb0
      refine SimC.bind (ih.annotate hsb rfl hwtb.1)
        (fun s₁ ty' ty'x hs₁ hP => ?_)
      obtain ⟨hty'd, hwty'⟩ := hP
      obtain rfl := hty'd
      refine SimC.bind_left
        (pureC_eff hs₁ (x := Expr.fvar d ty'))
        (fun s₂ fv hs₂ hQfv => ?_)
      have hQfv' : RelC fv (Expr.fvar d ty') := hQfv
      refine SimC.bind_left (peelFuelM_eff hs₂)
        (fun s₃ fuel hs₃ _hQfuel => ?_)
      exact annotateLamsC_tail_sim ih hs₃ rfl rfl rfl
        hQfv' hwty' hwtb.2
    · rw [if_neg hb0]
      refine SimC.bind (ih.annotate hsb rfl hwtb.1)
        (fun s₁ ty' ty'x hs₁ hP => ?_)
      obtain ⟨hty'd, hwty'⟩ := hP
      obtain rfl := hty'd
      refine SimC.bind_left
        (pureC_eff hs₁ (x := Expr.fvar d ty'))
        (fun s₂ fv hs₂ hQfv => ?_)
      have hQfv' : RelC fv (Expr.fvar d ty') := hQfv
      refine SimC.bind_left (inst1M_eff hs₂ rfl hQfv')
        (fun s₃ ob hs₃ hQob => ?_)
      refine SimC.bind (ih.annotate hs₃ hQob
        (Expr.WScoped.instantiate1 hwty' 0 hwtb.2))
        (fun s₄ body' body'x hs₄ hP₄ => ?_)
      obtain ⟨hbody'd, hwbody'⟩ := hP₄
      refine SimC.bind_left (abstract1M_eff hs₄ hbody'd)
        (fun s₈ bAbs hs₈ hQabs => ?_)
      -- task #161 P5: the single-binder write — the λ chain rule at a
      -- chain of length one, the same `annotPwLam` the spec clause runs.
      -- The rebuilt node is the same on both sides whatever the datum.
      have hstep : ∀ (s' : CState) (pw : PropWhen), CSOK mode env s' →
          SimC mode env s' (RelEC d)
            (pure (Expr.lam ty' bAbs ⟨pw⟩))
            (pure (Expr.lam ty' (body'x.abstract1 d)
              ⟨pw⟩)) := by
        intro s' pw hsS
        refine SimC.of_eff (pureC_eff hsS
          (x := Expr.lam ty' bAbs ⟨pw⟩)) _ (fun r hQ => ⟨by
            show _ = _
            have h2 : r
              = Expr.lam ty' bAbs ⟨pw⟩ := hQ
            rw [h2, hQabs], by
            simp only [Expr.WScoped]
            exact ⟨hwty', ConLeche.WScoped.abstract1 0 hwbody'⟩⟩)
      -- task #172 B3 method row: the cached guard reads
      -- `mode.verified`, the pure one `mode.verifiedChecks`; a bare
      -- `split` decides only one of the two `if`s.
      by_cases hpw : (!pwWritten m.pw) = true
      · simp only [hpw, ↓reduceIte]
        refine SimC.bind (annotPwLamC_sim ih hs₈ hbody'd hwbody')
          (fun s₉ pw pwx hs₉ hPpw => ?_)
        obtain rfl : pw = pwx := hPpw
        exact hstep s₉ pw hs₉
      · simp only [Bool.not_eq_true] at hpw
        simp only [hpw, ↓reduceIte]
        exact hstep s₈ m.pw hs₈
  | proj snN ipN pe =>
    dsimp only
    have hwpe : Expr.WScoped d pe := by
      have hw' : Expr.WScoped d (Expr.proj snN ipN pe) := hw
      simpa only [Expr.WScoped] using hw'
    unfold annotateBody
    try dsimp only
    refine SimC.bind (ih.annotate hs rfl hwpe)
      (fun s₁ e' e'x hs₁ hP => ?_)
    obtain ⟨he'd, hwe'⟩ := hP
    refine SimC.bind (ih.inferIO hs₁ he'd hwe')
      (fun s₂ tpe tpex hs₂ hP₂ => ?_)
    obtain ⟨htped, hwtpe⟩ := hP₂
    refine SimC.bind (ih.whnf hs₂ htped hwtpe)
      (fun s₃ te tex hs₃ hP₃ => ?_)
    obtain ⟨hted, hwte⟩ := hP₃
    refine SimC.pureB ?_
    obtain rfl := hted
    have hted : RelC te te := rfl
    have htargs : RelCL (Expr.getAppArgsC te) (Expr.getAppArgs te) :=
      Expr.getAppArgsC_spec te
    generalize hgn : Expr.getAppFn te = g
    cases g with
    | const T us =>
      dsimp only
      refine SimC.bind_left (pureEq_eff hs₃ T)
        (fun s₃T Tw hs₃T hTw => ?_)
      subst hTw
      rw [mkFEnv_findProj?]
      cases hfp : env.findProj? Tw ipN with
      | none =>
        exact SimC.throw
      | some entry =>
        dsimp only
        refine SimC.pureB ?_
        simp only [RelCL.length htargs]
        -- the node's own structure name (task #271), then the parameter count
        by_cases hsn : Tw = snN
        case neg => rw [if_neg hsn, if_neg hsn]; exact SimC.throw
        rw [if_pos hsn, if_pos hsn]
        by_cases hlen : (Expr.getAppArgs te).length = entry.numParams
        · rw [if_pos hlen, if_pos hlen]
          exact SimC.of_eff
            (pureC_eff hs₃T (x := Expr.proj Tw ipN e')) _
            (fun r hQ => ⟨by
                show _ = _
                have h2 : r = Expr.proj Tw ipN e' := hQ
                rw [h2, he'd], by
              simp only [Expr.WScoped]
              exact hwe'⟩)
        · rw [if_neg hlen, if_neg hlen]
          exact SimC.throw
    | bvar k =>
      exact SimC.throw
    | sort u =>
      exact SimC.throw
    | lit l =>
      exact SimC.throw
    | fvar idx t' =>
      exact SimC.throw
    | app f₂ a₂ =>
      exact SimC.throw
    | lam t' b' m' =>
      exact SimC.throw
    | forallE t' b' m' =>
      exact SimC.throw
    | letE t' v' b' =>
      exact SimC.throw
    | proj s' j' e'' =>
      exact SimC.throw

end Walks3

end ConLeche.Cached
