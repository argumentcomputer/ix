module

public import ConLeche.Verify.Cached.DiscC4

public section

/-!
# Cached body walks, part 5: definitional equality (task #163)

Port of `ConLeche/Verify/DiscI5.lean` under the recipe (DESIGN.md,
task #163): the simulation walks for `defeqStepI`, `defeqLoopI` and
`defeqBodyI` (`ConLeche/Cached/CoreC.lean`), whose bodies are
character-identical to their `ConLeche/Kernel/CoreI.lean` originals up to
`EIdx → Expr` / `CheckIM → CheckCM`.

Where the interned walk needed the arena's canonicity
(`beq_transfer`, via `denoteT_inj`) to identify an index comparison
with the spec's structural comparison, the cached walk uses
`Expr.beq_iff` — decided equality *is* equality of the
erasures (`eraseC_inj`), with no store in sight.  The pure comparand
side of every statement is byte-identical to the interned original's.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche.Cached

open ConLeche.Expr

variable {mode : CheckMode}

section Walks

variable {env : Env} {f : Nat}

/-- Decided `Expr` equality decides expression equality on the field
invariant — the port of `beq_transfer` (whose arena leg was
`denoteT_inj`). -/
private theorem beq_transferC {i j : Expr} {a b : Expr}
    (ha : RelC i a) (hb : RelC j b) : (i == j) = (a == b) := by
  obtain rfl := ha
  obtain rfl := hb
  rfl

/-- The one-sided-λ (right) stuck arm.  The name and binder-meta
bridges of the interned original collapse (the cached representation
stores `Name`s and `BinderMeta`s directly). -/
private theorem defeqC_etaR_arm (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {a' b' t₂ b₂ : Expr} {a'x ty₂x body₂x : Expr}
    {bm₂ : BinderMeta} {s₀ : CState} (hs : CSOK mode env s₀)
    (haS : RelC a' a'x)
    (hty₂ : RelC t₂ ty₂x)
    (hbody₂ : RelC b₂ body₂x)
    (hbS : RelC b' (.lam ty₂x body₂x bm₂))
    (hwa' : Expr.WScoped d a'x)
    (hwb' : Expr.WScoped d (Expr.lam ty₂x body₂x bm₂)) :
    SimC mode env s₀ RelVC
      (etaCertI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d
          t₂ b₂ bm₂ a' >>= fun r =>
        if r then pure true
        else stuckIrrelI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d a' b')
      (etaCert mode (fueledFns mode env) env d ty₂x body₂x bm₂
          a'x >>= fun r =>
        if r then pure true
        else stuckIrrel mode (fueledFns mode env) env d a'x
          (.lam ty₂x body₂x bm₂)) := by
  have h2 : Expr.WScoped d ty₂x ∧ Expr.WScoped d body₂x := by
    simpa only [Expr.WScoped] using hwb'
  refine SimC.bind (etaCertC_sim ih hs hty₂ hbody₂ haS h2.1 h2.2 hwa')
    (fun s₁ r r' hs₁ hP => ?_)
  obtain rfl : r = r' := hP
  cases r with
  | true =>
    simp only [↓reduceIte]
    exact SimC.pure hs₁ rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact stuckIrrelC_sim hμ ih henv hs₁ haS hbS hwa' hwb'

/-- The one-sided-λ (left) stuck arm. -/
private theorem defeqC_etaL_arm (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {a' b' t₁ b₁ : Expr} {b'x ty₁x body₁x : Expr}
    {bm₁ : BinderMeta} {s₀ : CState} (hs : CSOK mode env s₀)
    (haS : RelC a' (.lam ty₁x body₁x bm₁))
    (hty₁ : RelC t₁ ty₁x)
    (hbody₁ : RelC b₁ body₁x)
    (hbS : RelC b' b'x)
    (hwa' : Expr.WScoped d (Expr.lam ty₁x body₁x bm₁))
    (hwb' : Expr.WScoped d b'x) :
    SimC mode env s₀ RelVC
      (etaCertI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d
          t₁ b₁ bm₁ b' >>= fun r =>
        if r then pure true
        else stuckIrrelI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d a' b')
      (etaCert mode (fueledFns mode env) env d ty₁x body₁x bm₁
          b'x >>= fun r =>
        if r then pure true
        else stuckIrrel mode (fueledFns mode env) env d
          (.lam ty₁x body₁x bm₁) b'x) := by
  have h1 : Expr.WScoped d ty₁x ∧ Expr.WScoped d body₁x := by
    simpa only [Expr.WScoped] using hwa'
  refine SimC.bind (etaCertC_sim ih hs hty₁ hbody₁ hbS h1.1 h1.2 hwb')
    (fun s₁ r r' hs₁ hP => ?_)
  obtain rfl : r = r' := hP
  cases r with
  | true =>
    simp only [↓reduceIte]
    exact SimC.pure hs₁ rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact stuckIrrelC_sim hμ ih henv hs₁ haS hbS hwa' hwb'

/-- The lazy-delta "unfold both sides" branch (task #106: the
unfoldings are materialized only here, inside the branch that consumes
them). -/
private theorem defeqBothC (_ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {kI : Bool → Expr → Expr → CheckCM Bool}
    {kM : Bool → Expr → Expr → FueledM Bool}
    (hk : ∀ (pi : Bool) {s : CState} {p q : Expr} {x y : Expr},
      CSOK mode env s → RelC p x → RelC q y →
      Expr.WScoped d x → Expr.WScoped d y →
      SimC mode env s RelVC (kI pi p q) (kM pi x y))
    {i j : Expr} {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (unfoldDefinitionI (mkFEnv env) i >>= fun ua =>
        unfoldDefinitionI (mkFEnv env) j >>= fun ub =>
        match ua, ub with
        | some a₂, some b₂ => kI false a₂ b₂
        | _, _ => pure false)
      (match unfoldDefinition env a, unfoldDefinition env b with
        | some a₂, some b₂ => kM false a₂ b₂
        | _, _ => pure false) := by
  refine SimC.bind_left (unfoldDefinitionC_eff hs hdena)
    (fun s₁ ua hs₁ hQa => ?_)
  refine SimC.bind_left (unfoldDefinitionC_eff hs₁ hdenb)
    (fun s₂ ub hs₂ hQb => ?_)
  cases hua : unfoldDefinition env a with
  | none =>
    rw [hua] at hQa
    cases ua with
    | some a₂ => exact absurd hQa (by simp [OptEr])
    | none => cases ub <;> exact SimC.pure hs₂ rfl
  | some a₂x =>
    rw [hua] at hQa
    cases ua with
    | none => exact absurd hQa (by simp [OptEr])
    | some a₂ =>
      cases hub : unfoldDefinition env b with
      | none =>
        rw [hub] at hQb
        cases ub with
        | some b₂ => exact absurd hQb (by simp [OptEr])
        | none => exact SimC.pure hs₂ rfl
      | some b₂x =>
        rw [hub] at hQb
        cases ub with
        | none => exact absurd hQb (by simp [OptEr])
        | some b₂ =>
          exact hk _ hs₂ hQa hQb
            (unfoldDefinition_WScoped henv hua hwa)
            (unfoldDefinition_WScoped henv hub hwb)

theorem defeqStepC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {kI : Bool → Expr → Expr → CheckCM Bool}
    {kM : Bool → Expr → Expr → FueledM Bool}
    (hk : ∀ (pi : Bool) {s : CState} {p q : Expr} {x y : Expr},
      CSOK mode env s → RelC p x → RelC q y →
      Expr.WScoped d x → Expr.WScoped d y →
      SimC mode env s RelVC (kI pi p q) (kM pi x y))
    (pi : Bool)
    {i j : Expr} {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (defeqStepI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d kI pi i j)
      (defeqStep mode (fueledFns mode env) env d kM pi a b) := by
  unfold defeqStepI
  unfold defeqStep
  rw [beq_transferC hdena hdenb]
  by_cases hab : (a == b) = true
  · simp only [if_pos hab]
    exact SimC.pure hs rfl
  · simp only [if_neg hab]
    -- the eq-true shortcut (E2): two store reads for the guard, then the
    -- guarded `whnf`
    refine SimC.pureB ?_
    rw [isBoolTrue_spec' hdenb]
    refine SimC.pureB ?_
    rw [hasFvar_spec' hdena]
    refine SimC.bind (boolTrueShortcutIfC_sim ih hs hdena hwa _)
      (fun s₀b rbt rbtx hs₀b hPbt => ?_)
    cases hPbt
    cases rbt with
    | true =>
      simp only [↓reduceIte]
      exact SimC.pure hs₀b rfl
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hs := hs₀b
    refine SimC.bind (ih.whnfCore hs hdena hwa)
      (fun s₁ a' a'x hs₁ hPa => ?_)
    obtain ⟨ha'd, hwa'⟩ := hPa
    refine SimC.bind (ih.whnfCore hs₁ hdenb hwb)
      (fun s₂ b' b'x hs₂ hPb => ?_)
    obtain ⟨hb'd, hwb'⟩ := hPb
    rw [beq_transferC ha'd hb'd]
    by_cases hab' : (a'x == b'x) = true
    · simp only [if_pos hab']
      exact SimC.pure hs₂ rfl
    · simp only [if_neg hab']
      -- hoisted proof irrelevance (the `Prop` branch, task #168)
      -- the D4 quick-pair read
      refine SimC.pureB ?_
      rw [quickPair_spec' ha'd hb'd]
      refine SimC.bind (propIrrelIfC_sim ih hs₂ ha'd hb'd hwa' hwb' _)
        (fun s₂p rpi rpix hs₂p hPpi => ?_)
      cases hPpi
      cases rpi with
      | true =>
        simp only [↓reduceIte]
        exact SimC.pure hs₂p rfl
      | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hs₂ := hs₂p
      -- peel the fvar-guard read; `hasFvarI` agrees with the spec's
      -- `hasFvar`, so both sides carry the same guard
      refine SimC.pureB ?_
      rw [hasFvar_spec' ha'd, hasFvar_spec' hb'd]
      refine SimC.bind (reduceNatIfC_sim ih hs₂ ha'd hwa' _)
        (fun s₃ o₁ o₁x hs₃ hPo₁ => ?_)
      cases o₁ with
      | some a₂ =>
        cases o₁x with
        | none => exact absurd hPo₁ (by simp [RelOC])
        | some a₂x =>
          obtain ⟨ha₂d, hwa₂⟩ := hPo₁
          exact hk _ hs₃ ha₂d hb'd hwa₂ hwb'
      | none =>
        cases o₁x with
        | some a₂x => exact absurd hPo₁ (by simp [RelOC])
        | none =>
          refine SimC.bind (reduceNatIfC_sim ih hs₃ hb'd hwb' _)
            (fun s₄ o₂ o₂x hs₄ hPo₂ => ?_)
          cases o₂ with
          | some b₂ =>
            cases o₂x with
            | none => exact absurd hPo₂ (by simp [RelOC])
            | some b₂x =>
              obtain ⟨hb₂d, hwb₂⟩ := hPo₂
              exact hk _ hs₄ ha'd hb₂d hwa' hwb₂
          | none =>
            cases o₂x with
            | some b₂x => exact absurd hPo₂ (by simp [RelOC])
            | none =>
              -- Lazy delta, decision before materialization (task #106)
              refine SimC.pureB ?_
              refine SimC.pureB ?_
              rw [unfoldableHeadC_spec' ha'd,
                unfoldableHeadC_spec' hb'd]
              cases hda : unfoldableHead env a'x with
              | true =>
                cases hdb : unfoldableHead env b'x with
                | false =>
                  dsimp only
                  refine SimC.bind_left (unfoldDefinitionC_eff hs₄ ha'd)
                    (fun s₅ ua hs₅ hQa => ?_)
                  cases hua : unfoldDefinition env a'x with
                  | none =>
                    rw [hua] at hQa
                    cases ua with
                    | some a₂ => exact absurd hQa (by simp [OptEr])
                    | none => exact SimC.pure hs₅ rfl
                  | some a₂x =>
                    rw [hua] at hQa
                    cases ua with
                    | none => exact absurd hQa (by simp [OptEr])
                    | some a₂ =>
                      exact hk _ hs₅ hQa hb'd
                        (unfoldDefinition_WScoped henv hua hwa') hwb'
                | true =>
                  dsimp only
                  refine SimC.pureB ?_
                  refine SimC.pureB ?_
                  rw [headHintC_spec' ha'd,
                    headHintC_spec' hb'd]
                  by_cases hlt₁ : ReducibilityHint.lt
                      (headHint env b'x) (headHint env a'x) = true
                  · rw [if_pos hlt₁, if_pos hlt₁]
                    refine SimC.bind_left (unfoldDefinitionC_eff hs₄ ha'd)
                      (fun s₅ ua hs₅ hQa => ?_)
                    cases hua : unfoldDefinition env a'x with
                    | none =>
                      rw [hua] at hQa
                      cases ua with
                      | some a₂ => exact absurd hQa (by simp [OptEr])
                      | none => exact SimC.pure hs₅ rfl
                    | some a₂x =>
                      rw [hua] at hQa
                      cases ua with
                      | none => exact absurd hQa (by simp [OptEr])
                      | some a₂ =>
                        exact hk _ hs₅ hQa hb'd
                          (unfoldDefinition_WScoped henv hua hwa') hwb'
                  · rw [if_neg hlt₁, if_neg hlt₁]
                    by_cases hlt₂ : ReducibilityHint.lt
                        (headHint env a'x) (headHint env b'x) = true
                    · rw [if_pos hlt₂, if_pos hlt₂]
                      refine SimC.bind_left (unfoldDefinitionC_eff hs₄ hb'd)
                        (fun s₅ ub hs₅ hQb => ?_)
                      cases hub : unfoldDefinition env b'x with
                      | none =>
                        rw [hub] at hQb
                        cases ub with
                        | some b₂ => exact absurd hQb (by simp [OptEr])
                        | none => exact SimC.pure hs₅ rfl
                      | some b₂x =>
                        rw [hub] at hQb
                        cases ub with
                        | none => exact absurd hQb (by simp [OptEr])
                        | some b₂ =>
                          exact hk _ hs₅ ha'd hQb hwa'
                            (unfoldDefinition_WScoped henv hub hwb')
                    · rw [if_neg hlt₂, if_neg hlt₂]
                      refine SimC.pureB ?_
                      rw [sameConstHeadsC_spec' ha'd hb'd]
                      by_cases hsr : (ReducibilityHint.sameRegular
                          (headHint env a'x) (headHint env b'x) &&
                          sameConstHeads a'x b'x) = true
                      · rw [if_pos hsr, if_pos hsr]
                        refine SimC.bind (defeqSpineC_sim ih hs₄
                          ha'd hb'd hwa' hwb')
                          (fun s₇ sp sp' hs₇ hPsp => ?_)
                        obtain rfl : sp = sp' := hPsp
                        cases sp with
                        | true =>
                          simp only [↓reduceIte]
                          exact SimC.pure hs₇ rfl
                        | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          exact defeqBothC ih henv hk hs₇ ha'd hb'd hwa' hwb'
                      · rw [if_neg hsr, if_neg hsr]
                        exact defeqBothC ih henv hk hs₄ ha'd hb'd hwa' hwb'
              | false =>
              cases hdb : unfoldableHead env b'x with
              | true =>
                dsimp only
                refine SimC.bind_left (unfoldDefinitionC_eff hs₄ hb'd)
                  (fun s₅ ub hs₅ hQb => ?_)
                cases hub : unfoldDefinition env b'x with
                | none =>
                  rw [hub] at hQb
                  cases ub with
                  | some b₂ => exact absurd hQb (by simp [OptEr])
                  | none => exact SimC.pure hs₅ rfl
                | some b₂x =>
                  rw [hub] at hQb
                  cases ub with
                  | none => exact absurd hQb (by simp [OptEr])
                  | some b₂ =>
                    exact hk _ hs₅ ha'd hQb hwa'
                      (unfoldDefinition_WScoped henv hub hwb')
              | false =>
                dsimp only
                have haS := ha'd
                have hbS := hb'd
                have hs₆ := hs₄
                obtain rfl := ha'd
                obtain rfl := hb'd
                cases a' with
                | sort u₁ =>
                  cases b' with
                  | sort u₂ =>
                    dsimp only
                    refine SimC.bind_left (isEquivLM_eff hs₆ u₁ u₂)
                      (fun sE o hsE ho => ?_)
                    subst ho
                    exact SimC.liftFueled _ _ hsE
                  | lam t₂ b₂ m₂ =>
                    dsimp only
                    exact defeqC_etaR_arm hμ ih henv hs₆ haS rfl
                      rfl hbS hwa' hwb'
                  | _ =>
                    dsimp only
                    exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                | lit l₁ =>
                  cases l₁ with
                  | natVal n₁ =>
                    cases b' with
                    | lit l₂ =>
                      dsimp only
                      exact SimC.pure hs₆ rfl
                    | const c₂ us₂ =>
                      dsimp only
                      refine SimC.bind_left (pureEq_eff hs₆ (c₂ == natZeroName))
                        (fun s₆b bq hs₆b hbq => ?_)
                      subst bq
                      simp only [beq_iff_eq]
                      by_cases hz : c₂ = natZeroName ∧ us₂ = []
                      · rw [if_pos hz, if_pos hz]
                        exact SimC.pure hs₆b rfl
                      · rw [if_neg hz, if_neg hz]
                        exact stuckIrrelC_sim hμ ih henv hs₆b haS hbS hwa' hwb'
                    | app f₂ x₂ =>
                      have hwb'' : Expr.WScoped d
                        (Expr.app (f₂) (x₂)) := hwb'
                      have h2 : Expr.WScoped d (f₂) ∧
                          Expr.WScoped d (x₂) := by
                        simpa only [Expr.WScoped] using hwb''
                      dsimp only
                      cases n₁ with
                      | zero =>
                        dsimp only
                        exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                      | succ k =>
                        cases f₂ with
                        | const cf usf =>
                          cases usf with
                          | cons u us' =>
                            dsimp only
                            exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                          | nil =>
                            dsimp only
                            refine SimC.bind_left
                              (pureEq_eff hs₆ (cf == natSuccName))
                              (fun s₆b bq hs₆b hbq => ?_)
                            subst bq
                            simp only [beq_iff_eq]
                            by_cases hsc : cf = natSuccName
                            · rw [if_pos hsc, if_pos hsc]
                              refine SimC.bind_left (pureC_eff hs₆b
                                (x := Expr.lit (.natVal k)))
                                (fun s₇ kl hs₇ hQk => ?_)
                              have hQk' : RelC kl
                                (Expr.lit (.natVal k)) := hQk
                              exact ih.defeq hs₇ hQk' rfl
                                (by simp [Expr.WScoped]) h2.2
                            · rw [if_neg hsc, if_neg hsc]
                              exact stuckIrrelC_sim hμ ih henv hs₆b haS hbS
                                hwa' hwb'
                        | _ =>
                          dsimp only
                          exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                    | lam t₂ b₂ m₂ =>
                      dsimp only
                      exact defeqC_etaR_arm hμ ih henv hs₆ haS rfl
                        rfl hbS hwa' hwb'
                    | _ =>
                      dsimp only
                      exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                  | strVal str =>
                    cases b' with
                    | lit l₂ =>
                      dsimp only
                      exact SimC.pure hs₆ rfl
                    | app f₂ x₂ =>
                      dsimp only
                      cases f₂ with
                      | const cf usf =>
                        dsimp only
                        rw [strLitSupportedF_eq]
                        refine SimC.bind_left
                          (pureEq_eff hs₆ (cf == stringOfListName))
                          (fun s₆b bq hs₆b hbq => ?_)
                        subst bq
                        simp only [beq_iff_eq]
                        by_cases hsc : cf = stringOfListName ∧ usf = [] ∧
                            strLitSupported env = true
                        · rw [if_pos hsc, if_pos hsc]
                          refine SimC.bind_left (pureC_eff hs₆b
                            (strLitToConstructor str))
                            (fun s₇ sc hs₇ hQs => ?_)
                          exact ih.defeq hs₇ hQs hbS
                            (strLitToConstructor_WScoped str d) hwb'
                        · rw [if_neg hsc, if_neg hsc]
                          exact stuckIrrelC_sim hμ ih henv hs₆b haS hbS hwa' hwb'
                      | _ =>
                        dsimp only
                        exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                    | lam t₂ b₂ m₂ =>
                      dsimp only
                      exact defeqC_etaR_arm hμ ih henv hs₆ haS rfl
                        rfl hbS hwa' hwb'
                    | _ =>
                      dsimp only
                      exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                | fvar i₁ t₁ =>
                  cases b' with
                  | fvar i₂ t₂ =>
                    dsimp only
                    by_cases hij : (i₁ == i₂) = true
                    · rw [if_pos hij, if_pos hij]
                      exact SimC.pure hs₆ rfl
                    · rw [if_neg hij, if_neg hij]
                      exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                  | lam t₂ b₂ m₂ =>
                    dsimp only
                    exact defeqC_etaR_arm hμ ih henv hs₆ haS rfl
                      rfl hbS hwa' hwb'
                  | _ =>
                    dsimp only
                    exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                | const c₁ us₁ =>
                  cases b' with
                  | const c₂ us₂ =>
                    dsimp only
                    by_cases hcc : c₁ = c₂
                    · rw [if_pos hcc, if_pos hcc]
                      refine SimC.bind_left (isEquivListLM_eff hs₆)
                        (fun sE o hsE ho => ?_)
                      subst ho
                      refine SimC.bind (SimC.liftFueled _ _ hsE)
                        (fun s₇ ok ok' hs₇ hPok => ?_)
                      obtain rfl : ok = ok' := hPok
                      cases ok with
                      | true =>
                        simp only [↓reduceIte]
                        exact SimC.pure hs₇ rfl
                      | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        exact stuckIrrelC_sim hμ ih henv hs₇ haS hbS hwa' hwb'
                    · rw [if_neg hcc, if_neg hcc]
                      exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                  | lit l₂ =>
                    cases l₂ with
                    | natVal n₂ =>
                      dsimp only
                      refine SimC.bind_left (pureEq_eff hs₆ (c₁ == natZeroName))
                        (fun s₆b bq hs₆b hbq => ?_)
                      subst bq
                      simp only [beq_iff_eq]
                      by_cases hz : c₁ = natZeroName ∧ us₁ = []
                      · rw [if_pos hz, if_pos hz]
                        exact SimC.pure hs₆b rfl
                      · rw [if_neg hz, if_neg hz]
                        exact stuckIrrelC_sim hμ ih henv hs₆b haS hbS hwa' hwb'
                    | strVal str =>
                      dsimp only
                      exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                  | lam t₂ b₂ m₂ =>
                    dsimp only
                    exact defeqC_etaR_arm hμ ih henv hs₆ haS rfl
                      rfl hbS hwa' hwb'
                  | _ =>
                    dsimp only
                    exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                | forallE t₁ b₁ m₁ =>
                  have hwa'' : Expr.WScoped d
                    (Expr.forallE (t₁) (b₁) m₁) := hwa'
                  have h1 : Expr.WScoped d (t₁) ∧
                      Expr.WScoped d (b₁) := by
                    simpa only [Expr.WScoped] using hwa''
                  cases b' with
                  | forallE t₂ b₂ m₂ =>
                    dsimp only
                    have hwb'' : Expr.WScoped d
                      (Expr.forallE (t₂) (b₂) m₂) := hwb'
                    have h2 : Expr.WScoped d (t₂) ∧
                        Expr.WScoped d (b₂) := by
                      simpa only [Expr.WScoped] using hwb''
                    refine SimC.bind
                      (ih.defeq hs₆ rfl rfl h1.1 h2.1)
                      (fun s₇ r₁ r₁' hs₇ hP₁ => ?_)
                    obtain rfl : r₁ = r₁' := hP₁
                    cases r₁ with
                    | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      exact SimC.pure hs₇ rfl
                    | true =>
                      simp only [↓reduceIte]
                      -- one shared local for both bodies (official
                      -- `is_def_eq_binding`; task #201)
                      refine SimC.bind_left
                        (pureC_eff hs₇ (x := Expr.fvar d t₂))
                        (fun s₈ fv hs₈ hQf => ?_)
                      have hQf' : RelC fv
                        (Expr.fvar d (t₂)) := hQf
                      refine SimC.bind_left
                        (inst1M_eff hs₈ rfl hQf')
                        (fun s₉ ob₁ hs₉ hQo₁ => ?_)
                      refine SimC.bind_left
                        (inst1M_eff hs₉ rfl hQf')
                        (fun s₁₁ ob₂ hs₁₁ hQo₂ => ?_)
                      refine SimC.bind (ih.defeq hs₁₁ hQo₁ hQo₂
                        (Expr.WScoped.instantiate1 h2.1 0 h1.2)
                        (Expr.WScoped.instantiate1 h2.1 0 h2.2))
                        (fun s₁₂ r₂ r₂x hs₁₂ hPr₂ => ?_)
                      obtain rfl : r₂ = r₂x := hPr₂
                      cases r₂ with
                      | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        exact SimC.pure hs₁₂ rfl
                      | true =>
                        -- task #172 B3 method row: the cached side's
                        -- guard reads `mode.verified`, the
                        -- pure side's `mode.verifiedChecks`.  They are
                        -- `rfl`-equal but their `Decidable` instances
                        -- are not syntactically one, so `split`
                        -- decides only one `if`; `by_cases` on the
                        -- guard plus `↓reduceIte` decides both.
                        simp only [↓reduceIte]
                        by_cases hpw :
                            (mode.verifiedChecks && !m₁.pw == m₂.pw) = true
                        · simp only [hpw, ↓reduceIte]
                          exact SimC.throw_bind
                        · simp only [Bool.not_eq_true] at hpw
                          simp only [hpw, ↓reduceIte]
                          exact SimC.pure hs₁₂ rfl
                  | lam t₂ b₂ m₂ =>
                    dsimp only
                    exact defeqC_etaR_arm hμ ih henv hs₆ haS rfl
                      rfl hbS hwa' hwb'
                  | _ =>
                    dsimp only
                    exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                | lam t₁ b₁ m₁ =>
                  have hwa'' : Expr.WScoped d
                    (Expr.lam (t₁) (b₁) m₁) := hwa'
                  have h1 : Expr.WScoped d (t₁) ∧
                      Expr.WScoped d (b₁) := by
                    simpa only [Expr.WScoped] using hwa''
                  cases b' with
                  | lam t₂ b₂ m₂ =>
                    dsimp only
                    have hwb'' : Expr.WScoped d
                      (Expr.lam (t₂) (b₂) m₂) := hwb'
                    have h2 : Expr.WScoped d (t₂) ∧
                        Expr.WScoped d (b₂) := by
                      simpa only [Expr.WScoped] using hwb''
                    refine SimC.bind
                      (ih.defeq hs₆ rfl rfl h1.1 h2.1)
                      (fun s₇ r₁ r₁' hs₇ hP₁ => ?_)
                    obtain rfl : r₁ = r₁' := hP₁
                    cases r₁ with
                    | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      exact SimC.pure hs₇ rfl
                    | true =>
                      simp only [↓reduceIte]
                      -- one shared local for both bodies (official
                      -- `is_def_eq_binding`; task #201)
                      refine SimC.bind_left
                        (pureC_eff hs₇ (x := Expr.fvar d t₂))
                        (fun s₈ fv hs₈ hQf => ?_)
                      have hQf' : RelC fv
                        (Expr.fvar d (t₂)) := hQf
                      refine SimC.bind_left
                        (inst1M_eff hs₈ rfl hQf')
                        (fun s₉ ob₁ hs₉ hQo₁ => ?_)
                      refine SimC.bind_left
                        (inst1M_eff hs₉ rfl hQf')
                        (fun s₁₁ ob₂ hs₁₁ hQo₂ => ?_)
                      refine SimC.bind (ih.defeq hs₁₁ hQo₁ hQo₂
                        (Expr.WScoped.instantiate1 h2.1 0 h1.2)
                        (Expr.WScoped.instantiate1 h2.1 0 h2.2))
                        (fun s₁₂ r₂ r₂x hs₁₂ hPr₂ => ?_)
                      obtain rfl : r₂ = r₂x := hPr₂
                      cases r₂ with
                      | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        exact SimC.pure hs₁₂ rfl
                      | true =>
                        -- task #172 B3 method row: the cached side's
                        -- guard reads `mode.verified`, the
                        -- pure side's `mode.verifiedChecks`.  They are
                        -- `rfl`-equal but their `Decidable` instances
                        -- are not syntactically one, so `split`
                        -- decides only one `if`; `by_cases` on the
                        -- guard plus `↓reduceIte` decides both.
                        simp only [↓reduceIte]
                        by_cases hpw :
                            (mode.verifiedChecks && !m₁.pw == m₂.pw) = true
                        · simp only [hpw, ↓reduceIte]
                          exact SimC.throw_bind
                        · simp only [Bool.not_eq_true] at hpw
                          simp only [hpw, ↓reduceIte]
                          exact SimC.pure hs₁₂ rfl
                  | _ =>
                    dsimp only
                    exact defeqC_etaL_arm hμ ih henv hs₆ haS rfl
                      rfl hbS hwa' hwb'
                | app f₁ x₁ =>
                  have hwa'' : Expr.WScoped d
                    (Expr.app (f₁) (x₁)) := hwa'
                  have h1 : Expr.WScoped d (f₁) ∧
                      Expr.WScoped d (x₁) := by
                    simpa only [Expr.WScoped] using hwa''
                  cases b' with
                  | app f₂ x₂ =>
                    dsimp only
                    -- spine-wise congruence (task #106)
                    refine SimC.pureB ?_
                    refine SimC.pureB ?_
                    have hAA : RelCL
                        (Expr.getAppArgsC (Expr.app f₁ x₁))
                        (Expr.app (f₁) (x₁)).getAppArgs :=
                      Expr.getAppArgsC_spec _
                    have hBB : RelCL
                        (Expr.getAppArgsC (Expr.app f₂ x₂))
                        (Expr.app (f₂) (x₂)).getAppArgs :=
                      Expr.getAppArgsC_spec _
                    have hlena :
                        (Expr.getAppArgsC
                          (Expr.app f₁ x₁)).length
                        = (Expr.app (f₁) (x₁)).getAppArgs.length :=
                      RelCL.length hAA
                    have hlenb :
                        (Expr.getAppArgsC
                          (Expr.app f₂ x₂)).length
                        = (Expr.app (f₂) (x₂)).getAppArgs.length :=
                      RelCL.length hBB
                    simp only [hlena, hlenb]
                    by_cases hlen :
                        (Expr.app (f₁) (x₁)).getAppArgs.length
                          = (Expr.app (f₂) (x₂)).getAppArgs.length
                    · rw [if_pos hlen, if_pos hlen]
                      refine SimC.pureB ?_
                      refine SimC.pureB ?_
                      refine SimC.bind (ih.defeq hs₆ rfl rfl
                        hwa''.getAppFn hwb'.getAppFn)
                        (fun s₇ r₁ r₁' hs₇ hP₁ => ?_)
                      obtain rfl : r₁ = r₁' := hP₁
                      cases r₁ with
                      | true =>
                        simp only [↓reduceIte]
                        refine SimC.bind (defEqListC_sim ih hs₇ hAA hBB
                          hwa''.getAppArgs hwb'.getAppArgs)
                          (fun s₈ r₂ r₂' hs₈ hP₂ => ?_)
                        obtain rfl : r₂ = r₂' := hP₂
                        cases r₂ with
                        | true =>
                          simp only [↓reduceIte]
                          exact SimC.pure hs₈ rfl
                        | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          exact stuckIrrelC_sim hμ ih henv hs₈ haS hbS hwa' hwb'
                      | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        exact stuckIrrelC_sim hμ ih henv hs₇ haS hbS hwa' hwb'
                    · rw [if_neg hlen, if_neg hlen]
                      exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                  | lit l₂ =>
                    cases l₂ with
                    | natVal nn =>
                      dsimp only
                      cases nn with
                      | zero =>
                        dsimp only
                        exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                      | succ k =>
                        cases f₁ with
                        | const cf usf =>
                          cases usf with
                          | cons u us' =>
                            dsimp only
                            exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                          | nil =>
                            dsimp only
                            refine SimC.bind_left
                              (pureEq_eff hs₆ (cf == natSuccName))
                              (fun s₆b bq hs₆b hbq => ?_)
                            subst bq
                            simp only [beq_iff_eq]
                            by_cases hsc : cf = natSuccName
                            · rw [if_pos hsc, if_pos hsc]
                              refine SimC.bind_left (pureC_eff hs₆b
                                (x := Expr.lit (.natVal k)))
                                (fun s₇ kl hs₇ hQk => ?_)
                              have hQk' : RelC kl
                                (Expr.lit (.natVal k)) := hQk
                              exact ih.defeq hs₇ rfl hQk' h1.2
                                (by simp [Expr.WScoped])
                            · rw [if_neg hsc, if_neg hsc]
                              exact stuckIrrelC_sim hμ ih henv hs₆b haS hbS
                                hwa' hwb'
                        | _ =>
                          dsimp only
                          exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                    | strVal str =>
                      dsimp only
                      cases f₁ with
                      | const cf usf =>
                        dsimp only
                        rw [strLitSupportedF_eq]
                        refine SimC.bind_left
                          (pureEq_eff hs₆ (cf == stringOfListName))
                          (fun s₆b bq hs₆b hbq => ?_)
                        subst bq
                        simp only [beq_iff_eq]
                        by_cases hsc : cf = stringOfListName ∧ usf = [] ∧
                            strLitSupported env = true
                        · rw [if_pos hsc, if_pos hsc]
                          refine SimC.bind_left (pureC_eff hs₆b
                            (strLitToConstructor str))
                            (fun s₇ sc hs₇ hQs => ?_)
                          exact ih.defeq hs₇ haS hQs hwa'
                            (strLitToConstructor_WScoped str d)
                        · rw [if_neg hsc, if_neg hsc]
                          exact stuckIrrelC_sim hμ ih henv hs₆b haS hbS hwa' hwb'
                      | _ =>
                        dsimp only
                        exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                  | lam t₂ b₂ m₂ =>
                    dsimp only
                    exact defeqC_etaR_arm hμ ih henv hs₆ haS rfl
                      rfl hbS hwa' hwb'
                  | _ =>
                    dsimp only
                    exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                | bvar k₁ =>
                  cases b' with
                  | lam t₂ b₂ m₂ =>
                    dsimp only
                    exact defeqC_etaR_arm hμ ih henv hs₆ haS rfl
                      rfl hbS hwa' hwb'
                  | _ =>
                    dsimp only
                    exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                | letE t₁ v₁ b₁ =>
                  cases b' with
                  | lam t₂ b₂ m₂ =>
                    dsimp only
                    exact defeqC_etaR_arm hμ ih henv hs₆ haS rfl
                      rfl hbS hwa' hwb'
                  | _ =>
                    dsimp only
                    exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                | proj s₁' j₁ e₁ =>
                  have hwa'' : Expr.WScoped d
                    (Expr.proj s₁' j₁ (e₁)) := hwa'
                  have h1 : Expr.WScoped d (e₁) := by
                    simpa only [Expr.WScoped] using hwa''
                  cases b' with
                  | proj s₂' j₂ e₂ =>
                    dsimp only
                    have hwb'' : Expr.WScoped d
                      (Expr.proj s₂' j₂ (e₂)) := hwb'
                    have h2 : Expr.WScoped d (e₂) := by
                      simpa only [Expr.WScoped] using hwb''
                    by_cases hjj : (s₁' == s₂' && j₁ == j₂) = true
                    · rw [if_pos hjj, if_pos hjj]
                      refine SimC.bind
                        (ih.defeq hs₆ rfl rfl h1 h2)
                        (fun s₇ r₁ r₁' hs₇ hP₁ => ?_)
                      obtain rfl : r₁ = r₁' := hP₁
                      cases r₁ with
                      | true =>
                        simp only [↓reduceIte]
                        exact SimC.pure hs₇ rfl
                      | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        exact stuckIrrelC_sim hμ ih henv hs₇ haS hbS hwa' hwb'
                    · rw [if_neg hjj, if_neg hjj]
                      exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'
                  | lam t₂ b₂ m₂ =>
                    dsimp only
                    exact defeqC_etaR_arm hμ ih henv hs₆ haS rfl
                      rfl hbS hwa' hwb'
                  | _ =>
                    dsimp only
                    exact stuckIrrelC_sim hμ ih henv hs₆ haS hbS hwa' hwb'

/-- The lazy-delta *loop* simulates its specification, by induction on
the shared step budget (task #106). -/
theorem defeqLoopC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} :
    ∀ (n : Nat) (pi : Bool) {i j : Expr} {a b : Expr} {s₀ : CState},
      CSOK mode env s₀ →
      RelC i a → RelC j b →
      Expr.WScoped d a → Expr.WScoped d b →
      SimC mode env s₀ RelVC
        (defeqLoopI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d n pi i j)
        (defeqLoop mode (fueledFns mode env) env d n pi a b)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => SimC.throw
  | n + 1, pi, _, _, _, _, _, hs, hda, hdb, hwa, hwb => by
    simp only [defeqLoopI, defeqLoop]
    exact defeqStepC_sim hμ ih henv
      (fun pi' {_ _ _ _ _} h1 h2 h3 h4 h5 =>
        defeqLoopC_sim hμ ih henv n pi' h1 h2 h3 h4 h5)
      pi hs hda hdb hwa hwb

theorem defeqBodyC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i j : Expr} {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (defeqBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (defeqBody mode (fueledFns mode env) env d a b) :=
  defeqLoopC_sim hμ ih henv defeqLoopFuel true hs hdena hdenb hwa hwb

end Walks

end ConLeche.Cached
