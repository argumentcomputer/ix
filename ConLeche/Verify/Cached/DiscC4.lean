module

public import ConLeche.Verify.Cached.BinderLoopC
import ConLeche.Verify.BetaSpine

public section

/-!
# Cached body walks, part 4: head normalization and the whnf loop

The port of `ConLeche/Verify/DiscI4.lean` under the recipe (DESIGN.md,
task #163): simulation walks for the cached `whnfAppI`/`betaPeelI`,
`whnfCoreStepI`/`whnfCoreLoopI`/`whnfCoreBodyI`,
`whnfStepI`/`whnfLoopI`/`whnfBodyI`, `inferSpineI` and `inferBodyI`
(`ConLeche/Cached/CoreC.lean`) against the same pure fueled comparands
the interned walks use.  `SimAt → SimC`, denotation hypotheses →
`RelC`/`RelCL`, no `Ext`, node inversion by `cases` on
the `Expr` constructor.  The pure comparand side of every statement is
byte-identical to the interned original's.

The one code-shape deviation from the interned original (recorded at
the batch-10 re-sync) lives in `inferBodyI`: the binder-telescope peel
fuel is the constant `peelFuelM`, opaque to the binder-loop tails,
which quantify over the fuel.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche.Cached

open ConLeche.Expr

variable {mode : CheckMode}

section Walks

variable {env : Env} {f : Nat}

/-- The spine length the arity pre-check computes is the length of the
argument list the ι step builds. -/
private theorem iotaNumArgs_getAppArgsAcc (e : Expr) :
    ∀ acc : List Expr,
      iotaNumArgs e acc.length = (Expr.getAppArgsAccC e acc).length := by
  induction e with
  | app g a ihg _ =>
    intro acc
    rw [iotaNumArgs, Expr.getAppArgsAccC, ← ihg (a :: acc)]
    rfl
  | _ => intro acc; rfl

private theorem iotaNumArgs_zero (e : Expr) :
    iotaNumArgs e 0 = (Expr.getAppArgsC e).length :=
  iotaNumArgs_getAppArgsAcc e []

/-- Where the arity pre-check fails, the ι step has nothing to do: its
own guard returns `none` on exactly the same three grounds (the head is
not a constant, it is not a stored recursor, or the spine has the wrong
number of arguments or of levels). -/
private theorem iotaRecI_of_arityOk_false {mi : CheckMode} {r : CoreFnsI}
    {fe : FEnv} {d : Nat} {e : Expr} (h : iotaArityOk fe e = false) :
    iotaRecI mi r fe d e = pure none := by
  unfold iotaArityOk at h
  unfold iotaRecI
  cases hg : Expr.getAppFn e with
  | const c us =>
    rw [hg] at h
    dsimp only at h
    simp only [pure_bind]
    cases hf : fe.find? c with
    | none => rfl
    | some ci =>
      rw [hf] at h
      cases ci with
      | recInfo cv mI rP rules =>
        dsimp only at h ⊢
        rw [if_neg]
        rintro ⟨hlen, hlvl⟩
        rw [iotaNumArgs_zero, hlen, hlvl] at h
        simp at h
      | _ => rfl
  | _ => rfl

/-- The pre-check in the spine loop changes no verdict. -/
private theorem iotaArityOk_guard {mi : CheckMode} {r : CoreFnsI}
    {fe : FEnv} {d : Nat} {e : Expr} :
    (if iotaArityOk fe e then iotaRecI mi r fe d e else pure none)
      = iotaRecI mi r fe d e := by
  by_cases h : iotaArityOk fe e = true
  · rw [if_pos h]
  · rw [if_neg h, iotaRecI_of_arityOk_false (Bool.not_eq_true _ |>.mp h)]

private theorem whnfCoreStepM_unfold (env : Env) (d : Nat)
    (kM : Expr → FueledM Expr) (e : Expr) :
    whnfCoreStepM mode (fueledFns mode env) env d kM e =
    (match e with
    | .sort u => pure (.sort u)
    | .fvar idx ty => pure (.fvar idx ty)
    | .forallE ty body bi => pure (.forallE ty body bi)
    | .lam ty body mb => pure (.lam ty body mb)
    | .const n us => pure (.const n us)
    | .lit l => pure (.lit l)
    | .app g' a =>
      (fueledFns mode env).whnfCore d (Expr.app g' a).getAppFn >>= fun v =>
        whnfApp mode (fueledFns mode env) env d kM v (Expr.app g' a).getAppArgs
    | .proj sn i pe =>
      (fueledFns mode env).whnf d pe >>= fun e' =>
      projLitToCtor (fueledFns mode env) env d e' >>= fun e' =>
      match env.findProj? sn i with
      | some entry =>
        match e'.getAppFn with
        | .const c us =>
          if c = entry.ctor ∧ i < entry.numFields ∧
              e'.getAppArgs.length = entry.numParams + entry.numFields ∧
              us.length = entry.levelParams.length ∧
              entry.fireOk us = true then
            projCertAt (fueledFns mode env) env d mode.verifiedChecks mode.betaGate c us
                e'.getAppArgs >>=
              fun b =>
            if b then
              kM (e'.getAppArgs.getD (entry.numParams + i) (.bvar 0))
            else pure (.proj sn i e')
          else pure (.proj sn i e')
        | _ => pure (.proj sn i e')
      | none => pure (.proj sn i e')
    | .letE _ _ _ =>
      throw (.internal "whnfCore: `let` in an annotated expression")
    | .bvar _ =>
      throw (.notImplemented "whnf beyond the supported fragment")) := by
  cases e <;> rfl

mutual

/-- The bulk-beta argument loop simulates its pure mirror. -/
theorem whnfAppC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat}
    {kI : Expr → CheckCM Expr} {kM : Expr → FueledM Expr}
    (hk : ∀ {s : CState} {i : Expr} {ex : Expr}, CSOK mode env s →
      RelC i ex → Expr.WScoped d ex →
      SimC mode env s (RelEC d) (kI i) (kM ex)) :
    ∀ {args : List Expr} {xs : List Expr} {v : Expr} {vx : Expr}
      {s₀ : CState}, CSOK mode env s₀ →
      RelC v vx → Expr.WScoped d vx →
      RelCL args xs → (∀ x ∈ xs, Expr.WScoped d x) →
      SimC mode env s₀ (RelEC d)
        (whnfAppI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d kI v args)
        (whnfApp mode (fueledFns mode env) env d kM vx xs)
  | [], xs, v, vx, s₀, hs, hv, hwv, hargs, hwargs => by
    obtain rfl := hargs.nil_inv
    rw [whnfAppI.eq_def]
    dsimp only
    rw [whnfApp_nil]
    exact SimC.pure hs ⟨hv, hwv⟩
  | a :: rest, xs, v, vx, s₀, hs, hv, hwv, hargs, hwargs => by
    obtain ⟨xa, xs, rfl, hax, hrest⟩ := hargs.cons_inv
    rw [whnfAppI.eq_def]
    dsimp only
    obtain rfl := hv
    have hvr : RelC v v := rfl
    have hwxa : Expr.WScoped d xa := hwargs xa (List.mem_cons_self ..)
    have hwrest : ∀ x ∈ xs, Expr.WScoped d x :=
      fun x hx => hwargs x (List.mem_cons_of_mem _ hx)
    cases v with
    | lam ty body mb =>
      dsimp only
      have hwtb : Expr.WScoped d ty ∧ Expr.WScoped d body := by
        have hw' : Expr.WScoped d
          (.lam ty body mb) := hwv
        simpa only [Expr.WScoped] using hw'
      have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
        rw [show (Expr.instantiateList body [xa])
            = (Expr.instantiate1 body xa) by
          rw [Expr.instantiateList_cons, Expr.instantiateList_nil]]
        exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
      rw [show (Expr.lam ty body mb)
        = Expr.lam ty body mb from rfl, whnfApp_lam]
      unfold whnfAppLam
      -- task #161: the β gate reads the *same* `mb` on both sides
      -- (`eraseC` copies the binder meta), so one `by_cases`
      rw [betaSkip_of_verifiedChecks hμ]
      by_cases hgate : betaGateFires mode mb.pw = true
      · simp only [hgate, ↓reduceIte]
        exact betaPeelC_sim hμ ih henv hk hs rfl
          (RelCL.cons hax RelCL.nil) hwsub hrest hwrest
      have hgf : betaGateFires mode mb.pw = false := by
        simpa only [Bool.not_eq_true] using hgate
      simp only [hgf, Bool.false_eq_true, ↓reduceIte]
      refine SimC.bind (ih.inferIO hs hax hwxa)
        (fun s₁ ta tax hs₁ hP => ?_)
      obtain ⟨htad, hwta⟩ := hP
      refine SimC.bind (ih.defeq hs₁ htad rfl hwta hwtb.1)
        (fun s₂ b b' hs₂ hPb => ?_)
      obtain rfl : b = b' := hPb
      cases b with
      | true =>
        simp only [↓reduceIte]
        exact betaPeelC_sim hμ ih henv hk hs₂ rfl
          (RelCL.cons hax RelCL.nil) hwsub hrest hwrest
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine SimC.bind_left (pureC_eff hs₂
          (x := Expr.app (Expr.lam ty body mb) a)) (fun s₃ fa hs₃ hQfa => ?_)
        have hQfa' : RelC fa
            (Expr.app (.lam ty body mb) xa) := by
          show _ = _
          have hh := hQfa
          rw [hax] at hh
          exact hh
        refine SimC.of_eff (mkAppNM_eff hs₃ hQfa' hrest) _
          (fun r hQ => ⟨hQ, ?_⟩)
        refine Expr.WScoped.mkAppN ?_ hwrest
        simp only [Expr.WScoped]
        exact ⟨hwtb, hwxa⟩
    | bvar k =>
      have hnl : ∀ ty' body' mb',
          (Expr.bvar k) ≠ Expr.lam ty' body' mb' :=
        fun _ _ _ h => nomatch h
      rw [whnfApp_ne_lam _ _ _ _ hnl]
      exact whnfAppIotaC_sim hμ ih henv hk hs hvr hwv hax hwxa hrest hwrest
    | sort u =>
      have hnl : ∀ ty' body' mb',
          (Expr.sort u) ≠ Expr.lam ty' body' mb' :=
        fun _ _ _ h => nomatch h
      rw [whnfApp_ne_lam _ _ _ _ hnl]
      exact whnfAppIotaC_sim hμ ih henv hk hs hvr hwv hax hwxa hrest hwrest
    | const nm us =>
      have hnl : ∀ ty' body' mb',
          (Expr.const nm us) ≠ Expr.lam ty' body' mb' :=
        fun _ _ _ h => nomatch h
      rw [whnfApp_ne_lam _ _ _ _ hnl]
      exact whnfAppIotaC_sim hμ ih henv hk hs hvr hwv hax hwxa hrest hwrest
    | lit l =>
      have hnl : ∀ ty' body' mb',
          (Expr.lit l) ≠ Expr.lam ty' body' mb' :=
        fun _ _ _ h => nomatch h
      rw [whnfApp_ne_lam _ _ _ _ hnl]
      exact whnfAppIotaC_sim hμ ih henv hk hs hvr hwv hax hwxa hrest hwrest
    | fvar idx t =>
      have hnl : ∀ ty' body' mb',
          (Expr.fvar idx t) ≠ Expr.lam ty' body' mb' :=
        fun _ _ _ h => nomatch h
      rw [whnfApp_ne_lam _ _ _ _ hnl]
      exact whnfAppIotaC_sim hμ ih henv hk hs hvr hwv hax hwxa hrest hwrest
    | app f₂ a₂ =>
      have hnl : ∀ ty' body' mb',
          (Expr.app f₂ a₂) ≠ Expr.lam ty' body' mb' :=
        fun _ _ _ h => nomatch h
      rw [whnfApp_ne_lam _ _ _ _ hnl]
      exact whnfAppIotaC_sim hμ ih henv hk hs hvr hwv hax hwxa hrest hwrest
    | forallE t b mm =>
      have hnl : ∀ ty' body' mb',
          (Expr.forallE t b mm)
            ≠ Expr.lam ty' body' mb' :=
        fun _ _ _ h => nomatch h
      rw [whnfApp_ne_lam _ _ _ _ hnl]
      exact whnfAppIotaC_sim hμ ih henv hk hs hvr hwv hax hwxa hrest hwrest
    | letE t vv b =>
      have hnl : ∀ ty' body' mb',
          (Expr.letE t vv b)
            ≠ Expr.lam ty' body' mb' :=
        fun _ _ _ h => nomatch h
      rw [whnfApp_ne_lam _ _ _ _ hnl]
      exact whnfAppIotaC_sim hμ ih henv hk hs hvr hwv hax hwxa hrest hwrest
    | proj sn i pe =>
      have hnl : ∀ ty' body' mb',
          (Expr.proj sn i pe)
            ≠ Expr.lam ty' body' mb' :=
        fun _ _ _ h => nomatch h
      rw [whnfApp_ne_lam _ _ _ _ hnl]
      exact whnfAppIotaC_sim hμ ih henv hk hs hvr hwv hax hwxa hrest hwrest
  termination_by args _ => (args.length, 0)

/-- The iota arm of the loop simulates its mirror. -/
theorem whnfAppIotaC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat}
    {kI : Expr → CheckCM Expr} {kM : Expr → FueledM Expr}
    (hk : ∀ {s : CState} {i : Expr} {ex : Expr}, CSOK mode env s →
      RelC i ex → Expr.WScoped d ex →
      SimC mode env s (RelEC d) (kI i) (kM ex))
    {v a : Expr} {vx xa : Expr} {rest : List Expr} {xs : List Expr}
    {s₀ : CState} (hs : CSOK mode env s₀)
    (hv : RelC v vx) (hwv : Expr.WScoped d vx)
    (hax : RelC a xa) (hwxa : Expr.WScoped d xa)
    (hrest : RelCL rest xs) (hwrest : ∀ x ∈ xs, Expr.WScoped d x) :
    SimC mode env s₀ (RelEC d)
      (pure (Expr.app v a) >>= fun fa =>
        (if iotaArityOk (mkFEnv env) fa then
            iotaRecI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d fa
          else pure none) >>= fun o =>
        match o with
        | some e'' =>
          kI e'' >>= fun v' =>
            whnfAppI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d kI v' rest
        | none =>
          whnfAppI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d kI fa rest)
      (whnfAppIota mode (fueledFns mode env) env d kM vx xa xs) := by
    simp only [iotaArityOk_guard]
    unfold whnfAppIota
    have hwapp : Expr.WScoped d (.app vx xa) := by
      simp only [Expr.WScoped]
      exact ⟨hwv, hwxa⟩
    refine SimC.bind_left
      (pureC_eff hs (x := Expr.app v a))
      (fun s₁ fa hs₁ hQfa => ?_)
    have hQfa' : RelC fa (Expr.app vx xa) := by
      show _ = _
      have h := hQfa
      rw [hv, hax] at h
      exact h
    refine SimC.bind (iotaRecC_sim hμ ih henv hμ hs₁ hQfa' hwapp)
      (fun s₂ o ox hs₂ hPo => ?_)
    cases o with
    | some e'' =>
      cases ox with
      | none => exact absurd hPo (by simp [RelOC])
      | some e''x =>
        obtain ⟨hred, hwred⟩ := hPo
        refine SimC.bind (hk hs₂ hred hwred)
          (fun s₃ v' v'x hs₃ hP => ?_)
        obtain ⟨hv'd, hwv'⟩ := hP
        exact whnfAppC_sim hμ ih henv hk hs₃ hv'd hwv' hrest hwrest
    | none =>
      cases ox with
      | some e''x => exact absurd hPo (by simp [RelOC])
      | none =>
        exact whnfAppC_sim hμ ih henv hk hs₂ hQfa' hwapp hrest hwrest
  termination_by (rest.length, 1)

/-- The peel loop simulates its pure mirror. -/
theorem betaPeelC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat}
    {kI : Expr → CheckCM Expr} {kM : Expr → FueledM Expr}
    (hk : ∀ {s : CState} {i : Expr} {ex : Expr}, CSOK mode env s →
      RelC i ex → Expr.WScoped d ex →
      SimC mode env s (RelEC d) (kI i) (kM ex)) :
    ∀ {args : List Expr} {xs : List Expr} {t : Expr} {tx : Expr}
      {acc : List Expr} {ws : List Expr} {s₀ : CState}, CSOK mode env s₀ →
      RelC t tx → RelCL acc ws →
      Expr.WScoped d (tx.instantiateList ws) →
      RelCL args xs → (∀ x ∈ xs, Expr.WScoped d x) →
      SimC mode env s₀ (RelEC d)
        (betaPeelI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d kI t acc args)
        (betaPeel mode (fueledFns mode env) env d kM tx ws xs)
  | [], xs, t, tx, acc, ws, s₀, hs, ht, hacc, hwty, hargs, hwargs => by
    obtain rfl := hargs.nil_inv
    rw [betaPeelI.eq_def]
    dsimp only
    rw [betaPeel_nil]
    refine SimC.bind_left (instListM_eff (d := 0) hs ht hacc)
      (fun s₁ e' hs₁ hQ => ?_)
    exact hk hs₁ hQ hwty
  | a :: rest, xs, t, tx, acc, ws, s₀, hs, ht, hacc, hwty, hargs,
      hwargs => by
    obtain ⟨xa, xs, rfl, hax, hrest⟩ := hargs.cons_inv
    rw [betaPeelI.eq_def]
    dsimp only
    obtain rfl := ht
    have htr : RelC t t := rfl
    have hwxa : Expr.WScoped d xa := hwargs xa (List.mem_cons_self ..)
    have hwrest : ∀ x ∈ xs, Expr.WScoped d x :=
      fun x hx => hwargs x (List.mem_cons_of_mem _ hx)
    cases t with
    | lam ty body mb =>
      dsimp only
      rw [betaPeel_lam]
      unfold betaPeelLam
      have hcomp : Expr.WScoped d ((Expr.instantiateList ty ws))
          ∧ Expr.WScoped d ((Expr.instantiateList body ws 1)) := by
        have hw' : Expr.WScoped d
            ((Expr.lam ty body mb).instantiateList ws) :=
          hwty
        rw [instList_lam] at hw'
        simpa only [Expr.WScoped] using hw'
      have hwsub : Expr.WScoped d ((Expr.instantiateList body (xa :: ws))) := by
        rw [Expr.instantiateList_cons]
        exact Expr.WScoped.instantiate1_gen hwxa 0 hcomp.2
      -- task #161: the β gate, same datum on both sides
      rw [betaSkip_of_verifiedChecks hμ]
      by_cases hgate : betaGateFires mode mb.pw = true
      · simp only [hgate, ↓reduceIte]
        exact betaPeelC_sim hμ ih henv hk hs rfl
          (RelCL.cons hax hacc) hwsub hrest hwrest
      have hgf : betaGateFires mode mb.pw = false := by
        simpa only [Bool.not_eq_true] using hgate
      simp only [hgf, Bool.false_eq_true, ↓reduceIte]
      refine SimC.bind_left (instListM_eff (d := 0) hs rfl hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.inferIO hs₁ hax hwxa)
        (fun s₂ ta tax hs₂ hP => ?_)
      obtain ⟨htad, hwta⟩ := hP
      refine SimC.bind (ih.defeq hs₂ htad hQty hwta hcomp.1)
        (fun s₃ b b' hs₃ hPb => ?_)
      obtain rfl : b = b' := hPb
      cases b with
      | true =>
        simp only [↓reduceIte]
        exact betaPeelC_sim hμ ih henv hk hs₃ rfl
          (RelCL.cons hax hacc) hwsub hrest hwrest
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine SimC.bind_left (instListM_eff (d := 0) hs₃ htr hacc)
          (fun s₄ f' hs₄ hQf' => ?_)
        refine SimC.bind_left (pureC_eff hs₄ (x := Expr.app f' a)) (fun s₅ fa hs₅ hQfa => ?_)
        have hQfa' : RelC fa
            (Expr.app ((Expr.lam ty body
              mb).instantiateList ws) xa) := by
          show _ = _
          have hh := hQfa
          rw [hQf', hax] at hh
          exact hh
        refine SimC.of_eff (mkAppNM_eff hs₅ hQfa' hrest) _
          (fun r hQ => ⟨hQ, ?_⟩)
        refine Expr.WScoped.mkAppN ?_ hwrest
        simp only [Expr.WScoped]
        exact ⟨hwty, hwxa⟩
    | bvar k =>
      have hnl : ∀ ty' body' mb',
          (Expr.bvar k) ≠ Expr.lam ty' body' mb' :=
        fun _ _ _ h => nomatch h
      rw [betaPeel_ne_lam _ _ _ _ hnl]
      refine SimC.bind_left (instListM_eff (d := 0) hs htr hacc)
        (fun s₁ e' hs₁ hQ => ?_)
      refine SimC.bind (hk hs₁ hQ hwty) (fun s₂ vv vvx hs₂ hP => ?_)
      obtain ⟨hvd, hwv'⟩ := hP
      exact whnfAppC_sim hμ ih henv hk hs₂ hvd hwv'
        (RelCL.cons hax hrest) hwargs
    | sort u =>
      have hnl : ∀ ty' body' mb',
          (Expr.sort u) ≠ Expr.lam ty' body' mb' :=
        fun _ _ _ h => nomatch h
      rw [betaPeel_ne_lam _ _ _ _ hnl]
      refine SimC.bind_left (instListM_eff (d := 0) hs htr hacc)
        (fun s₁ e' hs₁ hQ => ?_)
      refine SimC.bind (hk hs₁ hQ hwty) (fun s₂ vv vvx hs₂ hP => ?_)
      obtain ⟨hvd, hwv'⟩ := hP
      exact whnfAppC_sim hμ ih henv hk hs₂ hvd hwv'
        (RelCL.cons hax hrest) hwargs
    | const nm us =>
      have hnl : ∀ ty' body' mb',
          (Expr.const nm us) ≠ Expr.lam ty' body' mb' :=
        fun _ _ _ h => nomatch h
      rw [betaPeel_ne_lam _ _ _ _ hnl]
      refine SimC.bind_left (instListM_eff (d := 0) hs htr hacc)
        (fun s₁ e' hs₁ hQ => ?_)
      refine SimC.bind (hk hs₁ hQ hwty) (fun s₂ vv vvx hs₂ hP => ?_)
      obtain ⟨hvd, hwv'⟩ := hP
      exact whnfAppC_sim hμ ih henv hk hs₂ hvd hwv'
        (RelCL.cons hax hrest) hwargs
    | lit l =>
      have hnl : ∀ ty' body' mb',
          (Expr.lit l) ≠ Expr.lam ty' body' mb' :=
        fun _ _ _ h => nomatch h
      rw [betaPeel_ne_lam _ _ _ _ hnl]
      refine SimC.bind_left (instListM_eff (d := 0) hs htr hacc)
        (fun s₁ e' hs₁ hQ => ?_)
      refine SimC.bind (hk hs₁ hQ hwty) (fun s₂ vv vvx hs₂ hP => ?_)
      obtain ⟨hvd, hwv'⟩ := hP
      exact whnfAppC_sim hμ ih henv hk hs₂ hvd hwv'
        (RelCL.cons hax hrest) hwargs
    | fvar idx tt =>
      have hnl : ∀ ty' body' mb',
          (Expr.fvar idx tt) ≠ Expr.lam ty' body' mb' :=
        fun _ _ _ h => nomatch h
      rw [betaPeel_ne_lam _ _ _ _ hnl]
      refine SimC.bind_left (instListM_eff (d := 0) hs htr hacc)
        (fun s₁ e' hs₁ hQ => ?_)
      refine SimC.bind (hk hs₁ hQ hwty) (fun s₂ vv vvx hs₂ hP => ?_)
      obtain ⟨hvd, hwv'⟩ := hP
      exact whnfAppC_sim hμ ih henv hk hs₂ hvd hwv'
        (RelCL.cons hax hrest) hwargs
    | app f₂ a₂ =>
      have hnl : ∀ ty' body' mb',
          (Expr.app f₂ a₂) ≠ Expr.lam ty' body' mb' :=
        fun _ _ _ h => nomatch h
      rw [betaPeel_ne_lam _ _ _ _ hnl]
      refine SimC.bind_left (instListM_eff (d := 0) hs htr hacc)
        (fun s₁ e' hs₁ hQ => ?_)
      refine SimC.bind (hk hs₁ hQ hwty) (fun s₂ vv vvx hs₂ hP => ?_)
      obtain ⟨hvd, hwv'⟩ := hP
      exact whnfAppC_sim hμ ih henv hk hs₂ hvd hwv'
        (RelCL.cons hax hrest) hwargs
    | forallE tt b mm =>
      have hnl : ∀ ty' body' mb',
          (Expr.forallE tt b mm)
            ≠ Expr.lam ty' body' mb' :=
        fun _ _ _ h => nomatch h
      rw [betaPeel_ne_lam _ _ _ _ hnl]
      refine SimC.bind_left (instListM_eff (d := 0) hs htr hacc)
        (fun s₁ e' hs₁ hQ => ?_)
      refine SimC.bind (hk hs₁ hQ hwty) (fun s₂ vv vvx hs₂ hP => ?_)
      obtain ⟨hvd, hwv'⟩ := hP
      exact whnfAppC_sim hμ ih henv hk hs₂ hvd hwv'
        (RelCL.cons hax hrest) hwargs
    | letE tt vv b =>
      have hnl : ∀ ty' body' mb',
          (Expr.letE tt vv b)
            ≠ Expr.lam ty' body' mb' :=
        fun _ _ _ h => nomatch h
      rw [betaPeel_ne_lam _ _ _ _ hnl]
      refine SimC.bind_left (instListM_eff (d := 0) hs htr hacc)
        (fun s₁ e' hs₁ hQ => ?_)
      refine SimC.bind (hk hs₁ hQ hwty) (fun s₂ vv' vvx hs₂ hP => ?_)
      obtain ⟨hvd, hwv'⟩ := hP
      exact whnfAppC_sim hμ ih henv hk hs₂ hvd hwv'
        (RelCL.cons hax hrest) hwargs
    | proj sn i pe =>
      have hnl : ∀ ty' body' mb',
          (Expr.proj sn i pe)
            ≠ Expr.lam ty' body' mb' :=
        fun _ _ _ h => nomatch h
      rw [betaPeel_ne_lam _ _ _ _ hnl]
      refine SimC.bind_left (instListM_eff (d := 0) hs htr hacc)
        (fun s₁ e' hs₁ hQ => ?_)
      refine SimC.bind (hk hs₁ hQ hwty) (fun s₂ vv vvx hs₂ hP => ?_)
      obtain ⟨hvd, hwv'⟩ := hP
      exact whnfAppC_sim hμ ih henv hk hs₂ hvd hwv'
        (RelCL.cons hax hrest) hwargs
  termination_by args _ => (args.length, 1)

end

theorem whnfCoreStepC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {kI : Expr → CheckCM Expr} {kM : Expr → FueledM Expr}
    (hk : ∀ {s : CState} {i : Expr} {ex : Expr}, CSOK mode env s →
      RelC i ex → Expr.WScoped d ex →
      SimC mode env s (RelEC d) (kI i) (kM ex))
    {i : Expr} {ex : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelEC d)
      (whnfCoreStepI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d kI i)
      (whnfCoreStepM mode (fueledFns mode env) env d kM ex) := by
  unfold whnfCoreStepI
  rw [whnfCoreStepM_unfold]
  obtain rfl := hden
  have hden : RelC i i := rfl
  cases i with
  | sort u => exact SimC.pure hs ⟨hden, hw⟩
  | fvar idx t => exact SimC.pure hs ⟨hden, hw⟩
  | forallE t b m => exact SimC.pure hs ⟨hden, hw⟩
  | lam t b m => exact SimC.pure hs ⟨hden, hw⟩
  | const nm us => exact SimC.pure hs ⟨hden, hw⟩
  | lit l => exact SimC.pure hs ⟨hden, hw⟩
  | bvar k => exact SimC.throw
  | letE t v b =>
    -- task #241: both sides are the same positive `.internal` error
    exact SimC.throw
  | app g' a =>
    dsimp only
    -- Bulk beta (task #50): the twin normalizes the spine head once and
    -- runs the argument loop against its mirror.
    refine SimC.pureB ?_
    refine SimC.pureB ?_
    have hhead : RelC (Expr.getAppFn (Expr.app g' a))
        ((Expr.app g' a).getAppFn) :=
      rfl
    have hargs : RelCL (Expr.getAppArgsC (Expr.app g' a))
        ((Expr.app g' a).getAppArgs) :=
      Expr.getAppArgsC_spec (Expr.app g' a)
    refine SimC.bind (ih.whnfCore hs hhead hw.getAppFn)
      (fun s₁ v vh hs₁ hP => ?_)
    exact whnfAppC_sim hμ ih henv hk hs₁ hP.1 hP.2 hargs hw.getAppArgs
  | proj sn ip pe =>
    dsimp only
    have hwpe : Expr.WScoped d pe := by
      have hw' : Expr.WScoped d (Expr.proj sn ip pe) := hw
      simpa only [Expr.WScoped] using hw'
    refine SimC.bind (ih.whnf hs rfl hwpe)
      (fun s₀' e₀ e₀x hs₀' hP₀ => ?_)
    obtain ⟨he₀d, hwe₀⟩ := hP₀
    refine SimC.bind (projLitToCtorC_sim ih hs₀' he₀d hwe₀)
      (fun s₁ e' e'x hs₁ hP => ?_)
    obtain ⟨rfl, hwe'⟩ := hP
    have he'd : RelC e' e' := rfl
    have hwproj : Expr.WScoped d (Expr.proj sn ip e') := by
      simpa only [Expr.WScoped] using hwe'
    refine SimC.bind_left (pureEq_eff hs₁ sn)
      (fun s₁' snw hs₁ hsnw => ?_)
    subst snw
    rw [mkFEnv_findProj?]
    cases hfp : env.findProj? sn ip with
    | none =>
      dsimp only
      exact SimC.of_eff
        (pureC_eff hs₁ (x := Expr.proj sn ip e')) _
        (fun pr hQ => ⟨hQ, hwproj⟩)
    | some entry =>
      dsimp only
      refine SimC.pureB ?_
      generalize hg : Expr.getAppFn e' = g
      cases g with
      | const c us =>
        dsimp only
        refine SimC.pureB ?_
        have hargs : RelCL (Expr.getAppArgsC e') ((Expr.getAppArgs e')) :=
          Expr.getAppArgsC_spec e'
        refine SimC.bind_left (pureEq_eff hs₁ (c == entry.ctor))
          (fun s₁b bq hs₁ hbq => ?_)
        subst bq
        rw [hargs.length]
        simp only [beq_iff_eq]
        have hwarg : Expr.WScoped d
            ((Expr.getAppArgs e').getD (entry.numParams + ip) (.bvar 0)) :=
          wscoped_getD hwe'.getAppArgs _
        split
        · rename_i hcond
          obtain ⟨rfl, -, -, -⟩ := hcond
          refine SimC.bind_left
            (pureBvar_eff hs₁ 0)
            (fun s₂ bvar0 hs₂ hQ0 => ?_)
          refine SimC.bind (projCertAtC_sim ih henv hs₂ hargs
              (fun x hx => hwe'.getAppArgs x hx))
            (fun s₃ b b' hs₃ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | true =>
            simp only [↓reduceIte]
            exact hk hs₃
              (RelCL.getD hQ0 (entry.numParams + ip) hargs) hwarg
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimC.of_eff
              (pureC_eff hs₃ (x := Expr.proj sn ip e')) _
              (fun pr hQ => ⟨hQ, hwproj⟩)
        · exact SimC.of_eff
            (pureC_eff hs₁ (x := Expr.proj sn ip e')) _
            (fun pr hQ => ⟨hQ, hwproj⟩)
      | bvar k =>
        exact SimC.of_eff
          (pureC_eff hs₁ (x := Expr.proj sn ip e')) _
          (fun pr hQ => ⟨hQ, hwproj⟩)
      | sort u =>
        exact SimC.of_eff
          (pureC_eff hs₁ (x := Expr.proj sn ip e')) _
          (fun pr hQ => ⟨hQ, hwproj⟩)
      | lit l =>
        exact SimC.of_eff
          (pureC_eff hs₁ (x := Expr.proj sn ip e')) _
          (fun pr hQ => ⟨hQ, hwproj⟩)
      | fvar idx t =>
        exact SimC.of_eff
          (pureC_eff hs₁ (x := Expr.proj sn ip e')) _
          (fun pr hQ => ⟨hQ, hwproj⟩)
      | app f₂ a₂ =>
        exact SimC.of_eff
          (pureC_eff hs₁ (x := Expr.proj sn ip e')) _
          (fun pr hQ => ⟨hQ, hwproj⟩)
      | lam t b m =>
        exact SimC.of_eff
          (pureC_eff hs₁ (x := Expr.proj sn ip e')) _
          (fun pr hQ => ⟨hQ, hwproj⟩)
      | forallE t b m =>
        exact SimC.of_eff
          (pureC_eff hs₁ (x := Expr.proj sn ip e')) _
          (fun pr hQ => ⟨hQ, hwproj⟩)
      | letE t v b =>
        exact SimC.of_eff
          (pureC_eff hs₁ (x := Expr.proj sn ip e')) _
          (fun pr hQ => ⟨hQ, hwproj⟩)
      | proj s' j' e'' =>
        exact SimC.of_eff
          (pureC_eff hs₁ (x := Expr.proj sn ip e')) _
          (fun pr hQ => ⟨hQ, hwproj⟩)

/-- The head-normalization *loop* simulates its mirror, by induction on
the shared step budget (task #106). -/
theorem whnfCoreLoopC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} :
    ∀ (n : Nat) {i : Expr} {ex : Expr} {s₀ : CState}, CSOK mode env s₀ →
      RelC i ex → Expr.WScoped d ex →
      SimC mode env s₀ (RelEC d)
        (whnfCoreLoopI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d n i)
        (whnfCoreLoopM mode (fueledFns mode env) env d n ex)
  | 0, _, _, _, _, _, _ => SimC.throw
  | n + 1, _, _, _, hs, hden, hw => by
    simp only [whnfCoreLoopI, whnfCoreLoopM]
    exact whnfCoreStepC_sim hμ ih henv
      (fun h1 h2 h3 => whnfCoreLoopC_sim hμ ih henv n h1 h2 h3) hs hden hw

/-- The cached head-normalization body simulates the chained
specification body: the loop run is reproduced by `whnfCoreBody` at
some knot fuel (`whnfCoreLoop_sound_body`). -/
theorem whnfCoreBodyC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i : Expr} {ex : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelEC d)
      (whnfCoreBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (whnfCoreBody mode (fueledFns mode env) env d ex) := by
  unfold whnfCoreBodyI
  exact SimC.wr (whnfCoreLoopC_sim hμ ih henv whnfCoreLoopFuel hs hden hw)
    (fun v F hF => whnfCoreLoop_sound_body d ex v whnfCoreLoopFuel F hF)

/-! ## The named concrete core's simulation (task #172, batch B2; the
R letter retired 2026-09-05)

**THE MEASUREMENT the batch was dispatched for.**  The walks above are
generic in `mode` (under `hμ : mode.verifiedChecks = true`, task
#185), so one proof serves every instantiation; the capstone is the
instance at `.verified`, where `hμ` is `rfl`.  The per-core letter is
therefore `exact` with no conversion step and no restated lemma: the
tower **INSTANTIATES**, and per concrete core the whnfCore family
costs **one proof line** (a term application) and **zero** new proof
steps.

`whnfCoreBodyRC_sim` was this letter's R twin.  It retired with its
subject when the R core went (2026-09-05): `whnfCoreBodyRC` and `cfgR`
are gone, so the statement has nothing left to be about.  The
measurement it recorded is not lost — it is the same one this letter
records, at the core that ships. -/

/-- The P core's head normalization simulates the specification. -/
theorem whnfCoreBodyPC_sim (ih : SSimC .verified env f) (henv : EnvWF env)
    {d : Nat} {i : Expr} {ex : Expr} {s₀ : CState}
    (hs : CSOK .verified env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC .verified env s₀ (RelEC d)
      (whnfCoreBodyPC (coreKnotI .verified (mkFEnv env) f) (mkFEnv env) d i)
      (whnfCoreBody .verified (fueledFns .verified env) env d ex) :=
  whnfCoreBodyC_sim rfl ih henv hs hden hw

end Walks

section Walks2

variable {env : Env} {f : Nat}

private theorem whnfStep_unfold (env : Env) (d : Nat)
    (kM : Expr → FueledM Expr) (e : Expr) :
    whnfStep (fueledFns mode env) env d kM e =
    ((fueledFns mode env).whnfCore d e >>= fun e₁ =>
      reduceNat (fueledFns mode env) env d e₁ >>= fun o =>
      match o with
      | some e₂ => kM e₂
      | none =>
        match unfoldDefinition env e₁ with
        | some e₂ => kM e₂
        | none => pure e₁) := rfl

/-- One iteration of the reduction loop simulates its specification
(task #106; the continuation is abstract, as in the body). -/
theorem whnfStepC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {kI : Expr → CheckCM Expr} {kM : Expr → FueledM Expr}
    (hk : ∀ {s : CState} {j : Expr} {ey : Expr}, CSOK mode env s →
      RelC j ey → Expr.WScoped d ey →
      SimC mode env s (RelEC d) (kI j) (kM ey))
    {i : Expr} {ex : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelEC d)
      (whnfStepI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d kI i)
      (whnfStep (fueledFns mode env) env d kM ex) := by
  unfold whnfStepI
  rw [whnfStep_unfold]
  refine SimC.bind (ih.whnfCore hs hden hw)
    (fun s₁ e₁ e₁x hs₁ hP => ?_)
  obtain ⟨he₁d, hwe₁⟩ := hP
  refine SimC.bind (reduceNatC_sim ih hs₁ he₁d hwe₁)
    (fun s₂ o ox hs₂ hPo => ?_)
  cases o with
  | some e₂ =>
    cases ox with
    | none => exact absurd hPo (by simp [RelOC])
    | some e₂x =>
      obtain ⟨he₂d, hwe₂⟩ := hPo
      exact hk hs₂ he₂d hwe₂
  | none =>
    cases ox with
    | some e₂x => exact absurd hPo (by simp [RelOC])
    | none =>
      refine SimC.bind_left (unfoldDefinitionC_eff hs₂ he₁d)
        (fun s₃ o₂ hs₃ hQ => ?_)
      cases hu : unfoldDefinition env e₁x with
      | some e₂x =>
        rw [hu] at hQ
        cases o₂ with
        | none => exact absurd hQ (by simp [OptEr])
        | some e₂ =>
          exact hk hs₃ hQ (unfoldDefinition_WScoped henv hu hwe₁)
      | none =>
        rw [hu] at hQ
        cases o₂ with
        | some e₂ => exact absurd hQ (by simp [OptEr])
        | none => exact SimC.pure hs₃ ⟨he₁d, hwe₁⟩

/-- The reduction loop simulates its specification, by induction on the
shared step budget (task #106). -/
theorem whnfLoopC_sim (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} :
    ∀ (n : Nat) {i : Expr} {ex : Expr} {s₀ : CState}, CSOK mode env s₀ →
      RelC i ex → Expr.WScoped d ex →
      SimC mode env s₀ (RelEC d)
        (whnfLoopI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d n i)
        (whnfLoop (fueledFns mode env) env d n ex)
  | 0, _, _, _, _, _, _ => SimC.throw
  | n + 1, _, _, _, hs, hden, hw => by
    simp only [whnfLoopI, whnfLoop]
    exact whnfStepC_sim ih henv
      (fun h1 h2 h3 => whnfLoopC_sim ih henv n h1 h2 h3) hs hden hw

theorem whnfBodyC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i : Expr} {ex : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelEC d)
      (whnfBodyI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (whnfBody (fueledFns mode env) env d ex) :=
  whnfLoopC_sim ih henv whnfLoopFuel hs hden hw

end Walks2

section Walks3

variable {env : Env} {f : Nat}

/-- The application-inference spine loop simulates its pure mirror. -/
theorem inferSpineC_sim (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} :
    ∀ {args : List Expr} {xs : List Expr} {ty : Expr} {tx : Expr}
      {acc : Array Expr} {ws : List Expr} {s₀ : CState}, CSOK mode env s₀ →
      RelC ty tx →
      RelCL acc.toList.reverse ws →
      Expr.WScoped d (tx.instantiateList ws) →
      RelCL args xs → (∀ x ∈ xs, Expr.WScoped d x) →
      SimC mode env s₀ (RelEC d)
        (inferSpineI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d ty acc args)
        (inferSpine (fueledFns mode env) d tx ws xs)
  | [], xs, ty, tx, acc, ws, s₀, hs, ht, hacc, hwty, hargs, hwargs => by
    obtain rfl := hargs.nil_inv
    rw [inferSpineI.eq_def]
    dsimp only
    rw [inferSpine_nil]
    exact SimC.of_eff (instListRevM_eff (d := 0) hs ht hacc) _
      (fun r hQ => ⟨hQ, hwty⟩)
  | a :: rest, xs, ty, tx, acc, ws, s₀, hs, ht, hacc, hwty, hargs,
      hwargs => by
    obtain ⟨xa, xs, rfl, hax, hrest⟩ := hargs.cons_inv
    rw [inferSpineI.eq_def]
    dsimp only
    obtain rfl := ht
    have htr : RelC ty ty := rfl
    have hwxa : Expr.WScoped d xa := hwargs xa (List.mem_cons_self ..)
    have hwrest : ∀ x ∈ xs, Expr.WScoped d x :=
      fun x hx => hwargs x (List.mem_cons_of_mem _ hx)
    cases ty with
    | forallE dom body mb =>
      dsimp only
      rw [show (Expr.forallE dom body mb)
        = Expr.forallE dom body mb from rfl, inferSpine_pi]
      unfold inferSpinePi
      have hcomp : Expr.WScoped d ((Expr.instantiateList dom ws))
          ∧ Expr.WScoped d ((Expr.instantiateList body ws 1)) := by
        have hw' : Expr.WScoped d
          ((Expr.forallE dom body mb).instantiateList ws) :=
          hwty
        rw [instList_forallE] at hw'
        simpa only [Expr.WScoped] using hw'
      have hwsub : Expr.WScoped d ((Expr.instantiateList body (xa :: ws))) := by
        rw [Expr.instantiateList_cons]
        exact Expr.WScoped.instantiate1_gen hwxa 0 hcomp.2
      dsimp only
      refine SimC.bind_left (instListRevM_eff (d := 0) hs rfl hacc)
        (fun s₁ dom' hs₁ hQdom => ?_)
      refine SimC.bind (ih.infer hs₁ hax hwxa)
        (fun s₂ ta tax hs₂ hP => ?_)
      obtain ⟨htad, hwta⟩ := hP
      refine SimC.bind (ih.defeq hs₂ htad hQdom hwta hcomp.1)
        (fun s₃ b b' hs₃ hPb => ?_)
      obtain rfl : b = b' := hPb
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact SimC.throw_bind
      | true =>
        simp only [↓reduceIte]
        exact inferSpineC_sim ih henv hs₃ rfl
          (by rw [toListRev_push]; exact RelCL.cons hax hacc) hwsub
          hrest hwrest
    | bvar k =>
      dsimp only
      have hnl : ∀ dom' body' bi',
          (Expr.bvar k) ≠ Expr.forallE dom' body' bi' :=
        fun _ _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body mb =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' m' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | sort u =>
      dsimp only
      have hnl : ∀ dom' body' bi',
          (Expr.sort u) ≠ Expr.forallE dom' body' bi' :=
        fun _ _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body mb =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' m' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | const nm us =>
      dsimp only
      have hnl : ∀ dom' body' bi',
          (Expr.const nm us) ≠ Expr.forallE dom' body' bi' :=
        fun _ _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body mb =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' m' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | lit l =>
      dsimp only
      have hnl : ∀ dom' body' bi',
          (Expr.lit l) ≠ Expr.forallE dom' body' bi' :=
        fun _ _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body mb =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' m' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | fvar idx tt =>
      dsimp only
      have hnl : ∀ dom' body' bi',
          (Expr.fvar idx tt) ≠ Expr.forallE dom' body' bi' :=
        fun _ _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body mb =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' m' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | app f₂ a₂ =>
      dsimp only
      have hnl : ∀ dom' body' bi',
          (Expr.app f₂ a₂) ≠ Expr.forallE dom' body' bi' :=
        fun _ _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body mb =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' m' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | lam tt b mm =>
      dsimp only
      have hnl : ∀ dom' body' bi',
          (Expr.lam tt b mm) ≠ Expr.forallE dom' body' bi' :=
        fun _ _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body mb =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' m' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | letE tt vv b =>
      dsimp only
      have hnl : ∀ dom' body' bi',
          (Expr.letE tt vv b) ≠ Expr.forallE dom' body' bi' :=
        fun _ _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body mb =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' m' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | proj sn j pe =>
      dsimp only
      have hnl : ∀ dom' body' bi',
          (Expr.proj sn j pe) ≠ Expr.forallE dom' body' bi' :=
        fun _ _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body mb =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' m' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw

theorem inferSpineIOC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} :
    ∀ {args : List Expr} {xs : List Expr} {ty : Expr} {tx : Expr}
      {acc : Array Expr} {ws : List Expr} {s₀ : CState}, CSOK mode env s₀ →
      RelC ty tx →
      RelCL acc.toList.reverse ws →
      Expr.WScoped d (tx.instantiateList ws) →
      RelCL args xs → (∀ x ∈ xs, Expr.WScoped d x) →
      SimC mode env s₀ (RelEC d)
        (inferSpineIOI mode
          (CoreFnsI.ioView (coreKnotI mode (mkFEnv env) f)) (mkFEnv env)
          d ty acc args)
        (inferSpineIO (fueledFns mode env) d tx ws xs)
  | [], xs, ty, tx, acc, ws, s₀, hs, ht, hacc, hwty, hargs, hwargs => by
    obtain rfl := hargs.nil_inv
    rw [inferSpineIOI.eq_def]
    dsimp only
    rw [inferSpineIO_nil]
    exact SimC.of_eff (instListRevM_eff (d := 0) hs ht hacc) _
      (fun r hQ => ⟨hQ, hwty⟩)
  | a :: rest, xs, ty, tx, acc, ws, s₀, hs, ht, hacc, hwty, hargs,
      hwargs => by
    obtain ⟨xa, xs, rfl, hax, hrest⟩ := hargs.cons_inv
    rw [inferSpineIOI.eq_def]
    dsimp only
    obtain rfl := ht
    have htr : RelC ty ty := rfl
    have hwxa : Expr.WScoped d xa := hwargs xa (List.mem_cons_self ..)
    have hwrest : ∀ x ∈ xs, Expr.WScoped d x :=
      fun x hx => hwargs x (List.mem_cons_of_mem _ hx)
    cases ty with
    | forallE dom body mb =>
      dsimp only
      rw [show (Expr.forallE dom body mb)
        = Expr.forallE dom body mb from rfl, inferSpineIO_pi]
      unfold inferSpineIOPi
      have hcomp : Expr.WScoped d ((Expr.instantiateList dom ws))
          ∧ Expr.WScoped d ((Expr.instantiateList body ws 1)) := by
        have hw' : Expr.WScoped d
          ((Expr.forallE dom body mb).instantiateList ws) :=
          hwty
        rw [instList_forallE] at hw'
        simpa only [Expr.WScoped] using hw'
      have hwsub : Expr.WScoped d ((Expr.instantiateList body (xa :: ws))) := by
        rw [Expr.instantiateList_cons]
        exact Expr.WScoped.instantiate1_gen hwxa 0 hcomp.2
      try dsimp only
      by_cases hg2 : mb.pw.isNever = true
      · simp only [ioSkip_of_verifiedChecks hμ, hg2, ↓reduceIte]
        exact inferSpineIOC_sim hμ ih henv hs rfl
          (by rw [toListRev_push]; exact RelCL.cons hax hacc) hwsub
          hrest hwrest
      · simp only [ioSkip_of_verifiedChecks hμ, hg2, Bool.false_eq_true, ↓reduceIte]
        refine SimC.bind_left (instListRevM_eff (d := 0) hs rfl hacc)
          (fun s₁ dom' hs₁ hQdom => ?_)
        refine SimC.bind (ih.inferIO hs₁ hax hwxa)
          (fun s₂ ta tax hs₂ hP => ?_)
        obtain ⟨htad, hwta⟩ := hP
        refine SimC.bind (ih.defeq hs₂ htad hQdom hwta hcomp.1)
          (fun s₃ b b' hs₃ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineIOC_sim hμ ih henv hs₃ rfl
            (by rw [toListRev_push]; exact RelCL.cons hax hacc) hwsub
            hrest hwrest
    | bvar k =>
      dsimp only
      have hnl : ∀ dom' body' bi',
          (Expr.bvar k) ≠ Expr.forallE dom' body' bi' :=
        fun _ _ _ h => nomatch h
      rw [inferSpineIO_ne_pi _ _ hnl]
      unfold inferSpineIOWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body mb =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        by_cases hg2 : mb.pw.isNever = true
        · simp only [ioSkip_of_verifiedChecks hμ, hg2, ↓reduceIte]
          exact inferSpineIOC_sim hμ ih henv hs₂ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
        · simp only [ioSkip_of_verifiedChecks hμ, hg2, Bool.false_eq_true, ↓reduceIte]
          refine SimC.bind (ih.inferIO hs₂ hax hwxa)
            (fun s₃ ta tax hs₃ hP₃ => ?_)
          obtain ⟨htad, hwta⟩ := hP₃
          refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
            (fun s₄ b b' hs₄ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimC.throw_bind
          | true =>
            simp only [↓reduceIte]
            exact inferSpineIOC_sim hμ ih henv hs₄ rfl
              (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
              hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' m' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | sort u =>
      dsimp only
      have hnl : ∀ dom' body' bi',
          (Expr.sort u) ≠ Expr.forallE dom' body' bi' :=
        fun _ _ _ h => nomatch h
      rw [inferSpineIO_ne_pi _ _ hnl]
      unfold inferSpineIOWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body mb =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        by_cases hg2 : mb.pw.isNever = true
        · simp only [ioSkip_of_verifiedChecks hμ, hg2, ↓reduceIte]
          exact inferSpineIOC_sim hμ ih henv hs₂ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
        · simp only [ioSkip_of_verifiedChecks hμ, hg2, Bool.false_eq_true, ↓reduceIte]
          refine SimC.bind (ih.inferIO hs₂ hax hwxa)
            (fun s₃ ta tax hs₃ hP₃ => ?_)
          obtain ⟨htad, hwta⟩ := hP₃
          refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
            (fun s₄ b b' hs₄ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimC.throw_bind
          | true =>
            simp only [↓reduceIte]
            exact inferSpineIOC_sim hμ ih henv hs₄ rfl
              (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
              hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' m' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | const nm us =>
      dsimp only
      have hnl : ∀ dom' body' bi',
          (Expr.const nm us) ≠ Expr.forallE dom' body' bi' :=
        fun _ _ _ h => nomatch h
      rw [inferSpineIO_ne_pi _ _ hnl]
      unfold inferSpineIOWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body mb =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        by_cases hg2 : mb.pw.isNever = true
        · simp only [ioSkip_of_verifiedChecks hμ, hg2, ↓reduceIte]
          exact inferSpineIOC_sim hμ ih henv hs₂ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
        · simp only [ioSkip_of_verifiedChecks hμ, hg2, Bool.false_eq_true, ↓reduceIte]
          refine SimC.bind (ih.inferIO hs₂ hax hwxa)
            (fun s₃ ta tax hs₃ hP₃ => ?_)
          obtain ⟨htad, hwta⟩ := hP₃
          refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
            (fun s₄ b b' hs₄ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimC.throw_bind
          | true =>
            simp only [↓reduceIte]
            exact inferSpineIOC_sim hμ ih henv hs₄ rfl
              (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
              hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' m' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | lit l =>
      dsimp only
      have hnl : ∀ dom' body' bi',
          (Expr.lit l) ≠ Expr.forallE dom' body' bi' :=
        fun _ _ _ h => nomatch h
      rw [inferSpineIO_ne_pi _ _ hnl]
      unfold inferSpineIOWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body mb =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        by_cases hg2 : mb.pw.isNever = true
        · simp only [ioSkip_of_verifiedChecks hμ, hg2, ↓reduceIte]
          exact inferSpineIOC_sim hμ ih henv hs₂ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
        · simp only [ioSkip_of_verifiedChecks hμ, hg2, Bool.false_eq_true, ↓reduceIte]
          refine SimC.bind (ih.inferIO hs₂ hax hwxa)
            (fun s₃ ta tax hs₃ hP₃ => ?_)
          obtain ⟨htad, hwta⟩ := hP₃
          refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
            (fun s₄ b b' hs₄ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimC.throw_bind
          | true =>
            simp only [↓reduceIte]
            exact inferSpineIOC_sim hμ ih henv hs₄ rfl
              (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
              hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' m' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | fvar idx tt =>
      dsimp only
      have hnl : ∀ dom' body' bi',
          (Expr.fvar idx tt) ≠ Expr.forallE dom' body' bi' :=
        fun _ _ _ h => nomatch h
      rw [inferSpineIO_ne_pi _ _ hnl]
      unfold inferSpineIOWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body mb =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        by_cases hg2 : mb.pw.isNever = true
        · simp only [ioSkip_of_verifiedChecks hμ, hg2, ↓reduceIte]
          exact inferSpineIOC_sim hμ ih henv hs₂ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
        · simp only [ioSkip_of_verifiedChecks hμ, hg2, Bool.false_eq_true, ↓reduceIte]
          refine SimC.bind (ih.inferIO hs₂ hax hwxa)
            (fun s₃ ta tax hs₃ hP₃ => ?_)
          obtain ⟨htad, hwta⟩ := hP₃
          refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
            (fun s₄ b b' hs₄ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimC.throw_bind
          | true =>
            simp only [↓reduceIte]
            exact inferSpineIOC_sim hμ ih henv hs₄ rfl
              (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
              hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' m' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | app f₂ a₂ =>
      dsimp only
      have hnl : ∀ dom' body' bi',
          (Expr.app f₂ a₂) ≠ Expr.forallE dom' body' bi' :=
        fun _ _ _ h => nomatch h
      rw [inferSpineIO_ne_pi _ _ hnl]
      unfold inferSpineIOWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body mb =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        by_cases hg2 : mb.pw.isNever = true
        · simp only [ioSkip_of_verifiedChecks hμ, hg2, ↓reduceIte]
          exact inferSpineIOC_sim hμ ih henv hs₂ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
        · simp only [ioSkip_of_verifiedChecks hμ, hg2, Bool.false_eq_true, ↓reduceIte]
          refine SimC.bind (ih.inferIO hs₂ hax hwxa)
            (fun s₃ ta tax hs₃ hP₃ => ?_)
          obtain ⟨htad, hwta⟩ := hP₃
          refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
            (fun s₄ b b' hs₄ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimC.throw_bind
          | true =>
            simp only [↓reduceIte]
            exact inferSpineIOC_sim hμ ih henv hs₄ rfl
              (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
              hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' m' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | lam tt b mm =>
      dsimp only
      have hnl : ∀ dom' body' bi',
          (Expr.lam tt b mm) ≠ Expr.forallE dom' body' bi' :=
        fun _ _ _ h => nomatch h
      rw [inferSpineIO_ne_pi _ _ hnl]
      unfold inferSpineIOWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body mb =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        by_cases hg2 : mb.pw.isNever = true
        · simp only [ioSkip_of_verifiedChecks hμ, hg2, ↓reduceIte]
          exact inferSpineIOC_sim hμ ih henv hs₂ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
        · simp only [ioSkip_of_verifiedChecks hμ, hg2, Bool.false_eq_true, ↓reduceIte]
          refine SimC.bind (ih.inferIO hs₂ hax hwxa)
            (fun s₃ ta tax hs₃ hP₃ => ?_)
          obtain ⟨htad, hwta⟩ := hP₃
          refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
            (fun s₄ b b' hs₄ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimC.throw_bind
          | true =>
            simp only [↓reduceIte]
            exact inferSpineIOC_sim hμ ih henv hs₄ rfl
              (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
              hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' m' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | letE tt vv b =>
      dsimp only
      have hnl : ∀ dom' body' bi',
          (Expr.letE tt vv b) ≠ Expr.forallE dom' body' bi' :=
        fun _ _ _ h => nomatch h
      rw [inferSpineIO_ne_pi _ _ hnl]
      unfold inferSpineIOWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body mb =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        by_cases hg2 : mb.pw.isNever = true
        · simp only [ioSkip_of_verifiedChecks hμ, hg2, ↓reduceIte]
          exact inferSpineIOC_sim hμ ih henv hs₂ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
        · simp only [ioSkip_of_verifiedChecks hμ, hg2, Bool.false_eq_true, ↓reduceIte]
          refine SimC.bind (ih.inferIO hs₂ hax hwxa)
            (fun s₃ ta tax hs₃ hP₃ => ?_)
          obtain ⟨htad, hwta⟩ := hP₃
          refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
            (fun s₄ b b' hs₄ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimC.throw_bind
          | true =>
            simp only [↓reduceIte]
            exact inferSpineIOC_sim hμ ih henv hs₄ rfl
              (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
              hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' m' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw
    | proj sn j pe =>
      dsimp only
      have hnl : ∀ dom' body' bi',
          (Expr.proj sn j pe) ≠ Expr.forallE dom' body' bi' :=
        fun _ _ _ h => nomatch h
      rw [inferSpineIO_ne_pi _ _ hnl]
      unfold inferSpineIOWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨rfl, hww⟩ := hP
      cases w with
      | forallE dom body mb =>
        dsimp only
        have hwtb : Expr.WScoped d dom
            ∧ Expr.WScoped d body := by
          have hw' : Expr.WScoped d
            (.forallE dom body mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((Expr.instantiateList body [xa])) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        by_cases hg2 : mb.pw.isNever = true
        · simp only [ioSkip_of_verifiedChecks hμ, hg2, ↓reduceIte]
          exact inferSpineIOC_sim hμ ih henv hs₂ rfl
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
        · simp only [ioSkip_of_verifiedChecks hμ, hg2, Bool.false_eq_true, ↓reduceIte]
          refine SimC.bind (ih.inferIO hs₂ hax hwxa)
            (fun s₃ ta tax hs₃ hP₃ => ?_)
          obtain ⟨htad, hwta⟩ := hP₃
          refine SimC.bind (ih.defeq hs₃ htad rfl hwta hwtb.1)
            (fun s₄ b b' hs₄ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimC.throw_bind
          | true =>
            simp only [↓reduceIte]
            exact inferSpineIOC_sim hμ ih henv hs₄ rfl
              (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
              hwsub hrest hwrest
      | bvar k' => exact SimC.throw
      | sort u' => exact SimC.throw
      | const nm' us' => exact SimC.throw
      | lit l' => exact SimC.throw
      | fvar idx' t' => exact SimC.throw
      | app f' a' => exact SimC.throw
      | lam t' b' m' => exact SimC.throw
      | letE t' v' b' => exact SimC.throw
      | proj s' j' e' => exact SimC.throw

theorem inferBodyC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i : Expr} {ex : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelEC d)
      (inferBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (inferBody mode (fueledFns mode env) env d ex) := by
  unfold inferBodyI
  obtain rfl := hden
  have hden : RelC i i := rfl
  cases i with
  | sort u =>
    dsimp only
    unfold inferBody
    dsimp only
    try dsimp only
    refine SimC.bind_left (pureEq_eff hs (Level.succ u))
      (fun s₁ su hs₁ hsu => ?_)
    subst su
    exact SimC.of_eff
      (pureC_eff hs₁ (x := Expr.sort (Level.succ u))) _
      (fun r hQ => ⟨hQ, by simp [Expr.WScoped]⟩)
  | bvar k =>
    dsimp only
    unfold inferBody
    dsimp only
    try dsimp only
    exact SimC.throw
  | letE t v b =>
    -- task #241: both sides are the same positive `.internal` error
    exact SimC.throw
  | fvar idx t =>
    simp only [inferBodyI, inferBody]
    have h' : idx < d ∧ Expr.WScoped idx t := by
      have hw' : Expr.WScoped d (Expr.fvar idx t) := hw
      simpa only [Expr.WScoped] using hw'
    by_cases hidx : idx < d
    · rw [if_pos hidx, if_pos hidx]
      exact SimC.pure hs
        ⟨rfl, Expr.WScoped.mono (Nat.le_of_lt h'.1) h'.2⟩
    · rw [if_neg hidx, if_neg hidx]
      exact SimC.throw
  | lit l =>
    dsimp only
    unfold inferBody
    dsimp only
    refine SimC.bind_pure_right ?_
    try dsimp only
    cases l with
    | natVal k =>
      rw [natLitSupportedF_eq]
      by_cases hg : natLitSupported env
      · rw [if_pos hg, if_pos hg]
        refine SimC.bind_left (pureEq_eff hs natName)
          (fun s₁ ni hs₁ hQni => ?_)
        subst ni
        exact SimC.of_eff
          (pureC_eff hs₁ (x := Expr.const natName [])) _
          (fun r hQ => ⟨hQ, by simp [Expr.WScoped]⟩)
      · rw [if_neg hg, if_neg hg]
        exact SimC.throw
    | strVal str =>
      rw [strLitSupportedF_eq]
      by_cases hg : strLitSupported env
      · rw [if_pos hg, if_pos hg]
        refine SimC.bind_left (pureEq_eff hs stringName)
          (fun s₁ ni hs₁ hQni => ?_)
        subst ni
        exact SimC.of_eff
          (pureC_eff hs₁ (x := Expr.const stringName [])) _
          (fun r hQ => ⟨hQ, by simp [Expr.WScoped]⟩)
      · rw [if_neg hg, if_neg hg]
        exact SimC.throw
  | const nm us =>
    dsimp only
    unfold inferBody
    dsimp only
    refine SimC.bind_pure_right ?_
    try dsimp only
    refine SimC.bind_left (pureEq_eff hs nm)
      (fun s₀' nw hs hnw => ?_)
    subst nw
    rw [mkFEnv_find?]
    cases hfn : env.find? nm with
    | none => exact SimC.throw
    | some ci =>
      dsimp only
      by_cases htw : (!ci.isTowerEntry) = true
      · rw [if_pos htw, if_pos htw]
        by_cases hlen : us.length = ci.toConstantVal.levelParams.length
        · rw [if_pos hlen, if_pos hlen]
          refine SimC.of_eff (constTyAtM_eff hs hfn) _ (fun r hQ => ?_)
          refine ⟨hQ, ?_⟩
          obtain ⟨htf, -⟩ := henv _ (find?_mem hfn)
          exact wscoped_instLevels_of_not_hasFvar htf _ _
        · rw [if_neg hlen, if_neg hlen]
          exact SimC.throw_bind
      · rw [if_neg htw, if_neg htw]
        exact SimC.throw_bind
  | forallE t b m =>
    dsimp only
    have hwtb : Expr.WScoped d t ∧ Expr.WScoped d b := by
      have hw' : Expr.WScoped d
        (Expr.forallE t b m) := hw
      simpa only [Expr.WScoped] using hw'
    unfold inferBody
    dsimp only
    try dsimp only
    refine SimC.bind (ih.infer hs rfl hwtb.1)
      (fun s₁ tty ttyx hs₁ hP => ?_)
    obtain ⟨httyd, hwtty⟩ := hP
    refine SimC.bind (ih.whnf hs₁ httyd hwtty)
      (fun s₂ w wx hs₂ hP₂ => ?_)
    obtain ⟨rfl, hww⟩ := hP₂
    cases w with
    | sort u =>
      dsimp only
      refine SimC.bind_left
        (pureC_eff hs₂ (x := Expr.fvar d t))
        (fun s₃ fv hs₃ hQfv => ?_)
      refine SimC.bind_left (peelFuelM_eff hs₃)
        (fun s₃f fuel hs₃f _hQfuel => ?_)
      exact inferPisC_tail_sim ih hs₃f rfl rfl hQfv hwtb.1 hwtb.2
    | bvar k' => exact SimC.throw
    | const nm' us' => exact SimC.throw
    | lit l' => exact SimC.throw
    | fvar idx' t' => exact SimC.throw
    | app f' a' => exact SimC.throw
    | lam t' b' m' => exact SimC.throw
    | forallE t' b' m' => exact SimC.throw
    | letE t' v' b' => exact SimC.throw
    | proj s' j' e' => exact SimC.throw
  | lam t b m =>
    dsimp only
    have hwtb : Expr.WScoped d t ∧ Expr.WScoped d b := by
      have hw' : Expr.WScoped d
        (Expr.lam t b m) := hw
      simpa only [Expr.WScoped] using hw'
    unfold inferBody
    dsimp only
    try dsimp only
    obtain ⟨mpw⟩ := m
    refine SimC.bind (ih.infer hs rfl hwtb.1)
      (fun s₁ tty ttyx hs₁ hP => ?_)
    obtain ⟨httyd, hwtty⟩ := hP
    refine SimC.bind (ih.whnf hs₁ httyd hwtty)
      (fun s₂ w wx hs₂ hP₂ => ?_)
    obtain ⟨rfl, hww⟩ := hP₂
    cases w with
    | sort u =>
      dsimp only
      refine SimC.bind_left
        (pureC_eff hs₂ (x := Expr.fvar d t))
        (fun s₃ fv hs₃ hQfv => ?_)
      refine SimC.bind_left (peelFuelM_eff hs₃)
        (fun s₃f fuel hs₃f _hQfuel => ?_)
      exact inferLamsC_tail_sim ih henv hs₃f rfl rfl hQfv
        hwtb.1 hwtb.2
    | bvar k' => exact SimC.throw
    | const nm' us' => exact SimC.throw
    | lit l' => exact SimC.throw
    | fvar idx' t' => exact SimC.throw
    | app f' a' => exact SimC.throw
    | lam t' b' m' => exact SimC.throw
    | forallE t' b' m' => exact SimC.throw
    | letE t' v' b' => exact SimC.throw
    | proj s' j' e' => exact SimC.throw
  | app g' a =>
    dsimp only
    -- Bulk telescope consumption (task #50): the twin infers the spine
    -- head once and walks the Π-telescope; `inferSpine_sound_body`
    -- reproduces the loop's verdict in the chained body.
    refine SimC.wr ?_
      (fun v F hF => inferSpine_sound_body d g' a v F hF)
    refine SimC.pureB ?_
    refine SimC.pureB ?_
    have hhead : RelC (Expr.getAppFn (Expr.app g' a))
        ((Expr.app g' a).getAppFn) :=
      rfl
    have hargsSpec : RelCL (Expr.getAppArgsC (Expr.app g' a))
        ((Expr.app g' a).getAppArgs) :=
      Expr.getAppArgsC_spec (Expr.app g' a)
    refine SimC.bind (ih.infer hs hhead hw.getAppFn)
      (fun s₁ tf tfx hs₁ hP => ?_)
    refine inferSpineC_sim ih henv hs₁ hP.1
      (by rw [toListRev_empty]; exact RelCL.nil) ?_
      hargsSpec hw.getAppArgs
    rw [Expr.instantiateList_nil]
    exact hP.2
  | proj sn ip pe =>
    dsimp only
    have hwpe : Expr.WScoped d pe := by
      have hw' : Expr.WScoped d (Expr.proj sn ip pe) := hw
      simpa only [Expr.WScoped] using hw'
    unfold inferBody
    dsimp only
    try dsimp only
    refine SimC.bind (ih.infer hs rfl hwpe)
      (fun s₁ tpe tpex hs₁ hP => ?_)
    obtain ⟨htped, hwtpe⟩ := hP
    refine SimC.bind (ih.whnf hs₁ htped hwtpe)
      (fun s₂ te tex hs₂ hP₂ => ?_)
    obtain ⟨rfl, hwte⟩ := hP₂
    refine SimC.pureB ?_
    generalize hg : Expr.getAppFn te = g
    cases g with
    | const T us =>
      dsimp only
      refine SimC.bind_left (pureEq_eff hs₂ T)
        (fun s₂' Tw hs₂ hTw => ?_)
      subst Tw
      rw [mkFEnv_findProj?]
      cases hfp : env.findProj? T ip with
      | none => exact SimC.throw
      | some entry =>
        dsimp only
        refine SimC.pureB ?_
        have htargs : RelCL (Expr.getAppArgsC te) ((Expr.getAppArgs te)) :=
          Expr.getAppArgsC_spec te
        rw [htargs.length]
        split
        · -- task #175 S1: the body at the spine and the subject —
          -- `Expr = Expr` (the identity world), so the two results
          -- coincide once `RelCL` rewrites the spine
          rename_i hcond
          rw [htargs]
          have hres : SimC mode env s₂' (RelEC d)
              (pure (entry.typeAtI us (Expr.getAppArgs te) pe))
              (pure (entry.typeAt us (Expr.getAppArgs te) pe) : FueledM Expr) :=
            SimC.pure hs₂ ⟨ProjEntry.typeAtI_eq entry us _ pe,
              projEntry_typeAt_WScoped henv hfp us
              hcond.2.1
              (fun a ha => hwte.getAppArgs a ha) hwpe⟩
          -- the Prop guard (task #175 W4c) runs no walk of its own
          split
          · split
            · exact hres
            · exact SimC.throw
          · exact hres
        · exact SimC.throw
    | bvar k' => exact SimC.throw
    | sort u' => exact SimC.throw
    | lit l' => exact SimC.throw
    | fvar idx' t' => exact SimC.throw
    | app f' a' => exact SimC.throw
    | lam t' b' m' => exact SimC.throw
    | forallE t' b' m' => exact SimC.throw
    | letE t' v' b' => exact SimC.throw
    | proj s' j' e' => exact SimC.throw

/-- The io inference body's walk (task #172 B4), at the gated mode
(the io memo step consults it only there; the gate-off slot is the
full-inference memo, covered by `inferBodyC_sim`).  The leaf, `letE`
and `proj` arms are `inferBodyC_sim`'s with the recursion at the io
slot; the two binder arms are the io lane's own **chained** clauses;
the application arm is the gated spine with
`inferSpineIO_sound_body`. -/
theorem inferBodyIOC_sim (hμ : mode.verifiedChecks = true) (hgb : mode.betaGate = true)
    (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i : Expr} {ex : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelEC d)
      (inferBodyIOI mode
        (CoreFnsI.ioView (coreKnotI mode (mkFEnv env) f)) (mkFEnv env) d i)
      (inferBodyIO mode (CoreFns.ioView (fueledFns mode env)) env d ex) := by
  unfold inferBodyIOI
  obtain rfl := hden
  have hden : RelC i i := rfl
  cases i with
  | sort u =>
    dsimp only
    unfold inferBodyI inferBodyIO
    dsimp only
    try dsimp only
    refine SimC.bind_left (pureEq_eff hs (Level.succ u))
      (fun s₁ su hs₁ hsu => ?_)
    subst su
    exact SimC.of_eff
      (pureC_eff hs₁ (x := Expr.sort (Level.succ u))) _
      (fun r hQ => ⟨hQ, by simp [Expr.WScoped]⟩)
  | bvar k =>
    dsimp only
    unfold inferBodyI inferBodyIO
    dsimp only
    try dsimp only
    exact SimC.throw
  | letE t v b =>
    -- task #241: both sides are the same positive `.internal` error
    exact SimC.throw
  | fvar idx t =>
    simp only [inferBodyI, inferBodyIO]
    have h' : idx < d ∧ Expr.WScoped idx t := by
      have hw' : Expr.WScoped d (Expr.fvar idx t) := hw
      simpa only [Expr.WScoped] using hw'
    by_cases hidx : idx < d
    · rw [if_pos hidx, if_pos hidx]
      exact SimC.pure hs
        ⟨rfl, Expr.WScoped.mono (Nat.le_of_lt h'.1) h'.2⟩
    · rw [if_neg hidx, if_neg hidx]
      exact SimC.throw
  | lit l =>
    dsimp only
    unfold inferBodyI inferBodyIO
    dsimp only
    refine SimC.bind_pure_right ?_
    try dsimp only
    cases l with
    | natVal k =>
      rw [natLitSupportedF_eq]
      by_cases hg : natLitSupported env
      · rw [if_pos hg, if_pos hg]
        refine SimC.bind_left (pureEq_eff hs natName)
          (fun s₁ ni hs₁ hQni => ?_)
        subst ni
        exact SimC.of_eff
          (pureC_eff hs₁ (x := Expr.const natName [])) _
          (fun r hQ => ⟨hQ, by simp [Expr.WScoped]⟩)
      · rw [if_neg hg, if_neg hg]
        exact SimC.throw
    | strVal str =>
      rw [strLitSupportedF_eq]
      by_cases hg : strLitSupported env
      · rw [if_pos hg, if_pos hg]
        refine SimC.bind_left (pureEq_eff hs stringName)
          (fun s₁ ni hs₁ hQni => ?_)
        subst ni
        exact SimC.of_eff
          (pureC_eff hs₁ (x := Expr.const stringName [])) _
          (fun r hQ => ⟨hQ, by simp [Expr.WScoped]⟩)
      · rw [if_neg hg, if_neg hg]
        exact SimC.throw
  | const nm us =>
    dsimp only
    unfold inferBodyI inferBodyIO
    dsimp only
    refine SimC.bind_pure_right ?_
    try dsimp only
    refine SimC.bind_left (pureEq_eff hs nm)
      (fun s₀' nw hs hnw => ?_)
    subst nw
    rw [mkFEnv_find?]
    cases hfn : env.find? nm with
    | none => exact SimC.throw
    | some ci =>
      dsimp only
      by_cases htw : (!ci.isTowerEntry) = true
      · rw [if_pos htw, if_pos htw]
        by_cases hlen : us.length = ci.toConstantVal.levelParams.length
        · rw [if_pos hlen, if_pos hlen]
          refine SimC.of_eff (constTyAtM_eff hs hfn) _ (fun r hQ => ?_)
          refine ⟨hQ, ?_⟩
          obtain ⟨htf, -⟩ := henv _ (find?_mem hfn)
          exact wscoped_instLevels_of_not_hasFvar htf _ _
        · rw [if_neg hlen, if_neg hlen]
          exact SimC.throw_bind
      · rw [if_neg htw, if_neg htw]
        exact SimC.throw_bind
  | forallE t b m =>
    dsimp only
    have hwtb : Expr.WScoped d t ∧ Expr.WScoped d b := by
      have hw' : Expr.WScoped d
        (Expr.forallE t b m) := hw
      simpa only [Expr.WScoped] using hw'
    unfold inferBodyIO
    dsimp only
    try dsimp only
    refine SimC.bind (ih.inferIO hs rfl hwtb.1)
      (fun s₁ tty ttyx hs₁ hP => ?_)
    obtain ⟨httyd, hwtty⟩ := hP
    refine SimC.bind (ih.whnf hs₁ httyd hwtty)
      (fun s₂ w wx hs₂ hP₂ => ?_)
    obtain ⟨rfl, hww⟩ := hP₂
    cases w with
    | sort u =>
      dsimp only
      refine SimC.bind_left
        (pureC_eff hs₂ (x := Expr.fvar d t))
        (fun s₃ fv hs₃ hQfv => ?_)
      subst hQfv
      refine SimC.bind_left (inst1M_eff hs₃ rfl rfl)
        (fun s₄ ob hs₄ hQob => ?_)
      have hwopen : Expr.WScoped (d + 1)
          (b.instantiate1 (Expr.fvar d t)) :=
        Expr.WScoped.instantiate1 hwtb.1 0 hwtb.2
      refine SimC.bind (ih.inferIO hs₄ hQob hwopen)
        (fun s₅ bt btx hs₅ hP₅ => ?_)
      obtain ⟨hbtd, hwbt⟩ := hP₅
      refine SimC.bind (ensureSortC_sim ih hs₅ hbtd hwbt)
        (fun s₆ v lv hs₆ hPv => ?_)
      obtain rfl := hPv
      by_cases hv : mode.verifiedChecks = true
      · simp only [hv, ↓reduceIte]
        by_cases hc : (Level.zeronessOf v == m.pw) = true
        · simp only [hc, ↓reduceIte]
          refine SimC.bind_left (pureEq_eff hs₆ (Level.imax u v))
            (fun s₇ iu hs₇ hQiu => ?_)
          subst hQiu
          exact SimC.of_eff
            (pureC_eff hs₇ (x := Expr.sort (Level.imax u v))) _
            (fun r hQ => ⟨hQ, by simp [Expr.WScoped]⟩)
        · simp only [hc, Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
      · simp only [hv, Bool.false_eq_true, ↓reduceIte]
        refine SimC.bind_left (pureEq_eff hs₆ (Level.imax u v))
          (fun s₇ iu hs₇ hQiu => ?_)
        subst hQiu
        exact SimC.of_eff
          (pureC_eff hs₇ (x := Expr.sort (Level.imax u v))) _
          (fun r hQ => ⟨hQ, by simp [Expr.WScoped]⟩)
    | bvar k' => exact SimC.throw
    | const nm' us' => exact SimC.throw
    | lit l' => exact SimC.throw
    | fvar idx' t' => exact SimC.throw
    | app f' a' => exact SimC.throw
    | lam t' b' m' => exact SimC.throw
    | forallE t' b' m' => exact SimC.throw
    | letE t' v' b' => exact SimC.throw
    | proj s' j' e' => exact SimC.throw
  | lam t b m =>
    dsimp only
    have hwtb : Expr.WScoped d t ∧ Expr.WScoped d b := by
      have hw' : Expr.WScoped d
        (Expr.lam t b m) := hw
      simpa only [Expr.WScoped] using hw'
    unfold inferBodyIO
    dsimp only
    try dsimp only
    -- task #168 stage 2: no domain-sort run at the io λ clause
    refine SimC.bind_left
      (pureC_eff hs (x := Expr.fvar d t))
      (fun s₃ fv hs₃ hQfv => ?_)
    subst hQfv
    refine SimC.bind_left (inst1M_eff hs₃ rfl rfl)
      (fun s₄ ob hs₄ hQob => ?_)
    have hwopen : Expr.WScoped (d + 1)
        (b.instantiate1 (Expr.fvar d t)) :=
      Expr.WScoped.instantiate1 hwtb.1 0 hwtb.2
    refine SimC.bind (ih.inferIO hs₄ hQob hwopen)
      (fun s₅ bt btx hs₅ hP₅ => ?_)
    obtain ⟨hbtd, hwbt⟩ := hP₅
    obtain rfl := hbtd
    have hres : ∀ {s₆ : CState}, CSOK mode env s₆ →
        SimC mode env s₆ (RelEC d)
          ((do
            let bAbs ← abstract1M bt d
            pure (Expr.forallE t bAbs m)) : CheckCM Expr)
          ((pure (Expr.forallE t (Expr.abstract1 bt d) m) :
            FueledM Expr)) := by
      intro s₆ hs₆
      refine SimC.bind_left (abstract1M_eff hs₆ rfl)
        (fun s₇ bAbs hs₇ hQ => ?_)
      subst hQ
      exact SimC.of_eff
        (pureC_eff hs₇
          (x := Expr.forallE t (Expr.abstract1 bt d) m)) _
        (fun r hQ => ⟨hQ, by
          simp only [Expr.WScoped]
          exact ⟨hwtb.1, ConLeche.WScoped.abstract1 0 hwbt⟩⟩)
    by_cases hv : mode.verifiedChecks = true
    · simp only [hv, ↓reduceIte]
      cases hbp : b.lamPw with
      | some pwI =>
        dsimp only
        by_cases hc : (m.pw == pwI) = true
        · simp only [hc, ↓reduceIte]
          exact hres hs₅
        · simp only [hc, Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
      | none =>
        dsimp only
        refine SimC.bind (ih.inferIO hs₅ rfl hwbt)
          (fun s₆ btt bttx hs₆ hP₆ => ?_)
        obtain ⟨hbttd, hwbtt⟩ := hP₆
        refine SimC.bind (ensureSortC_sim ih hs₆ hbttd hwbtt)
          (fun s₇ vb lvb hs₇ hPv => ?_)
        obtain rfl := hPv
        by_cases hc : (Level.zeronessOf vb == m.pw) = true
        · simp only [hc, ↓reduceIte]
          exact hres hs₇
        · simp only [hc, Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
    · simp only [hv, Bool.false_eq_true, ↓reduceIte]
      exact hres hs₅
  | app g' a =>
    dsimp only
    -- the gated spine; `inferSpineIO_sound_body` (at the gated mode)
    -- reproduces the loop's verdict in the chained io body over the
    -- io-grade view
    refine SimC.wr ?_
      (fun v F hF => inferSpineIO_sound_body hgb d g' a v F hF)
    refine SimC.pureB ?_
    refine SimC.pureB ?_
    have hhead : RelC (Expr.getAppFn (Expr.app g' a))
        ((Expr.app g' a).getAppFn) :=
      rfl
    have hargsSpec : RelCL (Expr.getAppArgsC (Expr.app g' a))
        ((Expr.app g' a).getAppArgs) :=
      Expr.getAppArgsC_spec (Expr.app g' a)
    refine SimC.bind (ih.inferIO hs hhead hw.getAppFn)
      (fun s₁ tf tfx hs₁ hP => ?_)
    refine inferSpineIOC_sim hμ ih henv hs₁ hP.1
      (by rw [toListRev_empty]; exact RelCL.nil) ?_
      hargsSpec hw.getAppArgs
    rw [Expr.instantiateList_nil]
    exact hP.2
  | proj sn ip pe =>
    dsimp only
    have hwpe : Expr.WScoped d pe := by
      have hw' : Expr.WScoped d (Expr.proj sn ip pe) := hw
      simpa only [Expr.WScoped] using hw'
    unfold inferBodyI inferBodyIO
    dsimp only
    try dsimp only
    refine SimC.bind (ih.inferIO hs rfl hwpe)
      (fun s₁ tpe tpex hs₁ hP => ?_)
    obtain ⟨htped, hwtpe⟩ := hP
    refine SimC.bind (ih.whnf hs₁ htped hwtpe)
      (fun s₂ te tex hs₂ hP₂ => ?_)
    obtain ⟨rfl, hwte⟩ := hP₂
    refine SimC.pureB ?_
    generalize hg : Expr.getAppFn te = g
    cases g with
    | const T us =>
      dsimp only
      refine SimC.bind_left (pureEq_eff hs₂ T)
        (fun s₂' Tw hs₂ hTw => ?_)
      subst Tw
      rw [mkFEnv_findProj?]
      cases hfp : env.findProj? T ip with
      | none => exact SimC.throw
      | some entry =>
        dsimp only
        refine SimC.pureB ?_
        have htargs : RelCL (Expr.getAppArgsC te) ((Expr.getAppArgs te)) :=
          Expr.getAppArgsC_spec te
        rw [htargs.length]
        split
        · -- task #175 S1: the body at the spine and the subject, as in
          -- `inferBodyC_sim`
          rename_i hcond
          rw [htargs]
          have hres : SimC mode env s₂' (RelEC d)
              (pure (entry.typeAtI us (Expr.getAppArgs te) pe))
              (pure (entry.typeAt us (Expr.getAppArgs te) pe) : FueledM Expr) :=
            SimC.pure hs₂ ⟨ProjEntry.typeAtI_eq entry us _ pe,
              projEntry_typeAt_WScoped henv hfp us
              hcond.2.1
              (fun a ha => hwte.getAppArgs a ha) hwpe⟩
          -- the Prop guard (task #175 W4c) runs no walk of its own
          split
          · split
            · exact hres
            · exact SimC.throw
          · exact hres
        · exact SimC.throw
    | bvar k' => exact SimC.throw
    | sort u' => exact SimC.throw
    | lit l' => exact SimC.throw
    | fvar idx' t' => exact SimC.throw
    | app f' a' => exact SimC.throw
    | lam t' b' m' => exact SimC.throw
    | forallE t' b' m' => exact SimC.throw
    | letE t' v' b' => exact SimC.throw
    | proj s' j' e' => exact SimC.throw


end Walks3

end ConLeche.Cached
