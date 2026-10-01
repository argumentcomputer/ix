module

import ConLeche.Cached.CoreC
public import ConLeche.Verify.Cached.GuardsC
public import ConLeche.Verify.Cached.SimCEff
import ConLeche.Verify.InstSpine

public section

/-!
# Cached body walks, part 1: list helpers and small twins (task #163)

Per-helper simulation walks: each cached twin
(`ConLeche/Cached/CoreC.lean`) is `SimC`-related to its `Expr` original
at the fueled record, on well-scoped inputs.  Ports of
`ConLeche/Verify/DiscI1.lean`'s walks under the recipe (DESIGN.md,
task #163): `SimAt → SimC`, denotation hypotheses → `RelC`/`RelCL`,
no `Ext`, node inversion by `cases` instead of
`denoteNode` unpacking.  The pure comparand side of every statement is
byte-identical to the interned original's.
-/

namespace ConLeche.Cached

open ConLeche.Expr

variable {mode : CheckMode}

/-- The cached conditional simulation at fuel `f` (the `SSimI` mirror):
every cached entry point simulates the corresponding fueled family on
well-scoped inputs.  Declared here so the per-body walks can
take it as their induction hypothesis; the knot batch proves it at
every fuel. -/
structure SSimC (mode : CheckMode) (env : Env) (f : Nat) : Prop where
  whnfCore : ∀ {s₀ : CState} {d : Nat} {i : Expr} {e : Expr},
    CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode env s₀ (RelEC d)
      ((coreKnotI mode (mkFEnv env) f).whnfCore d i)
      ((fueledFns mode env).whnfCore d e)
  whnf : ∀ {s₀ : CState} {d : Nat} {i : Expr} {e : Expr},
    CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode env s₀ (RelEC d)
      ((coreKnotI mode (mkFEnv env) f).whnf d i)
      ((fueledFns mode env).whnf d e)
  infer : ∀ {s₀ : CState} {d : Nat} {i : Expr} {e : Expr},
    CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode env s₀ (RelEC d)
      ((coreKnotI mode (mkFEnv env) f).infer d i)
      ((fueledFns mode env).infer d e)
  defeq : ∀ {s₀ : CState} {d : Nat} {i j : Expr} {a b : Expr},
    CSOK mode env s₀ → RelC i a → RelC j b →
    Expr.WScoped d a → Expr.WScoped d b →
    SimC mode env s₀ RelVC
      ((coreKnotI mode (mkFEnv env) f).defeq d i j)
      ((fueledFns mode env).defeq d a b)
  annotate : ∀ {s₀ : CState} {d : Nat} {i : Expr} {e : Expr},
    CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode env s₀ (RelEC d)
      ((coreKnotI mode (mkFEnv env) f).annotate d i)
      ((fueledFns mode env).annotate d e)
  /-- the io slot (task #172 B4): the memoized knot's `inferIO` entry
  simulates the fueled io-slot family -/
  inferIO : ∀ {s₀ : CState} {d : Nat} {i : Expr} {e : Expr},
    CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode env s₀ (RelEC d)
      ((coreKnotI mode (mkFEnv env) f).inferIO d i)
      ((fueledFns mode env).inferIO d e)

/-- The base case: fuel `0` throws everywhere. -/
theorem ssimC_zero (env : Env) : SSimC mode env 0 :=
  { whnfCore := fun _ _ _ => SimC.throw
    whnf := fun _ _ _ => SimC.throw
    infer := fun _ _ _ => SimC.throw
    defeq := fun _ _ _ _ _ => SimC.throw
    annotate := fun _ _ _ => SimC.throw
    inferIO := fun _ _ _ => SimC.throw }

section Walks

variable {env : Env} {f : Nat}

/-- Port of `defEqListI_sim`: the pairwise definitional-equality
helper simulates its fueled original on related, well-scoped lists. -/
theorem defEqListC_sim (ih : SSimC mode env f) {d : Nat} :
    ∀ {args : List Expr} {xs : List Expr} {brgs : List Expr}
      {ys : List Expr} {s₀ : CState}, CSOK mode env s₀ →
      RelCL args xs → RelCL brgs ys →
      (∀ x ∈ xs, Expr.WScoped d x) → (∀ y ∈ ys, Expr.WScoped d y) →
      SimC mode env s₀ RelVC
        (defEqListI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d args brgs)
        (defEqList (fueledFns mode env) env d xs ys) := by
  intro args
  induction args with
  | nil =>
    intro xs brgs ys s₀ hs hargs hbrgs _ _
    obtain rfl := hargs.nil_inv
    match brgs, ys, hbrgs.length with
    | [], [], _ => exact SimC.pure hs rfl
    | b :: bs, y :: ys, _ => exact SimC.pure hs rfl
  | cons a as iha =>
    intro xs brgs ys s₀ hs hargs hbrgs hwx hwy
    obtain ⟨x, xs, rfl, hax, hasxs⟩ := hargs.cons_inv
    match brgs, ys, hbrgs.length with
    | [], [], _ => exact SimC.pure hs rfl
    | b :: bs, ys', hlen =>
      obtain ⟨y, ys, rfl, hby, hbsys⟩ := hbrgs.cons_inv
      show SimC mode env s₀ RelVC
        ((coreKnotI mode (mkFEnv env) f).defeq d a b >>= fun r =>
          if r then defEqListI (coreKnotI mode (mkFEnv env) f)
            (mkFEnv env) d as bs
          else pure false)
        ((fueledFns mode env).defeq d x y >>= fun r =>
          if r then defEqList (fueledFns mode env) env d xs ys
          else pure false)
      refine SimC.bind (ih.defeq hs hax hby
        (hwx x (List.mem_cons_self ..)) (hwy y (List.mem_cons_self ..)))
        (fun s₁ rb r hs₁ hP => ?_)
      obtain rfl : rb = r := hP
      cases rb with
      | true =>
        simp only [↓reduceIte]
        exact iha hs₁ hasxs hbsys
          (fun x hx => hwx x (List.mem_cons_of_mem _ hx))
          (fun y hy => hwy y (List.mem_cons_of_mem _ hy))
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact SimC.pure hs₁ rfl

/-- Port of `iotaCertsIAux_sim`: the bulk-accumulating iota-certificate
loop simulates its fueled original. -/
theorem iotaCertsCAux_sim (ih : SSimC mode env f) {d : Nat} {lic : Bool} :
    ∀ {args : List Expr} {xs : List Expr} {acc : List Expr}
      {ws : List Expr} {ty : Expr} {tyx : Expr} {s₀ : CState},
      CSOK mode env s₀ →
      RelC ty tyx → RelCL acc ws →
      Expr.WScoped d (tyx.instantiateList ws) →
      RelCL args xs → (∀ x ∈ xs, Expr.WScoped d x) →
      SimC mode env s₀ RelVC
        (iotaCertsIAux (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d lic ty acc
          args)
        (iotaCerts (fueledFns mode env) env d lic (tyx.instantiateList ws) xs)
  | [], xs, acc, ws, ty, tyx, s₀, hs, hty, hacc, hwty, hargs, hwargs => by
    obtain rfl := hargs.nil_inv
    rw [iotaCertsIAux.eq_def]
    dsimp only
    exact SimC.pure hs rfl
  | a :: as, xs, acc, ws, ty, tyx, s₀, hs, hty, hacc, hwty, hargs, hwargs => by
    obtain ⟨x, xs, rfl, hax, hasxs⟩ := hargs.cons_inv
    rw [iotaCertsIAux.eq_def]
    obtain rfl := hty
    cases ty with
    | forallE t b m =>
      rw [show (Expr.instantiateList (Expr.forallE t b m) ws)
          = .forallE ((Expr.instantiateList t ws))
              ((Expr.instantiateList b ws 1)) m by
        simp [Expr.instantiateList]] at hwty ⊢
      have hwtb : Expr.WScoped d ((Expr.instantiateList t ws))
          ∧ Expr.WScoped d ((Expr.instantiateList b ws 1)) := by
        simpa only [Expr.WScoped] using hwty
      show SimC mode env s₀ RelVC
        (if lic && m.pw.isNever then
          iotaCertsIAux (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d lic b
            (a :: acc) as
        else
          instListM t acc >>= fun dom' =>
          (coreKnotI mode (mkFEnv env) f).inferIO d a >>= fun ta =>
          (coreKnotI mode (mkFEnv env) f).defeq d ta dom' >>= fun r =>
          if r then iotaCertsIAux (coreKnotI mode (mkFEnv env) f)
            (mkFEnv env) d lic b (a :: acc) as
          else pure false)
        (if lic && m.pw.isNever then
          iotaCerts (fueledFns mode env) env d lic
            (((Expr.instantiateList b ws 1)).instantiate1 x) xs
        else
          (fueledFns mode env).inferIO d x >>= fun ta =>
          (fueledFns mode env).defeq d ta ((Expr.instantiateList t ws)) >>=
            fun r =>
          if r then iotaCerts (fueledFns mode env) env d lic
            (((Expr.instantiateList b ws 1)).instantiate1 x) xs
          else pure false)
      have hwx : Expr.WScoped d x := hwargs x (List.mem_cons_self ..)
      -- the licensed slot: no run on either side
      have htail : SimC mode env s₀ RelVC
          (iotaCertsIAux (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d lic b
            (a :: acc) as)
          (iotaCerts (fueledFns mode env) env d lic
            (((Expr.instantiateList b ws 1)).instantiate1 x) xs) := by
        rw [← Expr.instantiateList_cons]
        refine iotaCertsCAux_sim ih hs rfl (RelCL.cons hax hacc) ?_
          hasxs (fun x' hx' => hwargs x' (List.mem_cons_of_mem _ hx'))
        rw [Expr.instantiateList_cons]
        exact Expr.WScoped.instantiate1_gen hwx 0 hwtb.2
      by_cases hg : (lic && m.pw.isNever) = true
      · rw [if_pos hg, if_pos hg]
        exact htail
      rw [if_neg hg, if_neg hg]
      refine SimC.bind_left (instListM_eff (d := 0) hs rfl hacc)
        (fun s₁ dom' hs₁ hQdom => ?_)
      refine SimC.bind (ih.inferIO hs₁ hax hwx) (fun s₂ ta tax hs₂ hP => ?_)
      obtain ⟨htax, hwtax⟩ := hP
      refine SimC.bind (ih.defeq hs₂ htax hQdom hwtax hwtb.1)
        (fun s₃ rb r hs₃ hP₂ => ?_)
      obtain rfl : rb = r := hP₂
      cases rb with
      | true =>
        simp only [↓reduceIte]
        rw [← Expr.instantiateList_cons]
        refine iotaCertsCAux_sim ih hs₃ rfl (RelCL.cons hax hacc) ?_
          hasxs (fun x' hx' => hwargs x' (List.mem_cons_of_mem _ hx'))
        rw [Expr.instantiateList_cons]
        exact Expr.WScoped.instantiate1_gen hwx 0 hwtb.2
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact SimC.pure hs₃ rfl
    | bvar k =>
      match acc with
      | [] =>
        obtain rfl := hacc.nil_inv
        rw [Expr.instantiateList_nil]
        exact SimC.pure hs rfl
      | a' :: acc' =>
        obtain ⟨w, ws', rfl, ha'w, hacc'⟩ := hacc.cons_inv
        show SimC mode env s₀ RelVC
          (instListM (Expr.bvar k) (a' :: acc') >>= fun ty' =>
            iotaCertsIAux (coreKnotI mode (mkFEnv env) f) (mkFEnv env)
              d lic ty' [] (a :: as))
          (iotaCerts (fueledFns mode env) env d lic
            ((Expr.instantiateList (Expr.bvar k) (w :: ws')))
            (x :: xs))
        refine SimC.bind_left (instListM_eff (d := 0) hs rfl hacc)
          (fun s₁ ty' hs₁ hQty => ?_)
        have := iotaCertsCAux_sim ih (lic := lic) (acc := []) (ws := [])
          (args := a :: as) (xs := x :: xs) hs₁ hQty RelCL.nil
          (by rw [Expr.instantiateList_nil]; exact hwty)
          (RelCL.cons hax hasxs) hwargs
        rwa [Expr.instantiateList_nil] at this
    | sort u =>
      rw [show (Expr.instantiateList (Expr.sort u) ws)
          = .sort u by simp [Expr.instantiateList]]
      exact SimC.pure hs rfl
    | const nm us =>
      rw [show (Expr.instantiateList (Expr.const nm us) ws)
          = .const nm us by simp [Expr.instantiateList]]
      exact SimC.pure hs rfl
    | lit l =>
      rw [show (Expr.instantiateList (Expr.lit l) ws)
          = .lit l by simp [Expr.instantiateList]]
      exact SimC.pure hs rfl
    | fvar idx t =>
      rw [show (Expr.instantiateList (Expr.fvar idx t) ws)
          = .fvar idx t by simp [Expr.instantiateList]]
      exact SimC.pure hs rfl
    | app f' a' =>
      rw [show (Expr.instantiateList (Expr.app f' a') ws)
          = .app ((Expr.instantiateList f' ws))
              ((Expr.instantiateList a' ws)) by
        simp [Expr.instantiateList]]
      exact SimC.pure hs rfl
    | lam t b m =>
      rw [show (Expr.instantiateList (Expr.lam t b m) ws)
          = .lam ((Expr.instantiateList t ws))
              ((Expr.instantiateList b ws 1)) m by
        simp [Expr.instantiateList]]
      exact SimC.pure hs rfl
    | letE t v b =>
      rw [show (Expr.instantiateList (Expr.letE t v b) ws)
          = .letE ((Expr.instantiateList t ws))
              ((Expr.instantiateList v ws))
              ((Expr.instantiateList b ws 1)) by
        simp [Expr.instantiateList]]
      exact SimC.pure hs rfl
    | proj sn j e' =>
      rw [show (Expr.instantiateList (Expr.proj sn j e') ws)
          = .proj sn j ((Expr.instantiateList e' ws)) by
        simp [Expr.instantiateList]]
      exact SimC.pure hs rfl
termination_by args _ acc => (args.length, acc.length)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

/-- Port of `iotaCertsI_sim`. -/
theorem iotaCertsC_sim (ih : SSimC mode env f) {d : Nat} {lic : Bool} :
    ∀ {args : List Expr} {xs : List Expr} {ty : Expr} {tyx : Expr}
      {s₀ : CState}, CSOK mode env s₀ →
      RelC ty tyx → Expr.WScoped d tyx →
      RelCL args xs → (∀ x ∈ xs, Expr.WScoped d x) →
      SimC mode env s₀ RelVC
        (iotaCertsI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d lic ty args)
        (iotaCerts (fueledFns mode env) env d lic tyx xs) := by
  intro args xs ty tyx s₀ hs hty hwty hargs hwargs
  have := iotaCertsCAux_sim ih (lic := lic) (acc := []) (ws := []) hs hty RelCL.nil
    (by rw [Expr.instantiateList_nil]; exact hwty) hargs hwargs
  rw [Expr.instantiateList_nil] at this
  exact this

end Walks

section Walks2

variable {env : Env} {f : Nat}

/-- Port of `ensureSortI_sim`. -/
theorem ensureSortC_sim (ih : SSimC mode env f) {d : Nat} {i : Expr}
    {e : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i e) (hw : Expr.WScoped d e) :
    SimC mode env s₀ RelVC (ensureSortI (coreKnotI mode (mkFEnv env) f) d i)
      (ensureSort (fueledFns mode env) env d e) := by
  show SimC mode env s₀ RelVC
    ((coreKnotI mode (mkFEnv env) f).whnf d i >>= fun w =>
      
      match w with
      | .sort u => pure u
      | _ => throw (.invalid "expected a sort"))
    ((fueledFns mode env).whnf d e >>= fun w =>
      match w with
      | .sort u => pure u
      | _ => throw (.invalid "expected a sort"))
  refine SimC.bind (ih.whnf hs hden hw) (fun s₁ w wx hs₁ hP => ?_)
  obtain ⟨hwden, hww⟩ := hP
  obtain rfl := hwden
  cases w with
  | sort u => exact SimC.pure hs₁ rfl
  | bvar k => exact SimC.throw
  | const nm us => exact SimC.throw
  | lit l => exact SimC.throw
  | fvar idx t => exact SimC.throw
  | app f' a' => exact SimC.throw
  | lam t b m => exact SimC.throw
  | forallE t b m => exact SimC.throw
  | letE t v b => exact SimC.throw
  | proj sn j e' => exact SimC.throw

/-- Port of `litToCtorIfNatI_eff`: the cached twin computes the spec's
`litToCtorIfNat`. -/
theorem litToCtorIfNatC_eff {s₀ : CState} (hs : CSOK mode env s₀)
    {i : Expr} {e : Expr} (hden : RelC i e) :
    CEff mode env s₀ (fun r => RelC r (litToCtorIfNat env e))
      (litToCtorIfNatI (mkFEnv env) i) := by
  show CEff mode env s₀ _ (
    match i with
    | .lit (.natVal n) =>
      if natLitSupportedF (mkFEnv env) then
        pure (natLitToConstructor n)
      else pure i
    | _ => pure i)
  obtain rfl := hden
  have hden : RelC i i := rfl
  cases i with
  | lit l =>
    cases l with
    | natVal k =>
      dsimp only
      rw [natLitSupportedF_eq]
      rw [show litToCtorIfNat env ((Expr.lit (.natVal k))) =
        (if natLitSupported env then natLitToConstructor k
         else .lit (.natVal k)) from rfl]
      by_cases hg : natLitSupported env
      · rw [if_pos hg, if_pos hg]
        exact pureC_eff hs _
      · rw [if_neg hg, if_neg hg]
        exact CEff.pure hs hden
    | strVal str => exact CEff.pure hs hden
  | bvar k =>
    exact CEff.pure hs hden
  | sort u =>
    exact CEff.pure hs hden
  | const nm us =>
    exact CEff.pure hs hden
  | fvar idx t =>
    exact CEff.pure hs hden
  | app f' a' =>
    exact CEff.pure hs hden
  | lam t b m =>
    exact CEff.pure hs hden
  | forallE t b m =>
    exact CEff.pure hs hden
  | letE t v b =>
    exact CEff.pure hs hden
  | proj sn j e' =>
    exact CEff.pure hs hden

/-- Port of `unfoldDefinitionI_eff`: the cached twin computes the
spec's pure `unfoldDefinition`. -/
theorem unfoldDefinitionC_eff {s₀ : CState} (hs : CSOK mode env s₀)
    {i : Expr} {e : Expr} (hden : RelC i e) :
    CEff mode env s₀ (fun o => OptEr o (unfoldDefinition env e))
      (unfoldDefinitionI (mkFEnv env) i) := by
  show CEff mode env s₀ _
    (
      match (Expr.getAppFn i) with
      | .const n us => do
        let nm ← pure n
        match (mkFEnv env).find? nm with
        | some (.defnInfo cv _ _) =>
          if us.length = cv.levelParams.length then do
            let v ← constValAtM (mkFEnv env) n nm us
            let args ← pure (Expr.getAppArgsC i)
            let r ← mkAppNM v args
            pure (some r)
          else pure none
        | _ => pure none
      | _ => pure none)
  refine CEff.pureB ?_
  obtain rfl := hden
  have hspec : unfoldDefinition env i =
      (match (Expr.getAppFn i) with
      | .const n us =>
        match env.find? n with
        | some (.defnInfo cv value _) =>
          if us.length = cv.levelParams.length then
            some (Expr.mkAppN (value.instantiateLevelParams cv.levelParams us)
              (Expr.getAppArgs i))
          else none
        | _ => none
      | _ => none) := rfl
  generalize hg : Expr.getAppFn i = g
  cases g with
  | const nm us =>
    have hfn' : (Expr.getAppFn i) = Expr.const nm us := hg
    rw [hspec, hfn']
    dsimp only
    refine (pureEq_eff hs nm).bind ?_
    intro s₀' nmv hs hnmv
    subst hnmv
    rw [mkFEnv_find?]
    cases hfc : env.find? nmv with
    | none => exact CEff.pure hs trivial
    | some ci =>
      cases ci with
      | defnInfo cv value hint =>
        dsimp only
        by_cases hlen : us.length = cv.levelParams.length
        · rw [if_pos hlen, if_pos hlen]
          refine CEff.bind (constValAtM_eff hs hfc) ?_
          intro s₁ v hs₁ hQv
          refine CEff.pureB ?_
          refine CEff.bind (mkAppNM_eff hs₁ hQv (Expr.getAppArgsC_spec _)) ?_
          intro s₂ r hs₂ hQr
          exact CEff.pure hs₂ hQr
        · rw [if_neg hlen, if_neg hlen]
          exact CEff.pure hs trivial
      | axiomInfo cv => exact CEff.pure hs trivial
      | thmInfo cv value => exact CEff.pure hs trivial
      | indInfo cv caps => exact CEff.pure hs trivial
      | ctorInfo cv nP nF => exact CEff.pure hs trivial
      | recInfo cv mI rP rules => exact CEff.pure hs trivial
      | projInfo entry => exact CEff.pure hs trivial
  | bvar k =>
    have hfn' : (Expr.getAppFn i) = Expr.bvar k := hg
    rw [hspec, hfn']
    exact CEff.pure hs trivial
  | sort u =>
    have hfn' : (Expr.getAppFn i) = Expr.sort u := hg
    rw [hspec, hfn']
    exact CEff.pure hs trivial
  | lit l =>
    have hfn' : (Expr.getAppFn i) = Expr.lit l := hg
    rw [hspec, hfn']
    exact CEff.pure hs trivial
  | fvar idx t =>
    have hfn' : (Expr.getAppFn i) = Expr.fvar idx t := hg
    rw [hspec, hfn']
    exact CEff.pure hs trivial
  | app f' a' =>
    have hfn' : (Expr.getAppFn i) = Expr.app f' a' :=
      hg
    rw [hspec, hfn']
    exact CEff.pure hs trivial
  | lam t b m =>
    have hfn' : (Expr.getAppFn i) = Expr.lam t b m :=
      hg
    rw [hspec, hfn']
    exact CEff.pure hs trivial
  | forallE t b m =>
    have hfn' : (Expr.getAppFn i)
        = Expr.forallE t b m := hg
    rw [hspec, hfn']
    exact CEff.pure hs trivial
  | letE t v b =>
    have hfn' : (Expr.getAppFn i)
        = Expr.letE t v b := hg
    rw [hspec, hfn']
    exact CEff.pure hs trivial
  | proj sn j e' =>
    have hfn' : (Expr.getAppFn i) = Expr.proj sn j e' := hg
    rw [hspec, hfn']
    exact CEff.pure hs trivial

end Walks2

section Walks3

variable {env : Env} {f : Nat}

/-- A twin-only effect against a pure fueled value. -/
theorem SimC.of_eff {s₀ : CState} {β α : Type} {Q : β → Prop}
    {P : β → α → Prop} {c : CheckCM β}
    (h : CEff mode env s₀ Q c) (a : α) (hPa : ∀ b, Q b → P b a) :
    SimC mode env s₀ P c (pure a) := by
  intro v' s' hr
  obtain ⟨hs', hQ⟩ := h v' s' hr
  exact ⟨hs', a, hPa v' hQ, 0, rfl⟩

/-- Port of `litMajorToCtorI_sim`. -/
theorem litMajorToCtorC_sim (ih : SSimC mode env f) {d : Nat} {i : Expr}
    {e : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i e) (hw : Expr.WScoped d e) :
    SimC mode env s₀ (RelEC d)
      (litMajorToCtorI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (litMajorToCtor (fueledFns mode env) env d e) := by
  unfold litMajorToCtorI
  obtain rfl := hden
  have hden : RelC i i := rfl
  cases i with
  | lit l =>
    cases l with
    | strVal str =>
      dsimp only
      rw [show litMajorToCtor (fueledFns mode env) env d
          ((Expr.lit (.strVal str))) =
        (if strLitSupported env then
          (fueledFns mode env).whnf d (strLitToConstructor str)
         else pure (.lit (.strVal str))) from rfl]
      rw [strLitSupportedF_eq]
      by_cases hg : strLitSupported env
      · rw [if_pos hg, if_pos hg]
        refine SimC.bind_left (pureC_eff hs (strLitToConstructor str))
          (fun s₁ x hs₁ hQ => ?_)
        exact ih.whnf hs₁ hQ (strLitToConstructor_WScoped str d)
      · rw [if_neg hg, if_neg hg]
        exact SimC.pure hs ⟨hden, hw⟩
    | natVal k =>
      refine SimC.of_eff (litToCtorIfNatC_eff hs hden) _ ?_
      intro b hQ
      exact ⟨hQ, litToCtorIfNat_WScoped hw⟩
  | bvar k =>
    exact SimC.of_eff (litToCtorIfNatC_eff hs hden) _
      (fun b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | sort u =>
    exact SimC.of_eff (litToCtorIfNatC_eff hs hden) _
      (fun b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | const nm us =>
    exact SimC.of_eff (litToCtorIfNatC_eff hs hden) _
      (fun b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | fvar idx t =>
    exact SimC.of_eff (litToCtorIfNatC_eff hs hden) _
      (fun b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | app f' a' =>
    exact SimC.of_eff (litToCtorIfNatC_eff hs hden) _
      (fun b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | lam t b m =>
    exact SimC.of_eff (litToCtorIfNatC_eff hs hden) _
      (fun b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | forallE t b m =>
    exact SimC.of_eff (litToCtorIfNatC_eff hs hden) _
      (fun b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | letE t v b =>
    exact SimC.of_eff (litToCtorIfNatC_eff hs hden) _
      (fun b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | proj sn jj e' =>
    exact SimC.of_eff (litToCtorIfNatC_eff hs hden) _
      (fun b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)

/-- Port of `projLitToCtorI_sim`. -/
theorem projLitToCtorC_sim (ih : SSimC mode env f) {d : Nat} {i : Expr}
    {e : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i e) (hw : Expr.WScoped d e) :
    SimC mode env s₀ (RelEC d)
      (projLitToCtorI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (projLitToCtor (fueledFns mode env) env d e) := by
  unfold projLitToCtorI
  obtain rfl := hden
  have hden : RelC i i := rfl
  cases i with
  | lit l =>
    cases l with
    | strVal str =>
      dsimp only
      rw [show projLitToCtor (fueledFns mode env) env d
          ((Expr.lit (.strVal str))) =
        (if strLitSupported env then
          (fueledFns mode env).whnf d (strLitToConstructor str)
         else pure (.lit (.strVal str))) from rfl]
      rw [strLitSupportedF_eq]
      by_cases hg : strLitSupported env
      · rw [if_pos hg, if_pos hg]
        refine SimC.bind_left (pureC_eff hs (strLitToConstructor str))
          (fun s₁ x hs₁ hQ => ?_)
        exact ih.whnf hs₁ hQ (strLitToConstructor_WScoped str d)
      · rw [if_neg hg, if_neg hg]
        exact SimC.pure hs ⟨hden, hw⟩
    | natVal k => exact SimC.pure hs ⟨hden, hw⟩
  | bvar k => exact SimC.pure hs ⟨hden, hw⟩
  | sort u => exact SimC.pure hs ⟨hden, hw⟩
  | const nm us => exact SimC.pure hs ⟨hden, hw⟩
  | fvar idx t => exact SimC.pure hs ⟨hden, hw⟩
  | app f' a' => exact SimC.pure hs ⟨hden, hw⟩
  | lam t b m => exact SimC.pure hs ⟨hden, hw⟩
  | forallE t b m => exact SimC.pure hs ⟨hden, hw⟩
  | letE t v b => exact SimC.pure hs ⟨hden, hw⟩
  | proj sn jj e' => exact SimC.pure hs ⟨hden, hw⟩

/-- Port of `defeqSpineI_sim`. -/
theorem defeqSpineC_sim (ih : SSimC mode env f) {d : Nat} {i j : Expr}
    {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (defeqSpineI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (defeqSpine (fueledFns mode env) env d a b) := by
  show SimC mode env s₀ RelVC
    (
      match (Expr.getAppFn i) with
      | .const nm us =>
        
        match (Expr.getAppFn j) with
        | .const nm' us' => do
          let aargs ← pure (Expr.getAppArgsC i)
          let bargs ← pure (Expr.getAppArgsC j)
          if nm = nm' ∧ aargs.length = bargs.length then do
            match ← isEquivListLM us us' with
            | some true =>
              defEqListI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d
                aargs bargs
            | _ => pure false
          else pure false
        | _ => pure false
      | _ => pure false)
    (defeqSpine (fueledFns mode env) env d a b)
  refine SimC.pureB ?_
  obtain rfl := hdena
  obtain rfl := hdenb
  have hspec : defeqSpine (fueledFns mode env) env d i j =
      (match (Expr.getAppFn i) with
      | .const nm us =>
        match (Expr.getAppFn j) with
        | .const nm' us' =>
          if nm = nm' ∧
              (Expr.getAppArgs i).length = (Expr.getAppArgs j).length then
            match Level.isEquivList us us' with
            | some true =>
              defEqList (fueledFns mode env) env d
                (Expr.getAppArgs i) (Expr.getAppArgs j)
            | _ => pure false
          else pure false
        | _ => pure false
      | _ => pure false) := rfl
  have haargs := Expr.getAppArgsC_spec i
  have hbargs := Expr.getAppArgsC_spec j
  have hlena : (Expr.getAppArgsC i).length = (Expr.getAppArgs i).length :=
    RelCL.length haargs
  have hlenb : (Expr.getAppArgsC j).length = (Expr.getAppArgs j).length :=
    RelCL.length hbargs
  generalize hga : Expr.getAppFn i = ga
  cases ga with
  | const nm us =>
    have hfa' : (Expr.getAppFn i) = Expr.const nm us := hga
    rw [hspec, hfa']
    dsimp only
    refine SimC.pureB ?_
    generalize hgb : Expr.getAppFn j = gb
    cases gb with
    | const nm' us' =>
      dsimp only
      refine SimC.pureB ?_
      refine SimC.pureB ?_
      simp only [hlena, hlenb]
      by_cases hcnd : nm = nm' ∧
          (Expr.getAppArgs i).length = (Expr.getAppArgs j).length
      · rw [if_pos hcnd, if_pos hcnd]
        refine SimC.bind_left (isEquivListLM_eff hs) ?_
        intro s₁ ob hs₁ hob
        subst hob
        cases hlv : Level.isEquivList us us' with
        | some tv =>
          cases tv with
          | true =>
            exact defEqListC_sim ih hs₁ haargs hbargs
              hwa.getAppArgs hwb.getAppArgs
          | false => exact SimC.pure hs₁ rfl
        | none => exact SimC.pure hs₁ rfl
      · rw [if_neg hcnd, if_neg hcnd]
        exact SimC.pure hs rfl
    | bvar k =>
      exact SimC.pure hs rfl
    | sort u' =>
      exact SimC.pure hs rfl
    | lit l' =>
      exact SimC.pure hs rfl
    | fvar idx' t' =>
      exact SimC.pure hs rfl
    | app f₂ a₂ =>
      exact SimC.pure hs rfl
    | lam t' b' m' =>
      exact SimC.pure hs rfl
    | forallE t' b' m' =>
      exact SimC.pure hs rfl
    | letE t' v' b' =>
      exact SimC.pure hs rfl
    | proj sn' j' e' =>
      exact SimC.pure hs rfl
  | bvar k =>
    rw [hspec, show (Expr.getAppFn i) = Expr.bvar k from hga]
    exact SimC.pure hs rfl
  | sort u =>
    rw [hspec, show (Expr.getAppFn i) = Expr.sort u from hga]
    exact SimC.pure hs rfl
  | lit l =>
    rw [hspec, show (Expr.getAppFn i) = Expr.lit l from hga]
    exact SimC.pure hs rfl
  | fvar idx t =>
    rw [hspec, show (Expr.getAppFn i) = Expr.fvar idx t
      from hga]
    exact SimC.pure hs rfl
  | app f' a' =>
    rw [hspec, show (Expr.getAppFn i) = Expr.app f' a'
      from hga]
    exact SimC.pure hs rfl
  | lam t b' m =>
    rw [hspec, show (Expr.getAppFn i)
      = Expr.lam t b' m from hga]
    exact SimC.pure hs rfl
  | forallE t b' m =>
    rw [hspec, show (Expr.getAppFn i)
      = Expr.forallE t b' m from hga]
    exact SimC.pure hs rfl
  | letE t v b' =>
    rw [hspec, show (Expr.getAppFn i)
      = Expr.letE t v b' from hga]
    exact SimC.pure hs rfl
  | proj sn j' e' =>
    rw [hspec, show (Expr.getAppFn i) = Expr.proj sn j' e'
      from hga]
    exact SimC.pure hs rfl

end Walks3

section Walks4

variable {env : Env} {f : Nat}

private theorem relOC_some_lit {r : Expr} {n : Nat} {d : Nat}
    (h : RelC r (.lit (.natVal n))) :
    RelOC d (some r) (some (.lit (.natVal n))) :=
  ⟨h, by simp [Expr.WScoped]⟩

/-- Port of `reduceNatI_sim`. -/
theorem reduceNatC_sim (ih : SSimC mode env f) {d : Nat} {i : Expr}
    {e : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i e) (hw : Expr.WScoped d e) :
    SimC mode env s₀ (RelOC d)
      (reduceNatI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (reduceNat (fueledFns mode env) env d e) := by
  unfold reduceNatI
  obtain rfl := hden
  cases i with
  | app f₁ b =>
    rw [show (Expr.app f₁ b)
        = Expr.app (f₁) b from rfl] at hw ⊢
    have hwfb : Expr.WScoped d (f₁) ∧ Expr.WScoped d b := by
      simpa only [Expr.WScoped] using hw
    cases f₁ with
    | const c us =>
      rw [show (Expr.const c us)
          = Expr.const c us from rfl]
      cases us with
      | cons u us' => exact SimC.pure hs trivial
      | nil =>
        refine SimC.bind_left (pureEq_eff hs c)
          (fun s₀' cv hs hcv => ?_)
        subst hcv
        rw [show reduceNat (fueledFns mode env) env d
          (.app (.const cv []) b) =
          (if cv = natSuccName ∧ natLitSupported env then
            (fueledFns mode env).whnf d b >>= fun w =>
            match rawNatLit? w with
            | some n => pure (some (.lit (.natVal (n + 1))))
            | none => pure none
          else pure none) from rfl]
        rw [natLitSupportedF_eq]
        by_cases hg1 : cv = natSuccName ∧ natLitSupported env
        · rw [if_pos hg1, if_pos hg1]
          refine SimC.bind (ih.whnf hs rfl hwfb.2)
            (fun s₁ w wx hs₁ hP => ?_)
          obtain ⟨hwden, hww⟩ := hP
          refine SimC.pureB ?_
          rw [rawNatLitC?_spec' hwden]
          cases rawNatLit? wx with
          | some k =>
            refine SimC.bind_left (pureC_eff hs₁ _)
              (fun s₂ r hs₂ hQ => ?_)
            exact SimC.pure hs₂ (relOC_some_lit hQ)
          | none => exact SimC.pure hs₁ trivial
        · rw [if_neg hg1, if_neg hg1]
          exact SimC.pure hs trivial
    | app f₂ a =>
      rw [show (Expr.app f₂ a)
          = Expr.app (f₂) a from rfl] at hwfb ⊢
      have hwf₂a : Expr.WScoped d (f₂) ∧ Expr.WScoped d a := by
        simpa only [Expr.WScoped] using hwfb.1
      cases f₂ with
      | const c us =>
        rw [show (Expr.const c us)
            = Expr.const c us from rfl]
        cases us with
        | cons u us' => exact SimC.pure hs trivial
        | nil =>
          refine SimC.bind_left (pureEq_eff hs c)
            (fun s₀' cv hs hcv => ?_)
          subst hcv
          rw [show reduceNat (fueledFns mode env) env d
            (.app (.app (.const cv []) a) b) =
            (if (cv = natAddName ∨ cv = natSubName ∨ cv = natMulName ∨
                cv = natPowName ∨ cv = natBeqName ∨ cv = natBleName ∨
                cv = natDivName ∨ cv = natModName ∨ cv = natGcdName ∨
                cv = natLandName ∨ cv = natLorName ∨ cv = natXorName ∨
                cv = natShiftLeftName ∨ cv = natShiftRightName) ∧
                natOpStored env cv = true then
              (fueledFns mode env).whnf d a >>= fun w₁ =>
              match rawNatLit? w₁ with
              | some n₁ =>
                (fueledFns mode env).whnf d b >>= fun w₂ =>
                match rawNatLit? w₂ with
                | some n₂ => pure (natOpResult cv n₁ n₂)
                | none => pure none
              | none => pure none
            else if natOpWfNames.contains cv ∧ natLitSupported env then
              (fueledFns mode env).whnf d a >>= fun w₁ =>
              match rawNatLit? w₁ with
              | some _ =>
                (fueledFns mode env).whnf d b >>= fun w₂ =>
                match rawNatLit? w₂ with
                | some _ => throw (.notImplemented
                    s!"native Nat computation on literals ({cv})")
                | none => pure none
              | none => pure none
            else pure none) from rfl]
          rw [natOpStoredF_eq, natLitSupportedF_eq]
          by_cases hg1 : (cv = natAddName ∨ cv = natSubName ∨
              cv = natMulName ∨ cv = natPowName ∨ cv = natBeqName ∨
              cv = natBleName ∨ cv = natDivName ∨ cv = natModName ∨
              cv = natGcdName ∨ cv = natLandName ∨ cv = natLorName ∨
              cv = natXorName ∨ cv = natShiftLeftName ∨
              cv = natShiftRightName) ∧ natOpStored env cv = true
          · rw [if_pos hg1, if_pos hg1]
            -- first argument first; the second only behind a literal (D15)
            refine SimC.bind (ih.whnf hs rfl hwf₂a.2)
              (fun s₁ w₁ wx₁ hs₁ hP₁ => ?_)
            obtain ⟨hw1den, hww1⟩ := hP₁
            refine SimC.pureB ?_
            rw [rawNatLitC?_spec' hw1den]
            cases rawNatLit? wx₁ with
            | some n₁ =>
              refine SimC.bind (ih.whnf hs₁ rfl hwfb.2)
                (fun s₂ w₂ wx₂ hs₂ hP₂ => ?_)
              obtain ⟨hw2den, hww2⟩ := hP₂
              refine SimC.pureB ?_
              rw [rawNatLitC?_spec' hw2den]
              cases rawNatLit? wx₂ with
              | some n₂ =>
                dsimp only
                cases hres : natOpResult cv n₁ n₂ with
                | some x =>
                  dsimp only
                  refine SimC.bind_left (pureC_eff hs₂ x)
                    (fun s₃ r hs₃ hQ => ?_)
                  refine SimC.pure hs₃ ⟨hQ, ?_⟩
                  rcases natOpResult_shape hres with ⟨n', rfl⟩ |
                    ⟨bn, rfl⟩ <;> simp [Expr.WScoped]
                | none => exact SimC.pure hs₂ trivial
              | none => exact SimC.pure hs₂ trivial
            | none => exact SimC.pure hs₁ trivial
          · rw [if_neg hg1, if_neg hg1]
            by_cases hg2 : natOpWfNames.contains cv ∧ natLitSupported env
            · rw [if_pos hg2, if_pos hg2]
              refine SimC.bind (ih.whnf hs rfl hwf₂a.2)
                (fun s₁ w₁ wx₁ hs₁ hP₁ => ?_)
              obtain ⟨hw1den, hww1⟩ := hP₁
              refine SimC.pureB ?_
              rw [rawNatLitC?_spec' hw1den]
              cases rawNatLit? wx₁ with
              | some n₁ =>
                refine SimC.bind (ih.whnf hs₁ rfl hwfb.2)
                  (fun s₂ w₂ wx₂ hs₂ hP₂ => ?_)
                obtain ⟨hw2den, hww2⟩ := hP₂
                refine SimC.pureB ?_
                rw [rawNatLitC?_spec' hw2den]
                cases rawNatLit? wx₂ with
                | some n₂ => exact SimC.throw
                | none => exact SimC.pure hs₂ trivial
              | none => exact SimC.pure hs₁ trivial
            · rw [if_neg hg2, if_neg hg2]
              exact SimC.pure hs trivial
      | bvar k => exact SimC.pure hs trivial
      | sort u => exact SimC.pure hs trivial
      | lit l => exact SimC.pure hs trivial
      | fvar idx t => exact SimC.pure hs trivial
      | app f₃ a₃ => exact SimC.pure hs trivial
      | lam t b' m => exact SimC.pure hs trivial
      | forallE t b' m => exact SimC.pure hs trivial
      | letE t v b' => exact SimC.pure hs trivial
      | proj sn jj e' => exact SimC.pure hs trivial
    | bvar k => exact SimC.pure hs trivial
    | sort u => exact SimC.pure hs trivial
    | lit l => exact SimC.pure hs trivial
    | fvar idx t => exact SimC.pure hs trivial
    | lam t b' m => exact SimC.pure hs trivial
    | forallE t b' m => exact SimC.pure hs trivial
    | letE t v b' => exact SimC.pure hs trivial
    | proj sn jj e' => exact SimC.pure hs trivial
  | bvar k => exact SimC.pure hs trivial
  | sort u => exact SimC.pure hs trivial
  | const nm us => exact SimC.pure hs trivial
  | lit l => exact SimC.pure hs trivial
  | fvar idx t => exact SimC.pure hs trivial
  | lam t b' m => exact SimC.pure hs trivial
  | forallE t b' m => exact SimC.pure hs trivial
  | letE t v b' => exact SimC.pure hs trivial
  | proj sn jj e' => exact SimC.pure hs trivial

/-- `reduceNatC_sim` under the defeq-side fvar guard (the guard is the
same `Bool` on both sides after the `hasFvarI` read is peeled, so the
pruned branch is `pure none` twinned). -/
theorem reduceNatIfC_sim (ih : SSimC mode env f) {d : Nat} {i : Expr}
    {e : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i e) (hw : Expr.WScoped d e) (g : Bool) :
    SimC mode env s₀ (RelOC d)
      (if g then reduceNatI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i
        else pure none)
      (if g then reduceNat (fueledFns mode env) env d e else pure none) := by
  cases g
  · exact SimC.pure hs trivial
  · exact reduceNatC_sim ih hs hden hw

end Walks4

end ConLeche.Cached
