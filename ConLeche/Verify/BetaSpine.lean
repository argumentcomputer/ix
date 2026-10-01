module

public import ConLeche.Verify.Fueled

public section

/-!
# Bulk beta: the spine loop and its identification with `whnfCoreBody`
(task #50)

The interned twin's app case (`whnfAppI`/`betaPeelI`,
`ConLeche/Kernel/CoreI.lean`) consumes a whole application spine in one
loop, batching consecutive lambda binders into a single bulk
substitution.  This file provides the pure mirrors (`whnfApp` /
`betaPeel`, generic over the core record like every helper) and proves
the **soundness of the loop against the chained spec**: a successful
loop run at the pure fueled knot is reproduced by the original
one-argument-at-a-time `whnfCoreBody` recursion at some fuel
(`whnfApp_sound_body`).  The interned walk (`ConLeche/Verify/DiscI4`)
composes its simulation against the mirror with this theorem, so the
`Expr`-level specification — and everything above it — is unchanged.

Key steps:

* `appStep` — the app clause's continuation after the function's
  whnf (`whnfCoreBody_app` re-expresses the body's app case with it);
* `whnfApp_snoc`/`betaPeel_snoc` — peeling the *last* argument off a
  loop run yields a loop run of the prefix followed by one `appStep`
  (the fold decomposition; bulk substitutions split by
  `Expr.instantiateList_cons`);
* `whnfApp_sound` — induction over the spine with the snoc
  decomposition, gluing with fuel monotonicity (every mirror is
  fuel-monotone via its `_atF` equation and the `FueledM` bundle).
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ConLeche

variable {mode : CheckMode}
variable {mi : CheckMode}

open Expr

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- The continuation of `whnfCoreBody`'s app case after the function
part's head normalization: beta with the possibly-Prop certificate on
a lambda, iota otherwise. -/
def appStep (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr) (w a : Expr) : m Expr :=
  match w with
  | .lam ty body mb => do
    if betaGateFires mode mb.pw then
      k (body.instantiate1 a)
    else do
      let ta ← r.inferIO depth a
      if ← r.defeq depth ta ty then
        k (body.instantiate1 a)
      else pure (.app (.lam ty body mb) a)
  | f' => do
    match ← iotaRec mode r env depth (.app f' a) with
    | some e'' => k e''
    | none => pure (.app f' a)

/-- `whnfCoreBody`'s app case is one head normalization followed by
`appStep`. -/
theorem whnfCoreBody_app (r : CoreFns m) (env : Env) (depth : Nat)
    (f a : Expr) :
    whnfCoreBody mode r env depth (.app f a)
      = r.whnfCore depth f >>= fun w =>
          appStep mode r env depth (r.whnfCore depth) w a := by rfl

mutual

/-- Pure mirror of the interned bulk-beta loop `whnfAppI`: consume the
spine against the whnf'd head. -/
@[expose] def whnfApp (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr) :
    Expr → List Expr → m Expr
  | v, [] => pure v
  | v, a :: rest =>
    match v with
    | .lam ty body mb => do
      if betaGateFires mode mb.pw then
        betaPeel mode r env depth k body [a] rest
      else do
        let ta ← r.inferIO depth a
        if ← r.defeq depth ta ty then
          betaPeel mode r env depth k body [a] rest
        else pure (Expr.mkAppN (.app (.lam ty body mb) a) rest)
    | v => do
      match ← iotaRec mode r env depth (.app v a) with
      | some e'' => do
        let v' ← k e''
        whnfApp mode r env depth k v' rest
      | none => whnfApp mode r env depth k (.app v a) rest
termination_by _ args => (args.length, 0)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

/-- Pure mirror of the interned peel loop `betaPeelI`: `t` is the raw
lambda body after the binders consumed so far, `acc` their arguments
(innermost first). -/
def betaPeel (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr) :
    Expr → List Expr → List Expr → m Expr
  | t, acc, [] => k (t.instantiateList acc)
  | t, acc, a :: rest =>
    match t with
    | .lam ty body mb => do
      if betaGateFires mode mb.pw then
        betaPeel mode r env depth k body (a :: acc) rest
      else do
        let ta ← r.inferIO depth a
        if ← r.defeq depth ta (ty.instantiateList acc) then
          betaPeel mode r env depth k body (a :: acc) rest
        else pure (Expr.mkAppN
          (.app ((Expr.lam ty body mb).instantiateList acc) a) rest)
    | t => do
      let v ← k (t.instantiateList acc)
      whnfApp mode r env depth k v (a :: rest)
termination_by _ _ args => (args.length, 1)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

end

/-- The iota arm of `whnfApp` (the loop body for a non-lambda head),
as a standalone computation: `whnfApp_ne_lam` identifies the loop with
it, giving every downstream proof a single equation instead of nine
head shapes. -/
@[expose] def whnfAppIota (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr) (v a : Expr) (rest : List Expr) : m Expr := do
  match ← iotaRec mode r env depth (.app v a) with
  | some e'' => do
    let v' ← k e''
    whnfApp mode r env depth k v' rest
  | none => whnfApp mode r env depth k (.app v a) rest

/-- The lambda arm of `whnfApp` (first binder of the peel), as a
standalone computation. -/
@[expose] def whnfAppLam (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr)
    (ty body : Expr) (mb : BinderMeta) (a : Expr)
    (rest : List Expr) : m Expr := do
  if betaGateFires mode mb.pw then
    betaPeel mode r env depth k body [a] rest
  else do
    let ta ← r.inferIO depth a
    if ← r.defeq depth ta ty then
      betaPeel mode r env depth k body [a] rest
    else pure (Expr.mkAppN (.app (.lam ty body mb) a) rest)

theorem whnfApp_nil (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr) (v : Expr) :
    whnfApp mode r env depth k v [] = pure v := by
  rw [whnfApp]

theorem whnfApp_lam (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr)
    (ty body : Expr) (mb : BinderMeta) (a : Expr)
    (rest : List Expr) :
    whnfApp mode r env depth k (.lam ty body mb) (a :: rest)
      = whnfAppLam mode r env depth k ty body mb a rest := by
  rw [whnfApp, whnfAppLam]

theorem whnfApp_ne_lam (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr)
    {v : Expr} (hv : ∀ ty body mb, v ≠ .lam ty body mb)
    (a : Expr) (rest : List Expr) :
    whnfApp mode r env depth k v (a :: rest)
      = whnfAppIota mode r env depth k v a rest := by
  cases v with
  | lam ty body mb => exact absurd rfl (hv ty body mb)
  | _ => rw [whnfApp, whnfAppIota] <;> exact fun _ _ _ h => nomatch h

/-- The non-lambda arm of `betaPeel` for a raw body that is not a
lambda: substitute and hand back to the argument loop. -/
theorem betaPeel_ne_lam (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr)
    {t : Expr} (ht : ∀ ty body mb, t ≠ .lam ty body mb)
    (acc : List Expr) (a : Expr) (rest : List Expr) :
    betaPeel mode r env depth k t acc (a :: rest)
      = k (t.instantiateList acc) >>= fun v =>
          whnfApp mode r env depth k v (a :: rest) := by
  cases t with
  | lam ty body mb => exact absurd rfl (ht ty body mb)
  | _ => rw [betaPeel] <;> exact fun _ _ _ h => nomatch h

theorem betaPeel_nil (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr) (t : Expr) (acc : List Expr) :
    betaPeel mode r env depth k t acc [] = k (t.instantiateList acc) := by
  rw [betaPeel]

/-- The lambda arm of `betaPeel` (peel one more binder). -/
@[expose] def betaPeelLam (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr)
    (ty body : Expr) (mb : BinderMeta) (acc : List Expr)
    (a : Expr) (rest : List Expr) : m Expr := do
  if betaGateFires mode mb.pw then
    betaPeel mode r env depth k body (a :: acc) rest
  else do
    let ta ← r.inferIO depth a
    if ← r.defeq depth ta (ty.instantiateList acc) then
      betaPeel mode r env depth k body (a :: acc) rest
    else pure (Expr.mkAppN
      (.app ((Expr.lam ty body mb).instantiateList acc) a) rest)

theorem betaPeel_lam (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr)
    (ty body : Expr) (mb : BinderMeta) (acc : List Expr)
    (a : Expr) (rest : List Expr) :
    betaPeel mode r env depth k (.lam ty body mb) acc (a :: rest)
      = betaPeelLam mode r env depth k ty body mb acc a rest := by
  rw [betaPeel, betaPeelLam]

/-- `iotaRec` is `none` whenever the spine head is not a constant. -/
theorem iotaRec_head_not_const (r : CoreFns m) (env : Env) (depth : Nat)
    {e : Expr} (h : ∀ c us, e.getAppFn ≠ .const c us) :
    iotaRec mode r env depth e = pure none := by
  unfold iotaRec
  split
  · rename_i c us hc
    exact absurd hc (h c us)
  · rfl

/-! ## The head-normalization loop mirror (task #106)

The interned `whnfCoreStepI`/`whnfCoreLoopI` run beta, iota and
projection steps as *iteration* on their own step budget instead of
chaining them through the knot.  These are the pure `Expr`-level
mirrors; `ConLeche/Verify/DiscI4.lean` simulates the interned loop
against them, and `whnfCoreLoop_sound_body` below reproduces a
successful mirror run by the chained specification `whnfCoreBody` at
some knot fuel — so the specification (and everything above it) is
unchanged. -/

/-- Pure mirror of `whnfCoreStepI`: one head-normalization step with
the loop's continuation `k` abstracted. -/
@[expose] def whnfCoreStepM (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr) : Expr → m Expr
  | .sort u => pure (.sort u)
  | .fvar idx ty => pure (.fvar idx ty)
  | .forallE ty body bi => pure (.forallE ty body bi)
  | .lam ty body mb => pure (.lam ty body mb)
  | .const n us => pure (.const n us)
  | .lit l => pure (.lit l)
  | .app f a =>
    r.whnfCore depth (Expr.app f a).getAppFn >>= fun v =>
      whnfApp mode r env depth k v (Expr.app f a).getAppArgs
  | .proj sn i pe => do
    let e' ← r.whnf depth pe
    let e' ← projLitToCtor r env depth e'
    match env.findProj? sn i with
    | some entry =>
      match e'.getAppFn with
      | .const c us =>
        let args := e'.getAppArgs
        if c = entry.ctor ∧ i < entry.numFields ∧
            args.length = entry.numParams + entry.numFields ∧
            us.length = entry.levelParams.length ∧
            entry.fireOk us = true then
          let arg := args.getD (entry.numParams + i) (.bvar 0)
          if ← projCertAt r env depth mode.verifiedChecks mode.betaGate c us args then
            k arg
          else pure (.proj sn i e')
        else pure (.proj sn i e')
      | _ => pure (.proj sn i e')
    | none => pure (.proj sn i e')
  | .letE _ _ _ =>
    -- unreachable by construction, as in `whnfCoreStepI` (task #241)
    throw (.internal "whnfCore: `let` in an annotated expression")
  | .bvar _ => throw (.notImplemented "whnf beyond the supported fragment")

/-- Pure mirror of `whnfCoreLoopI`: iterate `whnfCoreStepM` on the
step budget. -/
@[expose] def whnfCoreLoopM (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat) :
    Nat → Expr → m Expr
  | 0, _ => throw (.internal "fuel exhausted: whnfCore loop")
  | n + 1, e => whnfCoreStepM mode r env depth (whnfCoreLoopM mode r env depth n) e

/-! ## `atF` equations and fuel monotonicity for the mirrors -/

section AtF

variable {env : Env}

theorem appStep_atF (d : Nat) (k : Expr → FueledM Expr)
    (kF : Expr → CheckM Expr) (F : Nat) (hk : ∀ e, (k e).val F = kF e)
    (w a : Expr) :
    (appStep mode (fueledFns mode env) env d k w a).val F
      = appStep mode (pureFns mode env F) env d kF w a := by
  unfold appStep
  atF_tac4k hk

mutual

theorem whnfApp_atF (d : Nat) (k : Expr → FueledM Expr)
    (kF : Expr → CheckM Expr) (F : Nat) (hk : ∀ e, (k e).val F = kF e) :
    ∀ (xs : List Expr) (v : Expr),
      (whnfApp mode (fueledFns mode env) env d k v xs).val F
        = whnfApp mode (pureFns mode env F) env d kF v xs
  | [], v => by rw [whnfApp_nil, whnfApp_nil]; rfl
  | a :: rest, v => by
    by_cases hlam : ∃ ty body mb, v = Expr.lam ty body mb
    · obtain ⟨ty, body, mb, rfl⟩ := hlam
      rw [whnfApp_lam, whnfApp_lam]
      unfold whnfAppLam
      -- task #161: the β gate is decided before the certificate, and
      -- its condition is the *same* on both sides (`mb` is copied),
      -- so one `by_cases` and the ungated arm is verbatim
      by_cases hgate : betaGateFires mode mb.pw = true
      · rw [if_pos hgate, if_pos hgate]
        exact betaPeel_atF d k kF F hk rest body [a]
      rw [if_neg hgate, if_neg hgate]
      rw [FueledM.atF_bind]
      congr 1
      funext ta
      rw [FueledM.atF_bind]
      congr 1
      funext b
      rw [FueledM.atF_ite]
      cases b with
      | true =>
        simp only [↓reduceIte]
        exact betaPeel_atF d k kF F hk rest body [a]
      | false => rfl
    · have hv : ∀ ty body mb, v ≠ Expr.lam ty body mb :=
        fun ty b mb hh => hlam ⟨ty, b, mb, hh⟩
      rw [whnfApp_ne_lam _ _ _ _ hv, whnfApp_ne_lam _ _ _ _ hv]
      unfold whnfAppIota
      rw [FueledM.atF_bind, iotaRec_atF]
      congr 1
      funext o
      cases o with
      | some e'' =>
        rw [FueledM.atF_bind, hk]
        congr 1
        funext v'
        exact whnfApp_atF d k kF F hk rest v'
      | none => exact whnfApp_atF d k kF F hk rest (.app v a)
termination_by xs => (xs.length, 0)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

theorem betaPeel_atF (d : Nat) (k : Expr → FueledM Expr)
    (kF : Expr → CheckM Expr) (F : Nat) (hk : ∀ e, (k e).val F = kF e) :
    ∀ (xs : List Expr) (t : Expr) (acc : List Expr),
      (betaPeel mode (fueledFns mode env) env d k t acc xs).val F
        = betaPeel mode (pureFns mode env F) env d kF t acc xs
  | [], t, acc => by rw [betaPeel_nil, betaPeel_nil]; exact hk _
  | a :: rest, t, acc => by
    by_cases hlam : ∃ ty body mb, t = Expr.lam ty body mb
    · obtain ⟨ty, body, mb, rfl⟩ := hlam
      rw [betaPeel_lam, betaPeel_lam]
      unfold betaPeelLam
      by_cases hgate : betaGateFires mode mb.pw = true
      · rw [if_pos hgate, if_pos hgate]
        exact betaPeel_atF d k kF F hk rest body (a :: acc)
      rw [if_neg hgate, if_neg hgate]
      rw [FueledM.atF_bind]
      congr 1
      funext ta
      rw [FueledM.atF_bind]
      congr 1
      funext b
      rw [FueledM.atF_ite]
      cases b with
      | true =>
        simp only [↓reduceIte]
        exact betaPeel_atF d k kF F hk rest body (a :: acc)
      | false => rfl
    · have ht : ∀ ty body mb, t ≠ Expr.lam ty body mb :=
        fun ty b mb hh => hlam ⟨ty, b, mb, hh⟩
      rw [betaPeel_ne_lam _ _ _ _ ht, betaPeel_ne_lam _ _ _ _ ht]
      rw [FueledM.atF_bind, hk]
      congr 1
      funext v
      exact whnfApp_atF d k kF F hk (a :: rest) v
termination_by xs => (xs.length, 1)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

end

theorem whnfCoreStepM_atF (d : Nat) (k : Expr → FueledM Expr)
    (kF : Expr → CheckM Expr) (F : Nat) (hk : ∀ e, (k e).val F = kF e)
    (e : Expr) :
    (whnfCoreStepM mode (fueledFns mode env) env d k e).val F
      = whnfCoreStepM mode (pureFns mode env F) env d kF e := by
  cases e <;> (unfold whnfCoreStepM; try rfl)
  case app f a =>
    rw [FueledM.atF_bind]
    congr 1
    funext vh
    exact whnfApp_atF d k kF F hk _ vh
  case proj sn i pe =>
    atF_tac4k hk

theorem whnfCoreLoopM_atF (d : Nat) :
    ∀ (n : Nat) (e : Expr) (F : Nat),
      (whnfCoreLoopM mode (fueledFns mode env) env d n e).val F
        = whnfCoreLoopM mode (pureFns mode env F) env d n e
  | 0, _, _ => rfl
  | n + 1, e, F => by
    simp only [whnfCoreLoopM]
    exact whnfCoreStepM_atF d _ _ F
      (fun x => whnfCoreLoopM_atF d n x F) e

/-- Fuel monotonicity of the loop (via `whnfApp_atF` and the `FueledM`
bundle). -/
theorem whnfApp_mono {d : Nat} {xs : List Expr} {v : Expr} {F F' : Nat}
    (k : Expr → FueledM Expr) (kF kF' : Expr → CheckM Expr)
    (hkF : ∀ e, (k e).val F = kF e) (hkF' : ∀ e, (k e).val F' = kF' e)
    (hle : F ≤ F') {res : Expr}
    (h : whnfApp mode (pureFns mode env F) env d kF v xs = .ok res) :
    whnfApp mode (pureFns mode env F') env d kF' v xs = .ok res := by
  rw [← whnfApp_atF d k kF F hkF] at h
  rw [← whnfApp_atF d k kF' F' hkF']
  exact (whnfApp mode (fueledFns mode env) env d k v xs).property hle h

theorem betaPeel_mono {d : Nat} {xs acc : List Expr} {t : Expr}
    {F F' : Nat}
    (k : Expr → FueledM Expr) (kF kF' : Expr → CheckM Expr)
    (hkF : ∀ e, (k e).val F = kF e) (hkF' : ∀ e, (k e).val F' = kF' e)
    (hle : F ≤ F') {res : Expr}
    (h : betaPeel mode (pureFns mode env F) env d kF t acc xs = .ok res) :
    betaPeel mode (pureFns mode env F') env d kF' t acc xs = .ok res := by
  rw [← betaPeel_atF d k kF F hkF] at h
  rw [← betaPeel_atF d k kF' F' hkF']
  exact (betaPeel mode (fueledFns mode env) env d k t acc xs).property hle h

theorem appStep_mono {d : Nat} {w a : Expr} {F F' : Nat}
    (k : Expr → FueledM Expr) (kF kF' : Expr → CheckM Expr)
    (hkF : ∀ e, (k e).val F = kF e) (hkF' : ∀ e, (k e).val F' = kF' e)
    (hle : F ≤ F') {res : Expr}
    (h : appStep mode (pureFns mode env F) env d kF w a = .ok res) :
    appStep mode (pureFns mode env F') env d kF' w a = .ok res := by
  rw [← appStep_atF d k kF F hkF] at h
  rw [← appStep_atF d k kF' F' hkF']
  exact (appStep mode (fueledFns mode env) env d k w a).property hle h

theorem projLitToCtor_mono {d : Nat} {e : Expr} {F F' : Nat}
    (hle : F ≤ F') {res : Expr}
    (h : projLitToCtor (pureFns mode env F) env d e = .ok res) :
    projLitToCtor (pureFns mode env F') env d e = .ok res := by
  rw [← projLitToCtor_atF] at h ⊢
  exact (projLitToCtor (fueledFns mode env) env d e).property hle h

theorem projCert_mono {d : Nat} {lic : Bool} {c : Name} {us : List Level}
    {args : List Expr} {F F' : Nat} (hle : F ≤ F') {b : Bool}
    (h : projCert (pureFns mode env F) env d lic c us args = .ok b) :
    projCert (pureFns mode env F') env d lic c us args = .ok b := by
  rw [← projCert_atF] at h ⊢
  exact (projCert (fueledFns mode env) env d lic c us args).property hle h

theorem projCertAt_mono {d : Nat} {v lic : Bool} {c : Name} {us : List Level}
    {args : List Expr} {F F' : Nat} (hle : F ≤ F') {b : Bool}
    (h : projCertAt (pureFns mode env F) env d v lic c us args = .ok b) :
    projCertAt (pureFns mode env F') env d v lic c us args = .ok b := by
  unfold projCertAt at h ⊢
  split
  · rename_i hv
    rw [if_pos hv] at h
    exact projCert_mono hle h
  · rename_i hv
    rw [if_neg hv] at h
    exact h

theorem iotaRec_mono {d : Nat} {e : Expr} {F F' : Nat}
    (hle : F ≤ F') {o : Option Expr}
    (h : iotaRec mi (pureFns mode env F) env d e = .ok o) :
    iotaRec mi (pureFns mode env F') env d e = .ok o := by
  rw [← iotaRec_atF] at h ⊢
  exact (iotaRec mi (fueledFns mode env) env d e).property hle h

/-- `whnfCore` is the identity on a lambda (at nonzero fuel). -/
theorem whnfCore_lam (F d : Nat) (ty body : Expr)
    (mb : BinderMeta) :
    whnfCore mode env (F + 1) d (.lam ty body mb)
      = .ok (.lam ty body mb) := rfl

end AtF

/-! ## The snoc decomposition -/

section Snoc

variable {env : Env}

private theorem bind_ok {α β : Type} {x : Except CheckError α}
    {f : α → Except CheckError β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases hx : x with
  | error e =>
    rw [hx] at h
    exact nomatch h
  | ok a =>
    rw [hx] at h
    exact ⟨a, rfl, h⟩

/-- An application chain over an application base is never a lambda. -/
private theorem mkAppN_app_ne_lam :
    ∀ (ys : List Expr) (f a₀ : Expr) (ty body : Expr)
      (mb : BinderMeta), Expr.mkAppN (.app f a₀) ys ≠ .lam ty body mb
  | [], _, _, _, _, _ => by exact fun h => nomatch h
  | y :: ys, f, a₀, ty, body, mb => by
    rw [show Expr.mkAppN (.app f a₀) (y :: ys)
      = Expr.mkAppN (.app (.app f a₀) y) ys from rfl]
    exact mkAppN_app_ne_lam ys (.app f a₀) y ty body mb

/-- The bulk substitution of a lambda, exposed. -/
theorem instList_lam (ty body : Expr)
    (mb : BinderMeta) (acc : List Expr) :
    (Expr.lam ty body mb).instantiateList acc
      = .lam (ty.instantiateList acc) (body.instantiateList acc 1) mb := by
  simp [Expr.instantiateList]

/-- The bulk substitution splits off its head as the innermost
`instantiate1` (the `d = 0`, one-binder-under form used by the peel). -/
theorem instList_cons0 (body : Expr) (a : Expr)
    (acc : List Expr) :
    body.instantiateList (a :: acc)
      = (body.instantiateList acc 1).instantiate1 a := by
  exact Expr.instantiateList_cons acc body a 0

theorem instList_single (body : Expr) (a : Expr) :
    body.instantiateList [a] = body.instantiate1 a := by
  rw [instList_cons0, Expr.instantiateList_nil]

/-- `appStep` on a stuck application chain with a non-constant head:
one more stuck application. -/
private theorem appStep_stuck (F d : Nat) (kF : Expr → CheckM Expr)
    {w : Expr} (a : Expr)
    (hnl : ∀ ty body mb, w ≠ Expr.lam ty body mb)
    (hnc : ∀ c us, w.getAppFn ≠ Expr.const c us) :
    appStep mode (pureFns mode env F) env d kF w a = .ok (.app w a) := by
  have hiota : iotaRec mode (pureFns mode env F) env d (.app w a) = pure none := by
    refine iotaRec_head_not_const _ env d ?_
    intro c us h
    exact hnc c us h
  cases w with
  | lam ty body mb => exact absurd rfl (hnl ty body mb)
  | _ =>
    unfold appStep
    dsimp only
    rw [hiota]
    rfl

private theorem ok_bind {α β : Type} (a : α)
    (f : α → Except CheckError β) :
    ((Except.ok a : Except CheckError α) >>= f) = f a := rfl

mutual

theorem whnfApp_snoc {d : Nat} :
    ∀ (xs : List Expr) (v a : Expr) (F : Nat) (vres : Expr),
      whnfApp mode (pureFns mode env F) env d (whnfCore mode env F d) v (xs ++ [a])
          = .ok vres →
      ∃ F' w,
        whnfApp mode (pureFns mode env F') env d (whnfCore mode env F' d) v xs = .ok w ∧
        appStep mode (pureFns mode env F') env d (whnfCore mode env F' d) w a = .ok vres
  | [], v, a, F, vres => by
    intro H
    rw [List.nil_append] at H
    by_cases hlam : ∃ ty body mb, v = Expr.lam ty body mb
    · obtain ⟨ty, body, mb, rfl⟩ := hlam
      rw [whnfApp_lam] at H
      unfold whnfAppLam at H
      -- task #161: the β gate fires identically in `whnfAppLam` and
      -- in `appStep`; on the fired arm both are the peel/reduct with
      -- no certificate, and the ungated arm is the pre-gate proof
      by_cases hgate : betaGateFires mode mb.pw = true
      · rw [if_pos hgate] at H
        refine ⟨F, _, by rw [whnfApp_nil]; rfl, ?_⟩
        unfold appStep
        dsimp only
        rw [if_pos hgate]
        rw [betaPeel_nil, instList_single] at H
        exact H
      rw [if_neg hgate] at H
      obtain ⟨ta, hta, H⟩ := bind_ok H
      obtain ⟨b, hb, H⟩ := bind_ok H
      refine ⟨F, _, by rw [whnfApp_nil]; rfl, ?_⟩
      unfold appStep
      dsimp only
      rw [if_neg hgate, hta, ok_bind, hb, ok_bind]
      cases b with
      | true =>
        simp only [↓reduceIte] at H ⊢
        rw [betaPeel_nil, instList_single] at H
        exact H
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at H ⊢
        injection H with h
        subst h
        rfl
    · have hv : ∀ ty body mb, v ≠ Expr.lam ty body mb :=
        fun ty b mb hh => hlam ⟨ty, b, mb, hh⟩
      rw [whnfApp_ne_lam _ _ _ _ hv] at H
      unfold whnfAppIota at H
      obtain ⟨o, ho, H⟩ := bind_ok H
      refine ⟨F, v, by rw [whnfApp_nil]; rfl, ?_⟩
      cases v with
      | lam ty body mb => exact absurd rfl (hv ty body mb)
      | _ =>
        unfold appStep
        dsimp only
        rw [ho, ok_bind]
        cases o with
        | some e'' =>
          obtain ⟨v', hv', H⟩ := bind_ok H
          rw [whnfApp_nil] at H
          injection H with h
          subst h
          exact hv'
        | none =>
          rw [whnfApp_nil] at H
          injection H with h
          subst h
          rfl
  | x :: xs', v, a, F, vres => by
    intro H
    rw [List.cons_append] at H
    by_cases hlam : ∃ ty body mb, v = Expr.lam ty body mb
    · obtain ⟨ty, body, mb, rfl⟩ := hlam
      rw [whnfApp_lam] at H
      unfold whnfAppLam at H
      -- task #161: the fired β gate takes the peel arm with no
      -- certificate; the ungated arm below is the pre-gate proof
      by_cases hgate : betaGateFires mode mb.pw = true
      · rw [if_pos hgate] at H
        obtain ⟨F₁, w, hw, hstep⟩ := betaPeel_snoc xs' body [x] a F vres H
        refine ⟨max F F₁, w, ?_,
          appStep_mono ((fueledFns mode env).whnfCore d) _ _ (fun _ => rfl)
            (fun _ => rfl) (Nat.le_max_right F F₁) hstep⟩
        rw [whnfApp_lam]
        unfold whnfAppLam
        rw [if_pos hgate]
        exact betaPeel_mono ((fueledFns mode env).whnfCore d) _ _ (fun _ => rfl)
          (fun _ => rfl) (Nat.le_max_right F F₁) hw
      rw [if_neg hgate] at H
      obtain ⟨ta, hta, H⟩ := bind_ok H
      obtain ⟨b, hb, H⟩ := bind_ok H
      cases b with
      | true =>
        simp only [↓reduceIte] at H
        obtain ⟨F₁, w, hw, hstep⟩ := betaPeel_snoc xs' body [x] a F vres H
        refine ⟨max F F₁, w, ?_,
          appStep_mono ((fueledFns mode env).whnfCore d) _ _ (fun _ => rfl)
            (fun _ => rfl) (Nat.le_max_right F F₁) hstep⟩
        rw [whnfApp_lam]
        unfold whnfAppLam
        rw [if_neg hgate, inferTypeIO_def,
          inferTypeIO_mono (Nat.le_max_left F F₁) hta, ok_bind,
          defeq_def, isDefEqCore_mono (Nat.le_max_left F F₁) hb, ok_bind]
        simp only [↓reduceIte]
        exact betaPeel_mono ((fueledFns mode env).whnfCore d) _ _ (fun _ => rfl)
          (fun _ => rfl) (Nat.le_max_right F F₁) hw
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at H
        injection H with h
        subst h
        refine ⟨F, Expr.mkAppN
          (.app (.lam ty body mb) x) xs', ?_, ?_⟩
        · rw [whnfApp_lam]
          unfold whnfAppLam
          rw [if_neg hgate, hta, ok_bind, hb, ok_bind]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rfl
        · rw [Expr.mkAppN_append_one]
          refine appStep_stuck F d _ a (mkAppN_app_ne_lam xs' _ x) ?_
          intro c us hc
          rw [Expr.getAppFn_mkAppN] at hc
          exact nomatch hc
    · have hv : ∀ ty body mb, v ≠ Expr.lam ty body mb :=
        fun ty b mb hh => hlam ⟨ty, b, mb, hh⟩
      rw [whnfApp_ne_lam _ _ _ _ hv] at H
      unfold whnfAppIota at H
      obtain ⟨o, ho, H⟩ := bind_ok H
      cases o with
      | some e'' =>
        obtain ⟨v', hv', H⟩ := bind_ok H
        obtain ⟨F₁, w, hw, hstep⟩ := whnfApp_snoc xs' v' a F vres H
        refine ⟨max F F₁, w, ?_,
          appStep_mono ((fueledFns mode env).whnfCore d) _ _ (fun _ => rfl)
            (fun _ => rfl) (Nat.le_max_right F F₁) hstep⟩
        rw [whnfApp_ne_lam _ _ _ _ hv]
        unfold whnfAppIota
        rw [iotaRec_mono (Nat.le_max_left F F₁) ho, ok_bind]
        dsimp only
        rw [whnfCore_mono (Nat.le_max_left F F₁) hv', ok_bind]
        exact whnfApp_mono ((fueledFns mode env).whnfCore d) _ _ (fun _ => rfl)
          (fun _ => rfl) (Nat.le_max_right F F₁) hw
      | none =>
        obtain ⟨F₁, w, hw, hstep⟩ := whnfApp_snoc xs' (.app v x) a F vres H
        refine ⟨max F F₁, w, ?_,
          appStep_mono ((fueledFns mode env).whnfCore d) _ _ (fun _ => rfl)
            (fun _ => rfl) (Nat.le_max_right F F₁) hstep⟩
        rw [whnfApp_ne_lam _ _ _ _ hv]
        unfold whnfAppIota
        rw [iotaRec_mono (Nat.le_max_left F F₁) ho, ok_bind]
        dsimp only
        exact whnfApp_mono ((fueledFns mode env).whnfCore d) _ _ (fun _ => rfl)
          (fun _ => rfl) (Nat.le_max_right F F₁) hw
termination_by xs => (xs.length, 0)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

theorem betaPeel_snoc {d : Nat} :
    ∀ (xs : List Expr) (t : Expr) (acc : List Expr) (a : Expr) (F : Nat)
      (vres : Expr),
      betaPeel mode (pureFns mode env F) env d (whnfCore mode env F d) t acc (xs ++ [a])
          = .ok vres →
      ∃ F' w,
        betaPeel mode (pureFns mode env F') env d (whnfCore mode env F' d) t acc xs
          = .ok w ∧
        appStep mode (pureFns mode env F') env d (whnfCore mode env F' d) w a = .ok vres
  | [], t, acc, a, F, vres => by
    intro H
    rw [List.nil_append] at H
    by_cases hlam : ∃ ty body mb, t = Expr.lam ty body mb
    · obtain ⟨ty, body, mb, rfl⟩ := hlam
      rw [betaPeel_lam] at H
      unfold betaPeelLam at H
      have hid : betaPeel mode (pureFns mode env (F + 1)) env d
          (whnfCore mode env (F + 1) d) (Expr.lam ty body mb) acc []
          = .ok (.lam (ty.instantiateList acc)
              (body.instantiateList acc 1) mb) := by
        rw [betaPeel_nil, instList_lam]
        exact whnfCore_lam F d _ _ _
      by_cases hgate : betaGateFires mode mb.pw = true
      · rw [if_pos hgate] at H
        refine ⟨F + 1, _, hid, ?_⟩
        unfold appStep
        dsimp only
        rw [if_pos hgate]
        rw [betaPeel_nil] at H
        rw [← instList_cons0]
        exact whnfCore_mono (Nat.le_succ F) H
      rw [if_neg hgate] at H
      obtain ⟨ta, hta, H⟩ := bind_ok H
      obtain ⟨b, hb, H⟩ := bind_ok H
      refine ⟨F + 1, _, hid, ?_⟩
      unfold appStep
      dsimp only
      rw [if_neg hgate, inferTypeIO_def, inferTypeIO_mono (Nat.le_succ F) hta,
        ok_bind, defeq_def, isDefEqCore_mono (Nat.le_succ F) hb, ok_bind]
      cases b with
      | true =>
        simp only [↓reduceIte] at H ⊢
        rw [betaPeel_nil] at H
        rw [← instList_cons0]
        exact whnfCore_mono (Nat.le_succ F) H
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at H ⊢
        injection H with h
        subst h
        rw [instList_lam]
        rfl
    · have ht : ∀ ty body mb, t ≠ Expr.lam ty body mb :=
        fun ty b mb hh => hlam ⟨ty, b, mb, hh⟩
      rw [betaPeel_ne_lam _ _ _ _ ht] at H
      obtain ⟨v₀, hv₀, H⟩ := bind_ok H
      obtain ⟨F₁, w, hw, hstep⟩ := whnfApp_snoc [] v₀ a F vres H
      rw [whnfApp_nil] at hw
      injection hw with hw'
      subst hw'
      refine ⟨max F F₁, v₀, ?_,
        appStep_mono ((fueledFns mode env).whnfCore d) _ _ (fun _ => rfl)
            (fun _ => rfl) (Nat.le_max_right F F₁) hstep⟩
      rw [betaPeel_nil]
      exact whnfCore_mono (Nat.le_max_left F F₁) hv₀
  | x :: xs', t, acc, a, F, vres => by
    intro H
    rw [List.cons_append] at H
    by_cases hlam : ∃ ty body mb, t = Expr.lam ty body mb
    · obtain ⟨ty, body, mb, rfl⟩ := hlam
      rw [betaPeel_lam] at H
      unfold betaPeelLam at H
      by_cases hgate : betaGateFires mode mb.pw = true
      · rw [if_pos hgate] at H
        obtain ⟨F₁, w, hw, hstep⟩ :=
          betaPeel_snoc xs' body (x :: acc) a F vres H
        refine ⟨max F F₁, w, ?_,
          appStep_mono ((fueledFns mode env).whnfCore d) _ _ (fun _ => rfl)
            (fun _ => rfl) (Nat.le_max_right F F₁) hstep⟩
        rw [betaPeel_lam]
        unfold betaPeelLam
        rw [if_pos hgate]
        exact betaPeel_mono ((fueledFns mode env).whnfCore d) _ _ (fun _ => rfl)
          (fun _ => rfl) (Nat.le_max_right F F₁) hw
      rw [if_neg hgate] at H
      obtain ⟨ta, hta, H⟩ := bind_ok H
      obtain ⟨b, hb, H⟩ := bind_ok H
      cases b with
      | true =>
        simp only [↓reduceIte] at H
        obtain ⟨F₁, w, hw, hstep⟩ :=
          betaPeel_snoc xs' body (x :: acc) a F vres H
        refine ⟨max F F₁, w, ?_,
          appStep_mono ((fueledFns mode env).whnfCore d) _ _ (fun _ => rfl)
            (fun _ => rfl) (Nat.le_max_right F F₁) hstep⟩
        rw [betaPeel_lam]
        unfold betaPeelLam
        rw [if_neg hgate, inferTypeIO_def,
          inferTypeIO_mono (Nat.le_max_left F F₁) hta, ok_bind,
          defeq_def, isDefEqCore_mono (Nat.le_max_left F F₁) hb, ok_bind]
        simp only [↓reduceIte]
        exact betaPeel_mono ((fueledFns mode env).whnfCore d) _ _ (fun _ => rfl)
          (fun _ => rfl) (Nat.le_max_right F F₁) hw
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at H
        injection H with h
        subst h
        refine ⟨F, Expr.mkAppN
          (.app ((Expr.lam ty body mb).instantiateList acc)
            x) xs', ?_, ?_⟩
        · rw [betaPeel_lam]
          unfold betaPeelLam
          rw [if_neg hgate, hta, ok_bind, hb, ok_bind]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rfl
        · rw [Expr.mkAppN_append_one]
          refine appStep_stuck F d _ a (mkAppN_app_ne_lam xs' _ x) ?_
          intro c us hc
          rw [Expr.getAppFn_mkAppN] at hc
          rw [show Expr.getAppFn (.app
              ((Expr.lam ty body mb).instantiateList acc) x)
            = Expr.getAppFn
              ((Expr.lam ty body mb).instantiateList acc)
            from rfl, instList_lam] at hc
          exact nomatch hc
    · have ht : ∀ ty body mb, t ≠ Expr.lam ty body mb :=
        fun ty b mb hh => hlam ⟨ty, b, mb, hh⟩
      rw [betaPeel_ne_lam _ _ _ _ ht] at H
      obtain ⟨v₀, hv₀, H⟩ := bind_ok H
      obtain ⟨F₁, w, hw, hstep⟩ := whnfApp_snoc (x :: xs') v₀ a F vres H
      refine ⟨max F F₁, w, ?_,
        appStep_mono ((fueledFns mode env).whnfCore d) _ _ (fun _ => rfl)
            (fun _ => rfl) (Nat.le_max_right F F₁) hstep⟩
      rw [betaPeel_ne_lam _ _ _ _ ht,
        whnfCore_mono (Nat.le_max_left F F₁) hv₀, ok_bind]
      exact whnfApp_mono ((fueledFns mode env).whnfCore d) _ _ (fun _ => rfl)
          (fun _ => rfl) (Nat.le_max_right F F₁) hw
termination_by xs => (xs.length, 1)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

end

end Snoc

/-! ## Soundness of the loop against the chained body -/

section Sound

variable {env : Env}

private theorem whnfApp_sound_rev {d : Nat} :
    ∀ (rxs : List Expr) (h vh vres : Expr) (F₀ F : Nat),
      whnfCore mode env F₀ d h = .ok vh →
      whnfApp mode (pureFns mode env F) env d (whnfCore mode env F d) vh rxs.reverse
          = .ok vres →
      ∃ F', whnfCore mode env F' d (Expr.mkAppN h rxs.reverse) = .ok vres
  | [], h, vh, vres, F₀, F => by
    intro hh H
    rw [List.reverse_nil, whnfApp_nil] at H
    injection H with h1
    subst h1
    exact ⟨F₀, hh⟩
  | r :: rrs, h, vh, vres, F₀, F => by
    intro hh H
    rw [List.reverse_cons] at H
    obtain ⟨F₁, w, hw, hstep⟩ := whnfApp_snoc rrs.reverse vh r F vres H
    obtain ⟨F₂, hP⟩ := whnfApp_sound_rev rrs h vh w F₀ F₁ hh hw
    refine ⟨max F₂ F₁ + 1, ?_⟩
    rw [List.reverse_cons, Expr.mkAppN_append_one, whnfCore_succ,
      whnfCoreBody_app, whnfCore_def,
      whnfCore_mono (Nat.le_max_left F₂ F₁) hP, ok_bind]
    exact appStep_mono ((fueledFns mode env).whnfCore d) _ _ (fun _ => rfl)
      (fun _ => rfl) (Nat.le_max_right F₂ F₁) hstep

/-- A successful loop run over a normalized head is reproduced by the
chained `whnfCore` recursion on the whole application, at some fuel. -/
theorem whnfApp_sound {d : Nat} (xs : List Expr) (h vh vres : Expr)
    (F₀ F : Nat) (hh : whnfCore mode env F₀ d h = .ok vh)
    (H : whnfApp mode (pureFns mode env F) env d (whnfCore mode env F d) vh xs
      = .ok vres) :
    ∃ F', whnfCore mode env F' d (Expr.mkAppN h xs) = .ok vres := by
  have hx : xs.reverse.reverse = xs := List.reverse_reverse xs
  have := whnfApp_sound_rev (d := d) xs.reverse h vh vres F₀ F hh
    (by rw [hx]; exact H)
  rwa [hx] at this

/-! ### From the loop's continuation to the chained `whnfCore`

A loop run whose continuation is *sound* (every success it reports is
reproduced by the chained `whnfCore` at some fuel) is itself
reproduced by a loop run whose continuation **is** `whnfCore`; the
existing `snoc`/`sound` machinery then reduces it to `whnfCoreBody`.
This is what lets the interned loop (task #106) run its reduction
chain on its own step budget while the specification stays
chained. -/

/-- The soundness hypothesis carried by a loop continuation. -/
def KSound (mode : CheckMode) (env : Env) (d : Nat) (k : Expr → FueledM Expr) : Prop :=
  ∀ (G : Nat) (e v : Expr), (k e).val G = .ok v →
    ∃ M, whnfCore mode env M d e = .ok v

mutual

theorem whnfApp_ksound {d : Nat} (k : Expr → FueledM Expr)
    (hks : KSound mode env d k) :
    ∀ (xs : List Expr) (v res : Expr) (F : Nat),
      whnfApp mode (pureFns mode env F) env d (fun e => (k e).val F) v xs
        = .ok res →
      ∃ F', whnfApp mode (pureFns mode env F') env d (whnfCore mode env F' d) v xs
        = .ok res
  | [], v, res, F => by
    intro H
    rw [whnfApp_nil] at H
    injection H with h1
    subst h1
    exact ⟨F, by rw [whnfApp_nil]; rfl⟩
  | a :: rest, v, res, F => by
    intro H
    by_cases hlam : ∃ ty body mb, v = Expr.lam ty body mb
    · obtain ⟨ty, body, mb, rfl⟩ := hlam
      rw [whnfApp_lam] at H
      unfold whnfAppLam at H
      by_cases hgate : betaGateFires mode mb.pw = true
      · rw [if_pos hgate] at H
        obtain ⟨F₁, hP⟩ := betaPeel_ksound k hks rest body [a] res F H
        refine ⟨max F F₁, ?_⟩
        rw [whnfApp_lam]
        unfold whnfAppLam
        rw [if_pos hgate]
        exact betaPeel_mono ((fueledFns mode env).whnfCore d) _ _
          (fun _ => rfl) (fun _ => rfl) (Nat.le_max_right F F₁) hP
      rw [if_neg hgate] at H
      obtain ⟨ta, hta, H⟩ := bind_ok H
      obtain ⟨b, hb, H⟩ := bind_ok H
      cases b with
      | true =>
        simp only [↓reduceIte] at H
        obtain ⟨F₁, hP⟩ := betaPeel_ksound k hks rest body [a] res F H
        refine ⟨max F F₁, ?_⟩
        rw [whnfApp_lam]
        unfold whnfAppLam
        rw [if_neg hgate, inferTypeIO_def,
          inferTypeIO_mono (Nat.le_max_left F F₁) hta,
          ok_bind, defeq_def,
          isDefEqCore_mono (Nat.le_max_left F F₁) hb, ok_bind]
        simp only [↓reduceIte]
        exact betaPeel_mono ((fueledFns mode env).whnfCore d) _ _
          (fun _ => rfl) (fun _ => rfl) (Nat.le_max_right F F₁) hP
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at H
        injection H with h1
        subst h1
        refine ⟨F, ?_⟩
        rw [whnfApp_lam]
        unfold whnfAppLam
        rw [if_neg hgate, hta, ok_bind, hb, ok_bind]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rfl
    · have hv : ∀ ty body mb, v ≠ Expr.lam ty body mb :=
        fun ty b mb hh => hlam ⟨ty, b, mb, hh⟩
      rw [whnfApp_ne_lam _ _ _ _ hv] at H
      unfold whnfAppIota at H
      obtain ⟨o, ho, H⟩ := bind_ok H
      cases o with
      | some e'' =>
        obtain ⟨v', hv', H⟩ := bind_ok H
        obtain ⟨M, hM⟩ := hks F e'' v' hv'
        obtain ⟨F₁, hP⟩ := whnfApp_ksound k hks rest v' res F H
        refine ⟨max (max F M) F₁, ?_⟩
        rw [whnfApp_ne_lam _ _ _ _ hv]
        unfold whnfAppIota
        rw [iotaRec_mono (Nat.le_trans (Nat.le_max_left F M)
            (Nat.le_max_left _ F₁)) ho, ok_bind]
        dsimp only
        rw [whnfCore_mono (Nat.le_trans (Nat.le_max_right F M)
          (Nat.le_max_left _ F₁)) hM, ok_bind]
        exact whnfApp_mono ((fueledFns mode env).whnfCore d) _ _
          (fun _ => rfl) (fun _ => rfl) (Nat.le_max_right _ F₁) hP
      | none =>
        obtain ⟨F₁, hP⟩ := whnfApp_ksound k hks rest (.app v a) res F H
        refine ⟨max F F₁, ?_⟩
        rw [whnfApp_ne_lam _ _ _ _ hv]
        unfold whnfAppIota
        rw [iotaRec_mono (Nat.le_max_left F F₁) ho, ok_bind]
        dsimp only
        exact whnfApp_mono ((fueledFns mode env).whnfCore d) _ _
          (fun _ => rfl) (fun _ => rfl) (Nat.le_max_right F F₁) hP
termination_by xs => (xs.length, 0)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

theorem betaPeel_ksound {d : Nat} (k : Expr → FueledM Expr)
    (hks : KSound mode env d k) :
    ∀ (xs : List Expr) (t : Expr) (acc : List Expr) (res : Expr)
      (F : Nat),
      betaPeel mode (pureFns mode env F) env d (fun e => (k e).val F) t acc xs
        = .ok res →
      ∃ F', betaPeel mode (pureFns mode env F') env d (whnfCore mode env F' d) t acc xs
        = .ok res
  | [], t, acc, res, F => by
    intro H
    rw [betaPeel_nil] at H
    obtain ⟨M, hM⟩ := hks F _ _ H
    exact ⟨M, by rw [betaPeel_nil]; exact hM⟩
  | a :: rest, t, acc, res, F => by
    intro H
    by_cases hlam : ∃ ty body mb, t = Expr.lam ty body mb
    · obtain ⟨ty, body, mb, rfl⟩ := hlam
      rw [betaPeel_lam] at H
      unfold betaPeelLam at H
      by_cases hgate : betaGateFires mode mb.pw = true
      · rw [if_pos hgate] at H
        obtain ⟨F₁, hP⟩ :=
          betaPeel_ksound k hks rest body (a :: acc) res F H
        refine ⟨max F F₁, ?_⟩
        rw [betaPeel_lam]
        unfold betaPeelLam
        rw [if_pos hgate]
        exact betaPeel_mono ((fueledFns mode env).whnfCore d) _ _
          (fun _ => rfl) (fun _ => rfl) (Nat.le_max_right F F₁) hP
      rw [if_neg hgate] at H
      obtain ⟨ta, hta, H⟩ := bind_ok H
      obtain ⟨b, hb, H⟩ := bind_ok H
      cases b with
      | true =>
        simp only [↓reduceIte] at H
        obtain ⟨F₁, hP⟩ :=
          betaPeel_ksound k hks rest body (a :: acc) res F H
        refine ⟨max F F₁, ?_⟩
        rw [betaPeel_lam]
        unfold betaPeelLam
        rw [if_neg hgate, inferTypeIO_def,
          inferTypeIO_mono (Nat.le_max_left F F₁) hta,
          ok_bind, defeq_def,
          isDefEqCore_mono (Nat.le_max_left F F₁) hb, ok_bind]
        simp only [↓reduceIte]
        exact betaPeel_mono ((fueledFns mode env).whnfCore d) _ _
          (fun _ => rfl) (fun _ => rfl) (Nat.le_max_right F F₁) hP
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at H
        injection H with h1
        subst h1
        refine ⟨F, ?_⟩
        rw [betaPeel_lam]
        unfold betaPeelLam
        rw [if_neg hgate, hta, ok_bind, hb, ok_bind]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rfl
    · have ht : ∀ ty body mb, t ≠ Expr.lam ty body mb :=
        fun ty b mb hh => hlam ⟨ty, b, mb, hh⟩
      rw [betaPeel_ne_lam _ _ _ _ ht] at H
      obtain ⟨v₀, hv₀, H⟩ := bind_ok H
      obtain ⟨M, hM⟩ := hks F _ _ hv₀
      obtain ⟨F₁, hP⟩ := whnfApp_ksound k hks (a :: rest) v₀ res F H
      refine ⟨max M F₁, ?_⟩
      rw [betaPeel_ne_lam _ _ _ _ ht,
        whnfCore_mono (Nat.le_max_left M F₁) hM, ok_bind]
      exact whnfApp_mono ((fueledFns mode env).whnfCore d) _ _
        (fun _ => rfl) (fun _ => rfl) (Nat.le_max_right M F₁) hP
termination_by xs => (xs.length, 1)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

end

/-- One loop *step* whose continuation is sound is reproduced by the
chained specification body `whnfCoreBody` at some knot fuel. -/
theorem whnfCoreStepM_sound {d : Nat} (k : Expr → FueledM Expr)
    (hks : KSound mode env d k) {e res : Expr} (F : Nat)
    (H : whnfCoreStepM mode (pureFns mode env F) env d (fun x => (k x).val F) e
      = .ok res) :
    ∃ F', whnfCoreBody mode (pureFns mode env F') env d e = .ok res := by
  cases e with
  | bvar j => exact absurd H (by simp [whnfCoreStepM])
  | sort u => exact ⟨F, H⟩
  | fvar idx ty => exact ⟨F, H⟩
  | const nm us => exact ⟨F, H⟩
  | lit l => exact ⟨F, H⟩
  | lam ty bd mb => exact ⟨F, H⟩
  | forallE ty bd mb => exact ⟨F, H⟩
  | letE ty v bd =>
    -- task #241: the ζ arm is a positive `.internal` error
    exact absurd H (by simp [whnfCoreStepM])
  | app f a =>
    simp only [whnfCoreStepM] at H
    obtain ⟨vh, hvh, H⟩ := bind_ok H
    obtain ⟨F₁, hP⟩ := whnfApp_ksound k hks _ vh res F H
    obtain ⟨F₂, hQ⟩ := whnfApp_sound (Expr.app f a).getAppArgs
      (Expr.app f a).getAppFn vh res F F₁ hvh hP
    rw [Expr.mkAppN_getApp] at hQ
    cases F₂ with
    | zero => rw [whnfCore_zero] at hQ; exact nomatch hQ
    | succ G => exact ⟨G, by rw [← whnfCore_succ]; exact hQ⟩
  | proj sn i pe =>
    simp only [whnfCoreStepM] at H
    obtain ⟨w, hw, H⟩ := bind_ok H
    obtain ⟨w', hw', H⟩ := bind_ok H
    revert H
    cases hfp : env.findProj? sn i with
    | none =>
      intro H
      refine ⟨F, ?_⟩
      simp only [whnfCoreBody]
      rw [hw, ok_bind, hw', ok_bind, hfp]
      exact H
    | some entry =>
    cases hfn : w'.getAppFn with
    | const c us =>
      dsimp only
      split
      · rename_i hcond
        intro H
        obtain ⟨b, hb, H⟩ := bind_ok H
        cases b with
        | false =>
          refine ⟨F, ?_⟩
          simp only [whnfCoreBody]
          rw [hw, ok_bind, hw', ok_bind, hfp, hfn]
          dsimp only
          rw [if_pos hcond, hb, ok_bind]
          simpa only [Bool.false_eq_true, ↓reduceIte] using H
        | true =>
          simp only [↓reduceIte] at H
          obtain ⟨M, hM⟩ := hks F _ _ H
          refine ⟨max F M, ?_⟩
          simp only [whnfCoreBody]
          rw [whnf_def, whnf_mono (Nat.le_max_left F M) hw, ok_bind,
            projLitToCtor_mono (Nat.le_max_left F M) hw', ok_bind,
            hfp, hfn]
          dsimp only
          rw [if_pos hcond,
            projCertAt_mono (Nat.le_max_left F M) hb, ok_bind]
          simp only [↓reduceIte]
          rw [whnfCore_def]
          exact whnfCore_mono (Nat.le_max_right F M) hM
      · rename_i hcond
        intro H
        refine ⟨F, ?_⟩
        simp only [whnfCoreBody]
        rw [hw, ok_bind, hw', ok_bind, hfp, hfn]
        dsimp only
        rw [if_neg hcond]
        exact H
    | _ =>
      intro H
      refine ⟨F, ?_⟩
      simp only [whnfCoreBody]
      rw [hw, ok_bind, hw', ok_bind, hfp, hfn]
      exact H

/-- `KSound` for the loop mirror itself: by induction on the step
budget.  This is the bridge the interned walk composes with — a
successful *loop* run is reproduced by the chained specification at
some knot fuel, so `whnfCoreBody` (and everything above it) never sees
the loop. -/
theorem whnfCoreLoopM_ksound {d : Nat} :
    ∀ (n : Nat),
      KSound mode env d (fun e => whnfCoreLoopM mode (fueledFns mode env) env d n e)
  | 0 => by
    intro G e v h
    rw [whnfCoreLoopM_atF d 0 e G] at h
    exact absurd h (by simp [whnfCoreLoopM])
  | n + 1 => by
    intro G e v h
    rw [whnfCoreLoopM_atF d (n + 1) e G] at h
    simp only [whnfCoreLoopM] at h
    obtain ⟨F', hF'⟩ :=
      whnfCoreStepM_sound (env := env) (d := d)
        (fun x => whnfCoreLoopM mode (fueledFns mode env) env d n x)
        (whnfCoreLoopM_ksound n) (e := e) (res := v) G
        (by
          rw [show (fun x => (whnfCoreLoopM mode (fueledFns mode env) env d n x).val G)
              = whnfCoreLoopM mode (pureFns mode env G) env d n from
            funext fun x => whnfCoreLoopM_atF d n x G]
          exact h)
    exact ⟨F' + 1, by rw [whnfCore_succ]; exact hF'⟩

/-- The bridge the interned walk uses: a successful *loop* run at the
fueled record is reproduced by `whnfCoreBody` on the same node, at
some knot fuel. -/
theorem whnfCoreLoop_sound_body (d : Nat) (e vres : Expr) (n F : Nat)
    (H : (whnfCoreLoopM mode (fueledFns mode env) env d n e).val F = .ok vres) :
    ∃ F', (whnfCoreBody mode (fueledFns mode env) env d e).val F' = .ok vres := by
  obtain ⟨M, hM⟩ := whnfCoreLoopM_ksound n F e vres H
  cases M with
  | zero => rw [whnfCore_zero] at hM; exact nomatch hM
  | succ G =>
    exact ⟨G, by rw [whnfCoreBody_atF, ← whnfCore_succ]; exact hM⟩

end Sound

/-! ## The application-inference spine loop (task #50)

Same construction for `inferBody`'s app case: the type of an
application spine is inferred by walking the Π-telescope with deferred
substitution — syntactic `∀`-binders are peeled against the arguments
(each argument checked against its *substituted domain* only), the
codomain substituted once per peeled group; a non-syntactic telescope
step substitutes and normalizes, exactly like the chained body. -/

/-- The continuation of `inferBody`'s app case after the function
part's inference. -/
def inferStep (r : CoreFns m) (depth : Nat) (tf a : Expr) : m Expr := do
  match ← r.whnf depth tf with
  | .forallE ty body _mt => do
    let ta ← r.infer depth a
    unless ← r.defeq depth ta ty do
      throw (.invalid "application type mismatch")
    pure (body.instantiate1 a)
  | _ => throw (.invalid "function expected")

/-- `inferBody`'s app case at the pure knot is one inference followed
by `inferStep` (stated at `CheckM`, where the do-notation reduces). -/
theorem inferBody_app_pure (env : Env) (F depth : Nat) (f a : Expr) :
    inferBody mode (pureFns mode env F) env depth (.app f a)
      = (pureFns mode env F).infer depth f >>= fun tf =>
          inferStep (pureFns mode env F) depth tf a := by rfl

/-- Pure mirror of the interned inference spine loop `inferSpineI`:
`ty` is the raw Π-telescope after the binders consumed so far, `acc`
their arguments (innermost first). -/
@[expose] def inferSpine (r : CoreFns m) (depth : Nat) :
    Expr → List Expr → List Expr → m Expr
  | ty, acc, [] => pure (ty.instantiateList acc)
  | ty, acc, a :: rest =>
    match ty with
    | .forallE dom body _mt => do
      let ta ← r.infer depth a
      unless ← r.defeq depth ta (dom.instantiateList acc) do
        throw (.invalid "application type mismatch")
      inferSpine r depth body (a :: acc) rest
    | ty => do
      match ← r.whnf depth (ty.instantiateList acc) with
      | .forallE dom body _mt => do
        let ta ← r.infer depth a
        unless ← r.defeq depth ta dom do
          throw (.invalid "application type mismatch")
        inferSpine r depth body [a] rest
      | _ => throw (.invalid "function expected")

/-- The syntactic-`∀` arm of `inferSpine`. -/
@[expose] def inferSpinePi (r : CoreFns m) (depth : Nat) (dom body : Expr)
    (_mt : BinderMeta) (acc : List Expr) (a : Expr) (rest : List Expr) :
    m Expr := do
  let ta ← r.infer depth a
  unless ← r.defeq depth ta (dom.instantiateList acc) do
    throw (.invalid "application type mismatch")
  inferSpine r depth body (a :: acc) rest

/-- The normalize-and-retry arm of `inferSpine`. -/
@[expose] def inferSpineWhnf (r : CoreFns m) (depth : Nat) (ty : Expr)
    (acc : List Expr) (a : Expr) (rest : List Expr) : m Expr := do
  match ← r.whnf depth (ty.instantiateList acc) with
  | .forallE dom body _mt => do
    let ta ← r.infer depth a
    unless ← r.defeq depth ta dom do
      throw (.invalid "application type mismatch")
    inferSpine r depth body [a] rest
  | _ => throw (.invalid "function expected")

theorem inferSpine_nil (r : CoreFns m) (depth : Nat) (ty : Expr)
    (acc : List Expr) :
    inferSpine r depth ty acc [] = pure (ty.instantiateList acc) := by
  rw [inferSpine]

theorem inferSpine_pi (r : CoreFns m) (depth : Nat)
    (dom body : Expr) (bi : BinderMeta) (acc : List Expr) (a : Expr)
    (rest : List Expr) :
    inferSpine r depth (.forallE dom body bi) acc (a :: rest)
      = inferSpinePi r depth dom body bi acc a rest := by
  rw [inferSpine, inferSpinePi]

theorem inferSpine_ne_pi (r : CoreFns m) (depth : Nat) {ty : Expr}
    (hty : ∀ dom body bi, ty ≠ .forallE dom body bi)
    (acc : List Expr) (a : Expr) (rest : List Expr) :
    inferSpine r depth ty acc (a :: rest)
      = inferSpineWhnf r depth ty acc a rest := by
  cases ty with
  | forallE dom body bi => exact absurd rfl (hty dom body bi)
  | _ => rw [inferSpine, inferSpineWhnf] <;> exact fun _ _ _ h => nomatch h

/-- The bulk substitution of a `∀`, exposed. -/
theorem instList_forallE (dom body : Expr)
    (bi : BinderMeta) (acc : List Expr) :
    (Expr.forallE dom body bi).instantiateList acc
      = .forallE (dom.instantiateList acc)
          (body.instantiateList acc 1) bi := by
  simp [Expr.instantiateList]

section InferAtF

variable {env : Env}

theorem inferStep_atF (d : Nat) (tf a : Expr) (F : Nat) :
    (inferStep (fueledFns mode env) d tf a).val F
      = inferStep (pureFns mode env F) d tf a := by
  unfold inferStep
  atF_tac4

theorem inferSpine_atF (d : Nat) :
    ∀ (xs : List Expr) (ty : Expr) (acc : List Expr) (F : Nat),
      (inferSpine (fueledFns mode env) d ty acc xs).val F
        = inferSpine (pureFns mode env F) d ty acc xs
  | [], ty, acc, F => by rw [inferSpine_nil, inferSpine_nil]; rfl
  | a :: rest, ty, acc, F => by
    by_cases hpi : ∃ dom body bi, ty = Expr.forallE dom body bi
    · obtain ⟨dom, body, bi, rfl⟩ := hpi
      rw [inferSpine_pi, inferSpine_pi]
      unfold inferSpinePi
      rw [FueledM.atF_bind]
      congr 1
      funext ta
      rw [FueledM.atF_bind]
      congr 1
      funext b
      cases b with
      | true =>
        show (inferSpine (fueledFns mode env) d body (a :: acc) rest).val F = _
        rw [inferSpine_atF d rest body (a :: acc) F]
        rfl
      | false => rfl
    · have hty : ∀ dom body bi, ty ≠ Expr.forallE dom body bi :=
        fun dom b bi hh => hpi ⟨dom, b, bi, hh⟩
      rw [inferSpine_ne_pi _ _ hty, inferSpine_ne_pi _ _ hty]
      unfold inferSpineWhnf
      rw [FueledM.atF_bind]
      congr 1
      funext w
      cases w with
      | forallE dom body bi =>
        dsimp only
        rw [FueledM.atF_bind]
        congr 1
        funext ta
        rw [FueledM.atF_bind]
        congr 1
        funext b
        cases b with
        | true =>
          show (inferSpine (fueledFns mode env) d body [a] rest).val F = _
          rw [inferSpine_atF d rest body [a] F]
          rfl
        | false => rfl
      | _ => rfl

theorem inferSpine_mono {d : Nat} {xs acc : List Expr} {ty : Expr}
    {F F' : Nat} (hle : F ≤ F') {res : Expr}
    (h : inferSpine (pureFns mode env F) d ty acc xs = .ok res) :
    inferSpine (pureFns mode env F') d ty acc xs = .ok res := by
  rw [← inferSpine_atF] at h ⊢
  exact (inferSpine (fueledFns mode env) d ty acc xs).property hle h

theorem inferStep_mono {d : Nat} {tf a : Expr} {F F' : Nat}
    (hle : F ≤ F') {res : Expr}
    (h : inferStep (pureFns mode env F) d tf a = .ok res) :
    inferStep (pureFns mode env F') d tf a = .ok res := by
  rw [← inferStep_atF] at h ⊢
  exact (inferStep (fueledFns mode env) d tf a).property hle h

/-- `whnf` is the identity on a `∀` (at fuel `≥ 2`: one level for the
`whnfCore` inside the loop). -/
theorem whnf_forallE (F d : Nat) (t b : Expr)
    (mb : BinderMeta) :
    whnf mode env (F + 2) d (.forallE t b mb) = .ok (.forallE t b mb) := by
  -- one iteration of the reduction loop suffices (task #106: the step
  -- budget is `irreducible`, so peel it with its positivity witness)
  obtain ⟨k, hk⟩ := whnfLoopFuel_succ
  rw [whnf_succ]
  show whnfLoop (pureFns mode env (F + 1)) env d whnfLoopFuel _ = _
  rw [hk]
  rfl

end InferAtF

section InferSnoc

variable {env : Env}

theorem inferSpine_snoc {d : Nat} :
    ∀ (xs : List Expr) (ty : Expr) (acc : List Expr) (a : Expr) (F : Nat)
      (vres : Expr),
      inferSpine (pureFns mode env F) d ty acc (xs ++ [a]) = .ok vres →
      ∃ F' w, inferSpine (pureFns mode env F') d ty acc xs = .ok w ∧
        inferStep (pureFns mode env F') d w a = .ok vres
  | [], ty, acc, a, F, vres => by
    intro H
    rw [List.nil_append] at H
    by_cases hpi : ∃ dom body bi, ty = Expr.forallE dom body bi
    · obtain ⟨dom, body, bi, rfl⟩ := hpi
      rw [inferSpine_pi] at H
      unfold inferSpinePi at H
      obtain ⟨ta, hta, H⟩ := bind_ok H
      obtain ⟨b, hb, H⟩ := bind_ok H
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at H
        exact nomatch H
      | true =>
        simp only [↓reduceIte] at H
        rw [inferSpine_nil] at H
        injection H with h
        subst h
        refine ⟨F + 2, _, by rw [inferSpine_nil]; rfl, ?_⟩
        unfold inferStep
        rw [instList_forallE, whnf_def, whnf_forallE, ok_bind]
        dsimp only
        rw [infer_def, inferTypeCore_mono (Nat.le_add_right F 2) hta,
          ok_bind, defeq_def, isDefEqCore_mono (Nat.le_add_right F 2) hb,
          ok_bind]
        simp only [↓reduceIte]
        rw [← instList_cons0]
        rfl
    · have hty : ∀ dom body bi, ty ≠ Expr.forallE dom body bi :=
        fun dom b bi hh => hpi ⟨dom, b, bi, hh⟩
      rw [inferSpine_ne_pi _ _ hty] at H
      unfold inferSpineWhnf at H
      obtain ⟨w₀, hw₀, H⟩ := bind_ok H
      refine ⟨F, ty.instantiateList acc, by rw [inferSpine_nil]; rfl, ?_⟩
      unfold inferStep
      rw [whnf_def]
      show (whnf mode env F d (ty.instantiateList acc) >>= _) = _
      rw [show whnf mode env F d (ty.instantiateList acc) = .ok w₀ from hw₀,
        ok_bind]
      cases w₀ with
      | forallE dom body bi =>
        dsimp only at H ⊢
        obtain ⟨ta, hta, H⟩ := bind_ok H
        obtain ⟨b, hb, H⟩ := bind_ok H
        rw [hta, ok_bind, hb, ok_bind]
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at H
          exact nomatch H
        | true =>
          simp only [↓reduceIte] at H ⊢
          rw [inferSpine_nil, instList_single] at H
          exact H
      | bvar i => exact nomatch H
      | fvar idx t => exact nomatch H
      | sort u => exact nomatch H
      | const nm us => exact nomatch H
      | app f' a' => exact nomatch H
      | lam t b mb => exact nomatch H
      | letE t v b => exact nomatch H
      | lit l => exact nomatch H
      | proj s i e => exact nomatch H
  | x :: xs', ty, acc, a, F, vres => by
    intro H
    rw [List.cons_append] at H
    by_cases hpi : ∃ dom body bi, ty = Expr.forallE dom body bi
    · obtain ⟨dom, body, bi, rfl⟩ := hpi
      rw [inferSpine_pi] at H
      unfold inferSpinePi at H
      obtain ⟨ta, hta, H⟩ := bind_ok H
      obtain ⟨b, hb, H⟩ := bind_ok H
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at H
        exact nomatch H
      | true =>
        simp only [↓reduceIte] at H
        obtain ⟨F₁, w, hw, hstep⟩ :=
          inferSpine_snoc xs' body (x :: acc) a F vres H
        refine ⟨max F F₁, w, ?_,
          inferStep_mono (Nat.le_max_right F F₁) hstep⟩
        rw [inferSpine_pi]
        unfold inferSpinePi
        rw [infer_def, inferTypeCore_mono (Nat.le_max_left F F₁) hta,
          ok_bind, defeq_def, isDefEqCore_mono (Nat.le_max_left F F₁) hb,
          ok_bind]
        simp only [↓reduceIte]
        exact inferSpine_mono (Nat.le_max_right F F₁) hw
    · have hty : ∀ dom body bi, ty ≠ Expr.forallE dom body bi :=
        fun dom b bi hh => hpi ⟨dom, b, bi, hh⟩
      rw [inferSpine_ne_pi _ _ hty] at H
      unfold inferSpineWhnf at H
      obtain ⟨w₀, hw₀, H⟩ := bind_ok H
      cases w₀ with
      | forallE dom body bi =>
        dsimp only at H
        obtain ⟨ta, hta, H⟩ := bind_ok H
        obtain ⟨b, hb, H⟩ := bind_ok H
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at H
          exact nomatch H
        | true =>
          simp only [↓reduceIte] at H
          obtain ⟨F₁, w, hw, hstep⟩ :=
            inferSpine_snoc xs' body [x] a F vres H
          refine ⟨max F F₁, w, ?_,
            inferStep_mono (Nat.le_max_right F F₁) hstep⟩
          rw [inferSpine_ne_pi _ _ hty]
          unfold inferSpineWhnf
          rw [whnf_def]
          show (whnf mode env (max F F₁) d (ty.instantiateList acc) >>= _) = _
          rw [whnf_mono (Nat.le_max_left F F₁) hw₀, ok_bind]
          dsimp only
          rw [infer_def, inferTypeCore_mono (Nat.le_max_left F F₁) hta,
            ok_bind, defeq_def,
            isDefEqCore_mono (Nat.le_max_left F F₁) hb, ok_bind]
          simp only [↓reduceIte]
          exact inferSpine_mono (Nat.le_max_right F F₁) hw
      | bvar i => exact nomatch H
      | fvar idx t => exact nomatch H
      | sort u => exact nomatch H
      | const nm us => exact nomatch H
      | app f' a' => exact nomatch H
      | lam t b mb => exact nomatch H
      | letE t v b => exact nomatch H
      | lit l => exact nomatch H
      | proj s i e => exact nomatch H

private theorem inferSpine_sound_rev {d : Nat} :
    ∀ (rxs : List Expr) (h th vres : Expr) (F₀ F : Nat),
      inferTypeCore mode env F₀ d h = .ok th →
      inferSpine (pureFns mode env F) d th [] rxs.reverse = .ok vres →
      ∃ F', inferTypeCore mode env F' d (Expr.mkAppN h rxs.reverse) = .ok vres
  | [], h, th, vres, F₀, F => by
    intro hh H
    rw [List.reverse_nil, inferSpine_nil, Expr.instantiateList_nil] at H
    injection H with h1
    subst h1
    exact ⟨F₀, hh⟩
  | r :: rrs, h, th, vres, F₀, F => by
    intro hh H
    rw [List.reverse_cons] at H
    obtain ⟨F₁, w, hw, hstep⟩ := inferSpine_snoc rrs.reverse th [] r F vres H
    obtain ⟨F₂, hP⟩ := inferSpine_sound_rev rrs h th w F₀ F₁ hh hw
    refine ⟨max F₂ F₁ + 1, ?_⟩
    rw [List.reverse_cons, Expr.mkAppN_append_one, inferTypeCore_succ,
      inferBody_app_pure, infer_def,
      inferTypeCore_mono (Nat.le_max_left F₂ F₁) hP, ok_bind]
    exact inferStep_mono (Nat.le_max_right F₂ F₁) hstep

/-- A successful inference-spine run over the head's inferred type is
reproduced by the chained inference on the whole application, at some
fuel. -/
theorem inferSpine_sound {d : Nat} (xs : List Expr) (h th vres : Expr)
    (F₀ F : Nat) (hh : inferTypeCore mode env F₀ d h = .ok th)
    (H : inferSpine (pureFns mode env F) d th [] xs = .ok vres) :
    ∃ F', inferTypeCore mode env F' d (Expr.mkAppN h xs) = .ok vres := by
  have hx : xs.reverse.reverse = xs := List.reverse_reverse xs
  have := inferSpine_sound_rev (d := d) xs.reverse h th vres F₀ F hh
    (by rw [hx]; exact H)
  rwa [hx] at this

/-- The bridge the interned walk uses. -/
theorem inferSpine_sound_body (d : Nat) (fx ax : Expr) (vres : Expr)
    (F : Nat)
    (H : ((fueledFns mode env).infer d (Expr.app fx ax).getAppFn >>=
        fun tf => inferSpine (fueledFns mode env) d tf []
          (Expr.app fx ax).getAppArgs).val F = .ok vres) :
    ∃ F', (inferBody mode (fueledFns mode env) env d (.app fx ax)).val F'
      = .ok vres := by
  rw [FueledM.atF_bind] at H
  obtain ⟨th, hth, H⟩ := bind_ok H
  rw [inferSpine_atF] at H
  obtain ⟨F', hP⟩ := inferSpine_sound (Expr.app fx ax).getAppArgs
    (Expr.app fx ax).getAppFn th vres F F hth H
  rw [Expr.mkAppN_getApp] at hP
  cases F' with
  | zero =>
    rw [inferTypeCore_zero] at hP
    exact nomatch hP
  | succ G =>
    refine ⟨G, ?_⟩
    rw [inferBody_atF, ← inferTypeCore_succ]
    exact hP

end InferSnoc

section InferIOSpine

/-! ## The io-grade spine (task #172 B4)

The gated twins of `inferStep`/`inferSpine` and their identification
with the io inference body over the io-grade view: what the cached
walks consume at the converted application clause.  Everything is
stated over the knot's io *slot* family (`inferTypeIO` /
`CoreFns.inferIO`); the sound composition carries the gate hypothesis
(`mode.betaGate = true`) because only there is the slot the io lane —
the io memo step splits on the gate before consulting any of this
(gate-off reuses the full-inference memo step outright).

The mirrors are written join-point-free (explicit `ite` of full
monadic branches rather than `unless` sugar); the shapes are
definitionally the body's, which is what keeps
`inferBodyIO_app_pure` an `rfl`. -/

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- The io continuation of the application clause: the licence wraps
the certificate, the computed type is the telescope step's, verbatim.
The licence reads the binder's annotation datum and nothing else — the
`mode.verifiedChecks` conjunct went with the licence ruling of
2026-09-06, which is also why `mode` has left this family's
signatures. -/
def inferStepIO (r : CoreFns m) (depth : Nat)
    (tf a : Expr) : m Expr := do
  match ← r.whnf depth tf with
  | .forallE ty body mt =>
    if mt.pw.isNever then
      pure (body.instantiate1 a)
    else do
      let ta ← r.inferIO depth a
      if ← r.defeq depth ta ty then pure (body.instantiate1 a)
      else throw (.invalid "application type mismatch")
  | _ => throw (.invalid "function expected")

/-- The io-grade spine mirror (the cached `inferSpineIOI`'s pure
twin): per-argument certificate skipped at a `.never` binder, on the
datum alone. -/
@[expose] def inferSpineIO (r : CoreFns m) (depth : Nat) :
    Expr → List Expr → List Expr → m Expr
  | ty, acc, [] => pure (ty.instantiateList acc)
  | ty, acc, a :: rest =>
    match ty with
    | .forallE dom body mt =>
      if mt.pw.isNever then
        inferSpineIO r depth body (a :: acc) rest
      else do
        let ta ← r.inferIO depth a
        if ← r.defeq depth ta (dom.instantiateList acc) then
          inferSpineIO r depth body (a :: acc) rest
        else throw (.invalid "application type mismatch")
    | ty => do
      match ← r.whnf depth (ty.instantiateList acc) with
      | .forallE dom body mt =>
        if mt.pw.isNever then
          inferSpineIO r depth body [a] rest
        else do
          let ta ← r.inferIO depth a
          if ← r.defeq depth ta dom then
            inferSpineIO r depth body [a] rest
          else throw (.invalid "application type mismatch")
      | _ => throw (.invalid "function expected")

/-- The syntactic-`∀` arm of `inferSpineIO`. -/
@[expose] def inferSpineIOPi (r : CoreFns m) (depth : Nat)
    (dom body : Expr) (mt : BinderMeta) (acc : List Expr) (a : Expr)
    (rest : List Expr) : m Expr :=
  if mt.pw.isNever then
    inferSpineIO r depth body (a :: acc) rest
  else do
    let ta ← r.inferIO depth a
    if ← r.defeq depth ta (dom.instantiateList acc) then
      inferSpineIO r depth body (a :: acc) rest
    else throw (.invalid "application type mismatch")

/-- The normalize-and-retry arm of `inferSpineIO`. -/
@[expose] def inferSpineIOWhnf (r : CoreFns m) (depth : Nat)
    (ty : Expr) (acc : List Expr) (a : Expr) (rest : List Expr) :
    m Expr := do
  match ← r.whnf depth (ty.instantiateList acc) with
  | .forallE dom body mt =>
    if mt.pw.isNever then
      inferSpineIO r depth body [a] rest
    else do
      let ta ← r.inferIO depth a
      if ← r.defeq depth ta dom then
        inferSpineIO r depth body [a] rest
      else throw (.invalid "application type mismatch")
  | _ => throw (.invalid "function expected")

theorem inferSpineIO_nil (r : CoreFns m) (depth : Nat)
    (ty : Expr) (acc : List Expr) :
    inferSpineIO r depth ty acc [] = pure (ty.instantiateList acc) := by
  rw [inferSpineIO]

theorem inferSpineIO_pi (r : CoreFns m) (depth : Nat)
    (dom body : Expr) (bi : BinderMeta) (acc : List Expr)
    (a : Expr) (rest : List Expr) :
    inferSpineIO r depth (.forallE dom body bi) acc (a :: rest)
      = inferSpineIOPi r depth dom body bi acc a rest := by
  rw [inferSpineIO, inferSpineIOPi]

theorem inferSpineIO_ne_pi (r : CoreFns m) (depth : Nat)
    {ty : Expr} (hty : ∀ dom body bi, ty ≠ .forallE dom body bi)
    (acc : List Expr) (a : Expr) (rest : List Expr) :
    inferSpineIO r depth ty acc (a :: rest)
      = inferSpineIOWhnf r depth ty acc a rest := by
  cases ty with
  | forallE dom body bi => exact absurd rfl (hty dom body bi)
  | _ => rw [inferSpineIO, inferSpineIOWhnf] <;>
      exact fun _ _ _ h => nomatch h

end InferIOSpine

section InferIOAtF

variable {mode : CheckMode} {env : Env}

theorem inferStepIO_atF (d : Nat) (tf a : Expr) (F : Nat) :
    (inferStepIO (fueledFns mode env) d tf a).val F
      = inferStepIO (pureFns mode env F) d tf a := by
  unfold inferStepIO
  atF_tac4

theorem inferSpineIO_atF (d : Nat) :
    ∀ (xs : List Expr) (ty : Expr) (acc : List Expr) (F : Nat),
      (inferSpineIO (fueledFns mode env) d ty acc xs).val F
        = inferSpineIO (pureFns mode env F) d ty acc xs
  | [], ty, acc, F => by rw [inferSpineIO_nil, inferSpineIO_nil]; rfl
  | a :: rest, ty, acc, F => by
    by_cases hpi : ∃ dom body bi, ty = Expr.forallE dom body bi
    · obtain ⟨dom, body, bi, rfl⟩ := hpi
      rw [inferSpineIO_pi, inferSpineIO_pi]
      unfold inferSpineIOPi
      rw [FueledM.atF_ite]
      refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)
      · exact inferSpineIO_atF d rest body (a :: acc) F
      · rw [FueledM.atF_bind]
        congr 1
        funext ta
        rw [FueledM.atF_bind]
        congr 1
        funext b
        cases b with
        | true =>
          show (inferSpineIO (fueledFns mode env) d body (a :: acc)
            rest).val F = _
          rw [inferSpineIO_atF d rest body (a :: acc) F]
          rfl
        | false => rfl
    · have hty : ∀ dom body bi, ty ≠ Expr.forallE dom body bi :=
        fun dom b bi hh => hpi ⟨dom, b, bi, hh⟩
      rw [inferSpineIO_ne_pi _ _ hty, inferSpineIO_ne_pi _ _ hty]
      unfold inferSpineIOWhnf
      rw [FueledM.atF_bind]
      congr 1
      funext w
      cases w with
      | forallE dom body bi =>
        dsimp only
        rw [FueledM.atF_ite]
        refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)
        · exact inferSpineIO_atF d rest body [a] F
        · rw [FueledM.atF_bind]
          congr 1
          funext ta
          rw [FueledM.atF_bind]
          congr 1
          funext b
          cases b with
          | true =>
            show (inferSpineIO (fueledFns mode env) d body [a]
              rest).val F = _
            rw [inferSpineIO_atF d rest body [a] F]
            rfl
          | false => rfl
      | _ => rfl

theorem inferSpineIO_mono {d : Nat} {xs acc : List Expr} {ty : Expr}
    {F F' : Nat} (hle : F ≤ F') {res : Expr}
    (h : inferSpineIO (pureFns mode env F) d ty acc xs = .ok res) :
    inferSpineIO (pureFns mode env F') d ty acc xs = .ok res := by
  rw [← inferSpineIO_atF] at h ⊢
  exact (inferSpineIO (fueledFns mode env) d ty acc xs).property hle h

theorem inferStepIO_mono {d : Nat} {tf a : Expr} {F F' : Nat}
    (hle : F ≤ F') {res : Expr}
    (h : inferStepIO (pureFns mode env F) d tf a = .ok res) :
    inferStepIO (pureFns mode env F') d tf a = .ok res := by
  rw [← inferStepIO_atF] at h ⊢
  exact (inferStepIO (fueledFns mode env) d tf a).property hle h

/-- The io inference body's app case over the io-grade view is one
io-slot inference followed by `inferStepIO` (stated at `CheckM`). -/
theorem inferBodyIO_app_pure (env : Env) (F depth : Nat) (f a : Expr) :
    inferBodyIO mode (CoreFns.ioView (pureFns mode env F)) env depth
        (.app f a)
      = (pureFns mode env F).inferIO depth f >>= fun tf =>
          inferStepIO (CoreFns.ioView (pureFns mode env F)) depth
            tf a := by rfl

/-- The io mirrors read only `whnf`, `inferIO` and `defeq`, none of
which the io-grade view touches, so the view is transparent to them. -/
theorem inferStepIO_ioView (F d : Nat) (tf a : Expr) :
    inferStepIO (CoreFns.ioView (pureFns mode env F)) d tf a
      = inferStepIO (pureFns mode env F) d tf a := by rfl

end InferIOAtF

section InferIOSnoc

variable {mode : CheckMode} {env : Env}

theorem inferSpineIO_snoc {d : Nat} :
    ∀ (xs : List Expr) (ty : Expr) (acc : List Expr) (a : Expr) (F : Nat)
      (vres : Expr),
      inferSpineIO (pureFns mode env F) d ty acc (xs ++ [a]) = .ok vres →
      ∃ F' w, inferSpineIO (pureFns mode env F') d ty acc xs = .ok w ∧
        inferStepIO (pureFns mode env F') d w a = .ok vres
  | [], ty, acc, a, F, vres => by
    intro H
    rw [List.nil_append] at H
    by_cases hpi : ∃ dom body bi, ty = Expr.forallE dom body bi
    · obtain ⟨dom, body, bi, rfl⟩ := hpi
      rw [inferSpineIO_pi] at H
      unfold inferSpineIOPi at H
      refine ⟨F + 2, _, by rw [inferSpineIO_nil]; rfl, ?_⟩
      unfold inferStepIO
      rw [instList_forallE, whnf_def, whnf_forallE, ok_bind]
      dsimp only
      by_cases hg2 : bi.pw.isNever = true
      · simp only [hg2, ↓reduceIte] at H ⊢
        rw [inferSpineIO_nil] at H
        injection H with h1
        subst h1
        rw [← instList_cons0]
        rfl
      · simp only [hg2, Bool.false_eq_true, ↓reduceIte] at H ⊢
        obtain ⟨ta, hta, H⟩ := bind_ok H
        obtain ⟨b, hb, H⟩ := bind_ok H
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at H
          exact nomatch H
        | true =>
          simp only [↓reduceIte] at H
          rw [inferSpineIO_nil] at H
          injection H with h1
          subst h1
          rw [show (pureFns mode env (F + 2)).inferIO d a
              = inferTypeIO mode env (F + 2) d a from rfl,
            inferTypeIO_mono (Nat.le_add_right F 2) hta, ok_bind]
          rw [show (pureFns mode env (F + 2)).defeq d ta
                (dom.instantiateList acc)
              = isDefEqCore mode env (F + 2) d ta
                (dom.instantiateList acc) from rfl,
            isDefEqCore_mono (Nat.le_add_right F 2) hb, ok_bind]
          simp only [↓reduceIte]
          rw [← instList_cons0]
          rfl
    · have hty : ∀ dom body bi, ty ≠ Expr.forallE dom body bi :=
        fun dom b bi hh => hpi ⟨dom, b, bi, hh⟩
      rw [inferSpineIO_ne_pi _ _ hty] at H
      unfold inferSpineIOWhnf at H
      obtain ⟨w₀, hw₀, H⟩ := bind_ok H
      refine ⟨F, ty.instantiateList acc, by rw [inferSpineIO_nil]; rfl, ?_⟩
      unfold inferStepIO
      rw [whnf_def]
      show (whnf mode env F d (ty.instantiateList acc) >>= _) = _
      rw [show whnf mode env F d (ty.instantiateList acc) = .ok w₀ from hw₀,
        ok_bind]
      cases w₀ with
      | forallE dom body bi =>
        dsimp only at H ⊢
        by_cases hg2 : bi.pw.isNever = true
        · simp only [hg2, ↓reduceIte] at H ⊢
          rw [inferSpineIO_nil, instList_single] at H
          exact H
        · simp only [hg2, Bool.false_eq_true, ↓reduceIte] at H ⊢
          obtain ⟨ta, hta, H⟩ := bind_ok H
          obtain ⟨b, hb, H⟩ := bind_ok H
          rw [hta, ok_bind, hb, ok_bind]
          cases b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at H
            exact nomatch H
          | true =>
            simp only [↓reduceIte] at H ⊢
            rw [inferSpineIO_nil, instList_single] at H
            exact H
      | bvar i => exact nomatch H
      | fvar idx t => exact nomatch H
      | sort u => exact nomatch H
      | const nm us => exact nomatch H
      | app f' a' => exact nomatch H
      | lam t b mb => exact nomatch H
      | letE t v b => exact nomatch H
      | lit l => exact nomatch H
      | proj s i e => exact nomatch H
  | x :: xs', ty, acc, a, F, vres => by
    intro H
    rw [List.cons_append] at H
    by_cases hpi : ∃ dom body bi, ty = Expr.forallE dom body bi
    · obtain ⟨dom, body, bi, rfl⟩ := hpi
      rw [inferSpineIO_pi] at H
      unfold inferSpineIOPi at H
      by_cases hg2 : bi.pw.isNever = true
      · simp only [hg2, ↓reduceIte] at H
        obtain ⟨F₁, w, hw, hstep⟩ :=
          inferSpineIO_snoc xs' body (x :: acc) a F vres H
        refine ⟨F₁, w, ?_, hstep⟩
        rw [inferSpineIO_pi]
        unfold inferSpineIOPi
        simp only [hg2, ↓reduceIte]
        exact hw
      · simp only [hg2, Bool.false_eq_true, ↓reduceIte] at H
        obtain ⟨ta, hta, H⟩ := bind_ok H
        obtain ⟨b, hb, H⟩ := bind_ok H
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at H
          exact nomatch H
        | true =>
          simp only [↓reduceIte] at H
          obtain ⟨F₁, w, hw, hstep⟩ :=
            inferSpineIO_snoc xs' body (x :: acc) a F vres H
          refine ⟨max F F₁, w, ?_,
            inferStepIO_mono (Nat.le_max_right F F₁) hstep⟩
          rw [inferSpineIO_pi]
          unfold inferSpineIOPi
          simp only [hg2, Bool.false_eq_true, ↓reduceIte]
          rw [show (pureFns mode env (max F F₁)).inferIO d x
              = inferTypeIO mode env (max F F₁) d x from rfl,
            inferTypeIO_mono (Nat.le_max_left F F₁) hta, ok_bind]
          rw [show (pureFns mode env (max F F₁)).defeq d ta
                (dom.instantiateList acc)
              = isDefEqCore mode env (max F F₁) d ta
                (dom.instantiateList acc) from rfl,
            isDefEqCore_mono (Nat.le_max_left F F₁) hb, ok_bind]
          simp only [↓reduceIte]
          exact inferSpineIO_mono (Nat.le_max_right F F₁) hw
    · have hty : ∀ dom body bi, ty ≠ Expr.forallE dom body bi :=
        fun dom b bi hh => hpi ⟨dom, b, bi, hh⟩
      rw [inferSpineIO_ne_pi _ _ hty] at H
      unfold inferSpineIOWhnf at H
      obtain ⟨w₀, hw₀, H⟩ := bind_ok H
      cases w₀ with
      | forallE dom body bi =>
        dsimp only at H
        by_cases hg2 : bi.pw.isNever = true
        · simp only [hg2, ↓reduceIte] at H
          obtain ⟨F₁, w, hw, hstep⟩ :=
            inferSpineIO_snoc xs' body [x] a F vres H
          refine ⟨max F F₁, w, ?_,
            inferStepIO_mono (Nat.le_max_right F F₁) hstep⟩
          rw [inferSpineIO_ne_pi _ _ hty]
          unfold inferSpineIOWhnf
          rw [whnf_def]
          show (whnf mode env (max F F₁) d (ty.instantiateList acc) >>= _) = _
          rw [whnf_mono (Nat.le_max_left F F₁) hw₀, ok_bind]
          dsimp only
          simp only [hg2, ↓reduceIte]
          exact inferSpineIO_mono (Nat.le_max_right F F₁) hw
        · simp only [hg2, Bool.false_eq_true, ↓reduceIte] at H
          obtain ⟨ta, hta, H⟩ := bind_ok H
          obtain ⟨b, hb, H⟩ := bind_ok H
          cases b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at H
            exact nomatch H
          | true =>
            simp only [↓reduceIte] at H
            obtain ⟨F₁, w, hw, hstep⟩ :=
              inferSpineIO_snoc xs' body [x] a F vres H
            refine ⟨max F F₁, w, ?_,
              inferStepIO_mono (Nat.le_max_right F F₁) hstep⟩
            rw [inferSpineIO_ne_pi _ _ hty]
            unfold inferSpineIOWhnf
            rw [whnf_def]
            show (whnf mode env (max F F₁) d (ty.instantiateList acc) >>= _) = _
            rw [whnf_mono (Nat.le_max_left F F₁) hw₀, ok_bind]
            dsimp only
            simp only [hg2, Bool.false_eq_true, ↓reduceIte]
            rw [show (pureFns mode env (max F F₁)).inferIO d x
                = inferTypeIO mode env (max F F₁) d x from rfl,
              inferTypeIO_mono (Nat.le_max_left F F₁) hta, ok_bind]
            rw [show (pureFns mode env (max F F₁)).defeq d ta dom
                = isDefEqCore mode env (max F F₁) d ta dom from rfl,
              isDefEqCore_mono (Nat.le_max_left F F₁) hb, ok_bind]
            simp only [↓reduceIte]
            exact inferSpineIO_mono (Nat.le_max_right F F₁) hw
      | bvar i => exact nomatch H
      | fvar idx t => exact nomatch H
      | sort u => exact nomatch H
      | const nm us => exact nomatch H
      | app f' a' => exact nomatch H
      | lam t b mb => exact nomatch H
      | letE t v b => exact nomatch H
      | lit l => exact nomatch H
      | proj s i e => exact nomatch H

private theorem inferSpineIO_sound_rev (hgb : mode.betaGate = true)
    {d : Nat} :
    ∀ (rxs : List Expr) (h th vres : Expr) (F₀ F : Nat),
      inferTypeIO mode env F₀ d h = .ok th →
      inferSpineIO (pureFns mode env F) d th [] rxs.reverse
        = .ok vres →
      ∃ F', inferTypeIO mode env F' d (Expr.mkAppN h rxs.reverse)
        = .ok vres
  | [], h, th, vres, F₀, F => by
    intro hh H
    rw [List.reverse_nil, inferSpineIO_nil, Expr.instantiateList_nil] at H
    injection H with h1
    subst h1
    exact ⟨F₀, hh⟩
  | r :: rrs, h, th, vres, F₀, F => by
    intro hh H
    rw [List.reverse_cons] at H
    obtain ⟨F₁, w, hw, hstep⟩ :=
      inferSpineIO_snoc rrs.reverse th [] r F vres H
    obtain ⟨F₂, hP⟩ := inferSpineIO_sound_rev hgb rrs h th w F₀ F₁ hh hw
    refine ⟨max F₂ F₁ + 1, ?_⟩
    rw [List.reverse_cons, Expr.mkAppN_append_one, inferTypeIO_succ,
      hgb, if_pos rfl, inferBodyIO_app_pure]
    rw [show (pureFns mode env (max F₂ F₁)).inferIO d
        (Expr.mkAppN h rrs.reverse)
      = inferTypeIO mode env (max F₂ F₁) d (Expr.mkAppN h rrs.reverse)
      from rfl]
    rw [inferTypeIO_mono (Nat.le_max_left F₂ F₁) hP, ok_bind]
    rw [inferStepIO_ioView]
    exact inferStepIO_mono (Nat.le_max_right F₂ F₁) hstep

/-- A successful io-spine run over the head's io-inferred type is
reproduced by the chained io slot on the whole application, at some
fuel — **at the gated mode**, where the slot is the io lane (at a
gate-off mode the slot is full inference and a gated spine run proves
nothing about it; the io memo step never consults this lemma
there). -/
theorem inferSpineIO_sound (hgb : mode.betaGate = true) {d : Nat}
    (xs : List Expr) (h th vres : Expr) (F₀ F : Nat)
    (hh : inferTypeIO mode env F₀ d h = .ok th)
    (H : inferSpineIO (pureFns mode env F) d th [] xs = .ok vres) :
    ∃ F', inferTypeIO mode env F' d (Expr.mkAppN h xs) = .ok vres := by
  have hx : xs.reverse.reverse = xs := List.reverse_reverse xs
  have := inferSpineIO_sound_rev hgb (d := d) xs.reverse h th vres F₀ F hh
    (by rw [hx]; exact H)
  rwa [hx] at this

/-- The bridge the cached io walk uses. -/
theorem inferSpineIO_sound_body (hgb : mode.betaGate = true) (d : Nat)
    (fx ax : Expr) (vres : Expr) (F : Nat)
    (H : ((fueledFns mode env).inferIO d (Expr.app fx ax).getAppFn >>=
        fun tf => inferSpineIO (fueledFns mode env) d tf []
          (Expr.app fx ax).getAppArgs).val F = .ok vres) :
    ∃ F', (inferBodyIO mode (CoreFns.ioView (fueledFns mode env)) env d
      (.app fx ax)).val F' = .ok vres := by
  rw [FueledM.atF_bind] at H
  obtain ⟨th, hth, H⟩ := bind_ok H
  rw [inferSpineIO_atF] at H
  obtain ⟨F', hP⟩ := inferSpineIO_sound hgb (Expr.app fx ax).getAppArgs
    (Expr.app fx ax).getAppFn th vres F F hth H
  rw [Expr.mkAppN_getApp] at hP
  cases F' with
  | zero =>
    rw [inferTypeIO_zero] at hP
    simp [throw, throwThe, MonadExceptOf.throw] at hP
  | succ G =>
    refine ⟨G, ?_⟩
    rw [inferBodyIO_atF]
    rw [inferTypeIO_succ, hgb, if_pos rfl] at hP
    exact hP

end InferIOSnoc


end ConLeche
