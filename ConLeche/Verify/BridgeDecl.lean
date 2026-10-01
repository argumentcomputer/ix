module

public import ConLeche.Verify.Fueled
public import ConLeche.Kernel.Checker

public section

/-!
# The cache-refinement bridge, part C: the declaration checker

The declaration checker is monad-polymorphic over a `CheckerOps`
record, so the same pair-monad game applies: `bridgeRel` relates
monotone fueled families to plain executable computations
("success on the executable side is reproduced at some fuel"), the
fueled/cached operation records are related by part B's entry-point
bridges, and the projection batteries push the pairing through every
declaration-checker function.  The punchline: a successful
`checkDeclsPure mode (wfOpsM mode)` run is reproduced by `checkDeclsPure mode (fueledOps mode F)`
for some fuel `F`.

**The file split (task #184, the build-time audit).**  This module is the
*consumed* half: the operation records (`bridgeRel`, `OpsRel`, `pairOps`,
`fueledOpsM`, `wfOpsM` and the `wfOpsM_*` equations) and the `atF` battery
— for every `check*` function, `(… (fueledOpsM …) …).val F = … (fueledOps …
F) …`, which is what `Verify/BridgeWfImp` and the cached lane's
`Verify/Cached/Bridge*` rewrite by.  The pair-monad projection battery
(`X_fst_dproj` / `X_snd_dproj`, theorems that nothing outside their own file
consumes) moved to `ConLeche/Verify/BridgeDeclPair.lean`, which the `ConLeche`
umbrella imports so that it stays built and gated.

Why: the two batteries share nothing but the declarations above, and together
they were the largest node on the build's critical path (57 s of 203 s).
Apart, the projection battery elaborates in parallel and only the consumed
half stays on the chain.  No statement changed and the module name did not
move, so the frozen proof-dependency pin (`tests/proofdeps.sh`) is untouched.
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace ConLeche

variable {mode : CheckMode}
variable {pins : List NatOpPinSet}

/-- Success on the executable side is reproduced at some fuel. -/
def bridgeRel : MonadRel FueledM CheckM where
  R p c := ∀ v, c = .ok v → ∃ F, p.val F = .ok v
  pure_rel a := fun v h => ⟨0, by cases h; rfl⟩
  bind_rel {α β x₁ x₂ f₁ f₂} hx hf := by
    intro v h
    simp only [Bind.bind] at h
    cases hx2 : x₂ with
    | error e => rw [hx2] at h; exact nomatch h
    | ok a =>
      rw [hx2] at h
      dsimp only [Except.bind] at h
      obtain ⟨F₁, h1⟩ := hx a hx2
      obtain ⟨F₂, h2⟩ := hf a v h
      refine ⟨max F₁ F₂, ?_⟩
      rw [FueledM.atF_bind]
      simp only [Bind.bind]
      rw [x₁.property (Nat.le_max_left F₁ F₂) h1]
      dsimp only [Except.bind]
      exact (f₁ a).property (Nat.le_max_right F₁ F₂) h2
  throw_rel e := fun v h => nomatch h

/-- Componentwise relatedness of two operation records. -/
def OpsRel {M₁ M₂ : Type → Type} [Monad M₁] [Monad M₂]
    [MonadExceptOf CheckError M₁] [MonadExceptOf CheckError M₂]
    (rel : MonadRel M₁ M₂) (o₁ : CheckerOps M₁) (o₂ : CheckerOps M₂) :
    Prop :=
  (∀ env d e, rel.R (o₁.annotate env d e) (o₂.annotate env d e)) ∧
  (∀ env d e, rel.R (o₁.inferType env d e) (o₂.inferType env d e)) ∧
  (∀ env d a b, rel.R (o₁.isDefEq env d a b) (o₂.isDefEq env d a b)) ∧
  (∀ env d e, rel.R (o₁.ensureSort env d e) (o₂.ensureSort env d e)) ∧
  (∀ env d e, rel.R (o₁.whnf env d e) (o₂.whnf env d e)) ∧
  (∀ (x₁ : M₁ Bool) (x₂ : M₂ Bool) (k₁ : Option CheckError → M₁ Unit)
      (k₂ : Option CheckError → M₂ Unit),
    rel.R x₁ x₂ → (∀ r, rel.R (k₁ r) (k₂ r)) →
    rel.R (o₁.orElse x₁ k₁) (o₂.orElse x₂ k₂))

/-- The paired operation record. -/
def pairOps {M₁ M₂ : Type → Type} [Monad M₁] [Monad M₂]
    [MonadExceptOf CheckError M₁] [MonadExceptOf CheckError M₂]
    {rel : MonadRel M₁ M₂} (o₁ : CheckerOps M₁) (o₂ : CheckerOps M₂)
    (h : OpsRel rel o₁ o₂) : CheckerOps (PairM rel) where
  annotate env d e := ⟨(o₁.annotate env d e, o₂.annotate env d e), h.1 env d e⟩
  inferType env d e :=
    ⟨(o₁.inferType env d e, o₂.inferType env d e), h.2.1 env d e⟩
  isDefEq env d a b :=
    ⟨(o₁.isDefEq env d a b, o₂.isDefEq env d a b), h.2.2.1 env d a b⟩
  ensureSort env d e :=
    ⟨(o₁.ensureSort env d e, o₂.ensureSort env d e), h.2.2.2.1 env d e⟩
  whnf env d e := ⟨(o₁.whnf env d e, o₂.whnf env d e), h.2.2.2.2.1 env d e⟩
  orElse x k :=
    ⟨(o₁.orElse x.val.1 (fun r => (k r).val.1),
      o₂.orElse x.val.2 (fun r => (k r).val.2)),
      h.2.2.2.2.2 _ _ _ _ x.property (fun r => (k r).property)⟩

/-- The fueled operations as monotone families. -/
@[expose] def fueledOpsM (mode : CheckMode) : CheckerOps FueledM where
  annotate env d e :=
    ⟨fun F => annotateCore mode env F d e, fun hle h => annotateCore_mono hle h⟩
  inferType env d e :=
    ⟨fun F => inferTypeCore mode env F d e, fun hle h => inferTypeCore_mono hle h⟩
  isDefEq env d a b :=
    ⟨fun F => isDefEqCore mode env F d a b, fun hle h => isDefEqCore_mono hle h⟩
  ensureSort env d e :=
    ⟨fun F => ensureSortCore mode env F d e, fun hle h => ensureSortCore_mono hle h⟩
  whnf env d e :=
    ⟨fun F => whnf mode env F d e, fun hle h => whnf_mono hle h⟩
  -- the variant-fallback combinator (task #273): monotone because the
  -- result is `Unit` — an attempt that errs at one fuel and matches at
  -- a larger one changes the branch, not the success; the continuation
  -- is handed `none` (see `CheckerOps.orElse`)
  orElse x k :=
    ⟨fun F => match x.val F with
      | .ok true => pure ()
      | _ => (k none).val F, by
      intro F F' v hle h
      dsimp only at h ⊢
      cases hx : x.val F with
      | ok b =>
        rw [hx] at h
        rw [x.property hle hx]
        cases b with
        | true => exact h
        | false => exact (k none).property hle h
      | error e =>
        rw [hx] at h
        cases hx' : x.val F' with
        | ok b =>
          cases b with
          | true => cases v; rfl
          | false => exact (k none).property hle h
        | error e' => exact (k none).property hle h⟩

/-- `fueledOpsM`'s combinator at a fuel, by definition. -/
@[simp] theorem fueledOpsM_orElse_atF (x : FueledM Bool)
    (k : Option CheckError → FueledM Unit) (F : Nat) :
    ((fueledOpsM mode).orElse x k).val F =
      match x.val F with
      | .ok true => pure ()
      | _ => (k none).val F := rfl

/-- `fueledOps`' combinator, by definition (restated here for the
`atF` battery; `ConLeche/Verify/Extend/Inversions.lean` has the same
statement for its consumers). -/
theorem fueledOps_orElse' (F : Nat) (x : CheckM Bool)
    (k : Option CheckError → CheckM Unit) :
    (fueledOps mode F).orElse x k =
      match x with | .ok true => pure () | _ => k none := rfl

/-! ## The WF-conditional fueled comparand

Part B's entry-point bridges hold only over well-formed environments
(`EnvWF` — the depth-free memo cache is justified by depth invariance,
which needs it), and there is **no runtime check** for `EnvWF`: the
executable always runs the memoized knot.  To keep the pair-monad
battery unconditional, the fueled comparand is chosen per environment:
over a well-formed environment it is the pure fueled family, otherwise
the constant family that merely repeats the cached run (trivially
related).  The battery then yields, for *every* environment: a
successful cached `checkDecl` run is reproduced by its `wfOpsM mode`
instantiation at some fuel (`checkDecl_wfOpsM_bridge`).
`ConLeche/Verify/BridgeWfImp.lean` turns `wfOpsM mode` runs into pure
`fueledOps` runs by threading `EnvWF` through the declaration checker's
intermediate environments, using the `wfOpsM_*` equalities below. -/

open Classical in
/-- The fueled families over well-formed environments *and* well-scoped
arguments (both are hypotheses of part B's entry-point bridges — the
executable's memo operations carry no runtime check for either); the
constant `.internal` error (a trivially monotone family) otherwise.

Task #172: the `otherwise` branch used to be the interned executable's
own run, which is what made the entry-point bridges unconditional in
the environment.  With that executable deleted the branch has no
consumer — every surviving use of `wfOpsM` goes through the `if_pos`
equations below — so it is a constant. -/
noncomputable def wfOpsM (mode : CheckMode) : CheckerOps FueledM where
  annotate env d e :=
    if EnvWF env ∧ e.wscopedB d = true then
      ⟨fun F => annotateCore mode env F d e, fun hle h => annotateCore_mono hle h⟩
    else ⟨fun _ => throw (.internal "wfOpsM: precondition failed"),
      fun _ h => h⟩
  inferType env d e :=
    if EnvWF env ∧ e.wscopedB d = true then
      ⟨fun F => inferTypeCore mode env F d e,
        fun hle h => inferTypeCore_mono hle h⟩
    else ⟨fun _ => throw (.internal "wfOpsM: precondition failed"),
      fun _ h => h⟩
  isDefEq env d a b :=
    if EnvWF env ∧ a.wscopedB d = true ∧ b.wscopedB d = true then
      ⟨fun F => isDefEqCore mode env F d a b, fun hle h => isDefEqCore_mono hle h⟩
    else ⟨fun _ => throw (.internal "wfOpsM: precondition failed"),
      fun _ h => h⟩
  ensureSort env d e :=
    if EnvWF env ∧ e.wscopedB d = true then
      ⟨fun F => ensureSortCore mode env F d e,
        fun hle h => ensureSortCore_mono hle h⟩
    else ⟨fun _ => throw (.internal "wfOpsM: precondition failed"),
      fun _ h => h⟩
  whnf env d e :=
    if EnvWF env ∧ e.wscopedB d = true then
      ⟨fun F => whnf mode env F d e, fun hle h => whnf_mono hle h⟩
    else ⟨fun _ => throw (.internal "wfOpsM: precondition failed"),
      fun _ h => h⟩
  -- no precondition: the combinator runs no core body of its own
  orElse x k := (fueledOpsM mode).orElse x k

/-- Over a well-formed environment and a well-scoped argument `wfOpsM mode`
*is* the fueled record. -/
theorem wfOpsM_annotate {env : Env} (henv : EnvWF env) {d : Nat} {e : Expr}
    (hg : e.wscopedB d = true) :
    (wfOpsM mode).annotate env d e = (fueledOpsM mode).annotate env d e := by
  dsimp only [wfOpsM, fueledOpsM]
  exact if_pos ⟨henv, hg⟩

theorem wfOpsM_inferType {env : Env} (henv : EnvWF env) {d : Nat} {e : Expr}
    (hg : e.wscopedB d = true) :
    (wfOpsM mode).inferType env d e = (fueledOpsM mode).inferType env d e := by
  dsimp only [wfOpsM, fueledOpsM]
  exact if_pos ⟨henv, hg⟩

theorem wfOpsM_isDefEq {env : Env} (henv : EnvWF env) {d : Nat} {a b : Expr}
    (hga : a.wscopedB d = true) (hgb : b.wscopedB d = true) :
    (wfOpsM mode).isDefEq env d a b = (fueledOpsM mode).isDefEq env d a b := by
  dsimp only [wfOpsM, fueledOpsM]
  exact if_pos ⟨henv, hga, hgb⟩

theorem wfOpsM_ensureSort {env : Env} (henv : EnvWF env) {d : Nat} {e : Expr}
    (hg : e.wscopedB d = true) :
    (wfOpsM mode).ensureSort env d e = (fueledOpsM mode).ensureSort env d e := by
  dsimp only [wfOpsM, fueledOpsM]
  exact if_pos ⟨henv, hg⟩

theorem wfOpsM_whnf {env : Env} (henv : EnvWF env) {d : Nat} {e : Expr}
    (hg : e.wscopedB d = true) :
    (wfOpsM mode).whnf env d e = (fueledOpsM mode).whnf env d e := by
  dsimp only [wfOpsM, fueledOpsM]
  exact if_pos ⟨henv, hg⟩

theorem wfOpsM_orElse (x : FueledM Bool)
    (k : Option CheckError → FueledM Unit) :
    (wfOpsM mode).orElse x k = (fueledOpsM mode).orElse x k := by
  dsimp only [wfOpsM]

/-! ## The `atF` battery: fueled-family runs are fueled-ops runs -/

theorem foldlM_atF {α β : Type} (g : β → α → FueledM β) (F : Nat) :
    ∀ (l : List α) (init : β),
      (l.foldlM g init).val F =
        l.foldlM (fun b a => (g b a).val F) init
  | [], init => rfl
  | a :: l, init => by
    show ((g init a >>= fun b => l.foldlM g b : FueledM β)).val F = _
    rw [FueledM.atF_bind]
    show _ = (g init a).val F >>= fun b =>
      l.foldlM (fun b a => (g b a).val F) b
    congr 1
    funext b
    exact foldlM_atF g F l b

macro "datF_step_alt" : tactic =>
  `(tactic| first
    | (rw [liftFueled_atF])
    | (rw [foldlM_atF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only []))


macro "datF_tac" : tactic =>
  `(tactic| repeat' datF_step_alt)

theorem checkConstantVal_datF (env : Env) (cv : ConstantVal) (F : Nat) :
    (checkConstantVal (fueledOpsM mode) env cv).val F =
      checkConstantVal (fueledOps mode F) env cv := by
  unfold checkConstantVal
  datF_tac

theorem checkProjLookups_datF (env' : Env) (T ctorName : Name) (lps : List Name) (nP nF i : Nat) (F : Nat) :
    (checkProjLookups env' T ctorName lps nP nF i : FueledM _).val F =
      (checkProjLookups env' T ctorName lps nP nF i : CheckM _) := by
  unfold checkProjLookups
  datF_tac

theorem checkProjTy_datF (env' : Env) (T ctorName : Name) (lps : List Name) (mty : Expr) (nP nF : Nat) (F : Nat) :
    (checkProjTy env' T ctorName lps mty nP nF : FueledM _).val F =
      (checkProjTy env' T ctorName lps mty nP nF : CheckM _) := by
  unfold checkProjTy
  datF_tac

theorem checkProjShape_datF (pty cty : Expr) (nP nF : Nat) (F : Nat) :
    (checkProjShape pty cty nP nF : FueledM _).val F =
      checkProjShape (m := CheckM) pty cty nP nF := by
  unfold checkProjShape
  datF_tac

theorem fueledOpsM_isDefEq_atF (env : Env) (d : Nat) (a b : Expr)
    (F : Nat) :
    ((fueledOpsM mode).isDefEq env d a b).val F =
      (fueledOps mode F).isDefEq env d a b := by rfl

theorem unwrapOr_atF {α : Type} (o : Option α) (e : CheckError)
    (F : Nat) :
    (unwrapOr o e : FueledM α).val F = (unwrapOr o e : CheckM α) := by
  cases o <;> rfl

theorem checkDefEqList_datF (env : Env) (depth F : Nat) :
    ∀ (as bs : List Expr),
      (checkDefEqList (fueledOpsM mode) env depth as bs).val F =
      checkDefEqList (fueledOps mode F) env depth as bs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    unfold checkDefEqList
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
      fueledOpsM_isDefEq_atF, checkDefEqList_datF env depth F as bs]

theorem fueledOpsM_inferType_atF (env : Env) (d : Nat) (a : Expr)
    (F : Nat) :
    ((fueledOpsM mode).inferType env d a).val F =
      (fueledOps mode F).inferType env d a := by rfl

theorem checkTypedList_datF (env : Env) (depth F : Nat) :
    ∀ (as bs : List Expr),
      (checkTypedList (fueledOpsM mode) env depth as bs).val F =
      checkTypedList (fueledOps mode F) env depth as bs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    unfold checkTypedList
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
      FueledM.atF_ite, fueledOpsM_isDefEq_atF, fueledOpsM_inferType_atF,
      checkTypedList_datF env depth F as bs]

theorem fueledOpsM_annotate_atF' (env : Env) (d : Nat) (a : Expr)
    (F : Nat) :
    ((fueledOpsM mode).annotate env d a).val F =
      (fueledOps mode F).annotate env d a := by rfl

theorem checkAnnotList_datF (env : Env) (depth F : Nat) :
    ∀ (as : List Expr),
      (checkAnnotList (fueledOpsM mode) env depth as).val F =
      checkAnnotList (fueledOps mode F) env depth as
  | [] => rfl
  | a :: as => by
    unfold checkAnnotList
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
      FueledM.atF_ite, fueledOpsM_annotate_atF',
      checkAnnotList_datF env depth F as]

theorem checkIotaSidesTy_datF (envSelf : Env) (depth : Nat)
    (alphaS lhsS rhsS : Expr) (ℓA : Level) (cvName : Name) (F : Nat) :
    (checkIotaSidesTy mode (fueledOpsM mode) envSelf depth alphaS lhsS rhsS
      ℓA cvName).val F =
    checkIotaSidesTy mode (fueledOps mode F) envSelf depth alphaS lhsS rhsS
      ℓA cvName := by
  unfold checkIotaSidesTy
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
    FueledM.atF_ite, fueledOpsM_isDefEq_atF, fueledOpsM_inferType_atF]

macro "datF_stepPI_alt" : tactic =>
  `(tactic| first
    | (rw [checkIotaSidesTy_datF])
    | (rw [unwrapOr_atF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only []))


theorem checkProjIota_datF (env' envSelf : Env) (T ctorName : Name) (lps : List Name) (cvj : ConstantVal) (nP nF i : Nat) (F : Nat) :
    (checkProjIota mode (fueledOpsM mode) env' envSelf T ctorName lps cvj nP nF i).val F =
      checkProjIota mode (fueledOps mode F) env' envSelf T ctorName lps cvj nP nF i := by
  unfold checkProjIota
  repeat' datF_stepPI_alt

theorem checkIotaThm_datF (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) (cvj : ConstantVal)
    (cnP cnF : Nat) (rhsA : Expr) (F : Nat) :
    (checkIotaThm mode (fueledOpsM mode) env' envSelf f cvName lps tyA
      mI rP j r cvj cnP cnF rhsA).val F =
    checkIotaThm mode (fueledOps mode F) env' envSelf f cvName lps tyA mI rP
      j r cvj cnP cnF rhsA := by
  unfold checkIotaThm
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    fueledOpsM_isDefEq_atF, fueledOpsM_inferType_atF, unwrapOr_atF,
    checkDefEqList_datF, checkTypedList_datF, checkIotaSidesTy_datF]

theorem checkIotaThmN_datF (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) (cvj : ConstantVal)
    (cnP cnF : Nat) (rhsA : Expr) (F : Nat) :
    (checkIotaThmN mode (fueledOpsM mode) env' envSelf f cvName lps tyA
      mI rP j r cvj cnP cnF rhsA).val F =
    checkIotaThmN mode (fueledOps mode F) env' envSelf f cvName lps tyA mI rP
      j r cvj cnP cnF rhsA := by
  unfold checkIotaThmN
  split
  · rfl
  · simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
      fueledOpsM_isDefEq_atF, fueledOpsM_inferType_atF, unwrapOr_atF,
      checkDefEqList_datF, checkTypedList_datF, checkAnnotList_datF,
      checkIotaSidesTy_datF]

set_option maxHeartbeats 12800000 in
theorem checkIotaRule_datF (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) (F : Nat) :
    (checkIotaRule mode (fueledOpsM mode) env' envSelf f cvName lps tyA
      mI rP j r).val F =
    checkIotaRule mode (fueledOps mode F) env' envSelf f cvName lps tyA
      mI rP j r := by
  unfold checkIotaRule
  datF_tac
  all_goals first
  | rw [checkIotaThm_datF]
  | rw [checkIotaThmN_datF]

theorem checkIotaRules_datF (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP : Nat) (F : Nat) :
    ∀ (j : Nat) (rules : List RecRule),
      (checkIotaRules mode (fueledOpsM mode) env' envSelf f cvName lps tyA
        mI rP j rules).val F =
      checkIotaRules mode (fueledOps mode F) env' envSelf f cvName lps tyA
        mI rP j rules
  | _, [] => rfl
  | j, r :: rest => by
    show ((do
        let r' ← checkIotaRule mode (fueledOpsM mode) env' envSelf f cvName lps tyA
          mI rP j r
        let rest' ← checkIotaRules mode (fueledOpsM mode) env' envSelf f cvName lps
          tyA mI rP (j + 1) rest
        pure (r' :: rest') : FueledM _)).val F = (do
        let r' ← checkIotaRule mode (fueledOps mode F) env' envSelf f cvName lps
          tyA mI rP j r
        let rest' ← checkIotaRules mode (fueledOps mode F) env' envSelf f cvName
          lps tyA mI rP (j + 1) rest
        pure (r' :: rest'))
    rw [FueledM.atF_bind, checkIotaRule_datF]
    congr 1
    funext r'
    rw [FueledM.atF_bind, checkIotaRules_datF env' envSelf f cvName lps
      tyA mI rP F (j + 1) rest]
    rfl

macro "datF_step2_alt" : tactic =>
  `(tactic| first
    | (rw [liftFueled_atF])
    | (rw [foldlM_atF])
    | (rw [checkConstantVal_datF])
    | (rw [checkProjLookups_datF])
    | (rw [checkProjTy_datF])
    | (rw [checkProjShape_datF])
    | (rw [checkProjIota_datF])
    | (rw [checkProjRule_datF])
    | (rw [checkDefEqList_datF])
    | (rw [checkIndMember_datF])
    | (rw [checkIotaRule_datF])
    | (rw [checkIotaRules_datF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only []))

macro "datF_step2" : tactic => `(tactic| repeat datF_step2_alt)

macro "datF_tac2" : tactic =>
  `(tactic| repeat' datF_step2_alt)

theorem checkProjRule_datF (env' : Env) (pty : Expr) (cvj : ConstantVal) (lps : List Name) (nP nF i : Nat) (F : Nat) :
    (checkProjRule (fueledOpsM mode) env' pty cvj lps nP nF i).val F =
      checkProjRule (fueledOps mode F) env' pty cvj lps nP nF i := by
  unfold checkProjRule
  datF_tac2 <;> datF_step2 <;> datF_step2

theorem checkMemberVal_datF (blockNames : List Name)
    (env' : Env) (cv : ConstantVal) (F : Nat) :
    (checkMemberVal (fueledOpsM mode) blockNames env' cv).val F =
      checkMemberVal (fueledOps mode F) blockNames env' cv := by
  unfold checkMemberVal
  datF_tac2

theorem checkIndMember_datF (blockNames : List Name) (caps : IndCaps) (env' : Env) (ci : ConstantInfo) (F : Nat) :
    (checkIndMember (fueledOpsM mode) blockNames caps env' ci).val F =
      checkIndMember (fueledOps mode F) blockNames caps env' ci := by
  unfold checkIndMember
  datF_tac2
  all_goals rw [checkMemberVal_datF]

theorem provisionRecs_datF (blockNames : List Name) (F : Nat) :
    ∀ (envAcc : Env) (recs : List ConstantInfo),
      (provisionRecs (fueledOpsM mode) blockNames envAcc recs).val F =
      provisionRecs (fueledOps mode F) blockNames envAcc recs
  | _, [] => rfl
  | envAcc, ci :: rest => by
    unfold provisionRecs
    (datF_step2 <;> datF_step2) <;>
      first
        | (rw [checkMemberVal_datF])
        | exact provisionRecs_datF blockNames F _ rest
        | rfl

theorem checkIndRecs_datF (blockNames : List Name) (env₂ : Env)
    (recs : List ConstantInfo) (F : Nat) :
    (checkIndRecs mode (fueledOpsM mode) blockNames env₂ recs).val F =
      checkIndRecs mode (fueledOps mode F) blockNames env₂ recs := by
  unfold checkIndRecs
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    provisionRecs_datF, foldlM_atF, checkIotaRules_datF]

macro "datF_step3_alt" : tactic =>
  `(tactic| first
    | (rw [liftFueled_atF])
    | (rw [foldlM_atF])
    | (rw [checkConstantVal_datF])
    | (rw [checkProjLookups_datF])
    | (rw [checkProjTy_datF])
    | (rw [checkProjShape_datF])
    | (rw [checkProjIota_datF])
    | (rw [checkProjRule_datF])
    | (rw [checkDefEqList_datF])
    | (rw [checkIndMember_datF])
    | (rw [checkIotaRule_datF])
    | (rw [checkIotaRules_datF])
    | (rw [checkProjFn_datF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only []))

macro "datF_step3" : tactic => `(tactic| repeat datF_step3_alt)

macro "datF_tac3" : tactic =>
  `(tactic| repeat' datF_step3_alt)

theorem checkProjFn_datF (env' : Env) (T ctorName : Name) (lps : List Name) (nP nF i : Nat) (F : Nat) :
    (checkProjFn mode (fueledOpsM mode) env' T ctorName lps nP nF i).val F =
      checkProjFn mode (fueledOps mode F) env' T ctorName lps nP nF i := by
  unfold checkProjFn
  datF_tac3 <;> datF_step3 <;> datF_step3 <;> datF_step3

theorem installProjFnStep_datF (T ctorName : Name)
    (lps : List Name) (nP nF : Nat) (e : Env) (i : Nat) (F : Nat) :
    (installProjFnStep mode (fueledOpsM mode) T ctorName lps nP nF e i).val F
      = installProjFnStep mode (fueledOps mode F) T ctorName lps nP nF e i := by
  unfold installProjFnStep
  split
  · exact checkProjFn_datF e T ctorName lps nP nF i F
  · rfl

theorem installBasisDecl_datF (env : Env) (ci : ConstantInfo) (F : Nat) :
    (installBasisDecl env ci : FueledM _).val F =
      (installBasisDecl env ci : CheckM _) := by
  unfold installBasisDecl
  datF_tac

/-! ### The direct simple-structure path, at fuel `F` -/

theorem fueledOpsM_annotate_atF (env : Env) (d : Nat) (a : Expr)
    (F : Nat) :
    ((fueledOpsM mode).annotate env d a).val F =
      (fueledOps mode F).annotate env d a := by rfl

theorem fueledOpsM_ensureSort_atF (env : Env) (d : Nat) (a : Expr)
    (F : Nat) :
    ((fueledOpsM mode).ensureSort env d a).val F =
      (fueledOps mode F).ensureSort env d a := by rfl

theorem checkStructDomsAt_datF (env : Env) (off : Nat)
    (fvs doms : List Expr) (F : Nat) :
    ∀ j : Nat,
      (checkStructDomsAt (fueledOpsM mode) env off fvs doms j).val F =
        checkStructDomsAt (fueledOps mode F) env off fvs doms j
  | 0 => rfl
  | j + 1 => by
    unfold checkStructDomsAt
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
      FueledM.atF_ite, fueledOpsM_isDefEq_atF, unwrapOr_atF,
      checkStructDomsAt_datF env off fvs doms F j]

theorem checkStructProjTable_datF (T C : Name) (lps : List Name)
    (nP nF : Nat) (rs : Level) (guards : List Level) (off : Nat) (cvCa : ConstantVal)
    (env : Env) (F : Nat) :
    (checkStructProjTable T C lps nP nF rs guards off cvCa env : FueledM _).val F =
      (checkStructProjTable T C lps nP nF rs guards off cvCa env : CheckM _) := by
  unfold checkStructProjTable
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
    FueledM.atF_ite, unwrapOr_atF]

/-! ### The direct sum route (task #175 sum-types) -/

theorem fueledOpsM_whnf_atF (env : Env) (d : Nat) (a : Expr) (F : Nat) :
    ((fueledOpsM mode).whnf env d a).val F = (fueledOps mode F).whnf env d a := by rfl

/-- Official's telescope loop (task #195) at fuel `F`. -/
theorem whnfTelescope_datF (env : Env) (F : Nat) :
    ∀ (i n : Nat) (e : Expr),
      (whnfTelescope (fueledOpsM mode) env i n e).val F =
        whnfTelescope (fueledOps mode F) env i n e
  | i, 0, e => by
    unfold whnfTelescope
    simp only [FueledM.atF_bind, fueledOpsM_whnf_atF]
    congr 1
    funext e'
    split <;> simp only [FueledM.atF_pure, FueledM.atF_throw]
  | i, n + 1, e => by
    unfold whnfTelescope
    simp only [FueledM.atF_bind, fueledOpsM_whnf_atF]
    congr 1
    funext e'
    split
    · next nm dom body bm =>
      simp only [FueledM.atF_bind, FueledM.atF_pure,
        whnfTelescope_datF env F (i + 1) n (body.instantiate1 (.fvar i dom))]
    · simp only [FueledM.atF_throw]

/-- The former's telescope stage (task #195) at fuel `F`. -/
theorem checkSumTele_datF (env : Env) (cv : ConstantVal) (n : Nat)
    (cvTa₀ : ConstantVal) (F : Nat) :
    (checkSumTele (fueledOpsM mode) env cv n cvTa₀).val F =
      checkSumTele (fueledOps mode F) env cv n cvTa₀ := by
  unfold checkSumTele
  cases hst : cvTa₀.type.stripPis n with
  | none =>
    simp only [FueledM.atF_bind, FueledM.atF_pure, whnfTelescope_datF, checkConstantVal_datF]
  | some q =>
    obtain ⟨bs, body⟩ := q
    cases body <;> simp only [FueledM.atF_bind, FueledM.atF_pure, whnfTelescope_datF,
      checkConstantVal_datF]

theorem checkSumInd_datF (env : Env) (p : InductiveShape)
    (capsOf : InductiveShape → IndCaps) (F : Nat) :
    (checkSumInd (fueledOpsM mode) env p capsOf).val F =
      checkSumInd (fueledOps mode F) env p capsOf := by
  unfold checkSumInd
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
    FueledM.atF_ite, unwrapOr_atF, checkConstantVal_datF, checkSumTele_datF]

/-- `checkStructFieldSortsI` (task #175 indexed) at fuel `F`. -/
theorem checkStructFieldSortsI_datF (env : Env) (isProp large : Bool)
    (s : Level) (nP : Nat) (fvs idxArgs : List Expr) (F : Nat) :
    ∀ j : Nat,
      (checkStructFieldSortsI (fueledOpsM mode) env isProp large s nP fvs idxArgs
          j).val F =
        checkStructFieldSortsI (fueledOps mode F) env isProp large s nP fvs idxArgs j
  | 0 => rfl
  | j + 1 => by
    unfold checkStructFieldSortsI
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
      FueledM.atF_ite, fueledOpsM_inferType_atF, fueledOpsM_ensureSort_atF,
      liftFueled_atF, unwrapOr_atF,
      checkStructFieldSortsI_datF env isProp large s nP fvs idxArgs F j]

/-- Official's positivity walk as a normalisation (task #210 Part D)
at fuel `F`. -/
theorem normPosDom_datF (env : Env) (T : Name) (F : Nat) (fuel : Nat) :
    ∀ (d : Nat) (e : Expr),
      (normPosDom (fueledOpsM mode) env T d fuel e).val F =
        normPosDom (fueledOps mode F) env T d fuel e := by
  induction fuel with
  | zero =>
    intro d e
    unfold normPosDom
    simp only [FueledM.atF_throw]
  | succ fuel ih =>
    intro d e
    unfold normPosDom
    split
    · simp only [FueledM.atF_pure]
    simp only [FueledM.atF_bind, fueledOpsM_whnf_atF]
    congr 1
    funext w
    split
    · simp only [FueledM.atF_pure]
    · split
      · rename_i dom body bm _
        split
        · simp only [FueledM.atF_throw]
        · simp only [FueledM.atF_bind, FueledM.atF_pure,
            ih (d + 1) (body.instantiate1 (.fvar d dom))]
      · simp only [FueledM.atF_pure]

theorem normFieldDoms_datF (env : Env) (T : Name) (F : Nat) (n : Nat) :
    ∀ (i : Nat) (e : Expr),
      (normFieldDoms (fueledOpsM mode) env T i n e).val F =
        normFieldDoms (fueledOps mode F) env T i n e := by
  induction n with
  | zero =>
    intro i e
    unfold normFieldDoms
    simp only [FueledM.atF_pure]
  | succ n ih =>
    intro i e
    match e with
    | .forallE dom body bm =>
      simp only [normFieldDoms, FueledM.atF_bind, normPosDom_datF env T F 1024 i dom]
      congr 1
      funext dom'
      simp only [FueledM.atF_bind, FueledM.atF_pure,
        ih (i + 1) (body.instantiate1 (.fvar i dom))]
    | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _ | .letE _ _ _
    | .lit _ | .proj _ _ _ =>
      simp only [normFieldDoms, FueledM.atF_throw]

theorem normCtorVal_datF (env : Env) (T : Name) (nP nF : Nat) (cvC cvCa : ConstantVal)
    (F : Nat) :
    (normCtorVal (fueledOpsM mode) env T nP nF cvC cvCa).val F =
      normCtorVal (fueledOps mode F) env T nP nF cvC cvCa := by
  unfold normCtorVal
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    unwrapOr_atF, checkConstantVal_datF, normFieldDoms_datF]

theorem checkSumCtor_datF (env₀ env : Env) (T : Name) (lps : List Name)
    (nP nIdx : Nat) (rs : Level) (isProp large : Bool) (cvC : ConstantVal) (nF : Nat)
    (cvTa : ConstantVal) (F : Nat) :
    (checkSumCtor (fueledOpsM mode) env₀ env T lps nP nIdx rs isProp large
      cvC nF cvTa).val F =
      checkSumCtor (fueledOps mode F) env₀ env T lps nP nIdx rs isProp large
        cvC nF cvTa := by
  unfold checkSumCtor
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
    FueledM.atF_ite, unwrapOr_atF, checkConstantVal_datF, normCtorVal_datF,
    checkStructFieldSortsI_datF, checkStructDomsAt_datF]

theorem checkSumCtors_datF (env₀ env : Env) (T : Name) (lps : List Name)
    (nP nIdx : Nat) (rs : Level) (isProp large : Bool) (cvTa : ConstantVal) (F : Nat) :
    ∀ cs : List (ConstantVal × Nat),
      (checkSumCtors (fueledOpsM mode) env₀ env T lps nP nIdx rs isProp large
        cvTa cs).val F =
        checkSumCtors (fueledOps mode F) env₀ env T lps nP nIdx rs isProp large
          cvTa cs
  | [] => rfl
  | c :: cs => by
    unfold checkSumCtors
    simp only [FueledM.atF_bind, FueledM.atF_pure, checkSumCtor_datF,
      checkSumCtors_datF env₀ env T lps nP nIdx rs isProp large cvTa F cs]

/-! ### The direct recursive install (task #188) -/

theorem checkNativeRules_datF (envR : Env) (rlps : List Name) (T : Name)
    (lps : List Name) (elim : Name) (large : Bool) (nP nIdx : Nat) (tty : Expr)
    (ctors : List (Name × Nat × Expr × List Nat)) (recC : Name) (rlvls : List Level)
    (F : Nat) :
    ∀ k j : Nat,
      (checkNativeRules (m := FueledM) envR rlps T lps elim large nP nIdx tty ctors
        recC rlvls k j).val F =
        checkNativeRules (m := CheckM) envR rlps T lps elim large nP nIdx tty ctors
          recC rlvls k j
  | 0, _ => rfl
  | k + 1, j => by
    unfold checkNativeRules
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
      unwrapOr_atF,
      checkNativeRules_datF envR rlps T lps elim large nP nIdx tty ctors recC rlvls F k
        (j + 1)]

theorem checkNativeRec_datF (env : Env) (p : NativeParts)
    (cvTa : ConstantVal) (ctorsA : List (ConstantVal × Nat)) (F : Nat) :
    (checkNativeRec (fueledOpsM mode) env p cvTa ctorsA).val F =
      checkNativeRec (fueledOps mode F) env p cvTa ctorsA := by
  unfold checkNativeRec
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
    FueledM.atF_ite, fueledOpsM_isDefEq_atF, fueledOpsM_inferType_atF,
    fueledOpsM_ensureSort_atF, unwrapOr_atF, checkConstantVal_datF,
    checkNativeRules_datF]

/-- The projection table at a structure-like block (task #210 Part A)
at fuel `F`: operation-free, so the fuel is irrelevant. -/
theorem checkNativeTable_datF (p : NativeParts) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) (env : Env) (F : Nat) :
    (checkNativeTable (m := FueledM) p ctorsA sortss env).val F =
      checkNativeTable (m := CheckM) p ctorsA sortss env := by
  unfold checkNativeTable
  split
  · split
    · rw [checkStructProjTable_datF]
    · rfl
  · rfl

/-- The kinds' classification at fuel `F` (task #210 Part D):
operation-free, so the fuel is irrelevant. -/
theorem classifyFixKinds_datF (T : Name) (lps : List Name) (nP nIdx : Nat)
    (ctorsA : List (ConstantVal × Nat)) (F : Nat) :
    (classifyFixKinds (m := FueledM) T lps nP nIdx ctorsA).val F =
      classifyFixKinds (m := CheckM) T lps nP nIdx ctorsA := by
  unfold classifyFixKinds
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    unwrapOr_atF]

theorem checkNativePass_datF (env : Env) (p : NativeParts) (isRec : Bool) (F : Nat) :
    (checkNativePass (fueledOpsM mode) env p isRec).val F =
      checkNativePass (fueledOps mode F) env p isRec := by
  unfold checkNativePass
  simp only [FueledM.atF_bind, FueledM.atF_pure, checkSumInd_datF, checkSumCtors_datF,
    classifyFixKinds_datF]

theorem checkNativeTail_datF (env : Env) (q : NativePass Env) (F : Nat) :
    (checkNativeTail (fueledOpsM mode) env q).val F =
      checkNativeTail (fueledOps mode F) env q := by
  unfold checkNativeTail
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
    FueledM.atF_ite, checkNativeTable_datF, checkNativeRec_datF, unwrapOr_atF,
    checkStructFieldSortsI_datF]

theorem checkNative_datF (env : Env) (p : NativeParts) (F : Nat) :
    (checkNative (fueledOpsM mode) env p).val F =
      checkNative (fueledOps mode F) env p := by
  unfold checkNative
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
    FueledM.atF_ite, checkNativePass_datF, checkNativeTail_datF]

macro "datF_step4_alt" : tactic =>
  `(tactic| first
    | (rw [liftFueled_atF])
    | (rw [foldlM_atF])
    | (simp only [checkIndMember_datF, checkProjFn_datF,
        installProjFnStep_datF, installBasisDecl_datF])
    | (rw [checkConstantVal_datF])
    | (rw [checkProjLookups_datF])
    | (rw [checkProjTy_datF])
    | (rw [checkProjShape_datF])
    | (rw [checkProjIota_datF])
    | (rw [checkProjRule_datF])
    | (rw [checkDefEqList_datF])
    | (rw [checkIndMember_datF])
    | (rw [checkIotaRule_datF])
    | (rw [checkIotaRules_datF])
    | (rw [checkIndRecs_datF])
    | (rw [checkProjFn_datF])
    | (rw [checkStruct_datF])
    | (rw [checkModeled_datF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only []))


macro "datF_tac4" : tactic =>
  `(tactic| repeat' datF_step4_alt)

theorem checkModeled_datF (env : Env) (block : List ConstantInfo) (F : Nat) :
    (checkModeled mode (fueledOpsM mode) env block).val F =
      checkModeled mode (fueledOps mode F) env block := by
  unfold checkModeled
  datF_tac4

theorem checkDefnVal_datF (env : Env) (cv : ConstantVal) (value : Expr)
    (hint : ReducibilityHint) (F : Nat) :
    (checkDefnVal (fueledOpsM mode) env cv value hint).val F =
      checkDefnVal (fueledOps mode F) env cv value hint := by
  unfold checkDefnVal
  datF_tac

theorem checkThmVal_datF (env : Env) (cv : ConstantVal) (value : Expr)
    (F : Nat) :
    (checkThmVal (fueledOpsM mode) env cv value).val F =
      checkThmVal (fueledOps mode F) env cv value := by
  unfold checkThmVal
  datF_tac

theorem checkOpaqueVal_datF (env : Env) (cv : ConstantVal) (value : Expr)
    (F : Nat) :
    (checkOpaqueVal (fueledOpsM mode) env cv value).val F =
      checkOpaqueVal (fueledOps mode F) env cv value := by
  unfold checkOpaqueVal
  datF_tac

theorem certifyNatEqs_datF (env : Env) (F : Nat) :
    ∀ eqs : List (Expr × Expr),
      (certifyNatEqs (fueledOpsM mode) env eqs).val F =
        certifyNatEqs (fueledOps mode F) env eqs
  | [] => rfl
  | eq :: rest => by
    show ((do
        if ← CheckerOps.isDefEq (fueledOpsM mode) env 2 eq.1 eq.2 then
          certifyNatEqs (fueledOpsM mode) env rest
        else pure false : FueledM _)).val F = _
    rw [FueledM.atF_bind]
    show _ = (do
        if ← CheckerOps.isDefEq (fueledOps mode F) env 2 eq.1 eq.2 then
          certifyNatEqs (fueledOps mode F) env rest
        else pure false : CheckM _)
    congr 1
    funext b
    cases b with
    | true => exact certifyNatEqs_datF env F rest
    | false => rfl

theorem checkDivModCerts_datF (env : Env) (c : Name) (annVal : Expr)
    (F : Nat) :
    ∀ (stmts : List (List Expr × Expr)) (proofs : List Expr),
      (checkDivModCerts (fueledOpsM mode) env c annVal stmts proofs).val F =
        checkDivModCerts (fueledOps mode F) env c annVal stmts proofs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | (hyps, eqE) :: srest, proof :: prest => by
    simp only [checkDivModCerts]
    split
    · rw [FueledM.atF_bind]
      congr 1
      funext appliedA
      rw [FueledM.atF_bind]
      congr 1
      funext tp
      rw [FueledM.atF_bind]
      congr 1
      funext b
      cases b with
      | true => exact checkDivModCerts_datF env c annVal F srest prest
      | false => rfl
    · rfl

theorem checkDivModPinAt_datF (env : Env) (c : Name) (value' : Expr)
    (ps : NatOpPinSet) (F : Nat) :
    (checkDivModPinAt (fueledOpsM mode) env c value' ps).val F =
      checkDivModPinAt (fueledOps mode F) env c value' ps := by
  unfold checkDivModPinAt
  repeat (first
    | (rw [checkDivModCerts_datF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [FueledM.atF_pure, FueledM.atF_throw]))

theorem checkDivModPinLoop_datF (env : Env) (c : Name) (value' : Expr)
    (F : Nat) :
    ∀ (pss : List NatOpPinSet) (tried : List String),
      (checkDivModPinLoop (fueledOpsM mode) env c value' pss tried).val F =
        checkDivModPinLoop (fueledOps mode F) env c value' pss tried
  | [], _ => rfl
  | ps :: rest, tried => by
    unfold checkDivModPinLoop
    split
    · rw [fueledOpsM_orElse_atF, fueledOps_orElse', checkDivModPinAt_datF]
      cases checkDivModPinAt (fueledOps mode F) env c value' ps with
      | ok b =>
        cases b with
        | true => rfl
        | false => exact checkDivModPinLoop_datF env c value' F rest _
      | error e => exact checkDivModPinLoop_datF env c value' F rest _
    · exact checkDivModPinLoop_datF env c value' F rest _

theorem checkDivModPin_datF (env env2 : Env) (c : Name) (F : Nat) :
    (checkDivModPin (fueledOpsM mode) pins env env2 c).val F =
      checkDivModPin (fueledOps mode F) pins env env2 c := by
  unfold checkDivModPin
  repeat (first
    | (rw [checkDivModPinLoop_datF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [FueledM.atF_pure, FueledM.atF_throw]))

theorem checkReducePin_datF (env env2 : Env) (c : Name) (value : Expr)
    (F : Nat) :
    (checkReducePin (fueledOpsM mode) env env2 c value).val F =
      checkReducePin (fueledOps mode F) env env2 c value := by
  unfold checkReducePin
  repeat (first
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [FueledM.atF_pure, FueledM.atF_throw]))

/-- The pinned-block install at a fuel datum.  Three of `checkDecl`'s
arms share this body since task #293. -/
theorem checkBasisDecl_datF (env : Env) (kind : BasisKind) (F : Nat) :
    (checkBasisDecl (m := FueledM) env kind).val F =
      checkBasisDecl (m := CheckM) env kind := by
  unfold checkBasisDecl
  dsimp only
  by_cases hq : kind = .quotK
  · rw [if_pos hq, if_pos hq]
    by_cases he : env.find? eqName = some eqA
    · rw [if_pos he, if_pos he, foldlM_atF]
      simp only [installBasisDecl_datF]
    · rw [if_neg he, if_neg he, FueledM.atF_bind]
      simp only [FueledM.atF_throw]
      congr 1
      funext x
      rw [foldlM_atF]
      simp only [installBasisDecl_datF]
  · rw [if_neg hq, if_neg hq, foldlM_atF]
    simp only [installBasisDecl_datF]

theorem checkDecl_datF (env : Env) (d : Declaration) (F : Nat) :
    (checkDecl mode (fueledOpsM mode) pins env d).val F =
      checkDecl mode (fueledOps mode F) pins env d := by
  unfold checkDecl
  cases d with
  | defnDecl cv value hint =>
    dsimp only
    rw [FueledM.atF_bind, checkConstantVal_datF]
    congr 1
    funext cv'
    rw [FueledM.atF_bind, checkDefnVal_datF]
    congr 1
    funext env2
    repeat (first
      | (rw [certifyNatEqs_datF])
      | (rw [checkDivModPin_datF])
      | split
      | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
      | rfl
      | (simp only [FueledM.atF_pure, FueledM.atF_throw]))
  | thmDecl cv value =>
    show ((checkConstantVal (fueledOpsM mode) env cv >>= fun cv =>
      checkThmVal (fueledOpsM mode) env cv value : FueledM _)).val F = _
    rw [FueledM.atF_bind, checkConstantVal_datF]
    congr 1
    funext cv'
    rw [checkThmVal_datF]
  | opaqueDecl cv value =>
    dsimp only
    rw [FueledM.atF_bind, checkConstantVal_datF]
    congr 1
    funext cv'
    rw [FueledM.atF_bind, checkOpaqueVal_datF]
    congr 1
    funext env2
    repeat (first
      | (rw [checkReducePin_datF])
      | split
      | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
      | rfl
      | (simp only [FueledM.atF_pure, FueledM.atF_throw]))
  | axiomDecl cv =>
    dsimp only
    -- the `Quot.sound` comparison (task #293) is a pure guard
    by_cases hqs : cv.name = quotSoundName
    · rw [if_pos hqs, if_pos hqs]
      simp only [FueledM.atF_ite, FueledM.atF_pure, FueledM.atF_throw]
    · rw [if_neg hqs, if_neg hqs]
      rw [FueledM.atF_bind, checkConstantVal_datF]
      congr 1
      funext cvA
      simp only [FueledM.atF_ite, FueledM.atF_pure, FueledM.atF_throw]
  | basisDecl kind => exact checkBasisDecl_datF env kind F
  | quotDecl k cv =>
    dsimp only
    -- the pin comparison (task #293) is a pure guard
    by_cases hp : quotPinHit k cv = true
    · rw [if_pos hp, if_pos hp]
      cases k
      · exact checkBasisDecl_datF env .quotK F
      all_goals simp only [FueledM.atF_pure]
    · rw [if_neg hp, if_neg hp]
      simp only [FueledM.atF_throw]
  | indDecl block nP =>
    dsimp only
    -- the pinned-block recognition (task #293) and the declared
    -- parameter count (task #228) are pure guards: the two sides take
    -- the same branch, and the guards' `throw` is fuel-free
    split
    · exact checkBasisDecl_datF env _ F
    · split
      · split
        · exact checkNative_datF env _ F
        · exact checkModeled_datF env block F
      · rfl

theorem checkDeclsPure_datF (ds : List Declaration) (F : Nat) :
    (checkDeclsPure mode (fueledOpsM mode) pins ds).val F =
      checkDeclsPure mode (fueledOps mode F) pins ds := by
  unfold checkDeclsPure
  rw [foldlM_atF]
  simp only [checkDecl_datF]

end ConLeche
