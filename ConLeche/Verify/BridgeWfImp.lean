module

public import ConLeche.Verify.BridgeDecl

public section

/-!
# `wfOpsM mode` runs to pure runs, per declaration-checker function

With the memo operations unguarded, part B's entry-point bridges carry
the arguments' well-scopedness, so `wfOpsM mode`'s condition is per call
(`EnvWF env ∧ wscopedB`) and can no longer be discharged wholesale per
function.  This module proves the run-level implications instead: a
successful `wfOpsM mode` run of each declaration-checker function over a
well-formed environment is the pure `fueledOps` run at the same fuel.
At each operation call site the argument's well-scopedness comes from

* the checker's own input validation (`looseBVarsBounded`/`hasFvar`
  guards precede every `annotate` of raw input — at depth 0
  fvar-freedom *is* well-scopedness),
* the scoping-preservation lemmas for the operations' outputs
  (`annotateCore_WScoped`, `inferTypeCore_WScoped`), and
* scoping of the iota-theorem check's opened telescopes
  (`openPisAtFvars_WScoped`, `instPisAt_WScoped`, `instLamsAt_WScoped`
  — the defeq comparisons run at the opened depth, over variables of
  that frame).

The cached tier's bridge composes these with the intermediate `EnvWF`
facts into the per-declaration bridge: `ConLeche/Verify/Cached/BridgeCS1.lean`
through `BridgeCS3.lean` mirror the `_wfimp` walks per call site,
`BridgeCS4.lean` and `BridgeCSDecl.lean` chain them along the phase
drivers into `checkDeclSharedF_bridge`.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode}
variable {pins : List NatOpPinSet}

open Expr

/-! ## Small syntactic toolkit -/

theorem wscopedB_of_not_hasFvar {e : Expr} (h : e.hasFvar = false)
    {d : Nat} : e.wscopedB d = true :=
  (WScoped.of_not_hasFvar h).to_wscopedB

theorem hasFvar_liftLooseBVars (n : Nat) :
    ∀ (c : Nat) (e : Expr), (e.liftLooseBVars n c).hasFvar = e.hasFvar := by
  intro c e
  induction e generalizing c <;>
    simp_all [Expr.liftLooseBVars, Expr.hasFvar]
  case bvar i => split <;> simp [Expr.hasFvar]

theorem hasFvar_renameConsts (f : Name → Name) :
    ∀ (e : Expr), (e.renameConsts f).hasFvar = e.hasFvar := by
  intro e
  induction e <;> simp_all [Expr.renameConsts, Expr.hasFvar]

theorem hasFvar_mkAppN :
    ∀ (args : List Expr) (g : Expr), g.hasFvar = false →
      (∀ x ∈ args, x.hasFvar = false) → (Expr.mkAppN g args).hasFvar = false
  | [], g, hg, _ => hg
  | a :: as, g, hg, hargs => by
    simp only [Expr.mkAppN]
    refine hasFvar_mkAppN as _ ?_
      (fun x hx => hargs x (List.mem_cons_of_mem _ hx))
    simp only [Expr.hasFvar, Bool.or_eq_false_iff]
    exact ⟨hg, hargs a (List.mem_cons_self ..)⟩

theorem stripLams_not_hasFvar :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)}
      {body : Expr}, Expr.stripLams k e = some (bs, body) →
      e.hasFvar = false →
      (∀ b ∈ bs, (b.1).hasFvar = false) ∧ body.hasFvar = false
  | 0, e, bs, body, h, hf => by
    simp only [Expr.stripLams, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ : [] = bs ∧ e = body :=
      ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    exact ⟨(fun b hb => nomatch hb), hf⟩
  | k + 1, e, bs, body, h, hf => by
    match e, h with
    | .lam ty b m, h =>
      simp only [Expr.stripLams, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body'⟩, hstrip, heq⟩ := h
      obtain ⟨rfl, rfl⟩ : (ty, m) :: bs' = bs ∧ body' = body :=
        ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
      obtain ⟨hrest, hbody⟩ := stripLams_not_hasFvar k hstrip hf.2
      refine ⟨?_, hbody⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hf.1
      · exact hrest b hb

theorem stripPis_not_hasFvar :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)}
      {body : Expr}, Expr.stripPis k e = some (bs, body) →
      e.hasFvar = false →
      (∀ b ∈ bs, (b.1).hasFvar = false) ∧ body.hasFvar = false
  | 0, e, bs, body, h, hf => by
    simp only [Expr.stripPis, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ : [] = bs ∧ e = body :=
      ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    exact ⟨(fun b hb => nomatch hb), hf⟩
  | k + 1, e, bs, body, h, hf => by
    match e, h with
    | .forallE ty b m, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body'⟩, hstrip, heq⟩ := h
      obtain ⟨rfl, rfl⟩ : (ty, m) :: bs' = bs ∧ body' = body :=
        ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
      obtain ⟨hrest, hbody⟩ := stripPis_not_hasFvar k hstrip hf.2
      refine ⟨?_, hbody⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hf.1
      · exact hrest b hb

theorem atF_bind_ok {α β : Type} {x : FueledM α} {g : α → FueledM β}
    {F : Nat} {v : β} (h : (x >>= g).val F = .ok v) :
    ∃ a, x.val F = .ok a ∧ (g a).val F = .ok v := by
  rw [FueledM.atF_bind] at h
  revert h
  cases hx : x.val F with
  | error e =>
    intro h
    simp only [Bind.bind, Except.bind] at h
    exact nomatch h
  | ok a =>
    intro h
    simp only [Bind.bind, Except.bind] at h
    exact ⟨a, rfl, h⟩

theorem atF_throw_bind {α β : Type} {e : CheckError}
    {g : α → FueledM β} {F : Nat} {v : β}
    (h : ((throw e : FueledM α) >>= g).val F = .ok v) : False := by
  rw [FueledM.atF_bind] at h
  simp only [throw, throwThe, MonadExceptOf.throw, Bind.bind,
    Except.bind] at h
  exact nomatch h

/-! ## The leaf checker functions, `wfOpsM mode` runs to pure runs -/

theorem checkConstantVal_wfimp {env : Env} (henv : EnvWF env)
    {cv : ConstantVal} {F : Nat} {v : ConstantVal}
    (h : (checkConstantVal (wfOpsM mode) env cv).val F = .ok v) :
    checkConstantVal (fueledOps mode F) env cv = .ok v := by
  unfold checkConstantVal at h ⊢
  dsimp only [] at h ⊢
  by_cases h1 : (env.find? cv.name).isSome = true
  · rw [if_pos h1] at h
    exact absurd h atF_throw_bind
  rw [if_neg h1] at h ⊢
  by_cases h2 : reservedBasisNames.contains cv.name = true
  · rw [if_pos h2] at h
    exact absurd h atF_throw_bind
  rw [if_neg h2] at h ⊢
  by_cases h3 : cv.name.isProjFnShape = true
  · rw [if_pos h3] at h
    exact absurd h atF_throw_bind
  rw [if_neg h3] at h ⊢
  by_cases h4 : Name.nodup cv.levelParams = true
  case neg =>
    rw [if_neg h4] at h
    exact absurd h atF_throw_bind
  rw [if_pos h4] at h ⊢
  by_cases h5 : Expr.looseBVarsBounded 0 cv.type = true
  case neg =>
    rw [if_neg h5] at h
    exact absurd h atF_throw_bind
  rw [if_pos h5] at h ⊢
  by_cases h6 : cv.type.hasFvar = true
  · rw [if_pos h6] at h
    exact absurd h atF_throw_bind
  rw [if_neg h6] at h ⊢
  rw [wfOpsM_annotate henv
    (wscopedB_of_not_hasFvar (Bool.not_eq_true _ ▸ h6))] at h
  obtain ⟨type, hty, h⟩ := atF_bind_ok h
  have hty' : annotateCore mode env F 0 cv.type = .ok type := hty
  show (annotateCore mode env F 0 cv.type >>= _) = _
  rw [hty']
  simp only [Bind.bind, Except.bind]
  have hwty : WScoped 0 type := annotateCore_WScoped F cv.type hty'
    (WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h6))
  by_cases h7 : Expr.allLevelParamsDefined cv.levelParams type = true
  case neg =>
    rw [if_neg h7] at h
    exact absurd h atF_throw_bind
  rw [if_pos h7] at h ⊢
  by_cases h8 : Expr.constsResolve env type = true
  case neg =>
    rw [if_neg h8] at h
    exact absurd h atF_throw_bind
  rw [if_pos h8] at h ⊢
  rw [wfOpsM_inferType henv hwty.to_wscopedB] at h
  obtain ⟨stype, hsty, h⟩ := atF_bind_ok h
  have hsty' : inferTypeCore mode env F 0 type = .ok stype := hsty
  show (inferTypeCore mode env F 0 type >>= _) = _
  rw [hsty']
  simp only [Bind.bind, Except.bind]
  have hwsty : WScoped 0 stype := inferTypeCore_WScoped henv F hsty' hwty
  rw [wfOpsM_ensureSort henv hwsty.to_wscopedB] at h
  obtain ⟨u, hu, h⟩ := atF_bind_ok h
  have hu' : ensureSortCore mode env F 0 stype = .ok u := hu
  show (ensureSortCore mode env F 0 stype >>= _) = _
  rw [hu']
  simp only [Bind.bind, Except.bind]
  exact h

theorem checkDefnVal_wfimp {env : Env} (henv : EnvWF env)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hcvty : cv.type.hasFvar = false) {F : Nat} {v : Env}
    (h : (checkDefnVal (wfOpsM mode) env cv value hint).val F = .ok v) :
    checkDefnVal (fueledOps mode F) env cv value hint = .ok v := by
  unfold checkDefnVal at h ⊢
  dsimp only [] at h ⊢
  by_cases h1 : Expr.looseBVarsBounded 0 value = true
  case neg =>
    rw [if_neg h1] at h
    exact absurd h atF_throw_bind
  rw [if_pos h1] at h ⊢
  by_cases h2 : value.hasFvar = true
  · rw [if_pos h2] at h
    exact absurd h atF_throw_bind
  rw [if_neg h2] at h ⊢
  rw [wfOpsM_annotate henv
    (wscopedB_of_not_hasFvar (Bool.not_eq_true _ ▸ h2))] at h
  obtain ⟨value', hval, h⟩ := atF_bind_ok h
  have hval' : annotateCore mode env F 0 value = .ok value' := hval
  show (annotateCore mode env F 0 value >>= _) = _
  rw [hval']
  simp only [Bind.bind, Except.bind]
  have hwval : WScoped 0 value' := annotateCore_WScoped F value hval'
    (WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2))
  by_cases h3 : Expr.allLevelParamsDefined cv.levelParams value' = true
  case neg =>
    rw [if_neg h3] at h
    exact absurd h atF_throw_bind
  rw [if_pos h3] at h ⊢
  by_cases h4 : Expr.constsResolve env value' = true
  case neg =>
    rw [if_neg h4] at h
    exact absurd h atF_throw_bind
  rw [if_pos h4] at h ⊢
  rw [wfOpsM_inferType henv hwval.to_wscopedB] at h
  obtain ⟨vtype, hvt, h⟩ := atF_bind_ok h
  have hvt' : inferTypeCore mode env F 0 value' = .ok vtype := hvt
  show (inferTypeCore mode env F 0 value' >>= _) = _
  rw [hvt']
  simp only [Bind.bind, Except.bind]
  have hwvt : WScoped 0 vtype := inferTypeCore_WScoped henv F hvt' hwval
  rw [wfOpsM_isDefEq henv hwvt.to_wscopedB
    (wscopedB_of_not_hasFvar hcvty)] at h
  obtain ⟨b, hb, h⟩ := atF_bind_ok h
  have hb' : isDefEqCore mode env F 0 vtype cv.type = .ok b := hb
  show (isDefEqCore mode env F 0 vtype cv.type >>= _) = _
  rw [hb']
  simp only [Bind.bind, Except.bind]
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact absurd h atF_throw_bind

theorem checkThmVal_wfimp {env : Env} (henv : EnvWF env)
    {cv : ConstantVal} {value : Expr}
    (hcvty : cv.type.hasFvar = false) {F : Nat} {v : Env}
    (h : (checkThmVal (wfOpsM mode) env cv value).val F = .ok v) :
    checkThmVal (fueledOps mode F) env cv value = .ok v := by
  unfold checkThmVal at h ⊢
  dsimp only [] at h ⊢
  rw [wfOpsM_inferType henv (wscopedB_of_not_hasFvar hcvty)] at h
  obtain ⟨stype, hst, h⟩ := atF_bind_ok h
  have hst' : inferTypeCore mode env F 0 cv.type = .ok stype := hst
  show (inferTypeCore mode env F 0 cv.type >>= _) = _
  rw [hst']
  simp only [Bind.bind, Except.bind]
  have hwst : WScoped 0 stype := inferTypeCore_WScoped henv F hst'
    (WScoped.of_not_hasFvar hcvty)
  rw [wfOpsM_ensureSort henv hwst.to_wscopedB] at h
  obtain ⟨u, hu, h⟩ := atF_bind_ok h
  have hu' : ensureSortCore mode env F 0 stype = .ok u := hu
  show (ensureSortCore mode env F 0 stype >>= _) = _
  rw [hu']
  simp only [Bind.bind, Except.bind]
  obtain ⟨ok₁, hok, h⟩ := atF_bind_ok h
  rw [liftFueled_atF] at hok
  show ((liftFueled "level comparison" (u.isEquiv .zero) :
    CheckM Bool) >>= _) = _
  rw [hok]
  simp only [Bind.bind, Except.bind]
  by_cases h0 : ok₁ = true
  case neg =>
    rw [if_neg h0] at h
    exact absurd h atF_throw_bind
  rw [if_pos h0] at h ⊢
  by_cases h1 : Expr.looseBVarsBounded 0 value = true
  case neg =>
    rw [if_neg h1] at h
    exact absurd h atF_throw_bind
  rw [if_pos h1] at h ⊢
  by_cases h2 : value.hasFvar = true
  · rw [if_pos h2] at h
    exact absurd h atF_throw_bind
  rw [if_neg h2] at h ⊢
  rw [wfOpsM_annotate henv
    (wscopedB_of_not_hasFvar (Bool.not_eq_true _ ▸ h2))] at h
  obtain ⟨value', hval, h⟩ := atF_bind_ok h
  have hval' : annotateCore mode env F 0 value = .ok value' := hval
  show (annotateCore mode env F 0 value >>= _) = _
  rw [hval']
  simp only [Bind.bind, Except.bind]
  have hwval : WScoped 0 value' := annotateCore_WScoped F value hval'
    (WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2))
  by_cases h3 : Expr.allLevelParamsDefined cv.levelParams value' = true
  case neg =>
    rw [if_neg h3] at h
    exact absurd h atF_throw_bind
  rw [if_pos h3] at h ⊢
  by_cases h4 : Expr.constsResolve env value' = true
  case neg =>
    rw [if_neg h4] at h
    exact absurd h atF_throw_bind
  rw [if_pos h4] at h ⊢
  rw [wfOpsM_inferType henv hwval.to_wscopedB] at h
  obtain ⟨vtype, hvt, h⟩ := atF_bind_ok h
  have hvt' : inferTypeCore mode env F 0 value' = .ok vtype := hvt
  show (inferTypeCore mode env F 0 value' >>= _) = _
  rw [hvt']
  simp only [Bind.bind, Except.bind]
  have hwvt : WScoped 0 vtype := inferTypeCore_WScoped henv F hvt' hwval
  rw [wfOpsM_isDefEq henv hwvt.to_wscopedB
    (wscopedB_of_not_hasFvar hcvty)] at h
  obtain ⟨b, hb, h⟩ := atF_bind_ok h
  have hb' : isDefEqCore mode env F 0 vtype cv.type = .ok b := hb
  show (isDefEqCore mode env F 0 vtype cv.type >>= _) = _
  rw [hb']
  simp only [Bind.bind, Except.bind]
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact absurd h atF_throw_bind

theorem checkOpaqueVal_wfimp {env : Env} (henv : EnvWF env)
    {cv : ConstantVal} {value : Expr}
    (hcvty : cv.type.hasFvar = false) {F : Nat} {v : Env}
    (h : (checkOpaqueVal (wfOpsM mode) env cv value).val F = .ok v) :
    checkOpaqueVal (fueledOps mode F) env cv value = .ok v := by
  unfold checkOpaqueVal at h ⊢
  dsimp only [] at h ⊢
  by_cases h1 : Expr.looseBVarsBounded 0 value = true
  case neg =>
    rw [if_neg h1] at h
    exact absurd h atF_throw_bind
  rw [if_pos h1] at h ⊢
  by_cases h2 : value.hasFvar = true
  · rw [if_pos h2] at h
    exact absurd h atF_throw_bind
  rw [if_neg h2] at h ⊢
  rw [wfOpsM_annotate henv
    (wscopedB_of_not_hasFvar (Bool.not_eq_true _ ▸ h2))] at h
  obtain ⟨value', hval, h⟩ := atF_bind_ok h
  have hval' : annotateCore mode env F 0 value = .ok value' := hval
  show (annotateCore mode env F 0 value >>= _) = _
  rw [hval']
  simp only [Bind.bind, Except.bind]
  have hwval : WScoped 0 value' := annotateCore_WScoped F value hval'
    (WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2))
  by_cases h3 : Expr.allLevelParamsDefined cv.levelParams value' = true
  case neg =>
    rw [if_neg h3] at h
    exact absurd h atF_throw_bind
  rw [if_pos h3] at h ⊢
  by_cases h4 : Expr.constsResolve env value' = true
  case neg =>
    rw [if_neg h4] at h
    exact absurd h atF_throw_bind
  rw [if_pos h4] at h ⊢
  rw [wfOpsM_inferType henv hwval.to_wscopedB] at h
  obtain ⟨vtype, hvt, h⟩ := atF_bind_ok h
  have hvt' : inferTypeCore mode env F 0 value' = .ok vtype := hvt
  show (inferTypeCore mode env F 0 value' >>= _) = _
  rw [hvt']
  simp only [Bind.bind, Except.bind]
  have hwvt : WScoped 0 vtype := inferTypeCore_WScoped henv F hvt' hwval
  rw [wfOpsM_isDefEq henv hwvt.to_wscopedB
    (wscopedB_of_not_hasFvar hcvty)] at h
  obtain ⟨b, hb, h⟩ := atF_bind_ok h
  have hb' : isDefEqCore mode env F 0 vtype cv.type = .ok b := hb
  show (isDefEqCore mode env F 0 vtype cv.type >>= _) = _
  rw [hb']
  simp only [Bind.bind, Except.bind]
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact absurd h atF_throw_bind

theorem certifyNatEqs_wfimp {env : Env} (henv : EnvWF env) {F : Nat} :
    ∀ {eqs : List (Expr × Expr)},
      (∀ eq ∈ eqs, (eq.1.wscopedB 2 = true) ∧ (eq.2.wscopedB 2 = true)) →
      ∀ {v : Bool}, (certifyNatEqs (wfOpsM mode) env eqs).val F = .ok v →
      certifyNatEqs (fueledOps mode F) env eqs = .ok v
  | [], _, v, h => h
  | eq :: rest, hsc, v, h => by
    unfold certifyNatEqs at h ⊢
    have hh := hsc eq (List.mem_cons_self ..)
    rw [wfOpsM_isDefEq henv hh.1 hh.2] at h
    obtain ⟨b, hb, h⟩ := atF_bind_ok h
    have hb' : isDefEqCore mode env F 2 eq.1 eq.2 = .ok b := hb
    show (isDefEqCore mode env F 2 eq.1 eq.2 >>= _) = _
    rw [hb']
    simp only [Bind.bind, Except.bind]
    cases b with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact certifyNatEqs_wfimp henv
        (fun e he => hsc e (List.mem_cons_of_mem _ he)) h
    | false =>
      simpa using h

set_option maxHeartbeats 1600000 in
/-- `getD` with the `bvar 0` default preserves well-scopedness. -/
theorem WScoped_getD' {d : Nat} :
    ∀ {l : List Expr}, (∀ x ∈ l, WScoped d x) → ∀ (n : Nat),
      WScoped d (l.getD n (.bvar 0)) := by
  intro l
  induction l with
  | nil => intro _ n; simp [List.getD, WScoped]
  | cons x xs ih =>
    intro h n
    cases n with
    | zero => exact h x List.mem_cons_self
    | succ n =>
      exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) n

/-- `openPisAtFvars` puts the variable it creates for binder `j` at
index `i + j` — the positional companion of `openPisAtFvars_WScoped`,
needed wherever a check runs at each binder's *own* frame. -/
theorem openPisAtFvars_index :
    ∀ (n : Nat) (e : Expr) (i : Nat) {fvs : List Expr} {body : Expr},
      openPisAtFvars n e i = some (fvs, body) →
      ∀ (j : Nat) (x : Expr), fvs[j]? = some x →
        ∃ ty, x = Expr.fvar (i + j) ty := by
  intro n
  induction n with
  | zero =>
    intro e i fvs body h j x hx
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at hx
    exact nomatch hx
  | succ n ih =>
    intro e i fvs body h j x hx
    cases e with
    | forallE dom bodyE mb =>
      simp only [openPisAtFvars] at h
      revert h
      cases hrec : openPisAtFvars n
          (bodyE.instantiate1 (.fvar i dom)) (i + 1) with
      | none => intro h; exact nomatch h
      | some p =>
        obtain ⟨fvs', bodyR⟩ := p
        intro h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          exact ⟨dom, by rw [← hx, Nat.add_zero]⟩
        | succ j =>
          simp only [List.getElem?_cons_succ] at hx
          obtain ⟨ty', hx'⟩ := ih _ (i + 1) hrec j x hx
          exact ⟨ty', by rw [hx']; congr 1; omega⟩
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _
    | lam _ _ _ | letE _ _ _ | lit _ | proj _ _ _ =>
      exact nomatch h

/-- Opening a `∀`-telescope at fresh free variables produces variables
and a body scoped at the extended frame. -/
theorem openPisAtFvars_WScoped :
    ∀ (n : Nat) (e : Expr) (i : Nat) {fvs : List Expr} {body : Expr},
      openPisAtFvars n e i = some (fvs, body) → WScoped i e →
      (∀ x ∈ fvs, WScoped (i + n) x) ∧ WScoped (i + n) body := by
  intro n
  induction n with
  | zero =>
    intro e i fvs body h hw
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun x hx => nomatch hx), hw⟩
  | succ n ih =>
    intro e i fvs body h hw
    cases e with
    | forallE dom bodyE mb =>
      simp only [openPisAtFvars] at h
      revert h
      cases hrec : openPisAtFvars n
          (bodyE.instantiate1 (.fvar i dom)) (i + 1) with
      | none => intro h; exact nomatch h
      | some p =>
        obtain ⟨fvs', bodyR⟩ := p
        intro h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [WScoped] at hw
        obtain ⟨hdom, hbody⟩ := hw
        have hinst : WScoped (i + 1)
            (bodyE.instantiate1 (.fvar i dom)) :=
          WScoped.instantiate1 hdom 0 hbody
        obtain ⟨hfvs', hbody'⟩ := ih _ _ hrec hinst
        have harith : i + 1 + n = i + (n + 1) := by omega
        rw [harith] at hfvs' hbody'
        refine ⟨?_, hbody'⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp only [WScoped]
          exact ⟨by omega, hdom⟩
        · exact hfvs' x hx
    | bvar k => exact nomatch h
    | fvar a c => exact nomatch h
    | sort u => exact nomatch h
    | const c us => exact nomatch h
    | app f a => exact nomatch h
    | lam b c d => exact nomatch h
    | letE b c d => exact nomatch h
    | lit l => exact nomatch h
    | proj s k e => exact nomatch h

/-- Per-index scoping of an instantiated telescope: the `i`-th domain
mentions only the binders before it, so it is scoped at `d + i` when the
spine entries climb one frame at a time.  This is what lets the
recursor's minor-premise pins run at each field's **own** frame. -/
theorem instPisAt_index_WScoped :
    ∀ (spine : List Expr) {d : Nat} {ty : Expr} {doms : List Expr}
      {res : Expr},
      Expr.instPisAt spine ty = some (doms, res) → WScoped d ty →
      (∀ (i : Nat) (a : Expr), spine[i]? = some a → WScoped (d + i + 1) a) →
      ∀ (i : Nat) (x : Expr), doms[i]? = some x → WScoped (d + i) x
  | [], d, ty, doms, res, h, hty, _ => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro i x hx
    exact nomatch hx
  | a :: as, d, ty, doms, res, h, hty, hsp => by
    cases ty with
    | forallE dom body mb =>
      simp only [Expr.instPisAt, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, hqe⟩ := h
      simp only [Prod.mk.injEq] at hqe
      obtain ⟨rfl, rfl⟩ := hqe
      have hty' : WScoped d dom ∧ WScoped d body := by
        simpa [WScoped] using hty
      have haw : WScoped (d + 1) a := by
        have h0 := hsp 0 a rfl
        rwa [Nat.add_zero] at h0
      intro i x hx
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        rw [← hx, Nat.add_zero]
        exact hty'.1
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx
        have hrec := instPisAt_index_WScoped as (d := d + 1) hq
          (WScoped.instantiate1_gen haw 0 (hty'.2.mono (Nat.le_succ d)))
          (fun k b hb => by
            have h0 := hsp (k + 1) b (by simpa using hb)
            rw [show d + (k + 1) + 1 = d + 1 + k + 1 from by omega] at h0
            exact h0) i x hx
        rw [show d + (i + 1) = d + 1 + i from by omega]
        exact hrec
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _
    | letE _ _ _ | lit _ | proj _ _ _ => exact nomatch h

/-- `instPisAt` for `λ`-binders, scoped. -/
theorem instLamsAt_WScoped {d : Nat} :
    ∀ (args : List Expr) (ty : Expr) {doms : List Expr} {res : Expr},
      Expr.instLamsAt args ty = some (doms, res) → WScoped d ty →
      (∀ a ∈ args, WScoped d a) →
      (∀ x ∈ doms, WScoped d x) ∧ WScoped d res
  | [], ty, doms, res, h, hty, _ => by
    simp only [Expr.instLamsAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun x hx => nomatch hx), hty⟩
  | a :: as, ty, doms, res, h, hty, hargs => by
    cases ty with
    | lam dom body mb =>
      simp only [Expr.instLamsAt] at h
      revert h
      cases hrec : Expr.instLamsAt as (body.instantiate1 a) with
      | none => intro h; exact nomatch h
      | some p =>
        obtain ⟨ds, rest⟩ := p
        intro h
        simp only [Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [WScoped] at hty
        obtain ⟨hdom, hbody⟩ := hty
        have hinst : WScoped d (body.instantiate1 a) :=
          WScoped.instantiate1_gen (hargs a List.mem_cons_self) 0 hbody
        obtain ⟨hds, hres⟩ := instLamsAt_WScoped as _ hrec hinst
          (fun x hx => hargs x (List.mem_cons_of_mem _ hx))
        refine ⟨?_, hres⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hdom
        · exact hds x hx
    | bvar k => exact nomatch h
    | fvar a' c => exact nomatch h
    | sort u => exact nomatch h
    | const c us => exact nomatch h
    | app f a' => exact nomatch h
    | forallE b c d' => exact nomatch h
    | letE b c d' => exact nomatch h
    | lit l => exact nomatch h
    | proj s k e => exact nomatch h

/-- The read-off type of an opened variable is scoped. -/
theorem fvarTypeD_WScoped {d : Nat} {e : Expr} (h : WScoped d e) :
    WScoped d (Expr.fvarTypeD e) := by
  cases e with
  | fvar idx ty =>
    simp only [WScoped] at h
    exact WScoped.mono (Nat.le_of_lt h.1) h.2
  | bvar k => exact h
  | sort u => exact h
  | const c us => exact h
  | app f a => exact h
  | lam b c d' => exact h
  | forallE b c d' => exact h
  | letE b c d' => exact h
  | lit l => exact h
  | proj s k e => exact h

theorem unwrapOr_atF_ok {α : Type} {o : Option α} {err : CheckError}
    {F : Nat} {a : α}
    (h : (unwrapOr o err : FueledM α).val F = .ok a) : o = some a := by
  cases o with
  | none => exact nomatch h
  | some b =>
    have hb : b = a := by
      have h' : (Except.ok b : Except CheckError α) = .ok a := h
      exact Except.ok.inj h'
    rw [hb]

/-- Invert a stored-constant lookup (kind-agnostic: the certificate
checks consume only the stored constant's type). -/
theorem findCV?_ok {env : Env} {n : Name} {cvt : ConstantVal}
    (h : env.findCV? n = some cvt) :
    ∃ ci, env.find? n = some ci ∧ ci.toConstantVal = cvt := by
  simp only [Env.findCV?, Option.map_eq_some_iff] at h
  exact h

/-- The pairwise defeq check, `wfOpsM mode` run to pure run (the arguments
are scoped at the check's depth). -/
theorem checkDefEqList_wfimp {env : Env} (henv : EnvWF env)
    {depth : Nat} {F : Nat} :
    ∀ {as bs : List Expr},
      (∀ a ∈ as, WScoped depth a) → (∀ b ∈ bs, WScoped depth b) →
      ∀ {v : Unit},
      (checkDefEqList (wfOpsM mode) env depth as bs).val F = .ok v →
      checkDefEqList (fueledOps mode F) env depth as bs = .ok v
  | [], [], _, _, _, h => h
  | [], _ :: _, _, _, _, h => nomatch h
  | _ :: _, [], _, _, _, h => nomatch h
  | a :: as, b :: bs, ha, hb, v, h => by
    unfold checkDefEqList at h ⊢
    rw [wfOpsM_isDefEq henv (ha a List.mem_cons_self).to_wscopedB
      (hb b List.mem_cons_self).to_wscopedB] at h
    obtain ⟨c, hc, h⟩ := atF_bind_ok h
    have hc' : isDefEqCore mode env F depth a b = .ok c := hc
    show (isDefEqCore mode env F depth a b >>= _) = _
    rw [hc']
    simp only [Bind.bind, Except.bind]
    cases c with
    | false =>
      rw [if_neg (by simp)] at h
      exact absurd h atF_throw_bind
    | true =>
      rw [if_pos rfl] at h ⊢
      exact checkDefEqList_wfimp henv
        (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (fun y hy => hb y (List.mem_cons_of_mem _ hy)) h

/-- The pairwise inferred-type check, `wfOpsM mode` run to pure run. -/
theorem checkTypedList_wfimp {env : Env} (henv : EnvWF env)
    {depth : Nat} {F : Nat} :
    ∀ {as bs : List Expr},
      (∀ a ∈ as, WScoped depth a) → (∀ b ∈ bs, WScoped depth b) →
      ∀ {v : Unit},
      (checkTypedList (wfOpsM mode) env depth as bs).val F = .ok v →
      checkTypedList (fueledOps mode F) env depth as bs = .ok v
  | [], [], _, _, _, h => h
  | [], _ :: _, _, _, _, h => nomatch h
  | _ :: _, [], _, _, _, h => nomatch h
  | a :: as, b :: bs, ha, hb, v, h => by
    unfold checkTypedList at h ⊢
    rw [wfOpsM_inferType henv (ha a List.mem_cons_self).to_wscopedB] at h
    obtain ⟨ty, hty, h⟩ := atF_bind_ok h
    have hty' : inferTypeCore mode env F depth a = .ok ty := hty
    have htyW : WScoped depth ty :=
      inferTypeCore_WScoped henv F hty' (ha a List.mem_cons_self)
    show (inferTypeCore mode env F depth a >>= _) = _
    rw [hty']
    simp only [Bind.bind, Except.bind]
    rw [wfOpsM_isDefEq henv htyW.to_wscopedB
      (hb b List.mem_cons_self).to_wscopedB] at h
    obtain ⟨c, hc, h⟩ := atF_bind_ok h
    have hc' : isDefEqCore mode env F depth ty b = .ok c := hc
    show (isDefEqCore mode env F depth ty b >>= _) = _
    rw [hc']
    simp only [Bind.bind, Except.bind]
    cases c with
    | false =>
      rw [if_neg (by simp)] at h
      exact absurd h atF_throw_bind
    | true =>
      rw [if_pos rfl] at h ⊢
      exact checkTypedList_wfimp henv
        (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (fun y hy => hb y (List.mem_cons_of_mem _ hy)) h

/-- The annotate-idempotence check, `wfOpsM mode` run to pure run. -/
theorem checkAnnotList_wfimp {env : Env} (henv : EnvWF env)
    {depth : Nat} {F : Nat} :
    ∀ {as : List Expr},
      (∀ a ∈ as, WScoped depth a) →
      ∀ {v : Unit},
      (checkAnnotList (wfOpsM mode) env depth as).val F = .ok v →
      checkAnnotList (fueledOps mode F) env depth as = .ok v
  | [], _, _, h => h
  | a :: as, ha, v, h => by
    unfold checkAnnotList at h ⊢
    rw [wfOpsM_annotate henv (ha a List.mem_cons_self).to_wscopedB] at h
    obtain ⟨aA, hann, h⟩ := atF_bind_ok h
    have hann' : annotateCore mode env F depth a = .ok aA := hann
    show (annotateCore mode env F depth a >>= _) = _
    rw [hann']
    simp only [Bind.bind, Except.bind]
    by_cases hc : (aA == a) = true
    case neg =>
      rw [if_neg hc] at h
      exact absurd h atF_throw_bind
    case pos =>
      rw [if_pos hc] at h ⊢
      exact checkAnnotList_wfimp henv
        (fun x hx => ha x (List.mem_cons_of_mem _ hx)) h

set_option maxHeartbeats 6400000 in
/-- The iota-sides type certificate, `wfOpsM mode` to pure (task #100
stage 3). -/
theorem checkIotaSidesTy_wfimp {envSelf : Env} (henvSelf : EnvWF envSelf)
    {depth : Nat} {alphaS lhsS rhsS : Expr} {ℓA : Level} {cvName : Name}
    {F : Nat} {v : Unit}
    (hα : WScoped depth alphaS) (hl : WScoped depth lhsS)
    (hr : WScoped depth rhsS)
    (h : (checkIotaSidesTy mode (wfOpsM mode) envSelf depth alphaS lhsS rhsS
      ℓA cvName).val F = .ok v) :
    checkIotaSidesTy mode (fueledOps mode F) envSelf depth alphaS lhsS rhsS
      ℓA cvName = .ok v := by
  unfold checkIotaSidesTy at h ⊢
  rw [wfOpsM_inferType henvSelf hl.to_wscopedB] at h
  obtain ⟨tl, htl, h⟩ := atF_bind_ok h
  have htl' : inferTypeCore mode envSelf F depth lhsS = .ok tl := htl
  show (inferTypeCore mode envSelf F depth lhsS >>= _) = _
  rw [htl']
  simp only [Bind.bind, Except.bind]
  rw [wfOpsM_isDefEq henvSelf
    (inferTypeCore_WScoped henvSelf F htl' hl).to_wscopedB
    hα.to_wscopedB] at h
  obtain ⟨cl, hdl, h⟩ := atF_bind_ok h
  have hdl' : isDefEqCore mode envSelf F depth tl alphaS = .ok cl := hdl
  show (isDefEqCore mode envSelf F depth tl alphaS >>= _) = _
  rw [hdl']
  simp only [Bind.bind, Except.bind]
  cases cl with
  | false =>
    rw [if_neg (by simp)] at h
    exact nomatch h
  | true =>
  rw [if_pos rfl] at h ⊢
  rw [wfOpsM_inferType henvSelf hr.to_wscopedB] at h
  obtain ⟨tr, htr, h⟩ := atF_bind_ok h
  have htr' : inferTypeCore mode envSelf F depth rhsS = .ok tr := htr
  show (inferTypeCore mode envSelf F depth rhsS >>= _) = _
  rw [htr']
  simp only [Bind.bind, Except.bind]
  rw [wfOpsM_isDefEq henvSelf
    (inferTypeCore_WScoped henvSelf F htr' hr).to_wscopedB
    hα.to_wscopedB] at h
  obtain ⟨cr, hdr, h⟩ := atF_bind_ok h
  have hdr' : isDefEqCore mode envSelf F depth tr alphaS = .ok cr := hdr
  show (isDefEqCore mode envSelf F depth tr alphaS >>= _) = _
  rw [hdr']
  simp only [Bind.bind, Except.bind]
  cases cr with
  | false =>
    rw [if_neg (by simp)] at h
    exact nomatch h
  | true =>
  rw [if_pos rfl] at h ⊢
  -- the type slot's own sort (task #146) — mode-gated (task #147)
  cases htt : mode.ttChecks with
  | false =>
    rw [htt] at h
    simpa using h
  | true =>
  rw [htt] at h
  rw [if_pos rfl] at h ⊢
  rw [wfOpsM_inferType henvSelf hα.to_wscopedB] at h
  obtain ⟨tα, htα, h⟩ := atF_bind_ok h
  have htα' : inferTypeCore mode envSelf F depth alphaS = .ok tα := htα
  show (inferTypeCore mode envSelf F depth alphaS >>= _) = _
  rw [htα']
  simp only [Bind.bind, Except.bind]
  rw [wfOpsM_isDefEq henvSelf
    (inferTypeCore_WScoped henvSelf F htα' hα).to_wscopedB
    (by simp [Expr.wscopedB] : (Expr.sort ℓA).wscopedB depth = true)] at h
  obtain ⟨cα, hdα, h⟩ := atF_bind_ok h
  have hdα' : isDefEqCore mode envSelf F depth tα (Expr.sort ℓA) = .ok cα := hdα
  show (isDefEqCore mode envSelf F depth tα (Expr.sort ℓA) >>= _) = _
  rw [hdα']
  simp only [Bind.bind, Except.bind]
  cases cα with
  | false =>
    rw [if_neg (by simp)] at h
    exact nomatch h
  | true =>
    rw [if_pos rfl] at h ⊢
    exact h

/-- The iota-theorem check, `wfOpsM mode` run to pure run.  The recursor
type, the constructor type and the annotated rule right-hand side are
closed; everything the check compares is scoped at the opened
telescope's depth. -/
theorem checkIotaThm_wfimp {env' envSelf : Env} (henv' : EnvWF env')
    (henvSelf : EnvWF envSelf) {f : Name → Name} {cvName : Name}
    {lps : List Name} {tyA : Expr} {mI rP j : Nat} {r : RecRule}
    {cvj : ConstantVal} {cnP cnF : Nat} {rhsA : Expr} {F : Nat}
    {v : Unit}
    (htyA : tyA.hasFvar = false) (hctor : cvj.type.hasFvar = false)
    (hrhsA : rhsA.hasFvar = false)
    (h : (checkIotaThm mode (wfOpsM mode) env' envSelf f cvName lps tyA
      mI rP j r cvj cnP cnF rhsA).val F = .ok v) :
    checkIotaThm mode (fueledOps mode F) env' envSelf f cvName lps tyA
      mI rP j r cvj cnP cnF rhsA = .ok v := by
  unfold checkIotaThm at h ⊢
  try dsimp only [] at h ⊢
  obtain ⟨cvt, hthm, h⟩ := atF_bind_ok h
  have hthm' := unwrapOr_atF_ok hthm
  show ((unwrapOr (env'.findCV?
    ((cvName.str "_model").str s!"iota_{j}")) _ : CheckM _) >>= _) = _
  rw [hthm']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  -- the stored constant's statement is closed (kind-agnostic)
  have hcvtF : cvt.type.hasFvar = false := by
    obtain ⟨ci, hci, hcvt⟩ := findCV?_ok hthm'
    exact hcvt ▸ (henv' _ (find?_mem hci)).1
  by_cases h1 : cvt.levelParams = lps
  case neg => rw [if_neg h1] at h; exact absurd h atF_throw_bind
  rw [if_pos h1] at h ⊢
  obtain ⟨q, hopen, h⟩ := atF_bind_ok h
  obtain ⟨fvs, tbody⟩ := q
  have hopen' := unwrapOr_atF_ok hopen
  show ((unwrapOr (openPisAtFvars (rP + cnF) cvt.type 0) _ :
    CheckM _) >>= _) = _
  rw [hopen']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  -- scoping of the opened telescope
  have hopenW := openPisAtFvars_WScoped (rP + cnF) cvt.type 0
    hopen' (WScoped.of_not_hasFvar hcvtF)
  rw [Nat.zero_add] at hopenW
  obtain ⟨hfvsW, htbodyW⟩ := hopenW
  have htargsW : ∀ x ∈ tbody.getAppArgs,
      WScoped (rP + cnF) x := Expr.WScoped.getAppArgs htbodyW
  have hlhsW : WScoped (rP + cnF)
      (tbody.getAppArgs.getD 1 (.bvar 0)) := WScoped_getD' htargsW 1
  have hrhsSW : WScoped (rP + cnF)
      (tbody.getAppArgs.getD 2 (.bvar 0)) := WScoped_getD' htargsW 2
  have hlargsW : ∀ x ∈ (tbody.getAppArgs.getD 1 (.bvar 0)).getAppArgs,
      WScoped (rP + cnF) x := Expr.WScoped.getAppArgs hlhsW
  by_cases h2 : isEqHead tbody.getAppFn = true
  case neg => rw [if_neg h2] at h; exact absurd h atF_throw_bind
  rw [if_pos h2] at h ⊢
  by_cases h3 : tbody.getAppArgs.length = 3
  case neg => rw [if_neg h3] at h; exact absurd h atF_throw_bind
  rw [if_pos h3] at h ⊢
  try dsimp only [] at h ⊢
  by_cases h4 : ((tbody.getAppArgs.getD 1 (.bvar 0)).getAppFn ==
      Expr.const (f cvName) (lps.map .param)) = true
  case neg => rw [if_neg h4] at h; exact absurd h atF_throw_bind
  rw [if_pos h4] at h ⊢
  by_cases h5 : (tbody.getAppArgs.getD 1 (.bvar 0)).getAppArgs.length =
      mI + 1
  case neg => rw [if_neg h5] at h; exact absurd h atF_throw_bind
  rw [if_pos h5] at h ⊢
  by_cases h6 : ((tbody.getAppArgs.getD 1
      (.bvar 0)).getAppArgs.take rP ==
      fvs.take rP) = true
  case neg => rw [if_neg h6] at h; exact absurd h atF_throw_bind
  rw [if_pos h6] at h ⊢
  by_cases h7 : ((tbody.getAppArgs.getD 1
      (.bvar 0)).getAppArgs.getLastD (.bvar 0) ==
      Expr.mkAppN (.const (f r.ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop rP)) = true
  case neg => rw [if_neg h7] at h; exact absurd h atF_throw_bind
  rw [if_pos h7] at h ⊢
  by_cases h8 : (cvj.type.stripPis (cnP + cnF)).isSome = true
  case neg => rw [if_neg h8] at h; exact absurd h atF_throw_bind
  rw [if_pos h8] at h ⊢
  obtain ⟨q2, hcinst, h⟩ := atF_bind_ok h
  obtain ⟨cdoms, cres⟩ := q2
  have hcinst' := unwrapOr_atF_ok hcinst
  show ((unwrapOr (Expr.instPisAt (fvs.take cnP ++
    fvs.drop rP) (cvj.type.renameConsts f)) _ :
    CheckM _) >>= _) = _
  rw [hcinst']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hcargW : ∀ a ∈ fvs.take cnP ++ fvs.drop rP,
      WScoped (rP + cnF) a := by
    intro a hax
    rcases List.mem_append.mp hax with hax | hax
    · exact hfvsW a (List.mem_of_mem_take hax)
    · exact hfvsW a (List.mem_of_mem_drop hax)
  have hcinstW := instPisAt_WScoped _ _ hcinst'
    (WScoped.of_not_hasFvar (by
      rw [hasFvar_renameConsts]
      exact hctor)) hcargW
  obtain ⟨hcdomsW, hcresW⟩ := hcinstW
  by_cases h9 : cres.getAppArgs.length = cnP + (mI - rP)
  case neg => rw [if_neg h9] at h; exact absurd h atF_throw_bind
  rw [if_pos h9] at h ⊢
  obtain ⟨u1, hd1, h⟩ := atF_bind_ok h
  have hd1' := checkDefEqList_wfimp henvSelf
    (fun a ha => hlargsW a
      (List.mem_of_mem_drop (List.mem_of_mem_take ha)))
    (fun b hb => Expr.WScoped.getAppArgs hcresW b
      (List.mem_of_mem_drop hb)) hd1
  show (checkDefEqList (fueledOps mode F) envSelf _ _ _ >>= _) = _
  rw [hd1']
  simp only [Bind.bind, Except.bind]
  obtain ⟨u2, hd2, h⟩ := atF_bind_ok h
  have hd2' := checkDefEqList_wfimp henvSelf
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact fvarTypeD_WScoped (hfvsW x (List.mem_of_mem_drop hx)))
    (fun b hb => hcdomsW b (List.mem_of_mem_drop hb)) hd2
  show (checkDefEqList (fueledOps mode F) envSelf _ _ _ >>= _) = _
  rw [hd2']
  simp only [Bind.bind, Except.bind]
  obtain ⟨q3, hrinst, h⟩ := atF_bind_ok h
  obtain ⟨rdoms, rrest⟩ := q3
  have hrinst' := unwrapOr_atF_ok hrinst
  show ((unwrapOr (Expr.instPisAt (fvs.take rP)
    (tyA.renameConsts f)) _ : CheckM _) >>= _) = _
  rw [hrinst']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hrinstW := instPisAt_WScoped _ _ hrinst'
    (WScoped.of_not_hasFvar (by
      rw [hasFvar_renameConsts]
      exact htyA))
    (fun a ha => hfvsW a (List.mem_of_mem_take ha))
  obtain ⟨hrdomsW, -⟩ := hrinstW
  obtain ⟨u3, hd3, h⟩ := atF_bind_ok h
  have hd3' := checkDefEqList_wfimp henvSelf
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact fvarTypeD_WScoped (hfvsW x (List.mem_of_mem_take hx)))
    (fun b hb => hrdomsW b hb) hd3
  show (checkDefEqList (fueledOps mode F) envSelf _ _ _ >>= _) = _
  rw [hd3']
  simp only [Bind.bind, Except.bind]
  obtain ⟨q4, hopenP, h⟩ := atF_bind_ok h
  obtain ⟨fvsP, restP⟩ := q4
  have hopenP' := unwrapOr_atF_ok hopenP
  show ((unwrapOr (openPisAtFvars rP tyA 0) _ :
    CheckM _) >>= _) = _
  rw [hopenP']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hopenPW := openPisAtFvars_WScoped rP tyA 0 hopenP'
    (WScoped.of_not_hasFvar htyA)
  rw [Nat.zero_add] at hopenPW
  obtain ⟨hfvsPW, -⟩ := hopenPW
  obtain ⟨q5, hcinstP, h⟩ := atF_bind_ok h
  obtain ⟨cdomsP, crestP⟩ := q5
  have hcinstP' := unwrapOr_atF_ok hcinstP
  show ((unwrapOr (Expr.instPisAt (fvsP.take cnP) cvj.type) _ :
    CheckM _) >>= _) = _
  rw [hcinstP']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hcinstPW := instPisAt_WScoped (d := rP) _ _ hcinstP'
    (WScoped.of_not_hasFvar hctor)
    (fun a ha => hfvsPW a (List.mem_of_mem_take ha))
  obtain ⟨hcdomsPW, hcrestPW⟩ := hcinstPW
  obtain ⟨uP, hdP, h⟩ := atF_bind_ok h
  have hdP' := checkDefEqList_wfimp henvSelf
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact (fvarTypeD_WScoped
        (hfvsPW x (List.mem_of_mem_take hx))).mono (by omega))
    (fun b hb => (hcdomsPW b hb).mono (by omega)) hdP
  show (checkDefEqList (fueledOps mode F) envSelf _ _ _ >>= _) = _
  rw [hdP']
  simp only [Bind.bind, Except.bind]
  obtain ⟨q6, hopenX, h⟩ := atF_bind_ok h
  obtain ⟨xFvsP, crest2⟩ := q6
  have hopenX' := unwrapOr_atF_ok hopenX
  show ((unwrapOr (openPisAtFvars cnF crestP rP) _ :
    CheckM _) >>= _) = _
  rw [hopenX']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hopenXW := openPisAtFvars_WScoped cnF crestP rP
    hopenX' hcrestPW
  obtain ⟨hxFvsPW, -⟩ := hopenXW
  have hfvsPW' : ∀ a ∈ fvsP ++ xFvsP, WScoped (rP + cnF) a := by
    intro a hax
    rcases List.mem_append.mp hax with hax | hax
    · exact WScoped.mono (by omega) (hfvsPW a hax)
    · exact hxFvsPW a hax
  obtain ⟨q7, hlinst, h⟩ := atF_bind_ok h
  obtain ⟨ldoms, lrest⟩ := q7
  have hlinst' := unwrapOr_atF_ok hlinst
  show ((unwrapOr (Expr.instLamsAt (fvsP ++ xFvsP) rhsA) _ :
    CheckM _) >>= _) = _
  rw [hlinst']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hlinstW := instLamsAt_WScoped _ _ hlinst'
    (WScoped.of_not_hasFvar hrhsA) hfvsPW'
  obtain ⟨hldomsW, -⟩ := hlinstW
  obtain ⟨u4, hd4, h⟩ := atF_bind_ok h
  have hd4' := checkDefEqList_wfimp henvSelf
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact fvarTypeD_WScoped (hfvsPW' x hx))
    (fun b hb => hldomsW b hb) hd4
  show (checkDefEqList (fueledOps mode F) envSelf _ _ _ >>= _) = _
  rw [hd4']
  simp only [Bind.bind, Except.bind]
  rw [wfOpsM_isDefEq henvSelf hrhsSW.to_wscopedB
    (Expr.WScoped.mkAppN
      (WScoped.of_not_hasFvar (by
        rw [hasFvar_renameConsts]
        exact hrhsA))
      (fun x hx => hfvsW x hx)).to_wscopedB] at h
  obtain ⟨c, hde, h⟩ := atF_bind_ok h
  have hde' : isDefEqCore mode envSelf F (rP + cnF)
      (tbody.getAppArgs.getD 2 (.bvar 0))
      (Expr.mkAppN (rhsA.renameConsts f) fvs) = .ok c := hde
  show (isDefEqCore mode envSelf F _ _ _ >>= _) = _
  rw [hde']
  simp only [Bind.bind, Except.bind]
  cases c with
  | false =>
    rw [if_neg (by simp)] at h
    exact nomatch h
  | true =>
    rw [if_pos rfl] at h ⊢
    have hαSW : WScoped (rP + cnF)
        (tbody.getAppArgs.getD 0 (.bvar 0)) := WScoped_getD' htargsW 0
    exact checkIotaSidesTy_wfimp henvSelf hαSW hlhsW hrhsSW h

/-- A successful `nestedRuleShape` guards its stored parameter
instantiations: they are fvar-free. -/
theorem nestedRuleShape_pins {env' envSelf : Env} {cvName : Name}
    {lps : List Name} {tyA : Expr} {mI rP cnP j : Nat}
    {lvls : List Level} {pins : List Expr}
    (h : nestedRuleShape env' envSelf cvName lps tyA mI rP cnP j =
      some (lvls, pins)) :
    ∀ p ∈ pins, p.hasFvar = false := by
  intro p hp
  simp only [nestedRuleShape] at h
  repeat split at h
  all_goals try (simp at h; done)
  rename_i hcond
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have hall := List.all_eq_true.mp hcond.2.2.2.1 p hp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hall
  exact hall.1.1.1

set_option maxHeartbeats 6400000 in
/-- The nested-auxiliary iota-theorem check, `wfOpsM mode` run to pure run:
`checkIotaThm_wfimp` with the constructor's parameters and levels
fixed at the stored instantiations. -/
theorem checkIotaThmN_wfimp {env' envSelf : Env} (henv' : EnvWF env')
    (henvSelf : EnvWF envSelf) {f : Name → Name} {cvName : Name}
    {lps : List Name} {tyA : Expr} {mI rP j : Nat} {r : RecRule}
    {cvj : ConstantVal} {cnP cnF : Nat} {rhsA : Expr} {F : Nat}
    {v : RecRuleFire}
    (htyA : tyA.hasFvar = false) (hctor : cvj.type.hasFvar = false)
    (hrhsA : rhsA.hasFvar = false)
    (h : (checkIotaThmN mode (wfOpsM mode) env' envSelf f cvName lps tyA
      mI rP j r cvj cnP cnF rhsA).val F = .ok v) :
    checkIotaThmN mode (fueledOps mode F) env' envSelf f cvName lps tyA
      mI rP j r cvj cnP cnF rhsA = .ok v := by
  unfold checkIotaThmN at h ⊢
  revert h
  cases hshape : nestedRuleShape env' envSelf cvName lps tyA mI rP
      cnP j with
  | none => intro h; exact h
  | some q =>
  obtain ⟨lvls, pins⟩ := q
  intro h
  try dsimp only [] at h ⊢
  have hpinsF : ∀ p ∈ pins, p.hasFvar = false :=
    nestedRuleShape_pins hshape
  obtain ⟨cvt, hthm, h⟩ := atF_bind_ok h
  have hthm' := unwrapOr_atF_ok hthm
  show ((unwrapOr (env'.findCV?
    ((cvName.str "_model").str s!"iota_{j}")) _ : CheckM _) >>= _) = _
  rw [hthm']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  -- the stored constant's statement is closed (kind-agnostic)
  have hcvtF : cvt.type.hasFvar = false := by
    obtain ⟨ci, hci, hcvt⟩ := findCV?_ok hthm'
    exact hcvt ▸ (henv' _ (find?_mem hci)).1
  by_cases h1 : cvt.levelParams = lps
  case neg => rw [if_neg h1] at h; exact absurd h atF_throw_bind
  rw [if_pos h1] at h ⊢
  obtain ⟨q, hopen, h⟩ := atF_bind_ok h
  obtain ⟨fvs, tbody⟩ := q
  have hopen' := unwrapOr_atF_ok hopen
  show ((unwrapOr (openPisAtFvars (rP + cnF) cvt.type 0) _ :
    CheckM _) >>= _) = _
  rw [hopen']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  -- scoping of the opened telescope
  have hopenW := openPisAtFvars_WScoped (rP + cnF) cvt.type 0
    hopen' (WScoped.of_not_hasFvar hcvtF)
  rw [Nat.zero_add] at hopenW
  obtain ⟨hfvsW, htbodyW⟩ := hopenW
  have htargsW : ∀ x ∈ tbody.getAppArgs,
      WScoped (rP + cnF) x := Expr.WScoped.getAppArgs htbodyW
  have hlhsW : WScoped (rP + cnF)
      (tbody.getAppArgs.getD 1 (.bvar 0)) := WScoped_getD' htargsW 1
  have hrhsSW : WScoped (rP + cnF)
      (tbody.getAppArgs.getD 2 (.bvar 0)) := WScoped_getD' htargsW 2
  have hlargsW : ∀ x ∈ (tbody.getAppArgs.getD 1 (.bvar 0)).getAppArgs,
      WScoped (rP + cnF) x := Expr.WScoped.getAppArgs hlhsW
  by_cases h2 : isEqHead tbody.getAppFn = true
  case neg => rw [if_neg h2] at h; exact absurd h atF_throw_bind
  rw [if_pos h2] at h ⊢
  by_cases h3 : tbody.getAppArgs.length = 3
  case neg => rw [if_neg h3] at h; exact absurd h atF_throw_bind
  rw [if_pos h3] at h ⊢
  try dsimp only [] at h ⊢
  by_cases h4 : ((tbody.getAppArgs.getD 1 (.bvar 0)).getAppFn ==
      Expr.const (f cvName) (lps.map .param)) = true
  case neg => rw [if_neg h4] at h; exact absurd h atF_throw_bind
  rw [if_pos h4] at h ⊢
  by_cases h5 : (tbody.getAppArgs.getD 1 (.bvar 0)).getAppArgs.length =
      mI + 1
  case neg => rw [if_neg h5] at h; exact absurd h atF_throw_bind
  rw [if_pos h5] at h ⊢
  by_cases h6 : ((tbody.getAppArgs.getD 1
      (.bvar 0)).getAppArgs.take rP ==
      fvs.take rP) = true
  case neg => rw [if_neg h6] at h; exact absurd h atF_throw_bind
  rw [if_pos h6] at h ⊢
  by_cases h7 : (((tbody.getAppArgs.getD 1
      (.bvar 0)).getAppArgs.getLastD (.bvar 0))
      == (Expr.mkAppN (.const (f r.ctor) lvls)
        (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts f)) ++ fvs.drop rP))) = true
  case neg => rw [if_neg h7] at h; exact absurd h atF_throw_bind
  rw [if_pos h7] at h ⊢
  obtain ⟨q8, hstrip8, h⟩ := atF_bind_ok h
  obtain ⟨bs8, cbody8⟩ := q8
  have hstrip8' := unwrapOr_atF_ok hstrip8
  show ((unwrapOr (cvj.type.stripPis (cnP + cnF)) _ :
    CheckM _) >>= _) = _
  rw [hstrip8']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  obtain ⟨Dc, usc, hfnC⟩ : ∃ Dc usc,
      cbody8.getAppFn = Expr.const Dc usc := by
    revert h
    cases hfn0 : cbody8.getAppFn <;> intro h
    case const => exact ⟨_, _, rfl⟩
    all_goals
      rw [if_neg (by simp)] at h
      exact absurd h atF_throw_bind
  rw [hfnC] at h ⊢
  rw [if_pos rfl] at h ⊢
  try dsimp only [] at h ⊢
  obtain ⟨q2, hcinst, h⟩ := atF_bind_ok h
  obtain ⟨cdoms, cres⟩ := q2
  have hcinst' := unwrapOr_atF_ok hcinst
  show ((unwrapOr (Expr.instPisAt
    (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
      (p.renameConsts f)) ++ fvs.drop rP)
    ((cvj.type.instantiateLevelParams cvj.levelParams
      lvls).renameConsts f)) _ : CheckM _) >>= _) = _
  rw [hcinst']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hcargW : ∀ a ∈ pins.map (fun p =>
      Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)) ++
      fvs.drop rP, WScoped (rP + cnF) a := by
    intro a hax
    rcases List.mem_append.mp hax with hax | hax
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hax
      exact instSpine_WScoped (rP - 1)
        (WScoped.of_not_hasFvar (by
          rw [hasFvar_renameConsts]
          exact hpinsF x hx))
        (fun a' ha' => hfvsW a' (List.mem_of_mem_take ha'))
    · exact hfvsW a (List.mem_of_mem_drop hax)
  have hcinstW := instPisAt_WScoped _ _ hcinst'
    (WScoped.of_not_hasFvar (by
      rw [hasFvar_renameConsts, hasFvar_instantiateLevelParams]
      exact hctor)) hcargW
  obtain ⟨hcdomsW, hcresW⟩ := hcinstW
  by_cases h9 : cres.getAppArgs.length = cnP + (mI - rP)
  case neg => rw [if_neg h9] at h; exact absurd h atF_throw_bind
  rw [if_pos h9] at h ⊢
  obtain ⟨u1, hd1, h⟩ := atF_bind_ok h
  have hd1' := checkDefEqList_wfimp henvSelf
    (fun a ha => hlargsW a
      (List.mem_of_mem_drop (List.mem_of_mem_take ha)))
    (fun b hb => Expr.WScoped.getAppArgs hcresW b
      (List.mem_of_mem_drop hb)) hd1
  show (checkDefEqList (fueledOps mode F) envSelf _ _ _ >>= _) = _
  rw [hd1']
  simp only [Bind.bind, Except.bind]
  obtain ⟨u2, hd2, h⟩ := atF_bind_ok h
  have hd2' := checkDefEqList_wfimp henvSelf
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact fvarTypeD_WScoped (hfvsW x (List.mem_of_mem_drop hx)))
    (fun b hb => hcdomsW b (List.mem_of_mem_drop hb)) hd2
  show (checkDefEqList (fueledOps mode F) envSelf _ _ _ >>= _) = _
  rw [hd2']
  simp only [Bind.bind, Except.bind]
  obtain ⟨q3, hrinst, h⟩ := atF_bind_ok h
  obtain ⟨rdoms, rrest⟩ := q3
  have hrinst' := unwrapOr_atF_ok hrinst
  show ((unwrapOr (Expr.instPisAt (fvs.take rP)
    (tyA.renameConsts f)) _ : CheckM _) >>= _) = _
  rw [hrinst']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hrinstW := instPisAt_WScoped _ _ hrinst'
    (WScoped.of_not_hasFvar (by
      rw [hasFvar_renameConsts]
      exact htyA))
    (fun a ha => hfvsW a (List.mem_of_mem_take ha))
  obtain ⟨hrdomsW, -⟩ := hrinstW
  obtain ⟨u3, hd3, h⟩ := atF_bind_ok h
  have hd3' := checkDefEqList_wfimp henvSelf
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact fvarTypeD_WScoped (hfvsW x (List.mem_of_mem_take hx)))
    (fun b hb => hrdomsW b hb) hd3
  show (checkDefEqList (fueledOps mode F) envSelf _ _ _ >>= _) = _
  rw [hd3']
  simp only [Bind.bind, Except.bind]
  obtain ⟨q4, hopenP, h⟩ := atF_bind_ok h
  obtain ⟨fvsP, restP⟩ := q4
  have hopenP' := unwrapOr_atF_ok hopenP
  show ((unwrapOr (openPisAtFvars rP tyA 0) _ :
    CheckM _) >>= _) = _
  rw [hopenP']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hopenPW := openPisAtFvars_WScoped rP tyA 0 hopenP'
    (WScoped.of_not_hasFvar htyA)
  rw [Nat.zero_add] at hopenPW
  obtain ⟨hfvsPW, -⟩ := hopenPW
  obtain ⟨uA, hdA, h⟩ := atF_bind_ok h
  have hdA' := checkAnnotList_wfimp henvSelf
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact (instSpine_WScoped (rP - 1)
        (WScoped.of_not_hasFvar (hpinsF x hx))
        (fun a' ha' => hfvsPW a' (List.mem_of_mem_take ha'))).mono
        (by omega)) hdA
  show (checkAnnotList (fueledOps mode F) envSelf _ _ >>= _) = _
  rw [hdA']
  simp only [Bind.bind, Except.bind]
  obtain ⟨q5, hcinstP, h⟩ := atF_bind_ok h
  obtain ⟨cdomsP, crestP⟩ := q5
  have hcinstP' := unwrapOr_atF_ok hcinstP
  show ((unwrapOr (Expr.instPisAt
    (pins.map (fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p))
    (cvj.type.instantiateLevelParams cvj.levelParams lvls)) _ :
    CheckM _) >>= _) = _
  rw [hcinstP']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hcinstPW := instPisAt_WScoped (d := rP) _ _ hcinstP'
    (WScoped.of_not_hasFvar (by
      rw [hasFvar_instantiateLevelParams]
      exact hctor))
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact instSpine_WScoped (rP - 1)
        (WScoped.of_not_hasFvar (hpinsF x hx))
        (fun a' ha' => hfvsPW a' (List.mem_of_mem_take ha')))
  obtain ⟨hcdomsPW, hcrestPW⟩ := hcinstPW
  obtain ⟨uP, hdP, h⟩ := atF_bind_ok h
  have hdP' := checkTypedList_wfimp henvSelf
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact (instSpine_WScoped (rP - 1)
        (WScoped.of_not_hasFvar (hpinsF x hx))
        (fun a' ha' => hfvsPW a' (List.mem_of_mem_take ha'))).mono
        (by omega))
    (fun b hb => (hcdomsPW b hb).mono (by omega)) hdP
  show (checkTypedList (fueledOps mode F) envSelf _ _ _ >>= _) = _
  rw [hdP']
  simp only [Bind.bind, Except.bind]
  obtain ⟨q6, hopenX, h⟩ := atF_bind_ok h
  obtain ⟨xFvsP, crest2⟩ := q6
  have hopenX' := unwrapOr_atF_ok hopenX
  show ((unwrapOr (openPisAtFvars cnF crestP rP) _ :
    CheckM _) >>= _) = _
  rw [hopenX']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hopenXW := openPisAtFvars_WScoped cnF crestP rP
    hopenX' hcrestPW
  obtain ⟨hxFvsPW, -⟩ := hopenXW
  have hfvsPW' : ∀ a ∈ fvsP ++ xFvsP, WScoped (rP + cnF) a := by
    intro a hax
    rcases List.mem_append.mp hax with hax | hax
    · exact WScoped.mono (by omega) (hfvsPW a hax)
    · exact hxFvsPW a hax
  by_cases harX : (crest2.getAppArgs.length == cnP + (mI - rP)) = true
  case neg => rw [if_neg harX] at h; exact absurd h atF_throw_bind
  rw [if_pos harX] at h ⊢
  try dsimp only [] at h ⊢
  obtain ⟨q7, hlinst, h⟩ := atF_bind_ok h
  obtain ⟨ldoms, lrest⟩ := q7
  have hlinst' := unwrapOr_atF_ok hlinst
  show ((unwrapOr (Expr.instLamsAt (fvsP ++ xFvsP) rhsA) _ :
    CheckM _) >>= _) = _
  rw [hlinst']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hlinstW := instLamsAt_WScoped _ _ hlinst'
    (WScoped.of_not_hasFvar hrhsA) hfvsPW'
  obtain ⟨hldomsW, -⟩ := hlinstW
  obtain ⟨u4, hd4, h⟩ := atF_bind_ok h
  have hd4' := checkDefEqList_wfimp henvSelf
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact fvarTypeD_WScoped (hfvsPW' x hx))
    (fun b hb => hldomsW b hb) hd4
  show (checkDefEqList (fueledOps mode F) envSelf _ _ _ >>= _) = _
  rw [hd4']
  simp only [Bind.bind, Except.bind]
  rw [wfOpsM_isDefEq henvSelf hrhsSW.to_wscopedB
    (Expr.WScoped.mkAppN
      (WScoped.of_not_hasFvar (by
        rw [hasFvar_renameConsts]
        exact hrhsA))
      (fun x hx => hfvsW x hx)).to_wscopedB] at h
  obtain ⟨c, hde, h⟩ := atF_bind_ok h
  have hde' : isDefEqCore mode envSelf F (rP + cnF)
      (tbody.getAppArgs.getD 2 (.bvar 0))
      (Expr.mkAppN (rhsA.renameConsts f) fvs) = .ok c := hde
  show (isDefEqCore mode envSelf F _ _ _ >>= _) = _
  rw [hde']
  simp only [Bind.bind, Except.bind]
  cases c with
  | false =>
    rw [if_neg (by simp)] at h
    exact nomatch h
  | true =>
    rw [if_pos rfl] at h ⊢
    have hαSW : WScoped (rP + cnF)
        (tbody.getAppArgs.getD 0 (.bvar 0)) := WScoped_getD' htargsW 0
    obtain ⟨u9, hcert, h⟩ := atF_bind_ok h
    have hcert' := checkIotaSidesTy_wfimp henvSelf hαSW hlhsW hrhsSW hcert
    show (checkIotaSidesTy mode (fueledOps mode F) envSelf (rP + cnF) _ _ _ _ _ >>= _)
      = _
    rw [hcert']
    simp only [Bind.bind, Except.bind]
    exact h

theorem checkIotaRule_wfimp {env' envSelf : Env} (henv' : EnvWF env')
    (henvSelf : EnvWF envSelf) {f : Name → Name} {cvName : Name}
    {lps : List Name} {tyA : Expr} {mI rP j : Nat} {r : RecRule}
    {F : Nat} {v : RecRule} (htyA : tyA.hasFvar = false)
    (h : (checkIotaRule mode (wfOpsM mode) env' envSelf f cvName lps tyA
      mI rP j r).val F = .ok v) :
    checkIotaRule mode (fueledOps mode F) env' envSelf f cvName lps tyA
      mI rP j r = .ok v := by
  unfold checkIotaRule at h ⊢
  dsimp only [] at h ⊢
  revert h
  match hf : env'.find? r.ctor with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.ctorInfo cvj cnP cnF) => ?_
  intro h
  dsimp only [] at h ⊢
  by_cases h2 : r.nfields = cnF
  case neg => rw [if_neg h2] at h; exact absurd h atF_throw_bind
  rw [if_pos h2] at h ⊢
  by_cases h3 : Expr.looseBVarsBounded 0 (RecRule.rhs r) = true
  case neg => rw [if_neg h3] at h; exact absurd h atF_throw_bind
  rw [if_pos h3] at h ⊢
  by_cases h4 : (RecRule.rhs r).hasFvar = true
  · rw [if_pos h4] at h; exact absurd h atF_throw_bind
  rw [if_neg h4] at h ⊢
  rw [wfOpsM_annotate henvSelf
    (wscopedB_of_not_hasFvar (Bool.not_eq_true _ ▸ h4))] at h
  obtain ⟨rhsA, hann, h⟩ := atF_bind_ok h
  have hann' : annotateCore mode envSelf F 0 (RecRule.rhs r) = .ok rhsA := hann
  show (annotateCore mode envSelf F 0 (RecRule.rhs r) >>= _) = _
  rw [hann']
  simp only [Bind.bind, Except.bind]
  have hwrhsA : WScoped 0 rhsA := annotateCore_WScoped F _ hann'
    (WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h4))
  have hrhsAF : rhsA.hasFvar = false :=
    not_hasFvar_of_fvarsBelow_zero hwrhsA.fvarsBelow
  by_cases h5 : Expr.allLevelParamsDefined lps rhsA = true
  case neg => rw [if_neg h5] at h; exact absurd h atF_throw_bind
  rw [if_pos h5] at h ⊢
  by_cases h6 : Expr.constsResolve envSelf rhsA = true
  case neg => rw [if_neg h6] at h; exact absurd h atF_throw_bind
  rw [if_pos h6] at h ⊢
  by_cases h7 : (rhsA.stripLams (rP + cnF)).isSome = true
  case neg => rw [if_neg h7] at h; exact absurd h atF_throw_bind
  rw [if_pos h7] at h ⊢
  rw [wfOpsM_inferType henvSelf hwrhsA.to_wscopedB] at h
  obtain ⟨rhsTy, hity, h⟩ := atF_bind_ok h
  have hity' : inferTypeCore mode envSelf F 0 rhsA = .ok rhsTy := hity
  show (inferTypeCore mode envSelf F 0 rhsA >>= _) = _
  rw [hity']
  simp only [Bind.bind, Except.bind]
  by_cases h8 : Expr.recRulePlain tyA mI rP cnP = true
  case neg =>
    rw [if_neg h8] at h ⊢
    obtain ⟨fire, hthmN, h⟩ := atF_bind_ok h
    have hthmN' := checkIotaThmN_wfimp henv' henvSelf htyA
      (show cvj.type.hasFvar = false from (henv' _ (find?_mem hf)).1)
      hrhsAF hthmN
    show (checkIotaThmN mode (fueledOps mode F) env' envSelf f cvName lps tyA
      mI rP j r cvj cnP cnF rhsA >>= _) = _
    rw [hthmN']
    simp only [Bind.bind, Except.bind]
    exact h
  rw [if_pos h8] at h ⊢
  obtain ⟨u, hthm, h⟩ := atF_bind_ok h
  have hthm' := checkIotaThm_wfimp henv' henvSelf htyA
    (show cvj.type.hasFvar = false from (henv' _ (find?_mem hf)).1)
    hrhsAF hthm
  show (checkIotaThm mode (fueledOps mode F) env' envSelf f cvName lps tyA
    mI rP j r cvj cnP cnF rhsA >>= _) = _
  rw [hthm']
  simp only [Bind.bind, Except.bind]
  exact h

theorem checkIotaRules_wfimp {env' envSelf : Env} (henv' : EnvWF env')
    (henvSelf : EnvWF envSelf) {f : Name → Name} {cvName : Name}
    {lps : List Name} {tyA : Expr} {mI rP : Nat} {F : Nat}
    (htyA : tyA.hasFvar = false) :
    ∀ {j : Nat} {rules rules' : List RecRule},
      (checkIotaRules mode (wfOpsM mode) env' envSelf f cvName lps tyA
        mI rP j rules).val F = .ok rules' →
      checkIotaRules mode (fueledOps mode F) env' envSelf f cvName lps tyA
        mI rP j rules = .ok rules'
  | _, [], rules', h => h
  | j, r :: rest, rules', h => by
    unfold checkIotaRules at h ⊢
    obtain ⟨r', hr, h⟩ := atF_bind_ok h
    have hr' := checkIotaRule_wfimp henv' henvSelf htyA hr
    show (checkIotaRule mode (fueledOps mode F) env' envSelf f cvName lps tyA
      mI rP j r >>= _) = _
    rw [hr']
    simp only [Bind.bind, Except.bind]
    obtain ⟨rest', hrest, h⟩ := atF_bind_ok h
    have hrest' := checkIotaRules_wfimp henv' henvSelf htyA hrest
    show (checkIotaRules mode (fueledOps mode F) env' envSelf f cvName lps tyA
      mI rP (j + 1) rest >>= _) = _
    rw [hrest']
    simp only [Bind.bind, Except.bind]
    exact h

/-- The member-against-model check, `wfOpsM mode` run to pure run. -/
theorem checkMemberVal_wfimp {blockNames : List Name} {env' : Env}
    (henv' : EnvWF env') {cv : ConstantVal} {F : Nat} {v : ConstantVal}
    (h : (checkMemberVal (wfOpsM mode) blockNames env' cv).val F = .ok v) :
    checkMemberVal (fueledOps mode F) blockNames env' cv = .ok v := by
  unfold checkMemberVal at h ⊢
  dsimp only [] at h ⊢
  obtain ⟨cvA, hccvW, h⟩ := atF_bind_ok h
  have hccv := checkConstantVal_wfimp henv' hccvW
  show (checkConstantVal (fueledOps mode F) env' cv >>= _) = _
  rw [hccv]
  simp only [Bind.bind, Except.bind]
  by_cases h1 : cvA.name.isModelSuffix = true
  · rw [if_pos h1] at h
    exact absurd h atF_throw_bind
  rw [if_neg h1] at h ⊢
  revert h
  match hm : env'.find? (cvA.name.str "_model") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cvm mval mhint) => ?_
  intro h
  dsimp only [] at h ⊢
  by_cases h2 : cvm.levelParams = cvA.levelParams
  case neg => rw [if_neg h2] at h; exact absurd h atF_throw_bind
  rw [if_pos h2] at h ⊢
  by_cases h3 : ((cvA.type.renameConsts
      (fun n => if blockNames.contains n then n.str "_model" else n))
      == cvm.type) = true
  case neg => rw [if_neg h3] at h; exact absurd h atF_throw_bind
  rw [if_pos h3] at h ⊢
  exact h

theorem checkProjRule_wfimp {env' : Env} (henv' : EnvWF env')
    {pty : Expr} {cvj : ConstantVal} {lps : List Name}
    {nP nF i F : Nat} {v : Expr}
    (hptyf : pty.hasFvar = false)
    (_hptyb : pty.looseBVarsBounded 0 = true)
    (hCf : cvj.type.hasFvar = false)
    (_hCb : cvj.type.looseBVarsBounded 0 = true)
    (h : (checkProjRule (wfOpsM mode) env' pty cvj lps nP nF i).val F = .ok v) :
    checkProjRule (fueledOps mode F) env' pty cvj lps nP nF i = .ok v := by
  unfold checkProjRule at h ⊢
  dsimp only [] at h ⊢
  revert h
  match hrhs : Expr.pisToLams (nP + nF) cvj.type (.bvar (nF - 1 - i)) with
  | none => intro h; exact nomatch h
  | some rhs => ?_
  intro h
  dsimp only [] at h ⊢
  by_cases h1 : (!rhs.hasFvar && Expr.looseBVarsBounded 0 rhs) = true
  case neg => rw [if_neg h1] at h; exact absurd h atF_throw_bind
  rw [if_pos h1] at h ⊢
  have hrf : rhs.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
    exact h1.1
  rw [wfOpsM_annotate henv' (wscopedB_of_not_hasFvar hrf)] at h
  obtain ⟨rhsA, hann, h⟩ := atF_bind_ok h
  have hann' : annotateCore mode env' F 0 rhs = .ok rhsA := hann
  show (annotateCore mode env' F 0 rhs >>= _) = _
  rw [hann']
  simp only [Bind.bind, Except.bind]
  by_cases h2 : (Expr.allLevelParamsDefined lps rhsA &&
      Expr.constsResolve env' rhsA && Expr.looseBVarsBounded 0 rhsA &&
      !rhsA.hasFvar) = true
  case neg => rw [if_neg h2] at h; exact absurd h atF_throw_bind
  rw [if_pos h2] at h ⊢
  revert h
  match hstrip : rhsA.stripLams (nP + nF) with
  | none => intro h; exact nomatch h
  | some pr₁ => ?_
  obtain ⟨rbinders, rrbody⟩ := pr₁
  intro h
  try dsimp only [] at h ⊢
  by_cases h3 : (rrbody == Expr.bvar (nF - 1 - i)) = true
  case neg => rw [if_neg h3] at h; exact absurd h atF_throw_bind
  rw [if_pos h3] at h ⊢
  revert h
  match hstripC : cvj.type.stripPis (nP + nF) with
  | none => intro h; exact nomatch h
  | some pr₂ => ?_
  obtain ⟨cbindersR, cbodyR⟩ := pr₂
  intro h
  try dsimp only [] at h ⊢
  by_cases h4 : domsMatchAux (fun _ e => e) rbinders cbindersR 0 0
      (nP + nF) = true
  case neg => rw [if_neg h4] at h; exact absurd h atF_throw_bind
  rw [if_pos h4] at h ⊢
  -- the frame walks and pins
  revert h
  match hopenP : openPisAtFvars nP pty 0 with
  | none => intro h; exact nomatch h
  | some pr₃ => ?_
  obtain ⟨fvsP, rest0⟩ := pr₃
  intro h
  try dsimp only [] at h ⊢
  revert h
  match hcinstP : Expr.instPisAt fvsP cvj.type with
  | none => intro h; exact nomatch h
  | some pr₄ => ?_
  obtain ⟨cdomsP, crestP⟩ := pr₄
  intro h
  try dsimp only [] at h ⊢
  obtain ⟨hfvsW0, -⟩ := openPisAtFvars_WScoped nP pty 0 hopenP
    (WScoped.of_not_hasFvar hptyf)
  have hfvsW : ∀ x ∈ fvsP, WScoped nP x := by
    intro x hx
    have h0 := hfvsW0 x hx
    rwa [Nat.zero_add] at h0
  have hannW : ∀ a ∈ fvsP.map Expr.fvarTypeD, WScoped (nP + nF) a := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    have hw := hfvsW x hx
    cases x with
    | fvar idx ty =>
      simp only [WScoped] at hw
      exact hw.2.mono (by omega)
    | bvar _ => exact hw.mono (by omega)
    | sort _ => exact hw.mono (by omega)
    | const _ _ => exact hw.mono (by omega)
    | app _ _ => exact hw.mono (by omega)
    | lam _ _ _ => exact hw.mono (by omega)
    | forallE _ _ _ => exact hw.mono (by omega)
    | letE _ _ _ => exact hw.mono (by omega)
    | lit _ => exact hw.mono (by omega)
    | proj _ _ _ => exact hw.mono (by omega)
  obtain ⟨hcdW, hcrW⟩ := instPisAt_WScoped (d := nP) fvsP cvj.type
    hcinstP (WScoped.of_not_hasFvar hCf) hfvsW
  obtain ⟨u₁, hde1, h⟩ := atF_bind_ok h
  have hde1' := checkDefEqList_wfimp henv' hannW
    (fun b hb => (hcdW b hb).mono (by omega)) hde1
  show (checkDefEqList (fueledOps mode F) env' (nP + nF)
    (fvsP.map Expr.fvarTypeD) cdomsP >>= _) = _
  rw [hde1']
  simp only [Bind.bind, Except.bind]
  revert h
  match hopenX : openPisAtFvars nF crestP nP with
  | none => intro h; exact nomatch h
  | some pr₅ => ?_
  obtain ⟨xFvs, crest2X⟩ := pr₅
  intro h
  try dsimp only [] at h ⊢
  revert h
  match hlinst : Expr.instLamsAt (fvsP ++ xFvs) rhsA with
  | none => intro h; exact nomatch h
  | some pr₆ => ?_
  obtain ⟨ldoms, lrestL⟩ := pr₆
  intro h
  try dsimp only [] at h ⊢
  have hrhsAf : rhsA.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h2
    exact h2.2
  obtain ⟨hxW, -⟩ := openPisAtFvars_WScoped nF crestP nP hopenX hcrW
  have hspineW : ∀ a ∈ fvsP ++ xFvs, WScoped (nP + nF) a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (hfvsW a ha).mono (by omega)
    · exact hxW a ha
  have hannW2 : ∀ a ∈ (fvsP ++ xFvs).map Expr.fvarTypeD,
      WScoped (nP + nF) a := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    have hw := hspineW x hx
    cases x with
    | fvar idx ty =>
      simp only [WScoped] at hw
      exact hw.2.mono (by omega)
    | bvar _ => exact hw.mono (by omega)
    | sort _ => exact hw.mono (by omega)
    | const _ _ => exact hw.mono (by omega)
    | app _ _ => exact hw.mono (by omega)
    | lam _ _ _ => exact hw.mono (by omega)
    | forallE _ _ _ => exact hw.mono (by omega)
    | letE _ _ _ => exact hw.mono (by omega)
    | lit _ => exact hw.mono (by omega)
    | proj _ _ _ => exact hw.mono (by omega)
  obtain ⟨hldW, -⟩ := instLamsAt_WScoped (fvsP ++ xFvs) rhsA hlinst
    (WScoped.of_not_hasFvar hrhsAf) hspineW
  obtain ⟨u₂, hde2, h⟩ := atF_bind_ok h
  have hde2' := checkDefEqList_wfimp henv' hannW2
    (fun b hb => hldW b hb) hde2
  show (checkDefEqList (fueledOps mode F) env' (nP + nF)
    ((fvsP ++ xFvs).map Expr.fvarTypeD) ldoms >>= _) = _
  rw [hde2']
  simp only [Bind.bind, Except.bind]
  rw [wfOpsM_inferType henv' (wscopedB_of_not_hasFvar hrhsAf)] at h
  obtain ⟨rhsTy, hity, h⟩ := atF_bind_ok h
  have hity' : inferTypeCore mode env' F 0 rhsA = .ok rhsTy := hity
  show (inferTypeCore mode env' F 0 rhsA >>= _) = _
  rw [hity']
  simp only [Bind.bind, Except.bind]
  exact h

/-- The stored constructor behind a successful projection lookup. -/
theorem checkProjLookups_ctor {env' : Env} {T ctorName : Name}
    {lps : List Name} {nP nF i : Nat} {cvj mcv : ConstantVal}
    (h : (checkProjLookups env' T ctorName lps nP nF i :
      CheckM (ConstantVal × ConstantVal)) = .ok (cvj, mcv)) :
    ∃ cnP cnF, env'.find? ctorName = some (.ctorInfo cvj cnP cnF) := by
  unfold checkProjLookups at h
  revert h
  match hf : env'.find? ctorName with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.ctorInfo cvj' cnP cnF) => ?_
  intro h
  try dsimp only at h
  split at h
  next harm =>
    refine ⟨cnP, cnF, ?_⟩
    -- the remaining guards only gate success; the head is fixed
    revert h
    match env'.find? (projModelName T i) with
    | none => intro h; exact nomatch h
    | some (.axiomInfo _) => intro h; exact nomatch h
    | some (.thmInfo _ _) => intro h; exact nomatch h
    | some (.indInfo _ _) => intro h; exact nomatch h
    | some (.projInfo _) => intro h; exact nomatch h
    | some (.recInfo _ _ _ _) => intro h; exact nomatch h
    | some (.ctorInfo _ _ _) => intro h; exact nomatch h
    | some (.defnInfo mcv' _ _) => ?_
    intro h
    try dsimp only at h
    split at h
    next =>
      split at h
      next =>
        split at h
        next =>
          split at h
          next =>
            simp only [pure, Except.pure, Except.ok.injEq,
              Prod.mk.injEq] at h
            rw [h.1]
          next => exact nomatch h
        next => exact nomatch h
      next => exact nomatch h
    next => exact nomatch h
  next => exact nomatch h

/-- Well-formedness of a successfully checked projection type. -/
theorem checkProjTy_wf {env' : Env} {T ctorName : Name}
    {lps : List Name} {mty pty : Expr} {nP nF : Nat}
    (h : (checkProjTy env' T ctorName lps mty nP nF : CheckM Expr) =
      .ok pty) :
    pty.hasFvar = false ∧ pty.looseBVarsBounded 0 = true := by
  unfold checkProjTy at h
  try dsimp only at h
  split at h
  next =>
    split at h
    next =>
      split at h
      next hwf =>
        split at h
        next =>
          simp only [pure, Except.pure, Except.ok.injEq] at h
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not,
            Bool.not_true] at hwf
          rw [← h]
          exact ⟨hwf.1.2, hwf.1.1⟩
        next => exact nomatch h
      next => exact nomatch h
    next => exact nomatch h
  next => exact nomatch h

set_option maxHeartbeats 6400000 in
/-- The projection-iota check, `wfOpsM mode` run to pure run (task #100
stage 3: the side certificates run at the opened statement telescope,
which is scoped by the stored statement's closedness). -/
theorem checkProjIota_wfimp {env' : Env} (henv' : EnvWF env')
    {T ctorName : Name} {lps : List Name} {cvj : ConstantVal}
    {nP nF i F : Nat} {v : Unit}
    (h : (checkProjIota mode (wfOpsM mode) env' env' T ctorName lps cvj nP nF
      i).val F = .ok v) :
    checkProjIota mode (fueledOps mode F) env' env' T ctorName lps cvj nP nF i
      = .ok v := by
  unfold checkProjIota at h ⊢
  revert h
  match hthm : env'.find? ((projModelName T i).str "iota") with
  | none => intro h; rw [FueledM.atF_throw] at h; exact nomatch h
  | some (.axiomInfo _) => intro h; rw [FueledM.atF_throw] at h; exact nomatch h
  | some (.projInfo _) => intro h; rw [FueledM.atF_throw] at h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; rw [FueledM.atF_throw] at h; exact nomatch h
  | some (.indInfo _ _) => intro h; rw [FueledM.atF_throw] at h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; rw [FueledM.atF_throw] at h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; rw [FueledM.atF_throw] at h; exact nomatch h
  | some (.thmInfo tcv _tval) => ?_
  intro h
  dsimp only at h ⊢
  by_cases htlps : tcv.levelParams = lps
  case neg =>
    rw [if_neg htlps] at h
    first
    | exact absurd h atF_throw_bind
    | (rw [FueledM.atF_throw] at h; exact nomatch h)
  rw [if_pos htlps] at h ⊢
  try dsimp only at h ⊢
  revert h
  match hS_strip : tcv.type.stripPis (nP + nF) with
  | none => intro h; rw [FueledM.atF_throw] at h; exact nomatch h
  | some (sbinders, sbody) => ?_
  intro h
  dsimp only at h ⊢
  revert h
  match hC_strip : cvj.type.stripPis (nP + nF) with
  | none => intro h; rw [FueledM.atF_throw] at h; exact nomatch h
  | some (cbindersR, cbody) => ?_
  intro h
  dsimp only at h ⊢
  by_cases hsdomsB : domsMatchAux
      (fun _ e => e.renameConsts (projFwd T ctorName nF))
      sbinders cbindersR 0 0 (nP + nF) = true
  case neg =>
    rw [if_neg hsdomsB] at h
    first
    | exact absurd h atF_throw_bind
    | (rw [FueledM.atF_throw] at h; exact nomatch h)
  rw [if_pos hsdomsB] at h ⊢
  try dsimp only at h ⊢
  revert h
  cases sbody
  case bvar => intro h; exact absurd h atF_throw_bind
  case fvar => intro h; exact absurd h atF_throw_bind
  case sort => intro h; exact absurd h atF_throw_bind
  case const => intro h; exact absurd h atF_throw_bind
  case lam => intro h; exact absurd h atF_throw_bind
  case forallE => intro h; exact absurd h atF_throw_bind
  case letE => intro h; exact absurd h atF_throw_bind
  case lit => intro h; exact absurd h atF_throw_bind
  case proj => intro h; exact absurd h atF_throw_bind
  rename_i sA rhsC
  cases sA
  case bvar => intro h; exact absurd h atF_throw_bind
  case fvar => intro h; exact absurd h atF_throw_bind
  case sort => intro h; exact absurd h atF_throw_bind
  case const => intro h; exact absurd h atF_throw_bind
  case lam => intro h; exact absurd h atF_throw_bind
  case forallE => intro h; exact absurd h atF_throw_bind
  case letE => intro h; exact absurd h atF_throw_bind
  case lit => intro h; exact absurd h atF_throw_bind
  case proj => intro h; exact absurd h atF_throw_bind
  rename_i sB lhsC
  cases sB
  case bvar => intro h; exact absurd h atF_throw_bind
  case fvar => intro h; exact absurd h atF_throw_bind
  case sort => intro h; exact absurd h atF_throw_bind
  case const => intro h; exact absurd h atF_throw_bind
  case lam => intro h; exact absurd h atF_throw_bind
  case forallE => intro h; exact absurd h atF_throw_bind
  case letE => intro h; exact absurd h atF_throw_bind
  case lit => intro h; exact absurd h atF_throw_bind
  case proj => intro h; exact absurd h atF_throw_bind
  rename_i sEq tySlot
  cases sEq
  case bvar => intro h; exact absurd h atF_throw_bind
  case fvar => intro h; exact absurd h atF_throw_bind
  case sort => intro h; exact absurd h atF_throw_bind
  case app => intro h; exact absurd h atF_throw_bind
  case lam => intro h; exact absurd h atF_throw_bind
  case forallE => intro h; exact absurd h atF_throw_bind
  case letE => intro h; exact absurd h atF_throw_bind
  case lit => intro h; exact absurd h atF_throw_bind
  case proj => intro h; exact absurd h atF_throw_bind
  rename_i c ℓs
  cases ℓs
  case nil => intro h; exact absurd h atF_throw_bind
  rename_i ℓA ℓtail
  cases ℓtail
  case cons => intro h; exact absurd h atF_throw_bind
  intro h
  try dsimp only at h ⊢
  by_cases hc : c = eqName
  case neg =>
    rw [if_neg hc] at h
    exact absurd h atF_throw_bind
  rw [if_pos hc] at h ⊢
  try dsimp only at h ⊢
  by_cases hlhs : (lhsC == Expr.mkAppN
      (.const (projModelName T i) (lps.map .param))
      (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
       [Expr.mkAppN
         (.const (ctorName.str "_model") (cvj.levelParams.map .param))
         (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
          ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))])) = true
  case neg =>
    rw [if_neg hlhs] at h
    exact absurd h atF_throw_bind
  rw [if_pos hlhs] at h ⊢
  try dsimp only at h ⊢
  by_cases hrhsC : (rhsC == Expr.bvar (nF - 1 - i)) = true
  case neg =>
    rw [if_neg hrhsC] at h
    exact absurd h atF_throw_bind
  rw [if_pos hrhsC] at h ⊢
  try dsimp only at h ⊢
  obtain ⟨q, hopen, h⟩ := atF_bind_ok h
  obtain ⟨fvsO, sbodyO⟩ := q
  have hopen' := unwrapOr_atF_ok hopen
  show ((unwrapOr (openPisAtFvars (nP + nF) tcv.type 0) _ :
    CheckM _) >>= _) = _
  rw [hopen']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  have hcvtF : tcv.type.hasFvar = false :=
    (henv' _ (find?_mem hthm)).1
  have hopenW := openPisAtFvars_WScoped (nP + nF) tcv.type 0
    hopen' (WScoped.of_not_hasFvar hcvtF)
  rw [Nat.zero_add] at hopenW
  obtain ⟨-, htbodyW⟩ := hopenW
  have htargsW : ∀ x ∈ sbodyO.getAppArgs, WScoped (nP + nF) x :=
    Expr.WScoped.getAppArgs htbodyW
  exact checkIotaSidesTy_wfimp henv' (WScoped_getD' htargsW 0)
    (WScoped_getD' htargsW 1) (WScoped_getD' htargsW 2) h

theorem checkProjFn_wfimp {env' : Env} (henv' : EnvWF env')
    {T ctorName : Name} {lps : List Name} {nP nF i F : Nat} {v : Env}
    (h : (checkProjFn mode (wfOpsM mode) env' T ctorName lps nP nF i).val F = .ok v) :
    checkProjFn mode (fueledOps mode F) env' T ctorName lps nP nF i = .ok v := by
  unfold checkProjFn at h ⊢
  obtain ⟨⟨cvj, mcv⟩, hlk, h⟩ := atF_bind_ok h
  rw [checkProjLookups_datF] at hlk
  show ((checkProjLookups env' T ctorName lps nP nF i :
    CheckM (ConstantVal × ConstantVal)) >>= _) = _
  rw [hlk]
  simp only [Bind.bind, Except.bind]
  obtain ⟨pty, hty, h⟩ := atF_bind_ok h
  rw [checkProjTy_datF] at hty
  show ((checkProjTy env' T ctorName lps mcv.type nP nF :
    CheckM Expr) >>= _) = _
  rw [hty]
  simp only [Bind.bind, Except.bind]
  obtain ⟨u0, hshape, h⟩ := atF_bind_ok h
  rw [checkProjShape_datF] at hshape
  show ((checkProjShape pty cvj.type nP nF : CheckM Unit) >>= _) = _
  rw [hshape]
  simp only [Bind.bind, Except.bind]
  dsimp only [] at h ⊢
  by_cases h1 : i < nF
  case neg => rw [if_neg h1] at h; exact absurd h atF_throw_bind
  rw [if_pos h1] at h ⊢
  obtain ⟨rhsA, hrule, h⟩ := atF_bind_ok h
  obtain ⟨cnP0, cnF0, hctor⟩ := checkProjLookups_ctor hlk
  obtain ⟨hptyf, hptyb⟩ := checkProjTy_wf hty
  have hrule' := checkProjRule_wfimp henv' hptyf hptyb
    (show cvj.type.hasFvar = false from (henv' _ (find?_mem hctor)).1)
    (show cvj.type.looseBVarsBounded 0 = true from
      (henv' _ (find?_mem hctor)).2.2.2.1)
    hrule
  show (checkProjRule (fueledOps mode F) env' pty cvj lps nP nF i >>= _) = _
  rw [hrule']
  simp only [Bind.bind, Except.bind]
  obtain ⟨u, hiota, h⟩ := atF_bind_ok h
  have hiota' := checkProjIota_wfimp henv' hiota
  show (checkProjIota mode (fueledOps mode F) env' env' T ctorName lps cvj nP
    nF i >>= _) = _
  rw [hiota']
  simp only [Bind.bind, Except.bind]
  exact h

theorem installProjFnStep_wfimp {e : Env} (he : EnvWF e)
    {T ctorName : Name} {lps : List Name} {nP nF i F : Nat} {e' : Env}
    (h : (installProjFnStep mode (wfOpsM mode) T ctorName lps nP nF e i).val F =
      .ok e') :
    installProjFnStep mode (fueledOps mode F) T ctorName lps nP nF e i = .ok e' := by
  unfold installProjFnStep at h ⊢
  split at h
  · rw [if_pos (by assumption)]
    exact checkProjFn_wfimp he h
  · rw [if_neg (by assumption)]
    simp only [FueledM.atF_pure] at h
    exact h ▸ rfl

/-! ## Scoping of the structural-Nat certification equations -/

/-- The recurrence equations' sides are well-scoped at depth 2 (their
free variables are `fvar 0`/`fvar 1` with closed annotations). -/
theorem natOpEquations_wscopedB {c : Name} (hc : c ∈ natOpNames) :
    ∀ eq ∈ natOpEquations 0 c,
      eq.1.wscopedB 2 = true ∧ eq.2.wscopedB 2 = true := by
  simp only [natOpNames, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (intro eq heq
     simp +decide [natOpEquations] at heq
     first
       | (rcases heq with rfl | rfl | rfl | rfl) <;>
           simp +decide [Expr.wscopedB]
       | (rcases heq with rfl | rfl | rfl) <;>
           simp +decide [Expr.wscopedB]
       | (rcases heq with rfl | rfl) <;>
           simp +decide [Expr.wscopedB])

/-- Substituting a closed value for a constant preserves scoping. -/
theorem wscopedB_substConst0 {n : Name} {r : Expr}
    (hr : r.hasFvar = false) :
    ∀ (e : Expr) {d : Nat}, e.wscopedB d = true →
      (Expr.substConst0 n r e).wscopedB d = true
  | .const c us, d, he => by
    simp only [Expr.substConst0]
    split
    · exact wscopedB_of_not_hasFvar hr
    · exact he
  | .app f a, d, he => by
    simp only [Expr.substConst0, Expr.wscopedB, Bool.and_eq_true] at he ⊢
    exact ⟨wscopedB_substConst0 hr f he.1, wscopedB_substConst0 hr a he.2⟩
  | .bvar _, _, he | .fvar _ _, _, he | .sort _, _, he | .lit _, _, he
  | .lam _ _ _, _, he | .forallE _ _ _, _, he
  | .letE _ _ _, _, he | .proj _ _ _, _, he => he

/-! ## The div/mod pin gate, `wfOpsM mode` runs to pure runs -/

theorem atF_throw {α : Type} {e : CheckError} {F : Nat} {v : α}
    (h : ((throw e : FueledM α)).val F = .ok v) : False := by
  simp only [throw, throwThe, MonadExceptOf.throw] at h
  exact nomatch h

/-- The pinned open certificate statements are well-scoped at the
certificate frame: hypotheses at their own binder index (they ride as
the `fvar 2`/`fvar 3` annotations), the equation at the full frame. -/
theorem divModCertStmts_wscopedB {c : Name} (hc : c ∈ natDivModNames) :
    ∀ st ∈ divModCertStmts c,
      (∀ hyp ∈ st.1, hyp.wscopedB 2 = true) ∧ st.2.wscopedB 4 = true := by
  simp only [natDivModNames, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

/-- The applied certificate proof is well-scoped at the frame. -/
theorem divModCertApplied_wscopedB {proofS : Expr} {hyps : List Expr}
    (hp : proofS.hasFvar = false)
    (hh : ∀ hyp ∈ hyps, hyp.wscopedB 2 = true) :
    (divModCertApplied proofS hyps).wscopedB 4 = true := by
  have hpw : proofS.wscopedB 4 = true := wscopedB_of_not_hasFvar hp
  unfold divModCertApplied
  match hyps, hh with
  | [], hh => simp [Expr.wscopedB, hpw]
  | [h1], hh =>
    have h1w := hh h1 (by simp)
    simp [Expr.wscopedB, hpw, h1w]
  | [h1, h2], hh =>
    have h1w := hh h1 (by simp)
    have h2w3 : h2.wscopedB 3 = true :=
      (WScoped.mono (by omega) (WScoped.of_wscopedB
        (hh h2 (by simp)))).to_wscopedB
    simp [Expr.wscopedB, hpw, h1w, h2w3]
  | _ :: _ :: _ :: _, hh => simp [Expr.wscopedB, hpw]

theorem checkDivModCerts_wfimp {env : Env} (henv : EnvWF env) {F : Nat}
    {c : Name} {annVal : Expr} (hvf : annVal.hasFvar = false) :
    ∀ {stmts : List (List Expr × Expr)} {proofs : List Expr},
      (∀ st ∈ stmts, (∀ hyp ∈ st.1, hyp.wscopedB 2 = true) ∧
        st.2.wscopedB 4 = true) →
      ∀ {v : Bool},
        (checkDivModCerts (wfOpsM mode) env c annVal stmts proofs).val F = .ok v →
        checkDivModCerts (fueledOps mode F) env c annVal stmts proofs = .ok v
  | [], [], _, v, h => h
  | [], _ :: _, _, v, h => h
  | _ :: _, [], _, v, h => h
  | (hyps, eqE) :: srest, proof :: prest, hsc, v, h => by
    unfold checkDivModCerts at h ⊢
    obtain ⟨hhyps, heqw⟩ := hsc (hyps, eqE) (List.mem_cons_self ..)
    have hhypsS : ∀ hyp ∈ hyps.map (Expr.substConst0 c annVal),
        hyp.wscopedB 2 = true := by
      intro hyp hh
      obtain ⟨h₀, hh₀, rfl⟩ := List.mem_map.mp hh
      exact wscopedB_substConst0 hvf _ (hhyps h₀ hh₀)
    have heqS : (Expr.substConst0 c annVal eqE).wscopedB 4 = true :=
      wscopedB_substConst0 hvf _ heqw
    revert h
    by_cases hguards : divModCertGuard env c annVal hyps eqE proof = true
    case neg => rw [if_neg hguards, if_neg hguards]; intro h; exact h
    rw [if_pos hguards, if_pos hguards]
    have hguards' := hguards
    unfold divModCertGuard at hguards'
    simp only [Bool.and_eq_true] at hguards'
    have hpf : (Expr.substConstAll c annVal proof).hasFvar = false := by
      simpa using hguards'.1.1.1.1.2
    have happW : (divModCertApplied (Expr.substConstAll c annVal proof)
        (hyps.map (Expr.substConst0 c annVal))).wscopedB 4 = true :=
      divModCertApplied_wscopedB hpf hhypsS
    intro h
    rw [wfOpsM_annotate henv happW] at h
    obtain ⟨appliedA, hann, h⟩ := atF_bind_ok h
    have hann' : annotateCore mode env F 4 _ = .ok appliedA := hann
    show (annotateCore mode env F 4 _ >>= _) = _
    rw [hann']
    simp only [Bind.bind, Except.bind]
    have happAW : WScoped 4 appliedA :=
      annotateCore_WScoped F _ hann' (WScoped.of_wscopedB happW)
    rw [wfOpsM_inferType henv happAW.to_wscopedB] at h
    obtain ⟨tp, hinf, h⟩ := atF_bind_ok h
    have hinf' : inferTypeCore mode env F 4 appliedA = .ok tp := hinf
    show (inferTypeCore mode env F 4 appliedA >>= _) = _
    rw [hinf']
    simp only [Bind.bind, Except.bind]
    have htpW : WScoped 4 tp := inferTypeCore_WScoped henv F hinf' happAW
    rw [wfOpsM_isDefEq henv htpW.to_wscopedB heqS] at h
    obtain ⟨b, hde, h⟩ := atF_bind_ok h
    have hde' : isDefEqCore mode env F 4 tp _ = .ok b := hde
    show (isDefEqCore mode env F 4 tp _ >>= _) = _
    rw [hde']
    simp only [Bind.bind, Except.bind]
    cases b with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact checkDivModCerts_wfimp henv hvf
        (fun st hs => hsc st (List.mem_cons_of_mem _ hs)) h
    | false => simpa using h

/-- One pin variant's attempt, `wfOpsM mode` run to pure run (the
variant's guards supply the pin's scoping, the definition check the
stored value's; task #273). -/
theorem checkDivModPinAt_wfimp {env : Env} (henv : EnvWF env) {F : Nat}
    {c : Name} (hc : c ∈ natDivModNames) {value' : Expr}
    (hvf : value'.hasFvar = false) {ps : NatOpPinSet}
    (hping : (divModPinGuard ps env c &&
      divModCertsGuard ps env c value') = true) {b : Bool}
    (h : (checkDivModPinAt (wfOpsM mode) env c value' ps).val F = .ok b) :
    checkDivModPinAt (fueledOps mode F) env c value' ps = .ok b := by
  unfold checkDivModPinAt at h ⊢
  have hping' := hping
  simp only [Bool.and_eq_true] at hping'
  have hping'' := hping'.1
  unfold divModPinGuard at hping''
  simp only [Bool.and_eq_true] at hping''
  have hpinF : (divModDeclPin ps c).hasFvar = false := by
    simpa using hping''.1.1.2
  rw [wfOpsM_annotate henv (wscopedB_of_not_hasFvar hpinF)] at h
  obtain ⟨pinA, hann, h⟩ := atF_bind_ok h
  have hann' : annotateCore mode env F 0 _ = .ok pinA := hann
  show (annotateCore mode env F 0 _ >>= _) = _
  rw [hann']
  simp only [Bind.bind, Except.bind]
  have hpinAW : WScoped 0 pinA :=
    annotateCore_WScoped F _ hann' (WScoped.of_not_hasFvar hpinF)
  rw [wfOpsM_isDefEq henv (wscopedB_of_not_hasFvar hvf)
    hpinAW.to_wscopedB] at h
  obtain ⟨b', hde, h⟩ := atF_bind_ok h
  have hde' : isDefEqCore mode env F 0 value' pinA = .ok b' := hde
  show (isDefEqCore mode env F 0 value' pinA >>= _) = _
  rw [hde']
  simp only [Bind.bind, Except.bind]
  cases b' with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact h
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact checkDivModCerts_wfimp henv hvf (divModCertStmts_wscopedB hc) h

/-- The variant loop, `wfOpsM mode` run to pure run: the fueled
family's combinator hands its continuation `none`, and so does the
pure lane's — the two loops accumulate the same reasons and agree
branch for branch. -/
theorem checkDivModPinLoop_wfimp {env : Env} (henv : EnvWF env) {F : Nat}
    {c : Name} (hc : c ∈ natDivModNames) {value' : Expr}
    (hvf : value'.hasFvar = false) {u : Unit} :
    ∀ {pss : List NatOpPinSet} {tried : List String},
      (checkDivModPinLoop (wfOpsM mode) env c value' pss tried).val F = .ok u →
      checkDivModPinLoop (fueledOps mode F) env c value' pss tried = .ok u
  | [], _, h => absurd h atF_throw
  | ps :: rest, tried, h => by
    unfold checkDivModPinLoop at h ⊢
    revert h
    split
    case isTrue hping =>
      rw [wfOpsM_orElse, fueledOpsM_orElse_atF, fueledOps_orElse']
      cases hx : (checkDivModPinAt (wfOpsM mode) env c value' ps).val F with
      | ok b =>
        rw [checkDivModPinAt_wfimp henv hc hvf hping hx]
        cases b with
        | true => intro h; exact h
        | false => exact checkDivModPinLoop_wfimp henv hc hvf
      | error e =>
        intro h
        cases hx' : checkDivModPinAt (fueledOps mode F) env c value' ps with
        | ok b =>
          cases b with
          | true => cases u; rfl
          | false => exact checkDivModPinLoop_wfimp henv hc hvf h
        | error e' => exact checkDivModPinLoop_wfimp henv hc hvf h
    case isFalse => exact checkDivModPinLoop_wfimp henv hc hvf

theorem checkDivModPin_wfimp {env env2 : Env} (henv : EnvWF env) {F : Nat}
    {c : Name} (hc : c ∈ natDivModNames)
    (hv'f : ∀ cv' v' h', env2.find? c = some (.defnInfo cv' v' h') →
      v'.hasFvar = false)
    {u : Unit} (h : (checkDivModPin (wfOpsM mode) pins env env2 c).val F = .ok u) :
    checkDivModPin (fueledOps mode F) pins env env2 c = .ok u := by
  unfold checkDivModPin at h ⊢
  by_cases h1 : divModEnvGuard env2 c = true
  case neg =>
    rw [if_neg h1] at h
    exact absurd h atF_throw
  rw [if_pos h1] at h ⊢
  revert h
  cases hfind : env2.find? c with
  | none => intro h; exact absurd h atF_throw
  | some ci =>
    cases ci with
    | axiomInfo cv' => intro h; exact absurd h atF_throw
    | thmInfo cv' v' => intro h; exact absurd h atF_throw
    | indInfo cv' caps => intro h; exact absurd h atF_throw
    | ctorInfo cv' nP nF => intro h; exact absurd h atF_throw
    | recInfo cv' mI rP rules => intro h; exact absurd h atF_throw
    | projInfo _ => intro h; exact absurd h atF_throw
    | defnInfo cv' value' hint' =>
      exact checkDivModPinLoop_wfimp henv hc (hv'f _ _ _ hfind)

/-- The compiler-trust install gate, `wfOpsM mode` run to pure run (the
raw witness value's scoping comes from the preceding opaque check). -/
theorem checkReducePin_wfimp {env env2 : Env} (henv : EnvWF env)
    {F : Nat} {c : Name} {value : Expr}
    (hvf : value.hasFvar = false)
    {u : Unit}
    (h : (checkReducePin (wfOpsM mode) env env2 c value).val F = .ok u) :
    checkReducePin (fueledOps mode F) env env2 c value = .ok u := by
  unfold checkReducePin at h ⊢
  by_cases h1 : (reduceStoredOk env2 c && reduceElemOk env c) = true
  case neg =>
    rw [if_neg h1] at h
    exact absurd h atF_throw
  rw [if_pos h1] at h ⊢
  by_cases h2 : reducePinGuard env c = true
  case neg =>
    rw [if_neg h2] at h
    exact absurd h atF_throw
  rw [if_pos h2] at h ⊢
  rw [wfOpsM_annotate henv (wscopedB_of_not_hasFvar hvf)] at h
  obtain ⟨valA, hannv, h⟩ := atF_bind_ok h
  have hannv' : annotateCore mode env F 0 value = .ok valA := hannv
  show (annotateCore mode env F 0 value >>= _) = _
  rw [hannv']
  simp only [Bind.bind, Except.bind]
  have h2' := h2
  unfold reducePinGuard at h2'
  simp only [Bool.and_eq_true] at h2'
  have hpinF : (reduceDeclPin c).hasFvar = false := by
    simpa using h2'.1.1.2
  rw [wfOpsM_annotate henv (wscopedB_of_not_hasFvar hpinF)] at h
  obtain ⟨pinA, hannp, h⟩ := atF_bind_ok h
  have hannp' : annotateCore mode env F 0 (reduceDeclPin c) = .ok pinA := hannp
  show (annotateCore mode env F 0 (reduceDeclPin c) >>= _) = _
  rw [hannp']
  simp only [Bind.bind, Except.bind]
  have hvalAW : WScoped 0 valA :=
    annotateCore_WScoped F value hannv' (WScoped.of_not_hasFvar hvf)
  have hpinAW : WScoped 0 pinA :=
    annotateCore_WScoped F _ hannp' (WScoped.of_not_hasFvar hpinF)
  rw [wfOpsM_isDefEq henv hvalAW.to_wscopedB hpinAW.to_wscopedB] at h
  obtain ⟨b, hde, h⟩ := atF_bind_ok h
  have hde' : isDefEqCore mode env F 0 valA pinA = .ok b := hde
  show (isDefEqCore mode env F 0 valA pinA >>= _) = _
  rw [hde']
  simp only [Bind.bind, Except.bind]
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact absurd h atF_throw
  | true =>
    simp only [↓reduceIte] at h ⊢
    have hxW : WScoped 1 (reduceCertVar c) := by
      unfold reduceCertVar
      simp only [WScoped]
      refine ⟨Nat.zero_lt_one, ?_⟩
      unfold reduceElemTy
      split <;> simp only [WScoped]
    have happW : WScoped 1 (Expr.app valA (reduceCertVar c)) := by
      simp only [WScoped]
      exact ⟨WScoped.mono (Nat.zero_le 1) hvalAW, hxW⟩
    rw [wfOpsM_isDefEq henv happW.to_wscopedB hxW.to_wscopedB] at h
    obtain ⟨b2, hde2, h⟩ := atF_bind_ok h
    have hde2' : isDefEqCore mode env F 1 (.app valA (reduceCertVar c))
        (reduceCertVar c) = .ok b2 := hde2
    show (isDefEqCore mode env F 1 (.app valA (reduceCertVar c))
        (reduceCertVar c) >>= _) = _
    rw [hde2']
    simp only [Bind.bind, Except.bind]
    cases b2 with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact absurd h atF_throw
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact h

/-! ## The direct simple-structure path (task #82)

Run-level implications for the checks `checkStruct` composes.
The fabricated terms whose scoping has to be established here are the
openings of the recursor and constructor telescopes (at the pin frame
`nP + 2 + nF`), the generated projection type and the rule's
right-hand side — the last two are checked closed by the checker's own
`!hasFvar && looseBVarsBounded 0` guards before they are annotated. -/

/-- The per-frame parameter-domain pins, `wfOpsM mode` run to pure run: each
domain is scoped at its own frame. -/
theorem checkStructDomsAt_wfimp {env : Env} (henv : EnvWF env)
    {F off : Nat} {fvs doms : List Expr}
    (hc : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      WScoped (off + i) (Expr.fvarTypeD x))
    (ht : ∀ (i : Nat) (x : Expr), doms[i]? = some x → WScoped (off + i) x) :
    ∀ {j : Nat} {v : Unit},
      (checkStructDomsAt (wfOpsM mode) env off fvs doms j).val F = .ok v →
      checkStructDomsAt (fueledOps mode F) env off fvs doms j = .ok v
  | 0, _, h => h
  | j + 1, v, h => by
    unfold checkStructDomsAt at h ⊢
    obtain ⟨a, ha, h⟩ := atF_bind_ok h
    have ha' := unwrapOr_atF_ok ha
    show ((unwrapOr fvs[j]? _ : CheckM _) >>= _) = _
    rw [ha']
    simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
    obtain ⟨b, hb, h⟩ := atF_bind_ok h
    have hb' := unwrapOr_atF_ok hb
    show ((unwrapOr doms[j]? _ : CheckM _) >>= _) = _
    rw [hb']
    simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
    rw [wfOpsM_isDefEq henv (hc j a ha').to_wscopedB
      (ht j b hb').to_wscopedB] at h
    obtain ⟨c, hc2, h⟩ := atF_bind_ok h
    have hc2' : isDefEqCore mode env F (off + j) (Expr.fvarTypeD a) b = .ok c := hc2
    show (isDefEqCore mode env F (off + j) (Expr.fvarTypeD a) b >>= _) = _
    rw [hc2']
    simp only [Bind.bind, Except.bind]
    cases c with
    | false =>
      rw [if_neg (by simp)] at h
      exact absurd h atF_throw_bind
    | true =>
      rw [if_pos rfl] at h ⊢
      exact checkStructDomsAt_wfimp henv hc ht h

/-- Close a goal whose hypothesis is a pure run that begins with a
`throw`: such a run never succeeds. -/
macro "throwM_elim" h:ident : tactic =>
  `(tactic| simp only [throw, throwThe, MonadExceptOf.throw, Bind.bind,
      Except.bind, reduceCtorEq] at $h:ident)

/-- The type-slot `ConstWF` facts of a successfully checked constant:
level parameters and constant resolution are checked outright, and the
annotated type inherits closedness and fvar-freedom from the raw
checks through `annotate`. -/
theorem checkConstantVal_typeWF {env : Env} {cv cvA : ConstantVal}
    {F : Nat} (h : checkConstantVal (fueledOps mode F) env cv = .ok cvA) :
    cvA.type.hasFvar = false ∧
    cvA.type.allLevelParamsDefined cvA.levelParams = true ∧
    cvA.type.constsResolve env = true ∧
    cvA.type.looseBVarsBounded 0 = true := by
  unfold checkConstantVal at h
  by_cases h1 : (env.find? cv.name).isSome = true
  · rw [if_pos h1] at h; throwM_elim h
  rw [if_neg h1] at h
  by_cases h2 : reservedBasisNames.contains cv.name = true
  · rw [if_pos h2] at h; throwM_elim h
  rw [if_neg h2] at h
  by_cases h3 : cv.name.isProjFnShape = true
  · rw [if_pos h3] at h; throwM_elim h
  rw [if_neg h3] at h
  by_cases h4 : Name.nodup cv.levelParams = true
  case neg => rw [if_neg h4] at h; throwM_elim h
  rw [if_pos h4] at h
  by_cases h5 : Expr.looseBVarsBounded 0 cv.type = true
  case neg => rw [if_neg h5] at h; throwM_elim h
  rw [if_pos h5] at h
  by_cases h6 : cv.type.hasFvar = true
  · rw [if_pos h6] at h; throwM_elim h
  rw [if_neg h6] at h
  revert h
  match hann : (fueledOps mode F).annotate env 0 cv.type with
  | .error e => intro h; exact nomatch h
  | .ok type => ?_
  intro h
  simp only [Bind.bind, Except.bind] at h
  have hann' : annotateCore mode env F 0 cv.type = .ok type := hann
  by_cases h7 : Expr.allLevelParamsDefined cv.levelParams type = true
  case neg => rw [if_neg h7] at h; exact nomatch h
  rw [if_pos h7] at h
  by_cases h8 : Expr.constsResolve env type = true
  case neg => rw [if_neg h8] at h; exact nomatch h
  rw [if_pos h8] at h
  revert h
  match hity : (fueledOps mode F).inferType env 0 type with
  | .error e => intro h; exact nomatch h
  | .ok stype => ?_
  intro h
  simp only [Bind.bind, Except.bind] at h
  revert h
  match hsty : (fueledOps mode F).ensureSort env 0 stype with
  | .error e => intro h; exact nomatch h
  | .ok u => ?_
  intro h
  simp only [Bind.bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at h
  subst h
  refine ⟨?_, h7, h8, annotateCore_looseBVars F cv.type hann' h5⟩
  exact not_hasFvar_of_fvarsBelow_zero
    ((annotateCore_WScoped F cv.type hann'
      (WScoped.of_not_hasFvar (Bool.not_eq_true _ |>.mp h6))).fvarsBelow)

/-- Peeling a `∀`-telescope (without instantiating) keeps every binder
domain and the body scoped at the same frame. -/
theorem stripPis_WScoped {d : Nat} :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)}
      {body : Expr}, Expr.stripPis k e = some (bs, body) → WScoped d e →
      (∀ b ∈ bs, WScoped d b.1) ∧ WScoped d body
  | 0, e, bs, body, h, hw => by
    simp only [Expr.stripPis, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ : [] = bs ∧ e = body :=
      ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    exact ⟨(fun b hb => nomatch hb), hw⟩
  | k + 1, e, bs, body, h, hw => by
    match e, h with
    | .forallE ty b m, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body'⟩, hstrip, heq⟩ := h
      obtain ⟨rfl, rfl⟩ : (ty, m) :: bs' = bs ∧ body' = body :=
        ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
      simp only [WScoped] at hw
      obtain ⟨hrest, hbody⟩ := stripPis_WScoped k hstrip hw.2
      refine ⟨?_, hbody⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hw.1
      · exact hrest b hb

/-- The projection table, `wfOpsM mode` run to pure run (the stage is
ops-free, task #175 S1). -/
theorem checkStructProjTable_wfimp {T C : Name} {lps : List Name}
    {nP nF : Nat} {rs : Level} {guards : List Level} {off : Nat} {cvCa : ConstantVal}
    {env v : Env} {F : Nat}
    (h : (checkStructProjTable T C lps nP nF rs guards off cvCa env : FueledM Env).val F
      = Except.ok v) :
    (checkStructProjTable T C lps nP nF rs guards off cvCa env : CheckM Env)
      = Except.ok v := by
  rw [checkStructProjTable_datF] at h
  exact h

end ConLeche
