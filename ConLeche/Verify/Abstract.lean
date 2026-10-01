module

import ConLeche.Kernel.TypeChecker
public import ConLeche.Verify.Knot
public import ConLeche.Verify.Shift

public section

/-!
# Abstraction and the open/close roundtrip

`annotate` opens each binder, processes the body, and re-closes it with
`abstract1`.  The lemmas here make that roundtrip exact:

* `fvarConsistent d ty e`: every reachable `fvar d` leaf is exactly
  `fvar d n ty` — true of any opened body and preserved by `annotate`;
* `abstract1_instantiate1`: closing then re-opening is the identity,
  given consistency and no loose bound variables;
* scoping and loose-bvar bookkeeping for `abstract1`/`instantiate1` and
  their preservation through `annotate`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ConLeche

variable {mode : CheckMode}

open Expr

/-- Every reachable `fvar` leaf with index `d` is exactly `fvar d ty`. -/
@[expose] def Expr.fvarConsistent (d : Nat) (ty : Expr) : Expr → Prop
  | .fvar idx ty' => idx = d → ty' = ty
  | .app f a => fvarConsistent d ty f ∧ fvarConsistent d ty a
  | .lam t b _ | .forallE t b _ => fvarConsistent d ty t ∧ fvarConsistent d ty b
  | .letE t v b => fvarConsistent d ty t ∧ fvarConsistent d ty v ∧ fvarConsistent d ty b
  | .proj _ _ e => fvarConsistent d ty e
  | _ => True

/-- Closing then re-opening a binder body is the identity. -/
theorem abstract1_instantiate1 {d : Nat} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), fvarConsistent d ty e → e.looseBVarsBounded k = true →
      (e.abstract1 d k).instantiate1 (.fvar d ty) k = e := by
  intro e
  induction e <;> intro k hc hb <;>
    simp_all [Expr.fvarConsistent, Expr.looseBVarsBounded, Expr.abstract1, Expr.instantiate1]
  case bvar i =>
    have h1 : ¬ (i = k) := by omega
    have h2 : ¬ (i > k) := by omega
    simp [h1, h2]
  case fvar idx ty' ih =>
    by_cases hidx : idx = d
    · obtain rfl := hc hidx
      simp [hidx, Expr.instantiate1]
    · simp [hidx, Expr.instantiate1]

/-- Abstracting away the top variable lowers the scope bound. -/
theorem WScoped.abstract1 {d : Nat} :
    ∀ {e : Expr} (k : Nat), WScoped (d + 1) e → WScoped d (e.abstract1 d k) := by
  intro e
  induction e <;> intro k hw <;>
    simp_all [Expr.abstract1, WScoped]
  case fvar idx ty' ih =>
    by_cases hidx : idx = d
    · simp [hidx, WScoped]
    · simp only [hidx, if_false, WScoped]
      exact ⟨by omega, hw.2⟩

/-- Consistency at `d` survives abstracting a *different* index. -/
theorem fvarConsistent_abstract1 {d d' : Nat} {ty : Expr}
    (hne : d ≠ d') :
    ∀ (e : Expr) (k : Nat), fvarConsistent d ty e →
      fvarConsistent d ty (e.abstract1 d' k) := by
  intro e
  induction e <;> intro k hc <;>
    simp_all [Expr.abstract1, Expr.fvarConsistent]
  case fvar idx ty'' ih =>
    split
    · simp [Expr.fvarConsistent]
    · simpa [Expr.fvarConsistent] using hc

/-- Opening lowers the loose-bvar bound by one. -/
theorem looseBVarsBounded_instantiate1 {d : Nat} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded (k + 1) = true →
      (e.instantiate1 (.fvar d ty) k).looseBVarsBounded k = true := by
  intro e
  induction e <;> intro k hb <;>
    simp_all [Expr.instantiate1, Expr.looseBVarsBounded]
  case bvar i =>
    split
    · simp [Expr.looseBVarsBounded]
    · split <;> simp [Expr.looseBVarsBounded] <;> omega

/-- Abstracting raises the loose-bvar bound by one. -/
theorem looseBVarsBounded_abstract1 {d : Nat} :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded k = true →
      (e.abstract1 d k).looseBVarsBounded (k + 1) = true := by
  intro e
  induction e <;> intro k hb <;>
    simp_all [Expr.abstract1, Expr.looseBVarsBounded]
  case bvar i => omega
  case fvar idx ty' ih =>
    split <;> simp [Expr.looseBVarsBounded] <;> omega

/-! ## Preservation through `annotate` -/

/-- Inversion for `annotate` on projections: a projection-table entry
typed the node (which stays, with the display name normalized to the
type's head).  Task #175 wiring W5: the elimination fallbacks are
gone, so this is the only accepting arm; task #175 tower-flag: every
stored table is one, so the entry's existence is the whole test. -/
theorem annotateCore_proj_inv {env : Env} {fuel d : Nat} {sn : Name}
    {i : Nat} {e e' : Expr}
    (h : annotateCore mode env (fuel + 1) d (.proj sn i e) = .ok e') :
    ∃ e₂ tt te, annotateCore mode env fuel d e = .ok e₂ ∧
      inferTypeIO mode env fuel d e₂ = .ok tt ∧ whnf mode env fuel d tt = .ok te ∧
      (∃ T us entry, te.getAppFn = .const T us ∧
          env.findProj? T i = some entry ∧
          te.getAppArgs.length = entry.numParams ∧
          e' = .proj T i e₂) := by
  rw [annotateCore_succ] at h
  simp only [annotateBody, Bind.bind, Except.bind] at h
  simp only [annotate_def, inferTypeIO_def, whnf_def] at h
  cases he : annotateCore mode env fuel d e with
  | error err => rw [he] at h; exact nomatch h
  | ok e₂ =>
  rw [he] at h
  dsimp only at h
  cases hte : inferTypeIO mode env fuel d e₂ with
  | error err => rw [hte] at h; exact nomatch h
  | ok tt =>
  rw [hte] at h
  dsimp only at h
  cases hw : whnf mode env fuel d tt with
  | error err => rw [hw] at h; exact nomatch h
  | ok te =>
  rw [hw] at h
  dsimp only at h
  refine ⟨e₂, tt, te, rfl, hte, hw, ?_⟩
  revert h
  cases hfn : te.getAppFn with
  | const T us => ?_
  | bvar i2 => intro h; exact nomatch h
  | sort u => intro h; exact nomatch h
  | fvar i2 t2 => intro h; exact nomatch h
  | app f2 a2 => intro h; exact nomatch h
  | lam t2 b2 m2 => intro h; exact nomatch h
  | forallE t2 b2 m2 => intro h; exact nomatch h
  | letE t2 v2 b2 => intro h; exact nomatch h
  | lit l2 => intro h; exact nomatch h
  | proj s2 i2 e2 => intro h; exact nomatch h
  intro h
  dsimp only at h
  revert h
  cases hfp : env.findProj? T i with
  | none => intro h; exact nomatch h
  | some entry => ?_
  intro h
  dsimp only at h
  -- the node's own structure name (task #271), then the parameter count
  split at h
  case isFalse => exact nomatch h
  case isTrue _hsn =>
  split at h
  case isFalse => exact nomatch h
  case isTrue hlen =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨T, us, entry, rfl, hfp, hlen, h.symm⟩

/-- Inversion for `annotate` on applications: the two annotated subterms
are reassembled, and the application-rule check ran successfully. -/
theorem annotateCore_app_inv {env : Env} {fuel d : Nat} {f a e' : Expr}
    (h : annotateCore mode env (fuel + 1) d (.app f a) = .ok e') :
    ∃ f' a', annotateCore mode env fuel d f = .ok f' ∧
      annotateCore mode env fuel d a = .ok a' ∧
      e' = .app f' a' := by
  rw [annotateCore_succ] at h
  simp only [annotateBody, Bind.bind, Except.bind] at h
  simp only [annotate_def] at h
  cases hf : annotateCore mode env fuel d f with
  | error e => rw [hf] at h; exact nomatch h
  | ok f' =>
  rw [hf] at h; dsimp only at h
  cases ha : annotateCore mode env fuel d a with
  | error e => rw [ha] at h; exact nomatch h
  | ok a' =>
  rw [ha] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨f', a', rfl, rfl, h.symm⟩

/-- Inversion for `annotate` on let-expressions: the annotation and the
value are traversed, and the body is annotated with the value
transparent (as its zeta reduct).

Task #217 (audit follow-up #206-S1) put the official `infer_let` triple
back into the clause — `ensure_sort_core(infer(ty'))`, `infer(v')`,
`is_def_eq(tv, ty')` — because the pass returns the ζ reduct and
`inferBody`'s own `.letE` arm therefore never sees the node.  The four
extra conjuncts are back with it; consumers that do not need them
discard them with `-`. -/
theorem annotateCore_letE_inv {env : Env} {fuel d : Nat}
    {ty v b e' : Expr}
    (h : annotateCore mode env (fuel + 1) d (.letE ty v b) = .ok e') :
    ∃ ty' v', annotateCore mode env fuel d ty = .ok ty' ∧
      annotateCore mode env fuel d v = .ok v' ∧
      annotateCore mode env fuel d (b.instantiate1 v) = .ok e' ∧
      ∃ tty u tv,
        inferTypeCore mode env fuel d ty' = .ok tty ∧
        ensureSortCore mode env fuel d tty = .ok u ∧
        inferTypeCore mode env fuel d v' = .ok tv ∧
        isDefEqCore mode env fuel d tv ty' = .ok true := by
  rw [annotateCore_succ] at h
  simp only [annotateBody, Bind.bind, Except.bind] at h
  simp only [annotate_def, infer_def, defeq_def, ensureSort_def] at h
  cases hty : annotateCore mode env fuel d ty with
  | error e => rw [hty] at h; exact nomatch h
  | ok ty' =>
  rw [hty] at h; dsimp only at h
  cases hit : inferTypeCore mode env fuel d ty' with
  | error e => rw [hit] at h; exact nomatch h
  | ok tty =>
  rw [hit] at h; dsimp only at h
  cases hes : ensureSortCore mode env fuel d tty with
  | error e => rw [hes] at h; exact nomatch h
  | ok u =>
  rw [hes] at h; dsimp only at h
  cases hv : annotateCore mode env fuel d v with
  | error e => rw [hv] at h; exact nomatch h
  | ok v' =>
  rw [hv] at h; dsimp only at h
  cases hiv : inferTypeCore mode env fuel d v' with
  | error e => rw [hiv] at h; exact nomatch h
  | ok tv =>
  rw [hiv] at h; dsimp only at h
  cases hde : isDefEqCore mode env fuel d tv ty' with
  | error e => rw [hde] at h; exact nomatch h
  | ok bl =>
  rw [hde] at h; dsimp only at h
  cases bl with
  | false =>
    simp only [Bool.false_eq_true, if_false] at h
    exact nomatch h
  | true =>
  simp only [if_true] at h
  exact ⟨ty', v', rfl, rfl, h, tty, u, tv, hit, hes, hiv, hde⟩

/-! ### The binder clauses' inversion (task #161 P5)

The ∀/λ clauses gained one monadic bind: the untrusted `pw` write,
run only at the verified modes and only over the parse placeholder
(`annotPwPi` / `annotPwLam`).  The datum is *data*, not a check —
whatever it computes, the node's skeleton is the same — so the
inversions below take it existentially.  Every consumer in this file
(`WScoped`, `looseBVarsBounded`, `LeafEquiv`) is blind to binder
metadata, so the existential is exactly the right strength; the
consumers that *do* need the written value (the annotation-validation
battery) read it off the rebuilt node instead. -/

/-- Inversion for `annotate` on ∀-binders: the domain and the opened
body are annotated and the node is rebuilt, carrying *some* prop-ness
datum (the P5 write at the verified modes, the input datum otherwise). -/
theorem annotateCore_forallE_inv {env : Env} {fuel d : Nat}
    {ty body e' : Expr} {m : BinderMeta}
    (h : annotateCore mode env (fuel + 1) d (.forallE ty body m) = .ok e') :
    ∃ ty' body' pw, annotateCore mode env fuel d ty = .ok ty' ∧
      annotateCore mode env fuel (d + 1)
        (body.instantiate1 (.fvar d ty')) = .ok body' ∧
      e' = .forallE ty' (body'.abstract1 d) ⟨pw⟩ := by
  rw [annotateCore_succ] at h
  simp only [annotateBody, Bind.bind, Except.bind] at h
  simp only [annotate_def] at h
  cases hty : annotateCore mode env fuel d ty with
  | error e => rw [hty] at h; exact nomatch h
  | ok ty' =>
  rw [hty] at h; dsimp only at h
  cases hbody : annotateCore mode env fuel (d + 1)
      (body.instantiate1 (.fvar d ty')) with
  | error e => rw [hbody] at h; exact nomatch h
  | ok body' =>
  rw [hbody] at h; dsimp only at h
  revert h
  split
  · cases hpw : annotPwPi (pureFns mode env fuel) env (d + 1) body' with
    | error e => intro h; exact nomatch h
    | ok pw =>
      intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨ty', body', pw, rfl, hbody, h.symm⟩
  · intro h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨ty', body', m.pw, rfl, hbody, h.symm⟩

/-- Inversion for `annotate` on λ-binders (the ∀ twin; `annotPwLam`). -/
theorem annotateCore_lam_inv {env : Env} {fuel d : Nat}
    {ty body e' : Expr} {m : BinderMeta}
    (h : annotateCore mode env (fuel + 1) d (.lam ty body m) = .ok e') :
    ∃ ty' body' pw, annotateCore mode env fuel d ty = .ok ty' ∧
      annotateCore mode env fuel (d + 1)
        (body.instantiate1 (.fvar d ty')) = .ok body' ∧
      e' = .lam ty' (body'.abstract1 d) ⟨pw⟩ := by
  rw [annotateCore_succ] at h
  simp only [annotateBody, Bind.bind, Except.bind] at h
  simp only [annotate_def] at h
  cases hty : annotateCore mode env fuel d ty with
  | error e => rw [hty] at h; exact nomatch h
  | ok ty' =>
  rw [hty] at h; dsimp only at h
  cases hbody : annotateCore mode env fuel (d + 1)
      (body.instantiate1 (.fvar d ty')) with
  | error e => rw [hbody] at h; exact nomatch h
  | ok body' =>
  rw [hbody] at h; dsimp only at h
  revert h
  split
  · cases hpw : annotPwLam (pureFns mode env fuel) env (d + 1) body' with
    | error e => intro h; exact nomatch h
    | ok pw =>
      intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨ty', body', pw, rfl, hbody, h.symm⟩
  · intro h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨ty', body', m.pw, rfl, hbody, h.symm⟩

theorem annotateCore_WScoped {env : Env} :
    ∀ (fuel : Nat) (e : Expr) {d : Nat} {e' : Expr},
      annotateCore mode env fuel d e = .ok e' → WScoped d e → WScoped d e'
  | 0, _, _, _, h, _ => by simp [annotateCore_zero, throw, throwThe,
      MonadExceptOf.throw] at h
  | fuel + 1, .bvar i, d, e', h, hw => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hw
  | fuel + 1, .fvar idx ty, d, e', h, hw => by
    rw [annotateCore_succ] at h
    simp only [annotateBody] at h
    revert h
    split
    · intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ hw
    · intro h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1, .sort u, d, e', h, hw => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hw
  | fuel + 1, .const n us, d, e', h, hw => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hw
  | fuel + 1, .lit l, d, e', h, hw => by
    rw [annotateCore_succ] at h
    match l, h with
    | .natVal n, h => ?natCase
    | .strVal sv, h => ?strCase
    case strCase =>
      dsimp only [annotateBody] at h
      revert h
      split
      case isFalse =>
        intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
      case isTrue =>
        intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hw
    case natCase =>
      dsimp only [annotateBody] at h
      revert h
      split
      case isFalse =>
        intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
      case isTrue =>
        intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hw
  | fuel + 1, .app f a, d, e', h, hw => by
    simp only [WScoped] at hw
    obtain ⟨f', a', hf, ha, rfl, -⟩ := annotateCore_app_inv h
    simp only [WScoped]
    exact ⟨annotateCore_WScoped fuel f hf hw.1, annotateCore_WScoped fuel a ha hw.2⟩
  | fuel + 1, .proj sn i e, d, e', h, hw => by
    simp only [WScoped] at hw
    obtain ⟨e₂, tt, te, he, -, -, us, A, B, cv2, caps2, -, -, -, rfl⟩ :=
      annotateCore_proj_inv h
    simp only [WScoped]
    exact annotateCore_WScoped fuel e he hw
  | fuel + 1, .forallE ty body m, d, e', h, hw => by
    simp only [WScoped] at hw
    obtain ⟨ty', body', pw, hty, hbody, rfl⟩ := annotateCore_forallE_inv h
    have hwty' := annotateCore_WScoped fuel ty hty hw.1
    have hwbody' := annotateCore_WScoped fuel (body.instantiate1 (.fvar d ty')) hbody
      (hwty'.instantiate1 0 hw.2)
    simp only [WScoped]
    exact ⟨hwty', WScoped.abstract1 0 hwbody'⟩
  | fuel + 1, .lam ty body m, d, e', h, hw => by
    simp only [WScoped] at hw
    obtain ⟨ty', body', pw, hty, hbody, rfl⟩ := annotateCore_lam_inv h
    have hwty' := annotateCore_WScoped fuel ty hty hw.1
    have hwbody' := annotateCore_WScoped fuel (body.instantiate1 (.fvar d ty')) hbody
      (hwty'.instantiate1 0 hw.2)
    simp only [WScoped]
    exact ⟨hwty', WScoped.abstract1 0 hwbody'⟩
  | fuel + 1, .letE ty v b, d, e', h, hw => by
    simp only [WScoped] at hw
    obtain ⟨ty', v', -, -, hb, -⟩ := annotateCore_letE_inv h
    exact annotateCore_WScoped fuel _ hb
      (WScoped.instantiate1_gen hw.2.1 0 hw.2.2)

theorem annotateCore_looseBVars {env : Env} :
    ∀ (fuel : Nat) (e : Expr) {d : Nat} {e' : Expr},
      annotateCore mode env fuel d e = .ok e' → e.looseBVarsBounded 0 = true →
      e'.looseBVarsBounded 0 = true
  | 0, _, _, _, h, _ => by simp [annotateCore_zero, throw, throwThe,
      MonadExceptOf.throw] at h
  | fuel + 1, .bvar i, d, e', h, hb => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hb
  | fuel + 1, .fvar idx ty, d, e', h, hb => by
    rw [annotateCore_succ] at h
    simp only [annotateBody] at h
    revert h
    split
    · intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ hb
    · intro h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1, .sort u, d, e', h, hb => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hb
  | fuel + 1, .const n us, d, e', h, hb => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hb
  | fuel + 1, .lit l, d, e', h, hb => by
    rw [annotateCore_succ] at h
    match l, h with
    | .natVal n, h => ?natCase
    | .strVal sv, h => ?strCase
    case strCase =>
      dsimp only [annotateBody] at h
      revert h
      split
      case isFalse =>
        intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
      case isTrue =>
        intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hb
    case natCase =>
      dsimp only [annotateBody] at h
      revert h
      split
      case isFalse =>
        intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
      case isTrue =>
        intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hb
  | fuel + 1, .proj sn i e, d, e', h, hb => by
    simp only [Expr.looseBVarsBounded] at hb
    obtain ⟨e₂, tt, te, he, -, -, us, A, B, cv2, caps2, -, -, -, rfl⟩ :=
      annotateCore_proj_inv h
    simp only [Expr.looseBVarsBounded]
    exact annotateCore_looseBVars fuel e he hb
  | fuel + 1, .app f a, d, e', h, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨f', a', hf, ha, rfl, -⟩ := annotateCore_app_inv h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨annotateCore_looseBVars fuel f hf hb.1, annotateCore_looseBVars fuel a ha hb.2⟩
  | fuel + 1, .forallE ty body m, d, e', h, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨ty', body', pw, hty, hbody, rfl⟩ := annotateCore_forallE_inv h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    refine ⟨annotateCore_looseBVars fuel ty hty hb.1, ?_⟩
    exact looseBVarsBounded_abstract1 _ 0
      (annotateCore_looseBVars fuel _ hbody (looseBVarsBounded_instantiate1 body 0 hb.2))
  | fuel + 1, .lam ty body m, d, e', h, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨ty', body', pw, hty, hbody, rfl⟩ := annotateCore_lam_inv h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    refine ⟨annotateCore_looseBVars fuel ty hty hb.1, ?_⟩
    exact looseBVarsBounded_abstract1 _ 0
      (annotateCore_looseBVars fuel _ hbody (looseBVarsBounded_instantiate1 body 0 hb.2))
  | fuel + 1, .letE ty v bd, d, e', h, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨ty', v', -, -, hbody, -⟩ := annotateCore_letE_inv h
    exact annotateCore_looseBVars fuel _ hbody
      (looseBVarsBounded_instantiate1_gen hb.1.2 hb.2)


/-! ## Leaf equivalence

`annotate`-then-`abstract1` returns a term with the same skeleton and the
same `fvar`/`bvar` leaves as the unopened input — only binder annotations
(and inner binder bodies, recursively in the same way) differ.  `LeafEquiv`
captures exactly what `FvarsOk` can see, so `FvarsOk` transports across it.
-/

/-- Same constructor skeleton and identical `fvar`/`bvar` leaves;
binder metadata may differ. -/
def Expr.LeafEquiv : Expr → Expr → Prop
  | .bvar i, .bvar j => i = j
  | .fvar idx ty, .fvar idx' ty' => idx = idx' ∧ ty = ty'
  | .sort _, .sort _ => True
  | .const _ _, .const _ _ => True
  | .lit _, .lit _ => True
  | .app f a, .app f' a' => LeafEquiv f f' ∧ LeafEquiv a a'
  | .lam ty b _, .lam ty' b' _ => LeafEquiv ty ty' ∧ LeafEquiv b b'
  | .forallE ty b _, .forallE ty' b' _ => LeafEquiv ty ty' ∧ LeafEquiv b b'
  | .letE ty v b, .letE ty' v' b' =>
    LeafEquiv ty ty' ∧ LeafEquiv v v' ∧ LeafEquiv b b'
  | .proj _ _ e, .proj _ _ e' => LeafEquiv e e'
  | _, _ => False

theorem Expr.LeafEquiv.refl : ∀ (e : Expr), Expr.LeafEquiv e e := by
  intro e
  induction e <;> simp_all [Expr.LeafEquiv]


end ConLeche
