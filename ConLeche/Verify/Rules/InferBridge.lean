module

public import ConLeche.Verify.Rules.Defs
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferIOLemmas

public section

/-!
# The inference bridges (task #305, lane B4)

`inferTypeCore` (full grade) and `inferTypeCoreIO` (io grade) at
`fuel + 1` from the five bridges at `fuel`.  Eleven shapes each:

| clause | full inversion | io inversion | rule |
|---|---|---|---|
| `.sort` | inline | `inferTypeCoreIO_sort_eq` | `Infer.sort` |
| `.bvar` | throws | throws | — |
| `.fvar` | inline | `inferTypeCoreIO_fvar_eq` | `Infer.fvar` |
| `.const` | `inferTypeCore_const_inv` (+ the arity guard, `Accepted.lean:70`) | `inferTypeCoreIO_const_eq` | `Infer.const` |
| `.lit` | `inferTypeCore_natLit_inv` / `_strLit_inv` (`Accepted.lean`) | `inferTypeCoreIO_lit_eq` | `Infer.natLit` / `strLit` |
| `.forallE` | `inferTypeCore_forall_inv` | `inferTypeCoreIO_forall_inv` | `Infer.forallE` (+ `ensureSort_bridge`) |
| `.lam` | `inferTypeCore_lam_inv` | `inferTypeCoreIO_lam_inv` | `Infer.lam` |
| `.app` | `inferTypeCore_app_inv` | `inferTypeCoreIO_app_inv` | `Infer.app` / `Infer.appSkip` |
| `.proj` | `inferTypeCore_proj_inv` | `inferTypeCoreIO_proj_inv` | `Infer.proj` |
| `.letE` | `inferTypeCore_letE_inv` | `inferTypeCoreIO_letE_inv` | — |

The io body recurses through `pureFnsIO`, whose `whnf`/`defeq` are the
full knot's at the same fuel (`pureFnsIO_whnf`, `pureFnsIO_defeq`) and
whose `infer` is the lane at `fuel` (`inferIO_def`).
-/

namespace ConLeche.Rules

variable {env : Env} {fuel : Nat}

/-! ## The leaf clauses' inversions

`Verify/InferLemmas.lean` inverts the four recursive clauses; the six
leaves (`.sort`, `.fvar`, `.const`'s arity, the two literals, the
`.bvar` throw) have no inversion there because no previous consumer
needed one.  `Model/Steps/Accepted.lean:70-109` has three of them in
the model tier; they are transplanted here (the rules tier may not
import `Model/*`) and completed with the missing shapes and the io
twins.  Each is one `simp only [inferBody, …]` deep. -/

variable {mode : CheckMode}

/-- The `.sort` clause: the successor sort, no run. -/
theorem inferTypeCore_sort_inv {d : Nat} {u : Level} {t : Expr}
    (h : inferTypeCore mode env (fuel + 1) d (.sort u) = .ok t) :
    t = .sort (.succ u) := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, pure, Except.pure, Except.ok.injEq] at h
  exact h.symm

/-- The `.fvar` clause: the scope guard and the stored annotation. -/
theorem inferTypeCore_fvar_inv {d idx : Nat} {ty t : Expr}
    (h : inferTypeCore mode env (fuel + 1) d (.fvar idx ty) = .ok t) :
    idx < d ∧ t = ty := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, pure, Except.pure] at h
  by_cases hlt : idx < d
  · rw [if_pos hlt] at h
    simp only [Except.ok.injEq] at h
    exact ⟨hlt, h.symm⟩
  · rw [if_neg hlt] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The `.bvar` clause throws. -/
theorem inferTypeCore_bvar_inv {d i : Nat} {t : Expr}
    (h : inferTypeCore mode env (fuel + 1) d (.bvar i) = .ok t) : False := by
  rw [inferTypeCore_succ] at h
  simp [inferBody, throw, throwThe, MonadExceptOf.throw] at h

/-- The `.const` clause, whole: the stored constant, the table-entry
guard, the level arity and the instantiated type
(`inferTypeCore_const_inv` drops the arity — it is consumed inside its
own `split`; `Model/Steps/Accepted.lean:70`'s `_inv_len` recovers it). -/
theorem inferTypeCore_const_inv_full {d : Nat} {n : Name} {us : List Level}
    {t : Expr} (h : inferTypeCore mode env (fuel + 1) d (.const n us) = .ok t) :
    ∃ ci, env.find? n = some ci ∧ ci.isTowerEntry = false ∧
      us.length = ci.toConstantVal.levelParams.length ∧
      t = ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, pure, Except.pure, Bind.bind, Except.bind] at h
  revert h
  cases hf : env.find? n with
  | none => intro h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | some ci =>
    intro h
    dsimp only at h
    by_cases hte : ci.isTowerEntry = false
    · simp only [hte, Bool.not_false, ite_true] at h
      by_cases hlen : us.length = ci.toConstantVal.levelParams.length
      · rw [if_pos hlen] at h
        simp only [Except.ok.injEq] at h
        exact ⟨ci, rfl, hte, hlen, h.symm⟩
      · rw [if_neg hlen] at h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp only [Bool.not_eq_false] at hte
      simp [hte, throw, throwThe, MonadExceptOf.throw] at h

/-- The `Nat`-literal clause: the support guard and `Nat`. -/
theorem inferTypeCore_natLit_inv' {d k : Nat} {t : Expr}
    (h : inferTypeCore mode env (fuel + 1) d (.lit (.natVal k)) = .ok t) :
    natLitSupported env = true ∧ t = .const natName [] := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, pure, Except.pure] at h
  by_cases hg : natLitSupported env = true
  · rw [if_pos hg] at h
    simp only [Except.ok.injEq] at h
    exact ⟨hg, h.symm⟩
  · rw [if_neg hg] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The string-literal clause: the support guard and `String`. -/
theorem inferTypeCore_strLit_inv' {d : Nat} {s : String} {t : Expr}
    (h : inferTypeCore mode env (fuel + 1) d (.lit (.strVal s)) = .ok t) :
    strLitSupported env = true ∧ t = .const stringName [] := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, pure, Except.pure] at h
  by_cases hg : strLitSupported env = true
  · rw [if_pos hg] at h
    simp only [Except.ok.injEq] at h
    exact ⟨hg, h.symm⟩
  · rw [if_neg hg] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The io lane's `.bvar` clause throws too. -/
theorem inferTypeCoreIO_bvar_inv {d i : Nat} {t : Expr}
    (h : inferTypeCoreIO mode env (fuel + 1) d (.bvar i) = .ok t) : False := by
  rw [inferTypeCoreIO_succ] at h
  simp [inferBodyIO, throw, throwThe, MonadExceptOf.throw] at h

/-- `lamPw` is `none` exactly off a λ — the shape the rule's chain
premises are stated at, against the checker's `isLam` guard. -/
theorem lamPw_eq_none_iff {e : Expr} : e.lamPw = none ↔ e.isLam = false := by
  cases e <;> simp [Expr.lamPw, Expr.isLam]

/-- **`inferTypeCore` at `fuel + 1`**, full grade. -/
theorem infer_bridge_succ (hw : WhnfBridge env fuel) (hd : DefEqBridge env fuel)
    (hi : InferBridge env fuel) (hio : InferIOBridge env fuel) :
    InferBridge env (fuel + 1) := by
  intro d e t h
  match e, h with
  | .bvar _, h => exact (inferTypeCore_bvar_inv h).elim
  | .letE _ _ _, h => exact (inferTypeCore_letE_inv h).elim
  | .sort u, h =>
    obtain rfl := inferTypeCore_sort_inv h
    exact .sort
  | .fvar idx ty, h =>
    obtain ⟨hlt, rfl⟩ := inferTypeCore_fvar_inv h
    exact .fvar hlt
  | .const n us, h =>
    obtain ⟨ci, hf, hte, hlen, rfl⟩ := inferTypeCore_const_inv_full h
    exact .const hf hte hlen
  | .lit (.natVal k), h =>
    obtain ⟨hg, rfl⟩ := inferTypeCore_natLit_inv' h
    exact .natLit hg
  | .lit (.strVal s), h =>
    obtain ⟨hg, rfl⟩ := inferTypeCore_strLit_inv' h
    exact .strLit hg
  | .forallE ty body mb, h =>
    obtain ⟨tty, u, bt, v, hty, hwt, hbt, hes, hz, rfl⟩ :=
      inferTypeCore_forall_inv h
    exact .forallE (hi hty) (hw hwt) (hi hbt) (hw (ensureSortCore_inv hes))
      (hz rfl)
  | .app f a, h =>
    obtain ⟨tf, ty', body', m', htf, hwf, rfl, ta, hta, hde⟩ :=
      inferTypeCore_app_inv h
    exact .app (hi htf) (hw hwf) (hi hta) (hd hde)
  | .proj sn i pe, h =>
    obtain ⟨tpe, te, T, us, entry, hpe, hwpe, hfn, hentry, hlen, hlvl, hprop,
      rfl, rfl⟩ := inferTypeCore_proj_inv h
    simp only [beq_iff_eq] at hprop
    exact .proj (hi hpe) (hw hwpe) hfn hentry hlen hlvl hprop
  | .lam ty body mb, h =>
    obtain ⟨tty, u, bt, hty, hwt, hbt, hleaf, hchain, rfl⟩ :=
      inferTypeCore_lam_inv h
    cases hlp : body.lamPw with
    | none =>
      obtain ⟨btt, v, hbtt, hwv, hzv⟩ := hleaf rfl (lamPw_eq_none_iff.mp hlp)
      exact .lam (fun _ => hi hty) (fun _ => hw hwt) (hi hbt)
        (fun pwI hp => hchain rfl pwI hp)
        (fun _ => inferTypeIO_bridge hio hbtt) (fun _ => hw hwv)
        (fun _ => hzv)
    | some pwI =>
      exact .lam (btt := bt) (v := .zero) (fun _ => hi hty) (fun _ => hw hwt)
        (hi hbt) (fun pwI' hp => hchain rfl pwI' hp)
        (fun hn => absurd (hlp.symm.trans hn) (by simp))
        (fun hn => absurd (hlp.symm.trans hn) (by simp))
        (fun hn => absurd (hlp.symm.trans hn) (by simp))

/-- **`inferTypeCoreIO` at `fuel + 1`**, io grade. -/
theorem inferIO_bridge_succ (hw : WhnfBridge env fuel) (hd : DefEqBridge env fuel)
    (hio : InferIOBridge env fuel) :
    InferIOBridge env (fuel + 1) := by
  intro d e t h
  match e, h with
  | .bvar _, h => exact (inferTypeCoreIO_bvar_inv h).elim
  | .letE _ _ _, h => exact (inferTypeCoreIO_letE_inv h).elim
  | .sort u, h =>
    rw [inferTypeCoreIO_sort_eq] at h
    obtain rfl := inferTypeCore_sort_inv h
    exact .sort
  | .fvar idx ty, h =>
    rw [inferTypeCoreIO_fvar_eq] at h
    obtain ⟨hlt, rfl⟩ := inferTypeCore_fvar_inv h
    exact .fvar hlt
  | .const n us, h =>
    rw [inferTypeCoreIO_const_eq] at h
    obtain ⟨ci, hf, hte, hlen, rfl⟩ := inferTypeCore_const_inv_full h
    exact .const hf hte hlen
  | .lit (.natVal k), h =>
    rw [inferTypeCoreIO_lit_eq] at h
    obtain ⟨hg, rfl⟩ := inferTypeCore_natLit_inv' h
    exact .natLit hg
  | .lit (.strVal s), h =>
    rw [inferTypeCoreIO_lit_eq] at h
    obtain ⟨hg, rfl⟩ := inferTypeCore_strLit_inv' h
    exact .strLit hg
  | .forallE ty body mb, h =>
    obtain ⟨tty, u, bt, v, hty, hwt, hbt, hes, hz, rfl⟩ :=
      inferTypeCoreIO_forall_inv h
    exact .forallE (hio hty) (hw hwt) (hio hbt) (hw (ensureSortCore_inv hes))
      (hz rfl)
  | .proj sn i pe, h =>
    obtain ⟨tpe, te, T, us, entry, hpe, hwpe, hfn, hentry, hlen, hlvl, hprop,
      rfl, rfl⟩ := inferTypeCoreIO_proj_inv h
    simp only [beq_iff_eq] at hprop
    exact .proj (hio hpe) (hw hwpe) hfn hentry hlen hlvl hprop
  | .app f a, h =>
    obtain ⟨tf, ty', body', m', htf, hwf, rfl, hcert⟩ :=
      inferTypeCoreIO_app_inv h
    rcases hcert with hnever | ⟨ta, hta, hde⟩
    · exact .appSkip (hio htf) (hw hwf) hnever
    · exact .app (hio htf) (hw hwf) (hio hta) (hd hde)
  | .lam ty body mb, h =>
    obtain ⟨bt, hbt, hleaf, hchain, rfl⟩ := inferTypeCoreIO_lam_inv h
    cases hlp : body.lamPw with
    | none =>
      obtain ⟨btt, v, hbtt, hes, hzv⟩ := hleaf rfl (lamPw_eq_none_iff.mp hlp)
      exact .lam (s := ty) (u := .zero) (fun hg => nomatch hg) (fun hg => nomatch hg)
        (hio hbt) (fun pwI hp => hchain rfl pwI hp)
        (fun _ => hio hbtt) (fun _ => hw (ensureSortCore_inv hes))
        (fun _ => hzv)
    | some pwI =>
      exact .lam (s := ty) (u := .zero) (btt := bt) (v := .zero)
        (fun hg => nomatch hg) (fun hg => nomatch hg)
        (hio hbt) (fun pwI' hp => hchain rfl pwI' hp)
        (fun hn => absurd (hlp.symm.trans hn) (by simp))
        (fun hn => absurd (hlp.symm.trans hn) (by simp))
        (fun hn => absurd (hlp.symm.trans hn) (by simp))

end ConLeche.Rules
