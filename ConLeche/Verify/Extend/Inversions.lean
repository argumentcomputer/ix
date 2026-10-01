module

public import ConLeche.Kernel.Checker

public section

/-!
# Inversions

Small syntactic inversion lemmas and name disequalities shared by
the extension lemmas.

Every statement here is over `Env`/`Expr` only — no valuation, no
`SetTheory` — so the semantics and model tiers import it as it stands.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode}

open Expr

/-! Projection equations for the pure checker operations: the
declaration-checker inversions unfold through these (never through
`fueledOps` itself, so record spellings in hypotheses keep matching). -/

theorem fueledOps_annotate (F : Nat) (env : Env) (d : Nat) (e : Expr) :
    (fueledOps mode F).annotate env d e = annotateCore mode env F d e := rfl
theorem fueledOps_inferType (F : Nat) (env : Env) (d : Nat) (e : Expr) :
    (fueledOps mode F).inferType env d e = inferTypeCore mode env F d e := rfl
theorem fueledOps_isDefEq (F : Nat) (env : Env) (d : Nat) (a b : Expr) :
    (fueledOps mode F).isDefEq env d a b = isDefEqCore mode env F d a b := rfl
theorem fueledOps_ensureSort (F : Nat) (env : Env) (d : Nat) (e : Expr) :
    (fueledOps mode F).ensureSort env d e = ensureSortCore mode env F d e := rfl
theorem fueledOps_whnf (F : Nat) (env : Env) (d : Nat) (e : Expr) :
    (fueledOps mode F).whnf env d e = ConLeche.whnf mode env F d e := rfl
/-- The pure lane's variant-fallback combinator (task #273): the
continuation is handed `none` whatever the outcome — the outcome is
diagnostic text the executable's lane delivers. -/
theorem fueledOps_orElse (F : Nat) (x : CheckM Bool)
    (k : Option CheckError → CheckM Unit) :
    (fueledOps mode F).orElse x k =
      match x with | .ok true => pure () | _ => k none := rfl

/-- Inversion for `checkConstantVal`. -/
theorem checkConstantVal_inv {env : Env} {cv cv' : ConstantVal}
    (h : checkConstantVal (fueledOps mode F) env cv = .ok cv') :
    env.find? cv.name = none ∧
    reservedBasisNames.contains cv.name = false ∧
    cv.name.isProjFnShape = false ∧
    Name.nodup cv.levelParams = true ∧
    cv.type.looseBVarsBounded 0 = true ∧
    cv.type.hasFvar = false ∧
    ∃ type stype u,
      annotateCore mode env F 0 cv.type = .ok type ∧
      type.allLevelParamsDefined cv.levelParams = true ∧
      type.constsResolve env = true ∧
      inferTypeCore mode env F 0 type = .ok stype ∧
      ensureSortCore mode env F 0 stype = .ok u ∧
      cv' = { cv with type := type } := by
  simp only [checkConstantVal, fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
    fueledOps_ensureSort, fueledOps_whnf, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  by_cases hfind : (env.find? cv.name).isSome = true
  case pos => simp [hfind] at h
  simp only [hfind] at h
  by_cases hres : reservedBasisNames.contains cv.name = true
  case pos =>
    rw [if_pos hres] at h
    exact nomatch h
  simp only [hres] at h
  by_cases hpshape : cv.name.isProjFnShape = true
  case pos =>
    rw [if_pos hpshape] at h
    exact nomatch h
  rw [if_neg hpshape] at h
  have hpshapeF : cv.name.isProjFnShape = false := by
    revert hpshape; cases cv.name.isProjFnShape <;> simp
  by_cases hnd : Name.nodup cv.levelParams = true
  case neg => simp [hnd] at h
  simp only [hnd] at h
  by_cases hlb : cv.type.looseBVarsBounded 0 = true
  case neg => simp [hlb] at h
  simp only [hlb] at h
  by_cases hif : cv.type.hasFvar = true
  case pos => simp [hif] at h
  simp only [hif] at h
  cases hann : annotateCore mode env F 0 cv.type with
  | error e => rw [hann] at h; exact nomatch h
  | ok type =>
  rw [hann] at h
  try dsimp only at h
  by_cases htp : type.allLevelParamsDefined cv.levelParams = true
  case neg => simp [htp] at h
  simp only [htp] at h
  by_cases htr : type.constsResolve env = true
  case neg => simp [htr] at h
  simp only [htr] at h
  cases hst : inferTypeCore mode env F 0 type with
  | error e => rw [hst] at h; exact nomatch h
  | ok stype =>
  rw [hst] at h
  try dsimp only at h
  cases hsort : ensureSortCore mode env F 0 stype with
  | error e => rw [hsort] at h; exact nomatch h
  | ok u =>
  rw [hsort] at h
  simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
  have hfind0 : env.find? cv.name = none := by
    revert hfind
    cases env.find? cv.name <;> simp
  exact ⟨hfind0, by simpa using hres, hpshapeF, hnd, hlb,
    by simpa using hif,
    type, stype, u, rfl, htp, htr, hst, hsort, h.symm⟩

/-- Numeric names are never `str`-shaped. -/
theorem Name.num_ne_str (p : Name) (k : Nat) (q : Name) (s : String) :
    Name.num p k ≠ Name.str q s := fun h => nomatch h

/-- Reserved basis names are all `str`-shaped. -/
theorem reservedBasisNames_not_num (p : Name) (k : Nat) :
    reservedBasisNames.contains (Name.num p k) = false := rfl

/-- No `_model`-companion name equals a name that is not itself
`_model`-shaped. -/
theorem Name.str_model_ne {n m : Name} (hm : m.isModelSuffix = false) :
    n.str "_model" ≠ m := by
  intro h
  rw [← h] at hm
  simp [Name.isModelSuffix] at hm

theorem domsMatchAux_inv {g : Nat → Expr → Expr}
    {bs₁ bs₂ : List (Expr × BinderMeta)} {o₁ o₂ n : Nat}
    (h : domsMatchAux g bs₁ bs₂ o₁ o₂ n = true)
    {i : Nat} (hi : i < n) {b b' : Expr × BinderMeta}
    (hb : bs₁[o₁ + i]? = some b) (hb' : bs₂[o₂ + i]? = some b') :
    b.1 = g i b'.1 := by
  have hone := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  rw [hb, hb'] at hone
  exact eq_of_beq hone

/-- Split a successful monadic bind. -/
theorem Except.bind_ok {ε α β : Type _} {x : Except ε α}
    {k : α → Except ε β} {b : β}
    (h : Except.bind x k = .ok b) : ∃ a, x = .ok a ∧ k a = .ok b := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, h⟩

/-- One pinned basis install, inverted (relocated from the TT lane,
task #148 T6: both lanes' basis-block bridges invert the same fold). -/
theorem installBasisDecl_inv {env env₁ : Env} {ci : ConstantInfo}
    (h : installBasisDecl (m := CheckM) env ci = .ok env₁) :
    env.find? ci.name = none ∧ env₁ = ⟨ci :: env.consts⟩ := by
  unfold installBasisDecl at h
  revert h
  cases hf : env.find? ci.name with
  | none =>
    intro h
    simp only [Option.isNone_none, if_true, pure, Except.pure,
      Except.ok.injEq] at h
    exact ⟨rfl, h.symm⟩
  | some ci' =>
    intro h
    simp only [Option.isNone_some, Bool.false_eq_true, if_false,
      throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
    exact nomatch h
end ConLeche
