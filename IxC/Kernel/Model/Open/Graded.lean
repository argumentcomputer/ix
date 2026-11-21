module

public import IxC.Kernel.Model.Open.Levels

@[expose] public section

/-!
# Graded readings at open terms

`GradedBy` (`IxC/Kernel/Denotes.lean`) at the open-term reading `DenotesO`: every
application applies a function that denotes a member of a dependent product to an argument
in its domain. The rules' soundness over the public `Model` carries it beside the
denotation, because β fired with no certificate (`Red.betaGate`) and an application typed
with no argument certificate (`Infer.appSkip`) are sound on graded readings only.

* `GradedBy.toOpen`: a closed graded reading (a stored term, `Model.graded`) is an open one.
* `GradedBy.congr_envO`, `GradedBy.congr_fvarsO`: a grading reads the bound variables below
  the term's bound and the free variables the term mentions only.
* `GradedBy.instantiate1O`, `GradedBy.open_fvarO`: substitution and the opening of a binder.
* `GradedBy.instantiateLevelParamsO`: level instantiation.
* `GradedBy.mkAppN_headO`: a spine's reading and grading depend on its head's only.
-/

namespace Ix.Kernel

open SetTheory Ix.Kernel.SetModel

universe w

variable {V : Type w} [SetTheory V] {cval : Key md → (LevelParam → Nat) → V} {env : Env md}
  {φ : LevelParam → Nat} {σ : Nat → V}

/-- **A closed graded reading is an open one** (on a term with no free variable the two
readings agree). -/
theorem GradedBy.toOpen :
    ∀ {e : Expr md} {ρ : BVarIdx → V}, GradedBy (Denotes cval env φ) ρ e → e.hasFvar = false →
      GradedBy (DenotesO cval env φ σ) ρ e := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro ρ h hf
    simp only [GradedBy] at h ⊢
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    obtain ⟨hgf, hga, r, A, F, X, B, hF, hX, hm, hx, h0⟩ := h
    exact ⟨ihf hgf hf.1, iha hga hf.2, r, A, F, X, B, .of_denotes hF, .of_denotes hX, hm, hx, h0⟩
  | lam ty b m ihty ihb =>
    intro ρ h hf
    simp only [GradedBy] at h ⊢
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    exact ⟨ihty h.1 hf.1, fun A hA x hx => ihb (h.2 A (hA.to_denotes hf.1) x hx) hf.2⟩
  | forallE ty b m ihty ihb =>
    intro ρ h hf
    simp only [GradedBy] at h ⊢
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    exact ⟨ihty h.1 hf.1, fun A hA x hx => ihb (h.2 A (hA.to_denotes hf.1) x hx) hf.2⟩
  | proj s i e ih =>
    intro ρ h hf
    simp only [GradedBy] at h ⊢
    simp only [Expr.hasFvar] at hf
    exact ih h hf
  | bvar _ => intro _ _ _; exact True.intro
  | fvar _ _ _ => intro _ _ _; exact True.intro
  | sort _ => intro _ _ _; exact True.intro
  | const _ _ => intro _ _ _; exact True.intro
  | letE _ _ _ _ _ _ _ => intro _ _ _; exact True.intro
  | lit _ => intro _ _ _; exact True.intro

/-- **A grading reads the bound variables below the term's bound only.** -/
theorem GradedBy.congr_envO :
    ∀ {e : Expr md} {k : Nat} {ρ ρ' : BVarIdx → V}, (∀ i, i < k → ρ i = ρ' i) →
      e.looseBVarsBounded k = true →
      GradedBy (DenotesO cval env φ σ) ρ e → GradedBy (DenotesO cval env φ σ) ρ' e := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro k ρ ρ' hag hb h
    simp only [GradedBy] at h ⊢
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hgf, hga, r, A, F, X, B, hF, hX, hm, hx, h0⟩ := h
    exact ⟨ihf hag hb.1 hgf, iha hag hb.2 hga, r, A, F, X, B, hF.congr_env hag hb.1,
      hX.congr_env hag hb.2, hm, hx, h0⟩
  | lam ty b m ihty ihb =>
    intro k ρ ρ' hag hb h
    simp only [GradedBy] at h ⊢
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    refine ⟨ihty hag hb.1 h.1, fun A hA x hx => ?_⟩
    have hA' := hA.congr_env (fun i hi => (hag i hi).symm) hb.1
    refine ihb (k := k + 1) (ρ := push x ρ) (fun i hi => ?_) hb.2 (h.2 A hA' x hx)
    cases i with
    | zero => rfl
    | succ i => exact hag i (by omega)
  | forallE ty b m ihty ihb =>
    intro k ρ ρ' hag hb h
    simp only [GradedBy] at h ⊢
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    refine ⟨ihty hag hb.1 h.1, fun A hA x hx => ?_⟩
    have hA' := hA.congr_env (fun i hi => (hag i hi).symm) hb.1
    refine ihb (k := k + 1) (ρ := push x ρ) (fun i hi => ?_) hb.2 (h.2 A hA' x hx)
    cases i with
    | zero => rfl
    | succ i => exact hag i (by omega)
  | proj s i e ih =>
    intro k ρ ρ' hag hb h
    simp only [GradedBy] at h ⊢
    simp only [Expr.looseBVarsBounded] at hb
    exact ih hag hb h
  | bvar _ => intro _ _ _ _ _ _; exact True.intro
  | fvar _ _ _ => intro _ _ _ _ _ _; exact True.intro
  | sort _ => intro _ _ _ _ _ _; exact True.intro
  | const _ _ => intro _ _ _ _ _ _; exact True.intro
  | letE _ _ _ _ _ _ _ => intro _ _ _ _ _ _; exact True.intro
  | lit _ => intro _ _ _ _ _ _; exact True.intro

/-- A term with no loose bound variable is graded at every variable environment alike. -/
theorem GradedBy.closedO {ρ ρ' : BVarIdx → V} {e : Expr md}
    (h : GradedBy (DenotesO cval env φ σ) ρ e) (hb : e.looseBVarsBounded 0 = true) :
    GradedBy (DenotesO cval env φ σ) ρ' e :=
  GradedBy.congr_envO (k := 0) (fun _ h => absurd h (Nat.not_lt_zero _)) hb h

/-- **A grading reads the free variables the term mentions only.** -/
theorem GradedBy.congr_fvarsO :
    ∀ {e : Expr md} {ρ : BVarIdx → V} {σ' : Nat → V}, (∀ l ∈ e.fvarLeaves, σ l.1 = σ' l.1) →
      GradedBy (DenotesO cval env φ σ) ρ e → GradedBy (DenotesO cval env φ σ') ρ e := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro ρ σ' hag h
    simp only [GradedBy] at h ⊢
    have hagf : ∀ l ∈ f.fvarLeaves, σ l.1 = σ' l.1 := fun l hl =>
      hag l (by simp [Expr.fvarLeaves, hl])
    have haga : ∀ l ∈ a.fvarLeaves, σ l.1 = σ' l.1 := fun l hl =>
      hag l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hgf, hga, r, A, F, X, B, hF, hX, hm, hx, h0⟩ := h
    exact ⟨ihf hagf hgf, iha haga hga, r, A, F, X, B, hF.congr_fvars hagf,
      hX.congr_fvars haga, hm, hx, h0⟩
  | lam ty b m ihty ihb =>
    intro ρ σ' hag h
    simp only [GradedBy] at h ⊢
    have hagt : ∀ l ∈ ty.fvarLeaves, σ l.1 = σ' l.1 := fun l hl =>
      hag l (by simp [Expr.fvarLeaves, hl])
    have hagb : ∀ l ∈ b.fvarLeaves, σ l.1 = σ' l.1 := fun l hl =>
      hag l (by simp [Expr.fvarLeaves, hl])
    exact ⟨ihty hagt h.1, fun A hA x hx =>
      ihb hagb (h.2 A (hA.congr_fvars fun l hl => (hagt l hl).symm) x hx)⟩
  | forallE ty b m ihty ihb =>
    intro ρ σ' hag h
    simp only [GradedBy] at h ⊢
    have hagt : ∀ l ∈ ty.fvarLeaves, σ l.1 = σ' l.1 := fun l hl =>
      hag l (by simp [Expr.fvarLeaves, hl])
    have hagb : ∀ l ∈ b.fvarLeaves, σ l.1 = σ' l.1 := fun l hl =>
      hag l (by simp [Expr.fvarLeaves, hl])
    exact ⟨ihty hagt h.1, fun A hA x hx =>
      ihb hagb (h.2 A (hA.congr_fvars fun l hl => (hagt l hl).symm) x hx)⟩
  | proj s i e ih =>
    intro ρ σ' hag h
    simp only [GradedBy] at h ⊢
    exact ih (fun l hl => hag l (by simpa [Expr.fvarLeaves] using hl)) h
  | bvar _ => intro _ _ _ _; exact True.intro
  | fvar _ _ _ => intro _ _ _ _; exact True.intro
  | sort _ => intro _ _ _ _; exact True.intro
  | const _ _ => intro _ _ _ _; exact True.intro
  | letE _ _ _ _ _ _ _ => intro _ _ _ _; exact True.intro
  | lit _ => intro _ _ _ _; exact True.intro

/-- **Substitution for gradings**: at a value `a` with the same denotation `x` at every
variable environment, graded at every one, substituting `a` for bound variable `k` is
graded exactly when the term is, with `x` inserted at `k`. -/
theorem GradedBy.instantiate1O {a : Expr md} {x : V}
    (ha : ∀ ρ, DenotesO cval env φ σ ρ a x) (hga : ∀ ρ, GradedBy (DenotesO cval env φ σ) ρ a) :
    ∀ (e : Expr md) (k : Nat) (ρ : BVarIdx → V),
      GradedBy (DenotesO cval env φ σ) ρ (e.instantiate1 a k) ↔
        GradedBy (DenotesO cval env φ σ) (insertAt k x ρ) e := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ
    simp only [Expr.instantiate1]
    constructor
    · intro _; exact True.intro
    · intro _
      split
      · exact hga ρ
      · split
        · exact True.intro
        · exact True.intro
  | fvar i ty _ =>
    intro k ρ
    simp only [Expr.instantiate1]
    exact ⟨fun _ => True.intro, fun _ => True.intro⟩
  | sort u =>
    intro k ρ
    simp only [Expr.instantiate1]
    exact ⟨fun _ => True.intro, fun _ => True.intro⟩
  | const n us =>
    intro k ρ
    simp only [Expr.instantiate1]
    exact ⟨fun _ => True.intro, fun _ => True.intro⟩
  | app f b ihf ihb =>
    intro k ρ
    simp only [Expr.instantiate1, GradedBy]
    constructor
    · rintro ⟨hgf, hgb, r, A, F, X, B, hF, hX, hm, hx, h0⟩
      exact ⟨(ihf k ρ).1 hgf, (ihb k ρ).1 hgb, r, A, F, X, B,
        (DenotesO.instantiate1 ha f k ρ F).1 hF, (DenotesO.instantiate1 ha b k ρ X).1 hX,
        hm, hx, h0⟩
    · rintro ⟨hgf, hgb, r, A, F, X, B, hF, hX, hm, hx, h0⟩
      exact ⟨(ihf k ρ).2 hgf, (ihb k ρ).2 hgb, r, A, F, X, B,
        (DenotesO.instantiate1 ha f k ρ F).2 hF, (DenotesO.instantiate1 ha b k ρ X).2 hX,
        hm, hx, h0⟩
  | lam ty b m ihty ihb =>
    intro k ρ
    simp only [Expr.instantiate1, GradedBy]
    constructor
    · rintro ⟨hgt, hgb⟩
      refine ⟨(ihty k ρ).1 hgt, fun A hA y hy => ?_⟩
      have h := (ihb (k + 1) (push y ρ)).1
        (hgb A ((DenotesO.instantiate1 ha ty k ρ A).2 hA) y hy)
      rwa [← push_insertAt] at h
    · rintro ⟨hgt, hgb⟩
      refine ⟨(ihty k ρ).2 hgt, fun A hA y hy => ?_⟩
      refine (ihb (k + 1) (push y ρ)).2 ?_
      rw [← push_insertAt]
      exact hgb A ((DenotesO.instantiate1 ha ty k ρ A).1 hA) y hy
  | forallE ty b m ihty ihb =>
    intro k ρ
    simp only [Expr.instantiate1, GradedBy]
    constructor
    · rintro ⟨hgt, hgb⟩
      refine ⟨(ihty k ρ).1 hgt, fun A hA y hy => ?_⟩
      have h := (ihb (k + 1) (push y ρ)).1
        (hgb A ((DenotesO.instantiate1 ha ty k ρ A).2 hA) y hy)
      rwa [← push_insertAt] at h
    · rintro ⟨hgt, hgb⟩
      refine ⟨(ihty k ρ).2 hgt, fun A hA y hy => ?_⟩
      refine (ihb (k + 1) (push y ρ)).2 ?_
      rw [← push_insertAt]
      exact hgb A ((DenotesO.instantiate1 ha ty k ρ A).1 hA) y hy
  | letE ty val b lm _ _ _ =>
    intro k ρ
    simp only [Expr.instantiate1]
    exact ⟨fun _ => True.intro, fun _ => True.intro⟩
  | lit l =>
    intro k ρ
    simp only [Expr.instantiate1]
    exact ⟨fun _ => True.intro, fun _ => True.intro⟩
  | proj s i e ih =>
    intro k ρ
    simp only [Expr.instantiate1, GradedBy]
    exact ih k ρ

/-- Substitution at the innermost bound variable. -/
theorem GradedBy.instantiate1_zeroO {a : Expr md} {x : V}
    (ha : ∀ ρ, DenotesO cval env φ σ ρ a x) (hga : ∀ ρ, GradedBy (DenotesO cval env φ σ) ρ a)
    (e : Expr md) (ρ : BVarIdx → V) :
    GradedBy (DenotesO cval env φ σ) ρ (e.instantiate1 a) ↔
      GradedBy (DenotesO cval env φ σ) (push x ρ) e := by
  rw [← insertAt_zero]
  exact GradedBy.instantiate1O ha hga e 0 ρ

/-- **A binder's body, opened at a fresh free variable**, is graded exactly when the body
is, with the variable's set pushed. -/
theorem GradedBy.open_fvarO {d : Nat} {ty body : Expr md} {x : V}
    (hfresh : ∀ l ∈ body.fvarLeaves, l.1 ≠ d) (ρ : BVarIdx → V) :
    GradedBy (DenotesO cval env φ (setAt σ d x)) ρ (body.instantiate1 (.fvar d ty)) ↔
      GradedBy (DenotesO cval env φ σ) (push x ρ) body := by
  have hx : setAt σ d x d = x := by simp [setAt]
  have ha : ∀ ρ', DenotesO cval env φ (setAt σ d x) ρ' (.fvar d ty) x := fun ρ' => by
    have h := DenotesO.fvar (cval := cval) (env := env) (φ := φ) (σ := setAt σ d x) (ρ := ρ')
      (i := d) (ty := ty)
    rwa [hx] at h
  rw [GradedBy.instantiate1_zeroO ha (fun _ => True.intro) body ρ]
  constructor
  · intro h
    exact GradedBy.congr_fvarsO (fun l hl => by simp [setAt, hfresh l hl]) h
  · intro h
    exact GradedBy.congr_fvarsO (fun l hl => by simp [setAt, hfresh l hl]) h

/-- **Level instantiation for gradings**: the instantiated term is graded at `φ` exactly
when the term is at the assignment the instantiation induces. -/
theorem GradedBy.instantiateLevelParamsO (hcp : CvalParams cval env) (ks : List LevelParam)
    (us : List Level) :
    ∀ (e : Expr md) (ρ : BVarIdx → V),
      GradedBy (DenotesO cval env φ σ) ρ (e.instantiateLevelParams ks us) ↔
        GradedBy (DenotesO cval env (Level.substFn φ ks us) σ) ρ e := by
  intro e
  induction e with
  | bvar i =>
    intro ρ
    simp only [Expr.instantiateLevelParams]
    exact ⟨fun _ => True.intro, fun _ => True.intro⟩
  | fvar i ty _ =>
    intro ρ
    simp only [Expr.instantiateLevelParams]
    exact ⟨fun _ => True.intro, fun _ => True.intro⟩
  | sort u =>
    intro ρ
    simp only [Expr.instantiateLevelParams]
    exact ⟨fun _ => True.intro, fun _ => True.intro⟩
  | const n vs =>
    intro ρ
    simp only [Expr.instantiateLevelParams]
    exact ⟨fun _ => True.intro, fun _ => True.intro⟩
  | app f a ihf iha =>
    intro ρ
    simp only [Expr.instantiateLevelParams, GradedBy]
    constructor
    · rintro ⟨hgf, hga, r, A, F, X, B, hF, hX, hm, hx, h0⟩
      exact ⟨(ihf ρ).1 hgf, (iha ρ).1 hga, r, A, F, X, B,
        (DenotesO.instantiateLevelParams hcp ks us f ρ F).1 hF,
        (DenotesO.instantiateLevelParams hcp ks us a ρ X).1 hX, hm, hx, h0⟩
    · rintro ⟨hgf, hga, r, A, F, X, B, hF, hX, hm, hx, h0⟩
      exact ⟨(ihf ρ).2 hgf, (iha ρ).2 hga, r, A, F, X, B,
        (DenotesO.instantiateLevelParams hcp ks us f ρ F).2 hF,
        (DenotesO.instantiateLevelParams hcp ks us a ρ X).2 hX, hm, hx, h0⟩
  | lam ty body m ihty ihb =>
    intro ρ
    simp only [Expr.instantiateLevelParams, GradedBy]
    constructor
    · rintro ⟨hgt, hgb⟩
      exact ⟨(ihty ρ).1 hgt, fun A hA x hx =>
        (ihb _).1 (hgb A ((DenotesO.instantiateLevelParams hcp ks us ty ρ A).2 hA) x hx)⟩
    · rintro ⟨hgt, hgb⟩
      exact ⟨(ihty ρ).2 hgt, fun A hA x hx =>
        (ihb _).2 (hgb A ((DenotesO.instantiateLevelParams hcp ks us ty ρ A).1 hA) x hx)⟩
  | forallE ty body m ihty ihb =>
    intro ρ
    simp only [Expr.instantiateLevelParams, GradedBy]
    constructor
    · rintro ⟨hgt, hgb⟩
      exact ⟨(ihty ρ).1 hgt, fun A hA x hx =>
        (ihb _).1 (hgb A ((DenotesO.instantiateLevelParams hcp ks us ty ρ A).2 hA) x hx)⟩
    · rintro ⟨hgt, hgb⟩
      exact ⟨(ihty ρ).2 hgt, fun A hA x hx =>
        (ihb _).2 (hgb A ((DenotesO.instantiateLevelParams hcp ks us ty ρ A).1 hA) x hx)⟩
  | letE ty val body lm _ _ _ =>
    intro ρ
    simp only [Expr.instantiateLevelParams]
    exact ⟨fun _ => True.intro, fun _ => True.intro⟩
  | lit l =>
    intro ρ
    simp only [Expr.instantiateLevelParams]
    exact ⟨fun _ => True.intro, fun _ => True.intro⟩
  | proj s i e ih =>
    intro ρ
    simp only [Expr.instantiateLevelParams, GradedBy]
    exact ih ρ

/-- **A spine reads its head only**: replacing the head of `mkAppN f as` by a head with
the same denotations keeps the spine's denotations, and its grading when the new head is
graded wherever the old one is. -/
theorem GradedBy.mkAppN_headO {ρ : BVarIdx → V} :
    ∀ (as : List (Expr md)) {f f' : Expr md},
      (∀ v, DenotesO cval env φ σ ρ f v ↔ DenotesO cval env φ σ ρ f' v) →
      (GradedBy (DenotesO cval env φ σ) ρ f → GradedBy (DenotesO cval env φ σ) ρ f') →
      (∀ v, DenotesO cval env φ σ ρ (Expr.mkAppN f as) v ↔
          DenotesO cval env φ σ ρ (Expr.mkAppN f' as) v) ∧
        (GradedBy (DenotesO cval env φ σ) ρ (Expr.mkAppN f as) →
          GradedBy (DenotesO cval env φ σ) ρ (Expr.mkAppN f' as)) := by
  intro as
  induction as with
  | nil => intro f f' hD hG; exact ⟨hD, hG⟩
  | cons a as ih =>
    intro f f' hD hG
    simp only [Expr.mkAppN]
    refine ih (fun v => ⟨fun h => ?_, fun h => ?_⟩) (fun h => ?_)
    · cases h with
      | app hf ha => exact .app ((hD _).1 hf) ha
    · cases h with
      | app hf ha => exact .app ((hD _).2 hf) ha
    · simp only [GradedBy] at h ⊢
      obtain ⟨hgf, hga, r, A, F, X, B, hF, hX, hm, hx, h0⟩ := h
      exact ⟨hG hgf, hga, r, A, F, X, B, (hD F).1 hF, hX, hm, hx, h0⟩

end Ix.Kernel
