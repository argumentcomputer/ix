import Ix.CompileCert.Conv.Rel

/-!
# M7 X1: simple types of the erased terms (the domain of the development)

`Ix.Expr` has no typing judgment, and the development (`Develop.lean`) is untyped: its
termination is "the typed argument of the design document (each hereditary step substitutes at
a strictly smaller type)" (`Ix/Compile/Image/Develop.lean`, docstring). This module gives that
argument a judgment it can be stated in: **simple types of the erasure**,

* `Ty`: a base type `o`, arrows, and the two pair types the development reduces (`PProd`'s and
  `And`'s, `pairP`/`pairA`);
* `Typ Γ t τ`: bound variables have their context's type; an application needs an arrow; a λ
  has an arrow type (its binder annotation only needs to be typable, at any type: annotations
  are terms the development also rewrites, not types it reads); `PProd.mk`/`And.intro` build
  pairs and `PProd`/`And` projections take them apart; **every other constant, free variable,
  sort, literal, Π and projection is opaque**: it can be given any type, so polymorphic
  constants (`id (Nat → Nat) f 0`) are typable at each occurrence independently.

A Lean term that is well typed in Lean is not always simply typable this way (a variable of a
polymorphic type used at two incompatible arities; a dependent type whose arity depends on a
value), so typability is a hypothesis about the input, decided by first-order unification
(the census `Tests/Ix/Compile/DevCensus.lean` runs it on every development the compiler makes).
It is what the termination argument needs: the development never contracts a redex whose head
is opaque, and the pair projections it contracts are typed.

The theory: weakening (`Typ.lift`), strengthening (`Typ.lower`), substitution (`Typ.inst`),
application spines (`Typ.appN_iff`).
-/

namespace Ix.CompileCert.Conv

open Ix (Name Level Expr)

/-- Simple types: a base type, arrows, `PProd`-pairs and `And`-pairs. -/
inductive Ty where
  | o
  | arr (a b : Ty)
  | pairP (a b : Ty)
  | pairA (a b : Ty)
  deriving Inhabited

namespace Ty

def size : Ty → Nat
  | o => 1
  | arr a b | pairP a b | pairA a b => a.size + b.size + 1

/-- The pair type of kind `k` (`true`: `PProd`, `false`: `And`). -/
def pair : Bool → Ty → Ty → Ty
  | true, a, b => pairP a b
  | false, a, b => pairA a b

/-- `σ₁ → … → σₙ → τ`. -/
def arrows : List Ty → Ty → Ty
  | [], τ => τ
  | σ :: σs, τ => arr σ (arrows σs τ)

theorem pair_inj {k k' : Bool} {a b a' b' : Ty} (h : pair k a b = pair k' a' b') :
    k = k' ∧ a = a' ∧ b = b' := by
  cases k <;> cases k' <;> simp [pair] at h ⊢ <;> exact h

theorem size_pos : ∀ (τ : Ty), 0 < τ.size
  | o => by simp [size]
  | arr .. | pairP .. | pairA .. => by simp [size]

theorem size_pair (k : Bool) (a b : Ty) : (pair k a b).size = a.size + b.size + 1 := by
  cases k <;> rfl

end Ty

/-- The pair structure a projection name denotes (the tests of `projCtor?`, first `PProd`). -/
def pairKind (s : Name) : Option Bool :=
  if s == Ix.Compile.Image.nPProd then some true
  else if s == Ix.Compile.Image.nAnd then some false else none

/-- The pair a constructor name builds. -/
def ctorKind (c : Name) : Option Bool :=
  if c == Ix.Compile.Image.nPProdMk then some true
  else if c == Ix.Compile.Image.nAndIntro then some false else none

/-- **Simple types of the erased terms.** -/
inductive Typ : List Ty → Tm → Ty → Prop
  | bvar {Γ : List Ty} {i : Nat} {τ : Ty} : Γ[i]? = some τ → Typ Γ (.bvar i) τ
  | fvar {Γ : List Ty} (x : Name) (τ : Ty) : Typ Γ (.fvar x) τ
  | mvar {Γ : List Ty} (x : Name) (τ : Ty) : Typ Γ (.mvar x) τ
  | sort {Γ : List Ty} (u : Level) (τ : Ty) : Typ Γ (.sort u) τ
  | lit {Γ : List Ty} (l : Lean.Literal) (τ : Ty) : Typ Γ (.lit l) τ
  | const {Γ : List Ty} {c : Name} (us : Array Level) (τ : Ty) : ctorKind c = none →
      Typ Γ (.const c us) τ
  | pairMk {Γ : List Ty} {c : Name} {k : Bool} (us : Array Level) (α β a b : Ty) :
      ctorKind c = some k → Typ Γ (.const c us) (.arr α (.arr β (.arr a (.arr b (Ty.pair k a b)))))
  | app {Γ : List Ty} {f a : Tm} {σ τ : Ty} : Typ Γ f (.arr σ τ) → Typ Γ a σ → Typ Γ (.app f a) τ
  | lam {Γ : List Ty} {t b : Tm} {ρ σ τ : Ty} : Typ Γ t ρ → Typ (σ :: Γ) b τ →
      Typ Γ (.lam t b) (.arr σ τ)
  | pi {Γ : List Ty} {t b : Tm} {ρ σ ρ' : Ty} (τ : Ty) : Typ Γ t ρ → Typ (σ :: Γ) b ρ' →
      Typ Γ (.pi t b) τ
  | letE {Γ : List Ty} {t v b : Tm} {ρ σ τ : Ty} : Typ Γ t ρ → Typ Γ v σ → Typ (σ :: Γ) b τ →
      Typ Γ (.letE t v b) τ
  | proj0 {Γ : List Ty} {s : Name} {x : Tm} {k : Bool} {a b : Ty} : pairKind s = some k →
      Typ Γ x (Ty.pair k a b) → Typ Γ (.proj s 0 x) a
  | proj1 {Γ : List Ty} {s : Name} {x : Tm} {k : Bool} {a b : Ty} : pairKind s = some k →
      Typ Γ x (Ty.pair k a b) → Typ Γ (.proj s 1 x) b
  | projOpaque {Γ : List Ty} {s : Name} {i : Nat} {x : Tm} {ρ : Ty} (τ : Ty) :
      (pairKind s = none ∨ 2 ≤ i) → Typ Γ x ρ → Typ Γ (.proj s i x) τ

/-- Arguments typed pointwise. -/
inductive TypArgs (Γ : List Ty) : List Tm → List Ty → Prop
  | nil : TypArgs Γ [] []
  | cons {a : Tm} {σ : Ty} {as : List Tm} {σs : List Ty} :
      Typ Γ a σ → TypArgs Γ as σs → TypArgs Γ (a :: as) (σ :: σs)

namespace Typ

/-! ## Application spines -/

theorem appN_iff {Γ : List Ty} : ∀ {h : Tm} {as : List Tm} {τ : Ty},
    Typ Γ (Tm.appN h as) τ ↔ ∃ σs, Typ Γ h (Ty.arrows σs τ) ∧ TypArgs Γ as σs
  | h, [], τ => by
    simp only [Tm.appN_nil]
    constructor
    · intro t; exact ⟨[], t, .nil⟩
    · rintro ⟨σs, t, ha⟩; cases ha; exact t
  | h, a :: as, τ => by
    rw [Tm.appN_cons, appN_iff]
    constructor
    · rintro ⟨σs, t, ha⟩
      cases t with
      | app tf ta => exact ⟨_ :: σs, tf, .cons ta ha⟩
    · rintro ⟨σs, t, ha⟩
      cases ha with
      | cons ta ha' => exact ⟨_, .app t ta, ha'⟩

/-! ## Weakening -/

theorem lift {Θ Δ : List Ty} (Ξ : List Ty) {t : Tm} {τ : Ty} (h : Typ (Θ ++ Δ) t τ) :
    Typ (Θ ++ Ξ ++ Δ) (Tm.lift Ξ.length Θ.length t) τ := by
  generalize hΓ : Θ ++ Δ = Γ at h
  induction h generalizing Θ with
  | bvar hi =>
    subst hΓ
    rename_i i τ
    simp only [Tm.lift]
    apply Typ.bvar
    by_cases hc : Θ.length ≤ i
    · simp only [hc, ↓reduceIte]
      rw [List.getElem?_append_right (by simp; omega), List.length_append]
      rw [List.getElem?_append_right hc] at hi
      rw [← hi]; congr 1; omega
    · simp only [hc, ↓reduceIte]
      rw [List.append_assoc, List.getElem?_append_left (by omega)]
      rw [List.getElem?_append_left (by omega)] at hi
      exact hi
  | fvar x τ => exact .fvar x τ
  | mvar x τ => exact .mvar x τ
  | sort u τ => exact .sort u τ
  | lit l τ => exact .lit l τ
  | const us τ hc => exact .const us τ hc
  | pairMk us α β a b hc => exact .pairMk us α β a b hc
  | app _ _ ih1 ih2 => exact .app (ih1 hΓ) (ih2 hΓ)
  | @lam _ _ _ _ σ τ _ _ ih1 ih2 =>
    simp only [Tm.lift]
    refine .lam (ih1 hΓ) ?_
    have := @ih2 (σ :: Θ) (by rw [← hΓ]; rfl)
    simpa using this
  | @pi _ _ _ _ σ ρ' τ _ _ ih1 ih2 =>
    simp only [Tm.lift]
    refine Typ.pi (σ := σ) (ρ' := ρ') τ (ih1 hΓ) ?_
    have := @ih2 (σ :: Θ) (by rw [← hΓ]; rfl)
    simpa using this
  | @letE _ _ _ _ _ σ τ _ _ _ ih1 ih2 ih3 =>
    simp only [Tm.lift]
    refine .letE (ih1 hΓ) (ih2 hΓ) ?_
    have := @ih3 (σ :: Θ) (by rw [← hΓ]; rfl)
    simpa using this
  | proj0 hk _ ih => exact .proj0 hk (ih hΓ)
  | proj1 hk _ ih => exact .proj1 hk (ih hΓ)
  | projOpaque τ hs _ ih => exact .projOpaque τ hs (ih hΓ)

/-- Weakening at the front: a term of `Δ` lifted under `Θ`. -/
theorem lift_front {Δ : List Ty} (Θ : List Ty) {t : Tm} {τ : Ty} (h : Typ Δ t τ) :
    Typ (Θ ++ Δ) (Tm.lift Θ.length 0 t) τ := by
  have := @lift [] Δ Θ t τ h
  simpa using this

/-! ## Strengthening -/

theorem lower {Θ Δ : List Ty} {σ : Ty} {t : Tm} {τ : Ty} (h : Typ (Θ ++ σ :: Δ) t τ)
    (hocc : Tm.occ t Θ.length = false) : Typ (Θ ++ Δ) (Tm.lower 1 Θ.length t) τ := by
  generalize hΓ : Θ ++ σ :: Δ = Γ at h
  induction h generalizing Θ with
  | bvar hi =>
    subst hΓ
    rename_i i τ
    simp only [Tm.occ, beq_eq_false_iff_ne, ne_eq] at hocc
    simp only [Tm.lower]
    apply Typ.bvar
    by_cases hc : Θ.length + 1 ≤ i
    · simp only [hc, ↓reduceIte]
      rw [List.getElem?_append_right (by omega)]
      rw [List.getElem?_append_right (by omega)] at hi
      have : i - Θ.length = (i - 1 - Θ.length) + 1 := by omega
      rw [this, List.getElem?_cons_succ] at hi
      exact hi
    · simp only [hc, ↓reduceIte]
      have hlt : i < Θ.length := by omega
      rw [List.getElem?_append_left hlt]
      rw [List.getElem?_append_left hlt] at hi
      exact hi
  | fvar x τ => exact .fvar x τ
  | mvar x τ => exact .mvar x τ
  | sort u τ => exact .sort u τ
  | lit l τ => exact .lit l τ
  | const us τ hc => exact .const us τ hc
  | pairMk us α β a b hc => exact .pairMk us α β a b hc
  | app _ _ ih1 ih2 =>
    simp only [Tm.occ, Bool.or_eq_false_iff] at hocc
    exact .app (ih1 hocc.1 hΓ) (ih2 hocc.2 hΓ)
  | @lam _ _ _ _ σ' τ _ _ ih1 ih2 =>
    simp only [Tm.occ, Bool.or_eq_false_iff] at hocc
    simp only [Tm.lower]
    refine .lam (ih1 hocc.1 hΓ) ?_
    have := @ih2 (σ' :: Θ) (by simpa using hocc.2) (by rw [← hΓ]; rfl)
    simpa using this
  | @pi _ _ _ _ σ' ρ' τ _ _ ih1 ih2 =>
    simp only [Tm.occ, Bool.or_eq_false_iff] at hocc
    simp only [Tm.lower]
    refine Typ.pi (σ := σ') (ρ' := ρ') τ (ih1 hocc.1 hΓ) ?_
    have := @ih2 (σ' :: Θ) (by simpa using hocc.2) (by rw [← hΓ]; rfl)
    simpa using this
  | @letE _ _ _ _ _ σ' τ _ _ _ ih1 ih2 ih3 =>
    simp only [Tm.occ, Bool.or_eq_false_iff] at hocc
    simp only [Tm.lower]
    refine .letE (ih1 hocc.1.1 hΓ) (ih2 hocc.1.2 hΓ) ?_
    have := @ih3 (σ' :: Θ) (by simpa using hocc.2) (by rw [← hΓ]; rfl)
    simpa using this
  | proj0 hk _ ih => simp only [Tm.occ] at hocc; exact .proj0 hk (ih hocc hΓ)
  | proj1 hk _ ih => simp only [Tm.occ] at hocc; exact .proj1 hk (ih hocc hΓ)
  | projOpaque τ hs _ ih => simp only [Tm.occ] at hocc; exact .projOpaque τ hs (ih hocc hΓ)

/-! ## Substitution -/

theorem inst {Θ Δ : List Ty} {σ : Ty} {t v : Tm} {τ : Ty} (h : Typ (Θ ++ σ :: Δ) t τ)
    (hv : Typ Δ v σ) : Typ (Θ ++ Δ) (Tm.inst v Θ.length t) τ := by
  generalize hΓ : Θ ++ σ :: Δ = Γ at h
  induction h generalizing Θ with
  | bvar hi =>
    subst hΓ
    rename_i i τ
    simp only [Tm.inst]
    by_cases he : i = Θ.length
    · subst he
      simp only [↓reduceIte]
      rw [List.getElem?_append_right (by omega), Nat.sub_self, List.getElem?_cons_zero] at hi
      cases hi
      exact lift_front Θ hv
    · simp only [he, ↓reduceIte]
      apply Typ.bvar
      by_cases hk : Θ.length < i
      · simp only [hk, ↓reduceIte]
        rw [List.getElem?_append_right (by omega)]
        rw [List.getElem?_append_right (by omega)] at hi
        have : i - Θ.length = (i - 1 - Θ.length) + 1 := by omega
        rw [this, List.getElem?_cons_succ] at hi
        exact hi
      · simp only [hk, ↓reduceIte]
        have hlt : i < Θ.length := by omega
        rw [List.getElem?_append_left hlt]
        rw [List.getElem?_append_left hlt] at hi
        exact hi
  | fvar x τ => exact .fvar x τ
  | mvar x τ => exact .mvar x τ
  | sort u τ => exact .sort u τ
  | lit l τ => exact .lit l τ
  | const us τ hc => exact .const us τ hc
  | pairMk us α β a b hc => exact .pairMk us α β a b hc
  | app _ _ ih1 ih2 => exact .app (ih1 hΓ) (ih2 hΓ)
  | @lam _ _ _ _ σ' τ _ _ ih1 ih2 =>
    simp only [Tm.inst]
    refine .lam (ih1 hΓ) ?_
    have := @ih2 (σ' :: Θ) (by rw [← hΓ]; rfl)
    simpa using this
  | @pi _ _ _ _ σ' ρ' τ _ _ ih1 ih2 =>
    simp only [Tm.inst]
    refine Typ.pi (σ := σ') (ρ' := ρ') τ (ih1 hΓ) ?_
    have := @ih2 (σ' :: Θ) (by rw [← hΓ]; rfl)
    simpa using this
  | @letE _ _ _ _ _ σ' τ _ _ _ ih1 ih2 ih3 =>
    simp only [Tm.inst]
    refine .letE (ih1 hΓ) (ih2 hΓ) ?_
    have := @ih3 (σ' :: Θ) (by rw [← hΓ]; rfl)
    simpa using this
  | proj0 hk _ ih => exact .proj0 hk (ih hΓ)
  | proj1 hk _ ih => exact .proj1 hk (ih hΓ)
  | projOpaque τ hs _ ih => exact .projOpaque τ hs (ih hΓ)

end Typ

/-! ## Arguments -/

namespace TypArgs

theorem length {Γ : List Ty} {as : List Tm} {σs : List Ty} (h : TypArgs Γ as σs) :
    as.length = σs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem append {Γ : List Ty} {as bs : List Tm} {σs τs : List Ty} (h1 : TypArgs Γ as σs)
    (h2 : TypArgs Γ bs τs) : TypArgs Γ (as ++ bs) (σs ++ τs) := by
  induction h1 with
  | nil => exact h2
  | cons t _ ih => exact .cons t ih

end TypArgs

theorem Ty.arrows_append (σs τs : List Ty) (ρ : Ty) :
    Ty.arrows (σs ++ τs) ρ = Ty.arrows σs (Ty.arrows τs ρ) := by
  induction σs with
  | nil => rfl
  | cons σ σs ih => simp [Ty.arrows, ih]

end Ix.CompileCert.Conv
