module

public import IxC.Kernel.Denotes
import IxC.Kernel.Verify.StrLitExpr

@[expose] public section

/-!
# `Denotes` at open terms

The kernel's rules (`IxC/Kernel/Rules/Rel.lean`) work on open terms: a binder opens with
a free variable `.fvar d ty` that carries its type, and a term at depth `d` has no loose
bound variable. Their soundness over the public `Model` reads such terms by `DenotesO`:
`Denotes` with one more rule, a free variable denotes what an assignment `σ` (by the
variable's de Bruijn level, as the checker numbers them) gives it.

* `DenotesO.of_denotes`, `DenotesO.to_denotes`: on a term with no free variable the two
  relations agree, so a stored constant's type or value is read the same way.
* `DenotesO.functional`: a term has at most one denotation.
* `DenotesO.congr_env`: a denotation reads the bound variables below the term's bound
  only.
* `DenotesO.instantiate1`: the substitution lemma for the checker's `instantiate1`, at a
  value with no loose bound variable (β, and the opening of a binder at a free variable,
  are instances).
-/

namespace Ix.Kernel

open SetTheory Ix.Kernel.SetModel

universe w

variable {V : Type w} [SetTheory V]

/-- `DenotesO cval env φ σ ρ e v`: `Denotes`, with free variables read through `σ`. -/
inductive DenotesO (cval : Key md → (LevelParam → Nat) → V) (env : Env md) (φ : LevelParam → Nat)
    (σ : Nat → V) : (BVarIdx → V) → Expr md → V → Prop
  | bvar {ρ : BVarIdx → V} {i : BVarIdx} :
      DenotesO cval env φ σ ρ (.bvar i) (ρ i)
  | fvar {ρ : BVarIdx → V} {i : Nat} {ty : Expr md} :
      DenotesO cval env φ σ ρ (.fvar i ty) (σ i)
  | sort {ρ : BVarIdx → V} {u : Level} :
      DenotesO cval env φ σ ρ (.sort u) (univ (Level.eval φ u))
  | const {ρ : BVarIdx → V} {n : Key md} {us : List Level} {ci : ConstantInfo md}
      (hf : env.find? n = some ci)
      (hlen : us.length = ci.toConstantVal.levelParams.length) :
      DenotesO cval env φ σ ρ (.const n us)
        (cval n (Level.substFn φ ci.toConstantVal.levelParams us))
  | app {ρ : BVarIdx → V} {f a : Expr md} {F X : V}
      (hf : DenotesO cval env φ σ ρ f F) (ha : DenotesO cval env φ σ ρ a X) :
      DenotesO cval env φ σ ρ (.app f a) (app F X)
  | lam {ρ : BVarIdx → V} {ty body : Expr md} {m : BinderMeta} {A : V} {F : V → V}
      (hA : DenotesO cval env φ σ ρ ty A)
      (hF : ∀ x, x ∈ˢ A → DenotesO cval env φ σ (push x ρ) body (F x))
      (hP : regime φ m.pw = 0 → ∀ x, x ∈ˢ A → F x = pt) :
      DenotesO cval env φ σ ρ (.lam ty body m) (lamR (regime φ m.pw) A F)
  | pi {ρ : BVarIdx → V} {ty body : Expr md} {m : BinderMeta} {A : V} {B : V → V}
      (hA : DenotesO cval env φ σ ρ ty A)
      (hB : ∀ x, x ∈ˢ A → DenotesO cval env φ σ (push x ρ) body (B x))
      (hP : regime φ m.pw = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0) :
      DenotesO cval env φ σ ρ (.forallE ty body m) (piR (regime φ m.pw) A B)
  | proj_table {ρ : BVarIdx → V} {T : Key md} {i : Nat} {e : Expr md} {entry : ProjEntry md}
      {P : V} (ht : env.findProj? T i = some entry) (he : DenotesO cval env φ σ ρ e P) :
      DenotesO cval env φ σ ρ (.proj T i e) (field (i + entry.off) P)
  | proj_fst {ρ : BVarIdx → V} {T : Key md} {e : Expr md} {P : V}
      (ht : env.findProj? T 0 = none) (he : DenotesO cval env φ σ ρ e P) :
      DenotesO cval env φ σ ρ (.proj T 0 e) (sfst P)
  | proj_snd {ρ : BVarIdx → V} {T : Key md} {e : Expr md} {P : V}
      (ht : env.findProj? T 1 = none) (he : DenotesO cval env φ σ ρ e P) :
      DenotesO cval env φ σ ρ (.proj T 1 e) (ssnd P)
  | natLit {ρ : BVarIdx → V} {n : Nat} {X : V}
      (h : DenotesO cval env φ σ ρ (natLitToConstructor n) X) :
      DenotesO cval env φ σ ρ (.lit (.natVal n)) X
  | strLit {ρ : BVarIdx → V} {s : String} {X : V}
      (h : DenotesO cval env φ σ ρ (strLitToConstructor s) X) :
      DenotesO cval env φ σ ρ (.lit (.strVal s)) X

variable {cval : Key md → (LevelParam → Nat) → V} {env : Env md} {φ : LevelParam → Nat}
  {σ : Nat → V}

theorem natLitToConstructor_hasFvar (n : Nat) :
    ((natLitToConstructor (md := md)) n).hasFvar = false := by
  cases n <;> rfl

theorem natLitToConstructor_looseBVarsBounded (n k : Nat) :
    ((natLitToConstructor (md := md)) n).looseBVarsBounded k = true := by
  cases n <;> rfl

/-- **A closed reading is an open one.** -/
theorem DenotesO.of_denotes {ρ : BVarIdx → V} {e : Expr md} {v : V}
    (h : Denotes cval env φ ρ e v) : DenotesO cval env φ σ ρ e v := by
  induction h with
  | bvar => exact .bvar
  | sort => exact .sort
  | const hf hlen => exact .const hf hlen
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ hP ihA ihF => exact .lam ihA ihF hP
  | pi _ _ hP ihA ihB => exact .pi ihA ihB hP
  | proj_table ht _ ih => exact .proj_table ht ih
  | proj_fst ht _ ih => exact .proj_fst ht ih
  | proj_snd ht _ ih => exact .proj_snd ht ih
  | natLit _ ih => exact .natLit ih
  | strLit _ ih => exact .strLit ih

/-- **On a term with no free variable, an open reading is the closed one.** -/
theorem DenotesO.to_denotes {ρ : BVarIdx → V} {e : Expr md} {v : V}
    (h : DenotesO cval env φ σ ρ e v) : e.hasFvar = false → Denotes cval env φ ρ e v := by
  induction h with
  | bvar => exact fun _ => .bvar
  | fvar => intro hf; exact absurd hf (by simp [Expr.hasFvar])
  | sort => exact fun _ => .sort
  | const hf hlen => exact fun _ => .const hf hlen
  | app _ _ ihf iha =>
    intro hf
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    exact .app (ihf hf.1) (iha hf.2)
  | lam _ _ hP ihA ihF =>
    intro hf
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    exact .lam (ihA hf.1) (fun x hx => ihF x hx hf.2) hP
  | pi _ _ hP ihA ihB =>
    intro hf
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    exact .pi (ihA hf.1) (fun x hx => ihB x hx hf.2) hP
  | proj_table ht _ ih => exact fun hf => .proj_table ht (ih hf)
  | proj_fst ht _ ih => exact fun hf => .proj_fst ht (ih hf)
  | proj_snd ht _ ih => exact fun hf => .proj_snd ht (ih hf)
  | natLit _ ih => exact fun _ => .natLit (ih (natLitToConstructor_hasFvar _))
  | strLit _ ih => exact fun _ => .strLit (ih (strLitToConstructor_hasFvar _))

/-- **An open term has at most one denotation** (`Denotes_functional`'s twin). -/
theorem DenotesO.functional {ρ : BVarIdx → V} {e : Expr md} {v w : V}
    (hv : DenotesO cval env φ σ ρ e v) (hw : DenotesO cval env φ σ ρ e w) : v = w := by
  induction hv generalizing w with
  | bvar => cases hw; rfl
  | fvar => cases hw; rfl
  | sort => cases hw; rfl
  | const hf _ =>
    cases hw with
    | const hf' _ => rw [hf] at hf'; cases hf'; rfl
  | app _ _ ihf iha =>
    cases hw with
    | app hf' ha' => rw [ihf hf', iha ha']
  | lam _ _ _ ihA ihF =>
    cases hw with
    | lam hA' hF' _ =>
      obtain rfl := ihA hA'
      exact Ix.Kernel.SetModel.lamR_congr fun x hx => ihF x hx (hF' x hx)
  | pi _ _ _ ihA ihB =>
    cases hw with
    | pi hA' hB' _ =>
      obtain rfl := ihA hA'
      exact Ix.Kernel.SetModel.piR_congr fun x hx => ihB x hx (hB' x hx)
  | proj_table ht _ ih =>
    cases hw with
    | proj_table ht' he' => rw [ht] at ht'; cases ht'; rw [ih he']
    | proj_fst ht' _ => rw [ht] at ht'; exact nomatch ht'
    | proj_snd ht' _ => rw [ht] at ht'; exact nomatch ht'
  | proj_fst ht _ ih =>
    cases hw with
    | proj_table ht' _ => rw [ht] at ht'; exact nomatch ht'
    | proj_fst _ he' => rw [ih he']
  | proj_snd ht _ ih =>
    cases hw with
    | proj_table ht' _ => rw [ht] at ht'; exact nomatch ht'
    | proj_snd _ he' => rw [ih he']
  | natLit _ ih =>
    cases hw with
    | natLit h' => exact ih h'
  | strLit _ ih =>
    cases hw with
    | strLit h' => exact ih h'

/-- **A denotation reads the bound variables below the term's bound only.** -/
theorem DenotesO.congr_env {ρ : BVarIdx → V} {e : Expr md} {v : V}
    (h : DenotesO cval env φ σ ρ e v) :
    ∀ {k : Nat} {ρ' : BVarIdx → V}, (∀ i, i < k → ρ i = ρ' i) →
      e.looseBVarsBounded k = true → DenotesO cval env φ σ ρ' e v := by
  induction h with
  | @bvar ρ i =>
    intro k ρ' hag hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    rw [hag i hb]
    exact .bvar
  | fvar => exact fun _ _ => .fvar
  | sort => exact fun _ _ => .sort
  | const hf hlen => exact fun _ _ => .const hf hlen
  | app _ _ ihf iha =>
    intro k ρ' hag hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact .app (ihf hag hb.1) (iha hag hb.2)
  | lam _ _ hP ihA ihF =>
    intro k ρ' hag hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    refine .lam (ihA hag hb.1) (fun x hx => ihF x hx (k := k + 1) (fun i hi => ?_) hb.2) hP
    cases i with
    | zero => rfl
    | succ i => exact hag i (by omega)
  | pi _ _ hP ihA ihB =>
    intro k ρ' hag hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    refine .pi (ihA hag hb.1) (fun x hx => ihB x hx (k := k + 1) (fun i hi => ?_) hb.2) hP
    cases i with
    | zero => rfl
    | succ i => exact hag i (by omega)
  | proj_table ht _ ih => exact fun hag hb => .proj_table ht (ih hag hb)
  | proj_fst ht _ ih => exact fun hag hb => .proj_fst ht (ih hag hb)
  | proj_snd ht _ ih => exact fun hag hb => .proj_snd ht (ih hag hb)
  | natLit _ ih =>
    exact fun _ _ => .natLit (ih (k := 0) (fun _ h => absurd h (Nat.not_lt_zero _))
      (natLitToConstructor_looseBVarsBounded _ 0))
  | strLit _ ih =>
    exact fun _ _ => .strLit (ih (k := 0) (fun _ h => absurd h (Nat.not_lt_zero _))
      (strLitToConstructor_looseBVars _ 0))

/-- A term with no loose bound variable denotes the same set at every variable
environment. -/
theorem DenotesO.closed {ρ ρ' : BVarIdx → V} {e : Expr md} {v : V}
    (h : DenotesO cval env φ σ ρ e v) (hb : e.looseBVarsBounded 0 = true) :
    DenotesO cval env φ σ ρ' e v :=
  h.congr_env (k := 0) (fun _ h => absurd h (Nat.not_lt_zero _)) hb

/-! ## Substitution -/

omit [SetTheory V] in
/-- Insert `x` at index `k` of a variable environment: the indices below `k` keep their
sets, `k` gets `x`, and every index above moves up by one (`insertAt 0 = push`). -/
def insertAt (k : Nat) (x : V) (ρ : BVarIdx → V) : BVarIdx → V :=
  fun i => if i < k then ρ i else if i = k then x else ρ (i - 1)

omit [SetTheory V] in
theorem insertAt_zero (x : V) (ρ : BVarIdx → V) : insertAt 0 x ρ = push x ρ := by
  funext i
  cases i with
  | zero => simp [insertAt, push]
  | succ i => simp [insertAt, push]

omit [SetTheory V] in
theorem push_insertAt (y x : V) (k : Nat) (ρ : BVarIdx → V) :
    push y (insertAt k x ρ) = insertAt (k + 1) x (push y ρ) := by
  funext i
  cases i with
  | zero => simp [insertAt, push]
  | succ i =>
    simp only [push, insertAt]
    by_cases h1 : i < k
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]
      by_cases h2 : i = k
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        simp [push]

/-- **The substitution lemma**: at a value `a` with the same denotation `x` at every
variable environment (a term with no loose bound variable: `DenotesO.closed`),
substituting `a` for bound variable `k` denotes what the term denotes with `x` inserted
at `k`. -/
theorem DenotesO.instantiate1 {a : Expr md} {x : V}
    (ha : ∀ ρ, DenotesO cval env φ σ ρ a x) :
    ∀ (e : Expr md) (k : Nat) (ρ : BVarIdx → V) (v : V),
      DenotesO cval env φ σ ρ (e.instantiate1 a k) v ↔
        DenotesO cval env φ σ (insertAt k x ρ) e v := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ v
    simp only [Expr.instantiate1]
    by_cases hik : i = k
    · subst hik
      rw [if_pos rfl]
      have hx : insertAt i x ρ i = x := by simp [insertAt]
      constructor
      · intro h
        rw [DenotesO.functional h (ha ρ)]
        have hb := DenotesO.bvar (cval := cval) (env := env) (φ := φ) (σ := σ)
          (ρ := insertAt i x ρ) (i := i)
        rwa [hx] at hb
      · intro h
        cases h
        rw [hx]
        exact ha ρ
    · rw [if_neg hik]
      by_cases hgt : i > k
      · rw [if_pos hgt]
        have hv : insertAt k x ρ i = ρ (i - 1) := by
          simp only [insertAt, if_neg (show ¬ i < k by omega), if_neg hik]
        constructor
        · intro h
          cases h
          rw [← hv]
          exact .bvar
        · intro h
          cases h
          rw [hv]
          exact .bvar
      · rw [if_neg hgt]
        have hv : insertAt k x ρ i = ρ i := by
          simp only [insertAt, if_pos (show i < k by omega)]
        constructor
        · intro h
          cases h
          rw [← hv]
          exact .bvar
        · intro h
          cases h
          rw [hv]
          exact .bvar
  | fvar i ty =>
    intro k ρ v
    simp only [Expr.instantiate1]
    constructor
    · intro h; cases h; exact .fvar
    · intro h; cases h; exact .fvar
  | sort u =>
    intro k ρ v
    simp only [Expr.instantiate1]
    constructor
    · intro h; cases h; exact .sort
    · intro h; cases h; exact .sort
  | const n us =>
    intro k ρ v
    simp only [Expr.instantiate1]
    constructor
    · intro h
      cases h with
      | const hf hlen => exact .const hf hlen
    · intro h
      cases h with
      | const hf hlen => exact .const hf hlen
  | app f b ihf ihb =>
    intro k ρ v
    simp only [Expr.instantiate1]
    constructor
    · intro h
      cases h with
      | app hf hb => exact .app ((ihf k ρ _).1 hf) ((ihb k ρ _).1 hb)
    · intro h
      cases h with
      | app hf hb => exact .app ((ihf k ρ _).2 hf) ((ihb k ρ _).2 hb)
  | lam ty b m ihty ihb =>
    intro k ρ v
    simp only [Expr.instantiate1]
    constructor
    · intro h
      cases h with
      | lam hA hF hP =>
        refine .lam ((ihty k ρ _).1 hA) (fun y hy => ?_) hP
        rw [push_insertAt]
        exact (ihb (k + 1) (push y ρ) _).1 (hF y hy)
    · intro h
      cases h with
      | lam hA hF hP =>
        refine .lam ((ihty k ρ _).2 hA) (fun y hy => ?_) hP
        refine (ihb (k + 1) (push y ρ) _).2 ?_
        rw [← push_insertAt]
        exact hF y hy
  | forallE ty b m ihty ihb =>
    intro k ρ v
    simp only [Expr.instantiate1]
    constructor
    · intro h
      cases h with
      | pi hA hB hP =>
        refine .pi ((ihty k ρ _).1 hA) (fun y hy => ?_) hP
        rw [push_insertAt]
        exact (ihb (k + 1) (push y ρ) _).1 (hB y hy)
    · intro h
      cases h with
      | pi hA hB hP =>
        refine .pi ((ihty k ρ _).2 hA) (fun y hy => ?_) hP
        refine (ihb (k + 1) (push y ρ) _).2 ?_
        rw [← push_insertAt]
        exact hB y hy
  | letE ty val b lm _ _ _ =>
    intro k ρ v
    simp only [Expr.instantiate1]
    constructor
    · intro h; cases h
    · intro h; cases h
  | lit l =>
    intro k ρ v
    simp only [Expr.instantiate1]
    exact ⟨fun h => h.closed rfl, fun h => h.closed rfl⟩
  | proj s i e ih =>
    intro k ρ v
    simp only [Expr.instantiate1]
    constructor
    · intro h
      cases h with
      | proj_table ht he => exact .proj_table ht ((ih k ρ _).1 he)
      | proj_fst ht he => exact .proj_fst ht ((ih k ρ _).1 he)
      | proj_snd ht he => exact .proj_snd ht ((ih k ρ _).1 he)
    · intro h
      cases h with
      | proj_table ht he => exact .proj_table ht ((ih k ρ _).2 he)
      | proj_fst ht he => exact .proj_fst ht ((ih k ρ _).2 he)
      | proj_snd ht he => exact .proj_snd ht ((ih k ρ _).2 he)

/-- **β and the opening of a binder, at the innermost bound variable**: substituting a
value with no loose bound variable for bound variable `0`. -/
theorem DenotesO.instantiate1_zero {a : Expr md} {x : V}
    (ha : ∀ ρ, DenotesO cval env φ σ ρ a x) (e : Expr md) (ρ : BVarIdx → V) (v : V) :
    DenotesO cval env φ σ ρ (e.instantiate1 a) v ↔ DenotesO cval env φ σ (push x ρ) e v := by
  rw [← insertAt_zero]
  exact DenotesO.instantiate1 ha e 0 ρ v

end Ix.Kernel
