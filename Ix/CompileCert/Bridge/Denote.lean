import Ix.CompileCert.Bridge.Lane
import Ix.CompileCert.Installed

/-!
# M7 X2: the public reading under the de Bruijn and universe operations

The checker's public semantics `Kernel.Denotes cval env φ ρ e v` (`IxC/Kernel/Denotes.lean`) reads a
closed term `e` at a universe assignment `φ` and a bound-variable environment `ρ`. IxC states its
substitution and level-instantiation metatheory on the internal readings (`denote`, `denoteMeta`),
not on the public relation (PLAN-B §1). This module proves the public versions the bridge needs,
by induction on the derivation, using only the relation's constructors:

* `Denotes.lift`: a term read at `liftEnv n c ρ` is read at `ρ` once lifted (`liftLooseBVars`);
* `Denotes.inst`: a term read with `x` at index `k` is read with `v` substituted
  (`instantiate1Lift`, X1's `Tm.inst`), when `v` reads to `x` below the `k` crossed binders;
* `Denotes.lower`: lowering (`lowerBVars`) over an unused window;
* `Denotes.levels`: a term read at the composed assignment `substFn φ ks us` is read at `φ` once
  its universes are instantiated (`instantiateLevelParams`), for a level-local interpretation
  (`CvalLocal`, which every strong model has: `StrongInstalledModel.value_params`);
* `Denotes.env_agree`: a term reads the same under environments agreeing on its loose variables.

The literal clauses are closed terms (`natLitToConstructor`, `strLitToConstructor`), fixed by every
operation (`*_natLit`, `*_strLit`).
-/

namespace Ix.CompileCert.Bridge

open Kernel (Denotes push)

universe u

section Env

variable {V : Type u}

/-- The environment a term sees before it is lifted by `n` at cutoff `c`. -/
def liftEnv (n c : Nat) (ρ : Nat → V) : Nat → V := fun i => if c ≤ i then ρ (i + n) else ρ i

/-- The environment a term sees with `x` at index `k` (before the substitution). -/
def instEnv (k : Nat) (x : V) (ρ : Nat → V) : Nat → V :=
  fun i => if i < k then ρ i else if i = k then x else ρ (i - 1)

/-- The environment below `k` binders. -/
def dropEnv (k : Nat) (ρ : Nat → V) : Nat → V := fun i => ρ (i + k)

theorem push_liftEnv (x : V) (n c : Nat) (ρ : Nat → V) :
    Kernel.push x (liftEnv n c ρ) = liftEnv n (c + 1) (Kernel.push x ρ) := by
  funext i
  cases i with
  | zero => simp [Kernel.push, liftEnv]
  | succ i =>
    by_cases h : c ≤ i
    · simp [Kernel.push, liftEnv, h, show c + 1 ≤ i + 1 by omega, show i + 1 + n = (i + n) + 1 by omega]
    · simp [Kernel.push, liftEnv, h, show ¬ c + 1 ≤ i + 1 by omega]

theorem push_instEnv (y x : V) (k : Nat) (ρ : Nat → V) :
    Kernel.push y (instEnv k x ρ) = instEnv (k + 1) x (Kernel.push y ρ) := by
  funext i
  cases i with
  | zero => simp [Kernel.push, instEnv]
  | succ i =>
    by_cases h1 : i < k
    · simp [Kernel.push, instEnv, h1, show i + 1 < k + 1 by omega]
    · by_cases h2 : i = k
      · subst h2; simp [Kernel.push, instEnv]
      · have h3 : i - 1 + 1 = i := by omega
        simp [Kernel.push, instEnv, h1, h2, show ¬ i + 1 < k + 1 by omega,
          show i + 1 - 1 = (i - 1) + 1 by omega]

theorem dropEnv_push (y : V) (k : Nat) (ρ : Nat → V) :
    dropEnv (k + 1) (Kernel.push y ρ) = dropEnv k ρ := by
  funext i; simp [dropEnv, Kernel.push]

theorem liftEnv_zero_cut (k : Nat) (ρ : Nat → V) : liftEnv k 0 ρ = dropEnv k ρ := by
  funext i; simp [liftEnv, dropEnv]

theorem liftEnv_one_push (x : V) (ρ : Nat → V) : liftEnv 1 0 (Kernel.push x ρ) = ρ := by
  funext i; simp [liftEnv, Kernel.push]

/-- The environment a term sees before it is lowered by `n` at cutoff `c` (the window
`[c, c + n)` unused). -/
def lowerEnv (n c : Nat) (ρ : Nat → V) : Nat → V :=
  fun i => if c + n ≤ i then ρ (i - n) else ρ i

theorem push_lowerEnv (x : V) (n c : Nat) (ρ : Nat → V) :
    Kernel.push x (lowerEnv n c ρ) = lowerEnv n (c + 1) (Kernel.push x ρ) := by
  funext i
  cases i with
  | zero => simp [Kernel.push, lowerEnv]
  | succ i =>
    by_cases h : c + n ≤ i
    · simp [Kernel.push, lowerEnv, h, show c + 1 + n ≤ i + 1 by omega,
        show i + 1 - n = (i - n) + 1 by omega]
    · simp [Kernel.push, lowerEnv, h, show ¬ c + 1 + n ≤ i + 1 by omega]

end Env

/-- Loose variables of a term stay out of the window `[c, c + n)`. -/
def NoVarIn (n : Nat) : Nat → Kernel.Expr → Prop
  | c, .bvar i => ¬ (c ≤ i ∧ i < c + n)
  | _, .fvar _ _ => True
  | _, .sort _ => True
  | _, .const _ _ => True
  | c, .app f a => NoVarIn n c f ∧ NoVarIn n c a
  | c, .lam t b _ => NoVarIn n c t ∧ NoVarIn n (c + 1) b
  | c, .forallE t b _ => NoVarIn n c t ∧ NoVarIn n (c + 1) b
  | c, .letE t v b => NoVarIn n c t ∧ NoVarIn n c v ∧ NoVarIn n (c + 1) b
  | _, .lit _ => True
  | c, .proj _ _ e => NoVarIn n c e

/-! ## The literal terms are closed and level-free -/

section Literals

open Kernel.Expr

theorem natLit_closed_lift (n c k : Nat) :
    liftLooseBVars n c (Kernel.natLitToConstructor k) = Kernel.natLitToConstructor k := by
  cases k <;> rfl

theorem natLit_closed_inst (v : Kernel.Expr) (d k : Nat) :
    (Kernel.natLitToConstructor k).instantiate1Lift v d = Kernel.natLitToConstructor k := by
  cases k <;> rfl

theorem natLit_closed_lower (n c k : Nat) :
    lowerBVars n c (Kernel.natLitToConstructor k) = Kernel.natLitToConstructor k := by
  cases k <;> rfl

theorem natLit_closed_levels (ks : List Kernel.Name) (us : List Kernel.Level) (k : Nat) :
    (Kernel.natLitToConstructor k).instantiateLevelParams ks us = Kernel.natLitToConstructor k := by
  cases k <;> rfl

/-- The character list of a string literal's constructor form. -/
private def charList (cs : List Char) : Kernel.Expr :=
  cs.foldr (init := .app (.const Kernel.listNilName [.zero]) (.const Kernel.charName []))
    fun c e =>
      .app (.app (.app (.const Kernel.listConsName [.zero]) (.const Kernel.charName []))
        (.app (.const Kernel.charOfNatName []) (.lit (.natVal c.toNat)))) e

private theorem strLit_eq (s : String) :
    Kernel.strLitToConstructor s = .app (.const Kernel.stringOfListName []) (charList s.toList) := rfl

private theorem charList_lift (n c : Nat) : ∀ cs, liftLooseBVars n c (charList cs) = charList cs
  | [] => rfl
  | ch :: cs => by
    show Kernel.Expr.app _ (liftLooseBVars n c (charList cs)) = _
    rw [charList_lift n c cs]; rfl

private theorem charList_inst (v : Kernel.Expr) (d : Nat) :
    ∀ cs, (charList cs).instantiate1Lift v d = charList cs
  | [] => rfl
  | ch :: cs => by
    show Kernel.Expr.app _ ((charList cs).instantiate1Lift v d) = _
    rw [charList_inst v d cs]; rfl

private theorem charList_lower (n c : Nat) : ∀ cs, lowerBVars n c (charList cs) = charList cs
  | [] => rfl
  | ch :: cs => by
    show Kernel.Expr.app _ (lowerBVars n c (charList cs)) = _
    rw [charList_lower n c cs]; rfl

private theorem charList_levels (ks : List Kernel.Name) (us : List Kernel.Level) :
    ∀ cs, (charList cs).instantiateLevelParams ks us = charList cs
  | [] => rfl
  | ch :: cs => by
    show Kernel.Expr.app _ ((charList cs).instantiateLevelParams ks us) = _
    rw [charList_levels ks us cs]; rfl

private theorem charList_noVarIn (n : Nat) : ∀ (c : Nat) (cs : List Char), NoVarIn n c (charList cs)
  | c, [] => by simp [charList, NoVarIn]
  | c, ch :: cs => by
    show NoVarIn n c (Kernel.Expr.app _ (charList cs))
    simp only [NoVarIn]; exact ⟨by simp, charList_noVarIn n c cs⟩

theorem strLit_noVarIn (n c : Nat) (s : String) : NoVarIn n c (Kernel.strLitToConstructor s) := by
  rw [strLit_eq]; exact ⟨trivial, charList_noVarIn n c s.toList⟩

theorem strLit_closed_lift (n c : Nat) (s : String) :
    liftLooseBVars n c (Kernel.strLitToConstructor s) = Kernel.strLitToConstructor s := by
  rw [strLit_eq]; simp only [liftLooseBVars, charList_lift]

theorem strLit_closed_inst (v : Kernel.Expr) (d : Nat) (s : String) :
    (Kernel.strLitToConstructor s).instantiate1Lift v d = Kernel.strLitToConstructor s := by
  rw [strLit_eq]; simp only [instantiate1Lift, charList_inst]

theorem strLit_closed_lower (n c : Nat) (s : String) :
    lowerBVars n c (Kernel.strLitToConstructor s) = Kernel.strLitToConstructor s := by
  rw [strLit_eq]; simp only [lowerBVars, charList_lower]

theorem strLit_closed_levels (ks : List Kernel.Name) (us : List Kernel.Level) (s : String) :
    (Kernel.strLitToConstructor s).instantiateLevelParams ks us = Kernel.strLitToConstructor s := by
  rw [strLit_eq]; simp only [instantiateLevelParams, charList_levels, List.map_nil]

end Literals

/-! ## The public reading under the operations -/

section Reading

variable {V : Type u} [Kernel.SetTheory V] {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat}

open Kernel.Expr

/-- **Lifting**: what a term denotes at `liftEnv n c ρ`, its lift denotes at `ρ`. -/
theorem denotes_lift (n : Nat) {ρ : Nat → V} {e : Kernel.Expr} {X : V}
    (h : Denotes cval env φ ρ e X) : ∀ (c : Nat) (ρ' : Nat → V), ρ = liftEnv n c ρ' →
      Denotes cval env φ ρ' (liftLooseBVars n c e) X := by
  induction h with
  | @bvar ρ i =>
    intro c ρ' hρ
    subst hρ
    by_cases hc : c ≤ i
    · have : liftEnv n c ρ' i = ρ' (i + n) := by simp [liftEnv, hc]
      rw [this]; simp only [liftLooseBVars, show i ≥ c from hc, ↓reduceIte]; exact .bvar
    · have : liftEnv n c ρ' i = ρ' i := by simp [liftEnv, hc]
      rw [this]; simp only [liftLooseBVars, show ¬ i ≥ c by omega, ↓reduceIte]; exact .bvar
  | sort => intro c ρ' _; exact .sort
  | const hf hlen => intro c ρ' _; exact .const hf hlen
  | app _ _ ihf iha => intro c ρ' hρ; exact .app (ihf c ρ' hρ) (iha c ρ' hρ)
  | lam _ _ hP ihA ihF =>
    intro c ρ' hρ
    refine .lam (ihA c ρ' hρ) (fun x hx => ihF x hx (c + 1) (Kernel.push x ρ') ?_) hP
    rw [hρ, push_liftEnv]
  | pi _ _ hP ihA ihB =>
    intro c ρ' hρ
    refine .pi (ihA c ρ' hρ) (fun x hx => ihB x hx (c + 1) (Kernel.push x ρ') ?_) hP
    rw [hρ, push_liftEnv]
  | proj_table ht _ ih => intro c ρ' hρ; exact .proj_table ht (ih c ρ' hρ)
  | proj_fst ht _ ih => intro c ρ' hρ; exact .proj_fst ht (ih c ρ' hρ)
  | proj_snd ht _ ih => intro c ρ' hρ; exact .proj_snd ht (ih c ρ' hρ)
  | @natLit _ k _ _ ih =>
    intro c ρ' hρ
    have := ih c ρ' hρ; rw [natLit_closed_lift] at this; exact .natLit this
  | @strLit _ s _ _ ih =>
    intro c ρ' hρ
    have := ih c ρ' hρ; rw [strLit_closed_lift] at this; exact .strLit this

/-- Lifting one binder up: a term read at `ρ` is read, lifted, under any further binder. -/
theorem denotes_lift_push {ρ : Nat → V} {e : Kernel.Expr} {X : V} (h : Denotes cval env φ ρ e X)
    (x : V) : Denotes cval env φ (Kernel.push x ρ) (liftLooseBVars 1 0 e) X :=
  denotes_lift 1 h 0 (Kernel.push x ρ) (liftEnv_one_push x ρ).symm

/-- **Substitution** (IxC's `instantiate1Lift`, X1's `Tm.inst`): a term read with `x` at index `k`
is read with `v` substituted, when `v` reads to `x` below the `k` crossed binders. -/
theorem denotes_inst {ρ : Nat → V} {e : Kernel.Expr} {X : V}
    (h : Denotes cval env φ ρ e X) : ∀ (k : Nat) (ρ' : Nat → V) (v : Kernel.Expr) (x : V),
      ρ = instEnv k x ρ' → Denotes cval env φ (dropEnv k ρ') v x →
      Denotes cval env φ ρ' (e.instantiate1Lift v k) X := by
  induction h with
  | @bvar ρ i =>
    intro k ρ' v x hρ hv
    subst hρ
    rcases Nat.lt_trichotomy i k with h1 | h1 | h1
    · have e1 : instEnv k x ρ' i = ρ' i := by simp [instEnv, h1]
      have e2 : (Kernel.Expr.bvar i).instantiate1Lift v k = .bvar i := by
        simp [instantiate1Lift, Nat.ne_of_lt h1, Nat.not_lt.mpr (Nat.le_of_lt h1)]
      rw [e1, e2]; exact .bvar
    · subst h1
      have e1 : instEnv i x ρ' i = x := by simp [instEnv]
      have e2 : (Kernel.Expr.bvar i).instantiate1Lift v i = liftLooseBVars i 0 v := by
        simp [instantiate1Lift]
      rw [e1, e2]; exact denotes_lift i hv 0 ρ' (liftEnv_zero_cut i ρ').symm
    · have e1 : instEnv k x ρ' i = ρ' (i - 1) := by
        simp [instEnv, Nat.not_lt.mpr (Nat.le_of_lt h1), Nat.ne_of_gt h1]
      have e2 : (Kernel.Expr.bvar i).instantiate1Lift v k = .bvar (i - 1) := by
        simp [instantiate1Lift, Nat.ne_of_gt h1, h1]
      rw [e1, e2]; exact .bvar
  | sort => intro _ _ _ _ _ _; exact .sort
  | const hf hlen => intro _ _ _ _ _ _; exact .const hf hlen
  | app _ _ ihf iha =>
    intro k ρ' v x hρ hv; exact .app (ihf k ρ' v x hρ hv) (iha k ρ' v x hρ hv)
  | lam _ _ hP ihA ihF =>
    intro k ρ' v x hρ hv
    refine .lam (ihA k ρ' v x hρ hv)
      (fun y hy => ihF y hy (k + 1) (Kernel.push y ρ') v x ?_ ?_) hP
    · rw [hρ, push_instEnv]
    · rw [dropEnv_push]; exact hv
  | pi _ _ hP ihA ihB =>
    intro k ρ' v x hρ hv
    refine .pi (ihA k ρ' v x hρ hv)
      (fun y hy => ihB y hy (k + 1) (Kernel.push y ρ') v x ?_ ?_) hP
    · rw [hρ, push_instEnv]
    · rw [dropEnv_push]; exact hv
  | proj_table ht _ ih => intro k ρ' v x hρ hv; exact .proj_table ht (ih k ρ' v x hρ hv)
  | proj_fst ht _ ih => intro k ρ' v x hρ hv; exact .proj_fst ht (ih k ρ' v x hρ hv)
  | proj_snd ht _ ih => intro k ρ' v x hρ hv; exact .proj_snd ht (ih k ρ' v x hρ hv)
  | @natLit _ n _ _ ih =>
    intro k ρ' v x hρ hv
    have := ih k ρ' v x hρ hv; rw [natLit_closed_inst] at this; exact .natLit this
  | @strLit _ s _ _ ih =>
    intro k ρ' v x hρ hv
    have := ih k ρ' v x hρ hv; rw [strLit_closed_inst] at this; exact .strLit this

/-- β's substitution at the outermost binder: the body read at `push x ρ` is read at `ρ` with the
argument substituted, when the argument reads to `x`. -/
theorem denotes_inst0 {ρ : Nat → V} {b a : Kernel.Expr} {x X : V}
    (hb : Denotes cval env φ (Kernel.push x ρ) b X) (ha : Denotes cval env φ ρ a x) :
    Denotes cval env φ ρ (b.instantiate1Lift a 0) X := by
  refine denotes_inst hb 0 ρ a x ?_ ?_
  · funext i; cases i <;> simp [instEnv, Kernel.push]
  · have : dropEnv 0 ρ = ρ := by funext i; simp [dropEnv]
    rw [this]; exact ha

/-- **Lowering** over an unused window. -/
theorem denotes_lower (n : Nat) {ρ : Nat → V} {e : Kernel.Expr} {X : V}
    (h : Denotes cval env φ ρ e X) : ∀ (c : Nat) (ρ' : Nat → V), NoVarIn n c e →
      ρ = lowerEnv n c ρ' → Denotes cval env φ ρ' (lowerBVars n c e) X := by
  induction h with
  | @bvar ρ i =>
    intro c ρ' hw hρ
    subst hρ
    simp only [NoVarIn] at hw
    by_cases hc : c + n ≤ i
    · have : lowerEnv n c ρ' i = ρ' (i - n) := by simp [lowerEnv, hc]
      rw [this]; simp only [lowerBVars, show i ≥ c + n from hc, ↓reduceIte]; exact .bvar
    · have : lowerEnv n c ρ' i = ρ' i := by simp [lowerEnv, hc]
      rw [this]; simp only [lowerBVars, show ¬ i ≥ c + n by omega, ↓reduceIte]; exact .bvar
  | sort => intro _ _ _ _; exact .sort
  | const hf hlen => intro _ _ _ _; exact .const hf hlen
  | app _ _ ihf iha =>
    intro c ρ' hw hρ; simp only [NoVarIn] at hw
    exact .app (ihf c ρ' hw.1 hρ) (iha c ρ' hw.2 hρ)
  | lam _ _ hP ihA ihF =>
    intro c ρ' hw hρ; simp only [NoVarIn] at hw
    refine .lam (ihA c ρ' hw.1 hρ)
      (fun x hx => ihF x hx (c + 1) (Kernel.push x ρ') hw.2 ?_) hP
    rw [hρ, push_lowerEnv]
  | pi _ _ hP ihA ihB =>
    intro c ρ' hw hρ; simp only [NoVarIn] at hw
    refine .pi (ihA c ρ' hw.1 hρ)
      (fun x hx => ihB x hx (c + 1) (Kernel.push x ρ') hw.2 ?_) hP
    rw [hρ, push_lowerEnv]
  | proj_table ht _ ih => intro c ρ' hw hρ; exact .proj_table ht (ih c ρ' hw hρ)
  | proj_fst ht _ ih => intro c ρ' hw hρ; exact .proj_fst ht (ih c ρ' hw hρ)
  | proj_snd ht _ ih => intro c ρ' hw hρ; exact .proj_snd ht (ih c ρ' hw hρ)
  | @natLit _ k _ _ ih =>
    intro c ρ' _ hρ
    have := ih c ρ' (by cases k <;> simp [Kernel.natLitToConstructor, NoVarIn]) hρ
    rw [natLit_closed_lower] at this; exact .natLit this
  | @strLit _ s _ _ ih =>
    intro c ρ' _ hρ
    have := ih c ρ' (strLit_noVarIn n c s) hρ; rw [strLit_closed_lower] at this; exact .strLit this


/-! ## Universe instantiation -/

/-- A level-local interpretation: a constant's value at an assignment depends only on the
assignment of its own universe parameters. Every strong model has it
(`StrongInstalledModel.value_params`, from IxC's `acval_params`). -/
def CvalLocal (cval : Kernel.Name → (Kernel.Name → Nat) → V) (env : Kernel.Env) : Prop :=
  ∀ name info, env.find? name = some info → ∀ first second : Kernel.Name → Nat,
    (∀ p ∈ info.toConstantVal.levelParams, first p = second p) → cval name first = cval name second

theorem cvalLocal_of_strong (strong : StrongInstalledModel V env) :
    CvalLocal strong.public.cval env :=
  fun _ _ lookup first second agree => strong.value_params lookup first second agree

/-- The composed assignment of an instantiated constant occurrence. -/
theorem substFn_map_subst (ks : List Kernel.Name) (us : List Kernel.Level) :
    ∀ (ps : List Kernel.Name) (vs : List Kernel.Level) (p : Kernel.Name), p ∈ ps →
      vs.length = ps.length →
      Kernel.Level.substFn φ ps (vs.map (Kernel.Level.subst ks us)) p =
        Kernel.Level.substFn (Kernel.Level.substFn φ ks us) ps vs p
  | [], _, _, hp, _ => by simp at hp
  | _ :: _, [], _, _, hl => by simp at hl
  | k :: ps, v :: vs, p, hp, hl => by
    simp only [List.map_cons, Kernel.Level.substFn]
    by_cases hk : k = p
    · simp [hk, Kernel.Level.eval_subst]
    · simp only [hk, ↓reduceIte]
      have hp' : p ∈ ps := by
        rcases List.mem_cons.mp hp with h | h
        · exact absurd h.symm hk
        · exact h
      exact substFn_map_subst ks us ps vs p hp' (by simpa using hl)

theorem regime_substPW (ks : List Kernel.Name) (us : List Kernel.Level) (pw : Kernel.PropWhen) :
    Kernel.regime φ (Kernel.Level.substPW ks us pw) =
      Kernel.regime (Kernel.Level.substFn φ ks us) pw := by
  simp only [Kernel.regime, Kernel.Level.holds_substPW]

/-- **Universe instantiation**: a term read at the composed assignment `substFn φ ks us` is read
at `φ` once its universes are instantiated (sorts, constant levels, binder data). -/
theorem denotes_levels (hloc : CvalLocal cval env) (ks : List Kernel.Name) (us : List Kernel.Level)
    {ρ : Nat → V} {e : Kernel.Expr} {X : V}
    (h : Denotes cval env (Kernel.Level.substFn φ ks us) ρ e X) :
    Denotes cval env φ ρ (e.instantiateLevelParams ks us) X := by
  induction h with
  | bvar => exact .bvar
  | @sort ρ u =>
    have h := Denotes.sort (cval := cval) (env := env) (φ := φ) (ρ := ρ)
      (u := Kernel.Level.subst ks us u)
    rw [Kernel.Level.eval_subst] at h
    exact h
  | @const ρ n vs ci hf hlen =>
    have h := Denotes.const (cval := cval) (φ := φ) (ρ := ρ) (us := vs.map (Kernel.Level.subst ks us))
      hf (by simp [hlen])
    rw [hloc n ci hf _ _ (fun p hp => substFn_map_subst ks us _ vs p hp hlen)] at h
    exact h
  | app _ _ ihf iha => exact .app ihf iha
  | @lam ρ ty body m A F _ _ hP ihA ihF =>
    have h := Denotes.lam (cval := cval) (φ := φ) (m := ⟨Kernel.Level.substPW ks us m.pw⟩) ihA
      (fun x hx => ihF x hx) (by rw [regime_substPW]; exact hP)
    rw [regime_substPW] at h
    exact h
  | @pi ρ ty body m A B _ _ hP ihA ihB =>
    have h := Denotes.pi (cval := cval) (φ := φ) (m := ⟨Kernel.Level.substPW ks us m.pw⟩) ihA
      (fun x hx => ihB x hx) (by rw [regime_substPW]; exact hP)
    rw [regime_substPW] at h
    exact h
  | proj_table ht _ ih => exact .proj_table ht ih
  | proj_fst ht _ ih => exact .proj_fst ht ih
  | proj_snd ht _ ih => exact .proj_snd ht ih
  | natLit _ ih => rw [natLit_closed_levels] at ih; exact .natLit ih
  | strLit _ ih => rw [strLit_closed_levels] at ih; exact .strLit ih

end Reading

end Ix.CompileCert.Bridge
