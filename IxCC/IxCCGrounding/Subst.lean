import IxCCGrounding.Eqn

/-!
# Substitution lemmas for `Denotes` (`IxCCGrounding.Subst`)

What the generic `case` lemma needs of the kernel's model beyond its rules, all proved from
`Denotes`'s rules (and, for level instantiation, `cval_params`):

* **Environment agreement** (`den_agree`): a term denotes the same set in two variable
  environments that agree on its loose variables (`looseIn`); a closed term denotes the same set
  in every environment.
* **Lifting** (`den_lift`): a term lifted by `k` above `c` denotes in `ρ` what the term denotes in
  `skipEnv ρ k c`, the environment that skips the `k` inserted indices; with `pushAll`, skipping a
  block of bound sets (`skipEnv_pushAll`).
* **Level instantiation**: the zero-ness datum under a substitution (`holds_substPW`);
  instantiating a term at its own level parameters is the identity (`inst_self`); and a term
  whose level parameters are among `ks` denotes at `ψ` what its instantiation by `us` denotes at
  `φ`, when `ψ` agrees on `ks` with the assignment the instantiation induces (`den_inst`,
  `fits_inst`).
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel

universe w

/-! ## Syntax: loose variables, literal forms, environments -/

theorem looseIn_natLit (i n : Nat) : looseIn i (natLitToConstructor (md := .anon) n) = false := by
  cases n <;> simp [natLitToConstructor, looseIn]

theorem looseIn_strLit (i : Nat) (s : String) :
    looseIn i (strLitToConstructor (md := .anon) s) = false := by
  unfold strLitToConstructor
  generalize s.toList = l
  induction l with
  | nil => simp [looseIn]
  | cons c cs ih => simp only [List.foldr_cons, looseIn, Bool.false_or] at ih ⊢; exact ih

/-- A variable loose in a term all of whose variables are below `n` is below `n`. -/
theorem lt_of_bvarsLt : ∀ {n i : Nat} {e : KExpr}, bvarsLt n e = true → looseIn i e = true → i < n
  | n, i, .bvar k, h, hi => by
    simp only [bvarsLt, decide_eq_true_eq] at h; simp only [looseIn, beq_iff_eq] at hi; omega
  | _, _, .app f a, h, hi => by
    simp only [bvarsLt, Bool.and_eq_true] at h; simp only [looseIn, Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · exact lt_of_bvarsLt h.1 hi
    · exact lt_of_bvarsLt h.2 hi
  | _, _, .lam d b _, h, hi => by
    simp only [bvarsLt, Bool.and_eq_true] at h; simp only [looseIn, Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · exact lt_of_bvarsLt h.1 hi
    · have := lt_of_bvarsLt h.2 hi; omega
  | _, _, .forallE d b _, h, hi => by
    simp only [bvarsLt, Bool.and_eq_true] at h; simp only [looseIn, Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · exact lt_of_bvarsLt h.1 hi
    · have := lt_of_bvarsLt h.2 hi; omega
  | _, _, .letE t v b _, h, hi => by
    simp only [bvarsLt, Bool.and_eq_true] at h; simp only [looseIn, Bool.or_eq_true] at hi
    rcases hi with (hi | hi) | hi
    · exact lt_of_bvarsLt h.1.1 hi
    · exact lt_of_bvarsLt h.1.2 hi
    · have := lt_of_bvarsLt h.2 hi; omega
  | _, _, .proj _ _ e, h, hi => by
    simp only [bvarsLt] at h; simp only [looseIn] at hi; exact lt_of_bvarsLt h hi
  | _, _, .fvar _ _, _, hi | _, _, .sort _, _, hi | _, _, .const _ _, _, hi
  | _, _, .lit _, _, hi => by simp [looseIn] at hi

/-- A lifted term has no loose variable among the inserted indices. -/
theorem looseIn_lift (k : Nat) : ∀ (e : KExpr) (c i : Nat), c ≤ i → i < c + k →
    looseIn i (e.liftLooseBVars k c) = false
  | .bvar j, c, i, h1, h2 => by
    simp only [Expr.liftLooseBVars]
    split <;> simp [looseIn] <;> omega
  | .app f a, c, i, h1, h2 => by
    simp [Expr.liftLooseBVars, looseIn, looseIn_lift k f c i h1 h2, looseIn_lift k a c i h1 h2]
  | .lam d b _, c, i, h1, h2 => by
    simp [Expr.liftLooseBVars, looseIn, looseIn_lift k d c i h1 h2,
      looseIn_lift k b (c + 1) (i + 1) (by omega) (by omega)]
  | .forallE d b _, c, i, h1, h2 => by
    simp [Expr.liftLooseBVars, looseIn, looseIn_lift k d c i h1 h2,
      looseIn_lift k b (c + 1) (i + 1) (by omega) (by omega)]
  | .letE t v b _, c, i, h1, h2 => by
    simp [Expr.liftLooseBVars, looseIn, looseIn_lift k t c i h1 h2, looseIn_lift k v c i h1 h2,
      looseIn_lift k b (c + 1) (i + 1) (by omega) (by omega)]
  | .proj _ _ e, c, i, h1, h2 => by
    simp [Expr.liftLooseBVars, looseIn, looseIn_lift k e c i h1 h2]
  | .fvar _ _, _, _, _, _ | .sort _, _, _, _, _ | .const _ _, _, _, _, _ | .lit _, _, _, _, _ => by
    simp [Expr.liftLooseBVars, looseIn]

theorem not_looseIn_of_avoids {c j : Nat} {e : KExpr} (h : avoids c j e = true) {i : Nat}
    (h1 : c ≤ i) (h2 : i < c + j) : looseIn i e = false := by
  simp only [avoids, List.all_eq_true, List.mem_range, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  have := h (i - c) (by omega)
  rwa [Nat.add_sub_cancel' h1] at this

section Envs

variable {V : Type w}

/-- The environment that skips the `k` indices inserted at `c`. -/
def skipEnv (ρ : BVarIdx → V) (k c : Nat) : BVarIdx → V := fun i =>
  if i < c then ρ i else ρ (i + k)

theorem skipEnv_push (x : V) (ρ : BVarIdx → V) (k c : Nat) :
    skipEnv (push x ρ) k (c + 1) = push x (skipEnv ρ k c) := by
  funext i
  cases i with
  | zero => simp [skipEnv, push]
  | succ i =>
    show (if i + 1 < c + 1 then push x ρ (i + 1) else push x ρ (i + 1 + k)) = skipEnv ρ k c i
    simp only [skipEnv]
    by_cases h : i < c
    · have h' : i + 1 < c + 1 := by omega
      simp only [h, h', ↓reduceIte]; rfl
    · have h' : ¬ i + 1 < c + 1 := by omega
      simp only [h, h', ↓reduceIte]
      rw [show i + 1 + k = (i + k) + 1 by omega]; rfl

theorem pushAll_cons (x : V) (xs : List V) (ρ : BVarIdx → V) :
    pushAll (x :: xs) ρ = pushAll xs (push x ρ) := by
  refine funext fun (i : Nat) => ?_
  simp only [pushAll, List.reverse_cons, List.length_cons, List.getD_eq_getElem?_getD]
  by_cases h : i < xs.length
  · have h1 : i < xs.reverse.length := by simpa using h
    rw [List.getElem?_append_left h1, List.getElem?_eq_getElem h1]
    rfl
  · have h1 : xs.reverse.length ≤ i := by simp; omega
    rw [List.getElem?_append_right h1, List.getElem?_eq_none h1]
    simp only [List.length_reverse, Option.getD_none]
    by_cases h' : i = xs.length
    · subst h'; simp [push]
    · have h2 : [x].length ≤ i - xs.length := by simp; omega
      rw [List.getElem?_eq_none h2]
      simp only [Option.getD_none]
      rw [show i - xs.length = (i - (xs.length + 1)) + 1 by omega]; rfl

theorem pushAll_append (xs ys : List V) (ρ : BVarIdx → V) :
    pushAll (xs ++ ys) ρ = pushAll ys (pushAll xs ρ) := by
  induction xs generalizing ρ with
  | nil => rw [List.nil_append, pushAll_nil]
  | cons x xs ih => rw [List.cons_append, pushAll_cons, pushAll_cons, ih]

theorem pushAll_offset : ∀ (xs : List V) (ρ : BVarIdx → V) (i : Nat),
    pushAll xs ρ (i + xs.length) = ρ i
  | [], ρ, i => by rw [pushAll_nil]; rfl
  | x :: xs, ρ, i => by
    rw [pushAll_cons, List.length_cons, show i + (xs.length + 1) = (i + 1) + xs.length by omega,
      pushAll_offset xs]
    rfl

/-- The bound set `y`, read from under the sets `c`. -/
theorem pushAll_at (a : List V) (y : V) (c : List V) (ρ : BVarIdx → V) :
    pushAll (a ++ y :: c) ρ c.length = y := by
  rw [pushAll_append, pushAll_cons, show c.length = 0 + c.length by omega, pushAll_offset]; rfl

theorem skipEnv_zero (ρ : BVarIdx → V) (k : Nat) : skipEnv ρ k 0 = fun i => ρ (i + k) := by
  funext i; simp [skipEnv]

theorem skipEnv_pushAll_gen (k : Nat) : ∀ (c : List V) (E : BVarIdx → V) (d : Nat),
    skipEnv (pushAll c E) k (c.length + d) = pushAll c (skipEnv E k d)
  | [], E, d => by simp [pushAll_nil]
  | z :: c, E, d => by
    rw [pushAll_cons, pushAll_cons, List.length_cons, show c.length + 1 + d = c.length + (d + 1) by
      omega, skipEnv_pushAll_gen k c, skipEnv_push]

/-- **Skipping a block of bound sets**: the environment `a, b, c` read with the `b.length`
indices above the innermost `c.length` skipped is the environment `a, c`. -/
theorem skipEnv_pushAll (a b c : List V) (ρ : BVarIdx → V) :
    skipEnv (pushAll (a ++ b ++ c) ρ) b.length c.length = pushAll (a ++ c) ρ := by
  have h1 : pushAll (a ++ b ++ c) ρ = pushAll c (pushAll (a ++ b) ρ) := pushAll_append (a ++ b) c ρ
  have h2 : pushAll (a ++ c) ρ = pushAll c (pushAll a ρ) := pushAll_append a c ρ
  have h3 : skipEnv (pushAll (a ++ b) ρ) b.length 0 = pushAll a ρ := by
    rw [skipEnv_zero]; funext i; rw [pushAll_append, pushAll_offset]
  rw [h1, h2, ← h3, ← skipEnv_pushAll_gen]
  rfl

theorem skipEnv_skipEnv (E : BVarIdx → V) {a b c c' : Nat} (h1 : c ≤ c') (h2 : c' ≤ c + a) :
    skipEnv (skipEnv E b c') a c = skipEnv E (a + b) c := by
  refine funext fun (i : Nat) => ?_
  simp only [skipEnv]
  by_cases hi : i < c
  · have h3 : i < c' := by omega
    simp only [hi, h3, ↓reduceIte]
  · have h3 : ¬ i + a < c' := by omega
    simp only [hi, h3, ↓reduceIte, Nat.add_assoc]

end Envs

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

section Den

variable {cval : KKey → (LevelParam → Nat) → V} {φ : LevelParam → Nat}

/-! ## Environment agreement -/

/-- **A term denotes the same set in two environments that agree on its loose variables.** -/
theorem den_agree {ρ : BVarIdx → V} {e : KExpr} {X : V} (h : Denotes cval env φ ρ e X) :
    ∀ {ρ' : BVarIdx → V}, (∀ i, looseIn i e = true → ρ i = ρ' i) → Denotes cval env φ ρ' e X := by
  induction h with
  | @bvar ρ i =>
    intro ρ' hag
    rw [hag i (by simp [looseIn])]
    exact .bvar
  | sort => intro _ _; exact .sort
  | const hf hl => intro _ _; exact .const hf hl
  | app _ _ ihf iha =>
    intro ρ' hag
    exact .app (ihf fun i hi => hag i (by simp [looseIn, hi]))
      (iha fun i hi => hag i (by simp [looseIn, hi]))
  | lam _ _ hP ihA ihF =>
    intro ρ' hag
    refine .lam (ihA fun i hi => hag i (by simp [looseIn, hi])) (fun x hx => ihF x hx ?_) hP
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact hag i (by simp [looseIn, hi])
  | pi _ _ hP ihA ihB =>
    intro ρ' hag
    refine .pi (ihA fun i hi => hag i (by simp [looseIn, hi])) (fun x hx => ihB x hx ?_) hP
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact hag i (by simp [looseIn, hi])
  | proj_table ht _ ih => intro ρ' hag; exact .proj_table ht (ih fun i hi => hag i (by simpa [looseIn] using hi))
  | proj_fst ht _ ih => intro ρ' hag; exact .proj_fst ht (ih fun i hi => hag i (by simpa [looseIn] using hi))
  | proj_snd ht _ ih => intro ρ' hag; exact .proj_snd ht (ih fun i hi => hag i (by simpa [looseIn] using hi))
  | natLit _ ih =>
    intro ρ' _
    exact .natLit (ih fun i hi => by rw [looseIn_natLit] at hi; cases hi)
  | strLit _ ih =>
    intro ρ' _
    exact .strLit (ih fun i hi => by rw [looseIn_strLit] at hi; cases hi)

/-- A closed term denotes the same set in every environment. -/
theorem den_closed {ρ ρ' : BVarIdx → V} {e : KExpr} {X : V} (hc : bvarsLt 0 e = true)
    (h : Denotes cval env φ ρ e X) : Denotes cval env φ ρ' e X :=
  den_agree h fun i hi => absurd (lt_of_bvarsLt hc hi) (Nat.not_lt_zero i)

/-- `Fits` at an environment that agrees on the telescope's loose variables. -/
theorem fits_agree {ρ σ : BVarIdx → V} {T R : KExpr} {xs : List V}
    (h : Fits cval env φ ρ T xs σ R) :
    ∀ {ρ' : BVarIdx → V}, (∀ i, looseIn i T = true → ρ i = ρ' i) →
      ∃ σ', Fits cval env φ ρ' T xs σ' R := by
  induction h with
  | nil => intro ρ' _; exact ⟨ρ', .nil⟩
  | cons hA hx _ ih =>
    intro ρ' hag
    obtain ⟨σ', hf⟩ := ih (ρ' := push _ ρ') fun i hi => by
      cases i with
      | zero => rfl
      | succ i => exact hag i (by simp [looseIn, hi])
    exact ⟨σ', .cons (den_agree hA fun i hi => hag i (by simp [looseIn, hi])) hx hf⟩

/-! ## Lifting -/

theorem den_const_env {ρ ρ' : BVarIdx → V} {n : KKey} {us : List Level} {X : V}
    (h : Denotes cval env φ ρ (.const n us) X) : Denotes cval env φ ρ' (.const n us) X := by
  cases h with
  | const hf hl => exact .const hf hl

/-- **A lifted term denotes in `ρ` what the term denotes with the inserted indices skipped.** -/
theorem den_lift (k : Nat) (e : KExpr) : ∀ (c : Nat) (ρ : BVarIdx → V) (X : V),
    Denotes cval env φ ρ (e.liftLooseBVars k c) X ↔ Denotes cval env φ (skipEnv ρ k c) e X := by
  induction e with
  | bvar i =>
    intro c ρ X
    simp only [Expr.liftLooseBVars]
    by_cases h : i ≥ c
    · have h' : ¬ i < c := by omega
      simp only [h, h', ↓reduceIte, den_bvar, skipEnv]
    · have h' : i < c := by omega
      simp only [h, h', ↓reduceIte, den_bvar, skipEnv]
  | fvar _ _ _ =>
    intro c ρ X
    simp only [Expr.liftLooseBVars]
    constructor <;> intro h <;> cases h
  | sort u =>
    intro c ρ X
    simp only [Expr.liftLooseBVars, den_sort]
  | const n us =>
    intro c ρ X
    simp only [Expr.liftLooseBVars]
    exact ⟨den_const_env, den_const_env⟩
  | app f a ihf iha =>
    intro c ρ X
    simp only [Expr.liftLooseBVars, den_app, ihf, iha]
  | lam ty body m iht ihb =>
    intro c ρ X
    simp only [Expr.liftLooseBVars, den_lam, iht, ihb, skipEnv_push]
  | forallE ty body m iht ihb =>
    intro c ρ X
    simp only [Expr.liftLooseBVars, den_pi, iht, ihb, skipEnv_push]
  | letE _ _ _ _ _ _ _ =>
    intro c ρ X
    simp only [Expr.liftLooseBVars]
    constructor <;> intro h <;> cases h
  | lit l =>
    intro c ρ X
    simp only [Expr.liftLooseBVars]
    exact ⟨fun h => den_agree h fun i hi => by simp [looseIn] at hi,
      fun h => den_agree h fun i hi => by simp [looseIn] at hi⟩
  | proj s i e ih =>
    intro c ρ X
    simp only [Expr.liftLooseBVars]
    constructor
    · intro h
      cases h with
      | proj_table ht he => exact .proj_table ht ((ih c ρ _).mp he)
      | proj_fst ht he => exact .proj_fst ht ((ih c ρ _).mp he)
      | proj_snd ht he => exact .proj_snd ht ((ih c ρ _).mp he)
    · intro h
      cases h with
      | proj_table ht he => exact .proj_table ht ((ih c ρ _).mpr he)
      | proj_fst ht he => exact .proj_fst ht ((ih c ρ _).mpr he)
      | proj_snd ht he => exact .proj_snd ht ((ih c ρ _).mpr he)

/-- A lifted term, read in an environment holding a block `b` of as many sets as the lift
inserts, denotes what the term denotes without the block. -/
theorem den_lift_block {a b c : List V} {ρ : BVarIdx → V} {e : KExpr} {X : V} :
    Denotes cval env φ (pushAll (a ++ b ++ c) ρ) (e.liftLooseBVars b.length c.length) X ↔
      Denotes cval env φ (pushAll (a ++ c) ρ) e X := by
  rw [den_lift, skipEnv_pushAll]

end Den

/-! ## Level instantiation -/

/-- **The zero-ness datum under a level substitution** reads the induced assignment. -/
theorem holds_substPW (φ : LevelParam → Nat) (ks : List LevelParam) (vs : List Level)
    (pw : PropWhen) : (Level.substPW ks vs pw).holds φ = pw.holds (Level.substFn φ ks vs) := by
  unfold Level.substPW
  cases pw with
  | never => simp
  | ifAllZero ps =>
    rw [PropWhen.bindZ_ifAllZero, PropWhen.holds_bindZ_go, PropWhen.holds_ifAllZero]
    congr 1
    funext n
    rw [holds_zeronessOf, Level.eval_subst_go]

theorem subst_go_self : ∀ (ks : List LevelParam) (n : LevelParam),
    Level.subst.go ks (ks.map .param) n = .param n
  | [], _ => rfl
  | k :: ks, n => by
    simp only [List.map_cons, Level.subst.go]
    split
    · next h => rw [h]
    · exact subst_go_self ks n

theorem subst_self (ks : List LevelParam) : ∀ l : Level, Level.subst ks (ks.map .param) l = l
  | .zero => rfl
  | .succ l => by simp [Level.subst, subst_self ks l]
  | .max a b => by simp [Level.subst, subst_self ks a, subst_self ks b]
  | .imax a b => by simp [Level.subst, subst_self ks a, subst_self ks b]
  | .param n => subst_go_self ks n

theorem substPW_self (ks : List LevelParam) (pw : PropWhen) :
    Level.substPW ks (ks.map .param) pw = pw :=
  PropWhen.eq_of_holds fun φ => by rw [holds_substPW, Level.substFn_param_self]

/-- **Instantiating a term at its own level parameters is the identity.** -/
theorem inst_self (ks : List LevelParam) (e : KExpr) :
    e.instantiateLevelParams ks (ks.map .param) = e := by
  have hmap : ∀ vs : List Level, vs.map (Level.subst ks (ks.map .param)) = vs := fun vs => by
    induction vs with
    | nil => rfl
    | cons v vs ih => simp [subst_self ks v, ih]
  induction e with
  | bvar => rfl
  | fvar _ _ ih => simp [Expr.instantiateLevelParams, ih]
  | sort u => simp [Expr.instantiateLevelParams, subst_self ks u]
  | const n vs => simp [Expr.instantiateLevelParams, hmap]
  | app f a ihf iha => simp [Expr.instantiateLevelParams, ihf, iha]
  | lam t b m iht ihb => simp [Expr.instantiateLevelParams, iht, ihb, substPW_self]
  | forallE t b m iht ihb => simp [Expr.instantiateLevelParams, iht, ihb, substPW_self]
  | letE t v b _ iht ihv ihb => simp [Expr.instantiateLevelParams, iht, ihv, ihb]
  | lit => rfl
  | proj s i e ih => simp [Expr.instantiateLevelParams, ih]

theorem inst_natLit (ks : List LevelParam) (us : List Level) (n : Nat) :
    (natLitToConstructor (md := .anon) n).instantiateLevelParams ks us = natLitToConstructor n := by
  cases n <;> simp [natLitToConstructor, Expr.instantiateLevelParams]

theorem inst_strLit (ks : List LevelParam) (us : List Level) (s : String) :
    (strLitToConstructor (md := .anon) s).instantiateLevelParams ks us = strLitToConstructor s := by
  unfold strLitToConstructor
  simp only [Expr.instantiateLevelParams, List.map_nil]
  congr 1
  generalize s.toList = l
  induction l with
  | nil => simp [Expr.instantiateLevelParams, Level.subst]
  | cons c cs ih => simp [Expr.instantiateLevelParams, Level.subst, ih]

theorem defined_natLit (ks : List LevelParam) (n : Nat) :
    (natLitToConstructor (md := .anon) n).allLevelParamsDefined ks = true := by
  cases n <;> simp [natLitToConstructor, Expr.allLevelParamsDefined]

theorem defined_strLit (ks : List LevelParam) (s : String) :
    (strLitToConstructor (md := .anon) s).allLevelParamsDefined ks = true := by
  unfold strLitToConstructor
  simp only [Expr.allLevelParamsDefined, List.all_nil, Bool.true_and]
  generalize s.toList = l
  induction l with
  | nil => simp [Expr.allLevelParamsDefined, Level.allParamsDefined]
  | cons c cs ih => simp [Expr.allLevelParamsDefined, Level.allParamsDefined, ih]

theorem regime_congr {φ ψ : LevelParam → Nat} {pw pw' : PropWhen} (h : pw.holds φ = pw'.holds ψ) :
    regime φ pw = regime ψ pw' := by
  simp [regime, h]

/-- **Level instantiation**: a term whose level parameters are among `ks`, denoting `X` at `ψ`,
denotes `X` at `φ` once instantiated by `us`, when `ψ` agrees on `ks` with the assignment the
instantiation induces. The constants inside are read at assignments that agree on their own
parameters (`cval_params`). -/
theorem den_inst (M : Model V env) (hL : Laws M) {ks : List LevelParam} {us : List Level}
    {φ ψ : LevelParam → Nat} (hψ : ∀ p ∈ ks, Level.substFn φ ks us p = ψ p)
    {ρ : BVarIdx → V} {e : KExpr} {X : V} (h : Denotes M.cval env ψ ρ e X) :
    e.allLevelParamsDefined ks = true →
      Denotes M.cval env φ ρ (e.instantiateLevelParams ks us) X := by
  induction h with
  | bvar => intro _; exact .bvar
  | @sort ρ u =>
    intro hd
    simp only [Expr.allLevelParamsDefined] at hd
    have h1 := Denotes.sort (cval := M.cval) (env := env) (φ := φ) (ρ := ρ) (u := Level.subst ks us u)
    rwa [Level.eval_subst, Level.eval_ext hd hψ] at h1
  | @const ρ n vs ci hf hlen =>
    intro hd
    simp only [Expr.allLevelParamsDefined, List.all_eq_true] at hd
    simp only [Expr.instantiateLevelParams]
    have h1 := Denotes.const (cval := M.cval) (φ := φ) (ρ := ρ) (us := vs.map (Level.subst ks us)) hf
      (by rw [List.length_map, hlen])
    have heq : M.cval n (Level.substFn φ ci.toConstantVal.levelParams (vs.map (Level.subst ks us))) =
        M.cval n (Level.substFn ψ ci.toConstantVal.levelParams vs) :=
      hL.cval_params n ci hf _ _ fun p hp => by
        rw [Level.substFn_map_subst hlen hp]
        exact Level.substFn_ext hψ (fun u hu => hd u hu) hlen p hp
    rwa [heq] at h1
  | app _ _ ihf iha =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    exact .app (ihf hd.1) (iha hd.2)
  | @lam ρ ty body m A F _ _ hP ihA ihF =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    have hr : regime φ (Level.substPW ks us m.pw) = regime ψ m.pw :=
      regime_congr (by rw [holds_substPW]; exact PropWhen.holds_ext hd.2 hψ)
    have h1 := Denotes.lam (cval := M.cval) (env := env) (φ := φ) (ρ := ρ)
      (m := { m with pw := Level.substPW ks us m.pw }) (ihA hd.1.1) (fun x hx => ihF x hx hd.1.2)
      (fun h0 => hP (by rw [← hr]; exact h0))
    rw [show regime ψ m.pw = regime φ ({ m with pw := Level.substPW ks us m.pw } : BinderMeta).pw
      from hr.symm]
    exact h1
  | @pi ρ ty body m A B _ _ hP ihA ihB =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    have hr : regime φ (Level.substPW ks us m.pw) = regime ψ m.pw :=
      regime_congr (by rw [holds_substPW]; exact PropWhen.holds_ext hd.2 hψ)
    have h1 := Denotes.pi (cval := M.cval) (env := env) (φ := φ) (ρ := ρ)
      (m := { m with pw := Level.substPW ks us m.pw }) (ihA hd.1.1) (fun x hx => ihB x hx hd.1.2)
      (fun h0 => hP (by rw [← hr]; exact h0))
    rw [show regime ψ m.pw = regime φ ({ m with pw := Level.substPW ks us m.pw } : BinderMeta).pw
      from hr.symm]
    exact h1
  | proj_table ht _ ih =>
    intro hd; simp only [Expr.allLevelParamsDefined] at hd; exact .proj_table ht (ih hd)
  | proj_fst ht _ ih =>
    intro hd; simp only [Expr.allLevelParamsDefined] at hd; exact .proj_fst ht (ih hd)
  | proj_snd ht _ ih =>
    intro hd; simp only [Expr.allLevelParamsDefined] at hd; exact .proj_snd ht (ih hd)
  | @natLit ρ n X _ ih =>
    intro _
    have h1 := ih (defined_natLit ks n)
    rw [inst_natLit] at h1
    exact .natLit h1
  | @strLit ρ s X _ ih =>
    intro _
    have h1 := ih (defined_strLit ks s)
    rw [inst_strLit] at h1
    exact .strLit h1

/-- `Fits` under level instantiation (`den_inst` at each domain). -/
theorem fits_inst (M : Model V env) (hL : Laws M) {ks : List LevelParam} {us : List Level}
    {φ ψ : LevelParam → Nat} (hψ : ∀ p ∈ ks, Level.substFn φ ks us p = ψ p)
    {ρ σ : BVarIdx → V} {T R : KExpr} {xs : List V} (h : Fits M.cval env ψ ρ T xs σ R) :
    T.allLevelParamsDefined ks = true →
      Fits M.cval env φ ρ (T.instantiateLevelParams ks us) xs σ (R.instantiateLevelParams ks us) := by
  induction h with
  | nil => intro _; exact .nil
  | cons hA hx _ ih =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    simp only [Expr.instantiateLevelParams]
    exact .cons (den_inst M hL hψ hA hd.1.1) hx (ih hd.1.2)

end IxCC.Grounding
