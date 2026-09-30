/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Model.Annotated

/-! # Runtime terms: annotated syntax with free variables as levels (S1)

`RExpr β` is `AExpr β` with one more leaf, `fvar level`: the variable bound by
the `level`-th entry of the binder stack, counted from the outermost. A term
at a stack of depth `d` is *bvar-closed* (no loose de Bruijn index) and
mentions only levels below `d`. Opening a binder substitutes `fvar d` for its
index 0 (`inst1`), and nothing is shifted, since the replacement is
bvar-closed. This is nanoda's and con-leche's representation
(`ConLeche/Kernel/ExprOps.lean`, `instantiate1`, `abstract1`,
`abstractRange`), and Ix.Tc's `openBinder`/`abstractFVars` with levels in
place of unique names.

The model is not changed: claims stay about `AExpr` at a `Context`. The
bridge is `closeAt d j`, which reads a runtime term at stack depth `d` under
`j` further binders as the model term it denotes: level `k` is the index
`j + d - 1 - k`. It is a specification function; the commutation lemmas that
let rule sites rewrite their claims are in `Ix.Kernel.Runtime.Close`.

As for `AExpr` (B2), each node carries computed fields: `looseBound` (one
more than the largest loose index), `fvarBound` (one more than the largest
level, `0` when there is none) and `structHash`. Substitution and
abstraction stop at subterms their cutoff shows unchanged, by proved
`@[csimp]` equations, and equality is decided pointer-first. -/

namespace Ix.Kernel.Runtime

open Model Certified

universe u

inductive RExpr (β : Type u) where
  | bvar (index : Nat)
  | fvar (level : Nat)
  | sort (level : VLevel)
  | const (ref : ConstRef β) (levels : List VLevel)
  | app (fn arg : RExpr β)
  | lam (condition : PropWhen) (domain body : RExpr β)
  | forallE (condition : PropWhen) (domain body : RExpr β)
  | letE (type value body : RExpr β)
  | proj (ref : ConstRef β) (field : Nat) (major : RExpr β)
  | natLit (family : ConstRef β) (value : Nat)
with
  /-- One more than the largest loose de Bruijn index; `0` when bvar-closed. -/
  @[computed_field] looseBound : (β : Type u) → RExpr β → Nat
    | _, .bvar i => i + 1
    | _, .fvar _ => 0
    | _, .sort _ => 0
    | _, .const _ _ => 0
    | _, .app f a => max f.looseBound a.looseBound
    | _, .lam _ a b => max a.looseBound (b.looseBound - 1)
    | _, .forallE _ a b => max a.looseBound (b.looseBound - 1)
    | _, .letE t v b => max (max t.looseBound v.looseBound) (b.looseBound - 1)
    | _, .proj _ _ e => e.looseBound
    | _, .natLit _ _ => 0
  /-- One more than the largest free-variable level; `0` when there is none.
  Binders do not bind levels. -/
  @[computed_field] fvarBound : (β : Type u) → RExpr β → Nat
    | _, .bvar _ => 0
    | _, .fvar k => k + 1
    | _, .sort _ => 0
    | _, .const _ _ => 0
    | _, .app f a => max f.fvarBound a.fvarBound
    | _, .lam _ a b => max a.fvarBound b.fvarBound
    | _, .forallE _ a b => max a.fvarBound b.fvarBound
    | _, .letE t v b => max (max t.fvarBound v.fvarBound) b.fvarBound
    | _, .proj _ _ e => e.fvarBound
    | _, .natLit _ _ => 0
  /-- A structural hash, as `AExpr.structHash`, with its own tag for levels.
  Equal terms have equal hashes. -/
  @[computed_field] structHash : (β : Type u) → RExpr β → UInt64
    | _, .bvar i => mixHash 11 (hash i)
    | _, .fvar k => mixHash 43 (hash k)
    | _, .sort l => mixHash 13 (match l with
        | .zero => 1 | .succ _ => 2 | .max _ _ => 3 | .imax _ _ => 4 | .param i => mixHash 5 (hash i))
    | _, .const r ls => mixHash 17 (mixHash (match r with
        | .member _ i => hash i
        | .ctor _ i c => mixHash (hash i) (hash (c + 1))) (hash ls.length))
    | _, .app f a => mixHash 19 (mixHash f.structHash a.structHash)
    | _, .lam _ a b => mixHash 23 (mixHash a.structHash b.structHash)
    | _, .forallE _ a b => mixHash 29 (mixHash a.structHash b.structHash)
    | _, .letE t v b => mixHash 31 (mixHash t.structHash (mixHash v.structHash b.structHash))
    | _, .proj _ i e => mixHash 37 (mixHash (hash i) e.structHash)
    | _, .natLit _ n => mixHash 41 (hash n)
deriving DecidableEq

namespace RExpr

variable {β : Type u}

/-! ## Equality -/

/-- Equality decided pointer-first, as `AExpr.decEqFast`: identical objects
are equal, different structural hashes are unequal, and otherwise the
constructors are compared argument by argument, each argument the same way. -/
def decEqFast [DecidableEq β] (a b : RExpr β) : Decidable (a = b) :=
  withPtrEqDecEq a b fun _ =>
    if hh : a.structHash = b.structHash then
      match a, b with
      | .app f x, .app g y =>
        match decEqFast f g, decEqFast x y with
        | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
        | isFalse h, _ => isFalse fun e => h (by cases e; rfl)
        | _, isFalse h => isFalse fun e => h (by cases e; rfl)
      | .lam p d body, .lam p' d' body' =>
        if hp : p = p' then
          match decEqFast d d', decEqFast body body' with
          | isTrue h1, isTrue h2 => isTrue (hp ▸ h1 ▸ h2 ▸ rfl)
          | isFalse h, _ => isFalse fun e => h (by cases e; rfl)
          | _, isFalse h => isFalse fun e => h (by cases e; rfl)
        else isFalse fun e => hp (by cases e; rfl)
      | .forallE p d body, .forallE p' d' body' =>
        if hp : p = p' then
          match decEqFast d d', decEqFast body body' with
          | isTrue h1, isTrue h2 => isTrue (hp ▸ h1 ▸ h2 ▸ rfl)
          | isFalse h, _ => isFalse fun e => h (by cases e; rfl)
          | _, isFalse h => isFalse fun e => h (by cases e; rfl)
        else isFalse fun e => hp (by cases e; rfl)
      | .letE t v body, .letE t' v' body' =>
        match decEqFast t t', decEqFast v v', decEqFast body body' with
        | isTrue h1, isTrue h2, isTrue h3 => isTrue (h1 ▸ h2 ▸ h3 ▸ rfl)
        | isFalse h, _, _ => isFalse fun e => h (by cases e; rfl)
        | _, isFalse h, _ => isFalse fun e => h (by cases e; rfl)
        | _, _, isFalse h => isFalse fun e => h (by cases e; rfl)
      | .proj r i x, .proj r' i' x' =>
        if hri : r = r' ∧ i = i' then
          match decEqFast x x' with
          | isTrue h => isTrue (hri.1 ▸ hri.2 ▸ h ▸ rfl)
          | isFalse h => isFalse fun e => h (by cases e; rfl)
        else isFalse fun e => hri (by cases e; exact ⟨rfl, rfl⟩)
      | a, b => instDecidableEqRExpr a b
    else isFalse fun e => hh (e ▸ rfl)

/-- The runtime's equality on terms is `decEqFast`. -/
instance (priority := high) [DecidableEq β] : DecidableEq (RExpr β) := decEqFast

/-! ## Operations -/

/-- Substitute the bvar-closed `a` for the index `cutoff`, lowering the loose
indices above it. The replacement is not shifted: opening a binder with
`fvar d`, beta and zeta all substitute a bvar-closed term. -/
def inst1 : RExpr β → RExpr β → (cutoff : Nat := 0) → RExpr β
  | .bvar i, a, k => if i < k then .bvar i else if i = k then a else .bvar (i - 1)
  | .fvar l, _, _ => .fvar l
  | .sort l, _, _ => .sort l
  | .const r ls, _, _ => .const r ls
  | .app f x, a, k => .app (f.inst1 a k) (x.inst1 a k)
  | .lam p d b, a, k => .lam p (d.inst1 a k) (b.inst1 a (k + 1))
  | .forallE p d b, a, k => .forallE p (d.inst1 a k) (b.inst1 a (k + 1))
  | .letE t v b, a, k => .letE (t.inst1 a k) (v.inst1 a k) (b.inst1 a (k + 1))
  | .proj r i x, a, k => .proj r i (x.inst1 a k)
  | .natLit r v, _, _ => .natLit r v

/-- Instantiate universe parameters. -/
def instL (levels : List VLevel) : RExpr β → RExpr β
  | .bvar i => .bvar i
  | .fvar l => .fvar l
  | .sort l => .sort (l.inst levels)
  | .const r ls => .const r (ls.map (VLevel.inst levels))
  | .app f a => .app (f.instL levels) (a.instL levels)
  | .lam p a b => .lam (instCondition levels p) (a.instL levels) (b.instL levels)
  | .forallE p a b => .forallE (instCondition levels p) (a.instL levels) (b.instL levels)
  | .letE t v b => .letE (t.instL levels) (v.instL levels) (b.instL levels)
  | .proj r i e => .proj r i (e.instL levels)
  | .natLit r v => .natLit r v

/-- Apply to arguments, outermost first. -/
def appN (f : RExpr β) : List (RExpr β) → RExpr β
  | [] => f
  | x :: xs => appN (.app f x) xs

/-- Bind the variable at `level` as the index `cutoff`, the inverse of
opening with `fvar level` (con-leche's `abstract1`). Loose indices are
unchanged: the result is the body of a binder placed at `level`. -/
def abstract1 (level : Nat) : RExpr β → (cutoff : Nat := 0) → RExpr β
  | .bvar i, _ => .bvar i
  | .fvar l, k => if l = level then .bvar k else .fvar l
  | .sort l, _ => .sort l
  | .const r ls, _ => .const r ls
  | .app f a, k => .app (abstract1 level f k) (abstract1 level a k)
  | .lam p a b, k => .lam p (abstract1 level a k) (abstract1 level b (k + 1))
  | .forallE p a b, k => .forallE p (abstract1 level a k) (abstract1 level b (k + 1))
  | .letE t v b, k => .letE (abstract1 level t k) (abstract1 level v k) (abstract1 level b (k + 1))
  | .proj r i e, k => .proj r i (abstract1 level e k)
  | .natLit r v, _ => .natLit r v

/-- The model term a runtime term denotes at stack depth `d`, under `j`
further binders: level `k` is the index `j + d - 1 - k`, and indices are
kept. A specification function; claims are stated about its results. -/
def closeAt (d j : Nat) : RExpr β → AExpr β
  | .bvar i => .bvar i
  | .fvar k => .bvar (j + d - 1 - k)
  | .sort l => .sort l
  | .const r ls => .const r ls
  | .app f a => .app (closeAt d j f) (closeAt d j a)
  | .lam p a b => .lam p (closeAt d j a) (closeAt d (j + 1) b)
  | .forallE p a b => .forallE p (closeAt d j a) (closeAt d (j + 1) b)
  | .letE t v b => .letE (closeAt d j t) (closeAt d j v) (closeAt d (j + 1) b)
  | .proj r i e => .proj r i (closeAt d j e)
  | .natLit r v => .natLit r v

/-- The model term at stack depth `d`. -/
abbrev close (d : Nat) : RExpr β → AExpr β := closeAt d 0

/-- A model term as a runtime term with no free variables. -/
def ofAExpr : AExpr β → RExpr β
  | .bvar i => .bvar i
  | .sort l => .sort l
  | .const r ls => .const r ls
  | .app f a => .app (ofAExpr f) (ofAExpr a)
  | .lam p a b => .lam p (ofAExpr a) (ofAExpr b)
  | .forallE p a b => .forallE p (ofAExpr a) (ofAExpr b)
  | .letE t v b => .letE (ofAExpr t) (ofAExpr v) (ofAExpr b)
  | .proj r i e => .proj r i (ofAExpr e)
  | .natLit r v => .natLit r v

/-- A model term written at a context of depth `d`, under `j` further
binders, as a runtime term at stack depth `d`: its loose indices below the
context's depth become levels, the inverse of `closeAt d j`. Indices beyond
the context are kept. This is how a context built by `Context.push` becomes a
stack. -/
def openAt (d j : Nat) : AExpr β → RExpr β
  | .bvar i => if i < j then .bvar i else if i - j < d then .fvar (d - 1 - (i - j)) else .bvar i
  | .sort l => .sort l
  | .const r ls => .const r ls
  | .app f a => .app (openAt d j f) (openAt d j a)
  | .lam p a b => .lam p (openAt d j a) (openAt d (j + 1) b)
  | .forallE p a b => .forallE p (openAt d j a) (openAt d (j + 1) b)
  | .letE t v b => .letE (openAt d j t) (openAt d j v) (openAt d (j + 1) b)
  | .proj r i e => .proj r i (openAt d j e)
  | .natLit r v => .natLit r v

/-! ## Operations that skip unchanged subterms

As for `AExpr` (B2): a subterm whose loose indices are all below the cutoff
is unchanged by `inst1`, and one with no level at or above `level` is
unchanged by `abstract1`. The compiler uses the fast versions by the proved
equations. -/

theorem inst1_of_looseBound_le {a : RExpr β} : ∀ {e : RExpr β} {k : Nat},
    e.looseBound ≤ k → e.inst1 a k = e
  | .bvar i, k, h => by
    simp only [looseBound] at h
    simp [inst1, show i < k by omega]
  | .fvar _, _, _ | .sort _, _, _ | .const _ _, _, _ | .natLit _ _, _, _ => rfl
  | .app f x, k, h => by
    simp only [looseBound, Nat.max_le] at h
    simp [inst1, inst1_of_looseBound_le h.1, inst1_of_looseBound_le h.2]
  | .lam p d b, k, h | .forallE p d b, k, h => by
    simp only [looseBound, Nat.max_le] at h
    simp [inst1, inst1_of_looseBound_le h.1, inst1_of_looseBound_le (e := b) (k := k + 1) (by omega)]
  | .letE t v b, k, h => by
    simp only [looseBound, Nat.max_le] at h
    simp [inst1, inst1_of_looseBound_le h.1.1, inst1_of_looseBound_le h.1.2,
      inst1_of_looseBound_le (e := b) (k := k + 1) (by omega)]
  | .proj r i x, k, h => by
    simp only [looseBound] at h
    simp [inst1, inst1_of_looseBound_le h]

/-- `inst1`, stopping at subterms bounded by the cutoff. -/
def inst1Fast (e a : RExpr β) (cutoff : Nat := 0) : RExpr β :=
  if e.looseBound ≤ cutoff then e else
  match e with
  | .bvar i => if i < cutoff then .bvar i else if i = cutoff then a else .bvar (i - 1)
  | .fvar l => .fvar l
  | .sort l => .sort l
  | .const r ls => .const r ls
  | .app f x => .app (inst1Fast f a cutoff) (inst1Fast x a cutoff)
  | .lam p d b => .lam p (inst1Fast d a cutoff) (inst1Fast b a (cutoff + 1))
  | .forallE p d b => .forallE p (inst1Fast d a cutoff) (inst1Fast b a (cutoff + 1))
  | .letE t v b => .letE (inst1Fast t a cutoff) (inst1Fast v a cutoff) (inst1Fast b a (cutoff + 1))
  | .proj r i x => .proj r i (inst1Fast x a cutoff)
  | .natLit r v => .natLit r v

theorem inst1Fast_eq (a : RExpr β) : ∀ (e : RExpr β) (cutoff : Nat),
    inst1Fast e a cutoff = inst1 e a cutoff := by
  intro e
  induction e with
  | bvar _ | fvar _ | sort _ | const _ _ | natLit _ _ =>
    intro k; unfold inst1Fast; split
    · exact (inst1_of_looseBound_le ‹_›).symm
    · rfl
  | app f x hf hx =>
    intro k; unfold inst1Fast; split
    · exact (inst1_of_looseBound_le ‹_›).symm
    · simp [inst1, hf, hx]
  | lam p d b hd hb | forallE p d b hd hb =>
    intro k; unfold inst1Fast; split
    · exact (inst1_of_looseBound_le ‹_›).symm
    · simp [inst1, hd, hb]
  | letE t v b ht hv hb =>
    intro k; unfold inst1Fast; split
    · exact (inst1_of_looseBound_le ‹_›).symm
    · simp [inst1, ht, hv, hb]
  | proj r i x hx =>
    intro k; unfold inst1Fast; split
    · exact (inst1_of_looseBound_le ‹_›).symm
    · simp [inst1, hx]

@[csimp] theorem inst1_eq_inst1Fast : @inst1 = @inst1Fast := by
  funext β e a k; exact (inst1Fast_eq a e k).symm

theorem abstract1_of_fvarBound_le {level : Nat} : ∀ {e : RExpr β} {k : Nat},
    e.fvarBound ≤ level → abstract1 level e k = e
  | .fvar l, k, h => by
    simp only [fvarBound] at h
    simp [abstract1, show l ≠ level by omega]
  | .bvar _, _, _ | .sort _, _, _ | .const _ _, _, _ | .natLit _ _, _, _ => rfl
  | .app f x, k, h => by
    simp only [fvarBound, Nat.max_le] at h
    simp [abstract1, abstract1_of_fvarBound_le h.1, abstract1_of_fvarBound_le h.2]
  | .lam p d b, k, h | .forallE p d b, k, h => by
    simp only [fvarBound, Nat.max_le] at h
    simp [abstract1, abstract1_of_fvarBound_le h.1, abstract1_of_fvarBound_le h.2]
  | .letE t v b, k, h => by
    simp only [fvarBound, Nat.max_le] at h
    simp [abstract1, abstract1_of_fvarBound_le h.1.1, abstract1_of_fvarBound_le h.1.2,
      abstract1_of_fvarBound_le h.2]
  | .proj r i x, k, h => by
    simp only [fvarBound] at h
    simp [abstract1, abstract1_of_fvarBound_le h]

/-- `abstract1`, stopping at subterms without the abstracted level or any
above it. -/
def abstract1Fast (level : Nat) (e : RExpr β) (cutoff : Nat := 0) : RExpr β :=
  if e.fvarBound ≤ level then e else
  match e with
  | .bvar i => .bvar i
  | .fvar l => if l = level then .bvar cutoff else .fvar l
  | .sort l => .sort l
  | .const r ls => .const r ls
  | .app f a => .app (abstract1Fast level f cutoff) (abstract1Fast level a cutoff)
  | .lam p a b => .lam p (abstract1Fast level a cutoff) (abstract1Fast level b (cutoff + 1))
  | .forallE p a b => .forallE p (abstract1Fast level a cutoff) (abstract1Fast level b (cutoff + 1))
  | .letE t v b =>
    .letE (abstract1Fast level t cutoff) (abstract1Fast level v cutoff)
      (abstract1Fast level b (cutoff + 1))
  | .proj r i e => .proj r i (abstract1Fast level e cutoff)
  | .natLit r v => .natLit r v

theorem abstract1Fast_eq (level : Nat) : ∀ (e : RExpr β) (cutoff : Nat),
    abstract1Fast level e cutoff = abstract1 level e cutoff := by
  intro e
  induction e with
  | bvar _ | fvar _ | sort _ | const _ _ | natLit _ _ =>
    intro k; unfold abstract1Fast; split
    · exact (abstract1_of_fvarBound_le ‹_›).symm
    · rfl
  | app f x hf hx =>
    intro k; unfold abstract1Fast; split
    · exact (abstract1_of_fvarBound_le ‹_›).symm
    · simp [abstract1, hf, hx]
  | lam p d b hd hb | forallE p d b hd hb =>
    intro k; unfold abstract1Fast; split
    · exact (abstract1_of_fvarBound_le ‹_›).symm
    · simp [abstract1, hd, hb]
  | letE t v b ht hv hb =>
    intro k; unfold abstract1Fast; split
    · exact (abstract1_of_fvarBound_le ‹_›).symm
    · simp [abstract1, ht, hv, hb]
  | proj r i x hx =>
    intro k; unfold abstract1Fast; split
    · exact (abstract1_of_fvarBound_le ‹_›).symm
    · simp [abstract1, hx]

@[csimp] theorem abstract1_eq_abstract1Fast : @abstract1 = @abstract1Fast := by
  funext β level e k; exact (abstract1Fast_eq level e k).symm

end RExpr

end Ix.Kernel.Runtime
