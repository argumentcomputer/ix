/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Runtime.Stack
import Ix.Kernel.Model.Inductive.Telescope
import Ix.Kernel.Model.ContextTransport
import Ix.Kernel.Claims

/-! # Closing runtime terms: the commutation lemmas (S1)

A computation on runtime terms at a stack `s` of depth `d` produces claims
about `close d e` at `s.view`. Each rule application then needs one rewrite
that moves `close` through the runtime operation it performed. These are
those rewrites, each by induction on the term:

* `close_open`: opening a binder with the next level is reading its body one
  binder deeper (`TypingClaim.lam`, `.forallE`, `ConvClaim.lam`, `.forallE`,
  `ConvClaim.eta`);
* `close_inst`: substituting a bvar-closed term is model substitution of its
  closed form (beta, zeta, application typing, `applyTyped`);
* `close_abstract1`: binding the top level is reading the term one level
  shallower under one more binder (building the type of a λ or Π body);
* `close_instL`, `close_app`, `close_appN`, `close_proj`: structural;
* `close_lift`: a term closed at a shallower depth is the lift of its closed
  form (`view_push`, `getElem?_view`, and weakening along a stack);
* `close_ofAExpr`, `close_openAt`: the ingress maps are right inverse to
  `close`.

Side conditions are the stack's own invariants: terms at depth `d` are
bvar-closed and mention levels below `d` (`fvarBound ≤ d`); the bounds are
preserved by every operation (the `looseBound_*`/`fvarBound_*` lemmas).

The last section proves weakening along a stack extension for the claims
the caches hold (typing, reduction, conversion) and for formedness
(`Stack.typing_extend` and its siblings): the transport that makes
weakening-only cache reuse sound. Nothing here moves a claim to a shallower
or sibling stack. -/

namespace Ix.Kernel.Runtime

open Model Certified

universe u v

variable {β : Type u}

namespace RExpr

/-! ## Structural equations -/

@[simp] theorem closeAt_bvar (d j i : Nat) : closeAt d j (.bvar i : RExpr β) = .bvar i := rfl
@[simp] theorem closeAt_fvar (d j k : Nat) :
    closeAt d j (.fvar k : RExpr β) = .bvar (j + d - 1 - k) := rfl
@[simp] theorem closeAt_sort (d j : Nat) (l : VLevel) : closeAt d j (.sort l : RExpr β) = .sort l := rfl
@[simp] theorem closeAt_const (d j : Nat) (r : ConstRef β) (ls : List VLevel) :
    closeAt d j (.const r ls) = .const r ls := rfl
@[simp] theorem closeAt_app (d j : Nat) (f a : RExpr β) :
    closeAt d j (.app f a) = .app (closeAt d j f) (closeAt d j a) := rfl
@[simp] theorem closeAt_lam (d j : Nat) (p : PropWhen) (a b : RExpr β) :
    closeAt d j (.lam p a b) = .lam p (closeAt d j a) (closeAt d (j + 1) b) := rfl
@[simp] theorem closeAt_forallE (d j : Nat) (p : PropWhen) (a b : RExpr β) :
    closeAt d j (.forallE p a b) = .forallE p (closeAt d j a) (closeAt d (j + 1) b) := rfl
@[simp] theorem closeAt_letE (d j : Nat) (t w b : RExpr β) :
    closeAt d j (.letE t w b) = .letE (closeAt d j t) (closeAt d j w) (closeAt d (j + 1) b) := rfl
@[simp] theorem closeAt_proj (d j : Nat) (r : ConstRef β) (i : Nat) (e : RExpr β) :
    closeAt d j (.proj r i e) = .proj r i (closeAt d j e) := rfl
@[simp] theorem closeAt_natLit (d j : Nat) (r : ConstRef β) (n : Nat) :
    closeAt d j (.natLit r n : RExpr β) = .natLit r n := rfl

/-- A level at the top-level of a stack of depth `d` is the index `d - 1 - k`. -/
theorem close_fvar (d k : Nat) : close d (.fvar k : RExpr β) = .bvar (d - 1 - k) := by
  simp

theorem close_app (d : Nat) (f a : RExpr β) : close d (.app f a) = .app (close d f) (close d a) := rfl

theorem close_proj (d : Nat) (r : ConstRef β) (i : Nat) (e : RExpr β) :
    close d (.proj r i e) = .proj r i (close d e) := rfl

theorem closeAt_appN (d j : Nat) (f : RExpr β) (args : List (RExpr β)) :
    closeAt d j (f.appN args) = (closeAt d j f).appN (args.map (closeAt d j)) := by
  induction args generalizing f with
  | nil => rfl
  | cons x xs ih => simp only [appN, AExpr.appN, List.map_cons, ih, closeAt_app]

theorem close_appN (d : Nat) (f : RExpr β) (args : List (RExpr β)) :
    close d (f.appN args) = (close d f).appN (args.map (close d)) :=
  closeAt_appN d 0 f args

theorem closeAt_instL (d j : Nat) (ls : List VLevel) (e : RExpr β) :
    closeAt d j (e.instL ls) = (closeAt d j e).instL ls := by
  induction e generalizing j <;> simp_all [instL, AExpr.instL]

theorem close_instL (d : Nat) (ls : List VLevel) (e : RExpr β) :
    close d (e.instL ls) = (close d e).instL ls :=
  closeAt_instL d 0 ls e

/-! ## Ingress -/

theorem closeAt_ofAExpr (d j : Nat) (e : AExpr β) : closeAt d j (ofAExpr e) = e := by
  induction e generalizing j <;> simp_all [ofAExpr]

/-- The injection has no free variables, so no side condition is needed. -/
theorem close_ofAExpr (d : Nat) (e : AExpr β) : close d (ofAExpr e) = e := closeAt_ofAExpr d 0 e

theorem closeAt_openAt (d j : Nat) (e : AExpr β) : closeAt d j (openAt d j e) = e := by
  induction e generalizing j with
  | bvar i =>
    simp only [openAt]
    split
    · rfl
    · split
      · simp only [closeAt_fvar, AExpr.bvar.injEq]
        omega
      · rfl
  | _ => simp_all [openAt]

/-- Opening is right inverse to closing. Indices beyond the context are kept,
so no side condition is needed; the result is bvar-closed exactly when the
term's indices are within the context (`looseBound_openAt_le`). -/
theorem close_openAt (d : Nat) (e : AExpr β) : close d (openAt d 0 e) = e := closeAt_openAt d 0 e

/-! ## Lifting -/

/-- Closing deeper, or under more binders, lifts the closed form over the
inserted variables. Indices bound inside the term are below the cutoff. -/
theorem closeAt_liftN {d n m : Nat} : ∀ {e : RExpr β} {j : Nat},
    e.fvarBound ≤ d → e.looseBound ≤ j →
      closeAt (d + n) (j + m) e = (closeAt d j e).liftN (n + m) j
  | .bvar i, j, _, hl => by
    simp only [looseBound] at hl
    simp [AExpr.liftN, liftVar, show i < j by omega]
  | .fvar k, j, hf, _ => by
    simp only [fvarBound] at hf
    simp only [closeAt_fvar, AExpr.liftN, liftVar, AExpr.bvar.injEq]
    split <;> omega
  | .sort _, _, _, _ | .const _ _, _, _, _ | .natLit _ _, _, _, _ => rfl
  | .app f a, j, hf, hl => by
    simp only [fvarBound, looseBound, Nat.max_le] at hf hl
    simp only [closeAt_app, AExpr.liftN, closeAt_liftN hf.1 hl.1, closeAt_liftN hf.2 hl.2]
  | .lam p a b, j, hf, hl | .forallE p a b, j, hf, hl => by
    simp only [fvarBound, looseBound, Nat.max_le] at hf hl
    have hb := closeAt_liftN (d := d) (n := n) (m := m) (e := b) (j := j + 1) hf.2 (by omega)
    rw [show j + 1 + m = j + m + 1 by omega] at hb
    simp only [closeAt_lam, closeAt_forallE, AExpr.liftN, closeAt_liftN hf.1 hl.1, hb]
  | .letE t w b, j, hf, hl => by
    simp only [fvarBound, looseBound, Nat.max_le] at hf hl
    have hb := closeAt_liftN (d := d) (n := n) (m := m) (e := b) (j := j + 1) hf.2 (by omega)
    rw [show j + 1 + m = j + m + 1 by omega] at hb
    simp only [closeAt_letE, AExpr.liftN, closeAt_liftN hf.1.1 hl.1.1, closeAt_liftN hf.1.2 hl.1.2, hb]
  | .proj r i e, j, hf, hl => by
    simp only [fvarBound, looseBound] at hf hl
    simp only [closeAt_proj, AExpr.liftN, closeAt_liftN hf hl]

/-- Reading a term under more binders lifts its closed form. -/
theorem closeAt_shift {d j m : Nat} {e : RExpr β} (hf : e.fvarBound ≤ d) (hl : e.looseBound ≤ j) :
    closeAt d (j + m) e = (closeAt d j e).liftN m j := by
  simpa using closeAt_liftN (n := 0) (m := m) hf hl

/-- A bvar-closed term closed at a deeper stack is the lift of its closed form
at any depth that contains its levels. -/
theorem close_lift {d d' : Nat} {e : RExpr β} (hd : d ≤ d') (hf : e.fvarBound ≤ d)
    (hl : e.looseBound = 0) : close d' e = (close d e).liftN (d' - d) := by
  have h := closeAt_liftN (d := d) (n := d' - d) (m := 0) (j := 0) hf (by omega)
  simpa [show d + (d' - d) = d' by omega] using h

/-! ## Substitution and abstraction -/

/-- Substituting a bvar-closed term under `k` binders is model substitution
of its closed form. -/
theorem closeAt_inst1 {d : Nat} {a : RExpr β} (haf : a.fvarBound ≤ d) (hal : a.looseBound = 0) :
    ∀ {b : RExpr β} {k : Nat}, b.fvarBound ≤ d →
      closeAt d k (b.inst1 a k) = (closeAt d (k + 1) b).inst (close d a) k
  | .bvar i, k, _ => by
    by_cases hlt : i < k
    · simp [inst1, AExpr.inst, AExpr.instVar_eq, hlt]
    · by_cases heq : i = k
      · subst heq
        simp only [inst1, Nat.lt_irrefl, ↓reduceIte, closeAt_bvar, AExpr.inst, AExpr.instVar_eq]
        simpa using closeAt_shift (d := d) (j := 0) (m := i) haf (by omega)
      · simp [inst1, AExpr.inst, AExpr.instVar_eq, hlt, heq]
  | .fvar l, k, hf => by
    simp only [fvarBound] at hf
    simp only [inst1, closeAt_fvar, AExpr.inst, AExpr.instVar_eq]
    split
    · exfalso; omega
    · split
      · exfalso; omega
      · simp only [AExpr.bvar.injEq]
        omega
  | .sort _, _, _ | .const _ _, _, _ | .natLit _ _, _, _ => rfl
  | .app f x, k, hf => by
    simp only [fvarBound, Nat.max_le] at hf
    simp only [inst1, closeAt_app, AExpr.inst, closeAt_inst1 haf hal hf.1, closeAt_inst1 haf hal hf.2]
  | .lam p x b, k, hf | .forallE p x b, k, hf => by
    simp only [fvarBound, Nat.max_le] at hf
    simp only [inst1, closeAt_lam, closeAt_forallE, AExpr.inst, closeAt_inst1 haf hal hf.1,
      closeAt_inst1 haf hal (b := b) (k := k + 1) hf.2]
  | .letE t w b, k, hf => by
    simp only [fvarBound, Nat.max_le] at hf
    simp only [inst1, closeAt_letE, AExpr.inst, closeAt_inst1 haf hal hf.1.1,
      closeAt_inst1 haf hal hf.1.2, closeAt_inst1 haf hal (b := b) (k := k + 1) hf.2]
  | .proj r i x, k, hf => by
    simp only [fvarBound] at hf
    simp only [inst1, closeAt_proj, AExpr.inst, closeAt_inst1 haf hal hf]

/-- Beta, zeta and application typing: `close d (b.inst1 a)` is the model
instance of the binder body `closeAt d 1 b` at `close d a`. -/
theorem close_inst {d : Nat} {a b : RExpr β} (hbf : b.fvarBound ≤ d) (haf : a.fvarBound ≤ d)
    (hal : a.looseBound = 0) : close d (b.inst1 a) = (closeAt d 1 b).inst (close d a) :=
  closeAt_inst1 haf hal hbf

/-- Opening with the next level under `k` binders. -/
theorem closeAt_open {d : Nat} : ∀ {b : RExpr β} {k : Nat}, b.fvarBound ≤ d → b.looseBound ≤ k + 1 →
    closeAt (d + 1) k (b.inst1 (.fvar d) k) = closeAt d (k + 1) b
  | .bvar i, k, _, hl => by
    simp only [looseBound] at hl
    by_cases hlt : i < k
    · simp [inst1, hlt]
    · have heq : i = k := by omega
      subst heq
      simp only [inst1, Nat.lt_irrefl, ↓reduceIte, closeAt_fvar, closeAt_bvar, AExpr.bvar.injEq]
      omega
  | .fvar l, k, hf, _ => by
    simp only [fvarBound] at hf
    simp only [inst1, closeAt_fvar, AExpr.bvar.injEq]
    omega
  | .sort _, _, _, _ | .const _ _, _, _, _ | .natLit _ _, _, _, _ => rfl
  | .app f x, k, hf, hl => by
    simp only [fvarBound, looseBound, Nat.max_le] at hf hl
    simp only [inst1, closeAt_app, closeAt_open hf.1 hl.1, closeAt_open hf.2 hl.2]
  | .lam p x b, k, hf, hl | .forallE p x b, k, hf, hl => by
    simp only [fvarBound, looseBound, Nat.max_le] at hf hl
    simp only [inst1, closeAt_lam, closeAt_forallE, closeAt_open hf.1 hl.1,
      closeAt_open (b := b) (k := k + 1) hf.2 (by omega)]
  | .letE t w b, k, hf, hl => by
    simp only [fvarBound, looseBound, Nat.max_le] at hf hl
    simp only [inst1, closeAt_letE, closeAt_open hf.1.1 hl.1.1, closeAt_open hf.1.2 hl.1.2,
      closeAt_open (b := b) (k := k + 1) hf.2 (by omega)]
  | .proj r i x, k, hf, hl => by
    simp only [fvarBound, looseBound] at hf hl
    simp only [inst1, closeAt_proj, closeAt_open hf hl]

/-- Opening a binder body at the top of a stack of depth `d` with `fvar d` is
reading that body at depth `d` under one binder. -/
theorem close_open {d : Nat} {b : RExpr β} (hf : b.fvarBound ≤ d) (hl : b.looseBound ≤ 1) :
    close (d + 1) (b.inst1 (.fvar d)) = closeAt d 1 b :=
  closeAt_open hf hl

/-- Binding the top level under `j` binders. -/
theorem closeAt_abstract1 {d : Nat} : ∀ {e : RExpr β} {j : Nat}, e.fvarBound ≤ d + 1 →
    closeAt d (j + 1) (abstract1 d e j) = closeAt (d + 1) j e
  | .bvar _, _, _ => rfl
  | .fvar l, j, hf => by
    simp only [fvarBound] at hf
    simp only [abstract1]
    split
    · subst l
      simp only [closeAt_bvar, closeAt_fvar, AExpr.bvar.injEq]
      omega
    · simp only [closeAt_fvar, AExpr.bvar.injEq]
      omega
  | .sort _, _, _ | .const _ _, _, _ | .natLit _ _, _, _ => rfl
  | .app f x, j, hf => by
    simp only [fvarBound, Nat.max_le] at hf
    simp only [abstract1, closeAt_app, closeAt_abstract1 hf.1, closeAt_abstract1 hf.2]
  | .lam p x b, j, hf | .forallE p x b, j, hf => by
    simp only [fvarBound, Nat.max_le] at hf
    simp only [abstract1, closeAt_lam, closeAt_forallE, closeAt_abstract1 hf.1,
      closeAt_abstract1 (e := b) (j := j + 1) hf.2]
  | .letE t w b, j, hf => by
    simp only [fvarBound, Nat.max_le] at hf
    simp only [abstract1, closeAt_letE, closeAt_abstract1 hf.1.1, closeAt_abstract1 hf.1.2,
      closeAt_abstract1 (e := b) (j := j + 1) hf.2]
  | .proj r i x, j, hf => by
    simp only [fvarBound] at hf
    simp only [abstract1, closeAt_proj, closeAt_abstract1 hf]

/-- The type of a λ or Π body inferred at depth `d + 1`, bound as the body of
a binder at depth `d`. -/
theorem close_abstract1 {d : Nat} {e : RExpr β} (hf : e.fvarBound ≤ d + 1) :
    closeAt d 1 (abstract1 d e) = close (d + 1) e :=
  closeAt_abstract1 hf

/-! ## Bounds -/

theorem looseBound_inst1_le {a : RExpr β} (hal : a.looseBound = 0) :
    ∀ {b : RExpr β} {k : Nat}, b.looseBound ≤ k + 1 → (b.inst1 a k).looseBound ≤ k
  | .bvar i, k, hl => by
    simp only [looseBound] at hl
    by_cases hlt : i < k
    · simp [inst1, hlt, looseBound]
      omega
    · simp [inst1, show i = k by omega, hal]
  | .fvar _, _, _ | .sort _, _, _ | .const _ _, _, _ | .natLit _ _, _, _ => by
    simp [inst1, looseBound]
  | .app f x, k, hl => by
    simp only [looseBound, Nat.max_le] at hl
    simp only [inst1, looseBound, Nat.max_le]
    exact ⟨looseBound_inst1_le hal hl.1, looseBound_inst1_le hal hl.2⟩
  | .lam p x b, k, hl | .forallE p x b, k, hl => by
    simp only [looseBound, Nat.max_le] at hl
    have hb := looseBound_inst1_le hal (b := b) (k := k + 1) (by omega)
    simp only [inst1, looseBound, Nat.max_le]
    exact ⟨looseBound_inst1_le hal hl.1, by omega⟩
  | .letE t w b, k, hl => by
    simp only [looseBound, Nat.max_le] at hl
    have hb := looseBound_inst1_le hal (b := b) (k := k + 1) (by omega)
    simp only [inst1, looseBound, Nat.max_le]
    exact ⟨⟨looseBound_inst1_le hal hl.1.1, looseBound_inst1_le hal hl.1.2⟩, by omega⟩
  | .proj r i x, k, hl => by
    simp only [looseBound] at hl
    simp only [inst1, looseBound]
    exact looseBound_inst1_le hal hl

theorem fvarBound_inst1_le (a : RExpr β) :
    ∀ (b : RExpr β) (k : Nat), (b.inst1 a k).fvarBound ≤ max b.fvarBound a.fvarBound
  | .bvar i, k => by
    simp only [inst1]
    split
    · simp only [fvarBound]; omega
    · split
      · simp only [fvarBound]; omega
      · simp only [fvarBound]; omega
  | .fvar _, _ | .sort _, _ | .const _ _, _ | .natLit _ _, _ => by
    simp only [inst1, fvarBound]
    omega
  | .app f x, k => by
    have := fvarBound_inst1_le a f k
    have := fvarBound_inst1_le a x k
    simp only [inst1, fvarBound]
    omega
  | .lam p x b, k | .forallE p x b, k => by
    have := fvarBound_inst1_le a x k
    have := fvarBound_inst1_le a b (k + 1)
    simp only [inst1, fvarBound]
    omega
  | .letE t w b, k => by
    have := fvarBound_inst1_le a t k
    have := fvarBound_inst1_le a w k
    have := fvarBound_inst1_le a b (k + 1)
    simp only [inst1, fvarBound]
    omega
  | .proj r i x, k => by
    have := fvarBound_inst1_le a x k
    simp only [inst1, fvarBound]
    omega

@[simp] theorem looseBound_instL (ls : List VLevel) (e : RExpr β) :
    (e.instL ls).looseBound = e.looseBound := by
  induction e <;> simp_all [instL, looseBound]

@[simp] theorem fvarBound_instL (ls : List VLevel) (e : RExpr β) :
    (e.instL ls).fvarBound = e.fvarBound := by
  induction e <;> simp_all [instL, fvarBound]

theorem fvarBound_abstract1_le {d : Nat} : ∀ {e : RExpr β} {k : Nat}, e.fvarBound ≤ d + 1 →
    (abstract1 d e k).fvarBound ≤ d
  | .fvar l, k, hf => by
    simp only [fvarBound] at hf
    simp only [abstract1]
    split
    · simp [fvarBound]
    · simp only [fvarBound]
      omega
  | .bvar _, _, _ | .sort _, _, _ | .const _ _, _, _ | .natLit _ _, _, _ => by
    simp [abstract1, fvarBound]
  | .app f x, k, hf => by
    simp only [fvarBound, Nat.max_le] at hf
    simp only [abstract1, fvarBound, Nat.max_le]
    exact ⟨fvarBound_abstract1_le hf.1, fvarBound_abstract1_le hf.2⟩
  | .lam p x b, k, hf | .forallE p x b, k, hf => by
    simp only [fvarBound, Nat.max_le] at hf
    simp only [abstract1, fvarBound, Nat.max_le]
    exact ⟨fvarBound_abstract1_le hf.1, fvarBound_abstract1_le hf.2⟩
  | .letE t w b, k, hf => by
    simp only [fvarBound, Nat.max_le] at hf
    simp only [abstract1, fvarBound, Nat.max_le]
    exact ⟨⟨fvarBound_abstract1_le hf.1.1, fvarBound_abstract1_le hf.1.2⟩, fvarBound_abstract1_le hf.2⟩
  | .proj r i x, k, hf => by
    simp only [fvarBound] at hf
    simp only [abstract1, fvarBound]
    exact fvarBound_abstract1_le hf

theorem looseBound_abstract1_le {d : Nat} : ∀ {e : RExpr β} {k : Nat}, e.looseBound ≤ k →
    (abstract1 d e k).looseBound ≤ k + 1
  | .bvar i, k, hl => by
    simp only [looseBound] at hl
    simp only [abstract1, looseBound]
    omega
  | .fvar l, k, _ => by
    simp only [abstract1]
    split <;> simp [looseBound]
  | .sort _, _, _ | .const _ _, _, _ | .natLit _ _, _, _ => by simp [abstract1, looseBound]
  | .app f x, k, hl => by
    simp only [looseBound, Nat.max_le] at hl
    simp only [abstract1, looseBound, Nat.max_le]
    exact ⟨looseBound_abstract1_le hl.1, looseBound_abstract1_le hl.2⟩
  | .lam p x b, k, hl | .forallE p x b, k, hl => by
    simp only [looseBound, Nat.max_le] at hl
    have hb := looseBound_abstract1_le (d := d) (e := b) (k := k + 1) (by omega)
    simp only [abstract1, looseBound, Nat.max_le]
    exact ⟨looseBound_abstract1_le hl.1, by omega⟩
  | .letE t w b, k, hl => by
    simp only [looseBound, Nat.max_le] at hl
    have hb := looseBound_abstract1_le (d := d) (e := b) (k := k + 1) (by omega)
    simp only [abstract1, looseBound, Nat.max_le]
    exact ⟨⟨looseBound_abstract1_le hl.1.1, looseBound_abstract1_le hl.1.2⟩, by omega⟩
  | .proj r i x, k, hl => by
    simp only [looseBound] at hl
    simp only [abstract1, looseBound]
    exact looseBound_abstract1_le hl

@[simp] theorem looseBound_ofAExpr (e : AExpr β) : (ofAExpr e).looseBound = e.looseBound := by
  induction e <;> simp_all [ofAExpr, looseBound, AExpr.looseBound]

@[simp] theorem fvarBound_ofAExpr (e : AExpr β) : (ofAExpr e).fvarBound = 0 := by
  induction e <;> simp_all [ofAExpr, fvarBound]

theorem fvarBound_openAt_le (d : Nat) : ∀ (e : AExpr β) (j : Nat), (openAt d j e).fvarBound ≤ d
  | .bvar i, j => by
    simp only [openAt]
    split
    · simp [fvarBound]
    · split
      · simp only [fvarBound]; omega
      · simp [fvarBound]
  | .sort _, _ | .const _ _, _ | .natLit _ _, _ => by simp [openAt, fvarBound]
  | .app f x, j => by
    have := fvarBound_openAt_le d f j
    have := fvarBound_openAt_le d x j
    simp only [openAt, fvarBound]; omega
  | .lam p x b, j | .forallE p x b, j => by
    have := fvarBound_openAt_le d x j
    have := fvarBound_openAt_le d b (j + 1)
    simp only [openAt, fvarBound]; omega
  | .letE t w b, j => by
    have := fvarBound_openAt_le d t j
    have := fvarBound_openAt_le d w j
    have := fvarBound_openAt_le d b (j + 1)
    simp only [openAt, fvarBound]; omega
  | .proj r i x, j => by
    have := fvarBound_openAt_le d x j
    simp only [openAt, fvarBound]; omega

theorem looseBound_openAt_le {d : Nat} : ∀ {e : AExpr β} {j : Nat}, e.looseBound ≤ j + d →
    (openAt d j e).looseBound ≤ j
  | .bvar i, j, hl => by
    simp only [AExpr.looseBound] at hl
    simp only [openAt]
    split
    · simp only [looseBound]; omega
    · split
      · simp [looseBound]
      · exfalso; omega
  | .sort _, _, _ | .const _ _, _, _ | .natLit _ _, _, _ => by simp [openAt, looseBound]
  | .app f x, j, hl => by
    simp only [AExpr.looseBound, Nat.max_le] at hl
    simp only [openAt, looseBound, Nat.max_le]
    exact ⟨looseBound_openAt_le hl.1, looseBound_openAt_le hl.2⟩
  | .lam p x b, j, hl | .forallE p x b, j, hl => by
    simp only [AExpr.looseBound, Nat.max_le] at hl
    have hb := looseBound_openAt_le (d := d) (e := b) (j := j + 1) (by omega)
    simp only [openAt, looseBound, Nat.max_le]
    exact ⟨looseBound_openAt_le hl.1, by omega⟩
  | .letE t w b, j, hl => by
    simp only [AExpr.looseBound, Nat.max_le] at hl
    have hb := looseBound_openAt_le (d := d) (e := b) (j := j + 1) (by omega)
    simp only [openAt, looseBound, Nat.max_le]
    exact ⟨⟨looseBound_openAt_le hl.1.1, looseBound_openAt_le hl.1.2⟩, by omega⟩
  | .proj r i x, j, hl => by
    simp only [AExpr.looseBound] at hl
    simp only [openAt, looseBound]
    exact looseBound_openAt_le hl

/-- A closed form's loose indices are its own or its levels'. -/
theorem looseBound_closeAt_le {d : Nat} : ∀ {e : RExpr β} {j : Nat}, e.fvarBound ≤ d →
    (closeAt d j e).looseBound ≤ max e.looseBound (j + d)
  | .bvar i, j, _ => by
    simp only [closeAt_bvar, AExpr.looseBound, looseBound]
    omega
  | .fvar k, j, hf => by
    simp only [fvarBound] at hf
    simp only [closeAt_fvar, AExpr.looseBound, looseBound]
    omega
  | .sort _, _, _ | .const _ _, _, _ | .natLit _ _, _, _ => by simp [AExpr.looseBound, looseBound]
  | .app f x, j, hf => by
    simp only [fvarBound, Nat.max_le] at hf
    have := looseBound_closeAt_le (j := j) hf.1
    have := looseBound_closeAt_le (j := j) hf.2
    simp only [closeAt_app, AExpr.looseBound, looseBound]
    omega
  | .lam p x b, j, hf | .forallE p x b, j, hf => by
    simp only [fvarBound, Nat.max_le] at hf
    have := looseBound_closeAt_le (j := j) hf.1
    have := looseBound_closeAt_le (j := j + 1) hf.2
    simp only [closeAt_lam, closeAt_forallE, AExpr.looseBound, looseBound]
    omega
  | .letE t w b, j, hf => by
    simp only [fvarBound, Nat.max_le] at hf
    have := looseBound_closeAt_le (j := j) hf.1.1
    have := looseBound_closeAt_le (j := j) hf.1.2
    have := looseBound_closeAt_le (j := j + 1) hf.2
    simp only [closeAt_letE, AExpr.looseBound, looseBound]
    omega
  | .proj r i x, j, hf => by
    simp only [fvarBound] at hf
    have := looseBound_closeAt_le (j := j) hf
    simp only [closeAt_proj, AExpr.looseBound, looseBound]
    omega

/-- A term at a stack of depth `d` closes to a term scoped by the view. -/
theorem looseBound_close_le {d : Nat} {e : RExpr β} (hf : e.fvarBound ≤ d) (hl : e.looseBound = 0) :
    (close d e).looseBound ≤ d := by
  have := looseBound_closeAt_le (j := 0) hf
  show (closeAt d 0 e).looseBound ≤ d
  omega

end RExpr

/-! ## The view -/

namespace Stack

@[simp] theorem viewRev_nil : viewRev ([] : List (RExpr β)) = [] := rfl

@[simp] theorem viewRev_cons (A : RExpr β) (rest : List (RExpr β)) :
    viewRev (A :: rest) = Context.push (RExpr.close rest.length A) (viewRev rest) := rfl

@[simp] theorem view_empty : (Stack.empty : Stack β).view = [] := rfl

@[simp] theorem length_viewRev (l : List (RExpr β)) : (viewRev l).length = l.length := by
  induction l <;> simp_all [Context.push]

@[simp] theorem length_view (s : Stack β) : s.view.length = s.size := by
  simp [view, size]

/-- Pushing a variable pushes its type, read at the current depth, onto the
view. -/
theorem view_push (s : Stack β) (A : RExpr β) :
    (s.push A).view = s.view.push (RExpr.close s.size A) := by
  simp [view, size]

theorem WF.push {s : Stack β} {A : RExpr β} (hs : s.WF) (hf : A.fvarBound ≤ s.size)
    (hl : A.looseBound = 0) : (s.push A).WF := by
  simp only [WF, toList_push, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, WFRev, List.length_reverse, Array.length_toList]
  exact ⟨hf, hl, hs⟩

theorem WF.pop {s : Stack β} (hs : s.WF) : s.pop.WF := by
  simp only [WF, toList_pop, ← List.tail_reverse] at hs ⊢
  revert hs
  cases s.entries.toList.reverse with
  | nil => exact fun h => h
  | cons A rest => exact fun h => h.2.2

theorem WFRev.getElem? {l : List (RExpr β)} (hl : WFRev l) {i : Nat} {A : RExpr β}
    (hA : l[i]? = some A) : A.fvarBound + i + 1 ≤ l.length ∧ A.looseBound = 0 := by
  induction l generalizing i with
  | nil => simp at hA
  | cons B rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hA
      subst hA
      have := hl.1
      exact ⟨by simp only [List.length_cons]; omega, hl.2.1⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hA
      have := ih hl.2.2 hA
      exact ⟨by simp only [List.length_cons]; omega, this.2⟩

/-- Each view entry is its stack entry read at the full depth. -/
theorem getElem?_viewRev {l : List (RExpr β)} (hl : WFRev l) (i : Nat) :
    (viewRev l)[i]? = (l[i]?).map (RExpr.close l.length) := by
  induction l generalizing i with
  | nil => simp
  | cons A rest ih =>
    simp only [viewRev_cons, Context.push, List.length_cons]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq]
      rw [RExpr.close_lift (Nat.le_succ rest.length) hl.1 hl.2.1]
      simp
    | succ i =>
      simp only [List.getElem?_cons_succ, List.getElem?_map, ih hl.2.2 i, Option.map_map]
      cases hB : rest[i]? with
      | none => rfl
      | some B =>
        have hb := hl.2.2.getElem? hB
        simp only [Option.map_some, Function.comp_apply, Option.some.injEq]
        rw [RExpr.close_lift (Nat.le_succ rest.length) (by omega) hb.2]
        simp

/-- The variable at level `k` is the view's index `size - 1 - k`, and its
type there is its stack entry read at the full depth: the premise of
`TypingClaim.bvar` for `close s.size (fvar k)` (`RExpr.close_fvar`). -/
theorem getElem?_view {s : Stack β} (hs : s.WF) {k : Nat} {A : RExpr β}
    (hA : s.fvarType? k = some A) : s.view[s.size - 1 - k]? = some (RExpr.close s.size A) := by
  have hk : k < s.size := by
    simp only [fvarType?] at hA
    simp only [size]
    exact (Array.getElem?_eq_some_iff.mp hA).1
  simp only [view]
  rw [getElem?_viewRev hs, List.getElem?_reverse' (j := k) (by simp [size] at hk ⊢; omega)]
  simp only [fvarType?] at hA
  simp [Array.getElem?_toList, hA, size]

/-! ## Weakening along a stack

A claim at a stack holds at every stack extending it, read at the new depth:
the transport a weakening-only cache hit needs, once the hit has established
that the stack below the entry's depth is the one the entry was made at. -/

theorem viewRev_append_induction {P : Context β → Nat → Prop}
    (step : ∀ Γ n D, P Γ n → P (Γ.push D) (n + 1)) (xs : List (RExpr β)) :
    ∀ ys : List (RExpr β), P (viewRev xs) xs.length → P (viewRev (ys ++ xs)) (ys ++ xs).length
  | [], h => h
  | y :: ys, h => by
    simp only [List.cons_append, viewRev_cons, List.length_cons]
    exact step _ _ _ (viewRev_append_induction step xs ys h)

/-- A property preserved by every context push holds from a stack to any
stack extending it. -/
theorem extend_induction {P : Context β → Nat → Prop}
    (step : ∀ Γ n D, P Γ n → P (Γ.push D) (n + 1)) {s s' : Stack β}
    (hpre : s.entries.toList <+: s'.entries.toList) (h : P s.view s.size) : P s'.view s'.size := by
  obtain ⟨t, ht⟩ := hpre
  have hview : s'.view = viewRev (t.reverse ++ s.entries.toList.reverse) := by
    simp [view, ← ht]
  have hsize : s'.size = (t.reverse ++ s.entries.toList.reverse).length := by
    simp only [size, ← Array.length_toList, ← ht, List.length_append, List.length_reverse]
    omega
  rw [hview, hsize]
  exact viewRev_append_induction step _ _ (by simpa [view, size] using h)

end Stack

theorem formedClaim_weaken {entries : Environment β} {Γ : Context β} {e : AExpr β}
    (h : FormedClaim.{u,v} entries Γ e) (D : AExpr β) :
    FormedClaim.{u,v} entries (Γ.push D) (e.liftN 1) := by
  intro V _ constants realized levels env valid
  exact (wellDenoted_liftN _ _ _ _ _ _).mpr (h V constants realized levels _ valid.pop)

theorem convClaim_weaken {entries : Environment β} {Γ : Context β} {a b : AExpr β}
    (h : ConvClaim.{u,v} entries Γ a b) (D : AExpr β) :
    ConvClaim.{u,v} entries (Γ.push D) (a.liftN 1) (b.liftN 1) := by
  intro V _ constants realized levels env valid ha hb
  rw [wellDenoted_liftN] at ha hb
  simpa only [interp_liftN] using h V constants realized levels _ valid.pop ha hb

theorem reductionClaim_weaken {entries : Environment β} {Γ : Context β} {e e' : AExpr β}
    (h : ReductionClaim.{u,v} entries Γ e e') (D : AExpr β) :
    ReductionClaim.{u,v} entries (Γ.push D) (e.liftN 1) (e'.liftN 1) := by
  intro V _ constants realized levels env valid he
  rw [wellDenoted_liftN] at he
  obtain ⟨eq, hw⟩ := h V constants realized levels _ valid.pop he
  exact ⟨by simpa only [interp_liftN] using eq, (wellDenoted_liftN _ _ _ _ _ _).mpr hw⟩

namespace Stack

variable {entries : Environment β} {s s' : Stack β}

/-- One level deeper, a term whose levels are below `m ≤ n` closes to the
lift by one of its closed form at `n`: what `Context.push` weakening needs. -/
private theorem close_succ {m n : Nat} {e : RExpr β} (hn : m ≤ n) (hf : e.fvarBound ≤ m)
    (hl : e.looseBound = 0) : RExpr.close (n + 1) e = (RExpr.close n e).liftN 1 := by
  rw [RExpr.close_lift (Nat.le_succ n) (by omega) hl]
  simp

theorem typing_extend (hpre : s.entries.toList <+: s'.entries.toList) {e T : RExpr β}
    (he : e.fvarBound ≤ s.size) (hel : e.looseBound = 0)
    (hT : T.fvarBound ≤ s.size) (hTl : T.looseBound = 0)
    (h : TypingClaim.{u,v} entries s.view (RExpr.close s.size e) (RExpr.close s.size T)) :
    TypingClaim.{u,v} entries s'.view (RExpr.close s'.size e) (RExpr.close s'.size T) :=
  (extend_induction
    (P := fun Γ n => s.size ≤ n ∧
      TypingClaim.{u,v} entries Γ (RExpr.close n e) (RExpr.close n T))
    (fun _ _ D ⟨hn, hc⟩ => ⟨by omega, by
      rw [close_succ hn he hel, close_succ hn hT hTl]
      exact hc.weaken D⟩) hpre ⟨Nat.le_refl _, h⟩).2

theorem formed_extend (hpre : s.entries.toList <+: s'.entries.toList) {e : RExpr β}
    (he : e.fvarBound ≤ s.size) (hel : e.looseBound = 0)
    (h : FormedClaim.{u,v} entries s.view (RExpr.close s.size e)) :
    FormedClaim.{u,v} entries s'.view (RExpr.close s'.size e) :=
  (extend_induction
    (P := fun Γ n => s.size ≤ n ∧ FormedClaim.{u,v} entries Γ (RExpr.close n e))
    (fun _ _ D ⟨hn, hc⟩ => ⟨by omega, by
      rw [close_succ hn he hel]
      exact formedClaim_weaken hc D⟩) hpre ⟨Nat.le_refl _, h⟩).2

theorem conv_extend (hpre : s.entries.toList <+: s'.entries.toList) {a b : RExpr β}
    (ha : a.fvarBound ≤ s.size) (hal : a.looseBound = 0)
    (hb : b.fvarBound ≤ s.size) (hbl : b.looseBound = 0)
    (h : ConvClaim.{u,v} entries s.view (RExpr.close s.size a) (RExpr.close s.size b)) :
    ConvClaim.{u,v} entries s'.view (RExpr.close s'.size a) (RExpr.close s'.size b) :=
  (extend_induction
    (P := fun Γ n => s.size ≤ n ∧
      ConvClaim.{u,v} entries Γ (RExpr.close n a) (RExpr.close n b))
    (fun _ _ D ⟨hn, hc⟩ => ⟨by omega, by
      rw [close_succ hn ha hal, close_succ hn hb hbl]
      exact convClaim_weaken hc D⟩) hpre ⟨Nat.le_refl _, h⟩).2

theorem reduction_extend (hpre : s.entries.toList <+: s'.entries.toList) {e e' : RExpr β}
    (he : e.fvarBound ≤ s.size) (hel : e.looseBound = 0)
    (he' : e'.fvarBound ≤ s.size) (he'l : e'.looseBound = 0)
    (h : ReductionClaim.{u,v} entries s.view (RExpr.close s.size e) (RExpr.close s.size e')) :
    ReductionClaim.{u,v} entries s'.view (RExpr.close s'.size e) (RExpr.close s'.size e') :=
  (extend_induction
    (P := fun Γ n => s.size ≤ n ∧
      ReductionClaim.{u,v} entries Γ (RExpr.close n e) (RExpr.close n e'))
    (fun _ _ D ⟨hn, hc⟩ => ⟨by omega, by
      rw [close_succ hn he hel, close_succ hn he' he'l]
      exact reductionClaim_weaken hc D⟩) hpre ⟨Nat.le_refl _, h⟩).2

end Stack

end Ix.Kernel.Runtime
