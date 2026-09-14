/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Level
import Ix.Theory.Rename

/-!
# Annotated readings of exact anonymous expressions

Every binder occurrence carries its own zero condition. These are structural
readings, not evidence of typing: the semantic checker must establish that
each condition describes the inferred codomain sort in the current context.

The operations below preserve erasure exactly, including block/member and
constructor positions, level arguments, projection heads, and literals.
-/

namespace Ix.Theory.Model

open Certified

inductive AExpr (β : Type u) where
  | bvar (index : Nat)
  | sort (level : VLevel)
  | const (ref : ConstRef β) (levels : List VLevel)
  | app (fn arg : AExpr β)
  | lam (condition : PropWhen) (domain body : AExpr β)
  | forallE (condition : PropWhen) (domain body : AExpr β)
  | proj (ref : ConstRef β) (field : Nat) (major : AExpr β)
  | natLit (value : Nat)
deriving DecidableEq

namespace AExpr

def erase : AExpr β → VExpr β
  | .bvar i => .bvar i
  | .sort l => .sort l
  | .const r ls => .const r ls
  | .app f a => .app f.erase a.erase
  | .lam _ a b => .lam a.erase b.erase
  | .forallE _ a b => .forallE a.erase b.erase
  | .proj r i e => .proj r i e.erase
  | .natLit v => .natLit v

theorem eq_const_of_erase_eq {e : AExpr β} {r : ConstRef β} {ls : List VLevel}
    (h : e.erase = .const r ls) : e = .const r ls := by
  cases e <;> simp_all [erase]

/-- Scope of syntax and annotations, independently of semantic validity. -/
def Scope (universes depth : Nat) : AExpr β → Prop
  | .bvar i => i < depth
  | .sort l => l.WF universes
  | .const _ ls => ∀ l ∈ ls, l.WF universes
  | .app f a => f.Scope universes depth ∧ a.Scope universes depth
  | .lam p a b | .forallE p a b =>
    p.WF universes ∧ a.Scope universes depth ∧ b.Scope universes (depth + 1)
  | .proj _ _ e => e.Scope universes depth
  | .natLit _ => True

instance decidableScope {n k : Nat} : ∀ {e : AExpr β}, Decidable (e.Scope n k)
  | .bvar i => inferInstanceAs (Decidable (i < k))
  | .sort l => VLevel.decidable_WF (l := l)
  | .const _ ls => inferInstanceAs (Decidable (∀ l ∈ ls, VLevel.WF n l))
  | .app f a => @instDecidableAnd _ _ (decidableScope (e := f)) (decidableScope (e := a))
  | .lam p A b | .forallE p A b =>
    @instDecidableAnd _ _ (inferInstanceAs (Decidable (p.WF n)))
      (@instDecidableAnd _ _ (decidableScope (e := A)) (decidableScope (e := b)))
  | .proj _ _ e => decidableScope (e := e)
  | .natLit _ => instDecidableTrue

theorem Scope.erase {u k : Nat} {e : AExpr β} (h : e.Scope u k) :
    e.erase.LevelWF u ∧ e.erase.ClosedN k := by
  induction e generalizing k with
  | bvar i => exact ⟨trivial, h⟩
  | sort l => exact ⟨h, trivial⟩
  | const r ls => exact ⟨h, trivial⟩
  | app f a hf ha =>
    exact ⟨⟨(hf h.1).1, (ha h.2).1⟩, ⟨(hf h.1).2, (ha h.2).2⟩⟩
  | lam p a b ha hb | forallE p a b ha hb =>
    exact ⟨⟨(ha h.2.1).1, (hb h.2.2).1⟩, ⟨(ha h.2.1).2, (hb h.2.2).2⟩⟩
  | proj r i e ih => exact ih h
  | natLit v => exact ⟨trivial, trivial⟩

def liftN (count : Nat) : AExpr β → (cutoff : Nat := 0) → AExpr β
  | .bvar i, k => .bvar (liftVar count i k)
  | .sort l, _ => .sort l
  | .const r ls, _ => .const r ls
  | .app f a, k => .app (f.liftN count k) (a.liftN count k)
  | .lam p a b, k => .lam p (a.liftN count k) (b.liftN count (k + 1))
  | .forallE p a b, k => .forallE p (a.liftN count k) (b.liftN count (k + 1))
  | .proj r i e, k => .proj r i (e.liftN count k)
  | .natLit v, _ => .natLit v

@[simp] theorem erase_liftN (e : AExpr β) (n k : Nat) :
    (e.liftN n k).erase = e.erase.liftN n k := by
  induction e generalizing k <;> simp_all [liftN, erase, VExpr.liftN]

def instVar (i : Nat) (a : AExpr β) (k : Nat) : AExpr β :=
  if i < k then .bvar i else if i = k then a.liftN k else .bvar (i - 1)

def inst : AExpr β → AExpr β → (cutoff : Nat := 0) → AExpr β
  | .bvar i, a, k => instVar i a k
  | .sort l, _, _ => .sort l
  | .const r ls, _, _ => .const r ls
  | .app f a, e, k => .app (f.inst e k) (a.inst e k)
  | .lam p a b, e, k => .lam p (a.inst e k) (b.inst e (k + 1))
  | .forallE p a b, e, k => .forallE p (a.inst e k) (b.inst e (k + 1))
  | .proj r i e, a, k => .proj r i (e.inst a k)
  | .natLit v, _, _ => .natLit v

@[simp] theorem erase_inst (e a : AExpr β) (k : Nat) :
    (e.inst a k).erase = e.erase.inst a.erase k := by
  induction e generalizing k with
  | bvar i =>
    by_cases hi : i < k
    · simp [inst, erase, VExpr.inst, instVar, VExpr.instVar, hi]
    · by_cases he : i = k <;>
        simp [inst, erase, VExpr.inst, instVar, VExpr.instVar, hi, he]
  | _ => simp_all [inst, erase, VExpr.inst]

def instL (levels : List VLevel) : AExpr β → AExpr β
  | .bvar i => .bvar i
  | .sort l => .sort (l.inst levels)
  | .const r ls => .const r (ls.map (VLevel.inst levels))
  | .app f a => .app (f.instL levels) (a.instL levels)
  | .lam p a b => .lam (instCondition levels p) (a.instL levels) (b.instL levels)
  | .forallE p a b => .forallE (instCondition levels p) (a.instL levels) (b.instL levels)
  | .proj r i e => .proj r i (e.instL levels)
  | .natLit v => .natLit v

@[simp] theorem erase_instL (e : AExpr β) (ls : List VLevel) :
    (e.instL ls).erase = e.erase.instL ls := by
  induction e <;> simp_all [instL, erase, VExpr.instL]

theorem instL_instL (e : AExpr β) (ls ls' : List VLevel) :
    (e.instL ls).instL ls' = e.instL (ls.map (VLevel.inst ls')) := by
  induction e <;>
    simp_all [instL, VLevel.inst_inst, instCondition_comp, List.map_map, Function.comp_def]

def rename (mapping : β → γ) : AExpr β → AExpr γ
  | .bvar i => .bvar i
  | .sort l => .sort l
  | .const r ls => .const (r.rename mapping) ls
  | .app f a => .app (f.rename mapping) (a.rename mapping)
  | .lam p a b => .lam p (a.rename mapping) (b.rename mapping)
  | .forallE p a b => .forallE p (a.rename mapping) (b.rename mapping)
  | .proj r i e => .proj (r.rename mapping) i (e.rename mapping)
  | .natLit v => .natLit v

@[simp] theorem erase_rename (e : AExpr β) (mapping : β → γ) :
    (e.rename mapping).erase = e.erase.rename mapping := by
  induction e <;> simp_all [rename, erase, VExpr.rename]

end AExpr

/-- Untrusted annotations are indexed by occurrence, not a shared node ID.
Leaf syntax comes from the source expression and cannot be changed here. -/
inductive AnnotationTree where
  | leaf
  | app (fn arg : AnnotationTree)
  | lam (condition : Option (List Nat)) (domain body : AnnotationTree)
  | forallE (condition : Option (List Nat)) (domain body : AnnotationTree)
  | proj (major : AnnotationTree)
deriving DecidableEq, Repr

private def readCondition? (n : Nat) (raw : Option (List Nat)) :
    Option { p : PropWhen // p.toRaw = raw ∧ p.WF n } :=
  match h : PropWhen.fromRaw? n raw with
  | none => none
  | some p => some ⟨p, PropWhen.fromRaw?_sound h⟩

universe u
variable {β : Type u}

/-- Exact, scoped reading produced by the structural validator. -/
abbrev Reading (n k : Nat) (source : VExpr β) :=
  { e : AExpr β // e.erase = source ∧ e.Scope n k }

/-- Check shape, canonical conditions, and every term/universe index against
the exact input occurrence. Typing must subsequently validate binder meaning.
Proof fields are erased at runtime; every data check below is executable. -/
def readAnnotations? (n k : Nat) (source : VExpr β) (tree : AnnotationTree) :
    Option (Reading n k source) :=
  match source, tree with
  | .bvar i, .leaf => if h : i < k then some ⟨.bvar i, rfl, h⟩ else none
  | .sort l, .leaf => if h : l.WF n then some ⟨.sort l, rfl, h⟩ else none
  | .const r ls, .leaf =>
    if h : ∀ l ∈ ls, l.WF n then some ⟨.const r ls, rfl, h⟩ else none
  | .app f a, .app tf ta => do
    let f' ← readAnnotations? n k f tf
    let a' ← readAnnotations? n k a ta
    return ⟨.app f'.val a'.val,
      by simp [AExpr.erase, f'.property.1, a'.property.1],
      f'.property.2, a'.property.2⟩
  | .lam a b, .lam raw ta tb =>
    match readCondition? n raw with
    | none => none
    | some p => do
      let a' ← readAnnotations? n k a ta
      let b' ← readAnnotations? n (k + 1) b tb
      return ⟨.lam p.val a'.val b'.val,
        by simp [AExpr.erase, a'.property.1, b'.property.1],
        p.property.2, a'.property.2, b'.property.2⟩
  | .forallE a b, .forallE raw ta tb =>
    match readCondition? n raw with
    | none => none
    | some p => do
      let a' ← readAnnotations? n k a ta
      let b' ← readAnnotations? n (k + 1) b tb
      return ⟨.forallE p.val a'.val b'.val,
        by simp [AExpr.erase, a'.property.1, b'.property.1],
        p.property.2, a'.property.2, b'.property.2⟩
  | .proj r i e, .proj te => do
    let e' ← readAnnotations? n k e te
    return ⟨.proj r i e'.val, by simp [AExpr.erase, e'.property.1], e'.property.2⟩
  | .natLit v, .leaf => some ⟨.natLit v, rfl, trivial⟩
  | _, _ => none

end Ix.Theory.Model
