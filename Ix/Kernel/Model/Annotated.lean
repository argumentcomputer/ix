/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Model/Annotated.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: `natLit` carries the reference of its natural-number family, on raw and
annotated syntax alike, with its cases.
`letE` added (2026-09-17): the let-binding constructor, interpreted by
substitution, with its cases in every definition and proof here.
B2: two `@[computed_field]`s, `looseBound` and `structHash`, derived per node
at construction; logically ordinary structural functions. The kernel's fast
substitutions and equality read them (`Ix/Kernel/Model/FastOps.lean`).
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Level
import Ix.Kernel.Rename

/-!
# Annotated readings of exact anonymous expressions

Every binder occurrence carries its own zero condition. These are structural
readings, not evidence of typing: the semantic checker must establish that
each condition describes the inferred codomain sort in the current context.

The operations below preserve erasure exactly, including block/member and
constructor positions, level arguments, projection heads, and literals.
-/

namespace Ix.Kernel.Model

open Certified

inductive AExpr (β : Type u) where
  | bvar (index : Nat)
  | sort (level : VLevel)
  | const (ref : ConstRef β) (levels : List VLevel)
  | app (fn arg : AExpr β)
  | lam (condition : PropWhen) (domain body : AExpr β)
  | forallE (condition : PropWhen) (domain body : AExpr β)
  | letE (type value body : AExpr β)
  | proj (ref : ConstRef β) (field : Nat) (major : AExpr β)
  | natLit (family : ConstRef β) (value : Nat)
with
  /-- One more than the largest loose de Bruijn index; `0` when closed. -/
  @[computed_field] looseBound : (β : Type u) → AExpr β → Nat
    | _, .bvar i => i + 1
    | _, .sort _ => 0
    | _, .const _ _ => 0
    | _, .app f a => max f.looseBound a.looseBound
    | _, .lam _ a b => max a.looseBound (b.looseBound - 1)
    | _, .forallE _ a b => max a.looseBound (b.looseBound - 1)
    | _, .letE t v b => max (max t.looseBound v.looseBound) (b.looseBound - 1)
    | _, .proj _ _ e => e.looseBound
    | _, .natLit _ _ => 0
  /-- A structural hash: node kinds, indices, positions, and each level's head
  (not block keys, not whole levels: a level's hash would cost its size at
  every node). Equal terms have equal hashes. -/
  @[computed_field] structHash : (β : Type u) → AExpr β → UInt64
    | _, .bvar i => mixHash 11 (hash i)
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

namespace AExpr

def erase : AExpr β → VExpr β
  | .bvar i => .bvar i
  | .sort l => .sort l
  | .const r ls => .const r ls
  | .app f a => .app f.erase a.erase
  | .lam _ a b => .lam a.erase b.erase
  | .forallE _ a b => .forallE a.erase b.erase
  | .letE t v b => .letE t.erase v.erase b.erase
  | .proj r i e => .proj r i e.erase
  | .natLit r v => .natLit r v

/-- Every raw expression has a structural annotation. This says nothing
about the validity of the chosen binder conditions. -/
theorem erase_surjective : Function.Surjective (erase : AExpr β → VExpr β) := by
  intro term
  induction term with
  | bvar index => exact ⟨.bvar index, rfl⟩
  | sort level => exact ⟨.sort level, rfl⟩
  | const ref levels => exact ⟨.const ref levels, rfl⟩
  | natLit family value => exact ⟨.natLit family value, rfl⟩
  | app fn arg ihFn ihArg =>
      obtain ⟨f, rfl⟩ := ihFn
      obtain ⟨a, rfl⟩ := ihArg
      exact ⟨.app f a, rfl⟩
  | lam domain body ihDomain ihBody | forallE domain body ihDomain ihBody =>
      obtain ⟨A, rfl⟩ := ihDomain
      obtain ⟨b, rfl⟩ := ihBody
      first | exact ⟨.lam .always A b, rfl⟩ | exact ⟨.forallE .always A b, rfl⟩
  | letE type value body ihType ihValue ihBody =>
      obtain ⟨t, rfl⟩ := ihType
      obtain ⟨v, rfl⟩ := ihValue
      obtain ⟨b, rfl⟩ := ihBody
      exact ⟨.letE t v b, rfl⟩
  | proj ref field major ih =>
      obtain ⟨value, rfl⟩ := ih
      exact ⟨.proj ref field value, rfl⟩

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
  | .letE t v b => t.Scope universes depth ∧ v.Scope universes depth ∧ b.Scope universes (depth + 1)
  | .proj _ _ e => e.Scope universes depth
  | .natLit _ _ => True

instance decidableScope {n k : Nat} : ∀ {e : AExpr β}, Decidable (e.Scope n k)
  | .bvar i => inferInstanceAs (Decidable (i < k))
  | .sort l => VLevel.decidable_WF (l := l)
  | .const _ ls => inferInstanceAs (Decidable (∀ l ∈ ls, VLevel.WF n l))
  | .app f a => @instDecidableAnd _ _ (decidableScope (e := f)) (decidableScope (e := a))
  | .lam p A b | .forallE p A b =>
    @instDecidableAnd _ _ (inferInstanceAs (Decidable (p.WF n)))
      (@instDecidableAnd _ _ (decidableScope (e := A)) (decidableScope (e := b)))
  | .letE t v b => @instDecidableAnd _ _ (decidableScope (e := t))
      (@instDecidableAnd _ _ (decidableScope (e := v)) (decidableScope (e := b)))
  | .proj _ _ e => decidableScope (e := e)
  | .natLit _ _ => instDecidableTrue

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
  | letE t v b ht hv hb =>
    exact ⟨⟨(ht h.1).1, (hv h.2.1).1, (hb h.2.2).1⟩, ⟨(ht h.1).2, (hv h.2.1).2, (hb h.2.2).2⟩⟩
  | natLit _ v => exact ⟨trivial, trivial⟩

def liftN (count : Nat) : AExpr β → (cutoff : Nat := 0) → AExpr β
  | .bvar i, k => .bvar (liftVar count i k)
  | .sort l, _ => .sort l
  | .const r ls, _ => .const r ls
  | .app f a, k => .app (f.liftN count k) (a.liftN count k)
  | .lam p a b, k => .lam p (a.liftN count k) (b.liftN count (k + 1))
  | .forallE p a b, k => .forallE p (a.liftN count k) (b.liftN count (k + 1))
  | .letE t v b, k => .letE (t.liftN count k) (v.liftN count k) (b.liftN count (k + 1))
  | .proj r i e, k => .proj r i (e.liftN count k)
  | .natLit r v, _ => .natLit r v

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
  | .letE t v b, e, k => .letE (t.inst e k) (v.inst e k) (b.inst e (k + 1))
  | .proj r i e, a, k => .proj r i (e.inst a k)
  | .natLit r v, _, _ => .natLit r v

/-! ### Substitution that skips closed subterms (B2)

`looseBound` bounds the loose indices, so a subterm bounded by the cutoff is
left unchanged: the runtime substitutions stop there. The compiler uses them
in place of `liftN` and `inst` by the proved equations (`@[csimp]`). -/

theorem liftN_of_looseBound_le {n : Nat} : ∀ {e : AExpr β} {k : Nat},
    e.looseBound ≤ k → e.liftN n k = e
  | .bvar i, k, h => by
    simp only [looseBound] at h
    simp [liftN, liftVar, show i < k by omega]
  | .sort _, _, _ | .const _ _, _, _ | .natLit _ _, _, _ => rfl
  | .app f a, k, h => by
    simp only [looseBound, Nat.max_le] at h
    simp [liftN, liftN_of_looseBound_le h.1, liftN_of_looseBound_le h.2]
  | .lam p a b, k, h | .forallE p a b, k, h => by
    simp only [looseBound, Nat.max_le] at h
    simp [liftN, liftN_of_looseBound_le h.1, liftN_of_looseBound_le (e := b) (k := k + 1) (by omega)]
  | .letE t v b, k, h => by
    simp only [looseBound, Nat.max_le] at h
    simp [liftN, liftN_of_looseBound_le h.1.1, liftN_of_looseBound_le h.1.2,
      liftN_of_looseBound_le (e := b) (k := k + 1) (by omega)]
  | .proj r i e, k, h => by
    simp only [looseBound] at h
    simp [liftN, liftN_of_looseBound_le h]

/-- `liftN`, stopping at subterms bounded by the cutoff. -/
def liftNFast (count : Nat) (e : AExpr β) (cutoff : Nat := 0) : AExpr β :=
  if e.looseBound ≤ cutoff then e else
  match e with
  | .bvar i => .bvar (liftVar count i cutoff)
  | .sort l => .sort l
  | .const r ls => .const r ls
  | .app f a => .app (liftNFast count f cutoff) (liftNFast count a cutoff)
  | .lam p a b => .lam p (liftNFast count a cutoff) (liftNFast count b (cutoff + 1))
  | .forallE p a b => .forallE p (liftNFast count a cutoff) (liftNFast count b (cutoff + 1))
  | .letE t v b =>
    .letE (liftNFast count t cutoff) (liftNFast count v cutoff) (liftNFast count b (cutoff + 1))
  | .proj r i e => .proj r i (liftNFast count e cutoff)
  | .natLit r v => .natLit r v

theorem liftNFast_eq (count : Nat) : ∀ (e : AExpr β) (cutoff : Nat),
    liftNFast count e cutoff = liftN count e cutoff := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | natLit _ _ =>
    intro k; unfold liftNFast; split
    · exact (liftN_of_looseBound_le ‹_›).symm
    · rfl
  | app f a hf ha =>
    intro k; unfold liftNFast; split
    · exact (liftN_of_looseBound_le ‹_›).symm
    · simp [liftN, hf, ha]
  | lam p a b ha hb | forallE p a b ha hb =>
    intro k; unfold liftNFast; split
    · exact (liftN_of_looseBound_le ‹_›).symm
    · simp [liftN, ha, hb]
  | letE t v b ht hv hb =>
    intro k; unfold liftNFast; split
    · exact (liftN_of_looseBound_le ‹_›).symm
    · simp [liftN, ht, hv, hb]
  | proj r i e he =>
    intro k; unfold liftNFast; split
    · exact (liftN_of_looseBound_le ‹_›).symm
    · simp [liftN, he]

@[csimp] theorem liftN_eq_liftNFast : @liftN = @liftNFast := by
  funext β n e k; exact (liftNFast_eq n e k).symm

theorem inst_of_looseBound_le {a : AExpr β} : ∀ {e : AExpr β} {k : Nat},
    e.looseBound ≤ k → e.inst a k = e
  | .bvar i, k, h => by
    simp only [looseBound] at h
    simp [inst, instVar, show i < k by omega]
  | .sort _, _, _ | .const _ _, _, _ | .natLit _ _, _, _ => rfl
  | .app f x, k, h => by
    simp only [looseBound, Nat.max_le] at h
    simp [inst, inst_of_looseBound_le h.1, inst_of_looseBound_le h.2]
  | .lam p d b, k, h | .forallE p d b, k, h => by
    simp only [looseBound, Nat.max_le] at h
    simp [inst, inst_of_looseBound_le h.1, inst_of_looseBound_le (e := b) (k := k + 1) (by omega)]
  | .letE t v b, k, h => by
    simp only [looseBound, Nat.max_le] at h
    simp [inst, inst_of_looseBound_le h.1.1, inst_of_looseBound_le h.1.2,
      inst_of_looseBound_le (e := b) (k := k + 1) (by omega)]
  | .proj r i x, k, h => by
    simp only [looseBound] at h
    simp [inst, inst_of_looseBound_le h]

/-- `inst`, stopping at subterms bounded by the cutoff. -/
def instFast (e a : AExpr β) (cutoff : Nat := 0) : AExpr β :=
  if e.looseBound ≤ cutoff then e else
  match e with
  | .bvar i => instVar i a cutoff
  | .sort l => .sort l
  | .const r ls => .const r ls
  | .app f x => .app (instFast f a cutoff) (instFast x a cutoff)
  | .lam p d b => .lam p (instFast d a cutoff) (instFast b a (cutoff + 1))
  | .forallE p d b => .forallE p (instFast d a cutoff) (instFast b a (cutoff + 1))
  | .letE t v b => .letE (instFast t a cutoff) (instFast v a cutoff) (instFast b a (cutoff + 1))
  | .proj r i x => .proj r i (instFast x a cutoff)
  | .natLit r v => .natLit r v

theorem instFast_eq (a : AExpr β) : ∀ (e : AExpr β) (cutoff : Nat),
    instFast e a cutoff = inst e a cutoff := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | natLit _ _ =>
    intro k; unfold instFast; split
    · exact (inst_of_looseBound_le ‹_›).symm
    · rfl
  | app f x hf hx =>
    intro k; unfold instFast; split
    · exact (inst_of_looseBound_le ‹_›).symm
    · simp [inst, hf, hx]
  | lam p d b hd hb | forallE p d b hd hb =>
    intro k; unfold instFast; split
    · exact (inst_of_looseBound_le ‹_›).symm
    · simp [inst, hd, hb]
  | letE t v b ht hv hb =>
    intro k; unfold instFast; split
    · exact (inst_of_looseBound_le ‹_›).symm
    · simp [inst, ht, hv, hb]
  | proj r i x hx =>
    intro k; unfold instFast; split
    · exact (inst_of_looseBound_le ‹_›).symm
    · simp [inst, hx]

@[csimp] theorem inst_eq_instFast : @inst = @instFast := by
  funext β e a k; exact (instFast_eq a e k).symm

/-- Equality decided pointer-first: identical objects are equal, different
structural hashes are unequal, and otherwise the constructors are compared
argument by argument, each argument the same way. -/
def decEqFast [DecidableEq β] (a b : AExpr β) : Decidable (a = b) :=
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
      | a, b => instDecidableEqAExpr a b
    else isFalse fun e => hh (e ▸ rfl)

/-- The kernel's equality on terms is `decEqFast`. -/
instance (priority := high) [DecidableEq β] : DecidableEq (AExpr β) := decEqFast

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
  | .letE t v b => .letE (t.instL levels) (v.instL levels) (b.instL levels)
  | .proj r i e => .proj r i (e.instL levels)
  | .natLit r v => .natLit r v

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
  | .letE t v b => .letE (t.rename mapping) (v.rename mapping) (b.rename mapping)
  | .proj r i e => .proj (r.rename mapping) i (e.rename mapping)
  | .natLit r v => .natLit (r.rename mapping) v

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
  | letE (type value body : AnnotationTree)
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
  | .letE t v b, .letE tt tv tb => do
    let t' ← readAnnotations? n k t tt
    let v' ← readAnnotations? n k v tv
    let b' ← readAnnotations? n (k + 1) b tb
    return ⟨.letE t'.val v'.val b'.val,
      by simp [AExpr.erase, t'.property.1, v'.property.1, b'.property.1],
      t'.property.2, v'.property.2, b'.property.2⟩
  | .natLit r v, .leaf => some ⟨.natLit r v, rfl, trivial⟩
  | _, _ => none

end Ix.Kernel.Model
