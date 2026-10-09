import Ix.CompileCert.Canon.OccurrenceRelation
import Ix.CompileCert.Canon.GeneratedTables

namespace Ix.CompileCert.Canon
open Ix.Compile.Canon
open Ix (Name Expr)

/-- Equality of already related names is reflected in both directions.
This is the finite correspondence invariant, with no cached-name premise. -/
theorem NameCorrespondence.equal_iff {R : Lean.Name → Lean.Name → Prop}
    (names : NameCorrespondence R) {a a' b b' : Lean.Name}
    (left : R a a') (right : R b b') : a = b ↔ a' = b' := by
  constructor
  · intro same
    subst b
    exact names.functional left right
  · intro same
    subst b'
    exact names.injective left right

inductive TableResultRelated {α β : Type} (V : α → β → Prop) : Option α → Option β → Prop
  | none : TableResultRelated V none none
  | some {a b} : V a b → TableResultRelated V (some a) (some b)

theorem TableResultRelated.isSome {α β : Type} {V : α → β → Prop}
    {left : Option α} {right : Option β} (related : TableResultRelated V left right) :
    left.isSome = right.isSome := by
  cases related <;> rfl

/-- Ordered structural table entries, including their stored values.
The advisory cache is deliberately absent: actual lookup refines this list. -/
def NameTablesRelated {α β : Type} (R : Lean.Name → Lean.Name → Prop) (V : α → β → Prop)
    (left : NameTable α) (right : NameTable β) : Prop :=
  LRel (fun a b => R (keyName a.1) (keyName b.1) ∧ V a.2 b.2) left.entries right.entries

theorem nameLookup_related {α β : Type} {R : Lean.Name → Lean.Name → Prop}
    {V : α → β → Prop} (names : NameCorrespondence R)
    {left : List (Name × α)} {right : List (Name × β)}
    (entries : LRel (fun a b => R (keyName a.1) (keyName b.1) ∧ V a.2 b.2) left right)
    {query query' : Lean.Name} (queries : R query query') :
    TableResultRelated V (nameLookup left query) (nameLookup right query') := by
  induction entries with
  | nil => exact .none
  | cons head rest ih =>
    simp only [nameLookup]
    have equal := names.equal_iff head.1 queries
    split
    · rename_i found
      rw [ite_eq_left (equal.mp found)]
      exact .some head.2
    · rename_i absent
      rw [ite_eq_right (fun found => absent (equal.mpr found))]
      exact ih

theorem NameTablesRelated.lookup {α β : Type} {R : Lean.Name → Lean.Name → Prop}
    {V : α → β → Prop} {left : NameTable α} {right : NameTable β}
    (tables : NameTablesRelated R V left right) (names : NameCorrespondence R)
    {query query' : Name} (queries : R (keyName query) (keyName query')) :
    TableResultRelated V (left.get? query) (right.get? query') :=
  nameLookup_related names tables queries

theorem NameTablesRelated.contains {α β : Type} {R : Lean.Name → Lean.Name → Prop}
    {V : α → β → Prop} {left : NameTable α} {right : NameTable β}
    (tables : NameTablesRelated R V left right) (names : NameCorrespondence R)
    {query query' : Name} (queries : R (keyName query) (keyName query')) :
    left.contains query = right.contains query' :=
  (tables.lookup names queries).isSome

/-- A paired filter retains the exact order and multiplicity of surviving
entries. This covers the overwrite branch of the real NameTable insertion. -/
theorem LRel.filter_related {α β : Type} {R : α → β → Prop}
    {left : List α} {right : List β} (entries : LRel R left right)
    (p : α → Bool) (q : β → Bool) (predicates : ∀ a b, R a b → p a = q b) :
    LRel R (left.filter p) (right.filter q) := by
  induction entries with
  | nil => exact .nil
  | @cons a b as bs head rest ih =>
    cases selected : q b with
    | false =>
      simpa [List.filter_cons,predicates a b head,selected] using ih
    | true =>
      simpa [List.filter_cons,predicates a b head,selected] using LRel.cons head ih

/-- Both first insertion and overwriting an existing structural key retain
the complete ordered table correspondence. Hash buckets may differ freely. -/
theorem NameTablesRelated.insert {α β : Type} {R : Lean.Name → Lean.Name → Prop}
    {V : α → β → Prop} {left : NameTable α} {right : NameTable β}
    (tables : NameTablesRelated R V left right) (names : NameCorrespondence R)
    (name name' : Name) (keys : R (keyName name) (keyName name'))
    (value : α) (value' : β) (values : V value value') :
    NameTablesRelated R V (left.insert name value) (right.insert name' value') := by
  have lookups := tables.lookup names keys
  cases hl : left.get? name <;> cases hr : right.get? name' <;>
    rw [hl,hr] at lookups
  · have added : LRel (fun a b => R (keyName a.1) (keyName b.1) ∧ V a.2 b.2)
        ((name,value) :: left.entries) ((name',value') :: right.entries) :=
      .cons ⟨keys,values⟩ tables
    simpa [NameTablesRelated,NameTable.insert,hl,hr] using added
  · cases lookups
  · cases lookups
  · have filtered : LRel (fun a b => R (keyName a.1) (keyName b.1) ∧ V a.2 b.2)
        (left.entries.filter fun a => decide (keyName a.1 ≠ keyName name))
        (right.entries.filter fun b => decide (keyName b.1 ≠ keyName name')) := by
      apply LRel.filter_related tables
      intro a b related
      have equal := names.equal_iff related.1 keys
      simp only [ne_eq, equal]
    have added : LRel (fun a b => R (keyName a.1) (keyName b.1) ∧ V a.2 b.2)
        ((name,value) :: left.entries.filter fun a => decide (keyName a.1 ≠ keyName name))
        ((name',value') :: right.entries.filter fun b => decide (keyName b.1 ≠ keyName name')) :=
      .cons ⟨keys,values⟩ filtered
    simpa [NameTablesRelated,NameTable.insert,hl,hr] using added

theorem NameTablesRelated.empty {α β : Type} (R : Lean.Name → Lean.Name → Prop)
    (V : α → β → Prop) : NameTablesRelated R V ({} : NameTable α) ({} : NameTable β) :=
  .nil

/-- Existing entries remain related when discovery extends the finite
reference correspondence; value relations can grow with it. -/
theorem NameTablesRelated.mono {α β : Type} {R S : Lean.Name → Lean.Name → Prop}
    {V W : α → β → Prop} {left : NameTable α} {right : NameTable β}
    (tables : NameTablesRelated R V left right)
    (references : ∀ a b, R a b → S a b) (values : ∀ a b, V a b → W a b) :
    NameTablesRelated S W left right := by
  have lift {xs : List (Name × α)} {ys : List (Name × β)}
      (entries : LRel (fun a b => R (keyName a.1) (keyName b.1) ∧ V a.2 b.2) xs ys) :
      LRel (fun a b => S (keyName a.1) (keyName b.1) ∧ W a.2 b.2) xs ys := by
    induction entries with
    | nil => exact .nil
    | cons head rest ih => exact .cons ⟨references _ _ head.1,values _ _ head.2⟩ ih
  exact lift tables

/-- The predicate-based walker that production expansion actually calls.
Binder annotations and expression caches do not affect this decision. -/
theorem ERen.mentionsName {σ : Name → Name} {S : Name → Prop} {e e' : Expr}
    (expressions : ERen σ S e e') (left right : Name → Bool)
    (predicates : ∀ n, S n → left n = right (σ n)) :
    Ix.Compile.Canon.mentionsName left e = Ix.Compile.Canon.mentionsName right e' := by
  induction expressions <;> simp only [Ix.Compile.Canon.mentionsName, *]

/-- Exact production typeNames membership agrees on renamed source terms
once the enclosing state supplies its finite table/name correspondence. -/
theorem ERen.mentionsNameTables {σ : Name → Name} {S : Name → Prop}
    {R : Lean.Name → Lean.Name → Prop} {left right : NameSet}
    (tables : NameTablesRelated R (fun (_ _ : Unit) => True) left right)
    (names : NameCorrespondence R)
    (references : ∀ n, S n → R (keyName n) (keyName (σ n)))
    {e e' : Expr} (expressions : ERen σ S e e') :
    Ix.Compile.Canon.mentionsName left.contains e = Ix.Compile.Canon.mentionsName right.contains e' := by
  apply expressions.mentionsName
  intro n member
  exact tables.contains names (references n member)

end Ix.CompileCert.Canon

