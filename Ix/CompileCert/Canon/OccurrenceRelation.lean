import Ix.CompileCert.Canon.OccurrenceRename
import Ix.CompileCert.Canon.Rename

namespace Ix.CompileCert.Canon
open Ix.Compile.Canon

/-- A partial correspondence can grow as fresh auxiliaries are discovered.
Only related names need uniqueness; no globally injective extension or
cached-hash agreement is required. The queue invariant establishes this
property for the finite actual correspondence. -/
structure NameCorrespondence (R : Lean.Name → Lean.Name → Prop) : Prop where
  functional : ∀ {a b c}, R a b → R a c → b = c
  injective : ∀ {a b c}, R a c → R b c → a = b

def extendCorrespondence (R : Lean.Name → Lean.Name → Prop)
    (left right : Lean.Name) (a b : Lean.Name) : Prop :=
  R a b ∨ (a = left ∧ b = right)

/-- Add the next paired allocation using freshness derived from each actual
allocation forest and its protected source closure. These two freshness
arguments are internal induction hypotheses, not final caller premises. -/
theorem NameCorrespondence.extend {R : Lean.Name → Lean.Name → Prop}
    (correspondence : NameCorrespondence R) (left right : Lean.Name)
    (freshLeft : ∀ b, ¬ R left b) (freshRight : ∀ a, ¬ R a right) :
    NameCorrespondence (extendCorrespondence R left right) := by
  constructor
  · intro a b c hab hac
    rcases hab with old | ⟨rfl,rfl⟩
    · rcases hac with other | ⟨rfl,rfl⟩
      · exact correspondence.functional old other
      · exact (freshLeft _ old).elim
    · rcases hac with old | ⟨_,rfl⟩
      · exact (freshLeft _ old).elim
      · rfl
  · intro a b c hac hbc
    rcases hac with old | ⟨rfl,rfl⟩
    · rcases hbc with other | ⟨rfl,rfl⟩
      · exact correspondence.injective old other
      · exact (freshRight _ old).elim
    · rcases hbc with old | ⟨rfl,_⟩
      · exact (freshRight _ old).elim
      · rfl

inductive ReferenceRelated (R : Lean.Name → Lean.Name → Prop) :
    OccurrenceRef → OccurrenceRef → Prop
  | named {a b} : R a b → ReferenceRelated R (.named a) (.named b)
  | external (a : Address) : ReferenceRelated R (.external a) (.external a)

theorem ReferenceRelated.functional {R : Lean.Name → Lean.Name → Prop}
    (correspondence : NameCorrespondence R) {a b c : OccurrenceRef}
    (hab : ReferenceRelated R a b) (hac : ReferenceRelated R a c) : b = c := by
  cases hab <;> cases hac
  · congr 1
    apply correspondence.functional <;> assumption
  · rfl

theorem ReferenceRelated.injective {R : Lean.Name → Lean.Name → Prop}
    (correspondence : NameCorrespondence R) {a b c : OccurrenceRef}
    (hac : ReferenceRelated R a c) (hbc : ReferenceRelated R b c) : a = b := by
  cases hac <;> cases hbc
  · congr 1
    apply correspondence.injective <;> assumption
  · rfl

/-- Relational form of structural key renaming. Canonical erasures are
already present in these keys; external addresses retain their separate tag. -/
inductive KeyRelated (R : Lean.Name → Lean.Name → Prop) :
    OccurrenceKey → OccurrenceKey → Prop
  | bvar (i : Nat) : KeyRelated R (.bvar i) (.bvar i)
  | fvar (n : Lean.Name) : KeyRelated R (.fvar n) (.fvar n)
  | mvar (n : Lean.Name) : KeyRelated R (.mvar n) (.mvar n)
  | sort (u : KeyLevel) : KeyRelated R (.sort u) (.sort u)
  | const {a b} (us : List KeyLevel) : ReferenceRelated R a b →
      KeyRelated R (.const a us) (.const b us)
  | app {f f' a a'} : KeyRelated R f f' → KeyRelated R a a' →
      KeyRelated R (.app f a) (.app f' a')
  | lam (n : Lean.Name) (bi : UInt8) {t t' b b'} : KeyRelated R t t' → KeyRelated R b b' →
      KeyRelated R (.lam n t b bi) (.lam n t' b' bi)
  | forallE (n : Lean.Name) (bi : UInt8) {t t' b b'} : KeyRelated R t t' → KeyRelated R b b' →
      KeyRelated R (.forallE n t b bi) (.forallE n t' b' bi)
  | letE (n : Lean.Name) (nd : Bool) {t t' v v' b b'} :
      KeyRelated R t t' → KeyRelated R v v' → KeyRelated R b b' →
      KeyRelated R (.letE n t v b nd) (.letE n t' v' b' nd)
  | natLit (n : Nat) : KeyRelated R (.natLit n) (.natLit n)
  | strLit (s : String) : KeyRelated R (.strLit s) (.strLit s)
  | mdata (md : List (Lean.Name × KeyData)) {b b'} : KeyRelated R b b' →
      KeyRelated R (.mdata md b) (.mdata md b')
  | proj {n n' b b'} (i : Nat) : ReferenceRelated R n n' → KeyRelated R b b' →
      KeyRelated R (.proj n i b) (.proj n' i b')

theorem ReferenceRelated.mono {R S : Lean.Name → Lean.Name → Prop}
    (included : ∀ a b, R a b → S a b) {a b : OccurrenceRef}
    (related : ReferenceRelated R a b) : ReferenceRelated S a b := by
  cases related with
  | named h => exact .named (included _ _ h)
  | external a => exact .external a

theorem KeyRelated.mono {R S : Lean.Name → Lean.Name → Prop}
    (included : ∀ a b, R a b → S a b) {a b : OccurrenceKey}
    (related : KeyRelated R a b) : KeyRelated S a b := by
  induction related <;> constructor
  all_goals first
    | assumption
    | (apply ReferenceRelated.mono included; assumption)

theorem KeyRelated.functional {R : Lean.Name → Lean.Name → Prop}
    (correspondence : NameCorrespondence R) {a b c : OccurrenceKey}
    (hab : KeyRelated R a b) (hac : KeyRelated R a c) : b = c := by
  induction hab generalizing c <;> cases hac <;>
    first
    | rfl
    | (congr 1 <;> first
        | (apply ReferenceRelated.functional correspondence <;> assumption)
        | (apply_assumption; assumption))

theorem KeyRelated.injective {R : Lean.Name → Lean.Name → Prop}
    (correspondence : NameCorrespondence R) {a b c : OccurrenceKey}
    (hac : KeyRelated R a c) (hbc : KeyRelated R b c) : a = b := by
  induction hac generalizing b <;> cases hbc <;>
    first
    | rfl
    | (congr 1 <;> first
        | (apply ReferenceRelated.injective correspondence <;> assumption)
        | (apply_assumption; assumption))

theorem KeyRelated.eq_iff {R : Lean.Name → Lean.Name → Prop}
    (correspondence : NameCorrespondence R) {a a' b b' : OccurrenceKey}
    (ha : KeyRelated R a a') (hb : KeyRelated R b b') : a = b ↔ a' = b' := by
  constructor
  · intro equal
    subst b
    exact ha.functional correspondence hb
  · intro equal
    subst b'
    exact ha.injective correspondence hb

inductive LookupRelated (V : Ix.Name → Ix.Name → Prop) :
    Option Ix.Name → Option Ix.Name → Prop
  | none : LookupRelated V none none
  | some {a b} : V a b → LookupRelated V (some a) (some b)

/-- The actual first-hit list lookup commutes with a finite partial name
correspondence. The returned auxiliary correspondence may differ from the
key-name correspondence, and no cache hint appears in the statement. -/
theorem occurrenceLookup_related {R : Lean.Name → Lean.Name → Prop}
    {V : Ix.Name → Ix.Name → Prop} (correspondence : NameCorrespondence R)
    {left right : List (OccurrenceKey × Ix.Name)}
    (entries : LRel (fun a b => KeyRelated R a.1 b.1 ∧ V a.2 b.2) left right)
    {key key' : OccurrenceKey} (keys : KeyRelated R key key') :
    LookupRelated V (occurrenceLookup left key) (occurrenceLookup right key') := by
  induction entries with
  | nil => exact .none
  | cons related rest ih =>
    obtain ⟨entryKey,entryValue⟩ := related
    simp only [occurrenceLookup]
    have equal := entryKey.eq_iff correspondence keys
    split
    · rename_i found
      rw [ite_eq_left (equal.mp found)]
      exact .some entryValue
    · rename_i absent
      rw [ite_eq_right (fun found => absent (equal.mpr found))]
      exact ih

/-- First-discovery insertion preserves the actual entry correspondence.
Both no-op and new-entry branches follow from related lookups; cache buckets
can differ arbitrarily between runs. -/
theorem occurrenceInsert_related {R : Lean.Name → Lean.Name → Prop}
    {V : Ix.Name → Ix.Name → Prop} (correspondence : NameCorrespondence R)
    (left right : OccurrenceTable)
    (entries : LRel (fun a b => KeyRelated R a.1 b.1 ∧ V a.2 b.2)
      left.entries right.entries)
    (input input' : OccurrenceInput) (keys : KeyRelated R input.key input'.key)
    (value value' : Ix.Name) (values : V value value') :
    LRel (fun a b => KeyRelated R a.1 b.1 ∧ V a.2 b.2)
      (left.insert input value).entries (right.insert input' value').entries := by
  have lookups := occurrenceLookup_related correspondence entries keys
  change LookupRelated V (left.get? input) (right.get? input') at lookups
  cases hl : left.get? input <;> cases hr : right.get? input' <;>
    rw [hl,hr] at lookups
  · have added : LRel (fun a b => KeyRelated R a.1 b.1 ∧ V a.2 b.2)
        ((input.key,value) :: left.entries) ((input'.key,value') :: right.entries) :=
      .cons ⟨keys,values⟩ entries
    simpa [OccurrenceTable.insert,hl,hr] using added
  · cases lookups
  · cases lookups
  · simpa [OccurrenceTable.insert,hl,hr] using entries

end Ix.CompileCert.Canon
