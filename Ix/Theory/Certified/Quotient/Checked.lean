/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Quotient.Reading
import Ix.Theory.Certified.Signature

namespace Ix.Theory.Certified.Quotient

open Model Model.SetTheory

universe u v
variable {β : Type u} [DecidableEq β]

theorem mem_kinds (kind : Kind) : kind ∈ kinds := by cases kind <;> simp [kinds]

def Refs.header (refs : Refs β) (kind : Kind) : Signature.Header β :=
  ⟨refs.ref kind, kind.universes, refs.entryType kind⟩

def Refs.headers (refs : Refs β) : List (Signature.Header β) := kinds.map refs.header

def Refs.typeEnvironment (refs : Refs β) (entries : Environment β) : Environment β :=
  Signature.environment entries refs.headers

def Refs.liftRule (refs : Refs β) : Signature.Rule β :=
  ⟨2, liftRuleType refs, liftRuleLhs refs, liftRuleRhs refs⟩

def Refs.indRule (refs : Refs β) : Signature.Rule β :=
  ⟨1, indRuleType refs, indRuleLhs refs, indRuleRhs refs⟩

def Refs.ExactSource (refs : Refs β) (store : Store β) : Prop :=
  ∀ kind ∈ kinds, store.lookup (refs.ref kind) = some (refs.source kind)

def Refs.Fresh (refs : Refs β) (entries : Environment β) : Prop :=
  ∀ kind ∈ kinds, entries (refs.ref kind) = none

instance (refs : Refs β) (store : Store β) : Decidable (refs.ExactSource store) :=
  inferInstanceAs (Decidable (∀ kind ∈ kinds, store.lookup (refs.ref kind) = some (refs.source kind)))

instance (refs : Refs β) (entries : Environment β) : Decidable (refs.Fresh entries) :=
  inferInstanceAs (Decidable (∀ kind ∈ kinds, entries (refs.ref kind) = none))

structure Witness (β : Type u) where
  refs : Refs β
  types : List (Signature.TypeWitness β)
  liftRule : Signature.RuleWitness β
  indRule : Signature.RuleWitness β

structure Checked (entries : Environment β) (store : Store β) (refs : Refs β) : Prop where
  exactSource : refs.ExactSource store
  fresh : refs.Fresh entries
  equality : Basis.Equality.Interface entries refs.eq refs.eqRefl refs.eqRec
  types : Signature.Formed.{u,v} entries refs.headers
  liftRule : Signature.RuleFormed.{u,v} (refs.typeEnvironment entries) refs.liftRule
  indRule : Signature.RuleFormed.{u,v} (refs.typeEnvironment entries) refs.indRule

def check (fuel : Nat) (entries : Environment β) (store : Store β) (witness : Witness β) :
    Option (CheckedClaim.{u} (Checked.{u,v} entries store witness.refs)) :=
  if hs : witness.refs.ExactSource store then
    if hf : witness.refs.Fresh entries then
      if he : Basis.Equality.Interface entries witness.refs.eq witness.refs.eqRefl witness.refs.eqRec then do
        let ht ← Signature.checkTypes.{u,v} fuel entries witness.refs.headers witness.types
        let hl ← Signature.checkRule.{u,v} fuel (witness.refs.typeEnvironment entries) witness.refs.liftRule witness.liftRule
        let hi ← Signature.checkRule.{u,v} fuel (witness.refs.typeEnvironment entries) witness.refs.indRule witness.indRule
        return ⟨⟨hs, hf, he, ht.down, hl.down, hi.down⟩⟩
      else none
    else none
  else none

theorem check_sound {fuel : Nat} {entries : Environment β} {store : Store β} {witness : Witness β}
    {result} (_ : check.{u,v} fuel entries store witness = some result) :
    Checked.{u,v} entries store witness.refs := result.down

omit [DecidableEq β] in
theorem Refs.ExactSource.injective {refs : Refs β} {store : Store β} (h : refs.ExactSource store) :
    Function.Injective refs.ref := by
  intro a b he
  have ha := h a (mem_kinds a)
  have hb := h b (mem_kinds b)
  rw [he, hb] at ha
  have hs := Option.some.inj ha
  cases a <;> cases b <;> simp [Refs.source] at hs <;> rfl

def Refs.kind? (refs : Refs β) (r : ConstRef β) : Option Kind :=
  if r = refs.type then some .type else
  if r = refs.ctor then some .ctor else
  if r = refs.lift then some .lift else
  if r = refs.ind then some .ind else
  if r = refs.sound then some .sound else none

theorem Refs.kind?_same {refs : Refs β} {store : Store β} (h : refs.ExactSource store) (kind : Kind) :
    refs.kind? (refs.ref kind) = some kind := by
  have he (a b : Kind) (hne : a ≠ b) : refs.ref a ≠ refs.ref b := fun hab => hne (h.injective hab)
  have ht := he .ctor .type (by decide)
  have hlt := he .lift .type (by decide)
  have hlc := he .lift .ctor (by decide)
  have hit := he .ind .type (by decide)
  have hic := he .ind .ctor (by decide)
  have hil := he .ind .lift (by decide)
  have hst := he .sound .type (by decide)
  have hsc := he .sound .ctor (by decide)
  have hsl := he .sound .lift (by decide)
  have hsi := he .sound .ind (by decide)
  cases kind <;> simp_all [Refs.kind?, Refs.ref]

theorem Refs.kind?_sound {refs : Refs β} {r : ConstRef β} {kind : Kind}
    (h : refs.kind? r = some kind) : r = refs.ref kind := by
  unfold Refs.kind? at h
  split at h
  · cases Option.some.inj h; assumption
  · split at h
    · cases Option.some.inj h; assumption
    · split at h
      · cases Option.some.inj h; assumption
      · split at h
        · cases Option.some.inj h; assumption
        · split at h
          · cases Option.some.inj h; assumption
          · contradiction

variable {entries : Environment β} {store : Store β} {refs : Refs β}

theorem typeEnvironment_lookup (h : Checked.{u,v} entries store refs) (kind : Kind) :
    refs.typeEnvironment entries (refs.ref kind) = some (refs.header kind).entry :=
  h.types.lookup (List.mem_map.mpr ⟨kind, mem_kinds kind, rfl⟩)

variable {V : Type v} [SetTheory V]

noncomputable def Refs.assignment (refs : Refs β) (constants : Assignment β V) : Assignment β V :=
  fun r levels => match refs.kind? r with
    | some kind => refs.value constants kind levels
    | none => constants r levels

theorem assignment_same (h : Checked.{u,v} entries store refs) (constants : Assignment β V)
    (kind : Kind) (levels : List Nat) :
    refs.assignment constants (refs.ref kind) levels = refs.value constants kind levels := by
  simp only [Refs.assignment, Refs.kind?_same h.exactSource]

theorem assignment_agrees (h : Checked.{u,v} entries store refs) (constants : Assignment β V) :
    Assignment.AgreesOn entries constants (refs.assignment constants) := by
  intro r entry hr levels
  unfold Refs.assignment
  cases hk : refs.kind? r with
  | none => rfl
  | some kind =>
    have he := Refs.kind?_sound hk
    have hf := h.fresh kind (mem_kinds kind)
    rw [← he, hr] at hf
    contradiction

theorem assignment_reading (h : Checked.{u,v} entries store refs) (constants : Assignment β V) :
    Reading (refs.assignment constants) refs := by
  have heq (levels) : refs.assignment constants refs.eq levels = constants refs.eq levels := by
    obtain ⟨entry, he, _, _⟩ := h.equality.former
    exact assignment_agrees h constants _ _ he levels
  constructor
  · intro u
    exact assignment_same h constants .type [u]
  · intro u
    exact assignment_same h constants .ctor [u]
  · intro u v
    rw [show refs.lift = refs.ref .lift from rfl, assignment_same h constants]
    simp [Refs.value, liftValue, invariantSet, Basis.Equality.value, heq]
  · intro u
    exact assignment_same h constants .ind [u]
  · intro u
    exact assignment_same h constants .sound [u]

theorem typeAssignment_realizes (h : Checked.{u,v} entries store refs) (hE : entries.WF)
    (constants : Assignment β V) (hM : Realizes constants entries) :
    Realizes (refs.assignment constants) (refs.typeEnvironment entries) := by
  have hm := hM.of_agrees hE (assignment_agrees h constants)
  apply h.types.realizes hm
  intro header hh levels hn env
  obtain ⟨kind, _, rfl⟩ := List.mem_map.mp hh
  exact value_mem (assignment_reading h constants) h.equality hm kind levels hn env

end Ix.Theory.Certified.Quotient
