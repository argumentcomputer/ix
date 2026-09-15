/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Resolution
import Ix.Theory.Certified.Quotient.Publish

/-!
# Admission of the canonical quotient constants

Production accepts a `.quot` declaration only through `checkQuot`: the
declared address must be the reserved primitive address of its kind, the
universe count must be the fixed one, the declared type must hash to the
canonical type installed by Lean's `Environment.addQuot`, and `Quot.lift`
additionally requires the exact `Eq`/`Eq.refl` prerequisites. This module
inverts that guard sequence (`quot_type_trace`, `checkQuot_success`,
`checkEqType_success`), reads the four canonical kernel types to the certified
quotient description (`canonicalQuotType_reads`), and admits the four constants
into the set model with the certified quotient semantics (`extend_quotients`):
the published entries carry the certified types and the `Quot.lift`/`Quot.ind`
computation equations, and every model of the preceding interface extends to
them while keeping its old interpretations.

The certified package (`Ix.Theory.Certified.Quotient`) also names the
soundness axiom `Quot.sound`; production declares it as an ordinary axiom, not
as a quotient primitive, so it is outside this admission, and the certified
reading is instantiated with the induction reference standing in for it (both
denote the point). The `Eq` family is an inductive block, whose admission is
not yet refined in this library: its three model entries with the canonical
equality types are an explicit static binding premise (`EqualityBinding`), to
be discharged by the inductive admission of WP5. The environment fragment
`QuotientEnvironmentFragment` restates the environment theorems for runs whose
initial interface already contains that binding and whose work contains the
four accepted quotient standalones.
-/

namespace Ix.QuotKind

/-- The certified kind of a production quotient primitive. -/
def certified : Ix.QuotKind → Ix.Theory.Certified.Quotient.Kind
  | .type => .type
  | .ctor => .ctor
  | .lift => .lift
  | .ind => .ind

/-- The universe count required by `checkQuot`. -/
def universes : Ix.QuotKind → UInt64
  | .lift => 2
  | .type | .ctor | .ind => 1

theorem certified_universes (kind : Ix.QuotKind) :
    kind.certified.universes = kind.universes.toNat := by
  cases kind <;> rfl

theorem certified_injective {left right : Ix.QuotKind} (same : left.certified = right.certified) :
    left = right := by
  cases left <;> cases right <;> first | rfl | cases same

theorem eq_of_bne_eq_false {left right : Ix.QuotKind} (h : (left != right) = false) :
    left = right := by
  revert h
  cases left <;> cases right <;> decide

theorem eq_lift_of_beq {kind : Ix.QuotKind} (h : (kind == .lift) = true) : kind = .lift := by
  revert h
  cases kind <;> decide

theorem beq_lift_eq_false {kind : Ix.QuotKind} (h : kind ≠ .lift) : (kind == .lift) = false := by
  revert h
  cases kind <;> decide

end Ix.QuotKind

namespace Ix.Kernel

/-- The reserved primitive identifier of each quotient kind. -/
def Primitives.quot {m : Mode} (p : Primitives m) : Ix.QuotKind → KId m
  | .type => p.quotType
  | .ctor => p.quotCtor
  | .lift => p.quotLift
  | .ind => p.quotInd

end Ix.Kernel

namespace Ix.Kernel.Consistency

open Theory Theory.Model Theory.Model.SetTheory Theory.Certified

universe u v

/-! ### Certified quotient references -/

/-- The model references of the four quotient primitives together with the
equality family, its reflexivity constructor, and its recursor, which the
certified quotient semantics reads. -/
structure QuotientRefs (β : Type u) where
  type : ConstRef β
  ctor : ConstRef β
  lift : ConstRef β
  ind : ConstRef β
  eq : ConstRef β
  eqRefl : ConstRef β
  eqRec : ConstRef β

namespace QuotientRefs

variable {β : Type u}

/-- The certified reference package. Production declares `Quot.sound` as an
ordinary axiom rather than a quotient primitive, so no soundness entry is
published here; the induction reference stands in for it in the certified
reading, since both denote the point. -/
def certified (refs : QuotientRefs β) : Quotient.Refs β :=
  { eq := refs.eq, type := refs.type, ctor := refs.ctor, lift := refs.lift, ind := refs.ind,
    eqRefl := refs.eqRefl, eqRec := refs.eqRec, sound := refs.ind }

/-- The reference of a production quotient kind. -/
def ref (refs : QuotientRefs β) (kind : Ix.QuotKind) : ConstRef β :=
  refs.certified.ref kind.certified

/-- The certified type of a production quotient kind. -/
def entryType (refs : QuotientRefs β) (kind : Ix.QuotKind) : AExpr β :=
  refs.certified.entryType kind.certified

/-- The published entry of a production quotient kind: the certified type,
universe count, no value, the `Quot.lift`/`Quot.ind` computation equation, and
no facts. -/
def entry (refs : QuotientRefs β) (kind : Ix.QuotKind) : ConstantEntry β :=
  refs.certified.entry kind.certified

@[simp] theorem ref_type (refs : QuotientRefs β) : refs.ref .type = refs.type := rfl
@[simp] theorem ref_ctor (refs : QuotientRefs β) : refs.ref .ctor = refs.ctor := rfl
@[simp] theorem ref_lift (refs : QuotientRefs β) : refs.ref .lift = refs.lift := rfl
@[simp] theorem ref_ind (refs : QuotientRefs β) : refs.ref .ind = refs.ind := rfl

@[simp] theorem entry_universes (refs : QuotientRefs β) (kind : Ix.QuotKind) :
    (refs.entry kind).universes = kind.universes.toNat :=
  kind.certified_universes

@[simp] theorem entry_type (refs : QuotientRefs β) (kind : Ix.QuotKind) :
    (refs.entry kind).type = refs.entryType kind := rfl

@[simp] theorem entry_body (refs : QuotientRefs β) (kind : Ix.QuotKind) :
    (refs.entry kind).body = none := rfl

@[simp] theorem entry_facts (refs : QuotientRefs β) (kind : Ix.QuotKind) :
    (refs.entry kind).facts = [] := rfl

theorem entryType_type (refs : QuotientRefs β) : refs.entryType .type = Quotient.typeType := rfl
theorem entryType_ctor (refs : QuotientRefs β) :
    refs.entryType .ctor = Quotient.ctorType refs.certified := rfl
theorem entryType_lift (refs : QuotientRefs β) :
    refs.entryType .lift = Quotient.liftType refs.certified := rfl
theorem entryType_ind (refs : QuotientRefs β) :
    refs.entryType .ind = Quotient.indType refs.certified := rfl

/-- The four quotient references are pairwise distinct. -/
def Injective (refs : QuotientRefs β) : Prop := Function.Injective refs.ref

/-- The equality references are outside the four quotient references. -/
structure EqualityApart (refs : QuotientRefs β) : Prop where
  eq : ∀ kind, refs.ref kind ≠ refs.eq
  eqRefl : ∀ kind, refs.ref kind ≠ refs.eqRefl
  eqRec : ∀ kind, refs.ref kind ≠ refs.eqRec

end QuotientRefs

/-! ### The published environment -/

/-- The preceding interface extended by the four quotient entries. -/
def quotientEnvironment {β : Type u} [DecidableEq β] (refs : QuotientRefs β)
    (entries : Model.Environment β) : Model.Environment β :=
  (((entries.insert refs.type (refs.entry .type)).insert refs.ctor (refs.entry .ctor)).insert
    refs.lift (refs.entry .lift)).insert refs.ind (refs.entry .ind)

section Published

variable {β : Type u} [DecidableEq β] {refs : QuotientRefs β} {entries : Model.Environment β}

theorem quotientEnvironment_same (injective : refs.Injective) (kind : Ix.QuotKind) :
    quotientEnvironment refs entries (refs.ref kind) = some (refs.entry kind) := by
  have ne (left right : Ix.QuotKind) (different : left ≠ right) : refs.ref left ≠ refs.ref right :=
    fun same => different (injective same)
  have typeInd : refs.type ≠ refs.ind := ne .type .ind (by decide)
  have typeLift : refs.type ≠ refs.lift := ne .type .lift (by decide)
  have typeCtor : refs.type ≠ refs.ctor := ne .type .ctor (by decide)
  have ctorInd : refs.ctor ≠ refs.ind := ne .ctor .ind (by decide)
  have ctorLift : refs.ctor ≠ refs.lift := ne .ctor .lift (by decide)
  have liftInd : refs.lift ≠ refs.ind := ne .lift .ind (by decide)
  cases kind with
  | type => simp [quotientEnvironment, Model.Environment.insert, typeInd, typeLift, typeCtor]
  | ctor => simp [quotientEnvironment, Model.Environment.insert, ctorInd, ctorLift]
  | lift => simp [quotientEnvironment, Model.Environment.insert, liftInd]
  | ind => simp [quotientEnvironment, Model.Environment.insert]

theorem quotientEnvironment_old (fresh : ∀ kind, entries (refs.ref kind) = none)
    {r : ConstRef β} {entry : ConstantEntry β} (present : entries r = some entry) :
    quotientEnvironment refs entries r = some entry := by
  have notInd : r ≠ refs.ind := fresh_ne (fresh .ind) present
  have notLift : r ≠ refs.lift := fresh_ne (fresh .lift) present
  have notCtor : r ≠ refs.ctor := fresh_ne (fresh .ctor) present
  have notType : r ≠ refs.type := fresh_ne (fresh .type) present
  simp only [quotientEnvironment, Model.Environment.insert, if_neg notInd, if_neg notLift,
    if_neg notCtor, if_neg notType, present]

theorem quotientEnvironment_cases {r : ConstRef β} {entry : ConstantEntry β}
    (present : quotientEnvironment refs entries r = some entry) :
    entries r = some entry ∨ ∃ kind, r = refs.ref kind ∧ entry = refs.entry kind := by
  simp only [quotientEnvironment, Model.Environment.insert] at present
  split at present
  · exact .inr ⟨.ind, ‹_›, (Option.some.inj present).symm⟩
  split at present
  · exact .inr ⟨.lift, ‹_›, (Option.some.inj present).symm⟩
  split at present
  · exact .inr ⟨.ctor, ‹_›, (Option.some.inj present).symm⟩
  split at present
  · exact .inr ⟨.type, ‹_›, (Option.some.inj present).symm⟩
  · exact .inl present

theorem quotientEnvironment_extends (fresh : ∀ kind, entries (refs.ref kind) = none) :
    ∀ r entry, entries r = some entry → quotientEnvironment refs entries r = some entry :=
  fun _ _ present => quotientEnvironment_old fresh present

theorem _root_.Ix.Theory.Model.AExpr.ReferencesIn.quotient {e : AExpr β}
    (references : e.ReferencesIn entries) :
    e.ReferencesIn (quotientEnvironment refs entries) :=
  references.insert.insert.insert.insert

theorem _root_.Ix.Theory.Model.ConstantFact.ReferencesIn.quotient {fact : ConstantFact β}
    (references : fact.ReferencesIn entries) :
    fact.ReferencesIn (quotientEnvironment refs entries) :=
  references.insert.insert.insert.insert

end Published

/-! ### Syntactic closure of the certified quotient syntax -/

section Closure

variable {β : Type u}

theorem typeType_scope : (Quotient.typeType : AExpr β).Scope 1 0 := of_decide_eq_true rfl
theorem ctorType_scope (refs : Quotient.Refs β) : (Quotient.ctorType refs).Scope 1 0 :=
  of_decide_eq_true rfl
theorem liftType_scope (refs : Quotient.Refs β) : (Quotient.liftType refs).Scope 2 0 :=
  of_decide_eq_true rfl
theorem indType_scope (refs : Quotient.Refs β) : (Quotient.indType refs).Scope 1 0 :=
  of_decide_eq_true rfl
theorem liftRuleLhs_scope (refs : Quotient.Refs β) : (Quotient.liftRuleLhs refs).Scope 2 0 :=
  of_decide_eq_true rfl
theorem liftRuleRhs_scope (refs : Quotient.Refs β) : (Quotient.liftRuleRhs refs).Scope 2 0 :=
  of_decide_eq_true rfl
theorem indRuleLhs_scope (refs : Quotient.Refs β) : (Quotient.indRuleLhs refs).Scope 1 0 :=
  of_decide_eq_true rfl
theorem indRuleRhs_scope (refs : Quotient.Refs β) : (Quotient.indRuleRhs refs).Scope 1 0 :=
  of_decide_eq_true rfl

theorem QuotientRefs.entryType_scope (refs : QuotientRefs β) (kind : Ix.QuotKind) :
    (refs.entryType kind).Scope kind.universes.toNat 0 := by
  cases kind with
  | type => exact typeType_scope
  | ctor => exact ctorType_scope _
  | lift => exact liftType_scope _
  | ind => exact indType_scope _

theorem QuotientRefs.equation_scope (refs : QuotientRefs β) (kind : Ix.QuotKind)
    {law : ConstantEquation β} (listed : law ∈ (refs.entry kind).equations) :
    law.lhs.Scope kind.universes.toNat 0 ∧ law.rhs.Scope kind.universes.toNat 0 := by
  cases kind with
  | type | ctor => cases listed
  | lift =>
    cases List.mem_singleton.mp listed
    exact ⟨liftRuleLhs_scope _, liftRuleRhs_scope _⟩
  | ind =>
    cases List.mem_singleton.mp listed
    exact ⟨indRuleLhs_scope _, indRuleRhs_scope _⟩

/-- The references of the published types and equations: only the four
quotient references and the equality family. -/
theorem QuotientRefs.entryType_references (refs : QuotientRefs β) (kind : Ix.QuotKind)
    {entries : Model.Environment β} (type : (entries refs.type).isSome = true)
    (ctor : (entries refs.ctor).isSome = true) (eq : (entries refs.eq).isSome = true) :
    (refs.entryType kind).ReferencesIn entries := by
  intro r member
  cases kind <;> simp only [QuotientRefs.entryType, Quotient.Refs.entryType, Ix.QuotKind.certified,
    Quotient.typeType, Quotient.ctorType, Quotient.liftType, Quotient.indType,
    Quotient.liftPrefix, Quotient.indPrefix, Quotient.invariantType, Quotient.relationType,
    Quotient.applied, Quotient.constructed, Basis.Equality.applied, AExpr.forallN, AExpr.appN,
    AExpr.references, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false, false_or]
    at member
  · rcases member with rfl
    exact type
  · rcases member with rfl | rfl
    · exact eq
    · exact type
  · rcases member with rfl | rfl | rfl
    · exact type
    · exact ctor
    · exact type

theorem QuotientRefs.equation_references (refs : QuotientRefs β) (kind : Ix.QuotKind)
    {entries : Model.Environment β} (type : (entries refs.type).isSome = true)
    (ctor : (entries refs.ctor).isSome = true) (lift : (entries refs.lift).isSome = true)
    (ind : (entries refs.ind).isSome = true) (eq : (entries refs.eq).isSome = true)
    {law : ConstantEquation β} (listed : law ∈ (refs.entry kind).equations) :
    law.lhs.ReferencesIn entries ∧ law.rhs.ReferencesIn entries := by
  cases kind with
  | type | ctor => cases listed
  | lift =>
    cases List.mem_singleton.mp listed
    constructor
    · intro r member
      simp only [Quotient.liftRuleLhs, Quotient.liftRuleBinders, Quotient.liftPrefix,
        Quotient.invariantType, Quotient.relationType, Quotient.constructed,
        Basis.Equality.applied, AExpr.lamN, AExpr.appN, AExpr.references, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact eq
      · exact lift
      · exact ctor
    · intro r member
      simp only [Quotient.liftRuleRhs, Quotient.liftRuleBinders, Quotient.liftPrefix,
        Quotient.invariantType, Quotient.relationType, Basis.Equality.applied, AExpr.lamN,
        AExpr.appN, AExpr.references, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl
      exact eq
  | ind =>
    cases List.mem_singleton.mp listed
    constructor
    · intro r member
      simp only [Quotient.indRuleLhs, Quotient.indRuleBinders, Quotient.indPrefix,
        Quotient.relationType, Quotient.applied, Quotient.constructed, AExpr.lamN, AExpr.appN,
        AExpr.references, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact type
      · exact ctor
      · exact ind
      · exact ctor
    · intro r member
      simp only [Quotient.indRuleRhs, Quotient.indRuleBinders, Quotient.indPrefix,
        Quotient.relationType, Quotient.applied, Quotient.constructed, AExpr.lamN, AExpr.appN,
        AExpr.references, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact type
      · exact ctor

end Closure

section WellFormed

variable {β : Type u} [DecidableEq β] {refs : QuotientRefs β} {entries : Model.Environment β}

private theorem published_isSome (injective : refs.Injective) (kind : Ix.QuotKind) :
    (quotientEnvironment refs entries (refs.ref kind)).isSome = true := by
  rw [quotientEnvironment_same injective kind]
  rfl

/-- The published interface is syntactically closed whenever the preceding
one is: the certified syntax is scoped, and it references only the four
quotient references and the admitted equality family. -/
theorem quotientEnvironment_wf (wellFormed : entries.WF) (injective : refs.Injective)
    (fresh : ∀ kind, entries (refs.ref kind) = none)
    (equality : (entries refs.eq).isSome = true) :
    (quotientEnvironment refs entries).WF := by
  have eqPresent : (quotientEnvironment refs entries refs.eq).isSome = true := by
    cases present : entries refs.eq with
    | none => rw [present] at equality; cases equality
    | some entry => rw [quotientEnvironment_old fresh present]; rfl
  have closed : ∀ r entry, quotientEnvironment refs entries r = some entry →
      EntryClosed (quotientEnvironment refs entries) entry := by
    intro r entry present
    rcases quotientEnvironment_cases present with old | ⟨kind, _, rfl⟩
    · exact ⟨wellFormed.typeScope _ _ old, wellFormed.bodyScope _ _ old,
        (wellFormed.typeReferences _ _ old).quotient,
        fun body hb => (wellFormed.bodyReferences _ _ old body hb).quotient,
        wellFormed.equationScope _ _ old,
        fun law hl => ⟨(wellFormed.equationReferences _ _ old law hl).1.quotient,
          (wellFormed.equationReferences _ _ old law hl).2.quotient⟩,
        wellFormed.factScope _ _ old,
        fun fact hf => (wellFormed.factReferences _ _ old fact hf).quotient⟩
    · refine ⟨?_, (fun body hb => by cases hb), ?_, (fun body hb => by cases hb), ?_, ?_,
        (fun fact hf => by cases hf), (fun fact hf => by cases hf)⟩
      · simpa only [QuotientRefs.entry_universes, QuotientRefs.entry_type] using
          refs.entryType_scope kind
      · simpa only [QuotientRefs.entry_type] using refs.entryType_references kind
          (published_isSome injective .type) (published_isSome injective .ctor) eqPresent
      · intro law listed
        simpa only [QuotientRefs.entry_universes] using refs.equation_scope kind listed
      · intro law listed
        exact refs.equation_references kind (published_isSome injective .type)
          (published_isSome injective .ctor) (published_isSome injective .lift)
          (published_isSome injective .ind) eqPresent listed
  exact ⟨fun r e h => (closed r e h).typeScope, fun r e h => (closed r e h).bodyScope,
    fun r e h => (closed r e h).typeReferences, fun r e h => (closed r e h).bodyReferences,
    fun r e h => (closed r e h).equationScope, fun r e h => (closed r e h).equationReferences,
    fun r e h => (closed r e h).factScope, fun r e h => (closed r e h).factReferences⟩

end WellFormed

/-! ### Formation of the canonical quotient types

The certified validator establishes formation of these fixed types by running
its checker on a witness. Here the same typing claims are derived once, from
the model's rule producers, so no witness or validator run is needed. -/

section Formation

open Quotient

variable {β : Type u} {E : Model.Environment β} {refs : Refs β}

/-- `α → α → Prop` in a context whose most recent binder is a sort. -/
private theorem relationType_typing (Γ : Context β) (l : VLevel) :
    TypingClaim.{u,v} E (.sort l :: Γ) relationType
      (.sort (.imax l (.imax l (.succ .zero)))) := by
  apply TypingClaim.forallE (b := .imax l (.succ .zero)) (TypingClaim.bvar rfl) ?_ rfl
  exact TypingClaim.forallE (b := .succ .zero) (TypingClaim.bvar rfl) (TypingClaim.sort _) rfl

/-- Application with the result type supplied separately, so that expected-type
propagation is not blocked by an unevaluated substitution. -/
private theorem app_typing {Γ : Context β} {f a A B C : AExpr β} {p : PropWhen}
    (hf : TypingClaim.{u,v} E Γ f (.forallE p A B)) (ha : TypingClaim.{u,v} E Γ a A)
    (result : B.inst a = C) : TypingClaim.{u,v} E Γ (.app f a) C :=
  result ▸ TypingClaim.app hf ha

theorem typeType_formed :
    ∃ level, TypingClaim.{u,v} E [] (typeType : AExpr β) (.sort level) := by
  constructor
  apply TypingClaim.forallE (TypingClaim.sort _)
  · exact TypingClaim.forallE (b := .succ (.param 0)) (relationType_typing [] (.param 0))
      (TypingClaim.sort _) rfl
  · rfl

/-- The quotient former applied to a sort and a relation. The relation's
context entry is stated in the form produced by the application rule, so the
lookups are closed computations at each use. -/
private theorem applied_typing (hT : E.HasType refs.type 1 typeType) {Γ : Context β}
    {carrier relation : Nat} {sortLevel : VLevel} (hc : Γ[carrier]? = some (.sort sortLevel))
    (hr : Γ[relation]? = some ((relationType.instL [sortLevel]).inst (.bvar carrier))) :
    TypingClaim.{u,v} E Γ (applied refs sortLevel (.bvar carrier) (.bvar relation))
      (.sort sortLevel) := by
  obtain ⟨entry, he, hn, ht⟩ := hT
  have c := TypingClaim.const (Γ := Γ) (ls := [sortLevel]) he (by simp [hn])
  rw [ht] at c
  have a1 := TypingClaim.app c (TypingClaim.bvar hc)
  have a2 := TypingClaim.app a1 (TypingClaim.bvar hr)
  exact a2

theorem ctorType_formed (hT : E.HasType refs.type 1 typeType) :
    ∃ level, TypingClaim.{u,v} E [] (ctorType refs) (.sort level) := by
  constructor
  apply TypingClaim.forallE (TypingClaim.sort _)
  · apply TypingClaim.forallE (relationType_typing [] (.param 0))
    · apply TypingClaim.forallE (TypingClaim.bvar rfl)
      · exact applied_typing (carrier := 2) (relation := 1) hT rfl rfl
      · rfl
    · rfl
  · rfl

/-- The equality family applied to a sort and two of its elements, with the
element types in the form produced by the application rule. -/
private theorem equality_typing (hE : E.HasType refs.eq 1 Basis.Equality.type) {Γ : Context β}
    {carrier : Nat} {sortLevel : VLevel} {left right : AExpr β}
    (hc : Γ[carrier]? = some (.sort sortLevel))
    (hl : TypingClaim.{u,v} E Γ left (((AExpr.bvar 0).instL [sortLevel]).inst (.bvar carrier)))
    (hr : TypingClaim.{u,v} E Γ right
      ((((AExpr.bvar 1).instL [sortLevel]).inst (.bvar carrier) 1).inst left)) :
    TypingClaim.{u,v} E Γ (Basis.Equality.applied refs.eq sortLevel (.bvar carrier) left right)
      (.sort .zero) := by
  obtain ⟨entry, he, hn, ht⟩ := hE
  have c := TypingClaim.const (Γ := Γ) (ls := [sortLevel]) he (by simp [hn])
  rw [ht] at c
  have a1 := TypingClaim.app c (TypingClaim.bvar hc)
  have a2 := TypingClaim.app a1 hl
  have a3 := TypingClaim.app a2 hr
  exact a3

theorem liftType_formed (hT : E.HasType refs.type 1 typeType)
    (hE : E.HasType refs.eq 1 Basis.Equality.type) :
    ∃ level, TypingClaim.{u,v} E [] (liftType refs) (.sort level) := by
  constructor
  apply TypingClaim.forallE (TypingClaim.sort _)
  · apply TypingClaim.forallE (relationType_typing [] (.param 0))
    · apply TypingClaim.forallE (TypingClaim.sort _)
      · apply TypingClaim.forallE
        · exact TypingClaim.forallE (b := .param 1) (TypingClaim.bvar rfl) (TypingClaim.bvar rfl)
            rfl
        · apply TypingClaim.forallE
          · -- Invariance of `f` under `R`, in the context `[f, B, R, A]`.
            apply TypingClaim.forallE (TypingClaim.bvar rfl)
            · apply TypingClaim.forallE (TypingClaim.bvar rfl)
              · apply TypingClaim.forallE
                · exact app_typing (app_typing (TypingClaim.bvar rfl)
                    (TypingClaim.bvar rfl) rfl) (TypingClaim.bvar rfl) rfl
                · exact equality_typing (carrier := 4) hE rfl
                    (app_typing (TypingClaim.bvar rfl) (TypingClaim.bvar rfl) rfl)
                    (app_typing (TypingClaim.bvar rfl) (TypingClaim.bvar rfl) rfl)
                · rfl
              · rfl
            · rfl
          · -- The result `Quot A R → B`, in the context `[h, f, B, R, A]`.
            apply TypingClaim.forallE
            · exact applied_typing (carrier := 4) (relation := 3) hT rfl rfl
            · exact TypingClaim.bvar rfl
            · rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · rfl

theorem indType_formed (hT : E.HasType refs.type 1 typeType)
    (hC : E.HasType refs.ctor 1 (ctorType refs)) :
    ∃ level, TypingClaim.{u,v} E [] (indType refs) (.sort level) := by
  obtain ⟨entry, he, hn, ht⟩ := hC
  constructor
  apply TypingClaim.forallE (TypingClaim.sort _)
  · apply TypingClaim.forallE (relationType_typing [] (.param 0))
    · -- The motive domain `Quot A R → Prop`, in the context `[R, A]`.
      apply TypingClaim.forallE
      · exact TypingClaim.forallE (b := .succ .zero)
          (applied_typing (carrier := 1) (relation := 0) hT rfl rfl) (TypingClaim.sort _) rfl
      · -- The minor premise `∀ a, β (Quot.mk r a)`, in the context `[β, R, A]`.
        apply TypingClaim.forallE
        · apply TypingClaim.forallE (TypingClaim.bvar rfl)
          · have c := TypingClaim.const (Γ := Context.push (.bvar 2) (Context.push
                (.forallE .never (applied refs (.param 0) (.bvar 1) (.bvar 0)) (.sort .zero))
                (Context.push relationType (Context.push (.sort (.param 0)) []))))
              (ls := [.param 0]) he (by simp [hn])
            rw [ht] at c
            have mk := TypingClaim.app (TypingClaim.app (TypingClaim.app c
              (TypingClaim.bvar (i := 3) rfl)) (TypingClaim.bvar (i := 2) rfl))
              (TypingClaim.bvar (i := 0) rfl)
            exact app_typing (TypingClaim.bvar rfl) mk rfl
          · rfl
        · -- The conclusion `∀ q, β q`, in the context `[mk, β, R, A]`.
          apply TypingClaim.forallE
          · exact applied_typing (carrier := 3) (relation := 2) hT rfl rfl
          · exact app_typing (TypingClaim.bvar rfl) (TypingClaim.bvar rfl) rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · rfl

end Formation

/-! ### Realization -/

section Realization

open Quotient

variable {β : Type u} [DecidableEq β] {V : Type v} [SetTheory V]

/-- The certified quotient values installed at the four references; every
other reference keeps its value. -/
noncomputable def quotientAssignment (refs : QuotientRefs β) (constants : Assignment β V) :
    Assignment β V :=
  (((constants.insert refs.type (fun levels => formerValue (levels.getD 0 0))).insert refs.ctor
    (fun levels => constructorValue (levels.getD 0 0))).insert refs.lift
    (fun levels => liftValue constants refs.eq (levels.getD 0 0) (levels.getD 1 0))).insert
    refs.ind (fun _ => pt)

variable {refs : QuotientRefs β} {entries : Model.Environment β}

theorem quotientAssignment_agrees (fresh : ∀ kind, entries (refs.ref kind) = none)
    (constants : Assignment β V) :
    Assignment.AgreesOn entries constants (quotientAssignment refs constants) := by
  intro r entry present levels
  have notInd : r ≠ refs.ind := fresh_ne (fresh .ind) present
  have notLift : r ≠ refs.lift := fresh_ne (fresh .lift) present
  have notCtor : r ≠ refs.ctor := fresh_ne (fresh .ctor) present
  have notType : r ≠ refs.type := fresh_ne (fresh .type) present
  simp only [quotientAssignment, Assignment.insert, if_neg notInd, if_neg notLift, if_neg notCtor,
    if_neg notType]

/-- The installed values are the certified reading of the package. -/
theorem quotientAssignment_reading (injective : refs.Injective) (apart : refs.EqualityApart)
    (constants : Assignment β V) :
    Reading (quotientAssignment refs constants) refs.certified := by
  have ne (left right : Ix.QuotKind) (different : left ≠ right) : refs.ref left ≠ refs.ref right :=
    fun same => different (injective same)
  have typeInd : refs.type ≠ refs.ind := ne .type .ind (by decide)
  have typeLift : refs.type ≠ refs.lift := ne .type .lift (by decide)
  have typeCtor : refs.type ≠ refs.ctor := ne .type .ctor (by decide)
  have ctorInd : refs.ctor ≠ refs.ind := ne .ctor .ind (by decide)
  have ctorLift : refs.ctor ≠ refs.lift := ne .ctor .lift (by decide)
  have liftInd : refs.lift ≠ refs.ind := ne .lift .ind (by decide)
  have eqInd : refs.eq ≠ refs.ind := (apart.eq .ind).symm
  have eqLift : refs.eq ≠ refs.lift := (apart.eq .lift).symm
  have eqCtor : refs.eq ≠ refs.ctor := (apart.eq .ctor).symm
  have eqType : refs.eq ≠ refs.type := (apart.eq .type).symm
  have eqValue (levels : List Nat) : quotientAssignment refs constants refs.eq levels =
      constants refs.eq levels := by
    simp only [quotientAssignment, Assignment.insert, if_neg eqInd, if_neg eqLift, if_neg eqCtor,
      if_neg eqType]
  constructor
  · intro u
    simp only [QuotientRefs.certified, quotientAssignment, Assignment.insert, if_neg typeInd,
      if_neg typeLift, if_neg typeCtor, if_true, List.getD_cons_zero]
  · intro u
    simp only [QuotientRefs.certified, quotientAssignment, Assignment.insert, if_neg ctorInd,
      if_neg ctorLift, if_true, List.getD_cons_zero]
  · intro u w
    have lhs : quotientAssignment refs constants refs.lift [u, w] =
        liftValue constants refs.eq u w := by
      simp only [quotientAssignment, Assignment.insert, if_neg liftInd, if_true,
        List.getD_cons_zero,
        List.getD_cons_succ]
    simp only [QuotientRefs.certified]
    rw [lhs]
    simp only [liftValue, invariantSet, Basis.Equality.value, eqValue]
  · intro u
    simp only [QuotientRefs.certified, quotientAssignment, Assignment.insert, if_true]
  · intro u
    simp only [QuotientRefs.certified, quotientAssignment, Assignment.insert, if_true]

/-- The certified equality interface, restated for the quotient references. -/
def EqualityInterface (entries : Model.Environment β) (refs : QuotientRefs β) : Prop :=
  Basis.Equality.Interface entries refs.eq refs.eqRefl refs.eqRec

/-- Admitting the four quotient constants extends every model of the
preceding interface, which must already realize the equality family, and
keeps every old interpretation. The published entries carry the certified
types and the `Quot.lift`/`Quot.ind` computation equations. -/
theorem extend_quotients (wellFormed : entries.WF) (injective : refs.Injective)
    (apart : refs.EqualityApart) (fresh : ∀ kind, entries (refs.ref kind) = none)
    (equality : EqualityInterface entries refs)
    (constants : Assignment β V) (realizes : Realizes constants entries) :
    ∃ next : Assignment β V,
      Realizes next (quotientEnvironment refs entries) ∧
        Assignment.AgreesOn entries constants next := by
  let next := quotientAssignment refs constants
  have agrees : Assignment.AgreesOn entries constants next :=
    quotientAssignment_agrees fresh constants
  have reading : Reading next refs.certified := quotientAssignment_reading injective apart constants
  have old : Realizes next entries := realizes.of_agrees wellFormed agrees
  have ne (left right : Ix.QuotKind) (different : left ≠ right) : refs.ref left ≠ refs.ref right :=
    fun same => different (injective same)
  have eqType : entries.HasType refs.eq 1 Basis.Equality.type := equality.former
  -- Membership of each installed value in its published type.
  have member (kind : Ix.QuotKind) : ∀ levels, levels.length = (refs.entry kind).universes →
      ∀ env, next (refs.ref kind) levels ∈ˢ interp next levels env (refs.entry kind).type := by
    intro levels length env
    exact value_mem reading equality old kind.certified levels
      (by simpa only [QuotientRefs.entry_universes, ← Ix.QuotKind.certified_universes] using length)
      env
  -- The interface after each insertion, innermost first.
  let E₁ := entries.insert refs.type (refs.entry .type)
  let E₂ := E₁.insert refs.ctor (refs.entry .ctor)
  let E₃ := E₂.insert refs.lift (refs.entry .lift)
  have ctorType' : refs.ctor ≠ refs.type := ne .ctor .type (by decide)
  have liftCtor : refs.lift ≠ refs.ctor := ne .lift .ctor (by decide)
  have liftType' : refs.lift ≠ refs.type := ne .lift .type (by decide)
  have freshCtor₁ : E₁ refs.ctor = none := by
    simp only [E₁, Model.Environment.insert, if_neg ctorType']
    exact fresh .ctor
  have freshLift₁ : E₁ refs.lift = none := by
    simp only [E₁, Model.Environment.insert, if_neg liftType']
    exact fresh .lift
  have freshLift₂ : E₂ refs.lift = none := by
    simp only [E₂, Model.Environment.insert, if_neg liftCtor]
    exact freshLift₁
  have typeIn₁ : E₁.HasType refs.type 1 typeType :=
    ⟨_, Model.Environment.insert_same .., rfl, rfl⟩
  have typeIn₂ : E₂.HasType refs.type 1 typeType :=
    ⟨_, Model.Environment.insert_old freshCtor₁ (Model.Environment.insert_same ..), rfl, rfl⟩
  have ctorIn₂ : E₂.HasType refs.ctor 1 (ctorType refs.certified) :=
    ⟨_, Model.Environment.insert_same .., rfl, rfl⟩
  have typeIn₃ : E₃.HasType refs.type 1 typeType :=
    ⟨_, Model.Environment.insert_old freshLift₂
      (Model.Environment.insert_old freshCtor₁ (Model.Environment.insert_same ..)), rfl, rfl⟩
  have ctorIn₃ : E₃.HasType refs.ctor 1 (ctorType refs.certified) :=
    ⟨_, Model.Environment.insert_old freshLift₂ (Model.Environment.insert_same ..), rfl, rfl⟩
  have eqIn₂ : E₂.HasType refs.eq 1 Basis.Equality.type := by
    obtain ⟨entry, present, arity, type⟩ := eqType
    exact ⟨entry, Model.Environment.insert_old freshCtor₁
      (Model.Environment.insert_old (fresh .type) present), arity, type⟩
  have realizes₁ : Realizes next E₁ := by
    refine old.insert ⟨?_, member .type, (fun body hb => by cases hb), (fun body hb => by cases hb),
      (fun law hl => by cases hl), (fun fact hf => by cases hf)⟩
    intro levels _ env
    obtain ⟨_, formed⟩ := typeType_formed.{u,v} (E := entries)
    exact (formed V next old levels env
      (Context.valid_nil next levels env)).1
  have realizes₂ : Realizes next E₂ := by
    refine realizes₁.insert ⟨?_, member .ctor, (fun body hb => by cases hb),
      (fun body hb => by cases hb),
      (fun law hl => by cases hl), (fun fact hf => by cases hf)⟩
    intro levels _ env
    obtain ⟨_, formed⟩ := ctorType_formed.{u,v} (refs := refs.certified) typeIn₁
    exact (formed V next realizes₁ levels env
      (Context.valid_nil next levels env)).1
  have realizes₃ : Realizes next E₃ := by
    obtain ⟨_, formed⟩ := liftType_formed.{u,v} (refs := refs.certified) typeIn₂ eqIn₂
    refine realizes₂.insert ⟨?_, member .lift, (fun body hb => by cases hb),
      (fun body hb => by cases hb),
      ?_, (fun fact hf => by cases hf)⟩
    · intro levels _ env
      exact (formed V next realizes₂ levels env (Context.valid_nil next levels env)).1
    · intro law listed levels length env
      cases List.mem_singleton.mp listed
      match levels, length with
      | [u, w], _ => exact liftRule_eq reading equality old u w env
  obtain ⟨_, formed⟩ := indType_formed.{u,v} (refs := refs.certified) typeIn₃ ctorIn₃
  refine ⟨next, realizes₃.insert ⟨?_, member .ind, (fun body hb => by cases hb),
    (fun body hb => by cases hb), ?_, (fun fact hf => by cases hf)⟩, agrees⟩
  · intro levels _ env
    exact (formed V next realizes₃ levels env (Context.valid_nil next levels env)).1
  · intro law listed levels _ env
    cases List.mem_singleton.mp listed
    exact indRule_eq _ _ _ _

end Realization

/-! ### Production data of a quotient declaration -/

/-- The production data of one `.quot` declaration of the given kind: its address,
universe count, and declared type. -/
structure QuotientSpec (kind : Ix.QuotKind) where
  id : KId .anon
  lvls : UInt64
  sourceType : KExpr .anon

def QuotientSpec.constant {kind : Ix.QuotKind} (spec : QuotientSpec kind) : KConst .anon :=
  .quot () () kind spec.lvls spec.sourceType

private instance : LawfulBEq ByteArray where
  eq_of_beq {left right} h := by
    cases left
    cases right
    exact congrArg ByteArray.mk (eq_of_beq h)
  rfl {bytes} := beq_self_eq_true bytes.data

private instance : LawfulBEq Address where
  eq_of_beq {left right} h := by
    cases left
    cases right
    exact congrArg Address.mk (eq_of_beq h)
  rfl {addr} := by
    cases addr
    exact beq_self_eq_true (α := ByteArray) _

private theorem bind_success {α γ : Type} {action : TcM .anon α} {next : α → TcM .anon γ}
    {before after : TcState .anon} {result : γ}
    (accepted : EStateM.bind action next before = .ok result after) :
    ∃ value state, action before = .ok value state ∧ next value state = .ok result after := by
  cases run : action before with
  | error err failed => rw [EStateM.bind, run] at accepted; contradiction
  | ok value state =>
      rw [EStateM.bind, run] at accepted
      exact ⟨value, state, rfl, accepted⟩

private theorem anon_id (id : KId .anon) : (⟨id.addr, ()⟩ : KId .anon) = id := by
  cases id with
  | mk addr name => cases name; rfl

/-! ### The executed guard sequence -/

/-- A successful `checkQuotBody` passed exactly its four guards: the declared
kind is the one selected by the address, the universe count is the fixed one,
the declared type hashes to the canonical type, and `Quot.lift` ran the
`Eq`/`Eq.refl` prerequisite check from the same state. -/
theorem checkQuotBody_success {p : Primitives .anon} {expectedKind kind : Ix.QuotKind}
    {lvls : UInt64} {ty : KExpr .anon} {methods : Methods .anon} {before after : TcState .anon}
    (run : (RecM.checkQuotBody p expectedKind kind lvls ty).run methods before = .ok () after) :
    kind = expectedKind ∧ lvls = kind.universes ∧
      (ty.addr == (RecM.canonicalQuotType p kind).addr) = true ∧
      (kind = .lift → (RecM.checkEqType (m := .anon)).run methods before = .ok () after) ∧
      (kind ≠ .lift → after = before) := by
  unfold RecM.checkQuotBody at run
  by_cases mismatch : (kind != expectedKind) = true
  · simp only [mismatch, ↓reduceIte] at run
    cases run
  have same : kind = expectedKind := Ix.QuotKind.eq_of_bne_eq_false (Bool.eq_false_iff.mpr mismatch)
  simp only [mismatch, Bool.false_eq_true, ↓reduceIte] at run
  subst same
  refine ⟨rfl, ?_⟩
  cases kind with
  | lift =>
    dsimp only at run
    split at run
    · cases run
    rename_i arity
    split at run
    · cases run
    rename_i hash
    refine ⟨by simpa [Ix.QuotKind.universes] using Bool.eq_false_iff.mpr arity,
      by simpa [bne] using Bool.eq_false_iff.mpr hash, fun _ => ?_, fun h => absurd rfl h⟩
    simp only [show (Ix.QuotKind.lift == Ix.QuotKind.lift) = true from rfl, ↓reduceIte] at run
    exact run
  | type =>
    dsimp only at run
    split at run
    · cases run
    rename_i arity
    split at run
    · cases run
    rename_i hash
    refine ⟨by simpa [Ix.QuotKind.universes] using Bool.eq_false_iff.mpr arity,
      by simpa [bne] using Bool.eq_false_iff.mpr hash, (fun h => nomatch h), fun _ => ?_⟩
    simp only [show (Ix.QuotKind.type == Ix.QuotKind.lift) = false from rfl, Bool.false_eq_true,
      ↓reduceIte] at run
    cases run
    rfl
  | ctor =>
    dsimp only at run
    split at run
    · cases run
    rename_i arity
    split at run
    · cases run
    rename_i hash
    refine ⟨by simpa [Ix.QuotKind.universes] using Bool.eq_false_iff.mpr arity,
      by simpa [bne] using Bool.eq_false_iff.mpr hash, (fun h => nomatch h), fun _ => ?_⟩
    simp only [show (Ix.QuotKind.ctor == Ix.QuotKind.lift) = false from rfl, Bool.false_eq_true,
      ↓reduceIte] at run
    cases run
    rfl
  | ind =>
    dsimp only at run
    split at run
    · cases run
    rename_i arity
    split at run
    · cases run
    rename_i hash
    refine ⟨by simpa [Ix.QuotKind.universes] using Bool.eq_false_iff.mpr arity,
      by simpa [bne] using Bool.eq_false_iff.mpr hash, (fun h => nomatch h), fun _ => ?_⟩
    simp only [show (Ix.QuotKind.ind == Ix.QuotKind.lift) = false from rfl, Bool.false_eq_true,
      ↓reduceIte] at run
    cases run
    rfl

/-- A successful `checkQuot` selected the kind by the declared address, which
is therefore the reserved primitive address of that kind, and then passed the
body guards. -/
theorem checkQuot_success {id : KId .anon} {kind : Ix.QuotKind} {lvls : UInt64}
    {ty : KExpr .anon} {methods : Methods .anon} {before after : TcState .anon}
    (run : (RecM.checkQuot id kind lvls ty).run methods before = .ok () after) :
    id.addr = (before.prims.quot kind).addr ∧ lvls = kind.universes ∧
      (ty.addr == (RecM.canonicalQuotType before.prims kind).addr) = true ∧
      (kind = .lift → (RecM.checkEqType (m := .anon)).run methods before = .ok () after) ∧
      (kind ≠ .lift → after = before) := by
  unfold RecM.checkQuot at run
  simp only [ReaderT.run_bind] at run
  change EStateM.bind ((RecM.prims (m := .anon)).run methods) _ before = _ at run
  obtain ⟨p, primed, primsRun, run⟩ := bind_success run
  change EStateM.Result.ok before.prims before = _ at primsRun
  cases primsRun
  have dispatch (expectedKind : Ix.QuotKind)
      (selected : (id.addr == (before.prims.quot expectedKind).addr) = true)
      (rest : (RecM.checkQuotBody before.prims expectedKind kind lvls ty).run methods before =
        .ok () after) :
      id.addr = (before.prims.quot kind).addr ∧ lvls = kind.universes ∧
        (ty.addr == (RecM.canonicalQuotType before.prims kind).addr) = true ∧
        (kind = .lift → (RecM.checkEqType (m := .anon)).run methods before = .ok () after) ∧
        (kind ≠ .lift → after = before) := by
    obtain ⟨same, count, canonical, equality, unchanged⟩ := checkQuotBody_success rest
    subst same
    exact ⟨eq_of_beq selected, count, canonical, equality, unchanged⟩
  by_cases isType : (id.addr == before.prims.quotType.addr) = true
  · simp only [isType, ↓reduceIte] at run
    exact dispatch .type isType run
  simp only [isType, Bool.false_eq_true, ↓reduceIte] at run
  by_cases isCtor : (id.addr == before.prims.quotCtor.addr) = true
  · simp only [isCtor, ↓reduceIte] at run
    exact dispatch .ctor isCtor run
  simp only [isCtor, Bool.false_eq_true, ↓reduceIte] at run
  by_cases isLift : (id.addr == before.prims.quotLift.addr) = true
  · simp only [isLift, ↓reduceIte] at run
    exact dispatch .lift isLift run
  simp only [isLift, Bool.false_eq_true, ↓reduceIte] at run
  by_cases isInd : (id.addr == before.prims.quotInd.addr) = true
  · simp only [isInd, ↓reduceIte] at run
    exact dispatch .ind isInd run
  simp only [isInd, Bool.false_eq_true, ↓reduceIte] at run
  cases run

/-- The execution prefix of a successful quotient member check: validation,
the guard sequence, type inference, and the sort check. -/
structure QuotTypeTrace {kind : Ix.QuotKind} (spec : QuotientSpec kind) (methods : Methods .anon)
    (before : TcState .anon) where
  validated : TcState .anon
  guarded : TcState .anon
  inferred : KExpr .anon
  typeState : TcState .anon
  level : KUniv .anon
  afterSort : TcState .anon
  validationRun : (RecM.validateConstWellScoped spec.constant).run methods before = .ok () validated
  guardRun : (RecM.checkQuot spec.id kind spec.lvls spec.sourceType).run methods validated =
    .ok () guarded
  typeRun : (RecM.infer spec.sourceType).run methods guarded = .ok inferred typeState
  sortRun : (RecM.ensureSortDirect inferred).run methods typeState = .ok level afterSort

/-- Extract the executed prefix from a successful production member check. -/
theorem quot_type_trace {kind : Ix.QuotKind} {spec : QuotientSpec kind} {methods : Methods .anon}
    {before after : TcState .anon}
    (accepted : (RecM.checkConstMember spec.id spec.constant).run methods before = .ok () after) :
    Nonempty (QuotTypeTrace spec methods before) := by
  unfold RecM.checkConstMember at accepted
  simp only [QuotientSpec.constant, Mode.F.hasDups, Bool.false_eq_true, if_false,
    ReaderT.run_bind] at accepted
  change EStateM.bind ((RecM.validateConstWellScoped spec.constant).run methods) _ before = _
    at accepted
  obtain ⟨⟨⟩, validated, validationRun, accepted⟩ := bind_success accepted
  change EStateM.bind ((RecM.checkQuot spec.id kind spec.lvls spec.sourceType).run methods) _
    validated = _ at accepted
  obtain ⟨⟨⟩, guarded, guardRun, accepted⟩ := bind_success accepted
  change EStateM.bind ((RecM.infer spec.sourceType).run methods) _ guarded = _ at accepted
  obtain ⟨inferred, typeState, typeRun, accepted⟩ := bind_success accepted
  change EStateM.bind ((RecM.ensureSortDirect inferred).run methods) _ typeState = _ at accepted
  obtain ⟨level, afterSort, sortRun, _⟩ := bind_success accepted
  exact ⟨⟨validated, guarded, inferred, typeState, level, afterSort, validationRun, guardRun,
    typeRun, sortRun⟩⟩

/-- The guard facts of a trace, about the primitive table installed at the
validated state. -/
theorem QuotTypeTrace.guards {kind : Ix.QuotKind} {spec : QuotientSpec kind}
    {methods : Methods .anon} {before : TcState .anon}
    (trace : QuotTypeTrace spec methods before) :
    spec.id.addr = (trace.validated.prims.quot kind).addr ∧ spec.lvls = kind.universes ∧
      (spec.sourceType.addr == (RecM.canonicalQuotType trace.validated.prims kind).addr) = true :=
  let ⟨address, count, canonical, _, _⟩ := checkQuot_success trace.guardRun
  ⟨address, count, canonical⟩

/-- `Quot.lift` ran the `Eq`/`Eq.refl` prerequisite check from the validated state. -/
theorem QuotTypeTrace.equality {kind : Ix.QuotKind} {spec : QuotientSpec kind}
    {methods : Methods .anon} {before : TcState .anon}
    (trace : QuotTypeTrace spec methods before) (isLift : kind = .lift) :
    (RecM.checkEqType (m := .anon)).run methods trace.validated = .ok () trace.guarded :=
  (checkQuot_success trace.guardRun).2.2.2.1 isLift

/-! ### The `Eq`/`Eq.refl` prerequisite of `Quot.lift` -/

private theorem foldl_find_some {α γ : Type _} {pred : α → Bool} {f : α → γ} :
    ∀ {l : List α} {init : Option γ} {x : γ},
      l.foldl (fun acc a => if pred a then some (f a) else acc) init = some x →
      init = some x ∨ ∃ a ∈ l, pred a = true ∧ x = f a
  | [], _, _, h => .inl h
  | a :: l, init, x, h => by
      rw [List.foldl_cons] at h
      rcases foldl_find_some h with found | ⟨b, mem, pb, rfl⟩
      · by_cases pa : pred a = true
        · rw [if_pos pa] at found
          exact .inr ⟨a, List.mem_cons_self .., pa, (Option.some.inj found).symm⟩
        · rw [if_neg pa] at found
          exact .inl found
      · exact .inr ⟨b, List.mem_cons_of_mem _ mem, pb, rfl⟩

/-- The facts established by a successful `Eq`/`Eq.refl` prerequisite check
about the checker environment it inspected: a safe inductive record at the
reserved `Eq` address with one universe parameter, two parameters, one index,
a single constructor at the reserved `Eq.refl` address, and a type hashing to
the canonical equality type; and a safe constructor record at the reserved
`Eq.refl` address, of that family, with two parameters, no fields, and a type
hashing to the canonical reflexivity type. -/
structure EqualityPrerequisite (p : Primitives .anon) (env : KEnv .anon) : Prop where
  eq : ∃ (id : KId .anon) (name : Mode.anon.F Ix.Name) (levelParams : Mode.anon.F (Array Ix.Name))
    (block : KId .anon) (memberIdx : UInt64) (ty : KExpr .anon) (ctors : Array (KId .anon))
    (leanAll : Mode.anon.F (Array (KId .anon))),
    (id, KConst.indc name levelParams 1 2 1 false block memberIdx ty ctors leanAll) ∈
        env.consts.toList ∧
      id.addr = p.eq.addr ∧ ctors.size = 1 ∧ ctors[0]!.addr = p.eqRefl.addr ∧
      (ty.addr == (RecM.canonicalEqType (m := .anon)).addr) = true
  refl : ∃ (id : KId .anon) (name : Mode.anon.F Ix.Name) (levelParams : Mode.anon.F (Array Ix.Name))
    (induct : KId .anon) (ty : KExpr .anon),
    (id, KConst.ctor name levelParams false 1 induct 0 2 0 ty) ∈ env.consts.toList ∧
      id.addr = p.eqRefl.addr ∧ induct.addr = p.eq.addr ∧
      (ty.addr == (RecM.canonicalEqReflType p).addr) = true

/-- One guard of a `do` block: a successful run passed it and continued. -/
private theorem guard_success {c : Prop} [Decidable c] {α : Type} {e : TcError .anon}
    {rest : RecM .anon α} {methods : Methods .anon} {before after : TcState .anon} {a : α}
    (run : (if c then (do let _ ← (throw e : RecM .anon Unit); rest) else rest).run methods before =
      .ok a after) :
    ¬ c ∧ rest.run methods before = .ok a after := by
  by_cases h : c
  · rw [if_pos h] at run
    cases run
  · rw [if_neg h] at run
    exact ⟨h, run⟩

/-- The final guard of a `do` block: a successful run passed it and returned. -/
private theorem final_guard_success {c : Prop} [Decidable c] {e : TcError .anon}
    {methods : Methods .anon} {before after : TcState .anon}
    (run : (if c then (throw e : RecM .anon Unit) else pure ()).run methods before = .ok () after) :
    ¬ c ∧ after = before := by
  by_cases h : c
  · rw [if_pos h] at run
    cases run
  · rw [if_neg h] at run
    cases run
    exact ⟨h, rfl⟩

/-- A successful prerequisite check changes no state and establishes the
`Eq`/`Eq.refl` facts about the environment it inspected. -/
theorem checkEqType_success {methods : Methods .anon} {before after : TcState .anon}
    (run : (RecM.checkEqType (m := .anon)).run methods before = .ok () after) :
    after = before ∧ EqualityPrerequisite before.prims before.env := by
  unfold RecM.checkEqType at run
  rw [ReaderT.run_bind] at run
  change EStateM.bind ((RecM.prims (m := .anon)).run methods) _ before = _ at run
  obtain ⟨p, primed, primsRun, run⟩ := bind_success run
  change EStateM.Result.ok before.prims before = _ at primsRun
  cases primsRun
  rw [ReaderT.run_bind] at run
  change EStateM.bind ((get : RecM .anon (TcState .anon)).run methods) _ before = _ at run
  obtain ⟨state, got, getRun, run⟩ := bind_success run
  change EStateM.Result.ok before before = _ at getRun
  cases getRun
  dsimp only at run
  split at run
  case h_2 => cases run
  rename_i eqId eqC found
  split at run
  case h_2 => cases run
  rename_i name levelParams lvls params indices isUnsafe block memberIdx ty ctors leanAll
  obtain ⟨arity, run⟩ := guard_success run
  obtain ⟨parameters, run⟩ := guard_success run
  obtain ⟨indexed, run⟩ := guard_success run
  obtain ⟨safe, run⟩ := guard_success run
  obtain ⟨single, run⟩ := guard_success run
  obtain ⟨constructor, run⟩ := guard_success run
  obtain ⟨canonical, run⟩ := guard_success run
  rw [ReaderT.run_bind] at run
  change EStateM.bind ((get : RecM .anon (TcState .anon)).run methods) _ before = _ at run
  obtain ⟨state', got', getRun', run⟩ := bind_success run
  change EStateM.Result.ok before before = _ at getRun'
  cases getRun'
  split at run
  case h_2 => cases run
  rename_i reflC foundRefl
  split at run
  case h_2 => cases run
  rename_i reflName reflLevelParams reflUnsafe reflLvls induct cidx reflParams fields reflTy
  obtain ⟨metadata, run⟩ := guard_success run
  obtain ⟨reflCanonical, unchanged⟩ := final_guard_success run
  have eqMember : (eqId, KConst.indc name levelParams lvls params indices isUnsafe block memberIdx
      ty
      ctors leanAll) ∈ before.env.consts.toList ∧ (eqId.addr == before.prims.eq.addr) = true := by
    simp only [Std.HashMap.fold_eq_foldl_toList] at found
    rcases foldl_find_some (pred := fun (entry : KId .anon × KConst .anon) =>
        entry.1.addr == before.prims.eq.addr)
        (f := fun (entry : KId .anon × KConst .anon) => (entry.1, entry.2)) found with
      impossible | ⟨⟨id, constant⟩, member, selected, same⟩
    · cases impossible
    · cases same
      exact ⟨member, selected⟩
  have reflMember : (⟨before.prims.eqRefl.addr, ()⟩, KConst.ctor reflName reflLevelParams reflUnsafe
      reflLvls induct cidx reflParams fields reflTy) ∈ before.env.consts.toList := by
    simp only [Std.HashMap.fold_eq_foldl_toList] at foundRefl
    rcases foldl_find_some (pred := fun (entry : KId .anon × KConst .anon) =>
        entry.1.addr == before.prims.eqRefl.addr)
        (f := fun (entry : KId .anon × KConst .anon) => entry.2) foundRefl with
      impossible | ⟨⟨id, constant⟩, member, selected, same⟩
    · cases impossible
    · cases same
      have address : id.addr = before.prims.eqRefl.addr := eq_of_beq selected
      rw [← address, anon_id id]
      exact member
  simp only [Bool.or_eq_true, not_or] at metadata
  obtain ⟨⟨⟨⟨⟨unsafe', reflArity⟩, family⟩, index⟩, reflParameters⟩, reflFields⟩ := metadata
  refine ⟨unchanged, ?_, ?_⟩
  · have lvlsOne : lvls = 1 := by simpa using Bool.eq_false_iff.mpr arity
    have paramsTwo : params = 2 := by simpa using Bool.eq_false_iff.mpr parameters
    have indicesOne : indices = 1 := by simpa using Bool.eq_false_iff.mpr indexed
    have safeFalse : isUnsafe = false := Bool.eq_false_iff.mpr safe
    subst lvlsOne paramsTwo indicesOne safeFalse
    exact ⟨eqId, name, levelParams, block, memberIdx, ty, ctors, leanAll, eqMember.1,
      eq_of_beq eqMember.2, by simpa using Bool.eq_false_iff.mpr single,
      eq_of_beq (by simpa [bne] using Bool.eq_false_iff.mpr constructor),
      by simpa [bne] using Bool.eq_false_iff.mpr canonical⟩
  · have lvlsOne : reflLvls = 1 := by simpa using Bool.eq_false_iff.mpr reflArity
    have cidxZero : cidx = 0 := by simpa using Bool.eq_false_iff.mpr index
    have paramsTwo : reflParams = 2 := by simpa using Bool.eq_false_iff.mpr reflParameters
    have fieldsZero : fields = 0 := by simpa using Bool.eq_false_iff.mpr reflFields
    have safeFalse : reflUnsafe = false := Bool.eq_false_iff.mpr unsafe'
    subst lvlsOne cidxZero paramsTwo fieldsZero safeFalse
    exact ⟨_, reflName, reflLevelParams, induct, reflTy, reflMember, rfl,
      eq_of_beq (by simpa [bne] using Bool.eq_false_iff.mpr family),
      by simpa [bne] using Bool.eq_false_iff.mpr reflCanonical⟩

/-- The `Eq`/`Eq.refl` facts established while admitting `Quot.lift`, about
the environment at its validated state. -/
theorem QuotTypeTrace.equalityPrerequisite {kind : Ix.QuotKind} {spec : QuotientSpec kind}
    {methods : Methods .anon} {before : TcState .anon} (trace : QuotTypeTrace spec methods before)
    (isLift : kind = .lift) : EqualityPrerequisite trace.validated.prims trace.validated.env :=
  (checkEqType_success (trace.equality isLift)).2

/-- Store formation from the exact inference call made while admitting this
quotient constant, as for axioms. -/
def QuotTypeTrace.synthesisTypeCheck {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {kind : Ix.QuotKind} {spec : QuotientSpec kind} {fuel : Nat}
    {before : TcState .anon}
    (trace : QuotTypeTrace spec (methodsN fuel) before) {type : AExpr β} {level bound : VLevel}
    (inference : SynthesisInference resolve entries [] [] [] fuel trace.guarded spec.sourceType
      type (.sort level) bound)
    (reading : readScopedExpr? resolve [] spec.sourceType = some type.erase) :
    SynthesisTypeCheck resolve entries type level :=
  { fuel, before := trace.guarded, after := trace.typeState, source := spec.sourceType,
    result := trace.inferred, bound, inference, reading, run := trace.typeRun }

/-! ### Reading the canonical kernel types -/

@[simp] theorem readExpr?_mkAll {β : Type u} (resolve : Address → Option (ConstRef β))
    (name : Mode.anon.F Ix.Name) (bi : Mode.anon.F Lean.BinderInfo) (domain body : KExpr .anon) :
    readExpr? resolve (KExpr.mkAll name bi domain body) = do
      return .forallE (← readExpr? resolve domain) (← readExpr? resolve body) := rfl

@[simp] theorem readExpr?_mkApp {β : Type u} (resolve : Address → Option (ConstRef β))
    (fn arg : KExpr .anon) :
    readExpr? resolve (KExpr.mkApp fn arg) = do
      return .app (← readExpr? resolve fn) (← readExpr? resolve arg) := rfl

@[simp] theorem readExpr?_mkVar {β : Type u} (resolve : Address → Option (ConstRef β))
    (index : UInt64) (name : Mode.anon.F Ix.Name) :
    readExpr? resolve (KExpr.mkVar index name) = some (.bvar index.toNat) := rfl

@[simp] theorem readLevel_mkParam (index : UInt64) (name : Mode.anon.F Ix.Name) :
    readLevel (KUniv.mkParam index name) = .param index.toNat := rfl

@[simp] theorem readLevel_mkZero : readLevel (KUniv.mkZero (m := .anon)) = .zero := rfl

/-- The reserved quotient addresses resolve to the package references. -/
structure QuotientBinding {β : Type u} (resolve : Address → Option (ConstRef β))
    (prims : Primitives .anon) (refs : QuotientRefs β) : Prop where
  type : resolve prims.quotType.addr = some refs.type
  ctor : resolve prims.quotCtor.addr = some refs.ctor
  lift : resolve prims.quotLift.addr = some refs.lift
  ind : resolve prims.quotInd.addr = some refs.ind

theorem QuotientBinding.quot {β : Type u} {resolve : Address → Option (ConstRef β)}
    {prims : Primitives .anon} {refs : QuotientRefs β}
    (binding : QuotientBinding resolve prims refs)
    (kind : Ix.QuotKind) : resolve (prims.quot kind).addr = some (refs.ref kind) := by
  cases kind with
  | type => exact binding.type
  | ctor => exact binding.ctor
  | lift => exact binding.lift
  | ind => exact binding.ind

/-- The equality family admitted in the preceding interface: the reserved
`Eq`/`Eq.refl` addresses resolve to its references, whose entries carry the
canonical equality types together with the recursor. This is the static
binding discharged by the inductive admission of `Eq` (plan item WP5); until
then it is a premise of quotient admission, like `PrimitiveNatBinding`. -/
structure EqualityBinding {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (prims : Primitives .anon) (refs : QuotientRefs β) : Prop where
  eq : resolve prims.eq.addr = some refs.eq
  eqRefl : resolve prims.eqRefl.addr = some refs.eqRefl
  interface : EqualityInterface entries refs

/-- The canonical kernel type of each quotient kind reads to the certified
quotient syntax of that kind. -/
theorem canonicalQuotType_reads {β : Type u} {resolve : Address → Option (ConstRef β)}
    {prims : Primitives .anon} {refs : QuotientRefs β}
    (binding : QuotientBinding resolve prims refs)
    (equality : resolve prims.eq.addr = some refs.eq) (kind : Ix.QuotKind) :
    readExpr? resolve (RecM.canonicalQuotType prims kind) = some (refs.entryType kind).erase := by
  cases kind with
  | type => rfl
  | ctor =>
    simp [RecM.canonicalQuotType, RecM.canonicalAll, RecM.canonicalArrow, RecM.canonicalVar,
      RecM.canonicalQuotRelation, KExpr.mkAppN, binding.type, QuotientRefs.entryType,
      Quotient.Refs.entryType, Ix.QuotKind.certified, QuotientRefs.certified, Quotient.ctorType,
      Quotient.relationType, Quotient.applied, AExpr.erase, AExpr.appN]
  | lift =>
    simp [RecM.canonicalQuotType, RecM.canonicalAll, RecM.canonicalArrow, RecM.canonicalVar,
      RecM.canonicalQuotRelation, KExpr.mkAppN, binding.type, equality, QuotientRefs.entryType,
      Quotient.Refs.entryType, Ix.QuotKind.certified, QuotientRefs.certified, Quotient.liftType,
      Quotient.liftPrefix, Quotient.invariantType, Basis.Equality.applied, Quotient.relationType,
      Quotient.applied, AExpr.erase, AExpr.appN, AExpr.forallN]
  | ind =>
    simp [RecM.canonicalQuotType, RecM.canonicalAll, RecM.canonicalArrow, RecM.canonicalVar,
      RecM.canonicalQuotRelation, KExpr.mkAppN, binding.type, binding.ctor, QuotientRefs.entryType,
      Quotient.Refs.entryType, Ix.QuotKind.certified, QuotientRefs.certified, Quotient.indType,
      Quotient.indPrefix, Quotient.constructed, Quotient.relationType, Quotient.applied,
      AExpr.erase, AExpr.appN, AExpr.forallN]

/-- The reading of a declaration accepted by `checkQuot`, under address
faithfulness of the compared pair: the source type reads to the certified
syntax of its kind. -/
theorem QuotTypeTrace.reads {β : Type u} {resolve : Address → Option (ConstRef β)}
    {refs : QuotientRefs β} {kind : Ix.QuotKind} {spec : QuotientSpec kind}
    {methods : Methods .anon} {before : TcState .anon}
    (trace : QuotTypeTrace spec methods before)
    (binding : QuotientBinding resolve trace.validated.prims refs)
    (equality : resolve trace.validated.prims.eq.addr = some refs.eq)
    (faithful : spec.sourceType.AddrFaithful (RecM.canonicalQuotType trace.validated.prims kind)) :
    readExpr? resolve spec.sourceType = some (refs.entryType kind).erase := by
  rw [beq_readExpr? faithful trace.guards.2.2]
  exact canonicalQuotType_reads binding equality kind

/-! ### Quotient constants at work positions -/

/-- The four production quotient kinds. -/
def _root_.Ix.QuotKind.all : List Ix.QuotKind := [.type, .ctor, .lift, .ind]

theorem _root_.Ix.QuotKind.mem_all (kind : Ix.QuotKind) : kind ∈ Ix.QuotKind.all := by
  cases kind <;> simp [Ix.QuotKind.all]


/-- Syntactic provenance of one quotient constant at a real work position,
with the resources its guard sequence consumes: the primitive table installed
at the validated state, and address faithfulness of the compared pair. -/
structure QuotientObservation (env : Ixon.Env) (cfg : CheckCfg) (work : Array AnonWorkItem)
    (prims : Primitives .anon) {kind : Ix.QuotKind} (spec : QuotientSpec kind) where
  position : WorkPosition work (.standalone spec.id.addr)
  path : StandalonePrefix spec.id (position.state env cfg).checker spec.constant
  primitives : ∀ trace : QuotTypeTrace spec
    (methodsN (position.state env cfg).checker.recFuel.toNat) path.ready,
    trace.validated.prims = prims
  faithful : spec.sourceType.AddrFaithful (RecM.canonicalQuotType prims kind)

/-- Successful rows supply the guard facts of an observed quotient constant:
its address is the reserved one, its universe count is the fixed one, and its
type reads as the canonical kernel type under any reference map. -/
theorem QuotientObservation.guards {env : Ixon.Env} {cfg : CheckCfg} {work : Array AnonWorkItem}
    {prims : Primitives .anon} {kind : Ix.QuotKind} {spec : QuotientSpec kind}
    (observation : QuotientObservation env cfg work prims spec)
    (succeeded : ∀ result ∈ (runAnonCheckList cfg work.toList
      (initialAnonCheckLoopState env cfg)).results, result.err? = none) :
    spec.id.addr = (prims.quot kind).addr ∧ spec.lvls = kind.universes ∧
      ∀ {β : Type u} (resolve : Address → Option (ConstRef β)),
        readExpr? resolve spec.sourceType =
          readExpr? resolve (RecM.canonicalQuotType prims kind) := by
  obtain ⟨after, run⟩ := observation.position.check_success succeeded
  rw [anon_id] at run
  obtain ⟨trace⟩ := quot_type_trace (observation.path.member_success run)
  have primitives := observation.primitives trace
  obtain ⟨address, count, canonical⟩ := trace.guards
  rw [primitives] at address canonical
  exact ⟨address, count, fun _ => beq_readExpr? observation.faithful canonical⟩

/-- The four quotient constants of a run: the primitive table, the model
references, and one production declaration per kind. -/
structure QuotientPackage (β : Type u) where
  prims : Primitives .anon
  refs : QuotientRefs β
  spec : ∀ kind, QuotientSpec kind

/-- The declared addresses, in kind order. -/
def QuotientPackage.addresses {β : Type u} (package : QuotientPackage β) : List Address :=
  Ix.QuotKind.all.map fun kind => (package.spec kind).id.addr

theorem QuotientPackage.mem_addresses {β : Type u} (package : QuotientPackage β)
    (kind : Ix.QuotKind) :
    (package.spec kind).id.addr ∈ package.addresses :=
  List.mem_map.mpr ⟨kind, kind.mem_all, rfl⟩

/-- Model preservation composes along an interface extension. -/
theorem PreservesModels.trans {β : Type u} {before middle after : Model.Environment β}
    (extension : ∀ r entry, before r = some entry → middle r = some entry)
    (first : PreservesModels.{u,v} before middle) (second : PreservesModels.{u,v} middle after) :
    PreservesModels.{u,v} before after := by
  intro V _ constants realizes
  obtain ⟨next, nextModel, agrees⟩ := first V constants realizes
  obtain ⟨final, finalModel, finalAgrees⟩ := second V next nextModel
  refine ⟨final, finalModel, ?_⟩
  intro ref entry present levels
  exact (finalAgrees ref entry (extension ref entry present) levels).trans
    (agrees ref entry present levels)

/-! ### The environment fragment with the four quotient constants -/

/-- The production environment fragment of `ResolvedEnvironmentFragment`
extended by the four quotient constants. The initial interface is any closed
interface that contains the listed axioms and realizes the equality family;
the quotient entries are published right after it, at their canonical
standalone coordinates, and the definitions follow. All four quotient
constants must be present as accepted standalone work items. -/
structure QuotientEnvironmentFragment (env : Ixon.Env) (cfg : CheckCfg) where
  work : Array AnonWorkItem
  enumerated : buildAnonWork env = .ok work
  materializes : SourceMaterializes env
  initial : Model.Environment Address
  axioms : List (AxiomSpec Address)
  package : QuotientPackage Address
  definitions : List (DefinitionSpec Address)
  entries : Model.Environment Address
  canonical : ∀ spec ∈ axioms, spec.Canonical
  quotientCanonical : ∀ kind, package.refs.ref kind = .member (package.prims.quot kind).addr 0
  distinct : (axioms.map (·.id.addr) ++ package.addresses ++
    definitions.map (·.input.id.addr)).Nodup
  initialCanonical : CanonicalOutside initial
    (package.addresses ++ definitions.map (·.input.id.addr))
  axiomsInstalled : ∀ spec ∈ axioms, initial spec.ref = some spec.entry
  axiomRuns : ∀ spec ∈ axioms, Nonempty (ResolvedAxiomObservation env cfg work spec)
  quotientRuns : ∀ kind,
    Nonempty (QuotientObservation env cfg work package.prims (package.spec kind))
  equality : EqualityBinding env.resolve initial package.prims package.refs
  plan : ResolvedDefinitionPlan env cfg work (quotientEnvironment package.refs initial) definitions
    entries
  workCovered : ∀ item ∈ work,
    (∃ spec ∈ axioms, item = .standalone spec.id.addr) ∨
      (∃ kind, item = .standalone (package.spec kind).id.addr) ∨
      (∃ spec ∈ definitions, item = .standalone spec.input.id.addr) ∨
      (∃ block primary targets, item = .block block primary targets)

namespace QuotientEnvironmentFragment

variable {env : Ixon.Env} {cfg : CheckCfg} (fragment : QuotientEnvironmentFragment env cfg)

/-- The published quotient interface. -/
def published : Model.Environment Address :=
  quotientEnvironment fragment.package.refs fragment.initial

theorem serial_success {results : Array CheckResult}
    (accepted : checkEnvAnon env cfg = .ok results)
    (succeeded : ∀ result ∈ results, result.err? = none) :
    ∀ result ∈ (runAnonCheckList cfg fragment.work.toList
      (initialAnonCheckLoopState env cfg)).results, result.err? = none := by
  unfold checkEnvAnon at accepted
  rw [fragment.enumerated] at accepted
  cases accepted
  exact succeeded

/-- Every quotient constant of a successful run is declared at the reserved
address of its kind. -/
theorem address (serial : ∀ result ∈ (runAnonCheckList cfg fragment.work.toList
      (initialAnonCheckLoopState env cfg)).results, result.err? = none) (kind : Ix.QuotKind) :
    (fragment.package.spec kind).id.addr = (fragment.package.prims.quot kind).addr :=
  let ⟨observation⟩ := fragment.quotientRuns kind
  (observation.guards.{0} serial).1

/-- Every quotient constant of a successful run declares the fixed universe count. -/
theorem universes (serial : ∀ result ∈ (runAnonCheckList cfg fragment.work.toList
      (initialAnonCheckLoopState env cfg)).results, result.err? = none) (kind : Ix.QuotKind) :
    (fragment.package.spec kind).lvls = kind.universes :=
  let ⟨observation⟩ := fragment.quotientRuns kind
  (observation.guards.{0} serial).2.1

/-- The quotient references are pairwise distinct: their addresses are the
declared ones, which are listed without repetition. -/
theorem injective (serial : ∀ result ∈ (runAnonCheckList cfg fragment.work.toList
      (initialAnonCheckLoopState env cfg)).results, result.err? = none) :
    fragment.package.refs.Injective := by
  intro left right same
  rw [fragment.quotientCanonical left, fragment.quotientCanonical right] at same
  have addresses := (ConstRef.member.inj same).1
  rw [← fragment.address serial left, ← fragment.address serial right] at addresses
  have nodup : fragment.package.addresses.Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp fragment.distinct).1).2.1
  simp only [QuotientPackage.addresses, Ix.QuotKind.all, List.map_cons, List.map_nil,
    List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    not_false_eq_true,
    and_true] at nodup
  obtain ⟨⟨typeCtor, typeLift, typeInd⟩, ⟨ctorLift, ctorInd⟩, liftInd⟩ := nodup
  cases left <;> cases right <;> first
    | rfl
    | exact absurd addresses typeCtor
    | exact absurd addresses typeLift
    | exact absurd addresses typeInd
    | exact absurd addresses ctorLift
    | exact absurd addresses ctorInd
    | exact absurd addresses liftInd
    | exact absurd addresses.symm typeCtor
    | exact absurd addresses.symm typeLift
    | exact absurd addresses.symm typeInd
    | exact absurd addresses.symm ctorLift
    | exact absurd addresses.symm ctorInd
    | exact absurd addresses.symm liftInd

/-- Every quotient reference is fresh in the initial interface, whose entries
sit at canonical coordinates outside the declared addresses. -/
theorem fresh (serial : ∀ result ∈ (runAnonCheckList cfg fragment.work.toList
      (initialAnonCheckLoopState env cfg)).results, result.err? = none) :
    ∀ kind, fragment.initial (fragment.package.refs.ref kind) = none := by
  intro kind
  cases present : fragment.initial (fragment.package.refs.ref kind) with
  | none => rfl
  | some entry =>
    obtain ⟨addr, same, absent⟩ := fragment.initialCanonical _ entry present
    rw [fragment.quotientCanonical kind] at same
    obtain ⟨same, _⟩ := ConstRef.member.inj same
    subst same
    exact (absent (List.mem_append_left _ (fragment.address serial kind ▸
      fragment.package.mem_addresses kind))).elim

/-- A reference present in the initial interface is not a quotient reference. -/
theorem apart_of_present (serial : ∀ result ∈ (runAnonCheckList cfg fragment.work.toList
      (initialAnonCheckLoopState env cfg)).results, result.err? = none)
    {ref : ConstRef Address} {entry : ConstantEntry Address}
    (present : fragment.initial ref = some entry)
    (kind : Ix.QuotKind) : fragment.package.refs.ref kind ≠ ref := by
  intro same
  rw [← same, fragment.fresh serial kind] at present
  cases present

theorem apart (serial : ∀ result ∈ (runAnonCheckList cfg fragment.work.toList
      (initialAnonCheckLoopState env cfg)).results, result.err? = none) :
    fragment.package.refs.EqualityApart := by
  obtain ⟨eqEntry, eqPresent, _, _⟩ := fragment.equality.interface.former
  obtain ⟨reflEntry, reflPresent, _, _⟩ := fragment.equality.interface.reflexivity
  obtain ⟨recEntry, recPresent, _, _⟩ := fragment.equality.interface.elimination
  exact ⟨fragment.apart_of_present serial eqPresent, fragment.apart_of_present serial reflPresent,
    fragment.apart_of_present serial recPresent⟩

/-- The reserved quotient addresses resolve to the package references: each is
the declared address of an enumerated standalone item. -/
theorem binding (serial : ∀ result ∈ (runAnonCheckList cfg fragment.work.toList
      (initialAnonCheckLoopState env cfg)).results, result.err? = none) :
    QuotientBinding env.resolve fragment.package.prims fragment.package.refs := by
  have resolved (kind : Ix.QuotKind) :
      env.resolve (fragment.package.prims.quot kind).addr =
        some (fragment.package.refs.ref kind) := by
    obtain ⟨observation⟩ := fragment.quotientRuns kind
    rw [fragment.quotientCanonical kind, ← fragment.address serial kind]
    exact resolve_of_work_standalone fragment.materializes fragment.enumerated
      observation.position.mem
  exact ⟨resolved .type, resolved .ctor, resolved .lift, resolved .ind⟩

/-- The published quotient interface is closed whenever the initial one is. -/
theorem published_wf (wellFormed : fragment.initial.WF)
    (serial : ∀ result ∈ (runAnonCheckList cfg fragment.work.toList
      (initialAnonCheckLoopState env cfg)).results, result.err? = none) :
    fragment.published.WF := by
  obtain ⟨eqEntry, eqPresent, _, _⟩ := fragment.equality.interface.former
  exact quotientEnvironment_wf wellFormed (fragment.injective serial) (fragment.fresh serial)
    (by rw [eqPresent]; rfl)

/-- The published interface keeps every canonical coordinate outside the
pending definitions. -/
theorem published_canonical (serial : ∀ result ∈ (runAnonCheckList cfg fragment.work.toList
      (initialAnonCheckLoopState env cfg)).results, result.err? = none) :
    CanonicalOutside fragment.published (fragment.definitions.map (·.input.id.addr)) := by
  intro ref entry present
  rcases quotientEnvironment_cases present with old | ⟨kind, rfl, _⟩
  · obtain ⟨addr, same, absent⟩ := fragment.initialCanonical ref entry old
    exact ⟨addr, same, fun listed => absent (List.mem_append_right _ listed)⟩
  · refine ⟨(fragment.package.prims.quot kind).addr, fragment.quotientCanonical kind,
      fun listed => ?_⟩
    have disjoint := (List.nodup_append.mp fragment.distinct).2.2
    exact disjoint _ (List.mem_append_right _ (fragment.address serial kind ▸
      fragment.package.mem_addresses kind)) _ listed rfl

/-- The definition plan over the published interface is an atomic plan. -/
theorem atomicPlan (serial : ∀ result ∈ (runAnonCheckList cfg fragment.work.toList
      (initialAnonCheckLoopState env cfg)).results, result.err? = none) :
    AtomicDefinitionPlan env cfg fragment.work env.resolve fragment.published fragment.definitions
      fragment.entries :=
  fragment.plan.atomic fragment.materializes fragment.enumerated
    (fragment.published_canonical serial)
    (List.nodup_append.mp fragment.distinct).2.1

private theorem locations {work : Array AnonWorkItem} {before after : Model.Environment Address}
    {definitions : List (DefinitionSpec Address)}
    (plan : ResolvedDefinitionPlan env cfg work before definitions after) :
    ∀ spec ∈ definitions, ∃ position : WorkPosition work (.standalone spec.input.id.addr),
      Nonempty (StandalonePrefix spec.input.id (position.state env cfg).checker
        spec.input.constant) := by
  induction plan with
  | nil => simp
  | cons spec canonical position run tail ih =>
      intro candidate present
      rcases List.mem_cons.mp present with same | later
      · subst candidate
        exact ⟨position, ⟨run.path⟩⟩
      · exact ih candidate later

end QuotientEnvironmentFragment

/-- A successful `checkEnvAnon` run in the quotient fragment extends every
model of its initial interface, which must realize the equality family, while
preserving all its interpretations: the four quotient constants are admitted
with the certified quotient semantics, and the definitions follow. -/
theorem checkEnvAnon_preserves_model_quotient {env : Ixon.Env} {cfg : CheckCfg}
    (fragment : QuotientEnvironmentFragment env cfg) (wellFormed : fragment.initial.WF)
    {results : Array CheckResult} (accepted : checkEnvAnon env cfg = .ok results)
    (succeeded : ∀ result ∈ results, result.err? = none) :
    fragment.entries.WF ∧ PreservesModels.{0,v} fragment.initial fragment.entries := by
  have serial := fragment.serial_success accepted succeeded
  have publishedFormed := fragment.published_wf wellFormed serial
  obtain ⟨finalFormed, preserve⟩ := (fragment.atomicPlan serial).sound publishedFormed serial
  refine ⟨finalFormed, PreservesModels.trans
    (quotientEnvironment_extends (fragment.fresh serial)) ?_ preserve⟩
  intro V _ constants realizes
  exact extend_quotients wellFormed (fragment.injective serial) (fragment.apart serial)
    (fragment.fresh serial) fragment.equality.interface constants realizes

/-- The four quotient constants receive exactly the certified quotient entries
at their canonical coordinates. -/
theorem checkEnvAnon_quotient_published {env : Ixon.Env} {cfg : CheckCfg}
    (fragment : QuotientEnvironmentFragment env cfg)
    {results : Array CheckResult} (accepted : checkEnvAnon env cfg = .ok results)
    (succeeded : ∀ result ∈ results, result.err? = none) (kind : Ix.QuotKind) :
    fragment.entries (.member (fragment.package.spec kind).id.addr 0) =
      some (fragment.package.refs.entry kind) := by
  have serial := fragment.serial_success accepted succeeded
  have published := quotientEnvironment_same (entries := fragment.initial)
    (fragment.injective serial) kind
  rw [fragment.quotientCanonical kind, ← fragment.address serial kind] at published
  exact (fragment.atomicPlan serial).extends _ _ published

/-- Every standalone source record receives an interface entry whose type
reads the declaration reached by production lookup: axioms and quotient
constants with no body, definitions with the exact checked body. -/
theorem checkEnvAnon_represents_source_quotient {env : Ixon.Env} {cfg : CheckCfg}
    (fragment : QuotientEnvironmentFragment env cfg) (wellFormed : fragment.initial.WF)
    {results : Array CheckResult} (accepted : checkEnvAnon env cfg = .ok results)
    (succeeded : ∀ result ∈ results, result.err? = none) :
    ∀ addr, env.resolve addr = some (.member addr 0) →
      ∃ entry, fragment.entries (.member addr 0) = some entry ∧
        ∃ concrete : KConst .anon,
          (∃ before after, TcM.checkConst (⟨addr, ()⟩ : KId .anon) before = .ok () after ∧
            Nonempty (StandalonePrefix (⟨addr, ()⟩ : KId .anon) before concrete)) ∧
          DeclarationReading env.resolve concrete entry := by
  have serial := fragment.serial_success accepted succeeded
  have atomic := fragment.atomicPlan serial
  have publishedFormed := fragment.published_wf wellFormed serial
  have represented := atomic.represents publishedFormed serial
  intro addr resolved
  have listed := work_standalone_of_resolve fragment.materializes fragment.enumerated resolved
  rcases fragment.workCovered _ listed with ⟨spec, member, same⟩ | ⟨kind, same⟩ |
    ⟨spec, member, same⟩ | ⟨block, primary, targets, same⟩
  · cases AnonWorkItem.standalone.inj same
    obtain ⟨observation⟩ := fragment.axiomRuns spec member
    obtain ⟨after, run⟩ := observation.position.check_success serial
    refine ⟨spec.entry, ?_, spec.constant,
      ⟨(observation.position.state env cfg).checker, after, run, ?_⟩,
      observation.reads, rfl, rfl⟩
    · rw [← fragment.canonical spec member]
      exact atomic.extends _ _ (quotientEnvironment_old (fragment.fresh serial)
        (fragment.axiomsInstalled spec member))
    · simpa only [anon_id] using Nonempty.intro observation.path
  · cases AnonWorkItem.standalone.inj same
    obtain ⟨observation⟩ := fragment.quotientRuns kind
    obtain ⟨after, run⟩ := observation.position.check_success serial
    obtain ⟨_, count, reads⟩ := observation.guards.{0} serial
    refine ⟨fragment.package.refs.entry kind,
      checkEnvAnon_quotient_published fragment accepted succeeded kind,
      (fragment.package.spec kind).constant,
      ⟨(observation.position.state env cfg).checker, after, run, ?_⟩, ?_, ?_, rfl⟩
    · simpa only [anon_id] using Nonempty.intro observation.path
    · exact (reads env.resolve).trans
        (canonicalQuotType_reads (fragment.binding serial) fragment.equality.eq kind)
    · simp only [QuotientRefs.entry_universes, QuotientSpec.constant, KConst.lvls, count]
  · cases AnonWorkItem.standalone.inj same
    obtain ⟨resolvedSpec, installed, valueReads, typeReads⟩ := represented spec member
    have same : spec.ref = .member spec.input.id.addr 0 :=
      Option.some.inj (resolvedSpec.symm.trans resolved)
    obtain ⟨position, path⟩ := QuotientEnvironmentFragment.locations fragment.plan spec member
    obtain ⟨after, run⟩ := position.check_success serial
    refine ⟨spec.entry, ?_, spec.input.constant,
      ⟨(position.state env cfg).checker, after, run, ?_⟩, typeReads, rfl, spec.body, rfl,
      valueReads⟩
    · rw [← same]
      exact installed
    · simpa only [anon_id] using path
  · cases same

/-- No declaration can inhabit a type interpreted as empty in the initial
interface, such as `False`. -/
theorem checkEnvAnon_no_false_quotient {env : Ixon.Env} {cfg : CheckCfg}
    (fragment : QuotientEnvironmentFragment env cfg) (wellFormed : fragment.initial.WF)
    {results : Array CheckResult} (accepted : checkEnvAnon env cfg = .ok results)
    (succeeded : ∀ result ∈ results, result.err? = none)
    {V : Type v} [SetTheory V] (initialValues : Assignment Address V)
    (initialModel : Realizes initialValues fragment.initial)
    {falseAddr : Address} {falseEntry : ConstantEntry Address}
    (hasFalse : fragment.initial (.member falseAddr 0) = some falseEntry)
    (falseEmpty : initialValues (.member falseAddr 0) [] = SetTheory.empty)
    {ref : ConstRef Address} {entry : ConstantEntry Address}
    (present : fragment.entries ref = some entry)
    (isFalse : entry.type.erase = .const (.member falseAddr 0) []) : False := by
  obtain ⟨_, preserve⟩ :=
    checkEnvAnon_preserves_model_quotient fragment wellFormed accepted succeeded
  obtain ⟨values, model, agrees⟩ := preserve V initialValues initialModel
  have emptyValue : values (.member falseAddr 0) [] = SetTheory.empty :=
    (agrees _ _ hasFalse []).trans falseEmpty
  have typeEq := AExpr.eq_const_of_erase_eq isFalse
  have member := model.member ref entry present (List.replicate entry.universes 0)
    (by simp) (fun _ => SetTheory.empty)
  rw [typeEq] at member
  simp only [interp, List.map_nil, emptyValue] at member
  exact SetTheory.not_mem_empty _ member

end Ix.Kernel.Consistency
