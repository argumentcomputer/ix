/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Model.Checking

/-!
Substitution in the semantic judgments. The argument's typing supplies the
domain membership needed to extend a valid context. Hereditary validity of
an instantiated expected type can also be transported back to the original
body at that same argument value, which permits substitution in checking.
-/

namespace Ix.Theory.Model

open SetTheory SetModel

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

/-- Substitution cannot hide an invalid original subexpression. This
direction needs no validity premise for the argument, since an original
bound variable is hereditarily valid at every valuation. -/
theorem wellDenoted_of_inst (term argument : AExpr β) (constants : Assignment β V)
    (levels : List Nat) (env : Nat → V) (cutoff : Nat)
    (valid : WellDenoted constants levels env (term.inst argument cutoff)) :
    WellDenoted constants levels
      (Valuation.insert cutoff (interp constants levels (Valuation.skip cutoff 0 env) argument) env) term := by
  induction term generalizing cutoff env with
  | bvar index => trivial
  | app fn arg ihFn ihArg =>
      obtain ⟨fnValid, argValid, level, domain, body, fnMember, argMember, bodyBound⟩ := valid
      exact ⟨ihFn env cutoff fnValid, ihArg env cutoff argValid, level, domain, body,
        by simpa only [interp_inst] using fnMember,
        by simpa only [interp_inst] using argMember, bodyBound⟩
  | lam condition domain body ihDomain ihBody =>
      obtain ⟨domainValid, bodyValid, level, types, agrees, members⟩ := valid
      refine ⟨ihDomain env cutoff domainValid, ?_, level, types, agrees, ?_⟩
      · intro x member
        have inner := ihBody (Valuation.cons x env) (cutoff + 1)
          (bodyValid x (by simpa only [interp_inst] using member))
        simpa only [Valuation.skip_succ_cons, Valuation.insert_cons] using inner
      · intro x member
        simpa only [interp_inst, Valuation.skip_succ_cons, Valuation.insert_cons] using
          members x (by simpa only [interp_inst] using member)
  | forallE condition domain body ihDomain ihBody =>
      obtain ⟨domainValid, bodyValid, level, agrees, members⟩ := valid
      refine ⟨ihDomain env cutoff domainValid, ?_, level, agrees, ?_⟩
      · intro x member
        have inner := ihBody (Valuation.cons x env) (cutoff + 1)
          (bodyValid x (by simpa only [interp_inst] using member))
        simpa only [Valuation.skip_succ_cons, Valuation.insert_cons] using inner
      · intro x member
        simpa only [interp_inst, Valuation.skip_succ_cons, Valuation.insert_cons] using
          members x (by simpa only [interp_inst] using member)
  | proj ref field major ih => exact ih env cutoff valid
  | _ => trivial

theorem wellDenoted_inst_iff (term argument : AExpr β) (constants : Assignment β V)
    (levels : List Nat) (env : Nat → V) (cutoff : Nat)
    (argumentValid : WellDenoted constants levels (Valuation.skip cutoff 0 env) argument) :
    WellDenoted constants levels env (term.inst argument cutoff) ↔
      WellDenoted constants levels
        (Valuation.insert cutoff (interp constants levels (Valuation.skip cutoff 0 env) argument) env) term :=
  ⟨wellDenoted_of_inst term argument constants levels env cutoff,
    wellDenoted_inst _ _ _ _ _ _ argumentValid⟩

theorem Context.Valid.tail {constants : Assignment β V} {levels : List Nat}
    {context : Context β} {domain : AExpr β} {env : Nat → V}
    (valid : (context.push domain).Valid constants levels env) :
    context.Valid constants levels (Valuation.skip 1 0 env) := by
  intro index type found
  have after := valid (index + 1) (type.liftN 1) (by
    simp only [Context.push, List.getElem?_cons_succ, List.getElem?_map, found, Option.map_some])
  simpa only [wellDenoted_liftN, interp_liftN, Valuation.skip, Nat.not_lt_zero, ↓reduceIte,
    Nat.add_comm 1 index] using after

theorem Context.Valid.head {constants : Assignment β V} {levels : List Nat}
    {context : Context β} {domain : AExpr β} {env : Nat → V}
    (valid : (context.push domain).Valid constants levels env) :
    WellDenoted constants levels (Valuation.skip 1 0 env) domain ∧
      env 0 ∈ˢ interp constants levels (Valuation.skip 1 0 env) domain := by
  simpa only [wellDenoted_liftN, interp_liftN] using
    valid 0 (domain.liftN 1) (by simp only [Context.push, List.getElem?_cons_zero])

/-- Remove an outer parameter while retaining later dependent binders.
Each retained binder's domain is substituted in its own preceding context;
the argument remains expressed in the base context throughout. -/
inductive ContextSubstitution (base : Context β) (domain argument : AExpr β) :
    Context β → Context β → Nat → Prop
  | root : ContextSubstitution base domain argument (base.push domain) base 0
  | push {source target cutoff} (prior : ContextSubstitution base domain argument source target cutoff)
      (binder : AExpr β) :
      ContextSubstitution base domain argument (source.push binder)
        (target.push (binder.inst argument cutoff)) (cutoff + 1)

theorem ContextSubstitution.base_valid {base source target : Context β}
    {domain argument : AExpr β} {cutoff : Nat}
    (substitution : ContextSubstitution base domain argument source target cutoff)
    {constants : Assignment β V} {levels : List Nat} {env : Nat → V}
    (valid : target.Valid constants levels env) :
    base.Valid constants levels (Valuation.skip cutoff 0 env) := by
  induction substitution generalizing env with
  | root => simpa only [Valuation.skip_zero] using valid
  | @push source target cutoff prior binder ih =>
      have shifted : Valuation.skip cutoff 0 (Valuation.skip 1 0 env) =
          Valuation.skip (cutoff + 1) 0 env := by
        funext index
        simp only [Valuation.skip, Nat.not_lt_zero, ↓reduceIte]
        congr 1
        omega
      exact shifted ▸ ih valid.tail

theorem ContextSubstitution.source_valid {entries : Environment β} {base source target : Context β}
    {domain argument : AExpr β} {cutoff : Nat}
    (substitution : ContextSubstitution base domain argument source target cutoff)
    (value : TypingClaim.{u,v} entries base argument domain)
    {constants : Assignment β V} (realizes : Realizes constants entries)
    {levels : List Nat} {env : Nat → V} (valid : target.Valid constants levels env) :
    source.Valid constants levels
      (Valuation.insert cutoff (interp constants levels (Valuation.skip cutoff 0 env) argument) env) := by
  induction substitution generalizing env with
  | root =>
      have argumentTyped := value V constants realizes levels env valid
      simpa only [Valuation.skip_zero, Valuation.insert_zero] using
        valid.push argumentTyped.2.1 argumentTyped.2.2
  | @push source target cutoff prior binder ih =>
      have tailValid := ih valid.tail
      have originalDomain := wellDenoted_of_inst binder argument constants levels
        (Valuation.skip 1 0 env) cutoff valid.head.1
      have originalMember := valid.head.2
      rw [interp_inst] at originalMember
      have pushed := tailValid.push originalDomain originalMember
      have envCons : Valuation.cons (env 0) (Valuation.skip 1 0 env) = env := by
        funext index
        cases index <;> simp [Valuation.skip, Nat.add_comm]
      rw [← Valuation.insert_cons, ← Valuation.skip_succ_cons cutoff (env 0), envCons] at pushed
      exact pushed

/-- Substitute beneath an arbitrary retained dependent prefix. The context
relation updates every later parameter's type before that parameter is used. -/
theorem TypingClaim.instAt {entries : Environment β} {base source target : Context β}
    {term type argument domain : AExpr β} {cutoff : Nat}
    (body : TypingClaim.{u,v} entries source term type)
    (value : TypingClaim.{u,v} entries base argument domain)
    (substitution : ContextSubstitution base domain argument source target cutoff) :
    TypingClaim.{u,v} entries target (term.inst argument cutoff) (type.inst argument cutoff) := by
  intro V _ constants realizes levels env valid
  have argumentValid := (value V constants realizes levels _ (substitution.base_valid valid)).1
  obtain ⟨termValid, typeValid, member⟩ :=
    body V constants realizes levels _ (substitution.source_valid value realizes valid)
  exact ⟨wellDenoted_inst _ _ _ _ _ _ argumentValid termValid,
    wellDenoted_inst _ _ _ _ _ _ argumentValid typeValid, by simpa only [interp_inst] using member⟩

theorem CheckingClaim.instAt {entries : Environment β} {base source target : Context β}
    {term type argument domain : AExpr β} {cutoff : Nat}
    (body : CheckingClaim.{u,v} entries source term type)
    (value : TypingClaim.{u,v} entries base argument domain)
    (substitution : ContextSubstitution base domain argument source target cutoff) :
    CheckingClaim.{u,v} entries target (term.inst argument cutoff) (type.inst argument cutoff) := by
  intro V _ constants realizes levels env valid expected
  have argumentValid := (value V constants realizes levels _ (substitution.base_valid valid)).1
  obtain ⟨termValid, member⟩ :=
    body V constants realizes levels _ (substitution.source_valid value realizes valid)
      (wellDenoted_of_inst _ _ _ _ _ _ expected)
  exact ⟨wellDenoted_inst _ _ _ _ _ _ argumentValid termValid,
    by simpa only [interp_inst] using member⟩

theorem ConversionClaim.instAt {entries : Environment β} {base source target : Context β}
    {left right argument domain : AExpr β} {cutoff : Nat}
    (body : ConversionClaim.{u,v} entries source left right)
    (value : TypingClaim.{u,v} entries base argument domain)
    (substitution : ContextSubstitution base domain argument source target cutoff) :
    ConversionClaim.{u,v} entries target (left.inst argument cutoff) (right.inst argument cutoff) := by
  intro V _ constants realizes levels env valid
  simpa only [interp_inst] using
    body V constants realizes levels _ (substitution.source_valid value realizes valid)

/-- Instantiate a typed body using the actual domain of the removed
binder. Both the substituted term and type retain hereditary validity. -/
theorem TypingClaim.inst {entries : Environment β} {context : Context β}
    {term type argument domain : AExpr β}
    (body : TypingClaim.{u,v} entries (context.push domain) term type)
    (value : TypingClaim.{u,v} entries context argument domain) :
    TypingClaim.{u,v} entries context (term.inst argument) (type.inst argument) :=
  body.instAt value .root

/-- Checking may defer validity of its expected type, even through
substitution: validity of the instantiated type supplies the body premise. -/
theorem CheckingClaim.inst {entries : Environment β} {context : Context β}
    {term type argument domain : AExpr β}
    (body : CheckingClaim.{u,v} entries (context.push domain) term type)
    (value : TypingClaim.{u,v} entries context argument domain) :
    CheckingClaim.{u,v} entries context (term.inst argument) (type.inst argument) :=
  body.instAt value .root

theorem ConversionClaim.inst {entries : Environment β} {context : Context β}
    {left right argument domain : AExpr β}
    (body : ConversionClaim.{u,v} entries (context.push domain) left right)
    (value : TypingClaim.{u,v} entries context argument domain) :
    ConversionClaim.{u,v} entries context (left.inst argument) (right.inst argument) :=
  body.instAt value .root

end Ix.Theory.Model
