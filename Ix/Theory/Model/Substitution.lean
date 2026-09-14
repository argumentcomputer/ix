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

/-- Instantiate a typed body using the actual domain of the removed
binder. Both the substituted term and type retain hereditary validity. -/
theorem TypingClaim.inst {entries : Environment β} {context : Context β}
    {term type argument domain : AExpr β}
    (body : TypingClaim.{u,v} entries (context.push domain) term type)
    (value : TypingClaim.{u,v} entries context argument domain) :
    TypingClaim.{u,v} entries context (term.inst argument) (type.inst argument) := by
  intro V _ constants realizes levels env valid
  obtain ⟨argumentValid, domainValid, argumentMember⟩ := value V constants realizes levels env valid
  obtain ⟨termValid, typeValid, member⟩ := body V constants realizes levels
    (Valuation.cons (interp constants levels env argument) env) (valid.push domainValid argumentMember)
  refine ⟨?_, ?_, ?_⟩
  · apply wellDenoted_inst
    · simpa using argumentValid
    · simpa using termValid
  · apply wellDenoted_inst
    · simpa using argumentValid
    · simpa using typeValid
  · simpa only [interp_inst, Valuation.skip_zero, Valuation.insert_zero] using member

/-- Checking may defer validity of its expected type, even through
substitution: validity of the instantiated type supplies the body premise. -/
theorem CheckingClaim.inst {entries : Environment β} {context : Context β}
    {term type argument domain : AExpr β}
    (body : CheckingClaim.{u,v} entries (context.push domain) term type)
    (value : TypingClaim.{u,v} entries context argument domain) :
    CheckingClaim.{u,v} entries context (term.inst argument) (type.inst argument) := by
  intro V _ constants realizes levels env valid expected
  obtain ⟨argumentValid, domainValid, argumentMember⟩ := value V constants realizes levels env valid
  have typeValid := wellDenoted_of_inst type argument constants levels env 0 expected
  obtain ⟨termValid, member⟩ := body V constants realizes levels
    (Valuation.cons (interp constants levels env argument) env) (valid.push domainValid argumentMember)
    (by simpa only [Valuation.skip_zero, Valuation.insert_zero] using typeValid)
  refine ⟨?_, ?_⟩
  · apply wellDenoted_inst
    · simpa using argumentValid
    · simpa using termValid
  · simpa only [interp_inst, Valuation.skip_zero, Valuation.insert_zero] using member

theorem ConversionClaim.inst {entries : Environment β} {context : Context β}
    {left right argument domain : AExpr β}
    (body : ConversionClaim.{u,v} entries (context.push domain) left right)
    (value : TypingClaim.{u,v} entries context argument domain) :
    ConversionClaim.{u,v} entries context (left.inst argument) (right.inst argument) := by
  intro V _ constants realizes levels env valid
  have argumentTyped := value V constants realizes levels env valid
  simpa only [interp_inst, Valuation.skip_zero, Valuation.insert_zero] using
    body V constants realizes levels (Valuation.cons (interp constants levels env argument) env)
      (valid.push argumentTyped.2.1 argumentTyped.2.2)

end Ix.Theory.Model
