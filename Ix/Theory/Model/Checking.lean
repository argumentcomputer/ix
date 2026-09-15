/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Model.Judgment

/-!
# Checking against a formed type

Inference of a lambda constructs a dependent function type from the body's
inferred type. It does not independently infer the sort of that codomain.
`CheckingClaim` defers hereditary validity of the expected type until the
declaration's separate type check establishes it. Its rule producers still
quantify over every dependency model, level valuation, and valid context.
-/

namespace Ix.Theory.Model

open SetTheory SetModel Certified

universe u v
variable {β : Type u} {entries : Environment β} {Γ : Context β}

def CheckingClaim (entries : Environment β) (Γ : Context β) (e A : AExpr β) : Prop :=
  ∀ (V : Type v) [SetTheory V] (constants : Assignment β V),
    Realizes constants entries → ∀ levels env, Γ.Valid constants levels env →
      WellDenoted constants levels env A →
        WellDenoted constants levels env e ∧
          interp constants levels env e ∈ˢ interp constants levels env A

theorem TypingClaim.checking {e A : AExpr β} (typed : TypingClaim.{u,v} entries Γ e A) :
    CheckingClaim.{u,v} entries Γ e A := by
  intro V _ constants realizes levels env valid _
  have checked := typed V constants realizes levels env valid
  exact ⟨checked.1, checked.2.2⟩

/-- A synthesized function supplies the domain's hereditary validity, so its
argument may be checked without a separate universe-formation derivation. -/
theorem TypingClaim.appChecking {f a A B : AExpr β} {condition : PropWhen}
    (function : TypingClaim.{u,v} entries Γ f (.forallE condition A B))
    (argument : CheckingClaim.{u,v} entries Γ a A) :
    TypingClaim.{u,v} entries Γ (.app f a) (B.inst a) := by
  apply function.app
  intro V _ constants realizes levels env valid
  have domainValid := (function V constants realizes levels env valid).2.1.1
  obtain ⟨argumentValid, member⟩ := argument V constants realizes levels env valid domainValid
  exact ⟨argumentValid, domainValid, member⟩

namespace CheckingClaim

theorem typing {e A : AExpr β} {level : VLevel}
    (checked : CheckingClaim.{u,v} entries Γ e A)
    (formed : TypingClaim.{u,v} entries Γ A (.sort level)) :
    TypingClaim.{u,v} entries Γ e A := by
  intro V _ constants realizes levels env valid
  have typeValid := (formed V constants realizes levels env valid).1
  have result := checked V constants realizes levels env valid typeValid
  exact ⟨result.1, typeValid, result.2⟩

theorem typingSort {e : AExpr β} {level : VLevel}
    (checked : CheckingClaim.{u,v} entries Γ e (.sort level)) :
    TypingClaim.{u,v} entries Γ e (.sort level) :=
  checked.typing (TypingClaim.sort level)

/-- The expected Pi supplies a uniform codomain universe and hereditary
validity, including the Prop regime when the domain is empty. -/
theorem lam {A B body : AExpr β} {condition : PropWhen}
    (checked : CheckingClaim.{u,v} entries (Γ.push A) body B) :
    CheckingClaim.{u,v} entries Γ (.lam condition A body) (.forallE condition A B) := by
  intro V _ constants realizes levels env valid formed
  obtain ⟨domainValid, bodyValid, codomainLevel, regimeAgrees, inUniverse⟩ := formed
  have bodyChecked x hx := checked V constants realizes levels (Valuation.cons x env)
    (valid.push domainValid hx) (bodyValid x hx)
  refine ⟨⟨domainValid, fun x hx => (bodyChecked x hx).1, codomainLevel,
    (fun x => interp constants levels (Valuation.cons x env) B), regimeAgrees,
    fun x hx => ⟨(bodyChecked x hx).2, inUniverse x hx⟩⟩, ?_⟩
  exact lamR_mem (fun x hx => (bodyChecked x hx).2)

end CheckingClaim
end Ix.Theory.Model
