/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.SynthesisDerivation

/-! The semantic induction invariant retains checked binder children and
application arguments. It is proved from production inference; no source
support constructor takes this invariant as an input. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- A strengthening of typing that is closed under dependent substitution.
The syntactic children are essential when substitution exposes a lambda. -/
inductive HereditaryTyping {β : Type u} (entries : Model.Environment β) :
    Model.Context β → AExpr β → AExpr β → Prop
  | atom {context term type} (typed : TypingClaim.{u,v} entries context term type)
      (shape : BetaAtom term) : HereditaryTyping entries context term type
  | bvar {context index type} (typed : TypingClaim.{u,v} entries context (.bvar index) type)
      (atIndex : context[index]? = some type) : HereditaryTyping entries context (.bvar index) type
  | forallE {context condition domain body type domainLevel bodyLevel}
      (typed : TypingClaim.{u,v} entries context (.forallE condition domain body) type)
      (domainCheck : HereditaryTyping entries context domain (.sort domainLevel))
      (bodyCheck : HereditaryTyping entries (context.push domain) body (.sort bodyLevel))
      (conditionAgrees : condition = Certified.zeroCondition bodyLevel) :
      HereditaryTyping entries context (.forallE condition domain body) type
  | lam {context condition domain body codomain}
      (typed : TypingClaim.{u,v} entries context (.lam condition domain body) (.forallE condition domain codomain))
      (inner : HereditaryTyping entries (context.push domain) body codomain) :
      HereditaryTyping entries context (.lam condition domain body) (.forallE condition domain codomain)
  | app {context fn arg condition domain body}
      (function : HereditaryTyping entries context fn (.forallE condition domain body))
      (argument : HereditaryTyping entries context arg domain) :
      HereditaryTyping entries context (.app fn arg) (body.inst arg)
  | convert {context term sourceType resultType level}
      (prior : HereditaryTyping entries context term sourceType)
      (rigid : AExpr.HeadRigid sourceType resultType)
      (converted : ConversionClaim.{u,v} entries context sourceType resultType)
      (formed : TypingClaim.{u,v} entries context resultType (.sort level)) :
      HereditaryTyping entries context term resultType

namespace HereditaryTyping

variable {β : Type u} {entries : Model.Environment β}

theorem typing {context : Model.Context β} {term type : AExpr β}
    (checked : HereditaryTyping.{u,v} entries context term type) :
    TypingClaim.{u,v} entries context term type := by
  induction checked with
  | atom typed | bvar typed | forallE typed | lam typed => exact typed
  | app _ _ function argument => exact function.appChecking argument.checking
  | convert _ _ converted formed prior => exact prior.conv formed converted

theorem lambdaType {context : Model.Context β} {term type : AExpr β}
    (checked : HereditaryTyping.{u,v} entries context term type)
    {condition : Certified.PropWhen} {domain body : AExpr β}
    (same : term = .lam condition domain body) :
    ∃ codomain, type = .forallE condition domain codomain := by
  induction checked with
  | atom _ shape => exact False.elim (shape.not_lam _ _ _ same)
  | bvar | forallE | app => cases same
  | lam => cases same; exact ⟨_, rfl⟩
  | convert _ rigid _ _ ih =>
      obtain ⟨codomain, typeEq⟩ := ih same
      exact ⟨codomain, (rigid (by simp only [typeEq]; intro fn arg same; cases same)).trans typeEq⟩

theorem lambdaPrefix {context : Model.Context β} {term type : AExpr β}
    (checked : HereditaryTyping.{u,v} entries context term type) :
    LambdaPrefix term type term.lambdaDepth := by
  induction checked with
  | atom _ shape => cases shape <;> exact .zero _ _
  | bvar | forallE | app => exact .zero _ _
  | lam _ _ ih => exact .lam ih
  | @convert context term sourceType resultType level prior rigid converted formed ih =>
      cases term with
      | lam condition domain body =>
          obtain ⟨_, typeEq⟩ := prior.lambdaType rfl
          have fixed := rigid (by simp only [typeEq]; intro fn arg same; cases same)
          simpa only [fixed] using ih
      | _ => exact .zero _ _

theorem lambdaSpine {context : Model.Context β} {term type : AExpr β}
    (checked : HereditaryTyping.{u,v} entries context term type) :
    LambdaSpineTyping.{u,v} entries context term type := by
  induction checked with
  | atom _ shape =>
      exact .non_application (by cases shape <;> intro fn arg same <;> cases same) shape.not_lam
  | bvar | forallE =>
      exact .non_application (by intro fn arg same; cases same) (by intro condition domain body same; cases same)
  | @lam context condition domain body codomain typed inner _ =>
      exact .lam typed (.lam inner.lambdaPrefix)
  | app function argument functionSpine _ => exact functionSpine.app argument.typing
  | convert _ rigid converted formed prior => exact prior.convert rigid converted formed

theorem weakenAt {source target : Model.Context β} {cutoff : Nat} {term type : AExpr β}
    (checked : HereditaryTyping.{u,v} entries source term type)
    (insertion : ContextInsertion source target cutoff) :
    HereditaryTyping.{u,v} entries target (term.liftN 1 cutoff) (type.liftN 1 cutoff) := by
  induction checked generalizing target cutoff with
  | atom typed shape => exact .atom (insertion.typing typed) (shape.liftN 1 cutoff)
  | bvar typed found =>
      exact .bvar (insertion.typing typed) (by simpa only [liftVar, Nat.add_comm 1] using insertion.lookup found)
  | forallE typed _ _ agrees domain body =>
      exact .forallE (insertion.typing typed) (domain insertion) (body (insertion.push _)) agrees
  | lam typed _ inner => exact .lam (insertion.typing typed) (inner (insertion.push _))
  | app _ _ function argument =>
      simpa only [AExpr.liftN, AExpr.liftN_inst_zero] using
        HereditaryTyping.app (function insertion) (argument insertion)
  | convert _ rigid converted formed prior =>
      exact .convert (prior insertion)
        (AExpr.HeadRigid.map rigid (AExpr.liftN 1 · cutoff) (by intros; rfl))
        (insertion.conversion converted) (insertion.typing formed)

theorem extend {later : Model.Environment β} {context : Model.Context β} {term type : AExpr β}
    (checked : HereditaryTyping.{u,v} entries context term type) (extension : InterfaceExtends entries later) :
    HereditaryTyping.{u,v} later context term type := by
  induction checked with
  | atom typed shape => exact .atom (extension.typing typed) shape
  | bvar typed found => exact .bvar (extension.typing typed) found
  | forallE typed _ _ agrees domain body => exact .forallE (extension.typing typed) domain body agrees
  | lam typed _ inner => exact .lam (extension.typing typed) inner
  | app _ _ function argument => exact .app function argument
  | convert _ rigid converted formed prior =>
      exact .convert prior rigid (extension.conversion converted) (extension.typing formed)

end HereditaryTyping

theorem HereditaryTyping.liftValue {β : Type u} {entries : Model.Environment β}
    {base source target : Model.Context β} {domain argument term type : AExpr β} {cutoff : Nat}
    (substitution : ContextSubstitution base domain argument source target cutoff)
    (value : HereditaryTyping.{u,v} entries base term type) :
    HereditaryTyping.{u,v} entries target (term.liftN cutoff) (type.liftN cutoff) := by
  induction substitution with
  | root => simpa only [AExpr.liftN_zero] using value
  | @push source target cutoff prior binder ih =>
      have lifted := ih.weakenAt (ContextInsertion.root target (binder.inst argument cutoff))
      simpa only [AExpr.liftN_liftN_merge term cutoff 1 0 0 (Nat.le_refl _) (Nat.zero_le _),
        AExpr.liftN_liftN_merge type cutoff 1 0 0 (Nat.le_refl _) (Nat.zero_le _)] using lifted

theorem HereditaryTyping.substituteAt {β : Type u} {entries : Model.Environment β}
    {base source target : Model.Context β} {domain argument term type : AExpr β} {cutoff : Nat}
    (checked : HereditaryTyping.{u,v} entries source term type)
    (value : HereditaryTyping.{u,v} entries base argument domain)
    (substitution : ContextSubstitution base domain argument source target cutoff) :
    HereditaryTyping.{u,v} entries target (term.inst argument cutoff) (type.inst argument cutoff) := by
  induction checked generalizing target cutoff with
  | atom typed shape => exact .atom (typed.instAt value.typing substitution) (shape.inst argument cutoff)
  | @bvar context index type typed found =>
      by_cases equal : index = cutoff
      · subst index
        have sameType := substitution.instantiate_removed_type found
        simpa only [AExpr.inst, AExpr.instVar, Nat.lt_irrefl, if_false, if_true, sameType] using
          HereditaryTyping.liftValue substitution value
      · have retained := substitution.lookup_other found equal
        have substituted := typed.instAt value.typing substitution
        by_cases below : index < cutoff
        · simp only [AExpr.inst, AExpr.instVar, below, if_true] at substituted retained ⊢
          exact .bvar substituted retained
        · simp only [AExpr.inst, AExpr.instVar, below, equal, if_false] at substituted retained ⊢
          exact .bvar substituted retained
  | forallE typed _ _ agrees domainCheck bodyCheck =>
      exact .forallE (typed.instAt value.typing substitution) (domainCheck substitution)
        (bodyCheck (substitution.push _)) agrees
  | lam typed _ inner => exact .lam (typed.instAt value.typing substitution) (inner (substitution.push _))
  | app _ _ function applied =>
      simpa only [AExpr.inst, AExpr.inst_inst_zero] using
        HereditaryTyping.app (function substitution) (applied substitution)
  | convert _ rigid converted formed prior =>
      exact .convert (prior substitution)
        (AExpr.HeadRigid.map rigid (AExpr.inst · argument cutoff) (by intros; rfl))
        (converted.instAt value.typing substitution) (formed.instAt value.typing substitution)

end Ix.Kernel.Consistency
