/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Model.Substitution
import Ix.Theory.Model.BetaSubstitution

/-! Typed beta reduction along a finite application spine. The lambda
prefix records syntactic domains, while the argument spine records the
typing established at each dependent application. These are proof helpers
for source inference, not additional semantic premises at admission. -/

namespace Ix.Theory.Model

open Certified

universe u v

namespace AExpr

@[simp] theorem appN_nil (head : AExpr β) : head.appN [] = head := rfl

@[simp] theorem appN_cons (head argument : AExpr β) (arguments : List (AExpr β)) :
    head.appN (argument :: arguments) = (head.app argument).appN arguments := rfl

def lambdaDepth : AExpr β → Nat
  | .lam _ _ body => body.lambdaDepth + 1
  | _ => 0

/-- Reduce at most the specified number of original leading lambdas,
then retain the untouched argument suffix. -/
def betaPrefix : Nat → AExpr β → List (AExpr β) → AExpr β
  | 0, head, arguments => head.appN arguments
  | count + 1, .lam _ _ body, argument :: arguments =>
      betaPrefix count (body.inst argument) arguments
  | _ + 1, head, arguments => head.appN arguments

@[simp] theorem lambdaDepth_liftN (term : AExpr β) (count cutoff : Nat) :
    (term.liftN count cutoff).lambdaDepth = term.lambdaDepth := by
  induction term generalizing cutoff <;> simp_all [liftN, lambdaDepth]

@[simp] theorem lambdaDepth_instL (term : AExpr β) (levels : List VLevel) :
    (term.instL levels).lambdaDepth = term.lambdaDepth := by
  induction term <;> simp_all [instL, lambdaDepth]

theorem liftN_appN (head : AExpr β) (arguments : List (AExpr β)) (count cutoff : Nat) :
    (head.appN arguments).liftN count cutoff =
      (head.liftN count cutoff).appN (arguments.map (liftN count · cutoff)) := by
  induction arguments generalizing head with
  | nil => rfl
  | cons argument arguments ih => simpa only [appN_cons, liftN, List.map_cons] using ih (head.app argument)

theorem instL_appN (head : AExpr β) (arguments : List (AExpr β)) (levels : List VLevel) :
    (head.appN arguments).instL levels =
      (head.instL levels).appN (arguments.map (instL levels)) := by
  induction arguments generalizing head with
  | nil => rfl
  | cons argument arguments ih => simpa only [appN_cons, instL, List.map_cons] using ih (head.app argument)

theorem liftN_betaPrefix (count : Nat) (head : AExpr β) (arguments : List (AExpr β))
    (inserted cutoff : Nat) :
    (betaPrefix count head arguments).liftN inserted cutoff =
      betaPrefix count (head.liftN inserted cutoff) (arguments.map (liftN inserted · cutoff)) := by
  induction count generalizing head arguments with
  | zero => exact liftN_appN _ _ _ _
  | succ count ih =>
      cases head <;> cases arguments <;>
        simp only [betaPrefix, liftN, List.map_nil, List.map_cons, appN_nil, liftN_appN,
          ih, liftN_inst_zero]

theorem instL_betaPrefix (count : Nat) (head : AExpr β) (arguments : List (AExpr β))
    (levels : List VLevel) :
    (betaPrefix count head arguments).instL levels =
      betaPrefix count (head.instL levels) (arguments.map (instL levels)) := by
  induction count generalizing head arguments with
  | zero => exact instL_appN _ _ _
  | succ count ih =>
      cases head <;> cases arguments <;>
        simp only [betaPrefix, instL, List.map_nil, List.map_cons, appN_nil, instL_appN,
          ih, instL_inst]

theorem lambdaDepth_le_inst (term argument : AExpr β) (cutoff : Nat) :
    term.lambdaDepth ≤ (term.inst argument cutoff).lambdaDepth := by
  induction term generalizing cutoff with
  | lam condition domain body ihDomain ihBody =>
      exact Nat.add_le_add_right (ihBody (cutoff + 1)) 1
  | _ => exact Nat.zero_le _

theorem inst_appN (head : AExpr β) (arguments : List (AExpr β)) (value : AExpr β) (cutoff : Nat) :
    (head.appN arguments).inst value cutoff =
      (head.inst value cutoff).appN (arguments.map (inst · value cutoff)) := by
  induction arguments generalizing head with
  | nil => rfl
  | cons argument arguments ih => simpa only [appN_cons, inst, List.map_cons] using ih (head.app argument)

/-- Substitution preserves a reduction justified by the original lambda
prefix. Lambdas newly exposed beyond that prefix need their own origin. -/
theorem inst_betaPrefix (count : Nat) (head : AExpr β) (arguments : List (AExpr β))
    (value : AExpr β) (cutoff : Nat) (enough : count ≤ head.lambdaDepth) :
    (betaPrefix count head arguments).inst value cutoff =
      betaPrefix count (head.inst value cutoff) (arguments.map (inst · value cutoff)) := by
  induction count generalizing head arguments with
  | zero => exact inst_appN _ _ _ _
  | succ count ih =>
      cases head with
      | lam condition domain body =>
          cases arguments with
          | nil => rfl
          | cons argument arguments =>
              have remaining : count ≤ (body.inst argument).lambdaDepth :=
                Nat.le_trans (by simpa only [lambdaDepth, Nat.add_le_add_iff_right] using enough)
                  (lambdaDepth_le_inst body argument 0)
              simp only [betaPrefix, inst, List.map_cons, ih _ _ remaining, inst_inst_zero]
      | _ => simp [lambdaDepth] at enough

end AExpr

/-- Each leading lambda agrees with the corresponding inferred Pi.
The count limits this claim to the original syntactic prefix. -/
inductive LambdaPrefix {β : Type u} : AExpr β → AExpr β → Nat → Prop
  | zero (term type : AExpr β) : LambdaPrefix term type 0
  | lam {condition : PropWhen} {domain body codomain : AExpr β} {count : Nat}
      (inner : LambdaPrefix body codomain count) :
      LambdaPrefix (.lam condition domain body) (.forallE condition domain codomain) (count + 1)

/-- Substitution preserves every domain in the original lambda prefix.
No claim is made about new lambdas exposed beyond that prefix. -/
theorem LambdaPrefix.inst {β : Type u} {term type : AExpr β} {count : Nat}
    (leading : LambdaPrefix term type count) (argument : AExpr β) (cutoff : Nat) :
    LambdaPrefix (term.inst argument cutoff) (type.inst argument cutoff) count := by
  induction leading generalizing cutoff with
  | zero => exact .zero _ _
  | lam inner ih => exact .lam (ih (cutoff + 1))

theorem LambdaPrefix.liftN {β : Type u} {term type : AExpr β} {count : Nat}
    (leading : LambdaPrefix term type count) (inserted cutoff : Nat) :
    LambdaPrefix (term.liftN inserted cutoff) (type.liftN inserted cutoff) count := by
  induction leading generalizing cutoff with
  | zero => exact .zero _ _
  | lam inner ih => exact .lam (ih (cutoff + 1))

theorem LambdaPrefix.instL {β : Type u} {term type : AExpr β} {count : Nat}
    (leading : LambdaPrefix term type count) (arguments : List VLevel) :
    LambdaPrefix (term.instL arguments) (type.instL arguments) count := by
  induction leading with
  | zero => exact .zero _ _
  | lam inner ih => exact .lam ih

theorem LambdaPrefix.truncate {β : Type u} {term type : AExpr β} {total count : Nat}
    (leading : LambdaPrefix term type total) (enough : count ≤ total) :
    LambdaPrefix term type count := by
  induction leading generalizing count with
  | zero =>
      have : count = 0 := by omega
      subst count
      exact .zero _ _
  | lam inner ih =>
      cases count with
      | zero => exact .zero _ _
      | succ count => exact .lam (ih (by omega))

theorem AExpr.appN_ne_forallE {β : Type u} {head : AExpr β}
    (notPi : ∀ condition domain body, head ≠ .forallE condition domain body)
    (arguments : List (AExpr β)) :
    ∀ condition domain body, head.appN arguments ≠ .forallE condition domain body := by
  induction arguments generalizing head with
  | nil => exact notPi
  | cons argument arguments ih =>
      exact ih (by intro condition domain body same; cases same)

theorem LambdaPrefix.lambdaDepth_zero {β : Type u} {term type : AExpr β}
    (leading : LambdaPrefix term type term.lambdaDepth)
    (notPi : ∀ condition domain body, type ≠ .forallE condition domain body) :
    term.lambdaDepth = 0 := by
  cases term with
  | lam condition domain body =>
      cases leading with
      | lam => exact False.elim (notPi _ _ _ rfl)
  | _ => rfl

/-- The original body exposed by removing a syntactic lambda prefix. -/
inductive LambdaPeel {β : Type u} : AExpr β → Nat → AExpr β → Prop
  | zero (term : AExpr β) : LambdaPeel term 0 term
  | lam {condition : PropWhen} {domain head body : AExpr β} {count : Nat}
      (inner : LambdaPeel head count body) :
      LambdaPeel (.lam condition domain head) (count + 1) body

theorem LambdaPeel.length_bound {β : Type u} {head body : AExpr β} {count : Nat}
    (peeling : LambdaPeel head count body) : count ≤ head.lambdaDepth := by
  induction peeling with
  | zero => exact Nat.zero_le _
  | lam inner ih => exact Nat.add_le_add_right ih 1

theorem LambdaPeel.inst {β : Type u} {head body : AExpr β} {count : Nat}
    (peeling : LambdaPeel head count body) (argument : AExpr β) (cutoff : Nat) :
    LambdaPeel (head.inst argument cutoff) count (body.inst argument (cutoff + count)) := by
  induction peeling generalizing cutoff with
  | zero => exact .zero _
  | lam inner ih =>
      simpa only [AExpr.inst, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        LambdaPeel.lam (condition := _) (domain := _) (ih (cutoff + 1))

theorem LambdaPeel.snoc {β : Type u} {head domain body : AExpr β}
    {condition : PropWhen} {count : Nat}
    (peeling : LambdaPeel head count (.lam condition domain body)) :
    LambdaPeel head (count + 1) body := by
  induction count generalizing head with
  | zero => cases peeling; exact .lam (.zero _)
  | succ count ih =>
      cases peeling with
      | lam inner => exact .lam (ih inner)

/-- Sequential beta steps produce exactly simultaneous substitution of
the consumed prefix, followed by its untouched application suffix. -/
theorem LambdaPeel.betaPrefix {β : Type u} {head body : AExpr β}
    {arguments : List (AExpr β)} (peeling : LambdaPeel head arguments.length body)
    (trailing : List (AExpr β)) :
    AExpr.betaPrefix arguments.length head (arguments ++ trailing) =
      (body.instRev arguments).appN trailing := by
  induction arguments generalizing head body with
  | nil => cases peeling; rfl
  | cons argument arguments ih =>
      cases peeling with
      | lam inner =>
          have result := ih (inner.inst argument 0)
          simpa only [List.length_cons, List.cons_append, AExpr.betaPrefix, AExpr.instRev,
            Nat.zero_add] using result

/-- Types of arguments along the original application's dependent Pi
spine. Production inference will derive this helper from its actual calls. -/
inductive ArgumentSpine {β : Type u} (entries : Environment β) (context : Context β) :
    AExpr β → List (AExpr β) → AExpr β → Prop
  | nil (type : AExpr β) : ArgumentSpine entries context type [] type
  | cons {condition : PropWhen} {domain codomain argument result : AExpr β}
      {arguments : List (AExpr β)}
      (typed : TypingClaim.{u,v} entries context argument domain)
      (tail : ArgumentSpine entries context (codomain.inst argument) arguments result) :
      ArgumentSpine entries context (.forallE condition domain codomain) (argument :: arguments) result

theorem ArgumentSpine.append {β : Type u} {entries : Environment β} {context : Context β}
    {start middle finish : AExpr β} {left right : List (AExpr β)}
    (first : ArgumentSpine.{u,v} entries context start left middle)
    (second : ArgumentSpine.{u,v} entries context middle right finish) :
    ArgumentSpine.{u,v} entries context start (left ++ right) finish := by
  induction first with
  | nil => exact second
  | cons typed tail ih => exact .cons typed (ih second)

theorem ArgumentSpine.typing {β : Type u} {entries : Environment β} {context : Context β}
    {head type result : AExpr β} {arguments : List (AExpr β)}
    (spine : ArgumentSpine.{u,v} entries context type arguments result)
    (typed : TypingClaim.{u,v} entries context head type) :
    TypingClaim.{u,v} entries context (head.appN arguments) result := by
  induction spine generalizing head with
  | nil => exact typed
  | cons argumentTyped tail ih => exact ih (typed.app argumentTyped)

/-- Substitution updates the type at every step of a dependent argument
spine, including the type expected by the next application. -/
theorem ArgumentSpine.instAt {β : Type u} {entries : Environment β}
    {base source target : Context β} {type result argument domain : AExpr β}
    {arguments : List (AExpr β)} {cutoff : Nat}
    (spine : ArgumentSpine.{u,v} entries source type arguments result)
    (value : TypingClaim.{u,v} entries base argument domain)
    (substitution : ContextSubstitution base domain argument source target cutoff) :
    ArgumentSpine.{u,v} entries target (type.inst argument cutoff)
      (arguments.map (AExpr.inst · argument cutoff)) (result.inst argument cutoff) := by
  induction spine with
  | nil => exact .nil _
  | cons typed tail ih =>
      exact .cons (typed.instAt value substitution)
        (by simpa only [AExpr.inst_inst_zero] using ih)

theorem ContextSubstitution.removed_type {β : Type u} {base source target : Context β}
    {domain argument : AExpr β} {cutoff : Nat}
    (substitution : ContextSubstitution base domain argument source target cutoff) :
    source[cutoff]? = some (domain.liftN (cutoff + 1)) := by
  induction substitution with
  | root => rfl
  | @push source target cutoff prior binder ih =>
      simp only [Context.push, List.getElem?_cons_succ, List.getElem?_map, ih, Option.map_some,
        AExpr.liftN_liftN_merge domain (cutoff + 1) 1 0 0 (Nat.le_refl _) (Nat.zero_le _)]

theorem ContextSubstitution.instantiate_removed_type {β : Type u} {base source target : Context β}
    {domain argument type : AExpr β} {cutoff : Nat}
    (substitution : ContextSubstitution base domain argument source target cutoff)
    (atIndex : source[cutoff]? = some type) :
    type.inst argument cutoff = domain.liftN cutoff := by
  have same := Option.some.inj (atIndex.symm.trans substitution.removed_type)
  rw [same]
  exact AExpr.inst_liftN_within domain argument cutoff 0 cutoff (Nat.zero_le _) (by omega)

/-- Every retained local keeps its substituted type. Indices beyond the
removed parameter decrease by one; later parameters keep their indices. -/
theorem ContextSubstitution.lookup_other {β : Type u} {base source target : Context β}
    {domain argument type : AExpr β} {cutoff index : Nat}
    (substitution : ContextSubstitution base domain argument source target cutoff)
    (atIndex : source[index]? = some type) (distinct : index ≠ cutoff) :
    target[if index < cutoff then index else index - 1]? = some (type.inst argument cutoff) := by
  induction substitution generalizing index type with
  | root =>
      cases index with
      | zero => exact False.elim (distinct rfl)
      | succ index =>
          simp only [Context.push, List.getElem?_cons_succ, List.getElem?_map] at atIndex
          obtain ⟨type, sourceLookup, rfl⟩ := Option.map_eq_some_iff.mp atIndex
          simpa only [Nat.not_lt_zero, ↓reduceIte, Nat.add_sub_cancel,
            AExpr.inst_liftN_within type argument 0 0 0 (Nat.le_refl _) (by omega),
            AExpr.liftN_zero] using sourceLookup
  | @push source target cutoff prior binder ih =>
      cases index with
      | zero =>
          simp only [Context.push, List.getElem?_cons_zero, Option.some.injEq] at atIndex
          subst type
          simpa only [Nat.zero_lt_succ, ↓reduceIte, Context.push, List.getElem?_cons_zero,
            Nat.add_comm 1 cutoff] using
            congrArg some (AExpr.inst_liftN binder argument 1 0 cutoff (Nat.zero_le _)).symm
      | succ index =>
          simp only [Context.push, List.getElem?_cons_succ, List.getElem?_map] at atIndex
          obtain ⟨type, sourceLookup, rfl⟩ := Option.map_eq_some_iff.mp atIndex
          have retained := ih sourceLookup (show index ≠ cutoff by omega)
          have nextIndex : (if index + 1 < cutoff + 1 then index + 1 else index + 1 - 1) =
              (if index < cutoff then index else index - 1) + 1 := by
            split <;> split <;> omega
          rw [nextIndex]
          simp only [Context.push, List.getElem?_cons_succ, List.getElem?_map, retained,
            Option.map_some]
          exact congrArg some (by
            simpa only [Nat.add_comm 1 cutoff] using
              (AExpr.inst_liftN type argument 1 0 cutoff (Nat.zero_le _)).symm)

/-- Values from the base context can be used beneath the retained prefix.
Their types are lifted by the same number of dependent binders. -/
theorem ContextSubstitution.lift_typing {β : Type u} {entries : Environment β}
    {base source target : Context β} {domain argument term type : AExpr β} {cutoff : Nat}
    (substitution : ContextSubstitution base domain argument source target cutoff)
    (typed : TypingClaim.{u,v} entries base term type) :
    TypingClaim.{u,v} entries target (term.liftN cutoff) (type.liftN cutoff) := by
  intro V _ constants realizes levels env valid
  simpa only [wellDenoted_liftN, interp_liftN] using
    typed V constants realizes levels _ (substitution.base_valid valid)

theorem ConversionClaim.appN {β : Type u} {entries : Environment β} {context : Context β}
    {left right : AExpr β} (same : ConversionClaim.{u,v} entries context left right)
    (arguments : List (AExpr β)) :
    ConversionClaim.{u,v} entries context (left.appN arguments) (right.appN arguments) := by
  induction arguments generalizing left right with
  | nil => exact same
  | cons argument arguments ih => exact ih (same.app (.refl argument))

/-- Every consumed lambda retains its actual domain after substitution.
The untouched suffix is handled by ordinary application congruence. -/
theorem LambdaPrefix.beta_sound {β : Type u} {entries : Environment β} {context : Context β}
    {head type result : AExpr β} {arguments : List (AExpr β)} {count : Nat}
    (leading : LambdaPrefix head type count)
    (typed : TypingClaim.{u,v} entries context head type)
    (spine : ArgumentSpine.{u,v} entries context type arguments result) :
    ConversionClaim.{u,v} entries context (head.appN arguments)
      (AExpr.betaPrefix count head arguments) ∧
      TypingClaim.{u,v} entries context (AExpr.betaPrefix count head arguments) result := by
  induction count generalizing head type arguments with
  | zero => exact ⟨.refl _, spine.typing typed⟩
  | succ count ih =>
      cases leading with
      | lam inner =>
          cases spine with
          | nil => exact ⟨.refl _, typed⟩
          | cons argumentTyped tail =>
              obtain ⟨conversion, resultTyped⟩ := ih (inner.inst _ 0)
                (TypingClaim.betaResult typed argumentTyped) tail
              exact ⟨((ConversionClaim.beta typed argumentTyped).appN _).trans conversion,
                resultTyped⟩

/-- Source inference retains the typing of every original lambda-headed
spine. This internal result carries the domains needed by later reduction;
ordinary semantic typing alone cannot recover them in the proof regime. -/
def LambdaSpineTyping {β : Type u} (entries : Environment β) (context : Context β)
    (term type : AExpr β) : Prop :=
  ∀ (condition : PropWhen) (domain body : AExpr β) (arguments : List (AExpr β)),
    term = (AExpr.lam condition domain body).appN arguments →
      ∃ headType, TypingClaim.{u,v} entries context (.lam condition domain body) headType ∧
        LambdaPrefix (.lam condition domain body) headType (body.lambdaDepth + 1) ∧
        ArgumentSpine.{u,v} entries context headType arguments type

private theorem list_reverse_induction {α : Type u} {motive : List α → Prop}
    (nil : motive [])
    (append_singleton : ∀ tail last, motive tail → motive (tail ++ [last]))
    (values : List α) : motive values := by
  have reversed : ∀ items : List α, motive items.reverse := by
    intro items
    induction items with
    | nil => exact nil
    | cons item items ih =>
        simpa only [List.reverse_cons] using append_singleton items.reverse item ih
  simpa using reversed values.reverse

namespace LambdaSpineTyping

theorem non_application {β : Type u} {entries : Environment β} {context : Context β}
    {term type : AExpr β}
    (notApp : ∀ fn arg, term ≠ .app fn arg)
    (notLam : ∀ condition domain body, term ≠ .lam condition domain body) :
    LambdaSpineTyping.{u,v} entries context term type := by
  intro condition domain body arguments same
  induction arguments using list_reverse_induction with
  | nil => exact False.elim (notLam _ _ _ same)
  | append_singleton arguments argument ih =>
      exact False.elim (notApp _ _
        (by simpa only [AExpr.appN_append, AExpr.appN_cons, AExpr.appN_nil] using same))

theorem lam {β : Type u} {entries : Environment β} {context : Context β}
    {condition : PropWhen} {domain body type : AExpr β}
    (typed : TypingClaim.{u,v} entries context (.lam condition domain body) type)
    (leading : LambdaPrefix (.lam condition domain body) type (body.lambdaDepth + 1)) :
    LambdaSpineTyping.{u,v} entries context (.lam condition domain body) type := by
  intro otherCondition otherDomain otherBody arguments same
  induction arguments using list_reverse_induction with
  | nil =>
      cases same
      exact ⟨type, typed, leading, .nil _⟩
  | append_singleton arguments argument ih =>
      simp only [AExpr.appN_append, AExpr.appN_cons, AExpr.appN_nil] at same
      cases same

theorem app {β : Type u} {entries : Environment β} {context : Context β}
    {fn arg domain body : AExpr β} {condition : PropWhen}
    (function : LambdaSpineTyping.{u,v} entries context fn (.forallE condition domain body))
    (argument : TypingClaim.{u,v} entries context arg domain) :
    LambdaSpineTyping.{u,v} entries context (.app fn arg) (body.inst arg) := by
  intro headCondition headDomain headBody arguments same
  induction arguments using list_reverse_induction with
  | nil => cases same
  | append_singleton arguments last ih =>
      simp only [AExpr.appN_append, AExpr.appN_cons, AExpr.appN_nil, AExpr.app.injEq] at same
      obtain ⟨headType, headTyped, leading, spine⟩ := function _ _ _ arguments same.1
      refine ⟨headType, headTyped, leading, ?_⟩
      rw [← same.2]
      exact spine.append (.cons argument (.nil _))

theorem betaPrefix {β : Type u} {entries : Environment β} {context : Context β}
    {condition : PropWhen} {domain body type : AExpr β} {arguments : List (AExpr β)} {count : Nat}
    (source : LambdaSpineTyping.{u,v} entries context
      ((AExpr.lam condition domain body).appN arguments) type)
    (enough : count ≤ body.lambdaDepth + 1) :
    ConversionClaim.{u,v} entries context ((AExpr.lam condition domain body).appN arguments)
      (AExpr.betaPrefix count (.lam condition domain body) arguments) ∧
      TypingClaim.{u,v} entries context
        (AExpr.betaPrefix count (.lam condition domain body) arguments) type := by
  obtain ⟨_, typed, leading, spine⟩ := source _ _ _ _ rfl
  exact (leading.truncate enough).beta_sound typed spine

end LambdaSpineTyping

end Ix.Theory.Model
