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

end Ix.Theory.Model
