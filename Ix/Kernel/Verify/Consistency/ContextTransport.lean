/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.ContextInsertion

/-! Preserve checked application spines when an interface grows or a local
is inserted. Inverting the lifted syntax retains each original argument and
lambda domain, rather than trying to recover them from semantic typing. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

structure LiftedSpineView {β : Type u} (source head : AExpr β) (arguments : List (AExpr β))
    (count cutoff : Nat) where
  originalHead : AExpr β
  originalArguments : List (AExpr β)
  sourceEq : source = originalHead.appN originalArguments
  headEq : head = originalHead.liftN count cutoff
  argumentsEq : arguments = originalArguments.map (AExpr.liftN count · cutoff)

/-- Syntax inversion is data-producing: later retained checks can recover
their original head and arguments without a semantic or choice premise. -/
def liftedSpineView {β : Type u} {source head : AExpr β} {arguments : List (AExpr β)}
    {count cutoff : Nat} (same : source.liftN count cutoff = head.appN arguments) :
    LiftedSpineView source head arguments count cutoff := by
  by_cases empty : arguments = []
  · subst arguments
    exact ⟨source, [], rfl, same.symm, rfl⟩
  · have last : head.appN arguments =
        (head.appN arguments.dropLast).app (arguments.getLast empty) := by
      calc
        head.appN arguments = head.appN (arguments.dropLast ++ [arguments.getLast empty]) :=
          congrArg (AExpr.appN head) (List.dropLast_concat_getLast empty).symm
        _ = _ := by simp only [AExpr.appN_append, AExpr.appN_cons, AExpr.appN_nil]
    rw [last] at same
    cases source with
    | app fn arg =>
        obtain ⟨functionEq, argumentEq⟩ := AExpr.app.inj same
        let prior := liftedSpineView functionEq
        refine ⟨prior.originalHead, prior.originalArguments ++ [arg], ?_, prior.headEq, ?_⟩
        · simpa only [AExpr.appN_append, AExpr.appN_cons, AExpr.appN_nil] using
            congrArg (AExpr.app · arg) prior.sourceEq
        · rw [List.map_append, List.map_cons, List.map_nil, ← prior.argumentsEq, argumentEq]
          exact (List.dropLast_concat_getLast empty).symm
    | bvar | sort | const | lam | forallE | proj | natLit => cases same
termination_by structural source

structure LiftedForallView {β : Type u} (source : AExpr β) (condition : Certified.PropWhen)
    (domain body : AExpr β) (count cutoff : Nat) where
  originalDomain : AExpr β
  originalBody : AExpr β
  sourceEq : source = .forallE condition originalDomain originalBody
  domainEq : domain = originalDomain.liftN count cutoff
  bodyEq : body = originalBody.liftN count (cutoff + 1)

def liftedForallView {β : Type u} {source domain body : AExpr β} {condition : Certified.PropWhen}
    {count cutoff : Nat} (same : source.liftN count cutoff = .forallE condition domain body) :
    LiftedForallView source condition domain body count cutoff := by
  cases source with
  | forallE originalCondition originalDomain originalBody =>
      cases same
      exact ⟨originalDomain, originalBody, rfl, rfl, rfl⟩
  | bvar | sort | const | app | lam | proj | natLit => cases same

structure LiftedLambdaView {β : Type u} (source : AExpr β) (condition : Certified.PropWhen)
    (domain body : AExpr β) (count cutoff : Nat) where
  originalDomain : AExpr β
  originalBody : AExpr β
  sourceEq : source = .lam condition originalDomain originalBody
  domainEq : domain = originalDomain.liftN count cutoff
  bodyEq : body = originalBody.liftN count (cutoff + 1)

def liftedLambdaView {β : Type u} {source domain body : AExpr β} {condition : Certified.PropWhen}
    {count cutoff : Nat} (same : source.liftN count cutoff = .lam condition domain body) :
    LiftedLambdaView source condition domain body count cutoff := by
  cases source with
  | lam originalCondition originalDomain originalBody =>
      cases same
      exact ⟨originalDomain, originalBody, rfl, rfl, rfl⟩
  | bvar | sort | const | app | forallE | proj | natLit => cases same

structure LiftedApplicationView {β : Type u} (source fn arg : AExpr β) (count cutoff : Nat) where
  originalFunction : AExpr β
  originalArgument : AExpr β
  sourceEq : source = .app originalFunction originalArgument
  functionEq : fn = originalFunction.liftN count cutoff
  argumentEq : arg = originalArgument.liftN count cutoff

def liftedApplicationView {β : Type u} {source fn arg : AExpr β} {count cutoff : Nat}
    (same : source.liftN count cutoff = .app fn arg) : LiftedApplicationView source fn arg count cutoff := by
  cases source with
  | app originalFunction originalArgument =>
      cases same
      exact ⟨originalFunction, originalArgument, rfl, rfl, rfl⟩
  | bvar | sort | const | lam | forallE | proj | natLit => cases same

structure LiftedVariableSpineView {β : Type u} (source : AExpr β) (index : Nat)
    (arguments : List (AExpr β)) (count cutoff : Nat) where
  originalIndex : Nat
  originalArguments : List (AExpr β)
  sourceEq : source = (AExpr.bvar originalIndex).appN originalArguments
  indexEq : index = liftVar count originalIndex cutoff
  argumentsEq : arguments = originalArguments.map (AExpr.liftN count · cutoff)

def liftedVariableSpineView {β : Type u} {source : AExpr β} {index count cutoff : Nat}
    {arguments : List (AExpr β)} (same : source.liftN count cutoff = (AExpr.bvar index).appN arguments) :
    LiftedVariableSpineView source index arguments count cutoff := by
  let view := liftedSpineView same
  have headEq := view.headEq
  cases original : view.originalHead with
  | bvar originalIndex =>
      rw [original] at headEq
      refine ⟨originalIndex, view.originalArguments, ?_, AExpr.bvar.inj headEq, view.argumentsEq⟩
      simpa only [original] using view.sourceEq
  | sort | const | app | lam | forallE | proj | natLit =>
      rw [original] at headEq
      cases headEq

theorem liftN_sort_inv {β : Type u} {source : AExpr β} {level : VLevel} {count cutoff : Nat}
    (same : source.liftN count cutoff = .sort level) : source = .sort level := by
  cases source <;> cases same
  rfl

theorem InterfaceExtends.conversion {β : Type u} {earlier later : Model.Environment β}
    (extension : InterfaceExtends earlier later) {context : Model.Context β} {left right : AExpr β}
    (converted : ConversionClaim.{u,v} earlier context left right) :
    ConversionClaim.{u,v} later context left right := by
  intro V _ constants realizes levels env valid
  exact converted V constants (extension.realizes realizes) levels env valid

theorem InterfaceExtends.argumentSpine {β : Type u} {earlier later : Model.Environment β}
    (extension : InterfaceExtends earlier later) {context : Model.Context β}
    {start result : AExpr β} {arguments : List (AExpr β)}
    (spine : ArgumentSpine.{u,v} earlier context start arguments result) :
    ArgumentSpine.{u,v} later context start arguments result := by
  induction spine with
  | nil => exact .nil _
  | cons checked rest ih => exact .cons (extension.typing checked) ih
  | convert rigid converted formed rest ih =>
      exact .convert rigid (extension.conversion converted) (extension.typing formed) ih

theorem InterfaceExtends.lambdaSpine {β : Type u} {earlier later : Model.Environment β}
    (extension : InterfaceExtends earlier later) {context : Model.Context β} {term type : AExpr β}
    (spine : LambdaSpineTyping.{u,v} earlier context term type) :
    LambdaSpineTyping.{u,v} later context term type := by
  intro condition domain body arguments same
  obtain ⟨headType, typed, leading, checked⟩ := spine _ _ _ _ same
  exact ⟨headType, extension.typing typed, leading, extension.argumentSpine checked⟩

theorem ContextInsertion.argumentSpine {β : Type u} {entries : Model.Environment β}
    {source target : Model.Context β} {cutoff : Nat}
    (insertion : ContextInsertion source target cutoff)
    {start result : AExpr β} {arguments : List (AExpr β)}
    (spine : ArgumentSpine.{u,v} entries source start arguments result) :
    ArgumentSpine.{u,v} entries target (start.liftN 1 cutoff)
      (arguments.map (AExpr.liftN 1 · cutoff)) (result.liftN 1 cutoff) := by
  induction spine with
  | nil => exact .nil _
  | cons checked rest ih =>
      simpa only [AExpr.liftN, List.map_cons] using
        ArgumentSpine.cons (insertion.typing checked)
          (by simpa only [AExpr.liftN_inst_zero] using ih)
  | convert rigid converted formed rest ih =>
      exact .convert (AExpr.HeadRigid.map rigid (AExpr.liftN 1 · cutoff) (by intros; rfl))
        (insertion.conversion converted) (insertion.typing formed) ih

theorem ContextInsertion.lambdaSpine {β : Type u} {entries : Model.Environment β}
    {source target : Model.Context β} {cutoff : Nat}
    (insertion : ContextInsertion source target cutoff) {term type : AExpr β}
    (spine : LambdaSpineTyping.{u,v} entries source term type) :
    LambdaSpineTyping.{u,v} entries target (term.liftN 1 cutoff) (type.liftN 1 cutoff) := by
  intro condition domain body arguments same
  let view := liftedSpineView same
  have headEq := view.headEq
  cases original : view.originalHead with
  | lam priorCondition priorDomain priorBody =>
      rw [original] at headEq
      obtain ⟨rfl, rfl, rfl⟩ := AExpr.lam.inj headEq
      have sourceEq := view.sourceEq
      rw [original] at sourceEq
      obtain ⟨headType, typed, leading, checked⟩ := spine _ _ _ _ sourceEq
      refine ⟨headType.liftN 1 cutoff, insertion.typing typed, ?_, ?_⟩
      · simpa only [AExpr.liftN, AExpr.lambdaDepth_liftN] using leading.liftN 1 cutoff
      · rw [view.argumentsEq]
        exact insertion.argumentSpine checked
  | bvar | sort | const | app | forallE | proj | natLit =>
      rw [original] at headEq
      cases headEq

end Ix.Kernel.Consistency
