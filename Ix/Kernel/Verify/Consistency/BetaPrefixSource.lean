/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaPrefixPlan

/-! Construct the shared beta prefix from a returned raw lambda and the
original application arguments, using finite walker and interning resources. -/

namespace Ix.Kernel.Consistency.BetaPrefixSource

open Theory Theory.Model

universe u

def selected : KExpr .anon → Bool
  | .lam .. => true
  | _ => false

def peeled (head : KExpr .anon) (arguments : Array (KExpr .anon)) :=
  RecM.consumeBetaLams head arguments

def substituted (head : KExpr .anon) (arguments : Array (KExpr .anon)) (before : TcState .anon) :=
  simulSubst (peeled head arguments).1 (peeled head arguments).2.reverse 0 before.env.intern

def output (head : KExpr .anon) (arguments : Array (KExpr .anon)) (before : TcState .anon) :=
  let walk := substituted head arguments before
  internAppChain walk.1 (arguments.extract (peeled head arguments).2.size arguments.size).toList walk.2

def after (head : KExpr .anon) (arguments : Array (KExpr .anon)) (before : TcState .anon) : TcState .anon :=
  {before with env := {before.env with intern := (output head arguments before).2}}

structure Resources (head : KExpr .anon) (arguments : Array (KExpr .anon)) (before : TcState .anon) : Prop where
  bounds : SimulSubstBounds (peeled head arguments).1 (peeled head arguments).2.reverse 0
  substitutionFaithful : KExpr.CollisionFree fun term => before.env.intern.ExprSupport term ∨
    KExpr.SimulSubstReach (peeled head arguments).2.reverse (peeled head arguments).1 0 term
  suffixFaithful : KExpr.CollisionFree fun term => (substituted head arguments before).2.ExprSupport term ∨
    term ∈ cheapBetaChainList (substituted head arguments before).1
      (arguments.extract (peeled head arguments).2.size arguments.size).toList

private theorem consumed_size (fuel : Nat) (current : KExpr .anon)
    (arguments consumed : Array (KExpr .anon)) :
    consumed.size ≤ (RecM.consumeBetaLamsFuel fuel current arguments consumed).2.size := by
  induction fuel generalizing current consumed with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      unfold RecM.consumeBetaLamsFuel
      split
      · exact Nat.le_refl _
      · cases current with
        | lam => exact Nat.le_trans (by simp) (ih _ _)
        | _ => exact Nat.le_refl _

theorem consumed_nonempty {name bi rawDomain rawBody info} {arguments : Array (KExpr .anon)}
    (nonempty : 0 < arguments.size) :
    (!(RecM.consumeBetaLams (.lam name bi rawDomain rawBody info) arguments).2.isEmpty) = true := by
  have size : arguments.size = (arguments.size - 1) + 1 := by omega
  have positive : 0 < (RecM.consumeBetaLams (.lam name bi rawDomain rawBody info) arguments).2.size := by
    unfold RecM.consumeBetaLams
    rw [size, RecM.consumeBetaLamsFuel]
    simp only [Array.mkEmpty, Array.size_empty, show ¬ 0 ≥ arguments.size from by omega, if_false]
    have bound := consumed_size (arguments.size - 1) rawBody arguments
      ((Array.mkEmpty arguments.size).push arguments[0]!)
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (by
      simpa only [Array.size_push, Array.mkEmpty, Array.size_empty, Nat.zero_add] using bound)
  have notEmpty : (RecM.consumeBetaLams (.lam name bi rawDomain rawBody info) arguments).2.isEmpty = false := by
    apply Bool.eq_false_iff.mpr
    intro empty
    have zero := Array.isEmpty_iff_size_eq_zero.mp empty
    omega
  simp only [notEmpty, Bool.not_false]

private theorem lambda_shape {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {rawDomain rawBody : KExpr .anon} {info : ExprInfo .anon} {term : AExpr β}
    (reading : readScopedExpr? resolve locals (.lam name bi rawDomain rawBody info) = some term.erase) :
    ∃ condition domain body, term = .lam condition domain body := by
  cases term with
  | lam condition domain body => exact ⟨condition, domain, body, rfl⟩
  | _ =>
      cases hd : readScopedExpr? resolve locals rawDomain <;>
        cases hb : readScopedExpr? resolve locals rawBody 1 <;>
        simp [readScopedExpr?, hd, hb, AExpr.erase] at reading

structure Witness {β : Type u} (resolve : Address → Option (ConstRef β)) (locals : List FVarId)
    (before : TcState .anon) (head : KExpr .anon) (term : AExpr β)
    (rawArguments : Array (KExpr .anon)) (arguments : List (AExpr β)) where
  plan : BetaPrefixPlan resolve locals before
  raw : plan.rawLambda = head
  model : plan.modelLambda = term
  rawArgs : plan.rawArguments = rawArguments
  modelArgs : plan.arguments = arguments
  output : plan.output = BetaPrefixSource.output head rawArguments before

def construct {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {before : TcState .anon} {head : KExpr .anon} {term : AExpr β}
    {rawArguments : Array (KExpr .anon)} {arguments : List (AExpr β)}
    (chosen : selected head = true) (reading : readScopedExpr? resolve locals head = some term.erase)
    (argumentReads : rawArguments.toList.map (readScopedExpr? resolve locals ·) = arguments.map (some ·.erase))
    (supplied : 0 < rawArguments.size) (resources : Resources head rawArguments before) :
    Witness resolve locals before head term rawArguments arguments := by
  cases head with
  | lam name bi rawDomain rawInner lambdaInfo =>
      have shape := lambda_shape reading
      cases term with
      | lam condition domain inner =>
          exact ⟨{
            name, bi, rawDomain, rawInner, lambdaInfo, rawArguments,
            rawBody := (peeled (.lam name bi rawDomain rawInner lambdaInfo) rawArguments).1,
            consumed := (peeled (.lam name bi rawDomain rawInner lambdaInfo) rawArguments).2,
            condition, domain, inner, arguments, headReads := reading, argumentReads,
            peeling := rfl, nonempty := consumed_nonempty supplied,
            walkerBounds := resources.bounds, walkerFaithful := resources.substitutionFaithful,
            suffixFaithful := resources.suffixFaithful
          }, rfl, rfl, rfl, rfl, rfl⟩
      | _ => exfalso; obtain ⟨_, _, _, impossible⟩ := shape; cases impossible
  | _ => cases chosen

theorem Witness.result {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {before : TcState .anon} {head : KExpr .anon} {term : AExpr β}
    {rawArguments : Array (KExpr .anon)} {arguments : List (AExpr β)}
    (witness : Witness resolve locals before head term rawArguments arguments) :
    witness.plan.result = (BetaPrefixSource.output head rawArguments before).1 := congrArg Prod.fst witness.output

theorem Witness.after {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {before : TcState .anon} {head : KExpr .anon} {term : AExpr β}
    {rawArguments : Array (KExpr .anon)} {arguments : List (AExpr β)}
    (witness : Witness resolve locals before head term rawArguments arguments) :
    witness.plan.after = BetaPrefixSource.after head rawArguments before :=
  congrArg (fun result : KExpr .anon × InternTable .anon =>
    {before with env := {before.env with intern := result.2}}) witness.output

end Ix.Kernel.Consistency.BetaPrefixSource
