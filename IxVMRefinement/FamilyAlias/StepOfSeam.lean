import IxVMRefinement.FamilyAlias.Assembly

/-! # The family step's target from the circuit side's seam

`FamilySeam`: what a refinement of the family check owes the model side, at the family step's
own hypotheses: the family as read (`FamDeclReads`) with the facts of the check
(`FamilyCheckFacts`) at the prefix. It is named here, not proved.

`familyStepTarget_of_seam`: `FamilyStepTarget` from the seam and the root synchronization of
every prefix the step is asked at (`PrefixRootsSynced`). The prefix invariant carries the root
synchronization only per set theory (`FullDeclInv.declInvM.auxSynced`); the fold's clause beside
it carries it outright (`FoldExtra`, the `auxRoot` part of `FoldCore`), so at the family row it
is handed. -/

universe u

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Consistency
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open Ix.Kernel (ConstantInfo ConstantVal)
open IxVM.Refinement.Decl.FamilyAlias (FamilyAdvice FamilyCheckFacts)

set_option linter.unusedVariables false

/-- **The circuit side's seam**: at the family step's hypotheses, the family as read and the
facts of the family check at the prefix. -/
def FamilySeam : Prop :=
  ∀ (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (E₀ E : Ixon.Env) (env : Ix.Kernel.Env .anon) (B rb : _root_.Address)
    (cb crb : Ixon.Constant) (ms rs : Array Ixon.MutConst) (lim : Option Nat)
    (cs : List (Call F)),
    t.check = .ok () → LoadedReads.RunStore calls E₀ → StepStore calls t E₀ E →
    FamBlockRecord E₀ B cb ms → FamRecRecord E₀ rb crb rs →
    FamilyCallAtLim calls bAddr t B rb lim cs →
    ModeledRouteAt calls B →
    Decl.PrefixInv.{u} E t lim env →
    (∀ x, UsedRef E₀ B x →
      (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf B cb x ∨ ¬ NeedOk E₀ x) →
    (∀ x, UsedRef E₀ rb x →
      (env.find? (keyOf t x)).isSome = true ∨ FamAddr B cb rb crb x ∨ ¬ NeedOk E₀ x) →
    InertClause t cb → InertClause t crb →
    (∀ a, AdviceIn cs a → ∀ ca, recordOf E₀ a = some ca → ∀ x, ConstAddrOf a ca x →
      (env.find? (keyOf t x)).isSome = true) →
    (∀ a, AdviceIn cs a → ∀ x, UsedRef E₀ a x →
      (env.find? (keyOf t x)).isSome = true ∨ FamAddr B cb rb crb x ∨ ¬ NeedOk E₀ x) →
    env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA →
    (∀ x, FamAddr B cb rb crb x → env.find? (keyOf t x) = none) →
    (∀ x, FamAddr B cb rb crb x → Decl.KeyFree (keyOf t x)) →
    ∃ (blk : List (ConstantInfo .anon)) (adv : FamilyAdvice)
      (tys : List IxVM.Refinement.Core.KExpr)
      (rhsss : List (List IxVM.Refinement.Core.KExpr)),
      FamDeclReads t E₀ B cb rb crb blk ∧ FamilyCheckFacts env blk adv tys rhsss

/-- **The roots of every prefix are synchronized** where the prefix invariant holds. -/
def PrefixRootsSynced : Prop :=
  ∀ (E : Ixon.Env) (t : Ix.Kernel.RoleTable) (lim : Option Nat) (env : Ix.Kernel.Env .anon),
    Decl.PrefixInv.{u} E t lim env → Decl.AuxRootSynced env

/-- **The family step's target from the circuit side's seam** (module docstring). -/
theorem familyStepTarget_of_seam (hseam : FamilySeam.{u}) (hroots : PrefixRootsSynced.{u}) :
    FamilyStepTarget.{u} := by
  intro calls bAddr t E₀ E env B rb cb crb ms rs lim cs ht hRS hSS hB hR hcall hroute hinv
    hU1 hU2 hI1 hI2 hadv1 hadv2 heq hfresh hfree
  obtain ⟨blk, adv, tys, rhsss, hreads, hF⟩ := hseam calls bAddr t E₀ E env B rb cb crb ms rs
    lim cs ht hRS hSS hB hR hcall hroute hinv hU1 hU2 hI1 hI2 hadv1 hadv2 heq hfresh hfree
  exact famStepConclusion_of_facts hF hreads hinv.store.store (hroots E t lim env hinv) heq
    hfresh hfree

end IxVM.Refinement.Typing.FamilyAlias
