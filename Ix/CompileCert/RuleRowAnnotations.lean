import Ix.CompileCert.RuleFiringTuples

/-! # The outer telescope of an installed equality row

A recursor prefix ends in the recursor's result sort. Its binders therefore
need not have the same `PropWhen` data as the corresponding prefix of a
theorem ending in `Eq`. This module proposes the proposition regime for
exactly those outer binders and proves that the original dependent argument
tuple still types that telescope. Every domain, including annotations
inside domains, and both source firing endpoints are retained literally.

This is an untrusted row proposal. The actual installed theorem is still
read by `checkInstalledFiringRow`, which compares its complete annotated
statement. No target metadata is normalized or omitted from that check.
The raw exporter and source-installation correspondence remain separate.
-/

namespace Ix.CompileCert

/-- Outer binders of the proposed equality statement have a proposition
codomain. Domain expressions are copied verbatim, including all metadata
within them; the installed row check must validate this proposal. -/
def equationRowBinders : List (Kernel.Expr × Kernel.BinderMeta) →
    List (Kernel.Expr × Kernel.BinderMeta)
  | [] => []
  | (domain, _) :: rest => (domain, ⟨.ifAllZero []⟩) :: equationRowBinders rest

theorem equationRowBinders_domains (binders : List (Kernel.Expr × Kernel.BinderMeta)) :
    (equationRowBinders binders).map Prod.fst = binders.map Prod.fst := by
  induction binders with
  | nil => rfl
  | cons binder rest ih =>
    rcases binder with ⟨domain, metadata⟩
    simp only [equationRowBinders, List.map_cons, ih]

theorem equationRowBinders_length (binders : List (Kernel.Expr × Kernel.BinderMeta)) :
    (equationRowBinders binders).length = binders.length := by
  induction binders with
  | nil => rfl
  | cons binder rest ih =>
    rcases binder with ⟨domain, metadata⟩
    exact congrArg Nat.succ ih

/-- Only the outer telescope metadata is proposed afresh. -/
def FiringRowProposal.forEquation (proposal : FiringRowProposal) : FiringRowProposal :=
  { proposal with binders := equationRowBinders proposal.binders }

theorem FiringRowProposal.forEquation_preserves {env : Kernel.Env}
    {name : Kernel.Name} {index : Nat} (frame : InstalledRuleFrame env name index)
    (proposal : FiringRowProposal) :
    proposal.forEquation.binders.map Prod.fst = proposal.binders.map Prod.fst ∧
    proposal.forEquation.binders.length = proposal.binders.length ∧
    frame.rowLeft proposal.forEquation = frame.rowLeft proposal ∧
    frame.rowRight proposal.forEquation = frame.rowRight proposal ∧
    frame.rowBody proposal.forEquation = frame.rowBody proposal :=
  ⟨equationRowBinders_domains _, equationRowBinders_length _, rfl, rfl, rfl⟩

/-- Argument membership depends on each actual dependent domain. Changing
only the enclosing equation binders' metadata leaves all those domain
readings, argument values and valuations unchanged. This says nothing about
equality of the denotations of the two whole Pi-types. -/
theorem InstalledTelescope.equation_row_annotations
    {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {valuation finalValuation : Nat → V}
    {binders : List (Kernel.Expr × Kernel.BinderMeta)} {arguments : List V}
    {level : Kernel.Level} {carrier left right : Kernel.Expr}
    (typed : InstalledTelescope values env levels valuation
      (ruleRowForalls binders (kernelEq level carrier left right))
      arguments finalValuation (kernelEq level carrier left right)) :
    InstalledTelescope values env levels valuation
      (ruleRowForalls (equationRowBinders binders) (kernelEq level carrier left right))
      arguments finalValuation (kernelEq level carrier left right) := by
  induction binders generalizing valuation arguments with
  | nil => exact typed
  | cons binder rest ih =>
    rcases binder with ⟨domain, metadata⟩
    cases typed with
    | cons domainRead argumentTyped tail =>
      exact .cons domainRead argumentTyped (ih tail)

/-- A successful proposal is tied to the actual installed theorem's whole
statement. In particular the target outer metadata and every domain/RHS
annotation remain inputs to the existing comparison, without normalization.
-/
theorem checkInstalledFiringRow_equation_spec {source target : Kernel.Env}
    {names : Kernel.Name → Kernel.Name} {name : Kernel.Name} {index : Nat}
    {frame : InstalledRuleFrame source name index} {proposal : FiringRowProposal}
    {rowName : Kernel.Name}
    (checked : checkInstalledFiringRow source target names frame proposal.forEquation rowName = some true) :
    ∃ row proof binders level carrier left right,
      target.find? rowName = some (.thmInfo row proof) ∧
      row.type.stripPis proposal.binders.length =
        some (binders, kernelEq level carrier left right) ∧
      checkInstalledMemberExpr source target names name
        (ruleRowForalls (equationRowBinders proposal.binders) (frame.rowBody proposal))
        row.type = some true := by
  obtain ⟨row, proof, binders, level, carrier, left, right, lookup, stripped, compared⟩ :=
    checkInstalledFiringRow_spec checked
  rw [FiringRowProposal.forEquation, equationRowBinders_length] at stripped
  exact ⟨row, proof, binders, level, carrier, left, right, lookup, stripped, compared⟩

/-- The actual installed Eq row supplies the firing equation from the
original source tuple, even when the recursor prefix's outer metadata is
different. Both endpoint expressions and all semantic inputs are unchanged;
the complete checked installed statement supplies the equation. -/
theorem checkInstalledFiringRow_equation_sound {V : Type u} [Kernel.SetTheory V]
    {source targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name}
    (telescopes : checkTelescopes source targetEnv names = true)
    {name : Kernel.Name} {index : Nat} (frame : InstalledRuleFrame source name index)
    (proposal : FiringRowProposal) {rowName : Kernel.Name}
    (checked : checkInstalledFiringRow source targetEnv names frame proposal.forEquation rowName = some true)
    (levels : Kernel.Name → Nat) {valuation finalValuation : Nat → V} {arguments : List V}
    (typed : InstalledTelescope
      ((PullbackMap.fromEnvs source targetEnv names).values target.public.cval)
      source levels valuation (frame.rowStatement proposal)
      arguments finalValuation (frame.rowBody proposal)) :
    ∃ value,
      Kernel.Denotes ((PullbackMap.fromEnvs source targetEnv names).values target.public.cval)
        source levels finalValuation (frame.rowLeft proposal) value ∧
      Kernel.Denotes ((PullbackMap.fromEnvs source targetEnv names).values target.public.cval)
        source levels finalValuation (frame.rowRight proposal) value := by
  exact checkInstalledFiringRow_sound target telescopes frame proposal.forEquation checked levels
    typed.equation_row_annotations

end Ix.CompileCert
