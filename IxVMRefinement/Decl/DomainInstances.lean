import IxVMRefinement.Decl.DomainCoherence
import IxVMRefinement.Decl.SortTailTransport
import IxVMRefinement.Decl.NamedAliasTail

/-! # Constructed instances of the domain-origin protocol

The existing sort and checked-alias fragments instantiate the common syntax specialization.
Their instance constructors prove every obligation; no such invariant is added as a premise
to the public consistency statement.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model

universe u

theorem SortTail.invariant (env : Env .anon) (sortLevel : Level) :
    SyntacticDomainInvariant env (fun e => ∃ count, SortTail sortLevel count e) .never where
  checked := by
    intro depth e inferred level ⟨count, shape⟩ typed sorted
    exact shape.checked_zero typed sorted
  abstracts := by
    intro e index cut ⟨count, shape⟩
    exact ⟨count, shape.abstract1 index cut⟩
  instantiates := by
    intro e value cut ⟨count, shape⟩
    exact ⟨count, shape.instantiate1 value cut⟩
  annotates := by
    intro e out ⟨count, shape⟩ annotation
    exact ⟨count, shape.annotated annotation⟩
  whnf_closed := by
    intro fuel depth e out ⟨count, shape⟩ run
    exact ⟨count, shape.reduced (Rules.whnf_bridge run)⟩
  product_body := by
    intro domain body metadata ⟨count, shape⟩
    cases shape with
    | result impossible => cases impossible
    | pi bodyShape => exact ⟨_, bodyShape⟩
  product := by
    intro domain body metadata ⟨count, shape⟩
    exact ⟨count + 1, .pi shape⟩

theorem AliasTail.invariant {V : Type u} [SetTheory V] {env : Env .anon}
    (model : EnvModelM V .verified env) (definitions : DefinitionsTyped env)
    {aliasName targetName : Key .anon} {targetLevels : List Level}
    {aliasCV targetCV : ConstantVal .anon} {hint : ReducibilityHint} {caps : IndCaps .anon}
    {declared actual : Level}
    (aliasFound : env.find? aliasName = some (.defnInfo aliasCV (.const targetName targetLevels) hint))
    (noLevels : aliasCV.levelParams = [])
    (targetFound : env.find? targetName = some (.indInfo targetCV caps))
    (aliasHeader : aliasCV.type = .sort declared)
    (targetHeader : targetCV.type.instantiateLevelParams targetCV.levelParams targetLevels = .sort actual) :
    SyntacticDomainInvariant env (fun e => ∃ count, AliasTail aliasName targetName targetLevels count e)
      (Level.zeronessOf actual) where
  checked := by
    intro depth e inferred level ⟨count, shape⟩ typed sorted
    exact shape.checked_zero model definitions aliasFound noLevels targetFound aliasHeader targetHeader typed sorted
  abstracts := by
    intro e index cut ⟨count, shape⟩
    exact ⟨count, shape.abstract1 index cut⟩
  instantiates := by
    intro e value cut ⟨count, shape⟩
    exact ⟨count, shape.instantiate1 value cut⟩
  annotates := by
    intro e out ⟨count, shape⟩ annotation
    exact ⟨count, shape.annotated annotation⟩
  whnf_closed := by
    intro fuel depth e out ⟨count, shape⟩ run
    exact ⟨count, shape.whnf aliasFound noLevels targetFound run⟩
  product_body := by
    intro domain body metadata ⟨count, shape⟩
    cases shape with
    | result impossible => cases impossible
    | pi bodyShape => exact ⟨_, bodyShape⟩
  product := by
    intro domain body metadata ⟨count, shape⟩
    exact ⟨count + 1, .pi shape⟩

end IxVM.Refinement.Decl
