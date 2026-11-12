import IxVMRefinement.Core.Good
import IxC.Kernel.Model.Open.StoredFacts

/-! # The stored-constant facts of the environment invariant, from the fold's invariants

The arity facts of `EnvFacts` (`recArity`, `ruleCtorArity`, `tableCtorArity`, `familyArity`) and
the firing conjunct of `recRules` are what the declarations layer's model-free invariants
(`EnvWF`, `RecCtorsStored`, `ProjOkT`) give, as `Ix.Kernel.Open.StoredFacts` states them. -/

namespace IxVM.Refinement.Core

open Ix.Kernel (EnvWF RecCtorsStored ProjOkT)

/-- **The arity facts and the firing of stored rules, from the fold's invariants.** -/
theorem storedFacts_of_invariants (c : Ctx) (hwf : EnvWF c.env) (hrc : RecCtorsStored c.env)
    (hp : ProjOkT c.env) :
    (∀ k cv mI rP rls, c.env.find? k = some (.recInfo cv mI rP rls) → ∀ rl ∈ rls,
      rl.fire ≠ .inert ∧ ∃ cvj nF, c.env.find? rl.ctor = some (.ctorInfo cvj rl.ctorParams nF)) ∧
    (∀ k cv mI rP rls, c.env.find? k = some (.recInfo cv mI rP rls) → ∀ rl ∈ rls,
      (cv.type.stripPis (mI + 1)).isSome = true) ∧
    (∀ k cv mI rP rls, c.env.find? k = some (.recInfo cv mI rP rls) → ∀ rl ∈ rls,
      ∀ cvj nP nF, c.env.find? rl.ctor = some (.ctorInfo cvj nP nF) →
        nP = rl.ctorParams ∧ nF = rl.nfields ∧ (cvj.type.stripPis (nP + nF)).isSome = true) ∧
    (∀ sn i entry, c.env.findProj? sn i = some entry →
      ∀ cvC nP nF, c.env.find? entry.ctor = some (.ctorInfo cvC nP nF) →
        nP = entry.numParams ∧ nF = entry.numFields ∧
          (cvC.type.stripPis (nP + nF)).isSome = true) ∧
    (∀ T cvT caps, c.env.find? T = some (.indInfo cvT caps) →
      (caps.unitlike = true → (cvT.type.stripPis caps.unitParams).isSome = true) ∧
        (caps.eta = true → (cvT.type.stripPis caps.etaParams).isSome = true)) :=
  ⟨fun _ _ _ _ _ hk _ hrl => Ix.Kernel.Open.recRules_fire hrc hk hrl,
    fun _ _ _ _ _ hk _ hrl => Ix.Kernel.Open.recArity_of hwf hrc hk hrl,
    fun _ _ _ _ _ hk _ hrl _ _ _ hc => Ix.Kernel.Open.ruleCtor_arity hrc hk hrl hc,
    fun _ _ _ hpj _ _ _ hc => Ix.Kernel.Open.tableCtor_arity hp hpj hc,
    fun T cvT caps hT => (Ix.Kernel.Open.storedArities_of hwf hrc).1 T cvT caps hT⟩

end IxVM.Refinement.Core
