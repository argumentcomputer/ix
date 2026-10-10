import Ix.CompileCert.Pj.RecRead
import Ix.CompileCert.Pj.TeleTyped
import Ix.CompileCert.Pj.TelePredicateAnySort

/-! Dependent motive choice at the original universe assignment.
These lemmas prepare the recursor induction theorem. -/

namespace Ix.CompileCert.Pj

open Kernel.SetTheory Kernel.SetModel
open Ix.CompileCert (pushArguments)

universe u

variable {V : Type u} [Kernel.SetTheory V]
  {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat}

theorem RecRd.motive_graph {r : Kernel.Name} {R : RecRd}
    (checked : R.Check env r) {m : MotiveRd} (member : m ∈ R.motives) :
    ∀ p ∈ m.tele R.np, Kernel.regime φ p.2.pw ≠ 0 := by
  intro p inside
  have metadata := checked.2.2.2.1 m member p inside
  rw [metadata]
  simp only [Bridge.regime_never]
  decide

/-- Previously selected motive values are removed by the proved valuation
lift relation. No replacement of the universe assignment, zero-sort
condition, or syntactic name for a semantic argument is needed. -/
theorem motive_value_choice (np : Nat) (m : MotiveRd)
    (graph : ∀ p ∈ m.tele np, Kernel.regime φ p.2.pw ≠ 0)
    (ρ : Nat → V) (selected : List V) {A : V}
    (domain : Kernel.Denotes cval env φ (pushArguments ρ selected)
      ((m.type np).liftLooseBVars selected.length 0) A)
    (predicate : List V → Prop) :
    ∃ M, M ∈ˢ A ∧ ∀ arguments,
      TeleTyped cval env φ ρ ((m.tele np).map Prod.fst) arguments →
      arguments.foldl app M = truthVal (predicate arguments) := by
  have unlifted := denotes_unlift selected.length (m.type np)
    (valuationLift_prefix ρ selected) domain
  obtain ⟨M, member, applies⟩ :=
    tele_predicate_any_sort (m.tele np) graph unlifted predicate
  refine ⟨M, member, ?_⟩
  intro arguments typed
  exact applies arguments (pushArguments ρ arguments) typed.installed
    (by simpa only [List.length_map] using typed.length)

end Ix.CompileCert.Pj
