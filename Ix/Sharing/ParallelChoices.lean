module

public import Init.Data.Array.Lemmas
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Ix.Sharing.ParallelChoices

structure Branch (α : Type) where
  remaining : List α
  chosen : List α
  deriving Inhabited, Repr

/-- Split only an initial decision prefix. A leaf retains the suffix to be
walked by the existing bounded evaluator, not its exponential list of choices. -/
def frontier : Nat → List α → List α → List (Branch α)
  | 0, remaining, chosen => [⟨remaining, chosen⟩]
  | _ + 1, [], chosen => [⟨[], chosen⟩]
  | depth + 1, member :: rest, chosen =>
    frontier depth rest chosen ++ frontier depth rest (member :: chosen)

theorem one_le_two_pow (depth : Nat) : 1 ≤ 2 ^ depth := by
  induction depth with
  | zero => simp
  | succ depth ih => rw [Nat.pow_succ]; omega

theorem frontier_length (depth : Nat) (remaining chosen : List α) :
    (frontier depth remaining chosen).length ≤ 2 ^ depth := by
  induction depth generalizing remaining chosen with
  | zero => simp [frontier]
  | succ depth ih =>
    cases remaining with
    | nil => simpa only [frontier, List.length_singleton] using one_le_two_pow (depth + 1)
    | cons member rest =>
      have first := ih rest chosen
      have second := ih rest (member :: chosen)
      simp only [frontier, List.length_append, Nat.pow_succ]
      omega

/-- Every requested depth is capped before constructing a frontier. -/
def boundedDepth (depth : Nat) : Nat := if depth ≤ 3 then depth else 3

theorem bounded_frontier_length (depth : Nat) (remaining chosen : List α) :
    (frontier (boundedDepth depth) remaining chosen).length ≤ 8 := by
  have bound := frontier_length (boundedDepth depth) remaining chosen
  have small : boundedDepth depth ≤ 3 := by unfold boundedDepth; split <;> omega
  have cases : boundedDepth depth = 0 ∨ boundedDepth depth = 1 ∨
      boundedDepth depth = 2 ∨ boundedDepth depth = 3 := by omega
  rcases cases with h | h | h | h <;> rw [h] at bound ⊢ <;>
    exact Nat.le_trans bound (by decide)

theorem frontier_fold (run : List α → List α → β → β)
    (split : ∀ member rest chosen acc,
      run (member :: rest) chosen acc = run rest (member :: chosen) (run rest chosen acc))
    (depth : Nat) (remaining chosen : List α) (initial : β) :
    (frontier depth remaining chosen).foldl
      (fun acc branch => run branch.remaining branch.chosen acc) initial =
      run remaining chosen initial := by
  induction depth generalizing remaining chosen initial with
  | zero => simp [frontier]
  | succ depth ih =>
    cases remaining with
    | nil => simp [frontier]
    | cons member rest =>
      simp only [frontier, List.foldl_append]
      rw [ih, ih]
      exact (split member rest chosen initial).symm

/-- Materialize at most eight task handles before the first join. -/
def evaluate (run : Branch α → β) (branches : Array (Branch α)) : Array β :=
  let pending := branches.map fun branch => Task.spawn fun _ => run branch
  pending.map Task.get

theorem evaluate_eq (run : Branch α → β) (branches : Array (Branch α)) :
    evaluate run branches = branches.map run := by
  simp only [evaluate, Array.map_map, Function.comp_def]
  rfl

def run (depth : Nat) (remaining chosen : List α) (zero : β)
    (merge : β → β → β) (branch : List α → List α → β → β) : β :=
  let branches := (frontier (boundedDepth depth) remaining chosen).toArray
  (evaluate (fun work => branch work.remaining work.chosen zero) branches).foldl merge zero

theorem run_eq (branch : List α → List α → β → β) (merge : β → β → β) (zero : β)
    (split : ∀ member rest chosen acc,
      branch (member :: rest) chosen acc =
        branch rest (member :: chosen) (branch rest chosen acc))
    (combine : ∀ remaining chosen acc,
      merge acc (branch remaining chosen zero) = branch remaining chosen acc)
    (depth : Nat) (remaining chosen : List α) :
    run depth remaining chosen zero merge branch = branch remaining chosen zero := by
  unfold run
  dsimp only
  rw [evaluate_eq, Array.foldl_map, List.foldl_toArray]
  have same : (fun acc (work : Branch α) => merge acc (branch work.remaining work.chosen zero)) =
      (fun acc work => branch work.remaining work.chosen acc) := by
    funext acc work
    exact combine work.remaining work.chosen acc
  rw [same]
  exact frontier_fold branch split _ remaining chosen zero

end Ix.Sharing.ParallelChoices
