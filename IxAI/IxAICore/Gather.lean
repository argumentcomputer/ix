import IxAICore.Decision

/-!
# Training as a fold over gathered batches

`train` looks every scheduled index up in the example list as it steps. `gather` does all of
those lookups up front, so training is a plain fold of `Model.step` over a list of batches
(`train_eq_foldl_gather`). A program that takes the batches already gathered computes `train`
whenever it folds `Model.step` over `gather examples schedule`; the dataset enters through that
argument rather than through the program.
-/

namespace IxAICore

/-- The batches a schedule selects: every index replaced by its example, or by `d` when the
index is out of range. -/
def gather {α : Type} [Inhabited α] (examples : List α) (schedule : List (List Nat))
    (d : α := default) : List (List α) :=
  schedule.map fun idx => idx.map fun i => getD examples i d

/-- **Training is a fold of `Model.step` over the gathered batches.** The out-of-range default
is the spec's example of the default state, as in `Config.stepFn`. -/
theorem train_eq_foldl_gather {σ : Type} [Inhabited σ] (s : Spec σ) (c : Config) :
    train s c =
      (gather ((c.data s).map s.example) c.schedule (s.example default)).foldl
        (fun m b => m.step ⟨c.lrRaw⟩ b) (c.init s) := by
  unfold train gather
  rw [List.foldl_map]
  rfl

end IxAICore
