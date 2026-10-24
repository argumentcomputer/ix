import Ix.Compile.SourceGraph.Stream
import Ix.Cert.SourceGraph
import Ix.Cert.Schedule

/-! Actual pure chunk/task/join correspondence for the prospective producer.
No input-order, code-coherence, name-injectivity or positive-workers premise.
Live caller replacement and the full prepass remain explicitly unwired. -/
namespace Ix.Cert.SourceStream

open Ix (Name ConstantInfo)
open Ix.Compile.SourceGraph
open Ix.Compile.SourceGraph.Stream

theorem inspect_graph (thin : Ix.Environment) (reserved : Bool) (n : Name) (ci : ConstantInfo) :
    (inspect thin reserved n ci).graph = rowOfCanonical n ci := by
  simp only [inspect, rowUsingShared_eq]
  exact SourceGraph.rowUsing_eq n ci _ rfl

def itemSpec (thin : Ix.Environment) (reserved : Lean.ConstantInfo → Bool)
    (p : Name × Lean.ConstantInfo) : Item := inspect thin (reserved p.2) p.1 (Canon.constS p.2)

theorem step_spec (thin : Ix.Environment) (reserved : Lean.ConstantInfo → Bool)
    (p : Name × Lean.ConstantInfo) (s : Ix.CanonM.CanonState) :
    (Id.run ((step thin reserved p).run s)).1 = itemSpec thin reserved p := by
  simp only [step, itemSpec, StateT.run_bind, Id.run_bind, StateT.run_pure, Id.run_pure, Canon.canonConst_run]

/-- The complete Item, including unchanged error/digest/flag computations. -/
theorem chunk_spec (thin : Ix.Environment) (reserved : Lean.ConstantInfo → Bool)
    (input : Array (Name × Lean.ConstantInfo)) : chunk thin reserved input = input.map (itemSpec thin reserved) := by
  unfold chunk
  rw [Array.mapM_eq_mapM_toList]
  simp only [StateT.run'_eq, StateT.run_map, Id.run_map]
  rw [Canon.list_mapM_run _ _ (step_spec thin reserved)]
  rcases input with ⟨xs⟩
  simp

theorem partition_map_flatten {α β : Type} (f : α → β) (input : Array α) (workers : Nat) :
    ((partition input workers).map fun part => part.map f).flatten = input.map f := by
  unfold partition
  rw [Array.map_map]
  exact Schedule.slices_map f input _ _ (Schedule.ceil_mul_ge _ _
    (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)))

theorem partition_flatten {α : Type} (input : Array α) (workers : Nat) :
    (partition input workers).flatten = input := by
  simpa using partition_map_flatten id input workers

/-- Task completion timing cannot change the original row order. -/
theorem tasks_flatten (thin : Ix.Environment) (reserved : Lean.ConstantInfo → Bool)
    (input : Array (Name × Lean.ConstantInfo)) (workers : Nat) :
    ((tasks thin reserved input workers).map Task.get).flatten = input.map (itemSpec thin reserved) := by
  unfold tasks
  simp only [Array.map_map, chunk_spec]
  exact partition_map_flatten (itemSpec thin reserved) input workers

theorem join_eq (pending : Array (Task (Array Item))) :
    join pending = ((pending.map Task.get).flatten).foldl merge {} := by
  rw [Array.foldl_flatten, Array.foldl_map]
  rfl

theorem runLabelled_eq (thin : Ix.Environment) (reserved : Lean.ConstantInfo → Bool)
    (input : Array (Name × Lean.ConstantInfo)) (workers : Nat) :
    runLabelled thin reserved input workers = (input.map (itemSpec thin reserved)).foldl merge {} := by
  unfold runLabelled
  rw [join_eq, tasks_flatten]

private theorem fold_facts (items : List Item) (acc : Output) :
    (items.foldl merge acc).facts = (items.map (·.graph)).foldl mergeRow acc.facts := by
  induction items generalizing acc with
  | nil => rfl
  | cons x xs ih => exact ih (merge acc x)

theorem runLabelled_facts (thin : Ix.Environment) (reserved : Lean.ConstantInfo → Bool)
    (input : Array (Name × Lean.ConstantInfo)) (workers : Nat) :
    (runLabelled thin reserved input workers).facts =
      collect (input.toList.map fun (n, ci) => rowOfCanonical n (Canon.constS ci)) := by
  rw [runLabelled_eq, ← Array.foldl_toList, fold_facts]
  simp only [Array.toList_map, List.map_map, Function.comp_def, itemSpec, inspect_graph, collect]

theorem label_eq (input : Array (Lean.Name × Lean.ConstantInfo)) :
    label input = input.map (fun (n, ci) => (Canon.nameS n, ci)) := by
  simp only [label, Canon.canonName_run]

/-- Complete canonical-map specification, never allocated by runSource. -/
def canonical (input : Array (Lean.Name × Lean.ConstantInfo)) : List (Name × ConstantInfo) :=
  input.toList.map fun (n, ci) => (Canon.nameS n, Canon.constS ci)

theorem runSource_facts (thin : Ix.Environment) (reserved : Lean.ConstantInfo → Bool)
    (input : Array (Lean.Name × Lean.ConstantInfo)) (workers : Nat) :
    (runSource thin reserved input workers).facts =
      collect ((canonical input).map fun (n, ci) => rowOfCanonical n ci) := by
  rw [runSource, runLabelled_facts, label_eq]
  simp only [Array.toList_map, List.map_map, canonical, Function.comp_def]

theorem runSource_workers (thin : Ix.Environment) (reserved : Lean.ConstantInfo → Bool)
    (input : Array (Lean.Name × Lean.ConstantInfo)) (a b : Nat) :
    runSource thin reserved input a = runSource thin reserved input b := by
  simp only [runSource, runLabelled_eq]

theorem runSource_nodes_get (thin : Ix.Environment) (reserved : Lean.ConstantInfo → Bool)
    (input : Array (Lean.Name × Lean.ConstantInfo)) (workers : Nat) (n : Name) :
    (runSource thin reserved input workers).facts.nodes.get? n =
      ((SourceGraph.full (canonical input)).consts.get? n).map capture := by
  rw [runSource_facts]
  exact SourceGraph.collect_nodes_get _ n

theorem runSource_code_get (thin : Ix.Environment) (reserved : Lean.ConstantInfo → Bool)
    (input : Array (Lean.Name × Lean.ConstantInfo)) (workers : Nat) (n : Name) :
    (runSource thin reserved input workers).facts.code.get? n =
      ((SourceGraph.full (canonical input)).consts.get? n).bind keep := by
  rw [runSource_facts]
  exact SourceGraph.collect_code_get _ n

/-- Original-input enumeration is derived from the actual pure producer. -/
theorem runSource_contains (thin : Ix.Environment) (reserved : Lean.ConstantInfo → Bool)
    (input : Array (Lean.Name × Lean.ConstantInfo)) (workers : Nat) (n : Name) :
    (runSource thin reserved input workers).facts.nodes.contains n =
      (SourceGraph.full (canonical input)).consts.contains n := by
  rw [Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.contains_eq_isSome_getElem?]
  change ((runSource thin reserved input workers).facts.nodes.get? n).isSome = _
  rw [runSource_nodes_get]
  simp

theorem runSource_hybrid_get (thin : Ix.Environment) (reserved : Lean.ConstantInfo → Bool)
    (input : Array (Lean.Name × Lean.ConstantInfo)) (workers : Nat) (n : Name) :
    ({ consts := (runSource thin reserved input workers).facts.code
       fallback? := some (SourceGraph.full (canonical input)).get? } : Ix.Environment).get? n =
      (SourceGraph.full (canonical input)).get? n := by
  rw [runSource_facts]
  exact SourceGraph.collected_hybrid_get _ n

end Ix.Cert.SourceStream
