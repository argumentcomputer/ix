import Aiur.Optimized.Program

/-! Parallel evaluation of the certified optimized compiler for exporters.
`Optimized.compile` lays out every function independently before
deduplicating the system. `compileParallel` evaluates those layouts on
separate tasks and is proven equal to `Optimized.compile`, so it yields the
same certified artifact. -/
namespace Aiur.Trace
open Optimized

/-- `List.mapM` in `Except`, with every element evaluated on its own task.
Results and the first error in list order are those of `List.mapM`. -/
def _root_.List.parMapM {α β ε : Type} (xs : List α) (f : α → Except ε β) : Except ε (List β) :=
  (xs.map fun x => Task.spawn fun _ => f x).mapM Task.get

theorem _root_.List.parMapM_eq {α β ε : Type} (xs : List α) (f : α → Except ε β) :
    xs.parMapM f = xs.mapM f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.parMapM, List.map_cons, List.mapM_cons] at ih ⊢
      rw [ih]
      rfl

variable {F : Type} [Field F] [DecidableEq F]

/-- `Optimized.compile` with the per-function layouts evaluated in parallel. -/
def compileParallel (program : Program F) (entries : List String)
    (config : Config := {}) : Except String (Artifact F) := do
  if config.maxDegree < 3 then throw "the optimized compiler requires a degree cap of at least three"
  let _ ← (typecheck program).mapError reprStr
  for entry in entries do
    if (program.findFunction? entry).isNone then throw s!"unknown entrypoint {entry}"
    let _ ← (checkEntry program entry).mapError reprStr
  for declaration in program.enums do
    let _ ← (Circuit.checkEnumTags F declaration).mapError reprStr
  let layouts ← program.functions.parMapM fun fn => do
    layOut config (← Optimized.Compiler.function program config fn (entries.contains fn.name))
  let initial : Circuit.System F := ⟨layouts.map (·.chip), program.enums, program.tables, program.maps⟩
  let deduplicate : Except String (Dedup.CheckedResult initial entries) := if config.deduplicate then Dedup.run initial entries
    else Dedup.certify initial entries (Dedup.identity initial)
  let result ← deduplicate
  let _ ← (Circuit.checkChips [] result.system.chips).mapError reprStr
  if h : result.system.chips.all (fun chip => decide
      (chip.stats.maxConstraintDegree ≤ config.maxDegree ∧ chip.stats.maxLookupDegree ≤ 2 ∧ chip.maxLookupGuardDegree ≤ 1)) = true then
    return {
      config, entries, layouts, system := result.system, representatives := result.representatives
      unmerged := initial
      deduplication := result.certificate
      degreeBound := by
        intro chip member
        exact of_decide_eq_true (List.all_eq_true.mp h chip member)
    }
  else throw "optimized degree bound failed"

theorem compileParallel_eq (program : Program F) (entries : List String) (config : Config) :
    compileParallel program entries config = compile program entries config := by
  unfold compileParallel compile
  simp only [List.parMapM_eq]

end Aiur.Trace
