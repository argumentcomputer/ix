module

public import Ix.Sharing.FamilyContext
public import Ix.Sharing.FamilyParallel
import all Ix.Sharing.FamilyContext

@[expose] public section

namespace Ix.Sharing.Family.ParallelStage

open Ix.Sharing.Exact

def trace (depth : Nat) (cfg : Config) (width index : Nat) (members : Array Nat)
    (areaSize closureSize : Nat) (eval : (Nat → Bool) → Array Nat → Nat × Nat) : ComponentTrace :=
  let baseline := (eval (fun _ => false) #[]).1
  let cost : Cost := fun selected => ((eval selected.contains selected).1 : _root_.Int) - baseline
  let size := members.size
  let exact := size ≤ cfg.exactLimit
  { width, index, exact, members, areaSize, closureSize,
    rows := Parallel.tableWithDepth depth cfg cost members.toList,
    evaluations := if exact then 2 ^ size else size * (size + 1) / 2 + size + 1 }

theorem trace_eq (depth : Nat) (cfg : Config) (width index : Nat) (members : Array Nat)
    (areaSize closureSize : Nat) (eval : (Nat → Bool) → Array Nat → Nat × Nat) :
    trace depth cfg width index members areaSize closureSize eval =
      LightContext.trace cfg width index members areaSize closureSize eval := by
  simp only [trace, LightContext.trace, Parallel.tableWithDepth_eq]

def step (depth : Nat) (cfg : Config) (limits : Limits) (ex : Expanded) (stage : UStage)
    (width : Nat) (parents : Array (Array Nat)) (base : TBase) (acc : FamilyState)
    (members : Array Nat) : Except SharingError FamilyState := do
  let ((results, states, work), areaPositions, closurePositions) := acc
  let nextStates ← bump states (familyCalls cfg members.size) limits.maxStates .states
  if members.all (fun m => decide (m < ex.dag.size) && !stage.up.opaq[m]!) then
    let area := componentArea stage.up stage.f members
    let areaPositions := setPositions areaPositions area
    if areaOK ex.dag.size stage.up.opaq parents members area areaPositions then
      let (marks, found, stack) := upWalk parents members closurePositions
      if stack.isEmpty && area.all (fun y => marks[y]! != 0) then
        let light := LightContext.context stage members area
        if localSearchOK light then
          let nextWork ← bump work (familyWork cfg members.size found.size) limits.maxCostEvals .costEvals
          let aux := LightContext.auxiliary ex stage base area areaPositions found marks
          let closurePositions := clearPositions marks found
          let cached := Thunk.mk fun _ => LightContext.fullContext ex stage members
          let result ← retainedResult stage.slack
            (trace depth cfg width results.size members area.size found.size
              (phiA light areaPositions base aux (LightContext.forceContext cached)))
          return ((results.push result, nextStates, nextWork),
            clearPositions areaPositions area, closurePositions)
        else
          familyStepArea cfg limits ex stage width parents base
            ((results, states, work), clearPositions areaPositions area, clearPositions marks found) members
      else
        familyStepArea cfg limits ex stage width parents base
          ((results, states, work), clearPositions areaPositions area, clearPositions marks found) members
    else
      familyStepArea cfg limits ex stage width parents base
        ((results, states, work), clearPositions areaPositions area, closurePositions) members
  else
    familyStepArea cfg limits ex stage width parents base
      ((results, states, work), areaPositions, closurePositions) members

theorem step_eq (depth : Nat) (cfg : Config) (limits : Limits) (ex : Expanded) (stage : UStage)
    (width : Nat) (parents : Array (Array Nat)) (base : TBase) (acc : FamilyState)
    (members : Array Nat) :
    step depth cfg limits ex stage width parents base acc members =
      LightContext.step cfg limits ex stage width parents base acc members := by
  simp only [step, trace_eq]
  rfl

theorem step_eq_function (depth : Nat) : step depth = LightContext.step := by
  funext cfg limits ex stage width parents base acc members
  exact step_eq depth cfg limits ex stage width parents base acc members

def components (depth : Nat) (cfg : Config) (limits : Limits) (ex : Expanded) (stage : UStage)
    (width : Nat) (parents : Array (Array Nat)) : Except SharingError MeterState :=
  let base := TBase.ofPrep stage.up.prep stage.up.w stage.up.opaq
  if tStageOK stage.up.prep stage.up.w stage.up.opaq base then
    (stage.comps.foldlM (step depth cfg limits ex stage width parents base)
      ((#[], 0, 0), Array.replicate stage.up.prep.dag.size 0, Array.replicate ex.dag.size 0)).map (·.1)
  else familyComponents cfg limits ex stage width parents

/-- Exact full stage result for every input, including counters, first refusal
and fallback paths. No stage-validity premise or new budget is introduced. -/
theorem components_eq (depth : Nat) (cfg : Config) (limits : Limits) (ex : Expanded)
    (stage : UStage) (width : Nat) (parents : Array (Array Nat)) :
    components depth cfg limits ex stage width parents =
      LightContext.components cfg limits ex stage width parents := by
  simp only [components, step_eq_function]
  rfl

end Ix.Sharing.Family.ParallelStage
