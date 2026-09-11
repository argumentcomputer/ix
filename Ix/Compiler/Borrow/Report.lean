import Ix.Compiler.Borrow.Pipeline
import Ix.Compiler.Borrow.Sources
import Ix.Compiler.IxIR2.Borrow.Examples
import Ix.Compiler.Coverage.Run
import Ix.Compiler.Coverage.HeapSnapshot

namespace Ix.Compiler.Borrow

open Lean Ix.Compiler.Ixon

deriving instance ToJson for IxIR2.Borrow.Summary
deriving instance ToJson for IxIR2.Borrow.Inference
deriving instance ToJson for IxIR2.Borrow.Budget
deriving instance ToJson for Options

def resultJson (result : IxIR2.Eval.Result) : Json :=
  Json.mkObj [("value", toJson result.value), ("store", toJson result.store),
    ("control_remaining", toJson result.controlRemaining), ("heap_remaining", toJson result.heapRemaining)]

def programSize (program : IxIR2.Program) : Json :=
  let functions := program.main :: program.declarations.filterMap fun
    | (_, .fn definition) => some definition
    | _ => none
  Json.mkObj [("declarations", toJson program.declarations.length),
    ("blocks", toJson (functions.foldl (fun n f => n + f.blocks.size) 0)),
    ("instructions", toJson (functions.foldl (fun n f =>
      n + f.blocks.foldl (fun n b => n + b.instructions.size) 0) 0))]

private def controlJson (program : IxIR2.Program) (control : IxIR2.Eval.Control) :
    Except String Json := do
  match control with
  | .halted value => pure (Json.mkObj [("halted", toJson value)])
  | .running frame stack =>
      let owner ← if frame.definition == program.main then pure "main" else do
        let some entry := program.declarations.find? fun entry =>
          match entry.2 with | .fn definition => definition == frame.definition | _ => false
          | throw "execution frame does not belong to the compiled program"
        pure entry.1.toHex
      pure (Json.mkObj [("owner", toJson owner), ("block", toJson frame.block),
        ("pc", toJson frame.pc), ("values", toJson frame.values), ("stack_depth", toJson stack.length)])

/-- Complete heap slots and frame values at every actual evaluator step.
The terminal state must agree with the proof-carrying replay result. -/
def prefixesFrom (context : IxIR2.Validate.Context) (budget : IxIR2.Borrow.Budget)
    (program : IxIR2.Program) (initial : IxIR2.Eval.Machine) (result : IxIR2.Eval.Result) : Except String Json := do
  let mut machine := initial
  let mut rows := #[]
  for step in [:budget.control + 1] do
    rows := rows.push (Json.mkObj [("step", toJson step), ("store", toJson machine.store),
      ("heap_remaining", toJson machine.heapFuel), ("control", ← controlJson program machine.control)])
    match machine.control with
    | .halted value =>
        if toJson machine.store != toJson result.store || toJson value != toJson result.value ||
            machine.heapFuel != result.heapRemaining || step + result.controlRemaining != budget.control then
          throw "execution-prefix terminal state differs from the checked replay"
        return Json.arr rows
    | .running .. =>
        machine ← (IxIR2.Eval.step (IxIR2.Eval.Context.ofProgram program context.schemas)
          .physical machine).mapError (fun error => s!"prefix execution: {repr error}")
  throw "execution-prefix budget exhausted"

def prefixes (context : IxIR2.Validate.Context) (budget : IxIR2.Borrow.Budget)
    (program : IxIR2.Program) (result : IxIR2.Eval.Result) : Except String Json :=
  prefixesFrom context budget program (IxIR2.Eval.initialMachine program.main #[] budget.heap) result

def nativeBoundary (program : IxIR2.Program) : Except String String :=
  match X86.Select.select program with
  | .error (.invalidSource (.invalid _ .schema "missing constructor schema")) =>
      .ok "missingConstructorSchema"
  | .error error => .error s!"unexpected scalar selector boundary: {repr error}"
  | .ok _ => .error "borrowed heap chain unexpectedly became natively selectable"

structure CaseResult where
  name : String
  row : Json
  snapshot : Json
  compileMs : Nat
  borrowMs : Nat

private def checked {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw (IO.userError message)

private def fallbacks (source : Coverage.Source) (attached : source.Attached) :
    Except String Json := do
  let mut rows := #[]
  for (name, options) in [
      ("inference-budget", ({ maxAttempts := 0 } : Options)),
      ("target-replay-budget", { budget := { control := 0 } }),
      ("source-replay-budget", { sourceFuel := 0 })] do
    let selected := select attached options
    let .error reason := selected.attempt | throw s!"{name}: missing checked fallback"
    if selected.program != attached.target.artifact.program then
      throw s!"{name}: fallback changed the checked baseline"
    rows := rows.push (Json.mkObj [("name", toJson name), ("options", toJson options),
      ("reason", toJson (reprStr reason)), ("program", toJson selected.program)])
  return Json.arr rows

def runCase (depth : Nat) (successorCase : Bool) : IO CaseResult := do
  let source ← checked (Examples.source depth successorCase)
  let number := if successorCase then 22 else 11
  let start ← IO.monoMsNow
  let attached ← checked (source.compile.mapError (fun error => s!"source compilation: {repr error}"))
  let compiled ← IO.monoMsNow
  let selection := select attached
  let improved ← checked (selection.attempt.mapError (fun error => s!"borrow selection: {repr error}"))
  let borrowed ← IO.monoMsNow
  let before := improved.target.before.result
  let after := improved.target.after.result
  let program := improved.target.rewrite.program
  let baseline := attached.target.artifact.program
  let context := attached.target.artifact.validationContext
  let observations ← checked (source.observe attached number)
  if improved.source.number != number || before.store.heap.rcops != 5 || after.store.heap.rcops != 3 ||
      before.store.heap.allocs != 3 || after.store.heap.allocs != 3 ||
      before.store.peakLiveNodes != 2 || after.store.peakLiveNodes != 2 ||
      improved.target.rewrite.summaries.length != depth + 3 then
    throw (IO.userError "borrow witness result, RC, peak, or inferred ABI count drifted")
  let nativeBefore ← checked (nativeBoundary baseline)
  let nativeAfter ← checked (nativeBoundary program)
  let fallback ← if depth == 0 && !successorCase then checked (fallbacks source attached)
    else pure (toJson (#[] : Array Json))
  let beforePrefixes ← checked (prefixes context {} baseline before)
  let afterPrefixes ← checked (prefixes context {} program after)
  let row := Json.mkObj [
    ("name", toJson source.name), ("depth", toJson depth), ("successor", toJson successorCase),
    ("origin", toJson "synthetic-ixon"), ("source_root", toJson source.root),
    ("number", toJson number), ("snapshot", toJson s!"{source.name}.json"),
    ("baseline", toJson before.store.counters), ("borrowed", toJson after.store.counters),
    ("baseline_size", programSize baseline), ("borrowed_size", programSize program),
    ("inference", toJson selection.inference),
    ("baseline_control_steps", toJson (1000 - before.controlRemaining)),
    ("borrowed_control_steps", toJson (1000 - after.controlRemaining)),
    ("baseline_heap_work", toJson (1000 - before.heapRemaining)),
    ("borrowed_heap_work", toJson (1000 - after.heapRemaining)),
    ("native_baseline", toJson nativeBefore), ("native_borrowed", toJson nativeAfter)]
  let snapshot := Json.mkObj [
    ("format", toJson "compilatrix/source-borrow-case/1"), ("summary", row),
    ("compilation", source.compilationSnapshot attached), ("options", toJson ({} : Options)),
    ("rewritten", toJson program), ("validation_stats", toJson improved.target.rewrite.checked.stats),
    ("observations", observations.stages), ("baseline_execution", resultJson before),
    ("borrowed_execution", resultJson after), ("baseline_prefixes", beforePrefixes),
    ("borrowed_prefixes", afterPrefixes), ("fallbacks", fallback)]
  return { name := source.name, row, snapshot
           compileMs := compiled - start, borrowMs := borrowed - compiled }

end Ix.Compiler.Borrow
