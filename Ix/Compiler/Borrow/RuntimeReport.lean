import Ix.Compiler.Borrow.RuntimeInput
import Ix.Compiler.Borrow.Report

namespace Ix.Compiler.Borrow.Runtime

open Lean
open Ix.Compiler.Ixon (Address)
open IxIR2.Eval
open IxIR2.Borrow.Open (Schema)

deriving instance ToJson for IxIR2.Borrow.Open.Schema
deriving instance ToJson for IxIR2.Borrow.Open.Policy
deriving instance ToJson for Options
deriving instance ToJson for Tree
deriving instance ToJson for Argument

def inputs : Array (String × Argument) := #[
  ("zero", .zero),
  ("succ-0", .succ (.scalar 0)),
  ("succ-1", .succ (.scalar 1)),
  ("succ-wide", .succ (.scalar (2 ^ 256 + 19))),
  ("nested-zero-1", .succ .zero),
  ("nested-zero-8", .succ (Tree.nested 7 .zero)),
  ("nested-zero-32", .succ (Tree.nested 31 .zero)),
  ("nested-scalar-17", .succ (Tree.nested 16 (.scalar 4096)))]

/-- A caller adapter exercises exact PAP saturation of the preserved owned
export. Its construction is separate from source compilation and selection. -/
def dynamicCaller (entry : Address) : IxIR2.Function :=
  { signature := { params := #[{ world := .shared, passing := .owned }], result := .shared, papSafe := false }
    blocks := #[{
      valueParams := #[.owned .shared], creditParams := #[]
      instructions := #[.papp entry #[], .apply (.reg 1) #[.reg 0]]
      terminator := .ret (.reg 2) }] }

def callerAddress : Address := .replicate 240

def withCaller (program : IxIR2.Program) (entry : Address) : IxIR2.Program :=
  { program with declarations := program.declarations ++ [(callerAddress, .fn (dynamicCaller entry))] }

private def checked {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw (IO.userError message)

private def run (validation : IxIR2.Validate.Context) (program : IxIR2.Program)
    (definition : IxIR2.Function) (argument : RVal) (store : Store) : Except String Result :=
  (runFunction (.ofProgram program validation.schemas) .physical definition #[argument] 1000 1000 store).mapError reprStr

private def sourceNumber (source : Coverage.Source) (block : Address) (argument : Argument) : Except String Nat := do
  let ctx := Pipeline.validatedEvalCtx source.constants source.config
  let function ← (Ixon.Eval.eval ctx 1000 (Pipeline.validatedMainFrame source.root) [] Pipeline.validatedMainSource).mapError reprStr
  let result ← (Ixon.Eval.apply ctx 1000 function (argument.tree.sourceValue block)).mapError reprStr
  let .litV (.natL number) := result | throw "runtime Ixon application did not return a Nat literal"
  return number

private def rawNumber {constants root config eraseFuel lowerFuel options}
    {attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel}
    (certified : Certified attached options) (argument : Argument) : Except String Nat := do
  let ctx : IxIR0.Ctx := { env := IxIR0.Env.ofList attached.source.erasure.result.raw }
  let function ← (IxIR0.eval ctx 1000 [] (.ref root)).mapError reprStr
  let result ← (IxIR0.apply ctx 1000 function (argument.source certified.target.schema).value).mapError reprStr
  let .lit (.nat number) := result | throw "runtime raw IxIR0 application did not return a Nat literal"
  return number

private def executeInput {constants root config eraseFuel lowerFuel options}
    {attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel}
    (certified : Certified attached options) (source : Coverage.Source)
    (dataBlock : Address) (name : String) (argument : Argument) : Except String Json := do
  let schema := certified.target.schema
  let input := argument.make schema
  let value : RVal := .loc input.2
  let expected := (argument.major schema).result schema
  let ixon ← sourceNumber source dataBlock argument
  let raw ← rawNumber certified argument
  if ixon != expected || raw != expected then throw "runtime source result disagrees with the structural certificate"
  let validation := attached.target.artifact.validationContext
  let baseline := attached.target.artifact.program
  let rewritten := certified.target.rewrite.program
  let entry := certified.target.entry
  let mut paths := #[]
  for dynamic in [false, true] do
    let beforeProgram := if dynamic then withCaller baseline entry.summary.owner else baseline
    let afterProgram := if dynamic then withCaller rewritten entry.summary.owner else rewritten
    if dynamic then
      let _ ← (IxIR2.Validate.validate validation beforeProgram).mapError reprStr
      let _ ← (IxIR2.Validate.validate validation afterProgram).mapError reprStr
    let beforeDefinition := if dynamic then dynamicCaller entry.summary.owner else entry.before
    let afterDefinition := if dynamic then dynamicCaller entry.summary.owner else IxIR2.Borrow.ownedWrapper entry.summary.borrowed entry.before
    let before ← run validation beforeProgram beforeDefinition value input.1
    let after ← run validation afterProgram afterDefinition value input.1
    let beforePrefixes ← Borrow.prefixesFrom validation {} beforeProgram
      (initialMachine beforeDefinition #[value] 1000 input.1) before
    let afterPrefixes ← Borrow.prefixesFrom validation {} afterProgram
      (initialMachine afterDefinition #[value] 1000 input.1) after
    let allocations := argument.tree.nodes + (if dynamic then 1 else 0)
    let extra := if dynamic then 3 else 0
    if before.value != .lit (.nat expected) || after.value != before.value ||
        before.store.heap.rcops != after.store.heap.rcops + 2 ||
        before.store.heap.allocs != allocations || after.store.heap.allocs != allocations ||
        before.store.heap.frees != allocations || after.store.heap.frees != allocations ||
        before.store.live != 0 || after.store.live != 0 ||
        before.store.peakLiveNodes != allocations || after.store.peakLiveNodes != allocations ||
        1000 - before.controlRemaining != entry.beforeBody.ownedCost (argument.major schema).fieldCost + extra ||
        1000 - after.controlRemaining != entry.afterBody.readCost (argument.major schema).fieldCost + 3 + extra ||
        before.heapRemaining + 1 != after.heapRemaining then
      throw "open borrowed execution drifted from its structural cost/resource laws"
    paths := paths.push (Json.mkObj [
      ("kind", toJson (if dynamic then "dynamic" else "direct")),
      ("baseline", Borrow.resultJson before), ("borrowed", Borrow.resultJson after),
      ("baseline_prefixes", beforePrefixes), ("borrowed_prefixes", afterPrefixes)])
  return Json.mkObj [
    ("name", toJson name), ("argument", toJson argument), ("input_store", toJson input.1),
    ("input_value", toJson value), ("nodes", toJson argument.tree.nodes), ("number", toJson expected),
    ("ixon", toJson ixon), ("raw_ixir0", toJson raw), ("paths", toJson paths)]

private def lender {constants root config eraseFuel lowerFuel options}
    {attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel}
    (certified : Certified attached options) : Except String Json := do
  let argument : Argument := .succ (Tree.nested 7 .zero)
  let input := argument.make certified.target.schema
  let value : RVal := .loc input.2
  let retained ← (retainShared input.1 value >>= (retainShared · value)).mapError reprStr
  let validation := attached.target.artifact.validationContext
  let program := certified.target.rewrite.program
  let result ← run validation program certified.target.entry.after value retained
  let trace ← Borrow.prefixesFrom validation {} program
    (initialMachine certified.target.entry.after #[value] 1000 retained) result
  if toJson result.store != toJson retained || result.value != .lit (.nat certified.target.schema.succResult) then
    throw "borrowed entry changed the caller's aliased lender"
  let mut cleanup := result.store
  let mut fuel := result.heapRemaining
  for _ in [:3] do
    let released ← (releaseShared fuel cleanup value).mapError reprStr
    cleanup := released.1
    fuel := released.2
  if cleanup.live != 0 || cleanup.heap.allocs != cleanup.heap.frees then
    throw "caller could not reclaim the returned lender"
  return Json.mkObj [
    ("argument", toJson argument), ("owners", toJson (3 : Nat)),
    ("input_store", toJson retained), ("input_value", toJson value),
    ("execution", Borrow.resultJson result), ("prefixes", trace),
    ("cleanup_store", toJson cleanup), ("cleanup_remaining", toJson fuel)]

private def fallbacks {constants root config eraseFuel lowerFuel}
    (attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel) : Except String Json := do
  let mut rows := #[]
  for (name, options) in [
      ("disabled", ({ policy := { enabled := false } } : Options)),
      ("inference-budget", { maxAttempts := 0 }),
      ("target-structure-budget", { policy := { maxDepth := 0 } }),
      ("source-structure-budget", { maxSourceDepth := 0 })] do
    let selected := select attached options
    let .error reason := selected.attempt | throw s!"{name}: fallback was not selected"
    if selected.program != attached.target.artifact.program then throw s!"{name}: fallback changed baseline"
    rows := rows.push (Json.mkObj [("name", toJson name), ("options", toJson options),
      ("reason", toJson (reprStr reason)), ("program", toJson selected.program)])
  return toJson rows

structure CaseResult where
  name : String
  row : Json
  snapshot : Json
  compileMs : Nat
  checkMs : Nat

def runCase (depth : Nat) : IO CaseResult := do
  let source ← checked (Runtime.source depth)
  let started ← IO.monoMsNow
  let attached ← checked (source.compile.mapError reprStr)
  let compiled ← IO.monoMsNow
  let selection := select attached
  let certified ← checked (selection.attempt.mapError reprStr)
  let selected ← IO.monoMsNow
  if certified.target.rewrite.summaries.length != depth + 2 || certified.source.chain.depth != depth then
    throw (IO.userError "runtime summary or source chain depth drifted")
  let some block := source.constants[0]? | throw (IO.userError "missing source declaration group")
  let observations ← checked (inputs.mapM fun (name, argument) => executeInput certified source block.1 name argument)
  let lender ← checked (lender certified)
  let fallbacks ← checked (fallbacks attached)
  let nativeBefore ← checked (Borrow.nativeBoundary attached.target.artifact.program)
  let nativeAfter ← checked (Borrow.nativeBoundary certified.target.rewrite.program)
  let row := Json.mkObj [
    ("name", toJson source.name), ("depth", toJson depth), ("source_root", toJson source.root),
    ("snapshot", toJson s!"{source.name}.json"), ("origin", toJson "synthetic-ixon"),
    ("entry", toJson certified.target.entry.summary.owner), ("borrowed_entry", toJson certified.target.entry.summary.borrowed),
    ("factory", toJson certified.target.exported.factoryAddress), ("schema", toJson certified.target.schema),
    ("inference", toJson selection.inference),
    ("baseline_size", Borrow.programSize attached.target.artifact.program),
    ("borrowed_size", Borrow.programSize certified.target.rewrite.program),
    ("runtime_inputs", toJson observations.size), ("native_baseline", toJson nativeBefore), ("native_borrowed", toJson nativeAfter)]
  let snapshot := Json.mkObj [
    ("format", toJson "compilatrix/source-borrow-runtime-case/1"), ("summary", row),
    ("compilation", source.compilationSnapshot attached), ("rewritten", toJson certified.target.rewrite.program),
    ("options", toJson ({} : Options)), ("validation_stats", toJson certified.target.rewrite.checked.stats),
    ("observations", toJson observations), ("lender", lender), ("fallbacks", fallbacks)]
  return { name := source.name, row, snapshot, compileMs := compiled - started, checkMs := selected - compiled }

end Ix.Compiler.Borrow.Runtime
