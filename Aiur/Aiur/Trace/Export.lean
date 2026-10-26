import Aiur.Trace.Compile
import Aiur.Optimized.Activation
import Aiur.Optimized.Physical
import Aiur.Optimized.Grouping.Compile

namespace Aiur.Trace
open Optimized Lean

private def obj (fields : List (String × Json)) := Json.mkObj fields
private def js {α : Type} [ToJson α] (value : α) : Json := Lean.toJson value

def polynomialJson (encode : F → Nat) : Polynomial F → Json
  | .const x => obj [("const", js (encode x))]
  | .var x => obj [("var", js x)]
  | .add a b => obj [("add", js [polynomialJson encode a, polynomialJson encode b])]
  | .sub a b => obj [("sub", js [polynomialJson encode a, polynomialJson encode b])]
  | .mul a b => obj [("mul", js [polynomialJson encode a, polynomialJson encode b])]

def operationJson (encode : F → Nat) (hintPCs : List Nat) : Operation F → Except String Json
  | .assign dest values => return obj [("op", js "assign"), ("dest", js dest),
      ("values", js (values.map (polynomialJson encode)))]
  | .inverse dest value => return obj [("op", js "inverse"), ("dest", js dest),
      ("value", polynomialJson encode value)]
  | .choose dest tests => return obj [("op", js "choose"), ("dest", js dest),
      ("tests", js (tests.map (fun xs => js (xs.map (polynomialJson encode)))))]
  | .failure dest differences => return obj [("op", js "failure"), ("dest", js dest),
      ("differences", js (differences.map (polynomialJson encode)))]
  | .call name args dest => return obj [("op", js "call"), ("name", js name), ("dest", js dest),
      ("args", js (args.map (polynomialJson encode)))]
  | .store type values dest => return obj [("op", js "store"), ("type", Execution.typeJson type),
      ("values", js (values.map (polynomialJson encode))), ("dest", js dest)]
  | .load type address dest => return obj [("op", js "load"), ("type", Execution.typeJson type),
      ("address", polynomialJson encode address), ("dest", js dest)]
  | .hint site type keyType key dest channel => do
      let some pc := hintPCs[site]? | throw "missing execution hint site"
      return obj [("op", js "hint"), ("channel", js channel), ("instruction", js pc), ("type", Execution.typeJson type),
        ("key_type", Execution.typeJson keyType), ("key", js (key.map (polynomialJson encode))), ("dest", js dest)]

def chipJson [Field F] [DecidableEq F] (encode : F → Nat) (source : Circuit.Chip F) : Except String Json := do
  let chip := Activation.compile source
  unless chip.wellFormed do throw s!"invalid activated circuit {source.name}"
  unless chip.stats.maxConstraintDegree ≤ max 2 source.stats.maxConstraintDegree &&
      chip.maxLookupGuardDegree ≤ max 1 source.maxLookupGuardDegree do
    throw s!"activation increased the degree budget in {source.name}"
  let poly := polynomialJson encode
  return obj [("name", js chip.name), ("width", js chip.numVars),
    ("activation", js source.numVars),
    ("inputs", js (chip.inputs.flatMap WireValue.words)), ("output", js (chip.output.words.map poly)),
    ("constraints", js (chip.constraints.map poly)),
    ("sends", js (chip.sends.map fun send => obj [("channel", js send.channel),
      ("args", js ((send.args.flatMap WireValue.words).map poly)), ("result", js send.result.words),
      ("enable", poly send.enable)])),
    ("memory", js (chip.memory.map fun cell => obj [("type", Execution.typeJson cell.value.type),
      ("address", poly cell.address), ("values", js (cell.value.words.map poly)), ("enable", poly cell.enable)]))]

/-- Replay the actual layout functions to retain their otherwise discarded
definitions and compaction columns. Equality checks fail closed if either
compiler evolves without updating its companion metadata. -/
def functionJson [Field F] [DecidableEq F] (encode : F → Nat) (program : Program F)
    (config : Config) (fn : Function F) (layout : LaidOutChip F) (representative : String)
    (bytecode : Execution.Function F) (validateInputs : Bool := true) : Except String Json := do
  let source ← Compiler.function program config fn validateInputs
  let aliases ← resolveAliases source.chip
  let propagatedScopes := if config.propagateScopes then ScopedPropagation.transform aliases else aliases
  let simplified := if config.simplifyConstraints then (ConstraintElimination.run propagatedScopes).chip
    else propagatedScopes
  let degree ← Degree.boundState config simplified
  unless degree.chip == layout.logical do throw s!"trace logical layout mismatch in {fn.name}"
  let merged := (LookupMerging.run config degree.chip layout.layout).chip
  let columns ← if config.propagateValues then do
    let propagated := Propagation.propagate merged merged.numVars (.identity merged)
    let used := propagated.chip.variables
    let columns := (List.range propagated.chip.numVars).filter (used.contains ·)
    unless Propagation.compact propagated.chip columns == layout.chip do
      throw s!"trace final compaction mismatch in {fn.name}"
    pure columns
  else do
    unless merged == layout.chip do throw s!"trace final layout mismatch in {fn.name}"
    pure (List.range merged.numVars)
  let hintPCs := bytecode.code.toList.zipIdx.filterMap fun (op, pc) =>
    match op with | .hint .. => some pc | _ => none
  unless source.hints == hintPCs.length do throw s!"trace hint occurrence mismatch in {fn.name}"
  let steps := source.steps ++ (degree.cache.reverse.map fun (scope, value, dest) =>
    Step.mk scope (.assign [dest] [value])).toArray
  let steps ← steps.mapM fun step => do
    return obj [("guard", polynomialJson encode (source.chip.activation step.scope)),
      ("action", ← operationJson encode hintPCs step.operation)]
  let writes := columns.zipIdx.flatMap fun (old, column) =>
    (layout.layout.occupants[old]?.getD []).map fun id =>
      let guard := match degree.chip.roles[id]? with
        | some (.auxiliary scope) => source.chip.activation scope
        | _ => .const 1
      obj [("column", js column), ("source", js id), ("guard", polynomialJson encode guard)]
  return obj [("name", js fn.name), ("chip", js representative),
    ("witnesses", js degree.chip.roles.size), ("inputs", js (source.chip.inputs.flatMap WireValue.words)),
    ("output", js source.chip.output.words), ("steps", js steps), ("writes", js writes)]

def groupJson [Field F] [DecidableEq F] (encode : F → Nat) (group : Grouping.Layout F) : Json :=
  let poly := polynomialJson encode
  obj [("name", js group.name), ("width", js group.width),
    ("activation", poly group.activation), ("constraints", js (group.constraints.map poly)),
    ("receive", js (group.receive.map poly)),
    ("sends", js (group.sends.map fun s => obj [("enable", poly s.enable), ("args", js (s.args.map poly))])),
    ("members", js (group.members.map fun m => obj [("name", js m.name), ("columns", js m.columns),
      ("selector", js m.selector), ("writes", js (m.writes.map fun (column, value) =>
        obj [("column", js column), ("value", poly value)]))]))]

def exportPreparedJson [Field F] [DecidableEq F] (modulus : Nat) (encode : F → Nat)
    (program : Program F) (artifact : Optimized.Artifact F) (physical : Physical.Prepared artifact)
    (bytecode : Execution.Bytecode F) (groups : List (String × List String) := []) : Except String Json := do
  unless program.functions.length == artifact.layouts.length && program.functions.length == bytecode.functions.length do
    throw "trace program/function count mismatch"
  let functions ← ((program.functions.zip artifact.layouts).zip bytecode.functions).mapM fun ((fn, layout), code) => do
    unless fn.name == code.name do throw "trace bytecode function order mismatch"
    let representative := physical.representative fn.name
    functionJson encode program artifact.config fn layout representative code (artifact.entries.contains fn.name)
  let callableNames := bytecode.functions.map (·.name) ++ bytecode.maps.map (·.name)
  let id := fun name => if callableNames.contains name then pure (callableNames.idxOf name)
    else throw s!"unknown grouped callable {name}"
  let mut used : List String := []
  let mut layouts := []
  for (name, names) in groups do
    let names := (names.map physical.representative).dedup
    let chips := physical.system.chips.filter fun c =>
      names.contains c.name && !used.contains c.name && !artifact.entries.contains c.name
    if chips.length < 2 then continue
    let group ← Grouping.compile name id (chips.map fun c => (Activation.compile c, c.numVars))
    used := used ++ chips.map (·.name)
    layouts := layouts ++ [groupJson encode group]
  return obj [("version", js (2 : Nat)), ("modulus", js modulus),
    ("functions", js functions), ("chips", js (← physical.system.chips.mapM (chipJson encode))),
    ("groups", js layouts)]

def exportJson [Field F] [DecidableEq F] (modulus : Nat) (encode : F → Nat)
    (program : Program F) (artifact : Optimized.Artifact F) (bytecode : Execution.Bytecode F)
    (groups : List (String × List String) := []) : Except String Json := do
  exportPreparedJson modulus encode program artifact (← Physical.prepare artifact) bytecode groups

end Aiur.Trace
