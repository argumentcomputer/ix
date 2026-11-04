import Aiur.Trace.Compile
import Aiur.Trace.Parallel
import Aiur.Optimized.Activation
import Aiur.Optimized.Physical
import Aiur.Optimized.Grouping.Plan
import Aiur.Image

/-! Export of the certified compiler's output. The producers build the
typed runtime image (`Aiur.Image`) after checking that the replayed
population plans match the certified layouts; the JSON exporters render the
diagnostic JSON artifact from that image. -/

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

def operationImage (encode : F → Nat) (hintPCs : List Nat) : Operation F → Except String Image.Action
  | .assign dest values => do
    let values ← values.toArray.mapM (Image.poly encode)
    return .assign dest.toArray values
  | .inverse dest value => do
    let value ← Image.poly encode value
    return .inverse dest value
  | .choose dest tests => do
    let tests ← tests.toArray.mapM fun xs => xs.toArray.mapM (Image.poly encode)
    return .choose dest.toArray tests
  | .failure dest differences => do
    let differences ← differences.toArray.mapM (Image.poly encode)
    return .failure dest.toArray differences
  | .call name args dest => do
    let args ← args.toArray.mapM (Image.poly encode)
    return .call name args dest.toArray
  | .store type values dest => do
    let values ← values.toArray.mapM (Image.poly encode)
    return .store (Image.ty type) values dest
  | .load type address dest => do
    let address ← Image.poly encode address
    return .load (Image.ty type) address dest.toArray
  | .hint site type keyType key dest channel => do
    let some pc := hintPCs[site]? | throw "missing execution hint site"
    let key ← key.toArray.mapM (Image.poly encode)
    return .hint channel pc (Image.ty type) (Image.ty keyType) key dest.toArray

def chipImage [Field F] [DecidableEq F] (encode : F → Nat) (source : Circuit.Chip F) :
    Except String Image.Chip := do
  let chip := Activation.compile source
  unless chip.wellFormed do throw s!"invalid activated circuit {source.name}"
  unless chip.stats.maxConstraintDegree ≤ max 2 source.stats.maxConstraintDegree &&
      chip.maxLookupGuardDegree ≤ max 1 source.maxLookupGuardDegree do
    throw s!"activation increased the degree budget in {source.name}"
  let poly := Image.poly encode
  let polys := fun (ps : List (Polynomial F)) => ps.toArray.mapM poly
  return { name := chip.name, width := chip.numVars, activation := source.numVars
           inputs := (chip.inputs.flatMap WireValue.words).toArray
           output := ← polys chip.output.words
           constraints := ← polys chip.constraints
           sends := ← chip.sends.toArray.mapM fun send => do
             return { channel := send.channel, args := ← polys (send.args.flatMap WireValue.words)
                      result := send.result.words.toArray, enable := ← poly send.enable }
           memory := ← chip.memory.toArray.mapM fun cell => do
             return { type := Image.ty cell.value.type, address := ← poly cell.address
                      values := ← polys cell.value.words, enable := ← poly cell.enable } }

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

/-- The actual layout functions replayed from the source function alone, to
retain their otherwise discarded definitions and compaction columns. The
replay does not depend on the certified layout, so it can run while the
certified compiler runs; `functionJsonOf` then checks it against the layout. -/
structure Replay (F : Type) where
  source : Compiler.Result F
  degree : Degree.State F
  layout : ColumnLayout
  /-- The final chip this replay reproduces, before comparison with the layout. -/
  chip : Circuit.Chip F
  columns : List Nat

def replayFunction [Field F] [DecidableEq F] (program : Program F) (config : Config)
    (fn : Function F) (validateInputs : Bool := true) : Except String (Replay F) := do
  let source ← Compiler.function program config fn validateInputs
  let aliases ← resolveAliases source.chip
  let propagatedScopes := if config.propagateScopes then ScopedPropagation.transform aliases else aliases
  let simplified := if config.simplifyConstraints then (ConstraintElimination.run propagatedScopes).chip
    else propagatedScopes
  let degree ← Degree.boundState config simplified
  let layout := allocateColumns config degree.chip
  let merged := (LookupMerging.run config degree.chip layout).chip
  if config.propagateValues then
    let propagated := Propagation.propagate merged merged.numVars (.identity merged)
    let used := propagated.chip.variables
    let columns := (List.range propagated.chip.numVars).filter (used.contains ·)
    return ⟨source, degree, layout, Propagation.compact propagated.chip columns, columns⟩
  else
    return ⟨source, degree, layout, merged, List.range merged.numVars⟩

/-- Check a replay against the certified layout and emit its population plan.
Equality checks fail closed if either compiler evolves without updating its
companion metadata. -/
def functionJsonOf [Field F] [DecidableEq F] (encode : F → Nat) (config : Config) (fn : Function F)
    (replay : Replay F) (layout : LaidOutChip F) (representative : String)
    (bytecode : Execution.Function F) : Except String Json := do
  let ⟨source, degree, replayed, chip, columns⟩ := replay
  unless degree.chip == layout.logical do throw s!"trace logical layout mismatch in {fn.name}"
  unless replayed == layout.layout do throw s!"trace column allocation mismatch in {fn.name}"
  unless chip == layout.chip do
    throw (if config.propagateValues then s!"trace final compaction mismatch in {fn.name}"
      else s!"trace final layout mismatch in {fn.name}")
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

/-- Check a replay against the certified layout and emit its population
plan, as `functionJsonOf` does. -/
def functionImageOf [Field F] [DecidableEq F] (encode : F → Nat) (config : Config) (fn : Function F)
    (replay : Replay F) (layout : LaidOutChip F) (representative : String)
    (bytecode : Execution.Function F) : Except String Image.FunctionPlan := do
  let ⟨source, degree, replayed, chip, columns⟩ := replay
  unless degree.chip == layout.logical do throw s!"trace logical layout mismatch in {fn.name}"
  unless replayed == layout.layout do throw s!"trace column allocation mismatch in {fn.name}"
  unless chip == layout.chip do
    throw (if config.propagateValues then s!"trace final compaction mismatch in {fn.name}"
      else s!"trace final layout mismatch in {fn.name}")
  let hintPCs := bytecode.code.toList.zipIdx.filterMap fun (op, pc) =>
    match op with | .hint .. => some pc | _ => none
  unless source.hints == hintPCs.length do throw s!"trace hint occurrence mismatch in {fn.name}"
  let steps := source.steps ++ (degree.cache.reverse.map fun (scope, value, dest) =>
    Step.mk scope (.assign [dest] [value])).toArray
  let steps ← steps.mapM fun step => do
    return { guard := ← Image.poly encode (source.chip.activation step.scope)
             action := ← operationImage encode hintPCs step.operation : Image.Step }
  let writes ← (columns.zipIdx.flatMap fun (old, column) =>
    (layout.layout.occupants[old]?.getD []).map fun id =>
      let guard := match degree.chip.roles[id]? with
        | some (.auxiliary scope) => source.chip.activation scope
        | _ => .const 1
      (column, id, guard)).toArray.mapM fun (column, source, guard) => do
    return { column, source, guard := ← Image.poly encode guard : Image.ColumnWrite }
  return { name := fn.name, chip := representative, witnesses := degree.chip.roles.size
           inputs := (source.chip.inputs.flatMap WireValue.words).toArray
           output := source.chip.output.words.toArray, steps, writes }

def functionJson [Field F] [DecidableEq F] (encode : F → Nat) (program : Program F)
    (config : Config) (fn : Function F) (layout : LaidOutChip F) (representative : String)
    (bytecode : Execution.Function F) (validateInputs : Bool := true) : Except String Json := do
  functionJsonOf encode config fn (← replayFunction program config fn validateInputs) layout
    representative bytecode

def groupImage [Field F] [DecidableEq F] (encode : F → Nat) (group : Grouping.Layout F) :
    Except String Image.Group := do
  let poly := Image.poly encode
  let polys := fun (ps : List (Polynomial F)) => ps.toArray.mapM poly
  return { name := group.name, width := group.width, activation := ← poly group.activation
           constraints := ← polys group.constraints, receive := ← polys group.receive
           sends := ← group.sends.toArray.mapM fun s => do
             return { enable := ← poly s.enable, args := ← polys s.args }
           members := ← group.members.toArray.mapM fun m => do
             return { name := m.name, columns := m.columns, selector := m.selector
                      writes := ← m.writes.toArray.mapM fun (column, value) => do
                        return { column, value := ← poly value } } }

def groupJson [Field F] [DecidableEq F] (encode : F → Nat) (group : Grouping.Layout F) : Json :=
  let poly := polynomialJson encode
  obj [("name", js group.name), ("width", js group.width),
    ("activation", poly group.activation), ("constraints", js (group.constraints.map poly)),
    ("receive", js (group.receive.map poly)),
    ("sends", js (group.sends.map fun s => obj [("enable", poly s.enable), ("args", js (s.args.map poly))])),
    ("members", js (group.members.map fun m => obj [("name", js m.name), ("columns", js m.columns),
      ("selector", js m.selector), ("writes", js (m.writes.map fun (column, value) =>
        obj [("column", js column), ("value", poly value)]))]))]

def exportPreparedImage [Field F] [DecidableEq F] (modulus : Nat) (encode : F → Nat)
    (program : Program F) (artifact : Optimized.Artifact F) (physical : Physical.Prepared artifact)
    (bytecode : Execution.Bytecode F) (groups : List (String × List String) := [])
    (replays : Option (List (Except String (Replay F))) := none) : Except String Image.Trace := do
  unless program.functions.length == artifact.layouts.length && program.functions.length == bytecode.functions.length do
    throw "trace program/function count mismatch"
  if let some replays := replays then
    unless replays.length == program.functions.length do throw "trace replay count mismatch"
  let functions ← ((program.functions.zip artifact.layouts).zip bytecode.functions).zipIdx.parMapM
      fun (((fn, layout), code), index) => do
    unless fn.name == code.name do throw "trace bytecode function order mismatch"
    let representative := physical.representative fn.name
    let replay ← match replays with
      | some replays => replays[index]?.getD (throw "missing trace replay")
      | none => replayFunction program artifact.config fn (artifact.entries.contains fn.name)
    functionImageOf encode artifact.config fn replay layout representative code
  let callableNames := bytecode.functions.map (·.name) ++ bytecode.maps.map (·.name)
  let id := fun name => if callableNames.contains name then pure (callableNames.idxOf name)
    else throw s!"unknown grouped callable {name}"
  let mut used : List String := []
  let mut selected : Array (String × List (Circuit.Chip F)) := #[]
  for (name, names) in groups do
    let names := (names.map physical.representative).dedup
    let chips := physical.system.chips.filter fun c =>
      names.contains c.name && !used.contains c.name && !artifact.entries.contains c.name
    if chips.length < 2 then continue
    used := used ++ chips.map (·.name)
    selected := selected.push (name, chips)
  let packed ← selected.toList.parMapM fun (name, chips) => do
    return (⟨chips, ← Grouping.compile name id chips⟩ : Grouping.Packed F id)
  let plan ← Grouping.preparePlan physical.system id packed
  if modulus ≥ 2 ^ 64 then throw "trace export requires a modulus fitting UInt64"
  return { version := 2, modulus := modulus.toUInt64, functions := functions.toArray
           chips := (← physical.system.chips.parMapM (chipImage encode)).toArray
           groups := ← plan.groups.toArray.mapM fun p => groupImage encode p.checked.layout }

/-- The diagnostic JSON of `exportPreparedImage`. -/
def exportPreparedJson [Field F] [DecidableEq F] (modulus : Nat) (encode : F → Nat)
    (program : Program F) (artifact : Optimized.Artifact F) (physical : Physical.Prepared artifact)
    (bytecode : Execution.Bytecode F) (groups : List (String × List String) := [])
    (replays : Option (List (Except String (Replay F))) := none) : Except String Json := do
  (← exportPreparedImage modulus encode program artifact physical bytecode groups replays).toJson

def exportImage [Field F] [DecidableEq F] (modulus : Nat) (encode : F → Nat)
    (program : Program F) (artifact : Optimized.Artifact F) (bytecode : Execution.Bytecode F)
    (groups : List (String × List String) := []) : Except String Image.Trace := do
  exportPreparedImage modulus encode program artifact (← Physical.prepare artifact) bytecode groups

def exportJson [Field F] [DecidableEq F] (modulus : Nat) (encode : F → Nat)
    (program : Program F) (artifact : Optimized.Artifact F) (bytecode : Execution.Bytecode F)
    (groups : List (String × List String) := []) : Except String Json := do
  exportPreparedJson modulus encode program artifact (← Physical.prepare artifact) bytecode groups

/-- Compile a prepared module program and export its population plans. The
trace replays do not depend on the certified layouts, so they run on their own
tasks while the certified compiler lays out functions in parallel
(`compileParallel` is proven equal to `Optimized.compile`). -/
def exportModulesImage [Field F] [DecidableEq F] {source : Modules.Program F}
    (prepared : Modules.Prepared source) (modulus : Nat) (encode : F → Nat)
    (bytecode : Execution.Bytecode F) (groups : List (String × List String) := [])
    (config : Config := {}) : IO Image.Trace := do
  let specialized ← IO.ofExcept (Generic.specialize prepared.environment.source prepared.entries)
  let inlined ← IO.ofExcept (Inlining.prepare specialized.program specialized.inlineNames prepared.entries)
  let program := inlined.program
  let replays ← program.functions.mapM fun fn => IO.asTask <| IO.lazyPure fun _ =>
    replayFunction program config fn (prepared.entries.contains fn.name)
  let artifact ← IO.ofExcept (compileParallel program prepared.entries config)
  let physical ← IO.ofExcept (Physical.prepare artifact)
  let replays ← replays.mapM fun replay => do IO.ofExcept (← IO.wait replay)
  IO.ofExcept (exportPreparedImage modulus encode program artifact physical bytecode groups (some replays))

/-- The diagnostic JSON of `exportModulesImage`. -/
def exportModulesJson [Field F] [DecidableEq F] {source : Modules.Program F}
    (prepared : Modules.Prepared source) (modulus : Nat) (encode : F → Nat)
    (bytecode : Execution.Bytecode F) (groups : List (String × List String) := [])
    (config : Config := {}) : IO Json := do
  IO.ofExcept (← exportModulesImage prepared modulus encode bytecode groups config).toJson

/-- The runtime image of a prepared module program: its execution bytecode
and its certified trace artifact. -/
def modulesImage [Field F] [DecidableEq F] {source : Modules.Program F}
    (prepared : Modules.Prepared source) (exported : Execution.Export F) (modulus : Nat)
    (encode : F → Nat) (groups : List (String × List String) := []) (config : Config := {}) :
    IO Image.RuntimeImage := do
  let program ← IO.ofExcept (Image.program exported modulus encode)
  let trace ← exportModulesImage prepared modulus encode exported.bytecode groups config
  return { program, trace }

end Aiur.Trace
