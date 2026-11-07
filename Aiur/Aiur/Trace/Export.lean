import Aiur.Trace.Compile
import Aiur.Optimized.Activation
import Aiur.Optimized.Physical
import Aiur.Optimized.Grouping.Plan
import Aiur.Artifact

/-! Ixon encoding of companion population plans and physical circuits: the
trace section of an artifact. The grammar is documented with its Rust reader,
`aiur::artifact`; `Aiur.Artifact` frames the complete files. -/

namespace Aiur.Trace
open Optimized Aiur.Ixon Execution

/-- The trace plan semantics version. -/
def planVersion : Nat := 2

partial def putPolynomial (encode : F → Nat) : Polynomial F → PutM Unit
  | .const x => do u8 0; nat (encode x)
  | .var x => do u8 1; nat x
  | .add a b => do u8 2; putPolynomial encode a; putPolynomial encode b
  | .sub a b => do u8 3; putPolynomial encode a; putPolynomial encode b
  | .mul a b => do u8 4; putPolynomial encode a; putPolynomial encode b

private def putPolynomials (encode : F → Nat) (ps : List (Polynomial F)) : PutM Unit :=
  list ps (putPolynomial encode)

def putOperation (encode : F → Nat) (hintPCs : List Nat) : Operation F → PutM Unit
  | .assign dest values => do u8 0; nats dest; putPolynomials encode values
  | .inverse dest value => do u8 1; nat dest; putPolynomial encode value
  | .choose dest tests => do u8 2; nats dest; list tests (putPolynomials encode)
  | .failure dest differences => do u8 3; nats dest; putPolynomials encode differences
  | .call name args dest => do u8 4; str name; putPolynomials encode args; nats dest
  | .store type values dest => do u8 5; putTy type; putPolynomials encode values; nat dest
  | .load type address dest => do u8 6; putTy type; putPolynomial encode address; nats dest
  | .hint site type keyType key dest channel => do
      let some pc := hintPCs[site]? | throw "missing execution hint site"
      u8 7; str channel; nat pc; putTy type; putTy keyType
      putPolynomials encode key; nats dest

def putChip [Field F] [DecidableEq F] (encode : F → Nat) (source : Circuit.Chip F) :
    PutM Unit := do
  let chip := Activation.compile source
  unless chip.wellFormed do throw s!"invalid activated circuit {source.name}"
  unless chip.stats.maxConstraintDegree ≤ max 2 source.stats.maxConstraintDegree &&
      chip.maxLookupGuardDegree ≤ max 1 source.maxLookupGuardDegree do
    throw s!"activation increased the degree budget in {source.name}"
  let poly := putPolynomial encode
  str chip.name
  nat chip.numVars
  nat source.numVars
  nats (chip.inputs.flatMap WireValue.words)
  list chip.output.words poly
  list chip.constraints poly
  list chip.sends fun send => do
    str send.channel
    list (send.args.flatMap WireValue.words) poly
    nats send.result.words
    poly send.enable
  list chip.memory fun cell => do
    putTy cell.value.type
    poly cell.address
    list cell.value.words poly
    poly cell.enable

/-- Replay the actual layout functions to retain their otherwise discarded
definitions and compaction columns. Equality checks fail closed if either
compiler evolves without updating its companion metadata. -/
def putFunction [Field F] [DecidableEq F] (encode : F → Nat) (program : Program F)
    (config : Config) (fn : Function F) (layout : LaidOutChip F) (representative : String)
    (bytecode : Execution.Function F) (validateInputs : Bool := true) : PutM Unit := do
  let source ← MonadExcept.ofExcept (Compiler.function program config fn validateInputs)
  let aliases ← MonadExcept.ofExcept (resolveAliases source.chip)
  let propagatedScopes := if config.propagateScopes then ScopedPropagation.transform aliases else aliases
  let simplified := if config.simplifyConstraints then (ConstraintElimination.run propagatedScopes).chip
    else propagatedScopes
  let degree ← MonadExcept.ofExcept (Degree.boundState config simplified)
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
  let writes := columns.zipIdx.flatMap fun (old, column) =>
    (layout.layout.occupants[old]?.getD []).map fun id =>
      let guard := match degree.chip.roles[id]? with
        | some (.auxiliary scope) => source.chip.activation scope
        | _ => .const 1
      (column, id, guard)
  str fn.name
  str representative
  nat degree.chip.roles.size
  nats (source.chip.inputs.flatMap WireValue.words)
  nats source.chip.output.words
  array steps fun step => do
    putPolynomial encode (source.chip.activation step.scope)
    putOperation encode hintPCs step.operation
  list writes fun (column, id, guard) => do
    nat column; nat id; putPolynomial encode guard

def putGroup [Field F] [DecidableEq F] (encode : F → Nat) (group : Grouping.Layout F) :
    PutM Unit := do
  let poly := putPolynomial encode
  str group.name
  nat group.width
  poly group.activation
  list group.constraints poly
  list group.receive poly
  list group.sends fun s => do poly s.enable; list s.args poly
  list group.members fun m => do
    str m.name
    array m.columns nat
    nat m.selector
    list m.writes fun (column, value) => do nat column; poly value

/-- A function grouping artifact: checked groups alone, as `grouping_tune` writes
them for hosts that replace a package's grouping. -/
def exportGroups [Field F] [DecidableEq F] (encode : F → Nat) (groups : List (Grouping.Layout F)) :
    Except String ByteArray :=
  Ixon.run do
    raw Artifact.groupsMagic
    nat Artifact.formatVersion
    list groups (putGroup encode)

/-- The trace section of an artifact: population plans for every function,
the activated physical circuits, and the checked function groups. -/
def exportPreparedPlan [Field F] [DecidableEq F] (modulus : Nat) (encode : F → Nat)
    (program : Program F) (artifact : Optimized.Artifact F) (physical : Physical.Prepared artifact)
    (bytecode : Execution.Bytecode F) (groups : List (String × List String) := []) :
    Except String ByteArray := do
  unless program.functions.length == artifact.layouts.length && program.functions.length == bytecode.functions.length do
    throw "trace program/function count mismatch"
  let callableNames := bytecode.functions.map (·.name) ++ bytecode.maps.map (·.name)
  let id := fun name => if callableNames.contains name then pure (callableNames.idxOf name)
    else throw s!"unknown grouped callable {name}"
  let mut used : List String := []
  let mut packed : List (Grouping.Packed F id) := []
  for (name, names) in groups do
    let names := (names.map physical.representative).dedup
    let chips := physical.system.chips.filter fun c =>
      names.contains c.name && !used.contains c.name && !artifact.entries.contains c.name
    if chips.length < 2 then continue
    let group ← Grouping.compile name id chips
    used := used ++ chips.map (·.name)
    packed := packed ++ [⟨chips, group⟩]
  let plan ← Grouping.preparePlan physical.system id packed
  Ixon.run do
    nat planVersion
    nat modulus
    list ((program.functions.zip artifact.layouts).zip bytecode.functions) fun ((fn, layout), code) => do
      unless fn.name == code.name do throw "trace bytecode function order mismatch"
      putFunction encode program artifact.config fn layout (physical.representative fn.name) code
        (artifact.entries.contains fn.name)
    list physical.system.chips (putChip encode)
    list plan.groups fun p => putGroup encode p.checked.layout

def exportPlan [Field F] [DecidableEq F] (modulus : Nat) (encode : F → Nat)
    (program : Program F) (artifact : Optimized.Artifact F) (bytecode : Execution.Bytecode F)
    (groups : List (String × List String) := []) : Except String ByteArray := do
  exportPreparedPlan modulus encode program artifact (← Physical.prepare artifact) bytecode groups

end Aiur.Trace
