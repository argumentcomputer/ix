import Aiur.Trace.Compile
import Aiur.Optimized.Activation
import Aiur.Optimized.Physical
import Aiur.Optimized.Grouping.Plan
import Aiur.Optimized.EndToEnd
import Aiur.Optimized.Depth.Basic
import Aiur.Optimized.Depth.Classify
import Aiur.Optimized.Depth.Grouped
import Aiur.Optimized.Depth.Structural
import Aiur.Optimized.Depth.StructuralEndToEnd
import Aiur.Artifact

/-! Ixon encoding of companion population plans and physical circuits: the
trace section of an artifact. The grammar is documented with its Rust reader,
`aiur::artifact`; `Aiur.Artifact` frames the complete files. -/

namespace Aiur.Trace
open Optimized Aiur.Ixon Execution

/-- The trace plan semantics version. Version 3 adds the depth pass (Track A,
H1): the gap limb widths, and per circuit its depth column, SCC rank and call
slots. -/
def planVersion : Nat := 3

def putPolynomial (encode : F → Nat) : Polynomial F → PutM Unit
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
    (config : Config) (func : Function F) (layout : LaidOutChip F) (representative : String)
    (bytecode : Execution.Function F) (validateInputs : Bool := true) : PutM Unit := do
  let source ← MonadExcept.ofExcept (Compiler.function program config func validateInputs)
  let aliases ← MonadExcept.ofExcept (resolveAliases source.chip)
  let propagatedScopes := if config.propagateScopes then ScopedPropagation.transform aliases else aliases
  let simplified := if config.simplifyConstraints then (ConstraintElimination.run propagatedScopes).chip
    else propagatedScopes
  let degree ← MonadExcept.ofExcept (Degree.boundState config simplified)
  unless degree.chip == layout.logical do throw s!"trace logical layout mismatch in {func.name}"
  let merged := (LookupMerging.run config degree.chip layout.layout).chip
  let columns ← if config.propagateValues then do
    let propagated := Propagation.propagate merged merged.numVars (.identity merged)
    let used := propagated.chip.variables
    let columns := (List.range propagated.chip.numVars).filter (used.contains ·)
    unless Propagation.compact propagated.chip columns == layout.chip do
      throw s!"trace final compaction mismatch in {func.name}"
    pure columns
  else do
    unless merged == layout.chip do throw s!"trace final layout mismatch in {func.name}"
    pure (List.range merged.numVars)
  let hintPCs := bytecode.code.toList.zipIdx.filterMap fun (op, pc) =>
    match op with | .hint .. => some pc | _ => none
  unless source.hints == hintPCs.length do throw s!"trace hint occurrence mismatch in {func.name}"
  let steps := source.steps ++ (degree.cache.reverse.map fun (scope, value, dest) =>
    Step.mk scope (.assign [dest] [value])).toArray
  let writes := columns.zipIdx.flatMap fun (old, column) =>
    (layout.layout.occupants[old]?.getD []).map fun id =>
      let guard := match degree.chip.roles[id]? with
        | some (.auxiliary scope) => source.chip.activation scope
        | _ => .const 1
      (column, id, guard)
  str func.name
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

/-! ## Depth pass (Track A, H1) -/

/-- Gap limb widths, low limb first: `[16, 8]` (`k = 24`) whenever the field
holds all `2^16` rows of the `range16` table. A smaller test field gets one
limb that fits, so that no range table repeats a row; the acyclicity theorem
needs a large field anyway (`Depth.goldilocks_characteristic`). -/
def depthLimbs (modulus : Nat) : List Nat :=
  if 2 ^ 16 ≤ modulus then [16, 8] else [Nat.log2 modulus]

/-- The depth pass configuration of the physical circuits compiled from `program`, with the
measures of its exempt SCCs (`Depth.Structural`): recursive circuits whose calls descend on the
structure of an argument, or count a field argument down, carry no depth word. It is the
untrusted planners' output (`Depth.planPrepared`, then `Depth.Structural.plan`), refused unless
both halves of the depth certificate check (`Physical.Prepared.DepthCertified`). A plan without
a gap slot needs no limbs, so it adds no range maps or tables. -/
def depthConfig [Field F] [DecidableEq F] (modulus : Nat) (program : Program F)
    {artifact : Optimized.Artifact F} (physical : Physical.Prepared artifact) :
    Except String (Depth.Config × Depth.Structural.Plan) := do
  let base := Depth.planPrepared physical (depthLimbs modulus)
  let (cfg, measures) :=
    Depth.Structural.plan base physical.system program physical.representative
  let cfg := if cfg.plans.any (fun (_, plan) => plan.slots.contains .gap) then cfg
    else { cfg with limbs := [] }
  unless Depth.Structural.certify cfg physical.system do
    throw "the depth plan does not certify (Depth.Structural.certify)"
  unless Depth.Structural.check cfg program physical.representative measures do
    throw "the depth plan's measures do not check (Depth.Structural.check)"
  return (cfg, measures)

/-- The execution bytecode with the depth pass's range maps and their tables
(`Depth.rangeDecl`, `Depth.rangeTables`) appended, so that their callable IDs
follow every original callable. Execution never calls them; witness
population counts their uses. -/
def depthBytecode [NatCast F] (cfg : Depth.Config) (bytecode : Execution.Bytecode F) :
    Execution.Bytecode F :=
  let widths := cfg.limbs.dedup
  let base := bytecode.tables.length
  { bytecode with
    tables := bytecode.tables ++ widths.flatMap fun width =>
      [⟨Depth.rangeInputs width, .tuple [.field], (List.range (2 ^ width)).map fun n => [(n : F)]⟩,
       ⟨Depth.rangeUnits width, .tuple [], (List.range (2 ^ width)).map fun _ => []⟩]
    maps := bytecode.maps ++ widths.zipIdx.map fun (width, i) =>
      ⟨Depth.rangeName width, [.field], .tuple [], base + 2 * i, base + 2 * i + 1⟩ }

/-- Each call slot's kind and first new column, in send order, as
`Depth.compileChip` allocates them. -/
def slotColumns (limbs : List Nat) : Nat → List Depth.SlotKind → List (Depth.SlotKind × Nat)
  | _, [] => []
  | column, kind :: rest => (kind, column) :: slotColumns limbs (column + kind.width limbs) rest

/-- Population metadata of a depth chip, from its physical source chip: the
depth column of a recursive chip, its SCC rank, and one slot per original
send (the limb range checks follow those sends). -/
def putDepth (cfg : Depth.Config) (source : Circuit.Chip F) : PutM Unit := do
  let plan := cfg.plan source.name
  option (if plan.recursive then some source.numVars else none) nat
  nat (cfg.rank source.name)
  list (slotColumns cfg.limbs (plan.base source) plan.slots) fun (kind, column) =>
    match kind with
    | .plain => u8 0
    | .exact => u8 1
    | .gap => do u8 2; nat column
    | .external => do u8 3; nat column

/-- The trace section of an artifact: population plans for every function,
the activated depth circuits (`Depth.system` of the physical circuits), and
the checked function groups over them. It also returns `exported` with the
range maps (`depthBytecode`), which the package must carry. -/
def exportPreparedPlan [Field F] [DecidableEq F] (modulus : Nat) (encode : F → Nat)
    (program : Program F) (artifact : Optimized.Artifact F) (physical : Physical.Prepared artifact)
    (exported : Execution.Export F) (groups : List (String × List String) := []) :
    Except String (Execution.Export F × ByteArray) := do
  let original := exported.bytecode
  unless program.functions.length == artifact.layouts.length && program.functions.length == original.functions.length do
    throw "trace program/function count mismatch"
  let (cfg, measures) ← depthConfig modulus program physical
  let bytecode := depthBytecode cfg original
  let system := Depth.system cfg physical.system
  let callableNames := bytecode.functions.map (·.name) ++ bytecode.maps.map (·.name)
  let id := fun name => if callableNames.contains name then pure (callableNames.idxOf name)
    else throw s!"unknown grouped callable {name}"
  let mut used : List String := []
  let mut packed : List (Grouping.Packed F id) := []
  for (name, names) in groups do
    let names := (names.map physical.representative).dedup
    let chips := system.chips.filter fun c =>
      names.contains c.name && !used.contains c.name && !artifact.entries.contains c.name
    if chips.length < 2 then continue
    let group ← Grouping.compile name id chips
    used := used ++ chips.map (·.name)
    packed := packed ++ [⟨chips, group⟩]
  let plan ← Grouping.preparePlan system id packed
  -- Enforce all executable WS 2B-1 exporter safety certificates (`PlanCertificate`, both
  -- halves of the depth certificate, `cfg.bits ≤ 24`, and `Plan.WellFormedActivation`) before
  -- emitting bytes.
  unless Grouping.checkPlanCertificate system plan.singles plan.groups do
    throw "grouping partition failed executable certificate check (Grouping.checkPlanCertificate)"
  unless physical.checkDepthPlan program cfg measures plan do
    throw "depth-grouped plan failed executable safety certificate (Physical.Prepared.checkDepthPlan)"
  let trace ← Ixon.run do
    nat planVersion
    nat modulus
    nats cfg.limbs
    list ((program.functions.zip artifact.layouts).zip original.functions) fun ((func, layout), code) => do
      unless func.name == code.name do throw "trace bytecode function order mismatch"
      putFunction encode program artifact.config func layout (physical.representative func.name) code
        (artifact.entries.contains func.name)
    list (system.chips.zip physical.system.chips) fun (chip, source) => do
      putChip encode chip
      putDepth cfg source
    list plan.groups fun p => putGroup encode p.checked.layout
  return ({ exported with bytecode }, trace)

/-- `exportPreparedPlan` after physical deduplication of `artifact`. -/
def exportPlan [Field F] [DecidableEq F] (modulus : Nat) (encode : F → Nat)
    (program : Program F) (artifact : Optimized.Artifact F) (exported : Execution.Export F)
    (groups : List (String × List String) := []) :
    Except String (Execution.Export F × ByteArray) := do
  exportPreparedPlan modulus encode program artifact (← Physical.prepare artifact) exported groups

private def parMapExcept (xs : List α) (f : α → Except String β) : Except String (List β) :=
  let tasks := xs.map fun x => Task.spawn (prio := .default) fun _ => f x
  tasks.mapM (·.get)

/-- Parallel variant of `exportPreparedPlan` (`A8`). Evaluates independent group
compilations, per-function population plans (`putFunction`), per-chip activations
(`putChip`/`putDepth`), and per-group serializations (`putGroup`) concurrently via
`Task.spawn`, then concatenates their raw byte chunks in exact source order to
produce a byte-for-byte identical trace section without altering pure
`exportPreparedPlan` or `Optimized.compile`. -/
def exportPreparedPlanPar [Field F] [DecidableEq F] (modulus : Nat) (encode : F → Nat)
    (program : Program F) (artifact : Optimized.Artifact F) (physical : Physical.Prepared artifact)
    (exported : Execution.Export F) (groups : List (String × List String) := []) :
    Except String (Execution.Export F × ByteArray) := do
  let original := exported.bytecode
  unless program.functions.length == artifact.layouts.length && program.functions.length == original.functions.length do
    throw "trace program/function count mismatch"
  let (cfg, measures) ← depthConfig modulus program physical
  let bytecode := depthBytecode cfg original
  let system := Depth.system cfg physical.system
  let callableNames := bytecode.functions.map (·.name) ++ bytecode.maps.map (·.name)
  let id := fun name => if callableNames.contains name then pure (callableNames.idxOf name)
    else throw s!"unknown grouped callable {name}"
  let mut used : List String := []
  let mut groupSpecs : List (String × List (Circuit.Chip F)) := []
  for (name, names) in groups do
    let names := (names.map physical.representative).dedup
    let chips := system.chips.filter fun c =>
      names.contains c.name && !used.contains c.name && !artifact.entries.contains c.name
    if chips.length < 2 then continue
    used := used ++ chips.map (·.name)
    groupSpecs := groupSpecs ++ [(name, chips)]
  let packed : List (Grouping.Packed F id) ← parMapExcept groupSpecs fun (name, chips) => do
    let group ← Grouping.compile name id chips
    pure ⟨chips, group⟩
  let plan ← Grouping.preparePlan system id packed
  unless Grouping.checkPlanCertificate system plan.singles plan.groups do
    throw "grouping partition failed executable certificate check (Grouping.checkPlanCertificate)"
  unless physical.checkDepthPlan program cfg measures plan do
    throw "depth-grouped plan failed executable safety certificate (Physical.Prepared.checkDepthPlan)"
  let fnItems := (program.functions.zip artifact.layouts).zip original.functions
  let chipItems := system.chips.zip physical.system.chips
  let fnBytes ← parMapExcept fnItems fun ((func, layout), code) =>
    Ixon.run (capacity := 4096) do
      unless func.name == code.name do throw "trace bytecode function order mismatch"
      putFunction encode program artifact.config func layout (physical.representative func.name) code
        (artifact.entries.contains func.name)
  let chipBytes ← parMapExcept chipItems fun (chip, source) =>
    Ixon.run (capacity := 4096) do
      putChip encode chip
      putDepth cfg source
  let groupBytes ← parMapExcept plan.groups fun p =>
    Ixon.run (capacity := 4096) (putGroup encode p.checked.layout)
  let trace ← Ixon.run do
    nat planVersion
    nat modulus
    nats cfg.limbs
    list fnBytes raw
    list chipBytes raw
    list groupBytes raw
  return ({ exported with bytecode }, trace)

/-- `exportPreparedPlanPar` after physical deduplication of `artifact`. -/
def exportPlanPar [Field F] [DecidableEq F] (modulus : Nat) (encode : F → Nat)
    (program : Program F) (artifact : Optimized.Artifact F) (exported : Execution.Export F)
    (groups : List (String × List String) := []) :
    Except String (Execution.Export F × ByteArray) := do
  exportPreparedPlanPar modulus encode program artifact (← Physical.prepare artifact) exported groups

end Aiur.Trace
