import Aiur.Trace.Compile
import Aiur.Trace.Parallel
import Aiur.Optimized.Activation
import Aiur.Optimized.Physical
import Aiur.Optimized.Grouping.Plan
import Aiur.Optimized.EndToEnd
import Aiur.Optimized.Depth.Basic
import Aiur.Optimized.Depth.Classify
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

/-- The actual layout functions replayed from the source function alone, to
retain their otherwise discarded definitions and compaction columns. The
replay does not depend on the certified layout, so it can run while the
certified compiler runs; `putFunctionOf` then checks it against the layout. -/
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

/-- Check a replay against the certified layout and write its population
plan. Equality checks fail closed if either compiler evolves without updating
its companion metadata. -/
def putFunctionOf [Field F] [DecidableEq F] (encode : F → Nat) (config : Config)
    (fn : Function F) (replay : Replay F) (layout : LaidOutChip F) (representative : String)
    (bytecode : Execution.Function F) : PutM Unit := do
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

def putFunction [Field F] [DecidableEq F] (encode : F → Nat) (program : Program F)
    (config : Config) (fn : Function F) (layout : LaidOutChip F) (representative : String)
    (bytecode : Execution.Function F) (validateInputs : Bool := true) : PutM Unit := do
  putFunctionOf encode config fn
    (← MonadExcept.ofExcept (replayFunction program config fn validateInputs)) layout
    representative bytecode

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

/-- The depth pass configuration of a prepared physical system: the untrusted
planner's output (`Depth.planPrepared`), refused unless it certifies. A plan
without a gap slot needs no limbs, so it adds no range maps or tables. -/
def depthConfig [Field F] [DecidableEq F] (modulus : Nat) {artifact : Optimized.Artifact F}
    (physical : Physical.Prepared artifact) : Except String Depth.Config := do
  let cfg := Depth.planPrepared physical (depthLimbs modulus)
  let cfg := if cfg.plans.any (fun (_, plan) => plan.slots.contains .gap) then cfg
    else { cfg with limbs := [] }
  unless Depth.certify cfg physical.system do
    throw "the depth plan does not certify (Depth.Certified)"
  return cfg

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
    (exported : Execution.Export F) (groups : List (String × List String) := [])
    (replays : Option (List (Except String (Replay F))) := none) :
    Except String (Execution.Export F × ByteArray) := do
  let original := exported.bytecode
  unless program.functions.length == artifact.layouts.length && program.functions.length == original.functions.length do
    throw "trace program/function count mismatch"
  if let some replays := replays then
    unless replays.length == program.functions.length do throw "trace replay count mismatch"
  let cfg ← depthConfig modulus physical
  let bytecode := depthBytecode cfg original
  let system := Depth.system cfg physical.system
  let callableNames := bytecode.functions.map (·.name) ++ bytecode.maps.map (·.name)
  let id := fun name => if callableNames.contains name then pure (callableNames.idxOf name)
    else throw s!"unknown grouped callable {name}"
  let mut used : List String := []
  let mut selected : List (String × List (Circuit.Chip F)) := []
  for (name, names) in groups do
    let names := (names.map physical.representative).dedup
    let chips := system.chips.filter fun c =>
      names.contains c.name && !used.contains c.name && !artifact.entries.contains c.name
    if chips.length < 2 then continue
    used := used ++ chips.map (·.name)
    selected := selected ++ [(name, chips)]
  let packed ← selected.parMapM fun (name, chips) => do
    return (⟨chips, ← Grouping.compile name id chips⟩ : Grouping.Packed F id)
  let plan ← Grouping.preparePlan system id packed
  -- The backend theorems (`grouped_activated_heap_sound` and its siblings) assume
  -- `plan.WellFormedActivation`; refuse to export a plan that does not meet it.
  unless decide plan.WellFormedActivation do
    throw "an ungrouped chip is not well-formed before or after activation (Plan.WellFormedActivation)"
  let trace ← Ixon.run do
    nat planVersion
    nat modulus
    nats cfg.limbs
    list ((program.functions.zip artifact.layouts).zip original.functions).zipIdx
        fun (((fn, layout), code), index) => do
      unless fn.name == code.name do throw "trace bytecode function order mismatch"
      let replay ← match replays with
        | some replays => MonadExcept.ofExcept (replays[index]?.getD (throw "missing trace replay"))
        | none => MonadExcept.ofExcept (replayFunction program artifact.config fn
            (artifact.entries.contains fn.name))
      putFunctionOf encode artifact.config fn replay layout (physical.representative fn.name) code
    list (system.chips.zip physical.system.chips) fun (chip, source) => do
      putChip encode chip
      putDepth cfg source
    list plan.groups fun p => putGroup encode p.checked.layout
  return ({ exported with bytecode }, trace)

/-- `exportPreparedPlan` after physical deduplication of `artifact`. -/
def exportPlan [Field F] [DecidableEq F] (modulus : Nat) (encode : F → Nat)
    (program : Program F) (artifact : Optimized.Artifact F) (exported : Execution.Export F)
    (groups : List (String × List String) := []) : Except String (Execution.Export F × ByteArray) := do
  exportPreparedPlan modulus encode program artifact (← Physical.prepare artifact) exported groups

/-- `exportPlan` of the generic program `source` with entries `entries`, as
`Generic.Specialized.compileOptimized` compiles it, using every core: the
certified layouts come from `compileParallel` (proven equal to
`Optimized.compile`), and the population replays run alongside it, one task
per function. -/
def exportPlanParallel [Field F] [DecidableEq F] (modulus : Nat) (encode : F → Nat)
    (source : Generic.Source F) (entries : List String) (exported : Execution.Export F)
    (groups : List (String × List String) := []) (config : Config := {}) :
    IO (Execution.Export F × ByteArray) := do
  let specialized ← IO.ofExcept (Generic.specialize source entries)
  let inlined ← IO.ofExcept (Inlining.prepare specialized.program specialized.inlineNames entries)
  let program := inlined.program
  let replays ← program.functions.mapM fun fn => IO.asTask <| IO.lazyPure fun _ =>
    replayFunction program config fn (entries.contains fn.name)
  let artifact ← IO.ofExcept (compileParallel program entries config)
  let physical ← IO.ofExcept (Physical.prepare artifact)
  let replays ← replays.mapM fun replay => do IO.ofExcept (← IO.wait replay)
  IO.ofExcept (exportPreparedPlan modulus encode program artifact physical exported groups
    (some replays))

end Aiur.Trace
