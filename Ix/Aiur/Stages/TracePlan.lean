module

public import Ix.Aiur.Compiler.Layout

/-!
Main-trace planning over final Aiur bytecode. Column spans are relative to
their input, selector, auxiliary or lookup region, so a function plan can be
instantiated inside a grouped circuit. Value IDs are unique across branches;
bytecode's branch-local indices are resolved while building the plan.
-/

public section

namespace Aiur.TracePlan

open Bytecode

abbrev ValueId := Nat

structure Span where
  start : Nat
  size : Nat
  deriving Inhabited, Repr, BEq

structure BranchSpace where
  auxiliaries : Span
  lookups : Span
  seeds : Span
  deriving Inhabited, Repr

structure Value where
  degree : Nat
  producer : Option Nat := none
  input : Option Nat := none
  rowInputs : Array ValueId := #[]
  preparationInputs : Array ValueId := #[]
  deriving Inhabited, Repr

inductive ReadKind where
  | callResult (callee : FunIdx)
  | returnedCall (callee : FunIdx)
  | storePointer (width : Nat)
  | loadValues (width : Nat)
  | ioInfo
  | ioValues (length : Nat)
  | bigUintResults
  deriving Inhabited, Repr, BEq

structure ExternalRead where
  kind : ReadKind
  inputs : Array ValueId
  seed : Span
  deriving Inhabited, Repr

structure Operation where
  index : Nat
  opcode : Op
  inputs : Array ValueId
  outputs : Array ValueId
  outputDegrees : Array Nat
  auxiliaries : Span
  lookups : Span
  externalRead : Option ExternalRead
  deriving Repr

mutual
  inductive Control where
    | returnRow (selector : SelIdx) (values : Array ValueId)
    | yieldRow (selector : SelIdx) (values : Array ValueId)
    | branch (discriminant : ValueId) (arms : Array (G × BlockPlan))
        (fallback : Option BlockPlan) (defaultWitnesses : Span) (space : BranchSpace)
    | continueWith (discriminant : ValueId) (arms : Array (G × BlockPlan))
        (fallback : Option BlockPlan) (defaultWitnesses : Span) (space : BranchSpace)
        (mergeValues : Array ValueId) (mergeColumns : Span) (continuation : BlockPlan)
    deriving Inhabited, Repr

  structure BlockPlan where
    operations : Array Nat
    control : Control
    deriving Inhabited, Repr
end

/-- Storage for one seed word in the typed encoding. The multiplicity word is
always full width: negative field values are ordinary multiplicities. -/
inductive SeedWidth where
  | u8 | u16 | u32 | full
  deriving Inhabited, Repr, BEq, DecidableEq

def SeedWidth.bytes : SeedWidth → Nat
  | .u8 => 1 | .u16 => 2 | .u32 => 4 | .full => 8

/-- The narrowest width holding every canonical value below `bound`. -/
def SeedWidth.ofBound (bound : Nat) : SeedWidth :=
  if bound ≤ 256 then .u8 else if bound ≤ 65536 then .u16
  else if bound ≤ 4294967296 then .u32 else .full

/-- Byte layout of one typed seed. Words are stored widest first, in index
order within a width, so every word is naturally aligned and the multiplicity
stays at offset zero; the stride is padded to a multiple of eight. -/
structure SeedSchema where
  widths : Array SeedWidth
  offsets : Array Nat
  bytes : Nat
  deriving Inhabited, Repr, BEq

def SeedSchema.ofWidths (widths : Array SeedWidth) : SeedSchema := Id.run do
  let mut offsets := Array.replicate widths.size 0
  let mut cursor := 0
  for width in #[SeedWidth.full, .u32, .u16, .u8] do
    for i in [:widths.size] do
      if widths[i]! == width then
        offsets := offsets.set! i cursor
        cursor := cursor + width.bytes
  return { widths, offsets, bytes := ((cursor + 7) / 8) * 8 }

def SeedSchema.canonical (words : Nat) : SeedSchema :=
  SeedSchema.ofWidths (Array.replicate words .full)

/-- A schema whose typed and canonical encodings coincide. -/
def SeedSchema.isCanonical (schema : SeedSchema) : Bool :=
  schema.widths.all (· == .full)

structure FunctionPlan where
  index : FunIdx
  layout : FunctionLayout
  outputSize : Option Nat
  body : BlockPlan
  values : Array Value
  operations : Array Operation
  /-- Full-width seed words: multiplicity, inputs, then branch-shared reads. -/
  seedWords : Nat
  /-- Speculative per-word widths; the packer guards every narrowed word. -/
  seedSchema : SeedSchema
  rowOperations : Array Nat
  preparationOperations : Array Nat
  /-- Preparation dependencies including returned-call alias validation. -/
  aliasCheckOperations : Array Nat
  rowValues : Array ValueId
  preparationValues : Array ValueId
  aliasCheckValues : Array ValueId
  deriving Repr

def FunctionPlan.canonicalSeedBytes (plan : FunctionPlan) : Nat :=
  8 * plan.seedWords

def FunctionPlan.typedSeedBytes (plan : FunctionPlan) : Nat :=
  plan.seedSchema.bytes

structure ProgramPlan where
  /-- Indexed by function ID; unconstrained functions have no row writer. -/
  functions : Array (Option FunctionPlan)
  circuits : Array Circuit
  deriving Repr

/-- The functions of every circuit whose members together pack into at most
half their canonical seeds. A circuit is generated only when every member
is, so the selection is by circuit and the ratio is summed over its members;
it is the static signal that a seed is cheaper to move than the row it
replaces. Row weights, when they exist, should refine this. -/
def ProgramPlan.compactCircuitFunctions (plan : ProgramPlan) : Array FunIdx := Id.run do
  let mut selected := #[]
  for circuit in plan.circuits do
    let sizes := circuit.members.filterMap fun member =>
      plan.functions[member]?.join.map fun f => (f.typedSeedBytes, f.canonicalSeedBytes)
    let typed := sizes.foldl (fun n (t, _) => n + t) 0
    let canonical := sizes.foldl (fun n (_, c) => n + c) 0
    if sizes.size == circuit.members.size && 2 * typed ≤ canonical then
      selected := selected ++ circuit.members
  return selected

private structure Scope where
  locals : Array ValueId := #[]
  degrees : Array Nat := #[]
  auxiliary : Nat := 1
  lookup : Nat := 1
  seed : Nat := 1
  deriving Inhabited

private def Scope.maxSpace (base other : Scope) : Scope :=
  { base with
    auxiliary := max base.auxiliary other.auxiliary
    lookup := max base.lookup other.lookup
    seed := max base.seed other.seed }

private def Scope.spaceTo (start finish : Scope) : BranchSpace :=
  { auxiliaries := ⟨start.auxiliary, finish.auxiliary - start.auxiliary⟩
    lookups := ⟨start.lookup, finish.lookup - start.lookup⟩
    seeds := ⟨start.seed, finish.seed - start.seed⟩ }

private structure BuildState where
  values : Array Value := #[]
  operations : Array Operation := #[]
  selectors : Array SelIdx := #[]
  outputSize : Option Nat := none
  rowRoots : Array ValueId := #[]
  rowWrites : Array Nat := #[]
  preparationRoots : Array ValueId := #[]
  aliasRoots : Array ValueId := #[]

private abbrev PlanM := StateT BuildState (Except String)

private structure BlockResult where
  plan : BlockPlan
  scope : Scope
  /-- Yields escaping this block to its enclosing continuation. -/
  yields : Array (Array ValueId) := #[]
  deriving Inhabited

private def resolveLocal (scope : Scope) (index : ValIdx) : PlanM ValueId :=
  match scope.locals[index]? with
  | some value => pure value
  | none => throw s!"value {index} is outside the local stack of size {scope.locals.size}"

private def resolveLocals (scope : Scope) (indices : Array ValIdx) : PlanM (Array ValueId) :=
  indices.mapM (resolveLocal scope)

private def newValue (value : Value) : PlanM ValueId := do
  let index := (← get).values.size
  modify fun state => { state with values := state.values.push value }
  pure index

private def select (layout : FunctionLayout) (selector : SelIdx) : PlanM Unit := do
  if selector >= layout.selectors then
    throw s!"selector {selector} is outside the declared selector region"
  if (← get).selectors.contains selector then
    throw s!"selector {selector} is allocated by more than one terminal"
  modify fun state => { state with selectors := state.selectors.push selector }

private partial def returnsHaveSize (block : Bytecode.Block) (size : Nat) : Bool :=
  match block.ctrl with
  | .return _ values => values.size == size
  | .yield .. => true
  | .match _ arms fallback =>
    arms.all (fun (_, arm) => returnsHaveSize arm size) &&
      (fallback.map (fun arm => returnsHaveSize arm size)).getD true
  | .matchContinue _ arms fallback _ _ _ continuation =>
    arms.all (fun (_, arm) => returnsHaveSize arm size) &&
      (fallback.map (fun arm => returnsHaveSize arm size)).getD true &&
      returnsHaveSize continuation size

private def checkWord (values : Array ValIdx) : PlanM Unit := do
  unless values.size == 4 do
    throw s!"u32 operand has {values.size} bytes instead of 4"

private def checkMemory (top : Toplevel) (width : Nat) : PlanM Unit := do
  unless top.memorySizes.contains width do
    throw s!"memory width {width} has no table"

private def checkOp (top : Toplevel) (op : Op) : PlanM Unit := do
  match op with
  | .call index inputs outputs unconstrained =>
    let some callee := top.functions[index]?
      | throw s!"call target {index} does not exist"
    unless unconstrained || callee.constrained do
      throw s!"constrained call targets unconstrained function {index}"
    unless inputs.size == callee.layout.inputSize do
      throw s!"call {index}: input arity differs from its callee"
    unless returnsHaveSize callee.body outputs do
      throw s!"call {index}: output arity differs from its callee"
  | .store values => checkMemory top values.size
  | .load width _ => checkMemory top width
  | .assertEq xs ys _ =>
    unless xs.size == ys.size do
      throw "assertion operands have different arities"
  | .unconstrainedU32Add xs ys => checkWord xs; checkWord ys
  | .unconstrainedU32Add3 xs ys zs => checkWord xs; checkWord ys; checkWord zs
  | .u32ToField xs => checkWord xs
  | _ => pure ()

private def readKind (op : Op) (returned : Bool) : Option ReadKind :=
  match op with
  | .call callee _ size _ =>
    if size == 0 then none
    else some (if returned then .returnedCall callee else .callResult callee)
  | .store values => some (.storePointer values.size)
  | .load size _ => if size == 0 then none else some (.loadValues size)
  | .ioGetInfo .. => some .ioInfo
  | .ioRead _ _ size => if size == 0 then none else some (.ioValues size)
  | .unconstrainedBigUintDivMod .. => some .bigUintResults
  | _ => none

private def isReturnedCall (op : Op) (base : Nat) (control : Ctrl) : Bool :=
  match op, control with
  | .call _ _ size _, .return _ values =>
    size != 0 && values == Array.range' base size
  | _, _ => false

private def planOp (top : Toplevel) (scope : Scope) (op : Op) (control : Ctrl) :
    PlanM (Nat × Scope) := do
  let index := (← get).operations.size
  checkOp top op
  let inputs ← resolveLocals scope op.inputs
  let initial : Concrete.Bytecode.LayoutMState :=
    { functionLayout :=
        { inputSize := 0, selectors := 0,
          auxiliaries := scope.auxiliary, lookups := scope.lookup }
      memSizes := .empty, degrees := scope.degrees }
  let (_, allocated) := (Concrete.Bytecode.opLayout op).run initial
  unless allocated.degrees.size == scope.degrees.size + op.outputCount do
    throw s!"operation {index}: value count differs from layout degree count"
  let auxiliaries : Span :=
    ⟨scope.auxiliary, allocated.functionLayout.auxiliaries - scope.auxiliary⟩
  let lookups : Span :=
    ⟨scope.lookup, allocated.functionLayout.lookups - scope.lookup⟩
  let returned := isReturnedCall op scope.locals.size control
  let externalRead := (readKind op returned).map fun kind =>
    { kind, inputs := if returned then #[] else inputs,
      seed := ⟨scope.seed, op.outputCount⟩ : ExternalRead }
  let rowInputs := if externalRead.isSome then #[] else inputs
  let preparationInputs := if returned then #[] else inputs
  let outputDegrees := allocated.degrees.extract scope.degrees.size allocated.degrees.size
  let outputs ← outputDegrees.mapM fun degree =>
    newValue { degree, producer := some index, rowInputs, preparationInputs }
  let operation : Operation :=
    { index, opcode := op, inputs, outputs, outputDegrees,
      auxiliaries, lookups, externalRead }
  modify fun state => { state with operations := state.operations.push operation }
  if auxiliaries.size != 0 then
    modify fun state => { state with
      rowWrites := state.rowWrites.push index
      rowRoots := state.rowRoots ++ rowInputs }
  if let some read := externalRead then
    modify fun state => { state with preparationRoots := state.preparationRoots ++ read.inputs }
  if returned then
    modify fun state => { state with aliasRoots := state.aliasRoots ++ inputs }
  pure (index, { scope with
    locals := scope.locals ++ outputs
    degrees := allocated.degrees
    auxiliary := allocated.functionLayout.auxiliaries
    lookup := allocated.functionLayout.lookups
    seed := scope.seed + (externalRead.map (·.seed.size)).getD 0 })

private def markRowBranch (discriminant : ValueId) : PlanM Unit :=
  modify fun state => { state with
    rowRoots := state.rowRoots.push discriminant }

mutual
  private partial def planBlock (top : Toplevel) (layout : FunctionLayout)
      (scope : Scope) (yieldSize : Option Nat) (block : Bytecode.Block) :
      PlanM BlockResult := do
    let mut scope := scope
    let mut operations := #[]
    for op in block.ops do
      let (index, next) ← planOp top scope op block.ctrl
      operations := operations.push index
      scope := next
    let result ← planControl top layout scope yieldSize block.ctrl
    pure { result with plan := { result.plan with operations } }

  private partial def planArms (top : Toplevel) (layout : FunctionLayout)
      (scope : Scope) (yieldSize : Option Nat) (arms : Array (G × Bytecode.Block))
      (fallback : Option Bytecode.Block) :
      PlanM (Array (G × BlockPlan) × Option BlockPlan × Scope × Array (Array ValueId)) := do
    let mut cases : Array G := #[]
    let mut plans := #[]
    let mut maximum := scope
    let mut yields := #[]
    for (value, block) in arms do
      if cases.contains value then throw s!"duplicate match case {value.n}"
      cases := cases.push value
      let result ← planBlock top layout scope yieldSize block
      plans := plans.push (value, result.plan)
      maximum := maximum.maxSpace result.scope
      yields := yields ++ result.yields
    let mut fallbackPlan := none
    if let some block := fallback then
      let result ← planBlock top layout
        { scope with auxiliary := scope.auxiliary + arms.size } yieldSize block
      maximum := maximum.maxSpace result.scope
      yields := yields ++ result.yields
      fallbackPlan := some result.plan
    pure (plans, fallbackPlan, maximum, yields)

  private partial def planControl (top : Toplevel) (layout : FunctionLayout)
      (scope : Scope) (yieldSize : Option Nat) (control : Ctrl) : PlanM BlockResult := do
    match control with
    | .return selector indices =>
      let values ← resolveLocals scope indices
      select layout selector
      if let some size := (← get).outputSize then
        unless values.size == size do throw "function returns have different arities"
      modify fun state => { state with outputSize := some values.size }
      pure { plan := ⟨#[], .returnRow selector values⟩, scope }
    | .yield selector indices =>
      let values ← resolveLocals scope indices
      unless yieldSize == some values.size do
        throw "yield arity differs from its enclosing continuation"
      select layout selector
      modify fun state => { state with rowRoots := state.rowRoots ++ values }
      pure { plan := ⟨#[], .yieldRow selector values⟩, scope, yields := #[values] }
    | .match index arms fallback =>
      let discriminant ← resolveLocal scope index
      let defaultWitnesses : Span :=
        ⟨scope.auxiliary, if fallback.isSome then arms.size else 0⟩
      let (arms, fallback, maximum, yields) ← planArms top layout scope yieldSize arms fallback
      markRowBranch discriminant
      pure { plan := ⟨#[], .branch discriminant arms fallback defaultWitnesses
        (scope.spaceTo maximum)⟩, scope := maximum, yields }
    | .matchContinue index arms fallback size sharedAux sharedLookups continuation =>
      let discriminant ← resolveLocal scope index
      let defaultWitnesses : Span :=
        ⟨scope.auxiliary, if fallback.isSome then arms.size else 0⟩
      let (arms, fallback, maximum, yields) ← planArms top layout scope (some size) arms fallback
      let space := scope.spaceTo maximum
      unless space.auxiliaries.size == sharedAux && space.lookups.size == sharedLookups do
        throw s!"continuation reserves aux/lookups {sharedAux}/{sharedLookups}, \
          but its branches need {space.auxiliaries.size}/{space.lookups.size}"
      let mut merges := #[]
      for i in [:size] do
        let dependencies := yields.foldl (fun deps values => deps.push values[i]!) #[discriminant]
        let value ← newValue {
          degree := 1, rowInputs := dependencies, preparationInputs := dependencies }
        merges := merges.push value
      let next : Scope := { maximum with
        locals := scope.locals ++ merges
        degrees := scope.degrees ++ Array.replicate size 1
        auxiliary := maximum.auxiliary + size }
      let result ← planBlock top layout next yieldSize continuation
      markRowBranch discriminant
      pure { result with plan := ⟨#[], .continueWith discriminant arms fallback
        defaultWitnesses space merges ⟨maximum.auxiliary, size⟩ result.plan⟩ }

end

mutual
  private partial def preparationControls (operations : Array Operation)
      (block : BlockPlan) (afterYield : Bool) : Array ValueId × Bool :=
    let reads := block.operations.any fun index =>
      (operations[index]?.bind (·.externalRead)).isSome
    let (roots, needed) := preparationControl operations block.control afterYield
    (roots, reads || needed)

  private partial def preparationControl (operations : Array Operation)
      (control : Control) (afterYield : Bool) : Array ValueId × Bool :=
    match control with
    | .returnRow .. => (#[], false)
    | .yieldRow .. => (#[], afterYield)
    | .branch discriminant arms fallback _ _ =>
      preparationArms operations discriminant arms fallback afterYield
    | .continueWith discriminant arms fallback _ _ _ _ continuation =>
      let (continuationRoots, continuationNeeded) :=
        preparationControls operations continuation afterYield
      let (branchRoots, branchNeeded) :=
        preparationArms operations discriminant arms fallback continuationNeeded
      (branchRoots ++ continuationRoots, branchNeeded || continuationNeeded)

  private partial def preparationArms (operations : Array Operation) (discriminant : ValueId)
      (arms : Array (G × BlockPlan)) (fallback : Option BlockPlan)
      (afterYield : Bool) : Array ValueId × Bool := Id.run do
    let mut roots := #[]
    -- Nested returns can bypass a read in an enclosing continuation.
    -- Propagate that continuation demand through every intervening branch.
    let mut needed := afterYield
    for (_, block) in arms do
      let (branchRoots, branchNeeded) := preparationControls operations block afterYield
      roots := roots ++ branchRoots
      needed := needed || branchNeeded
    if let some block := fallback then
      let (branchRoots, branchNeeded) := preparationControls operations block afterYield
      roots := roots ++ branchRoots
      needed := needed || branchNeeded
    return (if needed then roots.push discriminant else roots, needed)
end

private def dependencies (values : Array Value) (operationCount : Nat)
    (roots : Array ValueId) (writes : Array Nat) (preparation : Bool) :
    Array Nat × Array ValueId := Id.run do
  let mut needed := Array.replicate values.size false
  let mut operations := Array.replicate operationCount false
  for root in roots do needed := needed.set! root true
  for write in writes do operations := operations.set! write true
  -- Dependencies precede their value, including continuation merges, whose
  -- alternatives have already been assigned distinct IDs.
  for offset in [:values.size] do
    let index := values.size - 1 - offset
    if needed[index]! then
      let value := values[index]!
      if let some producer := value.producer then
        operations := operations.set! producer true
      let inputs := if preparation then value.preparationInputs else value.rowInputs
      for input in inputs do needed := needed.set! input true
  return ((Array.range operationCount).filter fun index => operations[index]!,
    (Array.range values.size).filter fun index => needed[index]!)

/-! ## Seed value bounds

Exclusive upper bounds on canonical values, `gSize` when unknown. A word is
narrowed when any use anywhere in the function constrains it: byte-table
operations, u32 comparisons, equality assertions, exhaustive matches,
arguments passed to constrained callees whose own inputs are narrow, and
pointer positions. Values produced by byte operations, constants, bounded
arithmetic, calls and memory loads carry their bounds forward, through
continuation merges, function outputs and memory tables.

The union over paths is speculative on purpose: a value used as a byte on one
path is a byte on every path in the typed source language, and the packer
guards each narrowed word, so a wrong speculation costs a full-width span,
never a wrong row. Pointers are the other speculation: a memory pointer is
its record's base plus a table index and an I/O index counts buffer entries,
so both are taken to fit 32 bits. -/

private def unbounded : Nat := gSize.toNat

/-- Memory pointers and I/O indices. -/
private def pointerBound : Nat := 4294967296

/-- Bounds visible across the library: a function's inputs from their uses
inside it, its outputs from their producers at every return. -/
structure FunctionBounds where
  inputs : Array Nat
  outputs : Array Nat
  deriving Inhabited, Repr, BEq

/-- What one function's analysis may assume about the rest of the library:
callee bounds, and per memory width the bound of each stored value over
every store site. A table with no store site is unknown. -/
structure Library where
  callee : FunIdx → Option FunctionBounds
  memory : Nat → Option (Array Nat)

def Library.empty : Library := { callee := fun _ => none, memory := fun _ => none }

private def saturate (n : Nat) : Nat := min n unbounded

private def producedBounds (lib : Library) (op : Operation) (bound : ValueId → Nat) : Array Nat :=
  let a := (op.inputs[0]?.map bound).getD unbounded
  let b := (op.inputs[1]?.map bound).getD unbounded
  let unknown := Array.replicate op.outputs.size unbounded
  let bounds := match op.opcode with
    | .const g => #[g.n + 1]
    | .add .. => #[saturate (a + b - 1)]
    | .mul .. => #[saturate ((a - 1) * (b - 1) + 1)]
    | .eqZero .. | .u8LessThan .. | .u32LessThan .. => #[2]
    | .u8BitDecomposition .. => Array.replicate 8 2
    | .unconstrainedGToBytes .. => Array.replicate 8 256
    | .u8ShiftLeft .. | .u8ShiftRight .. | .u8Xor .. | .u8And .. | .u8Or .. => #[256]
    | .u8Add .. | .u8Sub .. => #[256, 2]
    | .u8Mul .. => #[256, 256]
    | .u8XorSplit4 .. => #[16, 256]
    | .u8XorSplit7 .. => #[2, 256]
    | .unconstrainedU32Add .. => #[256, 256, 256, 256, 2]
    | .unconstrainedU32Add3 .. => #[256, 256, 256, 256, 3]
    | .u32ToField .. => #[pointerBound]
    | .call index _ _ false => ((lib.callee index).map (·.outputs)).getD unknown
    | .store .. => #[pointerBound]
    | .load width _ => (lib.memory width).getD unknown
    | .ioGetInfo .. | .unconstrainedBigUintDivMod .. => #[pointerBound, pointerBound]
    | _ => unknown
  if bounds.size == op.outputs.size then bounds else unknown

private def requiredBounds (lib : Library) (op : Operation) (bound : ValueId → Nat) :
    Array (ValueId × Nat) :=
  match op.opcode with
  | .u8BitDecomposition .. | .u8ShiftLeft .. | .u8ShiftRight .. | .u8Xor .. | .u8Add ..
  | .u8Mul .. | .u8Sub .. | .u8And .. | .u8Or .. | .u8LessThan .. | .u8XorSplit7 ..
  | .u8XorSplit4 .. | .u8RangeCheck .. | .unconstrainedU32Add .. | .unconstrainedU32Add3 ..
  | .u32ToField .. => op.inputs.map (·, 256)
  | .u32LessThan .. => op.inputs.map (·, pointerBound)
  -- Operands are resolved value ids in `Op.inputs` order: the load pointer is
  -- the only operand, the I/O index follows the channel, and `ioSetInfo`
  -- ends with its index and length.
  | .load .. => (op.inputs[0]?.map (·, pointerBound)).toArray
  | .ioRead .. => (op.inputs[1]?.map (·, pointerBound)).toArray
  | .ioSetInfo .. =>
    (op.inputs.extract (op.inputs.size - 2) op.inputs.size).map (·, pointerBound)
  | .assertEq xs _ _ =>
    (Array.range xs.size).flatMap fun i =>
      match op.inputs[i]?, op.inputs[i + xs.size]? with
      | some x, some y => #[(x, bound y), (y, bound x)]
      | _, _ => #[]
  | .call index _ _ false =>
    match lib.callee index with
    | some bounds => op.inputs.zip bounds.inputs
    | none => #[]
  | _ => #[]

private structure Analysis where
  produced : Array Nat
  required : Array Nat
  /-- Pointwise maximum over returns; empty until the first return. -/
  outputs : Array Nat
  /-- Every store site: the memory width and its operands' bounds. -/
  stores : Array (Nat × Array Nat)

private def Analysis.bound (a : Analysis) (value : ValueId) : Nat :=
  min (a.produced[value]?.getD unbounded) (a.required[value]?.getD unbounded)

private def constrain (required : Array Nat) (value : ValueId) (bound : Nat) : Array Nat :=
  required.modify value (min · bound)

/-- Without a fallback arm, the discriminant is one of the case values. -/
private def guardDiscriminant (discriminant : ValueId) (arms : Array (G × BlockPlan))
    (fallback : Option BlockPlan) (required : Array Nat) : Array Nat :=
  if fallback.isSome then required
  else constrain required discriminant (arms.foldl (fun m (g, _) => max m g.n) 0 + 1)

mutual
  /-- Yields escaping a block to its enclosing continuation, in plan order. -/
  private partial def blockYields (block : BlockPlan) : Array (Array ValueId) :=
    match block.control with
    | .returnRow .. => #[]
    | .yieldRow _ values => #[values]
    | .branch _ arms fallback _ _ => armYields arms fallback
    | .continueWith _ _ _ _ _ _ _ continuation => blockYields continuation

  private partial def armYields (arms : Array (G × BlockPlan)) (fallback : Option BlockPlan) :
      Array (Array ValueId) :=
    arms.foldl (fun yields (_, block) => yields ++ blockYields block) #[] ++
      (fallback.map blockYields).getD #[]
end

mutual
  private partial def produceBlock (plan : FunctionPlan) (lib : Library)
      (block : BlockPlan) (a : Analysis) : Analysis :=
    let a := block.operations.foldl (init := a) fun a index =>
      match plan.operations[index]? with
      | some op =>
        let bound := fun v => a.produced[v]?.getD unbounded
        let bounds := producedBounds lib op bound
        let stores := match op.opcode with
          | .store .. => a.stores.push (op.inputs.size, op.inputs.map bound)
          | _ => a.stores
        let produced := (op.outputs.zip bounds).foldl (fun p (v, b) => p.set! v b) a.produced
        { a with stores := stores, produced := produced }
      | none => a
    produceControl plan lib block.control a

  private partial def produceArms (plan : FunctionPlan) (lib : Library)
      (arms : Array (G × BlockPlan)) (fallback : Option BlockPlan) (a : Analysis) : Analysis :=
    let a := arms.foldl (fun a (_, block) => produceBlock plan lib block a) a
    match fallback with
    | some block => produceBlock plan lib block a
    | none => a

  private partial def produceControl (plan : FunctionPlan) (lib : Library)
      (control : Control) (a : Analysis) : Analysis :=
    match control with
    | .returnRow _ values =>
      let bounds := values.map fun v => a.produced[v]?.getD unbounded
      { a with outputs := if a.outputs.isEmpty then bounds
          else (a.outputs.zip bounds).map fun (x, y) => max x y }
    | .yieldRow .. => a
    | .branch _ arms fallback _ _ => produceArms plan lib arms fallback a
    | .continueWith _ arms fallback _ _ merges _ continuation =>
      let a := produceArms plan lib arms fallback a
      let yields := armYields arms fallback
      let produced := merges.zipIdx.foldl (init := a.produced) fun p (merge, i) =>
        p.set! merge (yields.foldl (init := 1) fun b values =>
          max b ((values[i]?.map fun v => a.produced[v]?.getD unbounded).getD unbounded))
      produceBlock plan lib continuation { a with produced }
end

mutual
  private partial def requireBlock (plan : FunctionPlan) (lib : Library)
      (block : BlockPlan) (produced : Array Nat) (required : Array Nat) : Array Nat :=
    let required := block.operations.foldl (init := required) fun r index =>
      match plan.operations[index]? with
      | some op =>
        (requiredBounds lib op fun v => produced[v]?.getD unbounded).foldl
          (fun r (v, b) => constrain r v b) r
      | none => r
    requireControl plan lib block.control produced required

  private partial def requireArms (plan : FunctionPlan) (lib : Library)
      (arms : Array (G × BlockPlan)) (fallback : Option BlockPlan) (produced : Array Nat)
      (required : Array Nat) : Array Nat :=
    let required := arms.foldl (fun r (_, block) => requireBlock plan lib block produced r) required
    match fallback with
    | some block => requireBlock plan lib block produced required
    | none => required

  private partial def requireControl (plan : FunctionPlan) (lib : Library)
      (control : Control) (produced : Array Nat) (required : Array Nat) : Array Nat :=
    match control with
    | .returnRow .. | .yieldRow .. => required
    | .branch discriminant arms fallback _ _ =>
      requireArms plan lib arms fallback produced
        (guardDiscriminant discriminant arms fallback required)
    | .continueWith discriminant arms fallback _ _ merges _ continuation =>
      -- The continuation's uses of a merge bound every yield feeding it, so
      -- the continuation is analyzed before the arms that yield into it.
      let required := requireBlock plan lib continuation produced
        (guardDiscriminant discriminant arms fallback required)
      let required := (armYields arms fallback).foldl (init := required) fun r values =>
        (merges.zip values).foldl (fun r (merge, v) => constrain r v (r[merge]?.getD unbounded)) r
      requireArms plan lib arms fallback produced required
end

private def produce (plan : FunctionPlan) (lib : Library) : Analysis :=
  let unknown := Array.replicate plan.values.size unbounded
  let a := produceBlock plan lib plan.body
    { produced := unknown, required := unknown, outputs := #[], stores := #[] }
  if a.outputs.isEmpty then { a with outputs := Array.replicate (plan.outputSize.getD 0) unbounded } else a

private def analyze (plan : FunctionPlan) (lib : Library) : Analysis × FunctionBounds :=
  let a := produce plan lib
  let a := { a with required := requireBlock plan lib plan.body a.produced a.required }
  -- Input values are allocated first, so input `i` is value `i`.
  (a, { inputs := (Array.range plan.layout.inputSize).map a.bound, outputs := a.outputs })

/-- Bounds shared across functions are rounded to width classes so that both
library fixpoints range over a finite lattice. -/
private def roundBound (bound : Nat) : Nat :=
  if bound ≤ 256 then 256 else if bound ≤ 65536 then 65536
  else if bound ≤ 4294967296 then 4294967296 else unbounded

/-- One width per seed word: the multiplicity stays full, inputs and read
results take their value bounds, and a slot shared by mutually exclusive
reads takes the widest. Unused slots are always zero and pack as one byte. -/
private def seedSchema (plan : FunctionPlan) (a : Analysis) : SeedSchema := Id.run do
  let mut bounds := Array.replicate plan.seedWords 1
  bounds := bounds.set! 0 unbounded
  for i in [:plan.layout.inputSize] do
    bounds := bounds.modify (1 + i) (max · (a.bound i))
  for op in plan.operations do
    if let some read := op.externalRead then
      for j in [:op.outputs.size] do
        bounds := bounds.modify (read.seed.start + j) (max · (a.bound op.outputs[j]!))
  return SeedSchema.ofWidths (bounds.map SeedWidth.ofBound)

/-- Joins every store site's operand bounds per memory width, rounded. -/
private def memoryBounds (stores : Array (Nat × Array Nat)) : Array (Nat × Array Nat) :=
  stores.foldl (init := #[]) fun table (width, bounds) =>
    let bounds := bounds.map roundBound
    match table.findIdx? (·.1 == width) with
    | some i => table.modify i fun (width, joined) =>
        (width, (joined.zip bounds).map fun (x, y) => max x y)
    | none => table.push (width, bounds)

/-- Recomputes every schema with bounds shared across the library.

Output and memory bounds are the least fixpoint, iterated upward from the
smallest class: a recursive function whose returns are its own call results
or byte results then narrows to bytes, and a table only ever stored with
bytes loads bytes, which a downward iteration from unknown never would.
Every finite execution is covered by induction on its call depth, so the
limit is a valid bound; a phase that does not settle falls back to unknown.
Input bounds are then iterated downward from unknown, where every iterate is
already valid and stopping early is safe. -/
def resolveSchemas (functions : Array (Option FunctionPlan)) : Array (Option FunctionPlan) := Id.run do
  let plans := functions.filterMap id
  let mut outputs : Array (Option (Array Nat)) := functions.map fun plan => plan.map fun plan =>
    Array.replicate (plan.outputSize.getD 0) 256
  -- Only tables with a store site have bounds; the rest stay unknown.
  let mut memory : Array (Nat × Array Nat) := memoryBounds <|
    (plans.foldl (fun stores plan => stores ++ (produce plan Library.empty).stores) #[]).map
      fun (width, bounds) => (width, bounds.map fun _ => 256)
  let mut settled := false
  for _ in [:64] do
    let lib : Library := {
      callee := fun index => (outputs[index]?.join).map fun outputs => { inputs := #[], outputs }
      memory := fun width => (memory.find? (·.1 == width)).map (·.2) }
    let analyses := functions.map fun plan => plan.map fun plan => produce plan lib
    let nextOutputs := analyses.map fun a => a.map fun a => a.outputs.map roundBound
    let nextMemory := memoryBounds <|
      analyses.foldl (fun stores a => stores ++ (a.map (·.stores)).getD #[]) #[]
    if nextOutputs == outputs && nextMemory == memory then
      settled := true
      break
    outputs := nextOutputs
    memory := nextMemory
  unless settled do
    outputs := functions.map fun plan => plan.map fun plan =>
      Array.replicate (plan.outputSize.getD 0) unbounded
    memory := #[]
  let mut inputs : Array (Option (Array Nat)) := functions.map fun plan => plan.map fun plan =>
    Array.replicate plan.layout.inputSize unbounded
  let lib := fun (inputs : Array (Option (Array Nat))) => ({
    callee := fun index =>
      match inputs[index]?.join, outputs[index]?.join with
      | some inputs, some outputs => some { inputs, outputs }
      | _, _ => none
    memory := fun width => (memory.find? (·.1 == width)).map (·.2) } : Library)
  for _ in [:64] do
    let next := functions.map fun plan => plan.map fun plan =>
      (analyze plan (lib inputs)).2.inputs.map roundBound
    if next == inputs then break
    inputs := next
  return functions.map fun plan => plan.map fun plan =>
    { plan with seedSchema := seedSchema plan (analyze plan (lib inputs)).1 }

def function (top : Toplevel) (index : FunIdx) : Except String FunctionPlan := do
  let some definition := top.functions[index]? | throw s!"function {index} does not exist"
  unless definition.constrained do throw s!"function {index} has no constrained trace"
  let build : PlanM BlockResult := do
    let mut inputs := #[]
    for i in [:definition.layout.inputSize] do
      let value ← newValue { degree := 1, input := some i }
      inputs := inputs.push value
    let scope : Scope := {
      locals := inputs, degrees := Array.replicate inputs.size 1, seed := 1 + inputs.size }
    planBlock top definition.layout scope none definition.body
  let (result, state) ← (build.run {}).mapError fun error => s!"function {index}: {error}"
  let computed : FunctionLayout :=
    { inputSize := definition.layout.inputSize, selectors := state.selectors.size,
      auxiliaries := result.scope.auxiliary, lookups := result.scope.lookup }
  unless computed == definition.layout do
    throw s!"function {index}: planned layout {repr computed} differs from {repr definition.layout}"
  let (_, oracle) := (Concrete.Bytecode.blockLayout definition.body).run
    (Concrete.Bytecode.LayoutMState.new definition.layout.inputSize)
  let oracleLayout := { oracle.functionLayout with lookups := oracle.functionLayout.lookups + 1 }
  unless computed == oracleLayout do
    throw s!"function {index}: trace plan differs from the layout allocator"
  let reads := state.operations.filterMap fun op => op.externalRead.map fun _ => op.index
  let (controlRoots, _) := preparationControls state.operations result.plan false
  let preparationRoots := state.preparationRoots ++ controlRoots
  let (rowOperations, rowValues) := dependencies state.values state.operations.size
    state.rowRoots state.rowWrites false
  let (preparationOperations, preparationValues) := dependencies state.values state.operations.size
    preparationRoots reads true
  let (aliasCheckOperations, aliasCheckValues) := dependencies state.values state.operations.size
    (preparationRoots ++ state.aliasRoots) reads true
  let plan : FunctionPlan := {
    index, layout := computed, outputSize := state.outputSize, body := result.plan,
    values := state.values, operations := state.operations, seedWords := result.scope.seed
    seedSchema := SeedSchema.canonical result.scope.seed
    rowOperations, preparationOperations, aliasCheckOperations
    rowValues, preparationValues, aliasCheckValues }
  -- Without the library, callees and memory contribute no bounds; `program`
  -- refines this.
  pure { plan with seedSchema := seedSchema plan (analyze plan Library.empty).1 }

private def validateCircuits (top : Toplevel) : Except String Unit := do
  let mut seen := Array.replicate top.functions.size false
  for circuit in top.circuits do
    if circuit.members.isEmpty then throw s!"circuit {circuit.name} has no members"
    let mut merged : FunctionLayout :=
      { inputSize := 0, selectors := 0, auxiliaries := 0, lookups := 0 }
    for member in circuit.members do
      let some definition := top.functions[member]?
        | throw s!"circuit {circuit.name}: missing member {member}"
      unless definition.constrained do
        throw s!"circuit {circuit.name}: member {member} is unconstrained"
      if seen[member]! then throw s!"function {member} occurs in more than one circuit"
      seen := seen.set! member true
      merged := merged.merge definition.layout
    unless merged == circuit.layout do
      throw s!"circuit {circuit.name}: merged member layout differs from its declared layout"
  for i in [:top.functions.size] do
    unless seen[i]! == top.functions[i]!.constrained do
      throw s!"constrained function {i} has no circuit"

def program (top : Toplevel) : Except String ProgramPlan := do
  if top.functions.size >= gSize.toNat then throw "function count exceeds the field characteristic"
  for size in top.memorySizes do
    if size >= gSize.toNat then throw "memory width exceeds the field characteristic"
  validateCircuits top
  let mut functions := #[]
  for i in [:top.functions.size] do
    if top.functions[i]!.constrained then
      functions := functions.push (some (← function top i))
    else
      functions := functions.push none
  pure { functions := resolveSchemas functions, circuits := top.circuits }

end Aiur.TracePlan

end
