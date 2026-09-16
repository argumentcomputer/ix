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

structure FunctionPlan where
  index : FunIdx
  layout : FunctionLayout
  outputSize : Option Nat
  body : BlockPlan
  values : Array Value
  operations : Array Operation
  /-- Full-width seed words: multiplicity, inputs, then branch-shared reads. -/
  seedWords : Nat
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

/-- Hypothetical aligned size if every payload value passes a u8 guard.
This is a lower-bound scenario, not an inferred range or an emitted codec. -/
def FunctionPlan.guardedU8SeedBytes (plan : FunctionPlan) : Nat :=
  ((8 + (plan.seedWords - 1) + 7) / 8) * 8

structure ProgramPlan where
  /-- Indexed by function ID; unconstrained functions have no row writer. -/
  functions : Array (Option FunctionPlan)
  circuits : Array Circuit
  deriving Repr

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
  pure {
    index, layout := computed, outputSize := state.outputSize, body := result.plan,
    values := state.values, operations := state.operations, seedWords := result.scope.seed
    rowOperations, preparationOperations, aliasCheckOperations
    rowValues, preparationValues, aliasCheckValues }

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
  pure { functions, circuits := top.circuits }

end Aiur.TracePlan

end
