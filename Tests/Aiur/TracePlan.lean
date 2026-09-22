module

public import LSpec
public import Ix.Aiur.Stages.TraceReport

public section

open LSpec Aiur Aiur.Bytecode Aiur.TracePlan

namespace AiurTests.TracePlan

private def definition (inputs : Nat) (body : Bytecode.Block) : Bytecode.Function :=
  let (_, state) := (Concrete.Bytecode.blockLayout body).run
    (Concrete.Bytecode.LayoutMState.new inputs)
  { body, entry := false, constrained := true,
    layout := { state.functionLayout with lookups := state.functionLayout.lookups + 1 } }

private def singletonProgram (functions : Array Bytecode.Function)
    (memorySizes : Array Nat := #[]) : Bytecode.Toplevel :=
  { functions, memorySizes, circuits := functions.mapIdx fun index f =>
      { name := s!"function_{index}", members := #[index], layout := f.layout } }

private def accepts (name : String) (top : Bytecode.Toplevel)
    (check : FunctionPlan → Bool) : TestSeq :=
  match Aiur.TracePlan.function top 0 with
  | .ok plan => test name (check plan)
  | .error error => test s!"{name}: {error}" false

private def rejects (name : String) (top : Bytecode.Toplevel) : TestSeq :=
  test name ((match Aiur.TracePlan.program top with
    | .error _ => true
    | .ok _ => false) : Bool)

private def arithmetic : Bytecode.Function := definition 2 {
  ops := #[.mul 0 1, .const 7, .mul 2 3, .eqZero 4, .const 0, .eqZero 6,
    .u8Add 0 1, .unconstrainedU32Add #[0, 1, 0, 1] #[1, 0, 1, 0],
    .u32ToField #[10, 11, 12, 13]],
  ctrl := .return 0 #[15] }

private def identityFunction : Bytecode.Function := definition 1 {
  ops := #[], ctrl := .return 0 #[0] }

private def returnedCall : Bytecode.Function := definition 1 {
  ops := #[.mul 0 0, .add 1 0, .call 1 #[2] 1 false],
  ctrl := .return 0 #[3] }

private def callThenLoad : Bytecode.Function := definition 1 {
  ops := #[.mul 0 0, .call 1 #[1] 1 false, .load 2 2],
  ctrl := .return 0 #[4] }

private def branchBody (sharedAux : Nat := 4) (sharedLookups : Nat := 1)
    (continuationInput : Nat := 2) : Bytecode.Block := {
  ops := #[], ctrl := .matchContinue 0
    #[(0, { ops := #[.mul 1 1], ctrl := .yield 0 #[2] }),
      (1, { ops := #[.u8Add 1 1], ctrl := .yield 1 #[2] })]
    (some { ops := #[.eqZero 1], ctrl := .yield 2 #[2] })
    1 sharedAux sharedLookups
    { ops := #[.mul continuationInput 1], ctrl := .return 3 #[3] } }

private def nested : Bytecode.Function := definition 1 {
  ops := #[], ctrl := .matchContinue 0
    #[(0, {
      ops := #[], ctrl := .matchContinue 0
        #[(0, { ops := #[], ctrl := .yield 0 #[0] })] none 1 0 0
        { ops := #[], ctrl := .yield 1 #[1] } })]
    (some { ops := #[.const 2], ctrl := .yield 2 #[1] })
    1 1 0 { ops := #[], ctrl := .return 3 #[1] } }

private def earlyReturn : Bytecode.Function := definition 1 {
  ops := #[.mul 0 0], ctrl := .matchContinue 1
    #[(0, { ops := #[], ctrl := .return 0 #[0] })]
    (some { ops := #[], ctrl := .yield 1 #[] })
    0 1 0 { ops := #[.load 1 0], ctrl := .return 2 #[2] } }

private def branchReads : Bytecode.Function := definition 1 {
  ops := #[], ctrl := .matchContinue 0
    #[(0, { ops := #[.ioRead 0 0 1], ctrl := .yield 0 #[1] })]
    (some { ops := #[.ioRead 0 0 2], ctrl := .yield 1 #[2] })
    1 3 0 { ops := #[.ioRead 0 1 1], ctrl := .return 2 #[2] } }

private def nestedEarlyReturn : Bytecode.Function := definition 1 {
  ops := #[], ctrl := .matchContinue 0
    #[(0, {
      ops := #[.mul 0 0], ctrl := .match 1
        #[(0, { ops := #[], ctrl := .return 0 #[0] })]
        (some { ops := #[], ctrl := .yield 1 #[] }) })]
    (some { ops := #[], ctrl := .yield 2 #[] })
    0 2 0 { ops := #[.load 1 0], ctrl := .return 3 #[1] } }

private def externalReads : Bytecode.Function := definition 1 {
  ops := #[.store #[0], .load 1 1, .ioGetInfo 0 #[2], .ioRead 0 3 2,
    .unconstrainedBigUintDivMod 1 2, .ioSetInfo 0 #[2] 3 4, .ioWrite 0 #[5, 6]],
  ctrl := .return 0 #[7, 8] }

private def grouped : Bytecode.Toplevel := {
  functions := #[arithmetic, nested], memorySizes := #[],
  circuits := #[{
    name := "group", members := #[0, 1],
    layout := arithmetic.layout.merge nested.layout }] }

private def hasBackwardDependencies (plan : FunctionPlan) : Bool :=
  (plan.values.mapIdx fun index value =>
    value.rowInputs.all (· < index) && value.preparationInputs.all (· < index)).all id

def allocationTests : TestSeq :=
  accepts "degree-sensitive allocations and virtual carries"
    (singletonProgram #[arithmetic]) (fun plan =>
      plan.layout.auxiliaries == 9 && plan.layout.lookups == 2 &&
      plan.operations.map (·.auxiliaries) ==
        #[⟨1, 1⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨2, 2⟩, ⟨4, 0⟩, ⟨4, 0⟩,
          ⟨4, 1⟩, ⟨5, 4⟩, ⟨9, 0⟩] &&
      plan.operations.map (·.outputs.size) == #[1, 1, 1, 1, 1, 1, 2, 5, 1]) ++
  accepts "unused auxiliary writes survive but virtual return expressions need no row work"
    (singletonProgram #[arithmetic]) (fun plan =>
      plan.rowOperations == #[0, 1, 2, 3, 6, 7] &&
      plan.preparationOperations.isEmpty && plan.seedWords == 3) ++
  accepts "short branches reserve the maximum including default inverses"
    (singletonProgram #[definition 2 (branchBody 4)]) (fun plan =>
      plan.layout.auxiliaries == 7 && plan.layout.lookups == 2 &&
      plan.layout.selectors == 4 &&
      plan.operations.map (·.auxiliaries) == #[⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨6, 1⟩] &&
      match plan.body.control with
      | .continueWith _ _ _ inverses space merges columns _ =>
        inverses == ⟨1, 2⟩ && space.auxiliaries == ⟨1, 4⟩ &&
        space.lookups == ⟨1, 1⟩ && columns == ⟨5, 1⟩ && merges == #[6]
      | _ => false) ++
  accepts "nested continuations consume their own yields and preserve the outer scope"
    (singletonProgram #[nested]) (fun plan =>
      plan.layout.auxiliaries == 3 && plan.layout.selectors == 4 &&
      hasBackwardDependencies plan &&
      match plan.body.control with
      | .continueWith _ _ _ _ _ merges columns _ => merges == #[3] && columns == ⟨2, 1⟩
      | _ => false) ++
  rejects "incorrect shared auxiliary reservation is rejected"
    (singletonProgram #[definition 2 (branchBody 3)]) ++
  rejects "incorrect shared lookup reservation is rejected"
    (singletonProgram #[definition 2 (branchBody 4 0)]) ++
  rejects "continuation cannot refer to a discarded branch local"
    (singletonProgram #[definition 2 (branchBody 4 1 3)])

def preparationTests : TestSeq :=
  accepts "returned-call alias skips key arithmetic but retains strict-check dependencies"
    (singletonProgram #[returnedCall, identityFunction]) (fun plan =>
      plan.seedWords == 3 && plan.preparationOperations == #[2] &&
      plan.aliasCheckOperations == #[0, 1, 2] && plan.rowOperations == #[0, 2] &&
      plan.operations.filterMap (fun op => op.externalRead.map (·.kind)) ==
        #[.returnedCall 1]) ++
  accepts "call-result-to-load chain retains CPU key arithmetic"
    (singletonProgram #[callThenLoad, identityFunction] #[2]) (fun plan =>
      plan.seedWords == 5 && plan.preparationOperations == #[0, 1, 2] &&
      plan.operations.filterMap (fun op => op.externalRead.map (·.kind)) ==
        #[.callResult 1, .loadValues 2] &&
      plan.operations.filterMap (fun op => op.externalRead.map (·.seed)) ==
        #[⟨2, 1⟩, ⟨3, 2⟩]) ++
  accepts "early return retains the branch decision guarding a continuation read"
    (singletonProgram #[earlyReturn] #[1]) (fun plan =>
      plan.preparationOperations == #[0, 1] && plan.seedWords == 3) ++
  accepts "nested return retains its decision guarding an enclosing continuation read"
    (singletonProgram #[nestedEarlyReturn] #[1]) (fun plan =>
      plan.preparationOperations == #[0, 1] && plan.seedWords == 3) ++
  accepts "branch seed slots overlap and continuation starts after the larger arm"
    (singletonProgram #[branchReads]) (fun plan =>
      plan.seedWords == 5 && hasBackwardDependencies plan &&
      plan.operations.filterMap (fun op => op.externalRead.map (·.seed)) ==
        #[⟨2, 1⟩, ⟨2, 2⟩, ⟨4, 1⟩]) ++
  accepts "store, load, IO and BigUint are reads; execution-only effects have no seed"
    (singletonProgram #[externalReads] #[1]) (fun plan =>
      plan.seedWords == 10 && plan.preparationOperations == #[0, 1, 2, 3, 4] &&
      plan.operations.filterMap (fun op => op.externalRead.map (·.kind)) ==
        #[.storePointer 1, .loadValues 1, .ioInfo, .ioValues 2, .bigUintResults]) ++
  accepts "zero-output calls allocate a lookup without a seed or a key recomputation"
    (singletonProgram #[
      definition 1 { ops := #[.mul 0 0, .call 1 #[1] 0 false], ctrl := .return 0 #[] },
      definition 1 { ops := #[], ctrl := .return 0 #[] }]) (fun plan =>
      plan.layout.lookups == 2 && plan.seedWords == 2 &&
      plan.preparationOperations.isEmpty && plan.rowOperations == #[0]) ++
  accepts "unconstrained call results need advice but no call lookup"
    (singletonProgram #[
      definition 1 { ops := #[.call 1 #[0] 1 true], ctrl := .return 0 #[1] },
      identityFunction]) (fun plan =>
      plan.layout.lookups == 1 && plan.layout.auxiliaries == 2 && plan.seedWords == 3) ++
  accepts "129 inputs and 32 aliased outputs have the BLAKE3 seed-word count"
    (singletonProgram #[definition 129 {
      ops := #[.call 0 (Array.range 129) 32 false],
      ctrl := .return 0 (Array.range' 129 32) }]) (fun plan =>
      plan.seedWords == 162 && plan.canonicalSeedBytes == 1296)

private def programPlan (top : Bytecode.Toplevel) (index : Nat) : Option FunctionPlan :=
  match Aiur.TracePlan.program top with
  | .ok plan => plan.functions[index]?.join
  | .error _ => none

private def widths (plan : FunctionPlan) : Array SeedWidth := plan.seedSchema.widths

private def exhaustiveThenFallback : Bytecode.Function := definition 2 {
  ops := #[], ctrl := .match 0
    #[(0, { ops := #[], ctrl := .return 0 #[] }),
      (300, {
        ops := #[], ctrl := .match 1
          #[(1, { ops := #[], ctrl := .return 1 #[] })]
          (some { ops := #[], ctrl := .return 2 #[] }) })] none }

private def yieldsIntoByteUse : Bytecode.Function := definition 2 {
  ops := #[], ctrl := .matchContinue 0
    #[(0, { ops := #[], ctrl := .yield 0 #[1] })]
    (some { ops := #[.const 5], ctrl := .yield 1 #[2] })
    1 1 0 { ops := #[.u8Xor 2 2], ctrl := .return 2 #[3] } }

private def recursiveBytes : Bytecode.Function := definition 2 {
  ops := #[], ctrl := .match 0
    #[(7, { ops := #[.u8Xor 1 1], ctrl := .return 0 #[2] })]
    (some { ops := #[.const 1, .add 0 2, .call 0 #[3, 1] 1 false], ctrl := .return 1 #[4] }) }

private def boundedArithmetic : Bytecode.Function := definition 1 {
  ops := #[.u8Xor 0 0, .const 200, .add 1 2, .mul 3 3, .mul 4 4],
  ctrl := .return 0 #[3, 4, 5] }

private def callsBoundedArithmetic : Bytecode.Function := definition 1 {
  ops := #[.call 1 #[0] 3 false], ctrl := .return 0 #[1, 2, 3] }

private def byteIdentity : Bytecode.Function := definition 1 {
  ops := #[.u8Xor 0 0], ctrl := .return 0 #[1] }

private def callsByteIdentity : Bytecode.Function := definition 1 {
  ops := #[.call 1 #[0] 1 false, .mul 1 1], ctrl := .return 0 #[2] }

private def callsUnconstrained : Bytecode.Function := definition 1 {
  ops := #[.call 1 #[0] 1 true], ctrl := .return 0 #[1] }

/-- Singleton circuits for the constrained functions only. -/
private def library (functions : Array Bytecode.Function) : Bytecode.Toplevel :=
  { functions, memorySizes := #[],
    circuits := (functions.zipIdx.filter (·.1.constrained)).map fun (f, index) =>
      { name := s!"function_{index}", members := #[index], layout := f.layout } }

private def programWidths (name : String) (functions : Array Bytecode.Function)
    (expected : Array SeedWidth) (bytes : Nat) (memorySizes : Array Nat := #[]) : TestSeq :=
  test name ((match programPlan { library functions with memorySizes } 0 with
    | some plan => widths plan == expected && plan.typedSeedBytes == bytes
    | none => false) : Bool)

/-- Stores a byte and a field element, then loads the pair back. -/
private def storeThenLoad : Bytecode.Function := definition 2 {
  ops := #[.u8Xor 0 0, .store #[2, 1], .load 2 3], ctrl := .return 0 #[4, 5] }

/-- Loads from a table nothing in the library stores into. -/
private def loadUnstored : Bytecode.Function := definition 1 {
  ops := #[.load 2 0], ctrl := .return 0 #[1, 2] }

/-- Stores a wide value into the slot another function stores a byte into. -/
private def storeWide : Bytecode.Function := definition 1 {
  ops := #[.store #[0, 0]], ctrl := .return 0 #[1] }

/-- Loads through a continuation merge of input 1, after an arm-local
constant, so the pointer's bytecode index (2) is not its value id (3). -/
private def loadThroughMerge : Bytecode.Function := definition 2 {
  ops := #[], ctrl := .matchContinue 0
    #[(0, { ops := #[.const 7], ctrl := .yield 0 #[1] })]
    (some { ops := #[], ctrl := .yield 1 #[1] })
    1 1 0 { ops := #[.load 1 2], ctrl := .return 2 #[3] } }

def schemaTests : TestSeq :=
  test "typed layout stores wider words first, aligned, padded to eight"
    (let schema := SeedSchema.ofWidths #[.full, .u8, .u32, .u16, .full, .u8]
     schema.offsets == #[0, 22, 16, 20, 8, 23] && schema.bytes == 24) ++
  test "an all-full schema is the canonical encoding"
    ((SeedSchema.canonical 3).isCanonical && (SeedSchema.canonical 3).bytes == 24) ++
  accepts "byte operations narrow the inputs they consume"
    (singletonProgram #[arithmetic]) (fun plan =>
      widths plan == #[.full, .u8, .u8] && plan.typedSeedBytes == 16) ++
  accepts "an exhaustive match bounds its discriminant, a fallback does not"
    (singletonProgram #[exhaustiveThenFallback]) (fun plan =>
      widths plan == #[.full, .u16, .full] && plan.typedSeedBytes == 24) ++
  accepts "a byte use on one arm speculatively narrows the word on every arm"
    (singletonProgram #[definition 2 (branchBody 4)]) (fun plan =>
      widths plan == #[.full, .full, .u8]) ++
  accepts "continuation uses bound the values every arm yields"
    (singletonProgram #[yieldsIntoByteUse]) (fun plan =>
      widths plan == #[.full, .full, .u8]) ++
  -- The callee's byte use narrows the argument; 255 + 200 < 2^16, its square
  -- is below 2^32, and the square of that is wide.
  programWidths "constants and byte results bound sums and products through call results"
    #[callsBoundedArithmetic, boundedArithmetic] #[.full, .u8, .u16, .u32, .full] 24 ++
  programWidths "call results take callee output bounds and arguments take callee input bounds"
    #[callsByteIdentity, byteIdentity] #[.full, .u8, .u8] 16 ++
  programWidths "recursive returns reach the least fixpoint instead of staying wide"
    #[recursiveBytes] #[.full, .full, .u8, .u8] 24 ++
  programWidths "unconstrained callees contribute no bounds"
    #[callsUnconstrained, { byteIdentity with constrained := false }] #[.full, .full, .full] 24 ++
  -- Seed: multiplicity, the two inputs, the store pointer, the two loaded words.
  programWidths "loads take the join of every store into their table; pointers are u32"
    #[storeThenLoad] #[.full, .u8, .full, .u32, .u8, .full] 32 #[2] ++
  programWidths "a wide store elsewhere in the library widens the loaded slot"
    #[storeThenLoad, storeWide] #[.full, .u8, .full, .u32, .full, .full] 40 #[2] ++
  programWidths "a table with no store site loads unknown values but its pointer is u32"
    #[loadUnstored] #[.full, .u32, .full, .full] 32 #[2] ++
  programWidths "pointer bounds follow resolved operands through merges"
    #[loadThroughMerge] #[.full, .full, .u32, .full] 32 #[1]

def malformedTests : TestSeq :=
  rejects "invalid value index"
    (singletonProgram #[definition 1 { ops := #[.mul 0 1], ctrl := .return 0 #[1] }]) ++
  rejects "invalid callee index"
    (singletonProgram #[definition 1 { ops := #[.call 9 #[0] 1 false], ctrl := .return 0 #[1] }]) ++
  rejects "callee input arity mismatch"
    (singletonProgram #[definition 1 {
      ops := #[.call 1 #[] 1 false], ctrl := .return 0 #[1] }, identityFunction]) ++
  rejects "callee output arity mismatch"
    (singletonProgram #[definition 1 {
      ops := #[.call 1 #[0] 2 false], ctrl := .return 0 #[1, 2] }, identityFunction]) ++
  rejects "memory read without its table"
    (singletonProgram #[definition 1 { ops := #[.load 2 0], ctrl := .return 0 #[1, 2] }]) ++
  rejects "u32 operands must have four bytes"
    (singletonProgram #[definition 1 {
      ops := #[.unconstrainedU32Add #[0] #[0, 0, 0, 0]], ctrl := .return 0 #[1] }]) ++
  rejects "yield cannot escape a function"
    (singletonProgram #[definition 1 { ops := #[], ctrl := .yield 0 #[0] }]) ++
  rejects "yield arity must match its continuation"
    (singletonProgram #[definition 1 {
      ops := #[], ctrl := .matchContinue 0
        #[(0, { ops := #[], ctrl := .yield 0 #[] })] none 1 0 0
        { ops := #[], ctrl := .return 1 #[1] } }]) ++
  rejects "duplicate selector allocation"
    (singletonProgram #[definition 1 {
      ops := #[], ctrl := .match 0 #[(0, { ops := #[], ctrl := .return 0 #[0] })]
        (some { ops := #[], ctrl := .return 0 #[0] }) }]) ++
  rejects "selector outside the declared region"
    (singletonProgram #[definition 1 { ops := #[], ctrl := .return 1 #[0] }]) ++
  rejects "duplicate match cases"
    (singletonProgram #[definition 1 {
      ops := #[], ctrl := .match 0
        #[(0, { ops := #[], ctrl := .return 0 #[0] }),
          (0, { ops := #[], ctrl := .return 1 #[0] })] none }])

def groupingTests : TestSeq :=
  test "grouped functions retain member plans and merge only circuit regions"
    ((match Aiur.TracePlan.program grouped with
    | .error _ => false
    | .ok plan => plan.functions.size == 2 && grouped.circuits[0]!.layout ==
        { inputSize := 2, selectors := 5, auxiliaries := 9, lookups := 2 }) : Bool) ++
  rejects "missing constrained member" { grouped with circuits := #[] } ++
  rejects "duplicate circuit member" { grouped with
    circuits := grouped.circuits ++ grouped.circuits } ++
  rejects "declared circuit layout must match its members" { grouped with
    circuits := #[{ grouped.circuits[0]! with layout := arithmetic.layout }] } ++
  rejects "unconstrained function cannot be a circuit member" { grouped with
    functions := #[{ arithmetic with constrained := false }, nested] }

private def reportFixture (reverseAliases : Bool) : Except String Lean.Json :=
  let names : List (Global × Nat) := [(⟨`z_alias⟩, 0), (⟨`a_alias⟩, 0), (⟨`nested⟩, 1)]
  Aiur.TraceReport.program "fixture" {
    source := ⟨#[], #[], #[]⟩, bytecode := grouped,
    nameMap := .ofList (if reverseAliases then names.reverse else names) }

private def reportShapes : Except String Bool := do
  let report ← reportFixture false
  let circuits ← (← report.getObjVal? "circuits").getArr?
  let some circuit := circuits[0]? | throw "missing grouped circuit"
  let members ← (← circuit.getObjVal? "members").getArr?
  let some first := members[0]? | throw "missing first member"
  let some second := members[1]? | throw "missing second member"
  let firstSelector ← (← first.getObjVal? "selector_base").getNat?
  let secondSelector ← (← second.getObjVal? "selector_base").getNat?
  let firstAuxiliary ← (← first.getObjVal? "auxiliary_base").getNat?
  let secondAuxiliary ← (← second.getObjVal? "auxiliary_base").getNat?
  let unknownRows := match ← circuit.getObjVal? "real_rows" with
    | .null => true
    | _ => false
  let bytes ← (← report.getObjVal? "primitive_circuits").getArr?
  let some bytes1 := bytes[0]? | throw "missing bytes1"
  let some bytes2 := bytes[1]? | throw "missing bytes2"
  let height1 ← (← bytes1.getObjVal? "fixed_height").getNat?
  let height2 ← (← bytes2.getObjVal? "fixed_height").getNat?
  let active1 ← (← bytes1.getObjVal? "always_active").getBool?
  let active2 ← (← bytes2.getObjVal? "always_active").getBool?
  pure (firstSelector == 2 && secondSelector == 3 &&
    firstAuxiliary == 7 && secondAuxiliary == 7 && unknownRows &&
    height1 == 256 && height2 == 65536 && active1 && active2)

private def oneSelectorMatchIsBranchless : Except String Bool := do
  let top := singletonProgram #[definition 1 {
    ops := #[], ctrl := .match 0
      #[(0, { ops := #[], ctrl := .match 0 #[] none })]
      (some { ops := #[], ctrl := .return 0 #[0] }) }]
  let report ← Aiur.TraceReport.program "fixture" {
    source := ⟨#[], #[], #[]⟩, bytecode := top, nameMap := {} }
  let circuits ← (← report.getObjVal? "circuits").getArr?
  let some circuit := circuits[0]? | throw "missing circuit"
  (← circuit.getObjVal? "branchless").getBool?

def reportTests : TestSeq :=
  test "report ordering is independent of alias-map insertion order"
    ((match reportFixture false, reportFixture true with
    | .ok left, .ok right => left.compress == right.compress
    | _, _ => false) : Bool) ++
  test "report has group offsets, unknown weights and mandatory byte-table heights"
    ((match reportShapes with | .ok valid => valid | .error _ => false) : Bool) ++
  test "one-selector match with an empty arm is not branchless"
    ((match oneSelectorMatchIsBranchless with | .ok branchless => !branchless | .error _ => false) : Bool)

def tests : TestSeq := allocationTests ++ preparationTests ++ schemaTests ++
  malformedTests ++ groupingTests ++ reportTests

end AiurTests.TracePlan

end
