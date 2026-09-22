module

public import Ix.Aiur.Stages.TraceCodegen
public import Ix.Aiur.Compiler
public import Ix.IxVM.Toplevel

public section

namespace AiurTests.TraceCodegen

open Aiur Aiur.Bytecode

private def definition (inputs : Nat) (body : Block) (constrained : Bool := true) : Function :=
  let (_, state) := (Concrete.Bytecode.blockLayout body).run
    (Concrete.Bytecode.LayoutMState.new inputs)
  { body, entry := true, constrained,
    layout := { state.functionLayout with lookups := state.functionLayout.lookups + 1 } }

private def fields : Function := definition 2 {
  ops := #[.add 0 1, .sub 0 1, .mul 0 1, .const 7, .mul 4 5,
    .eqZero 6, .eqZero 0, .unconstrainedGInverse 0, .unconstrainedGToBytes 0],
  ctrl := .return 0 #[] }

private def bytes : Function := definition 2 {
  ops := #[.u8BitDecomposition 0, .u8ShiftLeft 0, .u8ShiftRight 0,
    .u8Xor 0 1, .u8Add 0 1, .u8Sub 0 1, .u8Mul 0 1, .u8And 0 1,
    .u8Or 0 1, .u8LessThan 0 1, .u8XorSplit7 0 1, .u8XorSplit4 0 1,
    .u8RangeCheck 0 1, .mul 14 16],
  ctrl := .return 0 #[] }

private def words : Function := definition 12 {
  ops := #[.u32ToField #[0,1,2,3], .u32ToField #[4,5,6,7], .u32LessThan 12 13,
    .unconstrainedU32Add #[0,1,2,3] #[4,5,6,7],
    .unconstrainedU32Add3 #[0,1,2,3] #[4,5,6,7] #[8,9,10,11], .mul 19 24],
  ctrl := .return 0 #[12,13,14,19,24] }

private def branches : Function := definition 2 {
  ops := #[], ctrl := .matchContinue 0
    #[(0, { ops := #[.mul 1 1], ctrl := .yield 0 #[2] }),
      (1, { ops := #[.u8Add 1 1], ctrl := .yield 1 #[2] })]
    (some { ops := #[.eqZero 1], ctrl := .yield 2 #[2] })
    1 4 1 { ops := #[.mul 2 1], ctrl := .return 3 #[3] } }

private def memory : Function := definition 1 {
  ops := #[.mul 0 0, .store #[0,1], .call 5 #[2] 1 false, .load 2 3, .add 4 5],
  ctrl := .return 0 #[6] }

private def identityFunction : Function := definition 1 { ops := #[], ctrl := .return 0 #[0] }

private def aliasFunction : Function := definition 1 {
  ops := #[.mul 0 0, .call 5 #[1] 1 false], ctrl := .return 0 #[2] }

private def ioFunction : Function := definition 2 {
  ops := #[.ioWrite 0 #[1], .ioGetInfo 0 #[1], .ioRead 0 2 2,
    .const 999, .ioSetInfo 0 #[6] 2 3, .assertEq #[4] #[4] (some "quoted \"value\"\nλ"),
    .debug "trace fixture" none],
  ctrl := .return 0 #[4,5] }

private def earlyReturn : Function := definition 1 {
  ops := #[.mul 0 0], ctrl := .matchContinue 1
    #[(0, { ops := #[], ctrl := .return 0 #[] })]
    (some { ops := #[], ctrl := .yield 1 #[] })
    0 1 0 { ops := #[.load 1 0], ctrl := .return 2 #[] } }

private def nestedEarlyReturn : Function := definition 1 {
  ops := #[], ctrl := .matchContinue 0
    #[(0, {
      ops := #[.mul 0 0]
      ctrl := .match 1
        #[(0, { ops := #[], ctrl := .return 0 #[] })]
        (some { ops := #[], ctrl := .yield 1 #[] }) })]
    (some { ops := #[], ctrl := .yield 2 #[] })
    0 2 0 { ops := #[.load 1 0], ctrl := .return 3 #[] } }

private def branchReads : Function := definition 2 {
  ops := #[.const 0], ctrl := .matchContinue 0
    #[(0, { ops := #[.ioRead 1 2 1], ctrl := .yield 0 #[3] })]
    (some { ops := #[.ioRead 1 2 2], ctrl := .yield 1 #[4] })
    1 3 0 { ops := #[.ioRead 1 3 1], ctrl := .return 2 #[4] } }

private def bigUint : Function := definition 2 {
  ops := #[.unconstrainedBigUintDivMod 0 1, .load 10 2], ctrl := .return 0 #[2,3] }

private def constants : Function := definition 0 {
  ops := #[.const 0, .eqZero 0, .const (G.ofNat (gSize.toNat - 1)), .eqZero 2],
  ctrl := .return 0 #[] }

private def unconstrainedFunction : Function := definition 1 {
  ops := #[.unconstrainedGInverse 0], ctrl := .return 0 #[1] } false

private def unconstrainedCaller : Function := definition 1 {
  ops := #[.call 13 #[0] 1 true], ctrl := .return 0 #[1] }

private def emptyCaller : Function := definition 1 {
  ops := #[.mul 0 0, .call 16 #[] 0 false, .load 0 0, .ioRead 0 0 0],
  ctrl := .return 0 #[] }

private def emptyFunction : Function := definition 0 { ops := #[], ctrl := .return 0 #[] }

private def nestedMergeRead : Function := definition 3 {
  ops := #[], ctrl := .matchContinue 0
    #[(0, {
      ops := #[]
      ctrl := .matchContinue 2
        #[(0, { ops := #[.const 0], ctrl := .yield 0 #[3] })]
        (some { ops := #[.const 1], ctrl := .yield 1 #[3] })
        1 1 0 { ops := #[.add 3 2], ctrl := .yield 2 #[4] } })]
    (some { ops := #[.const 2], ctrl := .yield 3 #[3] })
    1 2 0 { ops := #[.ioRead 1 3 1], ctrl := .return 4 #[4] } }

private def exhaustiveMatch : Function := definition 1 {
  ops := #[], ctrl := .match 0 #[(0, { ops := #[], ctrl := .return 0 #[] })] none }

mutual
  private partial def reindexBlock (oldIndex newIndex : Nat) (block : Block) : Except String Block := do
    let ops ← block.ops.mapM fun op => match op with
      | .call index args size unc =>
        if index != oldIndex then throw "BLAKE3 fixture gained an external callee"
        else pure (.call newIndex args size unc)
      | _ => pure op
    pure { ops, ctrl := ← reindexControl oldIndex newIndex block.ctrl }
  private partial def reindexControl (oldIndex newIndex : Nat) : Ctrl → Except String Ctrl
    | .match d arms fallback => do
      pure (.match d (← arms.mapM fun (v, b) => return (v, ← reindexBlock oldIndex newIndex b))
        (← fallback.mapM (reindexBlock oldIndex newIndex)))
    | .matchContinue d arms fallback n aux lookups continuation => do
      pure (.matchContinue d (← arms.mapM fun (v, b) => return (v, ← reindexBlock oldIndex newIndex b))
        (← fallback.mapM (reindexBlock oldIndex newIndex)) n aux lookups
        (← reindexBlock oldIndex newIndex continuation))
    | ctrl => pure ctrl
end

def fixtureProgram : Except String Toplevel := do
  let mut functions := #[fields, bytes, words, branches, memory, identityFunction,
    aliasFunction, ioFunction, earlyReturn, nestedEarlyReturn, branchReads, bigUint,
    constants, unconstrainedFunction, unconstrainedCaller, emptyCaller, emptyFunction]
  let source ← IxVM.ixVM.mapError (fun error => s!"{repr error}")
  let compiled ← source.compile
  let some index := compiled.getFuncIdx `blake3_compress | throw "missing BLAKE3 function"
  let function := compiled.bytecode.functions[index]!
  functions := functions.push { function with
    entry := true
    body := ← reindexBlock index functions.size function.body }
  functions := functions ++ #[nestedMergeRead, exhaustiveMatch, definition 12 {
    ops := #[.unconstrainedU32Add #[0,1,2,3] #[4,5,6,7],
      .unconstrainedU32Add3 #[0,1,2,3] #[4,5,6,7] #[8,9,10,11], .mul 16 21],
    ctrl := .return 0 #[16,21,22] }]
  let some multiply := compiled.getFuncIdx `u64_mul | throw "missing u64_mul function"
  functions := functions.push { compiled.bytecode.functions[multiply]! with entry := true }
  let mut circuits := #[{
    name := "mixed", members := #[0, 3, 12],
    layout := fields.layout.merge branches.layout |>.merge constants.layout : Circuit }]
  for i in [:functions.size] do
    if functions[i]!.constrained && !(#[0,3,12]).contains i then
      circuits := circuits.push { name := s!"function_{i}", members := #[i], layout := functions[i]!.layout }
  pure { functions, memorySizes := #[0,1,2,10], circuits }

def blake3Program : Except String Bytecode.Toplevel := do
  let top ← fixtureProgram
  let function := top.functions[17]!
  let body ← reindexBlock 17 0 function.body
  let function := { function with body }
  pure {
    functions := #[function], memorySizes := #[],
    circuits := #[{ name := "blake3", members := #[0], layout := function.layout }] }

def emitFixtures : Except String String := do
  Aiur.TraceCodegen.emit (← fixtureProgram) "crate"

end AiurTests.TraceCodegen

end
