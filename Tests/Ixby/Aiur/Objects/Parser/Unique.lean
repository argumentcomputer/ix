module
public import Tests.Ixby.Aiur.Objects.Parser.Common

namespace Tests.Ixby.Aiur.Objects.Parser

open Ix.Ixby Ix.Ixby.AiurBackend
open Ix.Ixby.AiurBackend.Objects.Memory Ix.Ixby.AiurBackend.Objects.Table Ix.Ixby.AiurBackend.Objects.Parser
open Ix.Ixby.AiurBackend.Objects.Identity
open Ix.Ixby.AiurBackend.Objects.Equality Ix.Ixby.AiurBackend.Objects.Unique
open Ix.Ixby.AiurBackend.Objects.Declarations
open Ix.Ixby.AiurBackend.Objects.Admission
open Aiur.Bytecode.Eval

private def testRawId (n : Nat) : RawId :=
  ⟨.ofNat n, 17, 29, 31, 43, 59, 61, 73, 83, 97⟩

private def storeDeclarations (st : EvalState) (decls : Array RawDecl) : EvalState × Aiur.G :=
  let (st, pointer) := memStore st tableNil
  decls.foldr (fun decl state =>
    let next := memStore state.1 (decl.cell state.2)
    (next.1, .ofNat next.2)) (st, .ofNat pointer)

private def uniqueFixture (zero step : Aiur.Bytecode.Block) : Aiur.Bytecode.Block :=
  ⟨#[], .match 11 #[(0, zero)] (some (uniqueNonzero step))⟩

public def uniquenessChecks (compiled : Aiur.CompiledToplevel) : Except String (List Check) := do
  let (comparer, cmp) ← function compiled `is_id_eq
  let (self, unique) ← function compiled `is_unique_id
  let body := uniqueBody comparer self 0 1
  let zero := uniqueZero 0
  let step := uniqueStep comparer self 1
  let accepts := fun b => checkUnique { unique with body := b } comparer self 0 1
  let mut checks : List Check := [
    ("full compiled uniqueness certificate", checkUnique unique comparer self 0 1),
    ("uniqueness certificate binds comparison index", !checkUnique unique (comparer + 1) self 0 1),
    ("uniqueness certificate binds recursion index", !checkUnique unique comparer (self + 1) 0 1),
    ("uniqueness certificate binds both selectors", !checkUnique unique comparer self 1 1 &&
      !checkUnique unique comparer self 0 0),
    ("uniqueness certificate rejects input arity", !checkUnique
      { unique with layout := { unique.layout with inputSize := 11 } } comparer self 0 1),
    ("uniqueness certificate ignores nonsemantic layout metadata", checkUnique
      { unique with layout := { unique.layout with auxiliaries := 999 }, constrained := false } comparer self 0 1),
    ("uniqueness certificate rejects extra root operation", !accepts { body with ops := #[.const 0] }),
    ("uniqueness certificate rejects wrong counter register", !accepts
      ⟨#[], .match 10 #[(0, zero)] (some (uniqueNonzero step))⟩),
    ("uniqueness certificate rejects wrong zero tag", !accepts
      ⟨#[], .match 11 #[(1, zero)] (some (uniqueNonzero step))⟩),
    ("uniqueness certificate rejects added zero arm", !accepts
      ⟨#[], .match 11 #[(0, zero), (1, zero)] (some (uniqueNonzero step))⟩),
    ("uniqueness certificate rejects missing recursive branch", !accepts ⟨#[], .match 11 #[(0, zero)] none⟩),
    ("uniqueness certificate binds Cons tag register", !accepts ⟨#[], .match 11 #[(0, zero)]
      (some ⟨#[.load 13 10], .match 13 #[(0, uniqueTagless step)] none⟩)⟩),
    ("uniqueness certificate rejects a Nil recursion arm", !accepts ⟨#[], .match 11 #[(0, zero)]
      (some ⟨#[.load 13 10], .match 12 #[(1, uniqueTagless step)] none⟩)⟩),
    ("uniqueness certificate rejects extra Cons fallback", !accepts ⟨#[], .match 11 #[(0, zero)]
      (some ⟨#[.load 13 10], .match 12 #[(0, uniqueTagless step)] (some step)⟩)⟩),
    ("uniqueness certificate binds tagless-constructor match", !accepts ⟨#[], .match 11 #[(0, zero)]
      (some ⟨#[.load 13 10], .match 12 #[(0, ⟨#[], .match 14 #[] (some step)⟩)] none⟩)⟩),
    ("uniqueness certificate rejects a tagless-constructor case", !accepts ⟨#[], .match 11 #[(0, zero)]
      (some ⟨#[.load 13 10], .match 12 #[(0, ⟨#[], .match 13 #[(0, step)] (some step)⟩)] none⟩)⟩),
    ("uniqueness certificate rejects yielding base", !accepts (uniqueFixture { zero with ctrl := .yield 0 #[] } step)),
    ("uniqueness certificate rejects yielding step", !accepts (uniqueFixture zero { step with ctrl := .yield 1 #[] })),
    ("uniqueness certificate rejects extra output", !accepts (uniqueFixture zero { step with ctrl := .return 1 #[0] }))]
  for i in [:zero.ops.size] do
    checks := checks ++ [(s!"uniqueness certificate binds base operation {i}",
      !accepts (uniqueFixture { zero with ops := zero.ops.set! i (.const 0) } step))]
  for i in [:step.ops.size] do
    -- The existing const-zero operation is replaced with a distinct constant.
    checks := checks ++ [(s!"uniqueness certificate binds recursive operation {i}",
      !accepts (uniqueFixture zero { step with ops := step.ops.set! i (.const 999) }))]
  for i in [:compareArgs.size] do
    let changed := step.ops.set! 0 (.call comparer (compareArgs.set! i 99) 1 false)
    checks := checks ++ [(s!"uniqueness certificate binds comparator argument {i}",
      !accepts (uniqueFixture zero { step with ops := changed }))]
  for i in [:recurseArgs.size] do
    let changed := step.ops.set! 5 (.call self (recurseArgs.set! i 99) 0 false)
    checks := checks ++ [(s!"uniqueness certificate binds recursive argument {i}",
      !accepts (uniqueFixture zero { step with ops := changed }))]
  let needle := testRawId 999
  let populated := (memStore (memStore initial #[101, 102, 103]).1 (Array.replicate 13 999)).1
  for count in [:17] do
    let decls : Array RawDecl := (Array.range count).map fun i => ⟨testRawId (i + 1), .ofNat (i % 8)⟩
    let (st, pointer) := storeDeclarations populated decls
    checks := checks ++ [(s!"fresh semantic ID across exact bounded table length {count}",
      (readTable (bytecodeMemory st) pointer.n count).isSome &&
      success (snapshot compiled `is_unique_id (needle.flat ++ #[pointer, .ofNat count]) st (count + 1)) #[] st)]
    for i in [:count] do
      let duplicate := testRawId (i + 1)
      checks := checks ++ [(s!"duplicate rejection at position {i} of {count}",
        failed (snapshot compiled `is_unique_id (duplicate.flat ++ #[pointer, .ofNat count]) st (count + 1)) .assertFailed)]
    if count > 0 then
      checks := checks ++ [(s!"uniqueness rejects too-small count for table length {count}",
        failed (snapshot compiled `is_unique_id (needle.flat ++ #[pointer, .ofNat (count - 1)]) st (count + 1)) .assertFailed)]
    checks := checks ++ [(s!"uniqueness rejects too-large count for table length {count}",
      failed (snapshot compiled `is_unique_id (needle.flat ++ #[pointer, .ofNat (count + 1)]) st (count + 2))
        .unreachableAfterLayout)]
  for i in [:13] do
    let (st, pointer) := memStore initial (tableNil.set! i 0)
    checks := checks ++ [(s!"uniqueness checks terminal Nil padding field {i}",
      failed (snapshot compiled `is_unique_id (needle.flat ++ #[.ofNat pointer, 0]) st 0) .assertFailed)]
  let (st, pointer) := storeDeclarations populated #[⟨testRawId 1, 3⟩, ⟨testRawId 2, 7⟩]
  let caller := { st with map := #[9999] ++ needle.flat ++ #[pointer, 2, 8888] }
  let arguments := (Array.range 12).map (· + 1)
  for flag in [false, true] do
    checks := checks ++ [(s!"uniqueness Call returns exact original caller state/{flag}",
      match Aiur.Bytecode.Eval.evalOp compiled.bytecode 4 (.call self arguments 0 flag) caller with
      | .ok after => after.map == caller.map && unchanged caller after | _ => false)]
  for (label, fuel, args, outputs, error) in [
      ("input arity", 4, #[1], 0, BytecodeError.arityMismatch self),
      ("missing argument register", 4, (arguments.set! 0 99), 0, .invalidValIdx 99),
      ("output arity", 4, arguments, 1, .callOutputSizeMismatch),
      ("fuel", 1, arguments, 0, .outOfFuel)] do
    checks := checks ++ [("uniqueness Call rejects " ++ label,
      match Aiur.Bytecode.Eval.evalOp compiled.bytecode fuel (.call self args outputs false) caller with
      | .error actual => reprStr actual == reprStr error | _ => false)]
  for n in [2 ^ 32 + pointer.n, goldilocksModulus - 1] do
    checks := checks ++ [(s!"uniqueness never narrows table pointer {n}",
      failed (snapshot compiled `is_unique_id (needle.flat ++ #[.ofNat n, 2]) st 3) (.invalidPointer 13 n))]
  for count in [0, 1] do
    checks := checks ++ [(s!"insufficient uniqueness fuel {count}",
      failed (snapshot compiled `is_unique_id (needle.flat ++ #[pointer, 2]) st count) .outOfFuel)]
  let (nilState, nilPtr) := storeDeclarations initial #[]
  checks := checks ++ [("empty uniqueness body needs no call fuel",
    success (snapshot compiled `is_unique_id (needle.flat ++ #[nilPtr, 0]) nilState 0) #[] nilState)]
  let (badTagState, badTagPtr) := memStore nilState ((RawDecl.cell ⟨testRawId 1, 1⟩ nilPtr).set! 0 2)
  checks := checks ++ [("uniqueness rejects unknown list tag",
    failed (snapshot compiled `is_unique_id (needle.flat ++ #[.ofNat badTagPtr, 1]) badTagState 2) .unreachableAfterLayout)]
  let invalid : RawId := { testRawId 1 with h := .ofNat (2 ^ 32) }
  let (rawState, rawPtr) := storeDeclarations initial #[⟨invalid, 0⟩]
  checks := checks ++ [("raw uniqueness does not establish semantic limb bounds",
    (readTable (bytecodeMemory rawState) rawPtr.n 1).isNone &&
      success (snapshot compiled `is_unique_id (needle.flat ++ #[rawPtr, 1]) rawState 2) #[] rawState),
    ("raw uniqueness still rejects equal out-of-range limbs",
      failed (snapshot compiled `is_unique_id (invalid.flat ++ #[rawPtr, 1]) rawState 2) .assertFailed)]
  let (cycleState, cyclePtr) := memStore initial (RawDecl.cell ⟨testRawId 1, 0⟩ 0)
  checks := checks ++ [("finite count rejects a cyclic raw spine at the terminal check",
    failed (snapshot compiled `is_unique_id (needle.flat ++ #[.ofNat cyclePtr, 3]) cycleState 4) .assertFailed)]
  let fakeCmp := { cmp with body := (⟨#[.const 0], .return 0 #[20]⟩ : Aiur.Bytecode.Block) }
  let fake := { compiled with bytecode := { compiled.bytecode with
    functions := compiled.bytecode.functions.set! comparer fakeCmp } }
  checks := checks ++ [("uniqueness body also requires its actual comparator certificate",
    checkUnique unique comparer self 0 1 && !checkIdEq fakeCmp 0 &&
    success (snapshot fake `is_unique_id ((testRawId 1).flat ++ #[pointer, 2]) st 3) #[] st)]
  return checks

end Tests.Ixby.Aiur.Objects.Parser
