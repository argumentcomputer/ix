module
import Tests.Ixby.Common
import Ix.Ixby.Aiur.Objects
import Ix.Ixby.Aiur.Objects.Memory
import Ix.Aiur.Compiler

/-! Concrete-layout conformance tests, not an AIR or compiler soundness proof.
The positive fixtures use the real compiled object helpers. The diagnostic
decoder also receives deliberately malformed raw memory, which is NOT an
advice channel exposed by the production interpreter. -/

namespace Tests.Ixby.Aiur.Objects.Memory

open Ix.Ixby Ix.Ixby.AiurBackend
open Ix.Ixby.AiurBackend.Objects.Refinement Ix.Ixby.AiurBackend.Objects.Memory
open Aiur.Bytecode.Eval

private def ctorId (tag : Nat) : CtorId := ⟨37, 2, tag⟩
private def table : Array CtorDecl :=
  #[⟨ctorId 0, 0⟩, ⟨ctorId 1, 1⟩, ⟨ctorId 2, 2⟩, ⟨ctorId 3, 16⟩]
private def obj (index : Nat) (fields : Array Value) : Value := .ctor table[index]!.id fields
private def word (n : Nat) : Value := .scalar (.word32 n.toUInt32)
private def atomFlat (tag : Nat) (a b c d : Aiur.G := 0) : Array Aiur.G :=
  if tag == 4 then #[0, 4, 4, 4, 4, 4] else #[0, .ofNat tag, a, b, c, d]
private def ctorFlat (index pointer count rank : Nat) : Array Aiur.G :=
  #[1, .ofNat index, .ofNat pointer, .ofNat count, .ofNat rank, 0]
private def nilFlat : Array Aiur.G := #[1, 1, 1, 1, 1, 1, 1, 1]
private def consFlat (value : Array Aiur.G) (tail : Nat) : Array Aiur.G :=
  #[0] ++ value ++ #[.ofNat tail]

private def memory (cells : List (Nat × Array Aiur.G)) : RawMemory := fun width pointer =>
  (cells.find? (fun cell => cell.1 == pointer && cell.2.size == width)).map Prod.snd
private def replace (raw : RawMemory) (pointer : Nat) (flat : Array Aiur.G) : RawMemory :=
  fun width address => if width == cellWidth && address == pointer then some flat else raw width address
private def empty : RawMemory := fun _ _ => none

private def pairMemory : RawMemory := memory [
  (0, nilFlat), (1, consFlat (atomFlat 1 17) 0), (2, consFlat (atomFlat 1 23) 1)]
private def pairFlat : Array Aiur.G := ctorFlat 2 2 2 2
private def pair : Value := obj 2 #[word 17, word 23]
private def accepts (raw : RawMemory) (flat : Array Aiur.G) (nodes : Nat)
    (value : Value) (remaining := 0) : Bool := reconstruct raw table flat nodes == some (value, remaining)
private def rejects (raw : RawMemory) (flat : Array Aiur.G) (nodes := 128) : Bool :=
  (reconstruct raw table flat nodes).isNone

private def decoderChecks : IO (List Check) := do
  return [
  ("Bool false", accepts empty (atomFlat 0) 1 (.scalar (.bool false))),
  ("Bool true", accepts empty (atomFlat 0 1) 1 (.scalar (.bool true))),
  ("Bool is not arbitrary nonzero", rejects empty (atomFlat 0 2)),
  ("Word32 byte order", accepts empty (atomFlat 1 0x78 0x56 0x34 0x12) 1 (word 0x12345678)),
  ("Word32 maximum", accepts empty (atomFlat 1 255 255 255 255) 1 (word 0xffffffff)),
  ("field maximum is not narrowed", accepts empty (atomFlat 2 (.ofNat (goldilocksModulus - 1)))
    1 (.scalar (.field (Goldilocks.reduce (goldilocksModulus - 1))))),
  ("extension coefficient order", accepts empty (atomFlat 3 7 11) 1
    (.scalar (.extField ⟨Goldilocks.reduce 7, Goldilocks.reduce 11⟩))),
  ("erased", accepts empty (atomFlat 4) 1 .erased),
  ("erased uses tag padding, not zero padding", rejects empty #[0, 4, 0, 0, 0, 0]),
  ("unknown scalar tag", rejects empty (atomFlat 5)),
  ("unknown reference tag", rejects empty #[2, 0, 0, 0, 0, 0]),
  ("short reference", rejects empty #[0, 4, 0, 0, 0]),
  ("long reference", rejects empty #[0, 4, 0, 0, 0, 0, 0]),
  ("empty node budget", rejects empty (atomFlat 4) 0),
  ("unused node budget returned", accepts empty (atomFlat 4) 128 .erased 127),
  ("empty depth budget", (reconstructRef (typedHeap empty) table 0 1 (.atom .erased)).isNone),
  ("nullary constructor consumes a node", accepts (memory [(0, nilFlat)]) (ctorFlat 0 0 0 1) 1 (obj 0 #[])),
  ("nullary constructor still requires Nil", rejects empty (ctorFlat 0 0 0 1)),
  ("Nil uses tag padding, not zero padding", rejects
    (memory [(0, #[1, 0, 0, 0, 0, 0, 0, 0])]) (ctorFlat 0 0 0 1)),
  ("declaration-order fields", accepts pairMemory pairFlat 3 pair),
  ("siblings share node budget", rejects pairMemory pairFlat 2),
  ("parent and children consume exactly three nodes", accepts pairMemory pairFlat 7 pair 4),
  ("missing declaration", rejects pairMemory (ctorFlat 4 2 2 2)),
  ("declaration arity mismatch", rejects pairMemory (ctorFlat 1 2 2 2)),
  ("count too short", rejects pairMemory (ctorFlat 1 2 1 2)),
  ("count too long", rejects pairMemory (ctorFlat 3 2 16 2)),
  ("huge field count rejected before traversal", rejects pairMemory (ctorFlat 2 2 (2 ^ 32) 2)),
  ("zero rank", rejects pairMemory (ctorFlat 2 2 2 0)),
  ("rank must equal computed maximum plus one", rejects pairMemory (ctorFlat 2 2 2 3)),
  ("rank over derived bound", rejects pairMemory (ctorFlat 2 2 2 289)),
  ("constructor padding", rejects pairMemory (pairFlat.set! 5 1)),
  ("missing physical pointer", rejects pairMemory (ctorFlat 2 99 2 2)),
  ("pointer is not truncated to u32", rejects pairMemory (ctorFlat 2 (2 ^ 32 + 2) 2 2)),
  ("logical index is not truncated to u32", rejects pairMemory (ctorFlat (2 ^ 32 + 2) 2 2 2)),
  ("wrong memory width", rejects (memory [(0, #[1, 0, 0, 0, 0, 0, 0])]) (ctorFlat 0 0 0 1)),
  ("malformed memory width returned by raw adapter", rejects (replace pairMemory 2 #[0]) pairFlat),
  ("unknown cell tag", rejects (replace pairMemory 2 ((consFlat (atomFlat 4) 1).set! 0 2)) pairFlat),
  ("early Nil", rejects (replace pairMemory 2 nilFlat) pairFlat),
  ("non-Nil terminator", rejects (replace pairMemory 0 (consFlat (atomFlat 4) 0)) pairFlat),
  ("cyclic field-list spine", rejects (replace pairMemory 1 (consFlat (atomFlat 1 17) 2)) pairFlat),
  ("cyclic child graph with forged rank", rejects
    (memory [(0, nilFlat), (1, consFlat (ctorFlat 1 1 1 1) 0)]) (ctorFlat 1 1 1 2)),
  ("unreachable malformed and cyclic memory is allowed", accepts
    (replace (replace pairMemory 99 #[2]) 100 (consFlat (ctorFlat 1 100 1 1) 100)) pairFlat 3 pair),
  ("equal cells at different pointers are allowed", accepts
    (replace pairMemory 99 (consFlat (atomFlat 1 23) 1)) (ctorFlat 2 99 2 2) 3 pair),
  ("large canonical physical pointer is allowed", accepts
    (replace pairMemory (2 ^ 32 + 2) (consFlat (atomFlat 1 23) 1))
    (ctorFlat 2 (2 ^ 32 + 2) 2 2) 3 pair)
] ++
  (List.range 4).map (fun i => (s!"word byte {i} range checked",
    rejects empty ((atomFlat 1).set! (i + 2) 256))) ++
  ([0, 2, 3, 4].flatMap fun tag =>
    let active := if tag == 3 then 2 else if tag == 4 then 0 else 1
    (List.range (4 - active)).map fun i => (s!"scalar {tag} padding {active + i} checked",
      rejects empty ((atomFlat tag).set! (2 + active + i) 1))) ++
  (List.range 7).map (fun i => (s!"Nil padding {i} checked",
    rejects (replace pairMemory 0 (nilFlat.set! (i + 1) 0)) pairFlat))

-- These source fixtures construct cells via typed stores and invoke the actual
-- interpreter helpers. No parallel model of is_make/is_project is substituted.
private def fixtures : Aiur.Source.Toplevel := ⟦
  fn om_ctors() -> ISCtors {
    let nilCells = store(ListNode.Nil);
    let pair = store(ListNode.Cons(ISCtorDecl.Mk([37, 0, 0, 0, 0, 0, 0, 0, 2, 2], 2), nilCells));
    let unary = store(ListNode.Cons(ISCtorDecl.Mk([37, 0, 0, 0, 0, 0, 0, 0, 2, 1], 1), pair));
    store(ListNode.Cons(ISCtorDecl.Mk([37, 0, 0, 0, 0, 0, 0, 0, 2, 0], 0), unary))
  }
  fn om_atom(kind: G) -> ISValue {
    match kind {
      0 => ISValue.Atom(IBValue.Bool(1)),
      1 => ISValue.Atom(IBValue.Word([120u8, 86u8, 52u8, 18u8])),
      2 => ISValue.Atom(IBValue.Field(18446744069414584320)),
      3 => ISValue.Atom(IBValue.Ext([7, 11])),
      _ => ISValue.Atom(IBValue.Erased),
    }
  }
  fn om_pair() -> ISValue {
    let nilCells = store(ListNode.Nil);
    let first = store(ListNode.Cons(om_atom(1), nilCells));
    let fields = store(ListNode.Cons(om_atom(3), first));
    is_make(om_ctors(), 3, 2, fields, 2)
  }
  fn om_project(index: G) -> ISValue { is_project(om_pair(), index) }
  fn om_nullary() -> ISValue { is_make(om_ctors(), 3, 0, store(ListNode.Nil), 0) }
  fn om_shared(levels: G) -> ISValue {
    match levels {
      0 => om_atom(1),
      _ =>
        let child = om_shared(levels - 1);
        let nilCells = store(ListNode.Nil);
        let first = store(ListNode.Cons(child, nilCells));
        let fields = store(ListNode.Cons(child, first));
        is_make(om_ctors(), 3, 2, fields, 2),
    }
  }
  fn om_chain(levels: G) -> ISValue {
    match levels {
      0 => om_atom(1),
      _ =>
        let child = om_chain(levels - 1);
        let fields = store(ListNode.Cons(child, store(ListNode.Nil)));
        is_make(om_ctors(), 3, 1, fields, 1),
    }
  }
⟧

private def compileFixture : IO (Except String Aiur.CompiledToplevel) := do
  return do
    let source ← objectsToplevel
    let source ← source.merge fixtures |>.mapError toString
    (source.prune [`om_atom, `om_pair, `om_project, `om_nullary, `om_shared, `om_chain]).compile
      |>.mapError toString

/-- Same function-boundary handling as runFunction, retaining its memory for
inspection. This test helper does not change the production evaluator API. -/
private def snapshot (compiled : Aiur.CompiledToplevel) (name : Lean.Name)
    (args : Array Aiur.G) (initial : EvalState := { ioBuffer := default }) :
    Except String (Array Aiur.G × EvalState) := do
  let some index := compiled.getFuncIdx name | throw s!"missing function {name}"
  let some f := compiled.bytecode.functions[index]? | throw s!"missing function {index}"
  unless f.layout.inputSize == args.size do throw s!"arity mismatch in {name}"
  match evalBlock compiled.bytecode 1024 f.body { initial with map := args } with
  | .ok (flat, state) | .error (.earlyReturn flat state) => return (flat, state)
  | .error e => throw s!"{name}: {repr e}"

private def dag : Nat → Value → Value
  | 0, leaf => leaf
  | n + 1, leaf => let child := dag n leaf; obj 2 #[child, child]
private def chain : Nat → Value → Value
  | 0, leaf => leaf
  | n + 1, leaf => obj 1 #[chain n leaf]

/-- Test-only entry adapter: native execution requires an entry, while ISValue
contains an internal pointer and cannot be a public source signature. Only the
entry flag changes; the compiled body and its callee bodies are untouched.
This does not build a proof system or change the production interpreter/key. -/
private def nativeSnapshot (compiled : Aiur.CompiledToplevel) (name : Lean.Name)
    (args : Array Aiur.G) : Except String (Array Aiur.G) := do
  let some index := compiled.getFuncIdx name | throw s!"missing function {name}"
  let functions := compiled.bytecode.functions.modify index (fun f => { f with entry := true })
  let bytecode := { compiled.bytecode with functions }
  return (← bytecode.execute index args default).1

private def fixtureChecks (compiled : Aiur.CompiledToplevel) : List (String × Bool) := Id.run do
  let mut checks := []
  let leaf := word 0x12345678
  let ext := Value.scalar (.extField ⟨Goldilocks.reduce 7, Goldilocks.reduce 11⟩)
  let cases : List (String × Lean.Name × Array Aiur.G × Nat × Value) := [
    ("compiled Bool layout", `om_atom, #[0], 1, .scalar (.bool true)),
    ("compiled Word layout", `om_atom, #[1], 1, leaf),
    ("compiled Field layout", `om_atom, #[2], 1, .scalar (.field (Goldilocks.reduce (goldilocksModulus - 1)))),
    ("compiled Ext layout", `om_atom, #[3], 1, ext),
    ("compiled Erased layout", `om_atom, #[4], 1, .erased),
    ("compiled nullary make", `om_nullary, #[], 1, obj 0 #[]),
    ("compiled asymmetric pair", `om_pair, #[], 3, obj 2 #[leaf, ext]),
    ("compiled first projection", `om_project, #[0], 1, leaf),
    ("compiled second projection", `om_project, #[1], 1, ext),
    ("compiled shared DAG unfolds seven nodes", `om_shared, #[2], 7, dag 2 leaf),
    ("compiled shared DAG unfolds 127 nodes", `om_shared, #[6], 127, dag 6 leaf),
    ("compiled intermediate exceeds I/O node bound", `om_shared, #[7], 255, dag 7 leaf),
    ("compiled intermediate exceeds I/O depth bound", `om_chain, #[33], 34, chain 33 leaf),
    ("compiled maximum intermediate rank", `om_chain, #[287], 288, chain 287 leaf)]
  for (label, name, args, nodes, expected) in cases do
    match snapshot compiled name args with
    | .error error => checks := checks ++ [(s!"{label}: {error}", false)]
    | .ok (flat, state) =>
      let decoded := reconstruct (bytecodeMemory state) table flat nodes
      let ok := decoded == some (expected, 0)
      let detail := if ok then label else s!"{label}: flat={flat.map (·.n)}, decoded={repr decoded}, cell={repr (memLoad state 8 (flat.getD 2 0).n)}"
      checks := checks ++ [(detail, ok),
        (label ++ " shared budget cannot be reset", rejects (bytecodeMemory state) flat (nodes - 1))]
      let native := nativeSnapshot compiled name args
      checks := checks ++ [(label ++ " native flat-output parity" ++
          (match native with | .error e => s!": {e}" | .ok _ => ""),
        match native with | .ok out => out == flat | .error _ => false)]
  for (label, name, args) in [
      ("projection out of bounds", `om_project, #[2]),
      ("rank 289 rejected", `om_chain, #[288])] do
    checks := checks ++ [(label, !(snapshot compiled name args).isOk)]
  return checks

/-- Deliberately forged helper inputs in the Lean bytecode evaluator. Production
execution cannot receive this raw memory as advice. These tests distinguish
local helper checks from the recursive invariant required for live values. -/
private def helperChecks (compiled : Aiur.CompiledToplevel) : List (String × Bool) := Id.run do
  let .ok (declPointer, declarations) := snapshot compiled `om_ctors #[]
    | return [("compiled declaration fixture", false)]
  let ctors := declPointer.getD 0 0
  let seed (cells : List (Array Aiur.G)) := cells.foldl
    (fun state cell => (memStore state cell).1) declarations
  let base := [nilFlat, consFlat (atomFlat 1 17) 0, consFlat (atomFlat 1 23) 1]
  let make (state : EvalState) (index pointer count : Nat) :=
    snapshot compiled `is_make #[ctors, 3, .ofNat index, .ofNat pointer, .ofNat count] state
  let expectedFailure (result : Except String (Array Aiur.G × EvalState))
      (error : BytecodeError) :=
    match result with
    | .error actual => actual == s!"is_make: {repr error}"
    | .ok _ => false
  let cyclic := ctorFlat 1 1 1 1
  let forged := seed [nilFlat, consFlat cyclic 0]
  let mut checks := [
    ("compiled seeded make reconstructs", match make (seed base) 2 2 2 with
      | .ok (flat, state) => accepts (bytecodeMemory state) flat 3 pair
      | _ => false),
    ("local helper does not establish child closure", match make forged 1 1 1 with
      | .ok (flat, state) => flat == ctorFlat 1 1 1 2 && rejects (bytecodeMemory state) flat
      | _ => false),
    ("compiled helper rejects missing pointer", expectedFailure (make (seed base) 2 99 2)
      (.invalidPointer 8 99)),
    ("compiled helper does not narrow pointers", expectedFailure (make (seed base) 2 (2 ^ 32 + 2) 2)
      (.invalidPointer 8 (2 ^ 32 + 2)))]
  let failures : List (String × List (Array Aiur.G) × Nat × Nat × Nat × BytecodeError) := [
    ("declaration arity", base, 1, 2, 2, .assertFailed),
    ("declaration index", base, 3, 2, 2, .assertFailed),
    ("short field count", base, 1, 2, 1, .assertFailed),
    ("long field count", base, 2, 1, 2, .unreachableAfterLayout),
    ("unknown cell tag", [(consFlat (atomFlat 4) 0).set! 0 2], 1, 0, 1, .unreachableAfterLayout),
    ("unknown reference tag", [nilFlat, consFlat #[2, 0, 0, 0, 0, 0] 0], 1, 1, 1, .unreachableAfterLayout),
    ("Nil padding", [(nilFlat.set! 7 0), consFlat (atomFlat 1 17) 0], 1, 1, 1, .assertFailed),
    ("zero child rank", [nilFlat, consFlat (ctorFlat 0 0 0 0) 0], 1, 1, 1, .assertFailed),
    ("child rank 289", [nilFlat, consFlat (ctorFlat 0 0 0 289) 0], 1, 1, 1, .assertFailed),
    ("computed parent rank 289", [nilFlat, consFlat (ctorFlat 0 0 0 288) 0], 1, 1, 1, .assertFailed),
    ("cyclic field spine", [nilFlat, consFlat (atomFlat 1 17) 2,
      consFlat (atomFlat 1 23) 1], 2, 2, 2, .assertFailed)]
  for (label, cells, index, pointer, count, error) in failures do
    let result := make (seed cells) index pointer count
    let ok := expectedFailure result error
    let detail := if ok then "" else s!": {repr (result.map Prod.fst)}"
    checks := checks ++ [("compiled helper rejects " ++ label ++ detail, ok)]
  return checks

public def suite : IO UInt32 := runChecks "ixby-objects-memory" do
  match ← compileFixture with
  | .error error => return [(s!"compile fixtures: {error}", false)]
  | .ok compiled => return (← decoderChecks) ++ fixtureChecks compiled ++ helperChecks compiled

end Tests.Ixby.Aiur.Objects.Memory
