module
import Tests.Ixby.Common
import Ix.Ixby.Aiur.Objects.Table
import Ix.Ixby.Aiur.Objects
import Ix.Aiur.Compiler

/-! Table/store conformance against the real compiled object parser and runner.
These tests do not build a new verifier or provide raw memory as production
advice. The pure bytecode evaluator exposes memory for inspection. -/

namespace Tests.Ixby.Aiur.Objects.Table

open Ix.Ixby Ix.Ixby.AiurBackend
open Ix.Ixby.AiurBackend.Objects.Memory Ix.Ixby.AiurBackend.Objects.Table
open Aiur.Bytecode.Eval

private def id (n : Nat) (member := 0) (tag := 0) : CtorId :=
  ⟨⟨n % (2 ^ 256), Nat.mod_lt _ (by decide)⟩, member, tag⟩
private def table : Array CtorDecl := #[⟨id 37 2 0, 0⟩, ⟨id 37 2 1, 2⟩]
private def word (n : Nat) : Value := .scalar (.word32 n.toUInt32)
private def pair : Value := .ctor table[1]!.id #[word 17, word 23]
private def identity (ctors := table) : Program := {
  constructors := ctors,
  functions := #[{ arity := 1, blocks := #[⟨1, .ret (.local 0)⟩] }] }
private def construct : Program := { constructors := table, functions := #[{
  arity := 2, blocks := #[⟨2, .letOp (.construct 1 [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }] }
private def caseFirst : Program := { constructors := table, functions := #[{
  arity := 1, blocks := #[⟨1, .caseCtor (.local 0) [⟨1, 1⟩]⟩,
    ⟨3, .ret (.local 1)⟩] }] }

private def idFlat (name : CtorId) : Array Aiur.G :=
  (Array.range 8).map (fun i => .ofNat ((name.block.val / limbBase ^ i) % limbBase)) ++
    #[.ofNat name.member, .ofNat name.tag]
private def consFlat (declaration : CtorDecl) (tail : Nat) : Array Aiur.G :=
  #[0] ++ idFlat declaration.id ++ #[.ofNat declaration.fields, .ofNat tail]
private def nilFlat : Array Aiur.G := Array.replicate tableWidth 1

private def storedTable (decls : Array CtorDecl) : EvalState × Nat :=
  decls.foldr (fun declaration state => memStore state.1 (consFlat declaration state.2))
    (memStore { ioBuffer := default } nilFlat)
private def replace (raw : RawMemory) (pointer : Nat) (flat : Array Aiur.G) : RawMemory :=
  fun width address => if width == tableWidth && address == pointer then some flat else raw width address
private def rawTable : RawMemory := bytecodeMemory (storedTable table).1
private def rejects (raw : RawMemory) (pointer := 2) (count := 2) : Bool :=
  (readTable raw pointer count).isNone

private def tableChecks : IO (List Check) := do
  return [
  ("tagless declaration layout and forward table order", readTable rawTable 2 2 == some table),
  ("empty table requires canonical Nil", readTable rawTable 0 0 == some #[]),
  ("missing empty table rejected", rejects (fun _ _ => none) 0 0),
  ("missing declaration cell", rejects rawTable 99),
  ("short table count", rejects rawTable 2 1),
  ("long table count", rejects rawTable 2 3),
  ("count over capacity rejected before traversal", rejects rawTable 2 17),
  ("huge count rejected before traversal", rejects rawTable 2 (2 ^ 32)),
  ("unknown declaration-list tag", rejects (replace rawTable 2 ((consFlat table[0]! 1).set! 0 2))),
  ("extra declaration tag is not accepted", rejects (replace rawTable 2 ((#[0] : Array Aiur.G) ++ consFlat table[0]! 1))),
  ("short declaration cell", rejects (replace rawTable 2 #[0, 0])),
  ("field capacity", rejects (replace rawTable 2 ((consFlat table[0]! 1).set! 11 17))),
  ("field count is not narrowed", rejects (replace rawTable 2 ((consFlat table[0]! 1).set! 11 (.ofNat (2 ^ 32))))),
  ("tail pointer is not narrowed", rejects (replace rawTable 1 ((consFlat table[1]! 0).set! 12 (.ofNat (2 ^ 32))))),
  ("cyclic declaration spine", rejects (replace rawTable 1 (consFlat table[1]! 2))),
  ("duplicate full semantic name", let state := storedTable #[table[0]!, table[0]!]
    rejects (bytecodeMemory state.1) state.2),
  ("duplicate name with different arity", let state := storedTable #[table[0]!, ⟨table[0]!.id, 2⟩]
    rejects (bytecodeMemory state.1) state.2),
  ("distinct arities do not alter distinct names", let decls := #[table[0]!, ⟨table[1]!.id, 16⟩]
    let state := storedTable decls; readTable (bytecodeMemory state.1) state.2 2 == some decls),
  ("full 256-bit digest and maximum member/tag", let decls := #[⟨id (2 ^ 256 - 1) (2 ^ 32 - 1) (2 ^ 32 - 1), 16⟩]
    let state := storedTable decls; readTable (bytecodeMemory state.1) state.2 1 == some decls),
  ("exact sixteen-declaration capacity", let decls := (Array.range 16).map fun n => ⟨id n, n⟩
    let state := storedTable decls; readTable (bytecodeMemory state.1) state.2 16 == some decls),
  ("unreachable malformed declarations allowed", readTable (replace rawTable 99 #[2]) 2 2 == some table),
  ("equal cells at different physical pointers", readTable (replace rawTable 99 (consFlat table[0]! 1)) 99 2 == some table),
  ("large canonical physical pointer", readTable
    (replace rawTable (2 ^ 32 + 2) (consFlat table[0]! 1)) (2 ^ 32 + 2) 2 == some table),
  ("matching program table", checkProgramTable rawTable 2 2 (identity)),
  ("reordered program table", !checkProgramTable rawTable 2 2 (identity table.reverse)),
  ("wrong table arity", !checkProgramTable rawTable 2 2 (identity (table.set! 0 ⟨table[0]!.id, 1⟩))),
  ("omitted unused declaration", !checkProgramTable rawTable 1 1 (identity))
] ++
  (List.range 10).map (fun limb => (s!"identity limb {limb} cannot exceed u32",
    rejects (replace rawTable 2 ((consFlat table[0]! 1).set! (limb + 1) (.ofNat (2 ^ 32)))))) ++
  (List.range 12).map (fun pad => (s!"table Nil padding {pad}",
    rejects (replace rawTable 0 (nilFlat.set! (pad + 1) 0)))) ++
  (List.range 10).map (fun limb => (s!"binding includes unused identity limb {limb}",
    !checkProgramTable (replace rawTable 2 ((consFlat table[0]! 1).set! (limb + 1) 255)) 2 2 (identity)))

private def compileFixture : IO (Except String Aiur.CompiledToplevel) := do
  return do
    let source ← objectsToplevel
    (source.prune [`is_read_ctors, `is_run]).compile |>.mapError toString

private def snapshot (compiled : Aiur.CompiledToplevel) (name : Lean.Name)
    (args : Array Aiur.G) (initial : EvalState) : Except String (Array Aiur.G × EvalState) := do
  let some index := compiled.getFuncIdx name | throw s!"missing function {name}"
  let some f := compiled.bytecode.functions[index]? | throw s!"missing function {index}"
  unless f.layout.inputSize == args.size do throw s!"arity mismatch in {name}"
  match evalBlock compiled.bytecode 4096 f.body { initial with map := args } with
  | .ok (flat, state) | .error (.earlyReturn flat state) => return (flat, state)
  | .error error => throw s!"{name}: {repr error}"

private def storeBytes (st : EvalState) (bytes : Codec.Bytes) : EvalState × Nat :=
  bytes.foldr (fun byte state => memStore state.1 #[0, .ofNat byte.toNat, .ofNat state.2])
    (memStore st #[1, 1, 1])
private def declarationBytes (decls : Array CtorDecl) : Except String Codec.Bytes :=
  Codec.Internal.encode 4096 0 (decls.forM fun decl => do
    Codec.Internal.writeCtorId decl.id
    Codec.Internal.writeU32 decl.fields) |>.mapError (fun error => s!"{repr error}")

private def parserChecks (compiled : Aiur.CompiledToplevel) : List (String × Bool) := Id.run do
  let mut checks := []
  let maximum := #[⟨id (2 ^ 256 - 1) (2 ^ 32 - 1) (2 ^ 32 - 1), 16⟩]
  for (label, decls) in [
      ("empty", #[]), ("asymmetric", table), ("reordered", table.reverse), ("maximum ID", maximum),
      ("sixteen declarations", (Array.range 16).map fun n => ⟨id n, n⟩)] do
    let result := do
      let bytes ← declarationBytes decls
      let (initial, pointer) := storeBytes { ioBuffer := default } bytes
      let (out, state) ← snapshot compiled `is_read_ctors #[.ofNat pointer, .ofNat decls.size] initial
      let decoded := readTable (bytecodeMemory state) (out.getD 0 0).n decls.size
      return decoded == some decls && (match memLoad state 3 (out.getD 1 0).n with
        | .ok tail => tail == #[1, 1, 1] | _ => false)
    checks := checks ++ [(s!"compiled parser {label}" ++
      (match result with | .error e => s!": {e}" | _ => ""),
      match result with | .ok ok => ok | .error _ => false)]
  for (label, decls) in [
      ("duplicate identity", #[table[0]!, table[0]!]),
      ("duplicate identity/different arity", #[table[0]!, ⟨table[0]!.id, 2⟩]),
      ("field count 17", #[⟨table[0]!.id, 17⟩])] do
    let result := do
      let bytes ← declarationBytes decls
      let (initial, pointer) := storeBytes { ioBuffer := default } bytes
      snapshot compiled `is_read_ctors #[.ofNat pointer, .ofNat decls.size] initial
    checks := checks ++ [("compiled parser rejects " ++ label,
      match result with | .error e => e == s!"is_read_ctors: {repr BytecodeError.assertFailed}" | _ => false)]
  return checks

private def executionChecks (compiled : Aiur.CompiledToplevel) : List (String × Bool) := Id.run do
  let mut checks := []
  let samples : List (String × Program × Array Value × Value × Nat) := [
    ("parsed input object", identity, #[pair], pair, 3),
    ("constructed runtime object", construct, #[word 17, word 23], pair, 3),
    ("case field transfer", caseFirst, #[pair], word 17, 1),
    ("erased input", identity, #[.erased], .erased, 1),
    ("empty constructor table", identity #[], #[word 7], word 7, 1)]
  for (label, program, input, expected, nodes) in samples do
    let result : Except String (List (String × Bool)) := do
      let code ← Codec.encodeProgram objectsProfile program |>.mapError (fun e => s!"{repr e}")
      let inputBytes ← Codec.encodeInput objectsProfile program input |>.mapError (fun e => s!"{repr e}")
      let (st, programPointer) := storeBytes { ioBuffer := default } code
      let (st, inputPointer) := storeBytes st inputBytes
      let (out, state) ← snapshot compiled `is_run #[.ofNat programPointer, .ofNat inputPointer] st
      let flat := out.extract 0 6
      let tablePointer := (out.getD 6 0).n
      let count := (out.getD 7 0).n
      let reconstructed := reconstructProgram (bytecodeMemory state) code tablePointer count flat nodes
      let expectedResult := some (program, expected, 0)
      let mut localChecks := [
        (label ++ " concrete program/table/value agreement", reconstructed == expectedResult),
        (label ++ " rejects changed artifact", (reconstructProgram (bytecodeMemory state)
          (code.push 0) tablePointer count flat nodes).isNone),
        (label ++ " preserves shared budget", (reconstructProgram (bytecodeMemory state)
          code tablePointer count flat (nodes - 1)).isNone)]
      -- A representation checker must not be described as execution verification:
      -- a different function body with the same table can represent the same value.
      let other : Program := { program with functions := #[{
        arity := input.size, blocks := #[⟨input.size, .ret (.literal (.word32 999))⟩] }] }
      let otherCode ← Codec.encodeProgram objectsProfile other |>.mapError (fun e => s!"{repr e}")
      localChecks := localChecks ++ [(label ++ " representation is not execution verification",
        reconstructProgram (bytecodeMemory state) otherCode tablePointer count flat nodes ==
          some (other, expected, 0))]
      if !program.constructors.isEmpty then
        let changed := { program with constructors := program.constructors.modify 0 fun decl =>
          { decl with id := { decl.id with member := decl.id.member + 1 } } }
        let changedCode ← Codec.encodeProgram objectsProfile changed |>.mapError (fun e => s!"{repr e}")
        localChecks := localChecks ++ [(label ++ " rejects mismatched table in valid program",
          (reconstructProgram (bytecodeMemory state) changedCode tablePointer count flat nodes).isNone)]
      for (storeLabel, stored) in [("zero width", #[]), ("scalar width", #[7]),
          ("object width", Array.replicate 8 2), ("declaration width", Array.replicate 13 2),
          ("existing Nil", nilFlat)] do
        let (next, pointer) := memStore state stored
        let (again, repeated) := memStore next stored
        let operation := Aiur.Bytecode.Eval.evalOp compiled.bytecode 64
          (.store (Array.range stored.size)) { state with map := stored }
        localChecks := localChecks ++ [
          (label ++ " store preservation: " ++ storeLabel,
            reconstructProgram (bytecodeMemory next) code tablePointer count flat nodes == expectedResult),
          (label ++ " content-dedup: " ++ storeLabel, pointer == repeated &&
            reconstructProgram (bytecodeMemory again) code tablePointer count flat nodes == expectedResult),
          (label ++ " store readback: " ++ storeLabel,
            match memLoad next stored.size pointer with | .ok found => found == stored | _ => false),
          (label ++ " actual Store instruction: " ++ storeLabel,
            match operation with
            | .ok next => reconstructProgram (bytecodeMemory next) code tablePointer count flat nodes == expectedResult
            | _ => false)]
      return localChecks
    match result with
    | .ok more => checks := checks ++ more
    | .error error => checks := checks ++ [(label ++ ": " ++ error, false)]
  return checks

public def suite : IO UInt32 := runChecks "ixby-objects-table" do
  match ← compileFixture with
  | .error error => return [(s!"compile fixtures: {error}", false)]
  | .ok compiled => return (← tableChecks) ++ parserChecks compiled ++ executionChecks compiled

end Tests.Ixby.Aiur.Objects.Table
