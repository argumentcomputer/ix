import CompilatrixTests.Ixby.Native.Support
import Compilatrix.Ixby.Binary

namespace CompilatrixTests.Ixby.Native

open Lean Ix.Ixby Compilatrix.Tools.Check Compilatrix.Ixby.LeanFrontend
open Compilatrix.Ixby.Runtime.Native

private def changeFunction (image : Image) (id : Nat) (f : Function → Function) : Image :=
  { image with program := { image.program with functions := image.program.functions.modify id f } }

def certificateMutations (image : Image) : IO Nat := do
  discard <| checked image.certifyWireRuntime
  discard <| checked (validateProgram image.state.limits image.program |>.mapError reprStr)
  let rejected ← IO.mkRef 0
  let admitted ← IO.mkRef 0
  let reject (changed : Image) (label : String) (wellFormed := false) : IO Unit := do
    if wellFormed then
      discard <| checked (validateProgram changed.state.limits changed.program |>.mapError reprStr)
      admitted.modify (· + 1)
    match changed.certifyWireRuntime with
    | .ok _ => throw (IO.userError s!"native certificate accepted {label}")
    | .error _ => rejected.modify (· + 1)
  for entry in Code.entries ++ Code.wireEntries do
    let change := changeFunction image entry.id
    reject (change fun fn => { fn with arity := fn.arity + 1 }) s!"arity {entry.name}"
    reject (change fun fn => { fn with entry := fn.blocks.size }) s!"entry {entry.name}"
    reject (change fun fn => { fn with blocks := fn.blocks.push ⟨0, .ret .erased⟩ })
      s!"unreachable block {entry.name}" true
    let wrongName := image.state.functionNames.insert entry.name (entry.id + 1)
    reject { image with state := { image.state with functionNames := wrongName } }
      s!"name binding {entry.name}" true
    let wrongSlot := image.state.functions.modify entry.id fun fn => { fn with name := `WrongRuntimeBinding }
    reject { image with state := { image.state with functions := wrongSlot } }
      s!"slot binding {entry.name}" true
    for (block, index) in entry.body.blocks.zipIdx do
      reject (change fun fn => { fn with blocks := fn.blocks.modify index fun old =>
        { old with locals := old.locals + 1 } }) s!"locals {entry.name}/{index}"
      let replacement : Instr := if block.instruction == .ret .erased then
        .ret (.literal (.word32 17)) else .ret .erased
      reject (change fun fn => { fn with blocks := fn.blocks.modify index fun old =>
        { old with instruction := replacement } }) s!"instruction {entry.name}/{index}" true
      if let .letOp (.primitive primitive operands) target := block.instruction then
        let some alternate := Compilatrix.Ixby.Binary.primitives.find?
          (fun candidate => candidate != primitive && candidate.arity == primitive.arity) |
          throw (IO.userError "no alternate primitive for mutation")
        reject (change fun fn => { fn with blocks := fn.blocks.modify index fun old =>
          { old with instruction := .letOp (.primitive alternate operands) target } })
          s!"primitive {entry.name}/{index}" true
        if !operands.isEmpty then
          let replacement : Operand :=
            if operands.head! == .erased then .literal (.bool false) else .erased
          reject (change fun fn => { fn with blocks := fn.blocks.modify index fun old =>
            { old with instruction := .letOp (.primitive primitive
                (replacement :: operands.tail)) target } }) s!"operand {entry.name}/{index}" true
  for ((name, _), index) in wireConstructors.zipIdx do
    let change (f : CtorDecl → CtorDecl) : Image :=
      { image with program := { image.program with constructors := image.program.constructors.modify index f } }
    reject (change fun decl => { decl with fields := decl.fields + 1 }) s!"constructor arity {name}"
    reject (change fun decl => { decl with id := { decl.id with block := 2 } }) s!"constructor block {name}"
    reject (change fun decl => { decl with id := { decl.id with member := 1 } }) s!"constructor member {name}"
    reject (change fun decl => { decl with id := { decl.id with tag := 500 } }) s!"constructor tag {name}"
    let names := image.state.constructorNames.insert name (index + 1)
    reject { image with state := { image.state with constructorNames := names } }
      s!"constructor name {name}" true
  let names := image.state.functionNames.insert `MultiStark.Verify.Codec.Wire.readBytes 0
  reject { image with state := { image.state with functionNames := names } } "source reader binding" true
  -- The frontend proof boundary remains explicit: an arbitrary source LCNF
  -- body is not certified by this native helper checker.
  let sourceChanged := changeFunction image 97 fun fn =>
    { fn with blocks := fn.blocks.modify 0 fun block => { block with instruction := .ret .erased } }
  discard <| checked sourceChanged.certifyWireRuntime
  IO.println s!"native certificates: 109 complete helper bodies; {← rejected.get} mutations rejected ({← admitted.get} structurally admitted); source-body boundary checked"
  return ← rejected.get

end CompilatrixTests.Ixby.Native
