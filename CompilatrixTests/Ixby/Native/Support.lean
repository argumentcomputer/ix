import CompilatrixTests.Ixby.SourceRuntime
import Compilatrix.Ixby.Runtime.Native.Image

namespace CompilatrixTests.Ixby.Native

open Lean Compilatrix.Tools.Check Compilatrix.Ixby.LeanFrontend

def certify (image : Image) : IO Unit := do
  discard <| checked image.certifyRuntime
  if image.state.functionNames.contains `MultiStark.Verify.Codec.Wire.encode then
    discard <| checked image.certifyWireRuntime

def compileImage (env : Environment) (name : Name) (wire := false) : IO Image := do
  let (result, _) ← (compile name
    (setup := if wire then Compilatrix.Ixby.Runtime.buildWire else pure ())).toIO
    { fileName := "native runtime regression", fileMap := default,
      maxRecDepth := 16384, maxHeartbeats := 0 } { env }
  let image ← checked result
  certify image
  return image

def same [BEq α] [BEq β] : Except α β → Except α β → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

def natural (n : Nat) : Ix.Ixby.Value := .scalar (.nat n)
def word (w : UInt32) : Ix.Ixby.Value := .scalar (.word32 w)
def boolean (b : Bool) : Ix.Ixby.Value := .scalar (.bool b)

abbrev Check := Nat → Array Ix.Ixby.Value → Ix.Ixby.Value → IO Unit

def runProgram (limits : Ix.Ixby.Limits) (program : Ix.Ixby.Program)
    (args : Array Ix.Ixby.Value) (fuel : Nat := 200000) : Except Ix.Ixby.Error Ix.Ixby.Value :=
  Compilatrix.Ixby.Runtime.Chunked.execute limits program args fuel

def expect (image : Image) (id : Nat) (args : Array Ix.Ixby.Value)
    (result : Except Ix.Ixby.Error Ix.Ixby.Value) : IO Unit := do
  let program := { image.program with entry := id }
  let actual := runProgram image.state.limits program args
  let reference := Ix.Ixby.execute image.state.limits program args 200000
  need (same actual reference) s!"native helper {id}: chunked/reference disagreement"
  need (same actual result) s!"native helper {id}: expected {reprStr result}, got {reprStr actual}"

end CompilatrixTests.Ixby.Native
