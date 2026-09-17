import CompilatrixTests.Ixby.Native.Certificates
import CompilatrixTests.Ixby.Native.ScalarCases
import CompilatrixTests.Ixby.Native.WordCases
import CompilatrixTests.Ixby.Native.ArrayCases
import CompilatrixTests.Ixby.Native.ArrayReadCases
import CompilatrixTests.Ixby.Native.WireCases
import CompilatrixTests.Ixby.Native.Resources
import CompilatrixTests.Ixby.Native.Fuel

namespace CompilatrixTests.Ixby.Native

open Lean Ix.Ixby Compilatrix.Tools.Check Compilatrix.Ixby.LeanFrontend

private def callers (image : Image)
    (cases : Std.HashMap Nat (Array Value × Value)) : IO Nat := do
  let id : CtorId := { block := 2 }
  let sentinel := word 0xc0ffee
  for (callee, (args, expected)) in cases do
    let entry := image.program.functions.size
    let constructor := image.program.constructors.size
    let arity := args.size
    let wrapper : Function := { arity, blocks := #[
      ⟨arity, .letOp (.call callee ((List.range arity).map Operand.local)) 1⟩,
      ⟨arity + 1, .letOp (.construct constructor
        ((List.range arity).map Operand.local ++ [.literal (.word32 0xc0ffee), .local arity])) 2⟩,
      ⟨arity + 2, .ret (.local (arity + 1))⟩] }
    let program : Program := { image.program with
      entry := entry
      functions := image.program.functions.push wrapper
      constructors := image.program.constructors.push ⟨id, arity + 2⟩ }
    let changed := { image with program }
    certify changed
    expect changed entry args (.ok (.ctor id (args.push sentinel |>.push expected)))
  IO.println s!"native callers: {cases.size} helpers preserved all inputs, a sentinel and the result"
  return cases.size

def run : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Compilatrix.Ixby.Runtime.Examples }] {}
  let image ← compileImage env `Compilatrix.Ixby.Runtime.Examples.wireWriter true
  discard <| certificateMutations image
  let count ← IO.mkRef 0
  let cases ← IO.mkRef ({} : Std.HashMap Nat (Array Value × Value))
  let check : Check := fun id args expected => do
    expect image id args (.ok expected)
    count.modify (· + 1)
    cases.modify (·.insert id (args, expected))
  scalarCases check
  wordCases check
  let rejected ← arrayCases image check
  wireCases image check
  IO.println s!"native helper contracts: {← count.get} source-oracle executions; {rejected} checked bounds rejections"
  discard <| callers image (← cases.get)
  discard <| resourceCases image
  discard <| fuelCases image
  arrayReadCases image
  discard <| SourceRuntime.run certify

end CompilatrixTests.Ixby.Native
