import CompilatrixTests.Ixby.Inline.Execution
import CompilatrixTests.Ixby.Inline.Checking
import CompilatrixTests.Ixby.Native.Support

namespace CompilatrixTests.Ixby.Inline

open Compilatrix.Ixby.Inline Compilatrix.Tools.Check

def run : IO Unit := do
  checking
  execution
  let count ← IO.mkRef 0
  discard <| SourceRuntime.run Native.certify fun image => do
    let wire := image.state.functionNames.contains `MultiStark.Verify.Codec.Wire.encode
    let selected ← checked (optimizeImage image { protectedPrefix := if wire then 112 else 97 })
    if let .optimized sites := selected.selected.status then count.modify (· + sites)
    for (slot, index) in selected.image.state.functions.zipIdx do
      need (slot.value == selected.image.program.functions[index]?) "selected builder body differs"
    return selected.image
  need ((← count.get) > 0) "typed source oracle corpus exercised no inline sites"
  IO.println s!"inline typed source oracles: {← count.get} sites; all runtime and wire certificates retained"

end CompilatrixTests.Ixby.Inline
