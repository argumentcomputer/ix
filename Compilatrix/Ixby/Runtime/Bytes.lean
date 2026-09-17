import Compilatrix.Ixby.Runtime.Number

/-! Byte accumulation uses immutable native builders. Helpers return frozen
Bytes, so internal builder values never become source-level array values. -/

namespace Compilatrix.Ixby.Runtime

open Lean Ix.Ixby

def buildByteBuffers : BuildM Unit := do
  discard <| defineFunction `Ixby.Runtime.appendBytes 2 do
    let builder ← primitive .byteBuilderEmpty []
    let builder ← primitive .byteBuilderAppend [builder, .local 0]
    let builder ← primitive .byteBuilderAppend [builder, .local 1]
    ret (← primitive .byteBuilderFreeze [builder])

end Compilatrix.Ixby.Runtime
