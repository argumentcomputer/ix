import Compilatrix.IxIR2.WireCheck

/-! Bounded snapshot file ingress. Read at most the caller's cap plus one
byte, including if the file grows after it is opened. No file-size metadata
is trusted to authorize an unbounded payload read. -/

namespace Compilatrix.IxIR2.Wire

def readBounded (path : System.FilePath) (limit : Nat) : IO ByteArray :=
  IO.FS.withFile path .read fun handle => do
    let mut bytes := ByteArray.empty
    for _ in [:limit + 1] do
      let request := min 65536 (limit + 1 - bytes.size)
      let chunk ← handle.read request.toUSize
      if chunk.size == 0 then return bytes
      bytes := bytes ++ chunk
      if bytes.size > limit then throw (IO.userError "IxIR2 snapshot file exceeds the byte limit")
    throw (IO.userError "IxIR2 snapshot file exceeds the byte limit")

end Compilatrix.IxIR2.Wire
