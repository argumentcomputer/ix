import Tests.Aiur2
import Tests.Archon
import Tests.FFIConsistency
import Tests.ByteArray
import Tests.Unsigned
import Tests.Ix
import Tests.Ix.Compile
import Tests.Keccak
import Tests.Cli
import Tests.Blake3

def main (args: List String) : IO UInt32 := do
  if args.contains "compile"
  then LSpec.lspecEachIO Tests.Ix.Compile.suiteIO id
  else if args.contains "cli" then
    Tests.Cli.suite
  else
    LSpec.lspecIO (.ofList [
      ("aiur", Tests.Aiur.suite),
      ("archon", Tests.Archon.suite),
      ("ffi-consistency", Tests.FFIConsistency.suite),
      ("byte-array", Tests.ByteArray.suite),
      ("unsigned", Tests.Unsigned.suite),
      ("ix", Tests.Ix.suite),
      ("keccak", Tests.Keccak.suite),
      ("blake3", Tests.Blake3.suite),
    ]) args
