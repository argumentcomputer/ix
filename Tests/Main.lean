import Tests.Aiur
import Tests.FFIConsistency
import Tests.ByteArray
import Tests.Ix
import Tests.Ix.Compile
import Tests.IxVM
import Tests.Keccak
import Tests.Cli

def main (args: List String) : IO UInt32 := do
  if args.contains "compile"
  then LSpec.lspecEachIO Tests.Ix.Compile.suiteIO id
  else if args.contains "cli" then
    Tests.Cli.suite
  else
    LSpec.lspecIO (.ofList [
      --("aiur", Tests.Aiur.suite),
      --("ffi-consistency", Tests.FFIConsistency.suite),
      --("byte-array", Tests.ByteArray.suite),
      --("ix", Tests.Ix.suite),
      --("ixvm", Tests.IxVM.suite),
      --("keccak", Tests.Keccak.suite),
    ]) args
