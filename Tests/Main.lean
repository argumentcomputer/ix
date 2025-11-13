import Tests.Aiur
import Tests.FFIConsistency
import Tests.ByteArray
import Tests.Ix
import Tests.Ix.Ixon
import Tests.Ix.Compile
import Tests.IxVM
import Tests.Keccak
import Tests.Cli

@[extern "rs_tmp_decode_const_map"]
opaque tmpDecodeConstMap : @& List (Lean.Name × Lean.ConstantInfo) → USize

def main (args: List String) : IO UInt32 := do
  if args.contains "rust-compile" then
    let env ← get_env!
    println! tmpDecodeConstMap env.constants.toList
    return 0
  else if args.contains "compile" then LSpec.lspecEachIO Tests.Ix.Compile.suiteIO id
  else if args.contains "cli" then
    Tests.Cli.suite
  else
    LSpec.lspecIO (.ofList [
       ("aiur", Tests.Aiur.suite),
       ("ffi-consistency", Tests.FFIConsistency.suite),
       ("byte-array", Tests.ByteArray.suite),
       ("ix", Tests.Ix.suite),
       --("ixon-units", Tests.Ixon.units),
       ("ixon", Tests.Ixon.suite),
       ("ixvm", Tests.IxVM.suite),
       ("keccak", Tests.Keccak.suite),
    ]) args
