import Tests.Aiur
import Tests.FFIConsistency
import Tests.ByteArray
import Tests.Ix
import Tests.Ix.Ixon
import Tests.Ix.Compile
import Tests.Ix.Sharing
import Tests.Ix.CanonM
import Tests.Ix.FFI
import Tests.IxVM
import Tests.Keccak
import Tests.Cli
import Tests.ShardMap
import Ix.Common
import Ix.Meta

@[extern "rs_tmp_decode_const_map"]
opaque tmpDecodeConstMap : @& List (Lean.Name × Lean.ConstantInfo) → USize

def main (args: List String) : IO UInt32 := do
  if args.contains "rust-compile" then
    let env ← get_env!
    IO.println s!"Loaded environment with {env.constants.toList.length} constants"
    let result := tmpDecodeConstMap env.constants.toList
    IO.println s!"Rust compiled: {result}"
    return 0
  else if args.contains "compile" then LSpec.lspecEachIO Tests.Ix.Compile.suiteIO id
  else if args.contains "compile-env" then LSpec.lspecEachIO Tests.Ix.Compile.envSuiteIO id
  else if args.contains "compile-env-incr" then LSpec.lspecEachIO Tests.Ix.Compile.envIncrSuiteIO id
  else if args.contains "cli" then
    Tests.Cli.suite
  else if args.contains "shard-map" then
    LSpec.lspecEachIO Tests.ShardMap.suiteIO id
  else if args.contains "sharing" then
    -- Run both sync and async sharing tests
    let syncResult ← LSpec.lspecIO (.ofList [("sharing", Tests.Sharing.suite)]) []
    if syncResult != 0 then return syncResult
    LSpec.lspecEachIO Tests.Sharing.suiteIO id
  else if args.contains "compile-compare" then
    -- Run just the compilation comparison test
    LSpec.lspecEachIO [Tests.Sharing.testCompilationComparison] id
  else if args.contains "canon-env" then
    LSpec.lspecEachIO Tests.CanonM.suiteIO id
  else if args.contains "rust-canon" then
    LSpec.lspecEachIO Tests.CanonM.suiteRustCanonIO id
  else if args.contains "ffi" then
    -- Run property-based FFI roundtrip tests
    let propResult ← LSpec.lspecIO (.ofList [("ffi", Tests.FFI.suite)]) []
    if propResult != 0 then return propResult
    -- Run IO-based tests for edge cases
    LSpec.lspecEachIO Tests.FFI.suiteIO id
  else
    LSpec.lspecIO (.ofList [
       ("aiur", Tests.Aiur.suite),
       ("ffi-consistency", Tests.FFIConsistency.suite),
       ("ffi", Tests.FFI.suite),
       ("byte-array", Tests.ByteArray.suite),
       ("ix", Tests.Ix.suite),
       ("ixon-units", [Tests.Ixon.units]),
       ("ixon", Tests.Ixon.suite),
       ("sharing", Tests.Sharing.suite),
       ("canonm", [Tests.CanonM.suite]),
       ("ixvm", Tests.IxVM.suite),
       ("keccak", Tests.Keccak.suite),
    ]) args
