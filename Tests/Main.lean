import Tests.Aiur
import Tests.ByteArray
import Tests.Ix.Ixon
import Tests.Ix.Claim
import Tests.Ix.Commit
import Tests.Ix.Compile
import Tests.Ix.Decompile
import Tests.Ix.RustSerialize
import Tests.Ix.RustDecompile
import Tests.Ix.Sharing
import Tests.Ix.CanonM
import Tests.Ix.GraphM
import Tests.Ix.CondenseM
import Tests.FFI
import Tests.Keccak
import Tests.Cli
import Tests.ShardMap
import Ix.Common
import Ix.Meta

@[extern "rs_tmp_decode_const_map"]
opaque tmpDecodeConstMap : @& List (Lean.Name × Lean.ConstantInfo) → USize

/-- Primary test suites - run by default -/
def primarySuites : Std.HashMap String (List LSpec.TestSeq) := .ofList [
  ("aiur", Tests.Aiur.suite),
  ("ffi", Tests.FFI.suite),
  ("byte-array", Tests.ByteArray.suite),
  ("ixon", Tests.Ixon.suite),
  ("claim", Tests.Claim.suite),
  ("commit", Tests.Commit.suite),
  ("canon", [Tests.CanonM.suite]),
  ("keccak", Tests.Keccak.suite),
  ("sharing", Tests.Sharing.suite),
  ("graph-unit", Tests.Ix.GraphM.suite),
  ("condense-unit", Tests.Ix.CondenseM.suite),
]

/-- Ignored test suites - expensive, run only when explicitly requested. These require significant RAM -/
def ignoredSuites : Std.HashMap String (List LSpec.TestSeq) := .ofList [
  ("shard-map", Tests.ShardMap.suite),
  ("rust-canon-roundtrip", Tests.CanonM.rustSuiteIO),
  ("serial-canon-roundtrip", Tests.CanonM.serialSuiteIO),
  ("parallel-canon-roundtrip", Tests.CanonM.parallelSuiteIO),
  ("graph-cross", Tests.Ix.GraphM.suiteIO),
  ("condense-cross", Tests.Ix.CondenseM.suiteIO),
  ("compile", Tests.Compile.compileSuiteIO),
  ("decompile", Tests.Decompile.decompileSuiteIO),
  ("rust-serialize", Tests.RustSerialize.rustSerializeSuiteIO),
  ("rust-decompile", Tests.RustDecompile.rustDecompileSuiteIO),
  ("commit-io", Tests.Commit.suiteIO),
]

def main (args : List String) : IO UInt32 := do
  -- Special case: rust-compile diagnostic
  if args.contains "rust-compile" then
    let env ← get_env!
    IO.println s!"Loaded environment with {env.constants.toList.length} constants"
    let result := tmpDecodeConstMap env.constants.toList
    IO.println s!"Rust compiled: {result}"
    return 0

  -- Special case: cli tests have their own runner
  if args.contains "cli" then
    return ← Tests.Cli.suite

  let runIgnored := args.contains "--ignored"
  let filterArgs := args.filter (· != "--ignored")

  -- Check if any filterArg matches an ignored suite
  let ignoredRequested := filterArgs.any (ignoredSuites.contains ·)

  -- Run primary tests
  let primaryResult ← LSpec.lspecIO primarySuites filterArgs
  if primaryResult != 0 then return primaryResult

  -- Run ignored tests if --ignored flag or specific ignored suite requested
  if runIgnored || ignoredRequested then
    LSpec.lspecIO ignoredSuites filterArgs
  else
    return 0
