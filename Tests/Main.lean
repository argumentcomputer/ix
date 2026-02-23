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
import Ix.IxVM

@[extern "rs_tmp_decode_const_map"]
opaque tmpDecodeConstMap : @& List (Lean.Name × Lean.ConstantInfo) → USize

/-- Primary test suites - run by default -/
def primarySuites : Std.HashMap String (List LSpec.TestSeq) := .ofList [
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

/-- Ignored test runners - expensive, deferred IO actions run only when explicitly requested -/
def ignoredRunners : List (String × IO UInt32) := [
  ("aiur", do
    IO.println "aiur"
    match AiurTestEnv.build (pure toplevel) with
    | .error e => IO.eprintln s!"Aiur setup failed: {e}"; return 1
    | .ok env => LSpec.lspecEachIO aiurTestCases fun tc => pure (env.runTestCase tc)),
  ("aiur-hashes", do
    IO.println "aiur-hashes"
    let .ok blake3Env := AiurTestEnv.build (IxVM.byteStream.merge IxVM.blake3)
      | IO.eprintln "Blake3 setup failed"; return 1
    let r1 ← LSpec.lspecEachIO blake3TestCases fun tc => pure (blake3Env.runTestCase tc)
    let .ok sha256Env := AiurTestEnv.build (IxVM.byteStream.merge IxVM.sha256)
      | IO.eprintln "SHA256 setup failed"; return 1
    let r2 ← LSpec.lspecEachIO sha256TestCases fun tc => pure (sha256Env.runTestCase tc)
    return if r1 == 0 && r2 == 0 then 0 else 1),
  ("ixvm", do LSpec.lspecIO (.ofList [("ixvm", [mkAiurTests IxVM.ixVM []])]) []),
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

  -- Run primary tests
  let primaryResult ← LSpec.lspecIO primarySuites filterArgs
  if primaryResult != 0 then return primaryResult

  -- Run ignored tests only when --ignored is specified
  if runIgnored then
    let mut result ← LSpec.lspecIO ignoredSuites filterArgs
    let filtered := if filterArgs.isEmpty then ignoredRunners
      else ignoredRunners.filter fun (key, _) => filterArgs.any fun arg => key == arg
    for (_, action) in filtered do
      let r ← action
      if r != 0 then result := r
    return result
  else
    return 0
