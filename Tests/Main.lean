import Tests.Aiur
import Tests.ByteArray
import Tests.Ix.Ixon
import Tests.Ix.IxonCorpus
import Tests.Ix.IxVM
import Tests.Ix.Claim
import Tests.Ix.Merkle
import Tests.Ix.AssumptionTree
import Tests.Ix.Commit
import Tests.Ix.Compile
import Tests.Ix.Compile.ValidateAux
import Tests.Ix.Decompile
import Tests.Ix.Kernel.BuildPrimitives
import Tests.Ix.Kernel.BuildPrimOrigs
import Tests.Ix.Kernel.CheckEnv
import Tests.Ix.Kernel.Roundtrip
import Tests.Ix.Kernel.RoundtripNoCompile
import Tests.Ix.Kernel.Tutorial
import Tests.Ix.Kernel.Arena
import Tests.Ix.RustSerialize
import Tests.Ix.RustDecompile
import Tests.Ix.Sharing
import Tests.Ix.Tc.Unit
import Tests.Ix.Tc.Substrate
import Tests.Ix.Tc.IxonFixtures
import Tests.Ix.Tc.WhnfTests
import Tests.Ix.Tc.InferDefEq
import Tests.Ix.Tc.CheckTests
import Tests.Ix.Tc.NodeAddr
import Tests.Ix.Tc.AnonDiff
import Tests.Ix.Tc.InitScale
import Tests.Ix.Tc.TutorialTc
import Tests.Ix.Tc.Roundtrip
import Tests.Ix.Tc.IngressMetaTests
import Tests.Ix.Tc.Pins
import Tests.Ix.CanonM
import Tests.Ix.GraphM
import Tests.Ix.CondenseM
import Tests.FFI
import Tests.Keccak
import Tests.MultiStark
import Tests.Cli
import Tests.ShardMap
import Tests.Ix.EnvBody
import Tests.Ix.Lean4Lean
import Ix.Common
import Ix.Meta
import Ix.IxVM

/-- Runs the full compile → serialize → decompile roundtrip over the given
    constants and returns the number of failures (0 = clean): decompile
    mismatches, or a non-zero constant count if a phase aborted. -/
@[extern "rs_tmp_decode_const_map"]
opaque tmpDecodeConstMap : @& List (Lean.Name × Lean.ConstantInfo) → USize

/-- Primary test suites - run by default -/
def primarySuites : Std.HashMap String (List LSpec.TestSeq) := .ofList [
  ("ffi", Tests.FFI.suite),
  ("byte-array", Tests.ByteArray.suite),
  ("ixon", Tests.Ixon.suite),
  ("claim", Tests.Claim.suite),
  ("merkle", Tests.Merkle.suite),
  ("assumption-tree", Tests.AssumptionTree.suite),
  ("commit", Tests.Commit.suite),
  ("canon", [Tests.CanonM.suite]),
  ("keccak", Tests.Keccak.suite),
  ("sharing", Tests.Sharing.suite),
  ("graph-unit", Tests.Ix.GraphM.suite),
  ("condense-unit", Tests.Ix.CondenseM.suite),
  ("aiur-cross", [AiurTests.Cross.tests]),
  ("tc-unit", Tests.Tc.Unit.suite ++ Tests.Tc.Substrate.suite
    ++ Tests.Tc.Fixtures.suite ++ Tests.Tc.WhnfTests.suite
    ++ Tests.Tc.InferDefEq.suite ++ Tests.Tc.CheckTests.suite
    ++ Tests.Tc.Roundtrip.unitTests ++ Tests.Tc.IngressMeta.unitTests),
]

/-- Ignored test suites - expensive, run only when explicitly requested. These require significant RAM -/
def ignoredSuites : Std.HashMap String (List LSpec.TestSeq) := .ofList [
  ("shard-map", Tests.ShardMap.suite),
  ("rust-canon-roundtrip", Tests.CanonM.rustSuiteIO),
  ("serial-canon-roundtrip", Tests.CanonM.serialSuiteIO),
  ("parallel-canon-roundtrip", Tests.CanonM.parallelSuiteIO),
  ("graph-cross", Tests.Ix.GraphM.suiteIO),
  ("condense-cross", Tests.Ix.CondenseM.suiteIO),
  -- Lean-side compilation/decompilation currently broken, disabled
  --("compile", Tests.Compile.compileSuiteIO),
  --("decompile", Tests.Decompile.decompileSuiteIO),
  ("rust-serialize", Tests.RustSerialize.rustSerializeSuiteIO),
  ("ixon-corpus", Tests.Ixon.Corpus.suite),
  ("rust-decompile", Tests.RustDecompile.rustDecompileSuiteIO),
  ("commit-io", Tests.Commit.suiteIO),
  ("kernel-ixon-roundtrip", Tests.Ix.Kernel.Roundtrip.suite),
  --("kernel-lean-roundtrip", Tests.Ix.Kernel.RoundtripNoCompile.suite),
  ("kernel-tutorial", Tests.Ix.Kernel.Tutorial.suite),
  ("kernel-check-env", Tests.Ix.Kernel.CheckEnv.suite),
  ("kernel-check-const", Tests.Ix.Kernel.CheckEnv.constSuite),
  ("rust-kernel-build-primitives", Tests.Ix.Kernel.BuildPrimitives.suite),
  ("rust-kernel-build-prim-origs", Tests.Ix.Kernel.BuildPrimOrigs.suite),
  ("tc-node-addr", Tests.Tc.NodeAddr.suite),
  ("tc-anon-diff", Tests.Tc.AnonDiff.suite),
  ("tc-init", Tests.Tc.InitScale.suite),
  ("tc-tutorial", Tests.Tc.TutorialTc.suite),
  ("tc-roundtrip", Tests.Tc.Roundtrip.suite),
  ("tc-ingress-meta", Tests.Tc.IngressMeta.suite),
]

/-- Ignored test runners - expensive, deferred IO actions run only when explicitly requested -/
def ignoredRunners (env : Lean.Environment) : List (String × IO UInt32) := [
  ("aiur", do
    IO.println "aiur"
    match AiurTestEnv.build (pure toplevel) with
    | .error e => IO.eprintln s!"Aiur setup failed: {e}"; return 1
    | .ok env => LSpec.lspecEachIO aiurTestCases fun tc => pure (env.runTestCase tc)),
  ("aiur-hashes", do
    IO.println "aiur-hashes"
    let .ok blake3Env := AiurTestEnv.build (do
        let t ← IxVM.core.merge IxVM.byteStream; t.merge IxVM.blake3)
      | IO.eprintln "Blake3 setup failed"; return 1
    let r1 ← LSpec.lspecEachIO blake3TestCases fun tc => pure (blake3Env.runTestCase tc)
    let .ok sha256Env := AiurTestEnv.build (do
        let t ← IxVM.core.merge IxVM.byteStream; t.merge IxVM.sha256)
      | IO.eprintln "SHA256 setup failed"; return 1
    let r2 ← LSpec.lspecEachIO sha256TestCases fun tc => pure (sha256Env.runTestCase tc)
    return if r1 == 0 && r2 == 0 then 0 else 1),
  ("ixvm", do
    let kernelUnitTests := .exec `kernel_unit_tests
    let serdeNatAddCommTest ← serdeNatAddComm env
    let kernelChecks ← kernelChecks env
    let claimSmokes ← claimSmokeTests env
    let parityCases ← parityCases env
    -- Test-only entrypoints (`kernel_unit_tests`, `ixon_serde_test`) exist
    -- only in the FULL toplevel; everything codegen-coupled (kernel checks,
    -- claim smokes, arena, parity) runs on the pruned production toplevel —
    -- the one `ix codegen` mirrors.
    match AiurTestEnv.build IxVM.ixVM, AiurTestEnv.build IxVM.ixVMFull with
    | .error e, _ | _, .error e => IO.eprintln s!"IxVM env build failed: {e}"; return 1
    | .ok aiurEnv, .ok fullEnv =>
      let arenaSeq ← Tests.Ix.Kernel.Arena.arenaTests env aiurEnv.compiled
      let fullSeq := [kernelUnitTests, serdeNatAddCommTest].foldl (init := .done)
        fun s tc => s ++ fullEnv.runTestCase tc
      let aiurSeq := (kernelChecks ++ claimSmokes).foldl (init := .done) fun s tc =>
        s ++ aiurEnv.runTestCase tc
      let paritySeq := parityCases.foldl (init := .done) fun s tc =>
        s ++ runParityCase aiurEnv.compiled tc
      LSpec.lspecIO (.ofList [("ixvm", [fullSeq, aiurSeq, arenaSeq, paritySeq])]) []),
  ("rbtree-map", do
    IO.println "rbtree-map"
    match AiurTestEnv.build (pure IxVM.rbTreeMap) with
    | .error e => IO.eprintln s!"RBTreeMap setup failed: {e}"; return 1
    | .ok env => LSpec.lspecEachIO rbTreeMapTestCases fun tc => pure (env.runTestCase tc)),
  -- Multi-STARK recursive verifier (formerly the `recursive-verifier` executable):
  -- `multi-stark` runs the cheap primitive self-tests, `recursive-verifier` runs the
  -- ~1.5 min factorial-prove → recursive-verify → reject-tampering pipeline.
  ("multi-stark", Tests.MultiStark.selfTestSuite),
  ("recursive-verifier", Tests.MultiStark.endToEndSuite),
  ("validate-aux", runCompileValidateAux env),
  -- lean4lean dependency smoke: accept a real closure, reject an
  -- ill-typed decl (see Tests.Ix.Lean4Lean).
  ("lean4lean", Tests.Ix.Lean4Lean.run env),
  -- Pure-Lean kernel regression pins against a real .ixe (needs
  -- IX_PINS_IXE; skips cleanly otherwise — see Tests.Tc.Pins).
  ("tc-pins", Tests.Tc.Pins.run),
]

def main (args : List String) : IO UInt32 := do
  -- Special case: rust-compile diagnostic (full env)
  if args.contains "rust-compile" then
    let env ← get_env!
    IO.println s!"Loaded environment with {env.constants.toList.length} constants"
    let failures := tmpDecodeConstMap env.constants.toList
    if failures != 0 then
      IO.eprintln s!"[rust-compile] FAILED: {failures} compile/decompile roundtrip failure(s)"
      return 1
    IO.println "[rust-compile] OK: compile → decompile roundtrip clean"
    return 0

  -- Special case: cli tests have their own runner
  if args.contains "cli" then
    return ← Tests.Cli.suite

  let runIgnored := args.contains "--ignored"
  let includeIgnored := args.contains "--include-ignored"
  let filterArgs := args.filter fun a => a != "--ignored" && a != "--include-ignored"

  -- Run primary tests unless --ignored (without --include-ignored) is specified
  if !runIgnored || includeIgnored then
    let primaryArgs := if runIgnored || includeIgnored then [] else filterArgs
    let primaryResult ← LSpec.lspecIO primarySuites primaryArgs
    if primaryResult != 0 then return primaryResult
    -- getFileEnv body-inclusion regression guard (IO: loads a fixture file)
    let envBodySeq ← Tests.Ix.EnvBody.suite
    let envBodyResult ← LSpec.lspecIO (.ofList [("getfileenv-body", [envBodySeq])]) primaryArgs
    if envBodyResult != 0 then return envBodyResult

  -- Run ignored tests when --ignored or --include-ignored is specified
  if runIgnored || includeIgnored then
    let mut result ← LSpec.lspecIO ignoredSuites filterArgs
    let env ← get_env!
    let ignored := ignoredRunners env
    let filtered := if filterArgs.isEmpty then ignored
      else filterArgs.filterMap fun arg => ignored.find? fun (key, _) => key == arg
    for (_, action) in filtered do
      let r ← action
      if r != 0 then result := r
    return result
  else
    return 0
