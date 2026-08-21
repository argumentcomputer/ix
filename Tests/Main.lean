import Tests.Aiur
import Tests.Ix.Ixon
import Tests.Ix.IxonCorpus
import Tests.Ix.IxonSyntax
import Tests.Ix.IxVM
import Tests.Ix.IxVM.Exploits
import Tests.Ix.Claim
import Tests.Ix.Merkle
import Tests.Ix.AssumptionTree
import Tests.Ix.Commit
import Tests.Ix.Compile
import Tests.Ix.Compile.ValidateAux
import Tests.Ix.Compile.AuxGenDiff
import Tests.Ix.Compile.DecompileDiff
import Tests.Ix.AuxGen.ExprUtilsTests
import Tests.Ix.AuxGen.LevelsTests
import Tests.Ix.AuxGen.RecursorTests
import Tests.Ix.AuxGen.SurgeryTests
import Tests.Ix.GroundTests
import Tests.Ix.Decompile
import Tests.Ix.Kernel.BuildPrimitives
import Tests.Ix.Kernel.BuildPrimOrigs
import Tests.Ix.Kernel.CheckEnv
import Tests.Ix.Kernel.Roundtrip
import Tests.Ix.Kernel.RoundtripNoCompile
import Tests.Ix.Kernel.Tutorial
import Tests.Ix.Kernel.Arena
import Tests.Ix.Kernel.PrimAddrs
import Tests.Ix.RustSerialize
import Tests.Ix.RustDecompile
import Tests.Ix.Sharing
import Tests.Ix.BenchMeasures
import Tests.Ix.Tc.Unit
import Tests.Ix.Tc.Substrate
import Tests.Ix.Tc.IxonFixtures
import Tests.Ix.Tc.WhnfTests
import Tests.Ix.Tc.InferDefEq
import Tests.Ix.Tc.CheckTests
import Tests.Ix.Tc.AnonDiff
import Tests.Ix.Tc.InitScale
import Tests.Ix.Tc.TutorialTc
import Tests.Ix.Tc.Roundtrip
import Tests.Ix.Tc.IngressMetaTests
import Tests.Ix.Tc.Pins
import Tests.Ix.Tc.AccelDiff
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
import Tests.Ix.MetaEnv
import Tests.Ix.Catalog
import Tests.Ix.ImportIxe
import Tests.Ix.CatalogFixtures
import Tests.Ix.CatalogQualified
import Tests.Ix.CatalogSpine
import Tests.Ix.TruthMinesRecords
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
  ("meta-env", Tests.Ix.MetaEnv.suite),
  ("catalog", Tests.Ix.Catalog.suite),
  ("import-ixe", Tests.Ix.ImportIxe.suite),
  ("catalog-qualified", Tests.Ix.CatalogQualified.suite),
  ("truthmines-spec", Tests.Ix.TruthMinesRecords.suite),
  ("ixon", Tests.Ixon.suite),
  ("ixon-syntax", Tests.IxonSyntax.suite),
  ("claim", Tests.Claim.suite),
  ("merkle", Tests.Merkle.suite),
  ("assumption-tree", Tests.AssumptionTree.suite),
  ("commit", Tests.Commit.suite),
  ("canon", [Tests.CanonM.suite]),
  ("keccak", Tests.Keccak.suite),
  ("sharing", Tests.Sharing.suite),
  ("graph-unit", Tests.Ix.GraphM.suite),
  ("condense-unit", Tests.Ix.CondenseM.suite),
  ("bench-measures", Tests.Ix.BenchMeasures.suite),
  ("aux-gen-unit", Tests.AuxGen.ExprUtils.suite ++ Tests.AuxGen.Levels.suite ++ Tests.AuxGen.Recursor.suite ++ Tests.AuxGen.Surgery.suite),
  ("ground-unit", Tests.Ground.suite),
  ("aiur-cross", [AiurTests.Cross.tests]),
  ("aiur-cost", [AiurTests.Cost.tests]),
  ("prim-addrs", Tests.Ix.Kernel.PrimAddrs.suite),
  ("primitive-address-parity", Tests.Ix.Kernel.BuildPrimitives.paritySuite
    ++ Tests.Ix.Kernel.BuildPrimOrigs.paritySuite),
  ("decompile-unit", Tests.Decompile.unitSuite),
  ("tc-unit", Tests.Tc.Unit.suite ++ Tests.Tc.Substrate.suite
    ++ Tests.Tc.Fixtures.suite ++ Tests.Tc.WhnfTests.suite
    ++ Tests.Tc.InferDefEq.suite ++ Tests.Tc.CheckTests.suite
    ++ Tests.Tc.Roundtrip.unitTests ++ Tests.Tc.IngressMeta.unitTests),
]

/-- Ignored test suites - expensive, run only when explicitly requested. These require significant RAM -/
def ignoredSuites : Std.HashMap String (List LSpec.TestSeq) := .ofList [
  ("shard-map", Tests.ShardMap.suite),
  ("catalog-fixtures", Tests.Ix.CatalogFixtures.suite),
  ("catalog-spine", Tests.Ix.CatalogSpine.suite),
  ("rust-canon-roundtrip", Tests.CanonM.rustSuiteIO),
  ("serial-canon-roundtrip", Tests.CanonM.serialSuiteIO),
  ("parallel-canon-roundtrip", Tests.CanonM.parallelSuiteIO),
  ("graph-cross", Tests.Ix.GraphM.suiteIO),
  ("condense-cross", Tests.Ix.CondenseM.suiteIO),
  -- Lean-side decompilation not yet revived, disabled
  ("compile", Tests.Compile.compileSuiteIO),
  ("decompile", Tests.Decompile.decompileSuiteIO),
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
  ("tc-anon-diff", Tests.Tc.AnonDiff.suite),
  ("tc-init", Tests.Tc.InitScale.suite),
  ("tc-tutorial", Tests.Tc.TutorialTc.suite),
  ("tc-roundtrip", Tests.Tc.Roundtrip.suite),
  ("tc-ingress-meta", Tests.Tc.IngressMeta.suite),
]

/-- Primary test runners — quick suites run by default alongside
`primarySuites`, but kept as deferred `IO` actions (not `TestSeq`
values) so their setup — Aiur system builds, STARK proofs — does not
execute at module initialization for unrelated invocations. All are
seconds-scale (measured 2026-08-05: aiur-prove ~11s, the rest 2-4s
each). -/
def primaryRunners : List (String × IO UInt32) := [
  ("aiur-prove", do
    IO.println "aiur-prove"
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
  ("rbtree-map", do
    IO.println "rbtree-map"
    match AiurTestEnv.build (pure IxVM.rbTreeMap) with
    | .error e => IO.eprintln s!"RBTreeMap setup failed: {e}"; return 1
    | .ok env => LSpec.lspecEachIO rbTreeMapTestCases fun tc => pure (env.runTestCase tc)),
  -- Multi-STARK recursive verifier: `multi-stark` runs the verifier's
  -- primitive self-tests, `recursive-verifier` the full
  -- factorial-prove → recursive-verify → reject-tampering pipeline.
  ("multi-stark", Tests.MultiStark.selfTestSuite),
  ("recursive-verifier", Tests.MultiStark.endToEndSuite),
]

/-- Ignored test runners - expensive, deferred IO actions run only when explicitly requested -/
def ignoredRunners (env : Lean.Environment) : List (String × IO UInt32) := [
  ("ixvm", do
    let kernelChecks ← kernelChecks env
    -- the kernel CheckEnv smokes .
    let claimEnv ← IxVM.ClaimHarness.loadIxonEnv ``Nat.add_comm env
    let envFull ← claimCheckEnvFull claimEnv
    let envFrontier ← claimCheckEnvFrontier claimEnv
    let checkAsm ← claimCheckWithAsm claimEnv
    let revealFields ← claimRevealDefnFields claimEnv
    let revealExpr ← claimRevealDefnExpr claimEnv
    let revealCPrj ← claimRevealCPrj claimEnv
    let containsTc ← claimContains
    -- Shared-infrastructure test entrypoints live only in the FULL
    -- toplevel (pruning drops them so test-only circuits never widen a
    -- committed kernel system).
    let kernelUnitTests := .exec `kernel_unit_tests
    let serdeTest ← serdeNatAddComm env
    match AiurTestEnv.build IxVM.ixVM, AiurTestEnv.build IxVM.ixVMFull with
    | .error e, _ | _, .error e =>
      IO.eprintln s!"IxVM env build failed: {e}"; return 1
    | .ok v2Env, .ok v2FullEnv =>
      -- Kernel-arena fixtures: the repo's NEGATIVE corpus (every
      -- `bad_*` must be rejected by an in-kernel assert_eq!). Runs
      -- through the kernel's subject-only `verify_const` debug
      -- entrypoint, which lives only in the FULL toplevel — the
      -- production one carries `verify_claim` alone.
      let arenaSeq ← Tests.Ix.Kernel.Arena.arenaTests env v2FullEnv.compiled
      -- Adversarial Ixon: exploit attempts authored as raw Ixon
      -- constants, below the layer the arena's Lean fixtures can
      -- reach. Each case pins the kernel's verdict, which is REJECT
      -- except where accepting is the specified claim semantics.
      let exploitSeq ← Tests.Ix.IxVM.Exploits.exploitTests env v2Env.compiled
      let aiurSeq := (kernelChecks ++
          [envFull, envFrontier, checkAsm,
           revealFields, revealExpr, revealCPrj, containsTc]).foldl
        (init := .done) fun s tc => s ++ v2Env.runTestCase tc
      -- Codegen parity gate: the generated Rust kernel is emitted from
      -- the toplevel, so this runs the same witnesses through both
      -- engines and asserts they agree. It is only meaningful against a
      -- CURRENT `ix codegen` output — regenerate after any Aiur edit, or
      -- this gate compares against a stale kernel. Reuses the
      -- `kernelChecks` cases (`runParityCase` ignores the FFT pins), so
      -- the per-constant witness setup runs once, not twice.
      let paritySeq := kernelChecks.foldl (init := .done) fun s tc =>
        s ++ runParityCase v2Env.compiled tc
      let fullSeq := [kernelUnitTests, serdeTest].foldl (init := .done)
        fun s tc => s ++ v2FullEnv.runTestCase tc
      -- Shard pipeline: witness built in Rust (thin-frontier claim,
      -- parallel closure walk) and run on the native kernel. Pinned FFT
      -- is the regression signal.
      let shardSeq ← match (← shardCheckEnvCase env) with
        -- Only reachable when the target constant is absent from this
        -- toolchain; a fixture that no longer selects any owned
        -- constants throws instead of skipping.
        | none => pure (LSpec.test "shard pipeline: SKIP (target absent)" true)
        | some (handle, ownedBlob) =>
          let funIdx := v2Env.compiled.getFuncIdx `verify_claim |>.get!
          match v2Env.compiled.bytecode.shardCheckWithEnv
                  funIdx handle ownedBlob false with
          | .error e =>
            pure (LSpec.test s!"shard pipeline execution: {e}" false)
          | .ok (_, _, qc) =>
            -- Exact pin, same convention as `kernelCheckEntries`
            -- (`.round.toUInt64.toNat`): any cost shift must be an
            -- explicit, reviewed bump.
            let actual :=
              (Aiur.computeStats v2Env.compiled qc v2Env.shapes).totalFftCost.round.toUInt64.toNat
            pure (LSpec.test
              s!"Shard pipeline FFT matches: expected 6_769_529_091, got {actual}"
              (actual = 6_769_529_091))
      LSpec.lspecIO
        (.ofList [("ixvm",
          [fullSeq, aiurSeq, arenaSeq, exploitSeq, paritySeq, shardSeq])]) []),
  ("validate-aux", runCompileValidateAux env),
  -- Cross-compiler differential over the same fixture corpus: pure-Lean
  -- Ix.CompileM per-block vs Rust, root-cause classified (see
  -- Tests.Ix.Compile.AuxGenDiff).
  ("aux-gen-diff", Tests.Compile.AuxGenDiff.run env),
  ("decompile-diff", Tests.Compile.DecompileDiff.run env),
  -- lean4lean dependency smoke: accept a real closure, reject an
  -- ill-typed decl (see Tests.Ix.Lean4Lean).
  ("lean4lean", Tests.Ix.Lean4Lean.run env),
  -- Pure-Lean kernel regression pins against a real .ixe, compiled on
  -- demand (see Tests.Tc.ParityEnv).
  ("tc-pins", Tests.Tc.Pins.run),
  -- Accelerated-vs-pure reduction differentials over that same real env
  -- (see Tests.Tc.AccelDiff and TcState.noAccel).
  ("tc-accel-diff", Tests.Tc.AccelDiff.run),
]

def main (args : List String) : IO UInt32 := do
  -- Special case: namespace-filtered kernel ixon roundtrip diagnostic.
  -- `kernel-roundtrip-ns=Nat.le` runs the same pipeline as the
  -- `kernel-ixon-roundtrip` suite (compile → ingress → egress →
  -- decompile → hash-compare) but only on the transitive closure of the
  -- constants matching the given name prefixes (comma-separated), so a
  -- single-family regression can be bisected in seconds instead of a
  -- full-env pass.
  if let some arg := args.find? (·.startsWith "kernel-roundtrip-ns=") then
    let prefixes := (arg.drop "kernel-roundtrip-ns=".length).toString.splitOn ","
      |>.filterMap fun s => if s.isEmpty then none else some s.toName
    let env ← get_env!
    let seeds := env.constants.toList.filterMap fun (n, _) =>
      if prefixes.any (·.isPrefixOf n) then some n else none
    let closed := collectDeps env seeds
    IO.println s!"[kernel-roundtrip-ns] {seeds.length} seeds, {closed.length} constants in closure"
    let errors ← Tests.Ix.Kernel.Roundtrip.rsKernelRoundtripFFI closed
    if errors.isEmpty then
      IO.println "[kernel-roundtrip-ns] OK: roundtrip clean"
      return 0
    IO.println s!"[kernel-roundtrip-ns] {errors.size} errors:"
    for msg in errors[:min 50 errors.size] do
      IO.println s!"  {msg}"
    return 1

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
  -- `--exclude=a,b,c` drops named ignored suites and runners from an unfiltered sweep.
  let excludeSet : List String :=
    match args.find? (·.startsWith "--exclude=") with
    | some a => (a.drop ("--exclude=".length)).toString.splitOn "," |>.filter fun s => !s.isEmpty
    | none => []
  let filterArgs := args.filter fun a =>
    a != "--ignored" && a != "--include-ignored" && !a.startsWith "--exclude="

  -- Run primary tests unless --ignored (without --include-ignored) is specified
  if !runIgnored || includeIgnored then
    let primaryArgs := if runIgnored || includeIgnored then [] else filterArgs
    -- Same guard as the ignored section: a filter arg naming neither a
    -- primary suite nor a primary runner must be an ERROR, not a silent
    -- no-op reporting success having run nothing.
    for arg in primaryArgs do
      if !primarySuites.contains arg
          && !(primaryRunners.any fun (key, _) => key == arg)
          && arg != "getfileenv-body" then
        IO.eprintln s!"error: no primary suite or runner named '{arg}'"
        return 1
    let primaryResult ← LSpec.lspecIO primarySuites primaryArgs
    if primaryResult != 0 then return primaryResult
    -- getFileEnv body-inclusion regression guard (IO: loads a fixture file)
    let envBodySeq ← Tests.Ix.EnvBody.suite
    let envBodyResult ← LSpec.lspecIO (.ofList [("getfileenv-body", [envBodySeq])]) primaryArgs
    if envBodyResult != 0 then return envBodyResult
    let runners := if primaryArgs.isEmpty then primaryRunners
      else primaryRunners.filter fun (key, _) => primaryArgs.contains key
    for (_, action) in runners do
      let r ← action
      if r != 0 then return r

  -- Run ignored tests when --ignored or --include-ignored is specified
  if runIgnored || includeIgnored then
    let env ← get_env!
    let allRunners := ignoredRunners env
    -- A named suite — selected via a filter arg or removed via `--exclude` —
    -- that matches nothing is an ERROR, not a silent no-op: otherwise a typo
    -- runs (or excludes) nothing and still reports success having executed
    -- nothing.
    for arg in filterArgs ++ excludeSet do
      if !(allRunners.any fun (key, _) => key == arg)
          && !ignoredSuites.contains arg then
        IO.eprintln s!"error: no ignored suite or runner named '{arg}'"
        return 1
    let suites := excludeSet.foldl (fun m k => m.erase k) ignoredSuites
    let runners := allRunners.filter fun (key, _) => !excludeSet.contains key
    let mut result ← LSpec.lspecIO suites filterArgs
    let filtered := if filterArgs.isEmpty then runners
      else filterArgs.filterMap fun arg => runners.find? fun (key, _) => key == arg
    for (_, action) in filtered do
      let r ← action
      if r != 0 then result := r
    return result
  else
    return 0
