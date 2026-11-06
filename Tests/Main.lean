import Tests.Aiur
import Tests.Aiur.IOBuffer
import Tests.Aiur.RustSyntax
import Tests.Ix.Ixon
import Tests.Ix.IxonRejectParity
import Tests.Ix.IxonSyntax
import Tests.Ix.IxVM
import Tests.Ix.IxVM.Eval
import Tests.Ix.IxVM.Exploits
import Tests.Ix.IxVM.DefinitionDependencies
import Tests.Ix.IxVM.BindingAnchors
import Tests.Ix.IxVM.BindingFrontier
import Tests.Ix.IxVM.TagN
import Tests.Ix.IOIngress
import Tests.Ix.Claim
import Tests.Ix.Merkle
import Tests.Ix.AssumptionTree
import Tests.Ix.Commit
import Tests.Ix.Compile.ValidateAux
import Tests.Ix.RoleCompile
import Tests.Ix.RoleEquations
import Tests.Ix.LeanExport
import Tests.Ix.HostAdmissionCli
import Tests.Ix.Compile.AuxiliaryClosureCanon
import Tests.Ix.Compile.IndFlags
import Tests.Ix.CompileDeterminism
import Tests.Ix.Kernel.AdmissionHashDiff
import Tests.Ix.Kernel.UserAxioms
import Tests.Ix.Compile.KernelReportTests
import Tests.Ix.Compile.LeanReportTests
import Tests.Ix.Compile.GroundRefusal
import Tests.Ix.Compile.SelectedClosure
import Tests.Ix.Compile.ClosureWhole
import Tests.Ix.Compile.CheckerSupport
import Tests.Ix.Compile.PackUnits
import Tests.Ix.IxVM.SubstBoundaries
import Tests.Ix.Decompile
import Tests.Ix.Kernel.BuildPrimitives
import Tests.Ix.Kernel.CheckCompPoly
import Tests.Ix.Kernel.CheckPrimeGaps
import Tests.Ix.Kernel.CheckTauCeti
import Tests.Ix.Kernel.CheckTauCetiReduction
import Tests.Ix.Kernel.Tutorial
import Tests.Ix.Kernel.Arena
import Tests.Ix.Kernel.FastPaths
import Tests.Ix.Kernel.PrimAddrs
import Tests.Ix.Kernel.ReaderRoundtrip
import Tests.Ix.Kernel.FidelityAccess
import Tests.Ix.Kernel.PreludeFidelity
import Tests.Ix.Kernel.SourceIngress
import Tests.Ix.Kernel.TierInd
import Tests.Ix.Kernel.BundleEvidence
import Tests.Ix.Cert.Statement
import Tests.Ix.InitStd
import Tests.RoleTableWire
import Tests.Ix.ResourceHints
import Tests.Ix.Kernel.RecordCheck
import Tests.Ix.Kernel.CheckLeanTargets
import Tests.Ix.Kernel.CheckLeanCli
import Tests.Ix.Kernel.ValidateReaderCli
import Tests.Ix.SharingExact
import Tests.Ix.SharingUniform
import Tests.Ix.SharingComponents
import Tests.Ix.SharingTiered
import Tests.Ix.SourceContract
import Tests.Ix.SourceContract.ImportCheck
import Tests.Ix.SourceContract.SyntaxCheck
import Tests.Ix.SourceContract.Driver
import Tests.Ix.BenchMeasures
import Tests.Ix.IxonUniverse
import Tests.Ix.Kernel.Pins
import Tests.Ix.Kernel.AccelSemantics
import Tests.FFI
import Tests.Keccak
import Tests.MultiStark
import Tests.Aggr
import Tests.AggrProof
import Tests.AggrBindingReuse
import Tests.AggrToolchains
import Tests.AggrSemantics
import Tests.AggrActivation
import Tests.Cli
import Tests.CompressionCli
import Tests.Ix.Ixes
import Tests.Ix.EnvBody
import Tests.Ix.MetaEnv
import Tests.Ix.Catalog
import Tests.Ix.CatalogDedup
import Tests.Ix.ImportIxe
import Tests.Ix.TruthMinesRecords
import Tests.Ix.TruthMines
import Tests.Registry
import Ix.Common
import Ix.Meta
import Ix.IxVM

/-!
  Main test runner and registry for `IxTests`.
-/

open Tests.Registry in
/-- Every `IxTests` entry with its tier (`Tests/Registry.lean`): primary
entries run with no arguments; the others are named, or selected by tier
(`--tier ci:<job>`, `landing`, `manual`). -/
def registry : List Entry := [
  -- primary suites
  .suite "ffi" .primary Tests.FFI.suite,
  .suite "meta-env" .primary Tests.Ix.MetaEnv.suite,
  .suite "catalog" .primary Tests.Ix.Catalog.suite,
  .suite "import-ixe" .primary Tests.Ix.ImportIxe.suite,
  .suite "lean-export" .primary Tests.Ix.LeanExport.suite,
  .suite "truthmines-spec" .primary Tests.Ix.TruthMinesRecords.suite,
  -- `concurrently`: the long role and admission checks run at once
  .suiteIO "ixon" .primary (concurrently (Tests.Ixon.suite ++ Tests.Ix.IxonUniverse.suite)),
  .suiteIO "ixon-reject-parity" .primary Tests.Ix.IxonRejectParity.suite,
  .suite "role-equations" .primary Tests.Ix.RoleEquations.suite,
  .suite "ixon-syntax" .primary Tests.IxonSyntax.suite,
  .suite "claim" .primary Tests.Claim.suite,
  .suite "merkle" .primary Tests.Merkle.suite,
  .suite "assumption-tree" .primary Tests.AssumptionTree.suite,
  .suite "commit" .primary Tests.Commit.suite,
  .suite "keccak" .primary Tests.Keccak.suite,
  .suiteIO "exact-sharing" .primary (concurrently (Tests.SharingExact.suite ++ Tests.SharingUniform.suite ++ Tests.SharingTiered.suite)),
  .suite "sharing-components" .primary Tests.SharingComponents.suite,
  .suite "source-contract" .primary (Tests.Ix.SourceContract.suite ++ Tests.Ix.SourceContract.Driver.suite),
  .suite "bench-measures" .primary Tests.Ix.BenchMeasures.suite,
  -- the compile's named refusal of ungrounded input (the IO pipeline and the pure compile)
  .suite "ground-unit" .primary Tests.Ix.Compile.GroundRefusal.suite,
  -- the strict readers of the checkers' reports (Tests.Ix.Compile.KernelReport)
  .suite "compiler-reports" .primary Tests.Ix.Compile.KernelReportTests.suite,
  .suite "compiler-lean-reports" .primary Tests.Ix.Compile.LeanReportTests.suite,
  .runner "ixvm-subst-boundaries" .primary Tests.Ix.IxVM.SubstBoundaries.runSuite,
  -- selected closures (`collectSelectedDeps`): whole logical units, a
  -- matcher's unit, mutual siblings, checker support from `Role.deps`
  .suite "compiler-selected-closure" .primary Tests.Ix.Compile.SelectedClosure.suite,
  .suite "aiur-cross" .primary [AiurTests.Cross.tests],
  .runner "aiur-io-buffer" .primary AiurTests.IOBuffer.runSuite,
  .suite "aiur-cost" .primary [AiurTests.Cost.tests],
  .suite "aiur-trace-plan" .primary [AiurTests.TracePlan.tests],
  .suite "prim-addrs" .primary Tests.Ix.Kernel.PrimAddrs.suite,
  -- the role table's wire vectors (Tests/Fixtures/ixon-v4/role-table.tsv), which
  -- Rust's codec is tested against, are IxC's codec's
  .runner "role-table-wire" .primary Tests.RoleTableWire.run,
  -- the Ixon reader against a direct translation of compiled Lean constants
  .suite "kernel-reader-roundtrip" .primary Tests.Ix.Kernel.ReaderRoundtrip.suite,
  .suite "kernel-fidelity-access" .primary Tests.Ix.Kernel.FidelityAccess.suite,
  .suite "kernel-prelude-fidelity" .primary Tests.Ix.Kernel.PreludeFidelity.suite,
  .suite "validate-lean-reader-cli" .primary Tests.Ix.Kernel.ValidateReaderCli.suite,
  -- the Source-mode check (`Ix.LeanIngress`) on the same fixtures, from Lean's constants
  .suite "kernel-source-ingress" .primary Tests.Ix.Kernel.SourceIngress.suite,
  -- the typing tier's inductive install and its answer view
  .suite "kernel-tier-ind" .primary Tests.Ix.Kernel.TierInd.suite,
  -- the resource validator's typing half on the compiled fixtures
  .suite "resource-hints" .primary Tests.ResourceHints.suite,
  -- Source mode's evidence from the committed bundle (`Ix.RoleEvidence.bundleEvidence`), on
  -- the well-founded operations' Init closure without the certificate theorems
  .suite "kernel-bundle-evidence" .primary Tests.Ix.Kernel.BundleEvidence.suite,
  -- the certification statements on the same fixtures: the compile's checks, and
  -- the per-root hypotheses and conclusion
  .suite "cert-statement" .primary Tests.Ix.Cert.Statement.suite,
  .suite "kernel-record-check" .primary Tests.Ix.Kernel.RecordCheck.suite,
  -- the fold and the role table's admission under each axiom policy (user axioms)
  .suite "kernel-user-axioms" .primary Tests.Ix.Kernel.UserAxioms.suite,
  .suite "kernel-check-lean-targets" .primary Tests.Ix.Kernel.CheckLeanTargets.suite,
  .suite "primitive-address-parity" .primary Tests.Ix.Kernel.BuildPrimitives.paritySuite,
  .suite "decompile-unit" .primary Tests.Decompile.unitSuite,
  -- getFileEnv body-inclusion regression guard (IO: loads a fixture file)
  .suiteIO "getfileenv-body" .primary (do return [← Tests.Ix.EnvBody.suite]),
  -- primary runners: quick suites kept as deferred `IO` actions (not
  -- `TestSeq` values) so their setup (Aiur system builds, STARK proofs) does
  -- not run at module initialization for unrelated invocations. All are
  -- seconds-scale: ixvm-tagn about 16 s, aiur-prove
  -- about 11 s and the rest 2-4 s each.
  .runner "aiur-rust-syntax" .primary AiurTests.RustSyntax.run,
  -- Reductions no kernel may make beyond Lean's (class methods reduced
  -- without their instance, `numBits ≡ 64`, the `Fin.val` commute): every
  -- probe's closure through IxC.
  .runner "kernel-fast-paths" .primary Tests.Ix.Kernel.FastPaths.run,
  -- The circuit TagN codec against the host codec (about 16 s).
  .runner "ixvm-tagn" .primary Tests.Ix.IxVM.TagN.runSuite,
  -- every IO byte stream of the IxVM, ix_aggr and multi-stark verifier
  -- circuits goes through the range-checked reader
  .suiteIO "io-ingress" .primary Tests.IOIngress.suite,
  .runner "aiur-prove" .primary (do
    IO.println "aiur-prove"
    match AiurTestEnv.build (pure toplevel) with
    | .error e => IO.eprintln s!"Aiur setup failed: {e}"; return 1
    | .ok env => do
      let r1 ← LSpec.lspecEachIO aiurTestCases fun tc => pure (env.runTestCase tc)
      -- The same toplevel with `testGroups` applied: the members share one
      -- circuit, and the whole suite of grouped cases proves through it.
      match AiurTestEnv.build (pure toplevel) testGroups with
      | .error e => IO.eprintln s!"Aiur grouped setup failed: {e}"; return 1
      | .ok genv => do
        let r2 ← LSpec.lspecEachIO groupedTestCases fun tc => pure (genv.runTestCase tc)
        let r3 ← LSpec.lspecIO
          (.ofList [("aiur-grouping", [groupingStructureChecks genv.compiled]),
            ("aiur-inline-order", [assertOrderChecks env.compiled])]) []
        return if r1 == 0 && r2 == 0 && r3 == 0 then 0 else 1),
  .runner "aiur-hashes" .primary (do
    IO.println "aiur-hashes"
    let .ok blake3Env := AiurTestEnv.build (do
        let t ← Aiur.Library.core.merge Aiur.Library.byteStream
        let t ← t.merge Aiur.Library.blake3
        t.merge blake3BoundaryProgram)
      | IO.eprintln "Blake3 setup failed"; return 1
    let r1 ← LSpec.lspecEachIO blake3TestCases fun tc => pure (blake3Env.runTestCase tc)
    let .ok sha256Env := AiurTestEnv.build (do
        let t ← Aiur.Library.core.merge Aiur.Library.byteStream; t.merge IxVM.sha256)
      | IO.eprintln "SHA256 setup failed"; return 1
    let r2 ← LSpec.lspecEachIO sha256TestCases fun tc => pure (sha256Env.runTestCase tc)
    return if r1 == 0 && r2 == 0 then 0 else 1),
  .runner "rbtree-map" .primary (do
    IO.println "rbtree-map"
    match AiurTestEnv.build (pure IxVM.rbTreeMap) with
    | .error e => IO.eprintln s!"RBTreeMap setup failed: {e}"; return 1
    | .ok env => LSpec.lspecEachIO rbTreeMapTestCases fun tc => pure (env.runTestCase tc)),
  -- Multi-STARK recursive verifier: `multi-stark` runs the verifier's
  -- primitive self-tests, `recursive-verifier` the full
  -- factorial-prove → recursive-verify → reject-tampering pipeline.
  .runner "multi-stark" .primary Tests.MultiStark.selfTestSuite,
  .runner "recursive-verifier" .primary Tests.MultiStark.endToEndSuite,
  -- Converged heterogeneous aggregation circuit: all fifteen `ix_aggr` shapes,
  -- driver/cache semantics, and one negative case per broken binding.
  .runner "ix-aggr" .primary Tests.Aggr.convergedSuite,
  -- `.ixes` manifest parser: trailing tree/peaks sections and strictness.
  .runner "ixes-manifest" .primary Tests.Ix.Ixes.suite,
  -- Non-canonical stored inductive flags and mixed mutual safety: refused by
  -- both Lean drivers and the pure compiler (Tests.Ix.Compile.IndFlags).
  .runner "compile-ind-flags" .primary Tests.Ix.Compile.IndFlags.run,
  -- Differential comparison of Address.blake3, Address.blake3Pure, and
  -- Address.admissionHash across multi-chunk boundaries and an .ixe artifact.
  .runner "admission-hash-diff" .primary Tests.Ix.Kernel.AdmissionHashDiff.run,

  -- CLI integration tests (ci.yml's lean-test job)
  .runner "cli" (.ci .cli) Tests.Cli.suite,
  .suite "compile-determinism" (.ci .cli) Tests.Ix.CompileDeterminism.suite,
  .suite "kernel-check-lean-cli" (.ci .cli) Tests.Ix.Kernel.CheckLeanCli.suite,
  .suite "artifact-compile-cli" (.ci .cli) Tests.Ix.RoleCompile.suite,
  .suite "host-admission-cli" (.ci .cli) Tests.Ix.HostAdmissionCli.suite,
  -- `ix prove-binding`, shard proofs that assume the binding, and their
  -- composition with the binding proof file and refusals without it, through
  -- the `ix` binary (`aggregate-binding-reuse` without its two aggregates).
  -- Its 64 GiB proving budget would set lean-test's memory peak, so it runs
  -- in the compiler-closures partition of the merge queue.
  .runner "binding-proof-cli" (.ci .compilerClosures) Tests.Aggr.BindingReuse.cli,

  -- expensive suites and runners (these require significant RAM)
  .suite "catalog-dedup" (.ci .misc) Tests.Ix.CatalogDedup.suite,
  .suite "truthmines" (.manual "builds the whole TruthMines corpus (network, Mathlib, FLT)") Tests.Ix.TruthMines.buildSuite,
  .suite "truthmines-check" (.manual "checks the whole TruthMines corpus built by `truthmines`") Tests.Ix.TruthMines.checkSuite,
  .suite "truthmines-mini" (.manual "builds the small TruthMines tier (network, Mathlib, FLT)") Tests.Ix.TruthMines.miniSuite,
  .suite "commit-io" (.ci .misc) Tests.Commit.suiteIO,
  .suite "kernel-tutorial" (.ci .misc) Tests.Ix.Kernel.Tutorial.suite,
  .suite "kernel-check-comppoly" (.manual "needs comppoly.ixe at the repository root") Tests.Ix.Kernel.CheckCompPoly.suite,
  .suite "kernel-check-primegaps" (.manual "self-contained, but in no gate yet") Tests.Ix.Kernel.CheckPrimeGaps.suite,
  .suite "kernel-check-tauceti" (.manual "needs tauceti.ixe") Tests.Ix.Kernel.CheckTauCeti.suite,
  .suite "kernel-check-tauceti-reduction" (.manual "self-contained, but in no gate yet") Tests.Ix.Kernel.CheckTauCetiReduction.suite,
  .suite "rust-kernel-build-primitives" (.manual "dumps the primitive content-address table for PrimAddrs::new") Tests.Ix.Kernel.BuildPrimitives.suite,
  -- auxiliary addresses do not depend on the compile set (closure vs whole env)
  .suite "canon-closure-aux" (.ci .compilerClosures) Tests.Ix.Compile.AuxiliaryClosureCanon.suite,
  -- `ix compile-lean` on Init+Std: its report checks, the reference digest
  -- (Tests/Fixtures/initstd-reference.txt), and `ix check-lean` on the artifact
  -- with every bound role admitted
  .runner "initstd-reference" (.ci .landingInitStdCli) Tests.Ix.InitStd.reference,
  -- Address.blake3, Address.blake3Pure and Address.admissionHash on every
  -- record, blob and the binding of the artifact `initstd-reference` leaves
  .runner "admission-hash-diff-initstd" (.ci .landingInitStdCli) Tests.Ix.Kernel.AdmissionHashDiff.runInitStd,
  -- `ix validate-lean` on Init+Std: compile, serde, projection, reader and
  -- decompile fidelity
  .runner "fidelity-initstd" (.ci .landingInitStdCli) Tests.Ix.InitStd.fidelity,
  .suite "cert-evidence-agreement" .primary Tests.Ix.Cert.Statement.evidenceSuite,
  .runner "aggregate-proof" (.manual "a proof round trip through the production ix_aggr circuit; minutes of proving") Tests.Aggr.proofRoundTrip,
  .runner "aggregate-binding-reuse" (.manual "one binding proof file discharges two aggregates, end to end through the `ix` binary; minutes of recursion and about 190 GB, needs `lake build ix`; `binding-proof-cli` runs it without the aggregates") Tests.Aggr.BindingReuse.run,
  .runner "aggregate-toolchains" (.manual "libraries from four Lean toolchains proven with one IxVM key and joined into one catalog root, end to end through the `ix` binary; tens of minutes of proving, needs `lake build ix` and `zstd`; IX_TOOLCHAINS_MAX_RAM sets the aggregate RAM budget in GiB (default 140)") Tests.Aggr.Toolchains.run,
  .runner "kernel-dependencies" (.manual "the IxVM definition-dependency checks alone; `ixvm` runs them too") (do
    match AiurTestEnv.build IxVM.ixVM IxVM.functionGroups with
    | .error e => IO.eprintln s!"IxVM setup failed: {e}"; return 1
    | .ok vm =>
      let tests ← Tests.Ix.IxVM.DefinitionDependencies.tests vm.compiled
      LSpec.lspecIO (.ofList [("kernel-dependencies", [tests])]) []),
  .env "ixvm" (.ci .misc) fun env => do
    let kernelChecks ← kernelChecks env
    -- The kernel CheckEnv smokes.
    let claimEnv ← IxVM.ClaimHarness.loadIxonEnv ``Nat.add_comm env
    let envFull ← claimCheckEnvFull claimEnv
    let envFrontier ← claimCheckEnvFrontier claimEnv
    let checkAsm ← claimCheckWithAsm claimEnv
    let revealFields ← claimRevealDefnFields claimEnv
    let revealExpr ← claimRevealDefnExpr claimEnv
    let revealModes ← claimRevealBinderModes
    let revealCPrj ← claimRevealCPrj claimEnv
    let containsTc ← claimContains
    -- Shared-infrastructure test entrypoints live only in the FULL
    -- toplevel (pruning drops them so test-only circuits never widen a
    -- committed kernel system).
    let kernelUnitTests := .exec `kernel_unit_tests
    let serdeTest ← serdeNatAddComm env
    match AiurTestEnv.build IxVM.ixVM IxVM.functionGroups, AiurTestEnv.build IxVM.ixVMFull with
    | .error e, _ | _, .error e =>
      IO.eprintln s!"IxVM env build failed: {e}"; return 1
    | .ok vmEnv, .ok fullVmEnv =>
      IO.eprintln "[ixvm] eval: reduction, output contracts, and compiled fixtures"
      let evalSeq ← Tests.Ix.IxVM.Eval.tests vmEnv
      let evalCompiledSeq ← Tests.Ix.IxVM.Eval.compiledTests env vmEnv
      let evalCommandSeq ← Tests.Ix.IxVM.Eval.commandTests env vmEnv
      IO.eprintln "[ixvm] eval: dependent, recursive, and neutral-term fixtures"
      let evalDifficultSeq ← Tests.Ix.IxVM.Eval.difficultTests env vmEnv
      IO.eprintln "[ixvm] eval: generated differential corpus (24 samples)"
      let evalDifferentialSeq ← Tests.Ix.IxVM.Eval.differentialTests env vmEnv
      -- Kernel-arena fixtures: the repo's NEGATIVE corpus (every
      -- `bad_*` must be rejected by an in-kernel assert_eq!). Runs
      -- through the kernel's subject-only `verify_const` debug
      -- entrypoint, which lives only in the FULL toplevel — the
      -- production one carries `verify_claim` alone.
      let arenaSeq ← Tests.Ix.Kernel.Arena.arenaTests env fullVmEnv.compiled
      -- Adversarial Ixon: exploit attempts authored as raw Ixon
      -- constants, below the layer the arena's Lean fixtures can
      -- reach. Each case pins the kernel's verdict, which is REJECT
      -- except where accepting is the specified claim semantics.
      let exploitSeq ← Tests.Ix.IxVM.Exploits.exploitTests env vmEnv.compiled
      let dependencySeq ← Tests.Ix.IxVM.DefinitionDependencies.tests vmEnv.compiled
      let bindingAnchorChecks ← Tests.Ix.IxVM.BindingAnchors.defaultChecks vmEnv.compiled
      let bindingAnchorSeq := bindingAnchorChecks.foldl
        (fun tests (name, passed) => tests ++ LSpec.test name passed) LSpec.TestSeq.done
      let bindingFrontierChecks ← Tests.Ix.IxVM.BindingFrontier.defaultChecks vmEnv.compiled
      let bindingFrontierSeq := bindingFrontierChecks.foldl
        (fun tests (name, passed) => tests ++ LSpec.test name passed) LSpec.TestSeq.done
      let aiurSeq := (kernelChecks ++
          [envFull, envFrontier, checkAsm,
           revealFields, revealExpr, revealModes, revealCPrj, containsTc]).foldl
        (init := .done) fun s tc => s ++ vmEnv.runTestCase tc
      -- Codegen parity gate: the generated Rust kernel is emitted from
      -- the toplevel, so this runs the same witnesses through both
      -- engines and asserts they agree. It is only meaningful against a
      -- CURRENT `ix codegen` output — regenerate after any Aiur edit, or
      -- this gate compares against a stale kernel. Reuses the
      -- `kernelChecks` cases (`runParityCase` ignores the FFT pins), so
      -- the per-constant witness setup runs once, not twice.
      let parityTasks ← kernelChecks.mapM fun tc =>
        IO.asTask (pure (runParityCase vmEnv.compiled tc))
      let paritySeq ← parityTasks.foldlM (init := .done) fun s task => do
        let seq ← IO.ofExcept task.get
        pure (s ++ seq)
      let fullSeq := [kernelUnitTests, serdeTest].foldl (init := .done)
        fun s tc => s ++ fullVmEnv.runTestCase tc
      -- Shard pipeline: witness built in Rust (thin-frontier claim,
      -- parallel closure walk) and run on the native kernel. Pinned FFT
      -- is the regression signal.
      let shardSeq ← match (← shardCheckEnvCase env) with
        -- The target constant is absent from this toolchain: a failure, as
        -- an absent pinned constant is in `kernelChecks`, so that a
        -- toolchain bump that renames it cannot turn the pin into a pass.
        -- A fixture that no longer selects any owned constants throws.
        | none => pure (LSpec.test
            "shard pipeline: the target ByteArray.utf8DecodeChar?_utf8EncodeChar_append is in the environment"
            false)
        | some (handle, ownedBlob) =>
          let funIdx := vmEnv.compiled.getFuncIdx `verify_claim |>.get!
          match vmEnv.compiled.bytecode.shardCheckWithEnv
                  funIdx handle ownedBlob false with
          | .error e =>
            pure (LSpec.test s!"shard pipeline execution: {e}" false)
          | .ok (_, _, qc) =>
            -- Exact pin, same convention as `kernelCheckEntries`
            -- (`.round.toUInt64.toNat`): any cost shift must be an
            -- explicit, reviewed bump.
            let actual :=
              (Aiur.computeStats vmEnv.compiled qc vmEnv.shapes).totalFftCost.round.toUInt64.toNat
            pure (LSpec.test
              s!"Shard pipeline FFT matches: expected 85_826_059_914, got {actual}"
              (actual = 85_826_059_914))
      LSpec.lspecIO
        (.ofList [("ixvm",
          [evalSeq, evalCompiledSeq, evalCommandSeq, evalDifficultSeq, evalDifferentialSeq,
           fullSeq, aiurSeq, arenaSeq, exploitSeq, dependencySeq, bindingAnchorSeq,
           bindingFrontierSeq, paritySeq, shardSeq])]) [],
  -- Selected closures (Tests.Ix.Compile.{SelectedClosure,ClosureWhole,CheckerSupport,PackUnits}):
  -- closure against whole, checker-support ground, and `ix pack` carrying the reference closure.
  .runner "compiler-selected-closure-e2e" (.ci .compilerClosures) Tests.Ix.Compile.SelectedClosure.run,
  .runner "compile-closure-whole" (.ci .compilerClosures) Tests.Ix.Compile.ClosureWhole.run,
  .runner "checker-support-regression" (.ci .compilerClosures) Tests.Ix.Compile.CheckerSupport.run,
  .runner "pack-units" (.ci .compilerClosures) Tests.Ix.Compile.PackUnits.run,
  -- The existing eight IxC selected-producer pins and their subject budgets.
  .runner "tc-pins" (.ci .compilerClosures) Tests.Tc.Pins.run,
  -- Exact retained acceleration inputs, value/head witnesses and full closures.
  .runner "kernel-accel-semantics" (.ci .compilerClosures) Tests.Ix.Kernel.AccelSemantics.run,
  -- the 132-case, twice-executed `ix_aggr` activation matrix, kept out of the
  -- primary suite and independent of the large environment
  .runner "aggregate-activation" (.manual "a diagnostic matrix (132 cases, run twice)") Tests.Aggr.activationAudit,
  -- Compression CLI setup and proof-rejection checks, run explicitly.
  .runner "compression-cli" (.manual "compression CLI setup and proof-rejection checks; needs `lake build ix`") (do
    Tests.CompressionCli.run
    return 0)
]

/-- The entries that must stay registered once, in their tier
(`Tests.Registry.coverageProblems`): the checks the certification, the
compiler and the proof system's claims rest on. Moving one to the
manual tier, or deleting it, fails `ixtests-registry`; so does a CI tier
with no required entry. -/
def required : List (String × String) := [
  ("cert-statement", "primary"),
  ("cert-evidence-agreement", "primary"),
  ("ix-aggr", "primary"),
  ("lean-export", "primary"),
  ("io-ingress", "primary"),
  ("kernel-source-ingress", "primary"),
  ("kernel-reader-roundtrip", "primary"),
  ("kernel-bundle-evidence", "primary"),
  ("resource-hints", "primary"),
  ("compiler-reports", "primary"),
  ("ground-unit", "primary"),
  ("prim-addrs", "primary"),
  ("role-table-wire", "primary"),
  ("exact-sharing", "primary"),
  ("ixon-reject-parity", "primary"),
  ("role-equations", "primary"),
  ("ixvm-tagn", "primary"),
  ("ixes-manifest", "primary"),
  ("kernel-record-check", "primary"),
  ("compile-ind-flags", "primary"),
  ("admission-hash-diff", "primary"),
  ("cli", "ci:cli"),
  ("compile-determinism", "ci:cli"),
  ("kernel-check-lean-cli", "ci:cli"),
  ("artifact-compile-cli", "ci:cli"),
  ("host-admission-cli", "ci:cli"),
  ("binding-proof-cli", "ci:compiler-closures"),
  ("canon-closure-aux", "ci:compiler-closures"),
  ("compile-closure-whole", "ci:compiler-closures"),
  ("checker-support-regression", "ci:compiler-closures"),
  ("tc-pins", "ci:compiler-closures"),
  ("kernel-accel-semantics", "ci:compiler-closures"),
  ("ixvm", "ci:misc"),
  ("kernel-tutorial", "ci:misc"),
  ("initstd-reference", "ci:landing-initstd-cli"),
  ("admission-hash-diff-initstd", "ci:landing-initstd-cli"),
  ("fidelity-initstd", "ci:landing-initstd-cli")]

def main (args : List String) : IO UInt32 :=
  Tests.Registry.run registry required get_env! args
