import Tests.Aiur
import Tests.Aiur.RustSyntax
import Tests.Ix.Ixon
import Tests.Ix.IxonCorpus
import Tests.Ix.IxonSyntax
import Tests.Ix.IxVM
import Tests.Ix.IxVM.Eval
import Tests.Ix.IxVM.Exploits
import Tests.Ix.IxVM.DefinitionDependencies
import Tests.Ix.IxVM.TagN
import Tests.Ix.Claim
import Tests.Ix.Merkle
import Tests.Ix.AssumptionTree
import Tests.Ix.Commit
import Tests.Ix.Compile
import Tests.Ix.Compile.ValidateAux
import Tests.Ix.Compile.AuxGenDiff
import Tests.Ix.Compile.NestedAgreement
import Tests.Ix.Compile.Canon
import Tests.Ix.Compile.CanonClique
import Tests.Ix.Compile.Clique.Dag
import Tests.Ix.Compile.Clique.Ownership
import Tests.Ix.Compile.Clique.OwnershipUnits
import Tests.Ix.Compile.Clique.Recognition
import Tests.Ix.Compile.Clique.Rows
import Tests.Ix.Compile.Clique.RustParity
import Tests.Ix.Compile.Clique.Transport
import Tests.Ix.Compile.AlphaEq
import Tests.Ix.Compile.MotiveEq
import Tests.Ix.Compile.ReservedInput
import Tests.Ix.Compile.Image
import Tests.Ix.Compile.Pass3RustParity
import Tests.Ix.Compile.O11aDecline
import Tests.Ix.Compile.O11aCopies
import Tests.Ix.Compile.O11aPlanning
import Tests.Ix.Compile.PlanCache
import Tests.Ix.Compile.Pass3Cliques
import Tests.Ix.Compile.ChangedSet
import Tests.Ix.Compile.DecompileDiff
import Tests.Ix.Compile.AuxGenClosure
import Tests.Ix.Compile.AuxGenClosureCanon
import Tests.Ix.Compile.AuxCert
import Tests.Ix.Compile.IndFlags
import Tests.Ix.Compile.ReservedMetadata
import Tests.Ix.Compile.ClaimConflict
import Tests.Ix.Compile.ClaimOrder
import Tests.Ix.Compile.ExpressionIndex
import Tests.Ix.Compile.ExpressionFrame
import Tests.Ix.Compile.ExactKey
import Tests.Ix.Compile.UniverseCache
import Tests.Ix.Compile.RewriteRetry
import Tests.Ix.Compile.Pass3Core
import Tests.Ix.Compile.HeadLookup
import Tests.Ix.Compile.KernelReportTests
import Tests.Ix.Compile.LeanReportTests
import Tests.Ix.Compile.AuxCertLeanExpect
import Tests.Ix.Compile.KernelLegs
import Tests.Ix.Compile.Pass3
import Tests.Ix.Compile.Pass3Tools
import Tests.Ix.Compile.DriverInput
import Tests.Ix.Compile.LocalBlob
import Tests.Ix.Compile.IndexSafety
import Tests.Ix.Compile.BridgeBoundaries
import Tests.Ix.Compile.BridgeScopes
import Tests.Ix.Compile.BridgePortable
import Tests.Ix.Compile.BridgeProvenance
import Tests.Ix.Compile.TableWorklist
import Tests.Ix.Compile.HeaderCounts
import Tests.Ix.Compile.PayloadArrays
import Tests.Ix.Compile.UniverseWire
import Tests.Ix.Compile.GroundRefusal
import Tests.Ix.Compile.SelectedClosure
import Tests.Ix.Compile.ClosureWhole
import Tests.Ix.Compile.ClosurePhase4
import Tests.Ix.Compile.CheckerSupport
import Tests.Ix.Compile.PackUnits
import Tests.Ix.Compile.Twins
import Tests.Ix.Compile.Oracle
import Tests.Ix.Compile.ScheduleIdentity
import Tests.Ix.Compile.SourceIdentity
import Tests.Ix.Compile.AuxSource
import Tests.Ix.Compile.SourceFamily
import Tests.Ix.AuxGen.ExprUtilsTests
import Tests.Ix.AuxGen.LevelsTests
import Tests.Ix.AuxGen.RecursorTests
import Tests.Ix.AuxGen.AuxKernelTests
import Tests.Ix.AuxGen.ConfigurationTests
import Tests.Ix.AuxGen.ElimRuleTests
import Tests.Ix.AuxGen.PortableKernel
import Tests.Ix.AuxGen.FlatBlockTests
import Tests.Ix.AuxGen.LevelEgressTests
import Tests.Ix.AuxGen.LevelReference
import Tests.Ix.AuxGen.ComponentsTests
import Tests.Ix.AuxGen.FlatBlockSource
import Tests.Ix.AuxGen.FlatBlockInitStd
import Tests.Ix.AuxGen.BelowIxc
import Tests.Ix.AuxGen.ClosureProbe
import Tests.Ix.AuxGen.AcceptanceProbe
import Tests.Ix.AuxGen.TierService
import Tests.Ix.AuxGen.CheckedGeneration
import Tests.Ix.GroundTests
import Tests.Ix.Decompile
import Tests.Ix.Kernel.BuildPrimitives
import Tests.Ix.Kernel.BuildPrimOrigs
import Tests.Ix.Kernel.CheckEnv
import Tests.Ix.Kernel.CheckCompPoly
import Tests.Ix.Kernel.CheckPrimeGaps
import Tests.Ix.Kernel.CheckTauCeti
import Tests.Ix.Kernel.CheckTauCetiReduction
import Tests.Ix.Kernel.Roundtrip
import Tests.Ix.Kernel.RoundtripNoCompile
import Tests.Ix.Kernel.Tutorial
import Tests.Ix.Kernel.Arena
import Tests.Ix.Kernel.FastPaths
import Tests.Ix.Kernel.PrimAddrs
import Tests.Ix.Kernel.AdmissionHashDiff
import Tests.Ix.Kernel.ReaderRoundtrip
import Tests.Ix.Kernel.FidelityAccess
import Tests.Ix.Kernel.ReaderAccess
import Tests.Ix.Kernel.PreludeFidelity
import Tests.Ix.Kernel.CollapseFidelity
import Tests.Ix.Kernel.SourceIngress
import Tests.Ix.Kernel.TierInd
import Tests.Ix.Kernel.BundleEvidence
import Tests.Ix.Cert.Statement
import Tests.Ix.ResourceHints
import Tests.Ix.Kernel.ReadCache
import Tests.Ix.Kernel.RecordCheck
import Tests.Ix.Kernel.CheckLeanTargets
import Tests.Ix.Kernel.CheckLeanCli
import Tests.Ix.Kernel.ValidateLeanCli
import Tests.Ix.Kernel.ValidateReaderCli
import Tests.Ix.RustSerialize
import Tests.Ix.RustDecompile
import Tests.Ix.SharingExact
import Tests.Ix.SharingUniform
import Tests.Ix.SharingFamilyPrototype
import Tests.Ix.SharingFamilyNormalize
import Tests.Ix.SharingTiered
import Tests.Ix.SharingExactFFI
import Tests.Ix.SourceContract
import Tests.Ix.SourceContract.ImportCheck
import Tests.Ix.SourceContract.SyntaxCheck
import Tests.Ix.SourceContract.Driver
import Tests.Ix.BenchMeasures
import Tests.Ix.Tc.Unit
import Tests.Ix.Tc.CanonicalCheck
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
import Tests.Ix.Kernel.Pins
import Tests.Ix.Tc.AccelDiff
import Tests.Ix.CanonM
import Tests.Ix.GraphM
import Tests.Ix.CondenseM
import Tests.FFI
import Tests.Keccak
import Tests.MultiStark
import Tests.Aggr
import Tests.AggrProof
import Tests.AggrSemantics
import Tests.AggrActivation
import Tests.Cli
import Tests.Ix.Ixes
import Tests.ShardMap
import Tests.Ix.EnvBody
import Tests.Ix.MetaEnv
import Tests.Ix.Catalog
import Tests.Ix.CatalogDedup
import Tests.Ix.CompileDeterminism
import Tests.Ix.CompileFidelity
import Tests.Ix.ImportIxe
import Tests.Ix.TruthMinesRecords
import Tests.Ix.TruthMines
import Tests.Registry
import Tests.Ix.RustCompile
import Ix.Common
import Ix.Meta
import Ix.IxVM

run_cmd do
  if (← Lean.getEnv).header.moduleNames.contains `Tests.Ix.Compile.AuxCert.NestedSortUK then
    throwError "M7's NestedSortUK fixture must be loaded at runtime, outside Tests.Main"

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
  .suite "truthmines-spec" .primary Tests.Ix.TruthMinesRecords.suite,
  .suite "ixon" .primary Tests.Ixon.suite,
  .suite "ixon-syntax" .primary Tests.IxonSyntax.suite,
  .suite "claim" .primary Tests.Claim.suite,
  .suite "merkle" .primary Tests.Merkle.suite,
  .suite "assumption-tree" .primary Tests.AssumptionTree.suite,
  .suite "commit" .primary Tests.Commit.suite,
  .suite "canon" .primary [Tests.CanonM.suite],
  .suite "keccak" .primary Tests.Keccak.suite,
  .suite "exact-sharing" .primary (Tests.SharingExact.suite ++ Tests.SharingUniform.suite ++ Tests.SharingTiered.suite),
  .suite "sharing-family-prototype" .primary Tests.SharingFamilyPrototype.suite,
  .suite "sharing-family-normalize" .primary Tests.SharingFamilyNormalize.suite,
  .suite "exact-sharing-ffi" .primary Tests.SharingExactFFI.suite,
  .suite "source-contract" .primary (Tests.Ix.SourceContract.suite ++ Tests.Ix.SourceContract.Driver.suite),
  .suite "graph-unit" .primary Tests.Ix.GraphM.suite,
  .suite "condense-unit" .primary Tests.Ix.CondenseM.suite,
  -- Pass 1's clique order: the pinned choice compares last
  .suite "canon-clique" .primary Tests.Ix.Compile.CanonClique.suite,
  -- The clique transport library (Ix.Compile.Pass.Clique, not yet wired into
  -- the compiler; these are its only coverage): its DAG helpers against the
  -- tree helpers and the memo's fuel and fresh-variable behaviour; on the
  -- clique twins and its own fixtures (loaded with the twins at run time),
  -- the recognisers and their adversarial negatives (encoding constants'
  -- names on user bodies refused or ordinary), and the transport against the
  -- twins' oracle, kernel-checked (Tests.Ix.Compile.Clique.{Dag,Recognition,
  -- Transport}; about 2 s and 23 s)
  .suite "clique-dag" .primary Tests.Ix.Compile.Clique.Dag.suite,
  .runner "clique-recognition" .primary Tests.Ix.Compile.Clique.Recognition.run,
  .runner "clique-transport" .primary Tests.Ix.Compile.Clique.Transport.run,
  -- the transport and the plan on cliques whose user values have the shape of
  -- their own encoding (both member orders): kernel-checked, every member
  -- evaluated against Lean's (one fixpoint unfolding deep), the controls
  -- transported; the carried-lemma plans, eq_def regeneration and the memo
  -- by ownership mode (Tests.Ix.Compile.Clique.Ownership, library cases; the
  -- compile units are the wiring step's; about 4 s)
  .runner "clique-ownership" .primary Tests.Ix.Compile.Clique.Ownership.run,
  -- the Rust clique library against the Lean one (test-only FFI, Rust on the
  -- clique's closure): the bounds tables, and every field of the plan of each
  -- fixture clique and of the adversarial inputs, under two addresses, and
  -- the rows of each transported plan (Tests.Ix.Compile.Clique.RustParity)
  .runner "clique-rust-parity" .primary Tests.Ix.Compile.Clique.RustParity.run,
  -- the equation rows of every transported well-founded fixture plan and the
  -- copies of its encoding, admitted by Lean's kernel, each row's swapped
  -- right-hand side rejected (Tests.Ix.Compile.Clique.Rows; IxC admission of
  -- emitted rows is the wiring step's)
  .runner "clique-rows" .primary Tests.Ix.Compile.Clique.Rows.run,
  -- the image generator's expression comparisons: raw-exact alpha equality, and motive
  -- matching up to canonical universes (Ix.Compile.Image)
  .suite "image-alpha-eq" .primary Tests.Ix.Compile.AlphaEq.suite,
  .suite "image-motive-eq" .primary Tests.Ix.Compile.MotiveEq.suite,
  -- Pass 3's reserved names: the reserved component `_ix`, the Ix auxiliaries'
  -- display names, prefixes by components, the drivers' refusals by their least message
  .suite "reserved-input" .primary Tests.Ix.Compile.ReservedInput.suite,
  .suite "bench-measures" .primary Tests.Ix.BenchMeasures.suite,
  .suite "aux-gen-unit" .primary (Tests.AuxGen.ExprUtils.suite ++ Tests.AuxGen.Levels.suite ++ Tests.AuxGen.Recursor.suite
    ++ Tests.AuxGen.AuxKernel.suite ++ Tests.AuxGen.ElimRule.suite ++ Tests.AuxGen.PortableKernel.suite ++ Tests.AuxGen.FlatBlock.suite
    ++ Tests.AuxGen.LevelEgress.suite ++ Tests.AuxGen.LevelReference.suite ++ Tests.AuxGen.Components.suite
    ++ Tests.Ix.AuxGen.ConfigurationTests.suite),
  -- source-body recognition of casesOn/recOn: the comparison controls (Ix.AuxGen.SourceIdentity)
  .suite "aux-source-identity-unit" .primary Tests.Ix.Compile.SourceIdentity.suite,
  -- `Ix.AuxSource`: telescopes and the split-minor helpers' temporary-variable supply (CQ5.1)
  .suite "aux-source-unit" .primary Tests.Compile.AuxSource.suite,
  -- the scan, and the compile's named refusal of ungrounded input (Lean and Rust)
  .suite "ground-unit" .primary (Tests.Ground.suite ++ Tests.Ix.Compile.GroundRefusal.suite),
  -- expression wire indices that do not fit a UInt64 are refused, never wrapped
  .suite "expression-index" .primary Tests.Ix.Compile.ExpressionIndex.suite,
  -- the ordinary expression compiler's frame: spines, caching, failure effects, DAGs
  .suite "expression-frame" .primary Tests.Ix.Compile.ExpressionFrame.suite,
  -- exact expression-cache keys: digest aliases never identify terms; DAG comparison
  .suite "exact-expression-key" .primary Tests.Ix.Compile.ExactKey.suite,
  -- exact universe-cache keys: the level and its complete parameter context
  .suite "universe-cache" .primary Tests.Ix.Compile.UniverseCache.suite,
  -- the call-site rewrite's retry after a proof-justified hit: generic callbacks keep
  -- it, the production ordering may skip it (Ix.Compile.Pass.Translate)
  .suite "rewrite-retry" .primary Tests.Ix.Compile.RewriteRetry.suite,
  -- the Pass 3 core without the driver: the call-site rewrite, the side-car, the memo
  -- shape and the views' equality (Ix.Compile.Pass)
  .suite "pass3-core-unit" .primary Tests.Ix.Compile.Pass3Core.suite,
  -- Pass 3's head table confirms the full name: a different name with a head's
  -- stored hash takes no route of the hooks (Tests.Ix.Compile.HeadLookup)
  .suite "image-head-lookup" .primary Tests.Ix.Compile.HeadLookup.suite,
  -- the strict readers of the checkers' reports (Tests.Ix.Compile.KernelReport)
  .suite "compiler-reports" .primary Tests.Ix.Compile.KernelReportTests.suite,
  .suite "compiler-lean-reports" .primary Tests.Ix.Compile.LeanReportTests.suite,
  .suite "aux-cert-lean-expect" .primary Tests.Ix.Compile.AuxCertLeanExpect.suite,
  .suite "compiler-kernel-legs" .primary Tests.Ix.Compile.KernelLegs.suite,
  -- auxiliary dump inputs keyed by the canonical member, not the Tarjan representative
  .suite "aux-dump-inputs" .primary Tests.Compile.AuxGenDiff.suite,
  -- the compile drivers refuse a condensation block without a reference set
  .suite "compile-driver-input" .primary Tests.Ix.Compile.DriverInput.suite,
  .suite "local-blob" .primary Tests.Ix.Compile.LocalBlob.suite,
  .suite "compiler-index-safety" .primary Tests.Ix.Compile.IndexSafety.suite,
  -- the aux kernel bridges refuse what they cannot convert (D-12)
  .suite "compiler-bridge-boundaries" .primary Tests.Ix.Compile.BridgeBoundaries.suite,
  .suite "compiler-bridge-scopes" .primary (Tests.Ix.Compile.BridgeScopes.suite ++ Tests.Ix.Compile.BridgePortable.suite),
  .suite "compiler-provenance" .primary Tests.Ix.Compile.BridgeProvenance.suite,
  .suite "table-worklist" .primary Tests.Ix.Compile.TableWorklist.suite,
  .suite "header-count" .primary Tests.Ix.Compile.HeaderCounts.suite,
  .suite "payload-arrays" .primary Tests.Ix.Compile.PayloadArrays.suite,
  .suite "universe-wire" .primary Tests.Ix.Compile.UniverseWire.suite,
  -- selected closures (`collectSelectedDeps`): whole logical units, a
  -- matcher's unit, mutual siblings, checker support from `Role.deps`
  .suite "compiler-selected-closure" .primary Tests.Ix.Compile.SelectedClosure.suite,
  .suite "aiur-cross" .primary [AiurTests.Cross.tests],
  .suite "aiur-cost" .primary [AiurTests.Cost.tests],
  .suite "aiur-trace-plan" .primary [AiurTests.TracePlan.tests],
  .suite "prim-addrs" .primary Tests.Ix.Kernel.PrimAddrs.suite,
  -- the Ixon reader against a direct translation of compiled Lean constants
  .suite "kernel-reader-roundtrip" .primary Tests.Ix.Kernel.ReaderRoundtrip.suite,
  .suite "kernel-fidelity-access" .primary Tests.Ix.Kernel.FidelityAccess.suite,
  .suite "kernel-reader-access" .primary Tests.Ix.Kernel.ReaderAccess.suite,
  .suite "kernel-prelude-fidelity" .primary Tests.Ix.Kernel.PreludeFidelity.suite,
  .suite "kernel-collapse-fidelity" .primary Tests.Ix.Kernel.CollapseFidelity.suite,
  .suite "validate-lean-fidelity-cli" .primary Tests.Ix.Kernel.ValidateLeanCli.suite,
  .suite "validate-lean-reader-cli" .primary Tests.Ix.Kernel.ValidateReaderCli.suite,
  -- the Source-mode check (`Ix.LeanIngress`) on the same fixtures, from Lean's constants
  .suite "kernel-source-ingress" .primary Tests.Ix.Kernel.SourceIngress.suite,
  -- the typing tier's inductive install and its answer view (M7 Q1)
  .suite "kernel-tier-ind" .primary Tests.Ix.Kernel.TierInd.suite,
  -- the resource validator's typing input (IxC's tiered entry, step 10c): its hints agree with
  -- `Ix.Cert.hintsOf`, every record is submitted once, and the compiled fixtures validate
  .suite "resource-hints" .primary Tests.ResourceHints.suite,
  -- Source mode's evidence from the committed bundle (`Ix.RoleEvidence.bundleEvidence`), on
  -- the well-founded operations' Init closure without the certificate theorems
  .suite "kernel-bundle-evidence" .primary Tests.Ix.Kernel.BundleEvidence.suite,
  -- AuxGen M1: the canonical flat blocks in Source mode, σ, the alias collapse resolved
  .suite "auxgen-flat-source" .primary Tests.Ix.AuxGen.FlatBlockSource.suite,
  -- AuxGen M7 Q1 (T2): the Source service's tier, an unsafe block's oracle over the answer view,
  -- `withFamily`
  .suite "auxgen-tier-service" .primary Tests.Ix.AuxGen.TierService.suite,
  -- the certification statements on the same fixtures: compile parity, and
  -- the per-root hypotheses and conclusion
  .suite "cert-statement" .primary Tests.Ix.Cert.Statement.suite,
  -- the environment check's persistent read cache: a run from the mapped plan gives the live rows
  .suite "kernel-read-cache" .primary Tests.Ix.Kernel.ReadCache.suite,
  .suite "kernel-record-check" .primary Tests.Ix.Kernel.RecordCheck.suite,
  .suite "kernel-check-lean-targets" .primary Tests.Ix.Kernel.CheckLeanTargets.suite,
  .suite "primitive-address-parity" .primary (Tests.Ix.Kernel.BuildPrimitives.paritySuite
    ++ Tests.Ix.Kernel.BuildPrimOrigs.paritySuite),
  .suite "decompile-unit" .primary Tests.Decompile.unitSuite,
  .suite "tc-unit" .primary (Tests.Tc.Unit.suite ++ Tests.Tc.Substrate.suite
    ++ Tests.Tc.Fixtures.suite ++ Tests.Tc.WhnfTests.suite
    ++ Tests.Tc.InferDefEq.suite ++ Tests.Tc.CheckTests.suite
    ++ Tests.Tc.Roundtrip.unitTests ++ Tests.Tc.IngressMeta.unitTests
    ++ Tests.Tc.CanonicalCheck.suite),
  -- getFileEnv body-inclusion regression guard (IO: loads a fixture file)
  .suiteIO "getfileenv-body" .primary (do return [← Tests.Ix.EnvBody.suite]),
  -- primary runners: quick suites kept as deferred `IO` actions (not
  -- `TestSeq` values) so their setup (Aiur system builds, STARK proofs) does
  -- not run at module initialization for unrelated invocations. All are
  -- seconds-scale: ixvm-tagn about 16 s (measured 2026-10-01), aiur-prove
  -- about 11 s and the rest 2-4 s each (measured 2026-08-05).
  .runner "aiur-rust-syntax" .primary AiurTests.RustSyntax.run,
  -- Reductions no kernel may make beyond Lean's (class methods reduced
  -- without their instance, `numBits ≡ 64`, the `Fin.val` commute): every
  -- probe's closure through the Rust kernel, Ix.Tc and IxC (about 9 s).
  .runner "kernel-fast-paths" .primary Tests.Ix.Kernel.FastPaths.run,
  -- The pure image generator (Ix.Compile.Image) on the prototype's fifteen sub-cases,
  -- with Lean's kernel as the oracle (Tests.Ix.Compile.Image).
  .runner "image-gen" .primary Tests.Ix.Compile.Image.run,
  -- The circuit TagN codec against the host codec (about 16 s).
  .runner "ixvm-tagn" .primary Tests.Ix.IxVM.TagN.runSuite,
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
        let t ← Aiur.Library.core.merge Aiur.Library.byteStream; t.merge Aiur.Library.blake3)
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
  -- Converged heterogeneous aggregation circuit: all ten `ix_aggr` shapes,
  -- driver/cache semantics, and one negative case per broken binding.
  .runner "ix-aggr" .primary Tests.Aggr.convergedSuite,
  -- `.ixes` manifest parser: trailing tree/peaks sections and strictness.
  .runner "ixes-manifest" .primary Tests.Ix.Ixes.suite,

  -- CLI integration tests (ci.yml's lean-test job)
  .runner "cli" (.ci .cli) Tests.Cli.suite,
  .suite "kernel-check-lean-cli" (.ci .cli) Tests.Ix.Kernel.CheckLeanCli.suite,

  -- expensive suites and runners (these require significant RAM)
  .suite "shard-map" (.ci .misc) Tests.ShardMap.suite,
  .suite "compile-determinism" (.ci .compile) Tests.Ix.CompileDeterminism.suite,
  .suite "fidelity-initstd" (.ci .misc) Tests.Ix.CompileFidelity.initStdSuite,
  .suite "fidelity-flt" (.manual "needs FLT built in Benchmarks/Compile") Tests.Ix.CompileFidelity.fltSuite,
  .suite "fidelity-mathlib" (.manual "needs Mathlib in Benchmarks/Compile; about 100 GB") Tests.Ix.CompileFidelity.mathlibSuite,
  .suite "catalog-dedup" (.ci .misc) Tests.Ix.CatalogDedup.suite,
  .suite "truthmines" (.manual "builds the whole TruthMines corpus (network, Mathlib, FLT)") Tests.Ix.TruthMines.buildSuite,
  .suite "truthmines-check" (.manual "checks the whole TruthMines corpus built by `truthmines`") Tests.Ix.TruthMines.checkSuite,
  .suite "truthmines-mini" (.manual "builds the small TruthMines tier (network, Mathlib, FLT)") Tests.Ix.TruthMines.miniSuite,
  .suite "truthmines-validate" (.manual "validates the whole TruthMines corpus") Tests.Ix.TruthMines.validateSuite,
  .suite "truthmines-validate-mini" (.manual "validates the small TruthMines tier") Tests.Ix.TruthMines.validateMiniSuite,
  .suite "rust-canon-roundtrip" (.ci .compilePipeline) Tests.CanonM.rustSuiteIO,
  .suite "serial-canon-roundtrip" (.ci .compilePipeline) Tests.CanonM.serialSuiteIO,
  .suite "parallel-canon-roundtrip" (.ci .compilePipeline) Tests.CanonM.parallelSuiteIO,
  .suite "graph-cross" (.ci .compilePipeline) Tests.Ix.GraphM.suiteIO,
  .suite "condense-cross" (.ci .compilePipeline) Tests.Ix.CondenseM.suiteIO,
  .suite "compile" (.ci .compile) Tests.Compile.compileSuiteIO,
  .suite "decompile" (.ci .decompile) Tests.Decompile.decompileSuiteIO,
  .suite "rust-serialize" (.ci .compilePipeline) Tests.RustSerialize.rustSerializeSuiteIO,
  .suite "ixon-corpus" (.ci .compilePipeline) Tests.Ixon.Corpus.suite,
  .suite "rust-decompile" (.ci .compilePipeline) Tests.RustDecompile.rustDecompileSuiteIO,
  .suite "commit-io" (.ci .misc) Tests.Commit.suiteIO,
  .suite "kernel-ixon-roundtrip" (.ci .misc) Tests.Ix.Kernel.Roundtrip.suite,
  --.suite "kernel-lean-roundtrip" … Tests.Ix.Kernel.RoundtripNoCompile.suite,
  .suite "kernel-tutorial" (.ci .misc) Tests.Ix.Kernel.Tutorial.suite,
  .suite "kernel-check-env" (.ci .misc) Tests.Ix.Kernel.CheckEnv.suite,
  .suite "kernel-check-const" (.ci .misc) Tests.Ix.Kernel.CheckEnv.constSuite,
  .suite "kernel-check-comppoly" (.manual "needs comppoly.ixe at the repository root") Tests.Ix.Kernel.CheckCompPoly.suite,
  .suite "kernel-check-primegaps" (.manual "self-contained, but in no gate yet") Tests.Ix.Kernel.CheckPrimeGaps.suite,
  .suite "kernel-check-tauceti" (.manual "needs tauceti.ixe") Tests.Ix.Kernel.CheckTauCeti.suite,
  .suite "kernel-check-tauceti-reduction" (.manual "self-contained, but in no gate yet") Tests.Ix.Kernel.CheckTauCetiReduction.suite,
  .suite "rust-kernel-build-primitives" (.ci .misc) Tests.Ix.Kernel.BuildPrimitives.suite,
  .suite "rust-kernel-build-prim-origs" (.ci .misc) Tests.Ix.Kernel.BuildPrimOrigs.suite,
  .suite "tc-anon-diff" (.ci .tc) Tests.Tc.AnonDiff.suite,
  .suite "tc-init" (.ci .tc) Tests.Tc.InitScale.suite,
  .suite "tc-tutorial" (.ci .tc) Tests.Tc.TutorialTc.suite,
  .suite "tc-roundtrip" (.ci .tc) Tests.Tc.Roundtrip.suite,
  .suite "tc-ingress-meta" (.ci .tc) Tests.Tc.IngressMeta.suite,
  -- aux_gen on closure-only environments (`ix compile --consts`)
  .suite "aux-gen-closure" (.ci .compilePipeline) Tests.Ix.Compile.AuxGenClosure.suite,
  -- aux addresses do not depend on the compile set (closure vs whole env)
  .suite "canon-closure-aux" (.ci .compilePipeline) Tests.Ix.Compile.AuxGenClosureCanon.suite,
  -- `Ix.Cert.compile` against the IO pipeline and the Rust compiler on Init
  .suite "cert-compile-parity-init" .landing Tests.Ix.Cert.Statement.initSuite,
  .suite "cert-roles-initstd" .landing Tests.Ix.Cert.Statement.rolesInitStdSuite,
  .suite "cert-noctor-initstd" .landing Tests.Ix.Cert.Statement.noCtorInitStdSuite,
  -- A0 safety fixtures (collapse refusal, aux existence, single ownership,
  -- refused fallbacks): both compilers, both kernels, the certified checker
  .suite "aux-cert" (.ci .compilePipeline) Tests.Ix.Compile.AuxCert.suite,
  .runner "aggregate-proof" (.manual "a proof round trip through the production ix_aggr circuit; minutes of proving") Tests.Aggr.proofRoundTrip,
  .runner "kernel-dependencies" (.manual "the IxVM definition-dependency checks alone; `ixvm` runs them too") (do
    match AiurTestEnv.build IxVM.ixVM IxVM.functionGroups with
    | .error e => IO.eprintln s!"IxVM setup failed: {e}"; return 1
    | .ok vm =>
      let tests ← Tests.Ix.IxVM.DefinitionDependencies.tests vm.compiled
      LSpec.lspecIO (.ofList [("kernel-dependencies", [tests])]) []),
  .env "ixvm" (.ci .misc) fun env => do
    let kernelChecks ← kernelChecks env
    -- the kernel CheckEnv smokes .
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
      let evalSeq ← Tests.Ix.IxVM.Eval.tests vmEnv.compiled
      let evalCompiledSeq ← Tests.Ix.IxVM.Eval.compiledTests env vmEnv.compiled
      let evalCommandSeq ← Tests.Ix.IxVM.Eval.commandTests env vmEnv.compiled
      IO.eprintln "[ixvm] eval: dependent, recursive, and neutral-term fixtures"
      let evalDifficultSeq ← Tests.Ix.IxVM.Eval.difficultTests env vmEnv.compiled
      IO.eprintln "[ixvm] eval: generated differential corpus (24 samples)"
      let evalDifferentialSeq ← Tests.Ix.IxVM.Eval.differentialTests env vmEnv.compiled
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
      let paritySeq := kernelChecks.foldl (init := .done) fun s tc =>
        s ++ runParityCase vmEnv.compiled tc
      let fullSeq := [kernelUnitTests, serdeTest].foldl (init := .done)
        fun s tc => s ++ fullVmEnv.runTestCase tc
      -- Shard pipeline: witness built in Rust (thin-frontier claim,
      -- parallel closure walk) and run on the native kernel. Pinned FFT
      -- is the regression signal.
      let shardSeq ← match (← shardCheckEnvCase env) with
        -- Only reachable when the target constant is absent from this
        -- toolchain; a fixture that no longer selects any owned
        -- constants throws instead of skipping.
        | none => pure (LSpec.test "shard pipeline: SKIP (target absent)" true)
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
              s!"Shard pipeline FFT matches: expected 6_227_982_091, got {actual}"
              (actual = 6_227_982_091))
      LSpec.lspecIO
        (.ofList [("ixvm",
          [evalSeq, evalCompiledSeq, evalCommandSeq, evalDifficultSeq, evalDifferentialSeq,
           fullSeq, aiurSeq, arenaSeq, exploitSeq, dependencySeq, paritySeq, shardSeq])]) [],
  .env "validate-aux" (.ci .compilePipeline) runCompileValidateAux,
  -- Cross-compiler differential over the same fixture corpus: pure-Lean
  -- Ix.CompileM per-block vs Rust, root-cause classified (see
  -- Tests.Ix.Compile.AuxGenDiff).
  .env "aux-gen-diff" (.ci .compilePipeline) Tests.Compile.AuxGenDiff.run,
  -- Checked generation capabilities, actual nine-target retries, immutable
  -- Source state and explicit callers; the expensive replay runs once.
  .runner "auxgen-checked-generation" (.ci .compilePipeline) Tests.Ix.AuxGen.CheckedGeneration.run,
  -- The compiler's nested expansion against IxC's nested modeller (SP5):
  -- source order, canonical order, permutation, field kinds and verdicts
  -- on every nested fixture block (Tests.Ix.Compile.NestedAgreement).
  .env "nested-agreement" .landing Tests.Ix.Compile.NestedAgreement.run,
  -- Pass 1 (Ix.Compile.Canon) against the compiler's CondenseM / sortConsts /
  -- nested order on the same fixture corpus, the port fixes' neutrality, and
  -- discovery order against Lean's rec_N (Tests.Ix.Compile.Canon).
  .env "canon-pass1" .landing Tests.Ix.Compile.Canon.run,
  -- The changed set (H1): the change predicate's causes, the set on the
  -- fixture corpus against both compilers' Pass 3 edits (the components the
  -- first hook edits, the published heads, the decompile records' carriers),
  -- and Init+Std empty (Tests.Ix.Compile.ChangedSet).
  .env "changed-set" (.ci .compilePipeline) Tests.Ix.Compile.ChangedSet.run,
  -- Route A B9a: on the same corpus, compiled by `Ix.Cert.compileReport`, the
  -- facts `avoids_unchanged` proves single the set out, and `FirstsAgree` holds
  -- (Tests.Ix.Cert.Statement).
  .env "cert-unchanged" (.ci .compilePipeline) Tests.Ix.Cert.Statement.unchangedCorpus,
  .runner "changed-set-initstd" .landing Tests.Ix.Compile.ChangedSet.runInitStd,
  .env "changed-set-testenv" (.manual "two Rust compiles of the whole test environment; the calibration of the change predicate against the Rust artifact's Pass 3 edits") Tests.Ix.Compile.ChangedSet.runTestEnv,
  .env "decompile-diff" (.ci .compilePipeline) Tests.Compile.DecompileDiff.run,
  -- Non-canonical stored inductive flags: refused by both compilers
  -- (Tests.Ix.Compile.IndFlags).
  .runner "compile-ind-flags" (.ci .compilePipeline) Tests.Ix.Compile.IndFlags.run,
  -- Reserved input: a metadata key or an input name with the reserved component `_ix`,
  -- refused by both compilers, which name the least of several reserved names
  -- (Tests.Ix.Compile.ReservedMetadata).
  .runner "compile-reserved-mdata" (.ci .compilePipeline) Tests.Ix.Compile.ReservedMetadata.run,
  -- Recognition of source auxiliaries against the generators run on the
  -- source recursors: ordinary casesOn/recOn recognized, custom bodies with
  -- their names declined; below/brecOn families authenticated as a whole
  -- (Tests.Ix.Compile.{SourceIdentity,SourceFamily}; fixtures elaborated at run time).
  .runner "aux-source-identity" (.ci .compilePipeline) Tests.Ix.Compile.SourceIdentity.run,
  .runner "aux-source-family" (.ci .compilePipeline) Tests.Ix.Compile.SourceFamily.run,
  -- Single ownership of compiled names: conflicting claims refused by both
  -- compilers (Tests.Ix.Compile.ClaimConflict).
  .runner "compile-claim-conflict" (.ci .compilePipeline) Tests.Ix.Compile.ClaimConflict.run,
  -- The Rust Pass 3 core against Ix.Compile.Image (the images of image-gen's
  -- fixtures, test-only FFI) and against the Lean compiler on their callers (bytes)
  .runner "pass3-rust-parity" (.ci .compilePipeline) Tests.Ix.Compile.Pass3RustParity.run,
  .runner "o11a-decline" (.ci .compilePipeline) Tests.Ix.Compile.O11aDecline.run,
  .runner "o11a-copies" (.ci .compilePipeline) Tests.Ix.Compile.O11aCopies.run,
  .runner "o11a-planning" (.ci .compilePipeline) Tests.Ix.Compile.O11aPlanning.run,
  -- Source ownership of auxiliary claims, independent of arrival order
  -- (Tests.Ix.Compile.ClaimOrder).
  .runner "compile-claim-order" (.ci .compilePipeline) Tests.Ix.Compile.ClaimOrder.run,
  -- Selected closures (Tests.Ix.Compile.{SelectedClosure,ClosureWhole,CheckerSupport,PackUnits}):
  -- closure against whole, checker-support ground, and `ix pack` carrying the reference closure.
  .runner "compiler-selected-closure-e2e" (.ci .compilerClosures) Tests.Ix.Compile.SelectedClosure.run,
  .runner "compile-closure-whole" (.ci .compilerClosures) Tests.Ix.Compile.ClosureWhole.run,
  .suite "compile-closure-phase4" .primary Tests.Ix.Compile.ClosurePhase4.suite,
  .runner "checker-support-regression" (.ci .compilerClosures) Tests.Ix.Compile.CheckerSupport.run,
  .runner "pack-units" (.ci .compilerClosures) Tests.Ix.Compile.PackUnits.run,
  -- Canonicity over twin presentations, exact against the non-canonical
  -- record under the records policy (Tests.Ix.Compile.Twins).
  .runner "twins" .landing Tests.Ix.Compile.Twins.run,
  -- Pass 3's clique tables (plans, rows) are memos: the check mode
  -- (`IX_PASS3_CHECK_PLANS`) at 1, 4 and 32 workers writes the reference's
  -- bytes, with negative controls (Tests.Ix.Compile.PlanCache)
  .runner "pass3-plan-cache" (.ci .compilePipeline) Tests.Ix.Compile.PlanCache.run,
  -- The clique transport wired: every plan of the twins unit, and its rows and
  -- `_ix.src` copies published exactly (Tests.Ix.Compile.Pass3Cliques)
  .runner "pass3-cliques" .landing Tests.Ix.Compile.Pass3Cliques.run,
  -- The clique-ownership cases compiled as units: plans over compiled addresses,
  -- WF8's caller refused by name, values, kernels, the Rust leg; the carried-lemma
  -- units (Tests.Ix.Compile.Clique.OwnershipUnits)
  .runner "clique-ownership-units" .landing Tests.Ix.Compile.Clique.OwnershipUnits.run,
  -- Pass 3 on every fixture family: names, decompile, the certified checker and the
  -- Rust kernel against the kernel-failure record, the images' computation rules,
  -- display names, block failures against the record (Tests.Ix.Compile.Pass3)
  .env "pass3" .landing Tests.Ix.Compile.Pass3.run,
  -- Its evidence and diagnostic tools, one per variable (Tests.Ix.Compile.Pass3Tools)
  .runner "pass3-tools" (.manual "one evidence or diagnostic tool of `pass3`, selected by exactly one PASS3_* variable; records nothing by itself and approves nothing") Tests.Ix.Compile.Pass3Tools.tools,
  -- Lean's own auxiliaries against the ones Ix regenerates, over the twin
  -- families with a canonical reference: the nested-order and packaging
  -- classes fail (Tests.Ix.Compile.Oracle).
  .runner "aux-oracle" .landing Tests.Ix.Compile.Oracle.run,
  -- The Lean compiler's output does not depend on the schedule: the fold at
  -- three widths, the reference schedule both ways and the pipeline at three
  -- worker counts, byte-identical (Tests.Ix.Compile.ScheduleIdentity).
  .runner "compile-schedule-identity" .landing Tests.Ix.Compile.ScheduleIdentity.run,
  -- AuxGen M1: the Source service environment and the flat blocks on Init+Std, measured
  .runner "auxgen-flat-initstd" (.manual "the AuxGen lane's Init+Std measurement of the drivers' Source service (about 2 min), in the compiler gate's suites") Tests.Ix.AuxGen.FlatBlockInitStd.run,
  -- AuxGen checked queries, exact references and fold bytes on the actual fixtures;
  -- the same checked query/table/byte contracts on Init+Std, with the service timed.
  .suite "auxgen-below-ixc" .landing Tests.Ix.AuxGen.BelowIxc.suite,
  .suite "auxgen-below-initstd" (.manual "the AuxGen lane's Init+Std measurement: checked generation and fold bytes under supported asks, with the Source service timed") Tests.Ix.AuxGen.BelowIxc.initStdSuite,
  .runner "auxgen-closure-probe" (.manual "AuxGen M3's coverage probe: the Source service on selected closures of Init+Std, failClosed and traced") Tests.Ix.AuxGen.ClosureProbe.run,
  .runner "auxgen-acceptance-probe" (.manual "AuxGen M5a library check: generated auxiliaries of flat and nested blocks accepted by Source mode, by kind") Tests.Ix.AuxGen.AcceptanceProbe.run,
  -- Source evidence from the committed bundle unblocks the service's inductive blocks
  .runner "bundle-evidence-initstd" (.manual "AuxGen's Source service on Init+Std without the certificate module, at the input's evidence and at the committed bundle's (about 2 min)") Tests.Ix.Kernel.BundleEvidence.runInitStd,
  -- Pure-Lean kernel regression pins against a real .ixe, compiled on
  -- demand (see Tests.Tc.ParityEnv).
  .runner "tc-pins" (.ci .tc) Tests.Tc.Pins.run,
  -- Accelerated-vs-pure reduction differentials over that same real env
  -- (see Tests.Tc.AccelDiff and TcState.noAccel).
  .runner "tc-accel-diff" (.ci .tc) Tests.Tc.AccelDiff.run,
  .runner "admission-hash-diff" .landing Tests.Ix.Kernel.AdmissionHashDiff.run,
  -- the Rust compiler's compile → decompile roundtrip over this binary's
  -- environment (Tests.Ix.RustCompile); before the registry, a special case
  -- that ran alone and skipped every other name
  .env "rust-compile" .landing Tests.Ix.RustCompile.run,
  .runner "rust-compile-coverage" .primary Tests.Ix.RustCompile.coverageControl,
  -- the 132-case, twice-executed `ix_aggr` activation matrix, kept out of the
  -- primary suite and independent of the large environment
  .runner "aggregate-activation" (.manual "a diagnostic matrix (132 cases, run twice)") Tests.Aggr.activationAudit
]

def main (args : List String) : IO UInt32 := do
  -- Namespace-filtered kernel ixon roundtrip diagnostic.
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
  Tests.Registry.run registry get_env! args (required :=
    [("auxgen-checked-generation", "ci:compile-pipeline"),
     ("pass3-plan-cache", "ci:compile-pipeline")])
