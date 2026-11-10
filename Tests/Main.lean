import Tests.Ix.Ixon
import Tests.Ix.IxonRejectParity
import Tests.Ix.IxonSyntax
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
import Tests.Ix.Decompile
import Tests.Ix.Kernel.BuildPrimitives
import Tests.Ix.Kernel.CheckCompPoly
import Tests.Ix.Kernel.CheckPrimeGaps
import Tests.Ix.Kernel.CheckTauCeti
import Tests.Ix.Kernel.CheckTauCetiReduction
import Tests.Ix.Kernel.Tutorial
import Tests.Ix.Kernel.FastPaths
import Tests.Ix.Kernel.PrimAddrs
import Tests.Ix.SpecDigestRendering
import Tests.Ix.InstanceSymbols
import Tests.Ix.VMSource
import Tests.Ix.Kernel.Arena
import Tests.Ix.IxVM
import Tests.Ix.AiurStatistics
import Tests.Ix.IxVM.Eval
import Tests.Ix.IxVM.Exploits
import Tests.Ix.IxVM.DefinitionDependencies
import Tests.Ix.IxVM.BindingAnchors
import Tests.Ix.IxVM.BindingFrontier
import Tests.Ix.IxVM.S4Bench
import Tests.Ix.IxVM.TagN
import Tests.Ix.IxVM.Codec
import Tests.Ix.IxVM.UserAxioms
import Tests.Ix.IxVM.DecisionRoles
import Tests.Ix.IxVM.CircuitVerdict
import Tests.Ix.IxVM.Differential
import Tests.Ix.IxVM.Mutator
import Tests.Ix.IxVM.PwHints
import Tests.Ix.Kernel.ReaderCoverage
import Tests.Ix.IOIngress
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
import Tests.AggrBindingReuse
import Tests.AggrToolchains
import Tests.AggrSemantics
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
  .suite "aiur-statistics" .primary Tests.Ix.AiurStatistics.suite,
  .suite "bench-measures" .primary Tests.Ix.BenchMeasures.suite,
  -- the compile's named refusal of ungrounded input (the IO pipeline and the pure compile)
  .suite "ground-unit" .primary Tests.Ix.Compile.GroundRefusal.suite,
  -- the strict readers of the checkers' reports (Tests.Ix.Compile.KernelReport)
  .suite "compiler-reports" .primary Tests.Ix.Compile.KernelReportTests.suite,
  .suite "compiler-lean-reports" .primary Tests.Ix.Compile.LeanReportTests.suite,
  -- selected closures (`collectSelectedDeps`): whole logical units, a
  -- matcher's unit, mutual siblings, checker support from `Role.deps`
  .suite "compiler-selected-closure" .primary Tests.Ix.Compile.SelectedClosure.suite,
  -- the formal IxVM program holds no address literal but its specification digest
  .suite "prim-addrs" .primary Tests.Ix.Kernel.PrimAddrs.suite,
  -- every IO byte the IxVM and multi-stark programs read is range-checked
  .suite "io-ingress" .primary Tests.IOIngress.suite,
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
  -- Reductions no kernel may make beyond Lean's (class methods reduced
  -- without their instance, `numBits ≡ 64`, the `Fin.val` commute): every
  -- probe's closure through IxC.
  .runner "kernel-fast-paths" .primary Tests.Ix.Kernel.FastPaths.run,
  -- Aggregate driver/cache/manifest semantics.
  .runner "ix-aggr" .primary Tests.Aggr.convergedSuite,
  -- `.ixes` manifest parser: trailing tree/peaks sections and strictness.
  .runner "ixes-manifest" .primary Tests.Ix.Ixes.suite,
  -- Non-canonical stored inductive flags and mixed mutual safety: refused by
  -- both Lean drivers and the pure compiler (Tests.Ix.Compile.IndFlags).
  .runner "compile-ind-flags" .primary Tests.Ix.Compile.IndFlags.run,
  -- Differential comparison of Address.blake3, Address.blake3Pure, and
  -- Address.admissionHash across multi-chunk boundaries and an .ixe artifact.
  .runner "admission-hash-diff" .primary Tests.Ix.Kernel.AdmissionHashDiff.run,
  -- `KernelRoleSpec.lean` rebuilt from the specification digest's bytes; mutated
  -- bytes or a mutated file are refused (`IxVM.RoleSpecGen.checkRendering`).
  .runner "spec-digest-rendering" .primary Tests.Ix.SpecDigestRendering.run,
  -- Instance symbols: the structural encoding agrees with the JSON form on every
  -- deployed program (`Aiur.Generic.Instance.symbol`).
  .runner "instance-symbols" .primary Tests.Ix.InstanceSymbols.run,
  -- The public IxVM source agrees with native preparation of the imported
  -- DSL declarations (`IxVM.Check`).
  .env "ixvm-source" .primary Tests.Ix.VMSource.run,

  -- CLI integration tests (ci.yml's lean-test job)
  .runner "cli" (.ci .cli) Tests.Cli.suite,
  .suite "compile-determinism" (.ci .cli) Tests.Ix.CompileDeterminism.suite,
  .suite "kernel-check-lean-cli" (.ci .cli) Tests.Ix.Kernel.CheckLeanCli.suite,
  .suite "artifact-compile-cli" (.ci .cli) Tests.Ix.RoleCompile.suite,
  .suite "host-admission-cli" (.ci .cli) Tests.Ix.HostAdmissionCli.suite,

  -- Claims through the formal IxVM program (`ixvm-proof test` on the claim
  -- artifact; `Tests.Ix.IxVM.Harness`), each verdict pinned: the only
  -- evidence, until the refinement proof lands, that the program rejects
  -- what it must.
  -- Kernel verdicts and exact FFT costs for constants, the binding claim and a shard.
  .env "ixvm-kernel-checks" (.ci .ixvm) Tests.Ix.IxVM.kernelChecks,
  -- The trusted reader (`prepareWith`) accepts the logical records of the closures
  -- the IxVM suites check (`IxVM.consistent`'s `ReadIn`; decision D10).
  .env "ixvm-reader-coverage" (.ci .ixvm) Tests.Ix.Kernel.ReaderCoverage.run,
  -- Prover-authored malformed Ixon, each exploit with its controls.
  .env "ixvm-exploits" (.ci .ixvm) Tests.Ix.IxVM.Exploits.run,
  -- The lean-kernel-arena tutorial fixtures: good accepted, `bad_*` rejected.
  .env "ixvm-arena" (.ci .ixvm) Tests.Ix.Kernel.Arena.run,
  -- The program's TagN codec against the host's (`Ixon.putTagN`/`getTagN`).
  .runner "ixvm-tagn" (.ci .ixvm) Tests.Ix.IxVM.TagN.run,
  -- The program's Ixon codec (`ixon-v4-tests`' vectors) and claim boundary.
  .runner "ixvm-codec" (.ci .ixvm) Tests.Ix.IxVM.Codec.run,
  -- Evaluation claims against Lean's own reduction and generated arithmetic.
  .env "ixvm-eval" (.ci .ixvm) Tests.Ix.IxVM.Eval.run,
  -- Every leaf of a claim's axioms tree type-checked, used or not.
  .runner "ixvm-user-axioms" (.ci .ixvm) Tests.Ix.IxVM.UserAxioms.run,
  -- A decision's `of_decide_eq_*` roles bound by a compiled binding
  -- (`Array.extract_append._proof_1_1`).
  .env "ixvm-decision-roles" (.ci .ixvm) Tests.Ix.IxVM.DecisionRoles.run,
  -- Circular definitions, binding anchors and the lazy binding frontier.
  .runner "ixvm-definition-dependencies" (.ci .ixvm) Tests.Ix.IxVM.DefinitionDependencies.run,
  .runner "ixvm-binding-anchors" (.ci .ixvm) Tests.Ix.IxVM.BindingAnchors.run,
  .runner "ixvm-binding-frontier" (.ci .ixvm) Tests.Ix.IxVM.BindingFrontier.run,
  -- A constant byte out of range is refused.
  .runner "ixvm-io-ingress" (.ci .ixvm) Tests.IOIngress.run,
  -- Execution with every assertion checked gives the circuit's verdict on a witness;
  -- default execution skips the deferred range checks and can accept what the
  -- circuit cannot prove.
  .env "ixvm-circuit-verdict" (.ci .ixvm) Tests.Ix.IxVM.CircuitVerdict.run,
  -- The binder data (D2) a witness carries for the conversion: hand-made records
  -- with known data, the host-side check (coverage, the kernel's values), tampering.
  .runner "ixvm-pw-hints" (.ci .ixvm) Tests.Ix.IxVM.PwHints.run,
  -- A wrong datum is rejected and a missing one a host error, through the program
  -- (runs once the program reads the data).
  .runner "ixvm-pw-circuit" (.ci .ixvm) Tests.Ix.IxVM.PwHints.circuit,
  .env "ixvm-pw-diag" (.manual "why the kernel refuses records of a claim; IX_PW_NAME") Tests.Ix.IxVM.PwHints.diag,
  .runner "ixvm-pw-corpus" (.manual "the binder-data annotator on a compiled corpus; IX_PW_IXE, IX_PW_IXES") Tests.Ix.IxVM.PwHints.corpus,
  -- IxVM against Lean's kernel on a compiled corpus, and an adversarial mutator over
  -- real inductive blocks and recursor records (circuit verdict).
  .env "ixvm-differential" (.manual "a compiled corpus through IxVM and Lean's kernel; IX_DIFF_MODULES, IX_DIFF_LIMIT") Tests.Ix.IxVM.Differential.run,
  .env "ixvm-differential-shards" (.manual "a sharded corpus: an ix check report against Lean's kernel, rejected shards bisected; IX_DIFF_IXE, IX_DIFF_IXES, IX_DIFF_REPORT, IX_DIFF_OUT") Tests.Ix.IxVM.Differential.runShards,
  .env "ixvm-mutator" (.manual "mutated blocks and recursors; IX_MUT_MODULES, IX_MUT_BUDGET, IX_MUT_SEED") Tests.Ix.IxVM.Mutator.run,
  -- Lane s4 measurements (spike S4): declaration costs, a Std shard, the
  -- inductive census and the in-process modeller's records. Not a gate.
  .env "ixvm-s4-bench" (.manual "lane s4 measurements; needs IX_TEST_OUTPUT_DIR") Tests.Ix.IxVM.S4Bench.bench,
  .env "ixvm-s4-census" (.manual "lane s4 inductive census and modeller records") Tests.Ix.IxVM.S4Bench.census,
  .env "ixvm-s4-model" (.manual "lane s4 candidate (a) prototype; needs IX_TEST_OUTPUT_DIR") Tests.Ix.IxVM.S4Bench.modelProbe,
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
  .runner "aggregate-binding-reuse" (.manual "one binding proof file discharges two aggregates, end to end through the `ix` binary; minutes of recursion and about 190 GB, needs `lake build ix`; `binding-proof-cli` runs it without the aggregates") Tests.Aggr.BindingReuse.run,
  .runner "aggregate-toolchains" (.manual "libraries from four Lean toolchains proven with one IxVM key and joined into one catalog root, end to end through the `ix` binary; tens of minutes of proving, needs `lake build ix` and `zstd`; IX_TOOLCHAINS_MAX_RAM sets the aggregate RAM budget in GiB (default 140)") Tests.Aggr.Toolchains.run,
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
  -- Compression CLI setup and proof-rejection checks, and the bundled release
  -- keys' acceptance of the formal backends.
  .runner "compression-cli" (.ci .cli) (do
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
  ("kernel-source-ingress", "primary"),
  ("kernel-reader-roundtrip", "primary"),
  ("kernel-bundle-evidence", "primary"),
  ("resource-hints", "primary"),
  ("aiur-statistics", "primary"),
  ("compiler-reports", "primary"),
  ("ground-unit", "primary"),
  ("prim-addrs", "primary"),
  ("io-ingress", "primary"),
  ("role-table-wire", "primary"),
  ("exact-sharing", "primary"),
  ("ixon-reject-parity", "primary"),
  ("role-equations", "primary"),
  ("ixes-manifest", "primary"),
  ("kernel-record-check", "primary"),
  ("compile-ind-flags", "primary"),
  ("admission-hash-diff", "primary"),
  ("spec-digest-rendering", "primary"),
  ("instance-symbols", "primary"),
  ("ixvm-source", "primary"),
  ("cli", "ci:cli"),
  ("compile-determinism", "ci:cli"),
  ("kernel-check-lean-cli", "ci:cli"),
  ("artifact-compile-cli", "ci:cli"),
  ("host-admission-cli", "ci:cli"),
  ("compression-cli", "ci:cli"),
  ("ixvm-kernel-checks", "ci:ixvm"),
  ("ixvm-reader-coverage", "ci:ixvm"),
  ("ixvm-exploits", "ci:ixvm"),
  ("ixvm-arena", "ci:ixvm"),
  ("ixvm-tagn", "ci:ixvm"),
  ("ixvm-codec", "ci:ixvm"),
  ("ixvm-eval", "ci:ixvm"),
  ("ixvm-user-axioms", "ci:ixvm"),
  ("ixvm-decision-roles", "ci:ixvm"),
  ("ixvm-io-ingress", "ci:ixvm"),
  ("ixvm-circuit-verdict", "ci:ixvm"),
  ("ixvm-pw-hints", "ci:ixvm"),
  ("binding-proof-cli", "ci:compiler-closures"),
  ("canon-closure-aux", "ci:compiler-closures"),
  ("compile-closure-whole", "ci:compiler-closures"),
  ("checker-support-regression", "ci:compiler-closures"),
  ("tc-pins", "ci:compiler-closures"),
  ("kernel-accel-semantics", "ci:compiler-closures"),
  ("kernel-tutorial", "ci:misc"),
  ("initstd-reference", "ci:landing-initstd-cli"),
  ("admission-hash-diff-initstd", "ci:landing-initstd-cli"),
  ("fidelity-initstd", "ci:landing-initstd-cli")]

def main (args : List String) : IO UInt32 :=
  Tests.Registry.run registry required get_env! args
