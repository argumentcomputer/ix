import Tests.Ix.Ixon
import Tests.Ix.IxonRejectParity
import Tests.Ix.IxonRustParity
import Tests.Ix.IxonSyntax
import Tests.Ix.Claim
import Tests.Ix.Merkle
import Tests.Ix.AssumptionTree
import Tests.Ix.Commit
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
import Tests.Ix.CollectDependencies
import Tests.Ix.Compile.ClosureWhole
import Tests.Ix.Compile.CheckerSupport
import Tests.Ix.Compile.PackUnits
import Tests.Ix.Decompile
import Tests.Ix.Kernel.BuildPrimitives
import Tests.Ix.Kernel.Tutorial
import Tests.Ix.Kernel.FastPaths
import Tests.Ix.Kernel.PrimAddrs
import Tests.Ix.SpecDigestRendering
import Tests.Ix.AiurStatistics
import Tests.Ix.IxVM.Differential
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
import Tests.Ix.ResourceModes
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
import Tests.AggrBindingReuse
import Tests.AggrSemantics
import Tests.Cli
import Tests.CompressionCli
import Tests.Ix.Ixes
import Tests.Ix.EnvBody
import Tests.Ix.MetaEnv
import Tests.Ix.Catalog
import Tests.Ix.ClaimPolicy
import Tests.Ix.ClaimPolicyCli
import Tests.Ix.CatalogDedup
import Tests.Ix.ImportIxe
import Tests.Ix.TruthMinesRecords
import Tests.Registry
import Ix.Common
import Ix.Meta

/-!
  Main host test runner and registry for `IxTests`.
  IxVM circuit-verdict suites live in `Tests/IxVMMain.lean` (`IxVMTests`), and
  manual benchmark/corpus runners live in `Tests/ManualMain.lean` (`IxManualTests`).
-/

open Tests.Registry in
/-- The CI jobs owned by `IxTests` (host primary, CLI, closures, binding-proof,
misc, landing Init+Std, and nightly host sweeps). -/
def ownedJobs : List CiJob :=
  [.cli, .compilerClosures, .bindingProof, .misc, .landingInitStdCli, .nightly]

open Tests.Registry in
/-- Every host `IxTests` entry with its tier (`Tests/Registry.lean`): primary
entries run with no arguments; the others are named, or selected by tier
(`--tier ci:<job>`, `landing`). -/
def registry : List Entry := [
  -- primary suites
  .suite "ffi" .primary Tests.FFI.suite,
  .suite "meta-env" .primary Tests.Ix.MetaEnv.suite,
  .suite "catalog" .primary Tests.Ix.Catalog.suite,
  .suiteIO "claim-policy" .primary Tests.ClaimPolicy.suite,
  .suite "import-ixe" .primary Tests.Ix.ImportIxe.suite,
  .suite "lean-export" .primary Tests.Ix.LeanExport.suite,
  .suite "truthmines-spec" .primary Tests.Ix.TruthMinesRecords.suite,
  -- `concurrently`: the long role and admission checks run at once
  .suiteIO "ixon" .primary (concurrently (Tests.Ixon.suite ++ Tests.Ix.IxonUniverse.suite)),
  .suiteIO "ixon-reject-parity" .primary Tests.Ix.IxonRejectParity.suite,
  .suiteIO "ixon-rust-parity" .primary Tests.Ix.IxonRustParity.suite,
  .suite "role-equations" .primary Tests.Ix.RoleEquations.suite,
  .suite "ixon-syntax" .primary Tests.IxonSyntax.suite,
  .suite "claim" .primary Tests.Claim.suite,
  .suite "merkle" .primary Tests.Merkle.suite,
  .suite "assumption-tree" .primary Tests.AssumptionTree.suite,
  .suite "commit" .primary Tests.Commit.suite,
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
  -- the raw dependency collector (`Lean.collectDependenciesMany`) lists a mutual family once
  .suite "collect-dependencies" .primary Tests.Ix.CollectDependencies.suite,
  -- the formal IxVM program holds no address literal but its specification digest
  .suite "prim-addrs" .primary Tests.Ix.Kernel.PrimAddrs.suite,
  -- every IO byte the IxVM and multi-stark programs read is range-checked
  .suite "io-ingress" .primary Tests.IOIngress.suite,
  -- the role table's wire vectors (Tests/Fixtures/ixon/role-table.tsv), which
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
  -- the resource-mode model (`runR`) and the uncertified mode checker on small run programs
  .suite "resource-modes" .primary Tests.ResourceModes.suite,
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
  -- Pure host checks for binder-data annotation and re-addressing (no IxVM
  -- circuit invocation).
  .runner "ixvm-pw-hints" .primary Tests.Ix.IxVM.PwHints.run,
  .runner "ixvm-binder-data" .primary Tests.Ix.IxVM.BinderData.run,
  -- The sharded differential's attribution on a hand-made report: an isolated
  -- rejection, an interaction set and inconclusive parts stay distinct.
  .runner "ixvm-differential-attribution" .primary Tests.Ix.IxVM.Differential.runAttribution,

  -- CLI integration tests (`host-test-cli`)
  .runner "cli" (.ci .cli) Tests.Cli.suite,
  .suite "compile-determinism" (.ci .cli) Tests.Ix.CompileDeterminism.suite,
  .suite "kernel-check-lean-cli" (.ci .cli) Tests.Ix.Kernel.CheckLeanCli.suite,
  .suite "artifact-compile-cli" (.ci .cli) Tests.Ix.RoleCompile.suite,
  .suite "host-admission-cli" (.ci .cli) Tests.Ix.HostAdmissionCli.suite,
  -- `ix verify` and `ix compress` refuse, through the `ix` binary, each claim the claim
  -- policy refuses by default (`Ix.Cli.ClaimPolicy`), and accept it under its flag
  .runner "claim-policy-cli" (.ci .cli) Tests.ClaimPolicyCli.run,
  -- Compression CLI setup and proof-rejection checks, and the bundled release
  -- keys' acceptance of the formal backends.
  .runner "compression-cli" (.ci .cli) (do
    Tests.CompressionCli.run
    return 0),

  -- `ix prove-binding`, shard proofs that assume the binding, and their
  -- composition with the binding proof file and refusals without it, through
  -- the `ix` binary (`aggregate-binding-reuse` without its two aggregates).
  -- Runs in its own parallel formal CI job (`ci:binding-proof`) on the cached
  -- `ixvm.ixa` artifact with a 64 GiB proving budget.
  .runner "binding-proof-cli" (.ci .bindingProof) Tests.Aggr.BindingReuse.cli,

  -- Misc host suites (`host-test-misc`)
  .suite "catalog-dedup" (.ci .misc) Tests.Ix.CatalogDedup.suite,
  .suite "commit-io" (.ci .misc) Tests.Commit.suiteIO,
  .suite "kernel-tutorial" (.ci .misc) Tests.Ix.Kernel.Tutorial.suite,

  -- Init+Std landing & trusted reader coverage (`host-test-landing`)
  -- `ix compile-lean` on Init+Std: its report checks, the reference digest
  -- (Tests/Fixtures/initstd-reference.txt), and `ix check-lean` on the artifact
  -- with every bound role admitted
  .runner "initstd-reference" (.ci .landingInitStdCli) Tests.Ix.InitStd.reference,
  -- `ix validate-lean` on Init+Std: compile, serde, projection, reader and
  -- decompile fidelity (reusing `.lake/build/initstd-reference.ixe`)
  .runner "fidelity-initstd" (.ci .landingInitStdCli) Tests.Ix.InitStd.fidelity,
  -- The trusted reader (`prepareWith`) accepts the logical records of the closures
  -- the IxVM suites check (`IxVM.consistent`'s `ReadIn`).
  .env "ixvm-reader-coverage" (.ci .landingInitStdCli) Tests.Ix.Kernel.ReaderCoverage.run,

  -- Compiler closures & IxC pins (`host-test-closures`)
  -- auxiliary addresses do not depend on the compile set (closure vs whole env)
  .suite "canon-closure-aux" (.ci .compilerClosures) Tests.Ix.Compile.AuxiliaryClosureCanon.suite,
  .suite "cert-evidence-agreement" (.ci .compilerClosures) Tests.Ix.Cert.Statement.evidenceSuite,
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

  -- Nightly host sweeps (`nightly.yml`: `IxTests --tier ci:nightly`)
  -- Address.blake3, Address.blake3Pure and Address.admissionHash on every
  -- record, blob and the binding of the artifact `initstd-reference` leaves
  -- (253 MB pure-Lean hash sweep; runs nightly after `initstd-reference`).
  .runner "admission-hash-diff-initstd" (.ci .nightly) Tests.Ix.Kernel.AdmissionHashDiff.runInitStd,
  -- Full brute-force exact-sharing oracle (`witness2` 3M-candidate sweep,
  -- 13.7k tied-minima tables, and 400/600-input uniform search sweeps).
  .suiteIO "exact-sharing-full" (.ci .nightly)
    (concurrently (Tests.SharingExact.nightlySuite ++ Tests.SharingUniform.nightlySuite))
]

/-- The host entries that must stay registered once, in their tier
(`Tests.Registry.coverageProblems`): the checks the certification, the
compiler and the proof system's claims rest on. Moving one to the
manual tier, or deleting it, fails `ixtests-registry`; so does a CI tier
with no required entry. -/
def required : List (String × String) := [
  ("cert-statement", "primary"),
  ("ix-aggr", "primary"),
  ("lean-export", "primary"),
  ("kernel-source-ingress", "primary"),
  ("kernel-reader-roundtrip", "primary"),
  ("kernel-bundle-evidence", "primary"),
  ("resource-hints", "primary"),
  ("resource-modes", "primary"),
  ("aiur-statistics", "primary"),
  ("compiler-reports", "primary"),
  ("ground-unit", "primary"),
  ("prim-addrs", "primary"),
  ("io-ingress", "primary"),
  ("role-table-wire", "primary"),
  ("exact-sharing", "primary"),
  ("ixon-reject-parity", "primary"),
  ("ixon-rust-parity", "primary"),
  ("role-equations", "primary"),
  ("ixes-manifest", "primary"),
  ("kernel-record-check", "primary"),
  ("compile-ind-flags", "primary"),
  ("admission-hash-diff", "primary"),
  ("spec-digest-rendering", "primary"),
  ("ixvm-pw-hints", "primary"),
  ("ixvm-binder-data", "primary"),
  ("cli", "ci:cli"),
  ("compile-determinism", "ci:cli"),
  ("kernel-check-lean-cli", "ci:cli"),
  ("artifact-compile-cli", "ci:cli"),
  ("host-admission-cli", "ci:cli"),
  ("compression-cli", "ci:cli"),
  ("claim-policy", "primary"),
  ("claim-policy-cli", "ci:cli"),
  ("binding-proof-cli", "ci:binding-proof"),
  ("cert-evidence-agreement", "ci:compiler-closures"),
  ("canon-closure-aux", "ci:compiler-closures"),
  ("compile-closure-whole", "ci:compiler-closures"),
  ("checker-support-regression", "ci:compiler-closures"),
  ("tc-pins", "ci:compiler-closures"),
  ("kernel-accel-semantics", "ci:compiler-closures"),
  ("kernel-tutorial", "ci:misc"),
  ("initstd-reference", "ci:landing-initstd-cli"),
  ("fidelity-initstd", "ci:landing-initstd-cli"),
  ("ixvm-reader-coverage", "ci:landing-initstd-cli"),
  ("admission-hash-diff-initstd", "ci:nightly"),
  ("exact-sharing-full", "ci:nightly")]

def main (args : List String) : IO UInt32 :=
  Tests.Registry.runScoped "ixtests-registry" .primary true ownedJobs registry required get_env! args
