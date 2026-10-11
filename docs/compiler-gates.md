# Compiler and certification gates

This is the gate and record inventory for the compiler and compiler-certification
lane at `cfe49cb95ee8f0f953e253a4a47a50181dbc390f` (Lean 4.34.1). Update this
inventory when registering a suite or changing its scope. The registrations in
[`Tests/Main.lean`](../Tests/Main.lean), the assertions in the linked test modules,
and the commands in the two CI workflows are the executable definitions.

A byte comparison, a kernel verdict, a source-correspondence check, and a theorem
audit answer different questions. Keep their results separate. In particular,
Lean/Rust agreement does not by itself establish agreement with Lean's source
meaning, and an expected refusal is not an accepted declaration. The theorem
statements and remaining proof obligations belong in
[compiler certification](compiler-certification.md); the compiler's output
contract is in [compiler passes](compiler-passes.md).

## Running and recording a gate

```sh
lake build --wfail Ix IxTests ix kernel-check-ixe
lake test --wfail
lake test --wfail -- canon-clique compiler-reports
lake test --wfail -- --ignored canon-pass1 twins
lake run check-cert
```

The unfiltered `lake test --wfail` runs the primary suites, the file-environment
body check, and primary runners such as `image-gen`. A primary name is selected
without `--ignored`. Ignored suites and ignored runners require `--ignored`;
unknown suite names fail. `--include-ignored <names>` also runs all primary tests.
An unfiltered ignored run includes large library and corpus tests; select the
intended suites explicitly for a package gate.

Keep one log per command with the exact source commit, `lean --version`, command,
exit code, complete summary and any failure inventory. For a native compiler or
certifier, also record the executable and FFI-library hashes, source manifest,
input hashes, benchmark dependency revision and imported artifacts. A source
commit alone does not identify an old executable or a changed import cache.
Check those identities again after a long run. Preserve failure outputs and
separate producer failure from a later provenance-check failure.

Runtime is not a fixed property of a suite. Unless a test explicitly has a
budget, the tables below give its input/work scope, not a timing promise. Measure
the exact invocation, for example with `/usr/bin/time -v`, and retain elapsed
time, maximum RSS, workers, inputs and concurrent box load. The `tc-pins` table
has explicit per-pin budgets; these are regression limits, not microbenchmarks.
Use [benchmarking](benchmarking.md) for performance measurements. A filtered,
quick, sampled or measurement-only run must retain that label in its result.

## Recorded runtime observations

These are observations from the 2026-10-08 landing at
`881c2b86be98ab77fa29d58daef7a6a798a556d7`, not timing guarantees for this or a
later revision. It ran on a shared build server; the receipt does not establish
a quiet machine or record concurrent load. Do not use these observations as a
performance comparison. No tests were repeated to populate this guide.

The following **coarse gate intervals** are differences between whole-second
UTC start markers and the next marker. They include command execution, log
tailing and gate bookkeeping; maximum RSS was not captured by this harness.
The exact receipt is `out/m6-perf-20261008t0802z-int15.log`, SHA-256
`bb9806fbcf420383a5c0a0401ccdc8c0043049642d75e488dc5c7512a9e5d4eb`.
Except where stated, a row is `lake test --wfail -- --ignored <suite>` using
that suite's full default input; the schedule tier and fixture pack defaults
were not reduced.

| Suite or command | Gate interval (m:ss) |
| --- | ---: |
| `pass3-cliques` | 0:32 |
| `validate-lean` | 5:46 |
| `lake test --wfail` (combined primary run) | 5:35 |
| `pass3` | 9:01 |
| `pass3-plan-cache` | 52:59 |
| `twins` | 1:40 |
| `canon-pass1` | 0:21 |
| `clique-transport` | 0:29 |
| `clique-ownership` | 1:42 |
| `aux-oracle` | 1:06 |
| `aux-cert` | 0:57 |
| `validate-lean-nc` | 5:42 |
| `adversarial-matrix` | 0:30 |
| `decompile-diff` | 0:21 |
| `compile-claim-conflict` | 0:13 |
| `compile-claim-order` | 0:15 |
| `compiler-selected-closure-e2e` | 0:46 |
| `o11a-decline` | 0:14 |
| `compile-closure-whole` | 2:02 |
| `compile-caller-independence` | 0:16 |
| `changed-set` | 22:21 |
| `pack-units` | 0:12 |
| `validate-aux` | 0:25 |
| `aux-gen-diff` | 4:25 |
| `rust-decompile` | 0:39 |
| `kernel-ixon-roundtrip` | 1:04 |
| `pass3-rust-parity` | 5:58 |
| `pass3-rust-parity` with `PARITY_FILE=Benchmarks/Compile/CompileInitStd.lean` | 3:44 |
| `lake exe aux-shape-sweep self-check` | 0:02 |
| `lake exe checker-support-regression` | 1:16 |
| `compile` | 7:19 |
| `compile-schedule-identity` | 19:05 |
| `lake run check-cert` (combined lane gate) | 18:52 |
| `lake run check-kernel --with-model` | 3:04 |

The supplemental commands used `/usr/bin/time -v` around each complete
`lake test --wfail -- --ignored <suite>` invocation. Their retained
`out/m6-perf-20261008t0802z/run.log` has SHA-256
`8347a4741a15b89cd4bd4bb74d28ff2e1be776ba269a3343fc31d1061b67682a`.
They have the same shared-server limitation.

| Suite | Elapsed (m:ss.ss) | Maximum RSS (reported kbytes) |
| --- | ---: | ---: |
| `rust-serialize` | 2:23.08 | 27827680 |
| `decompile` | 6:35.39 | 30149392 |
| `canon-closure-aux` | 1:32.74 | 6436604 |
| `ixon-corpus` | 1:37.65 | 27081160 |
| `aux-gen-closure` | 0:15.18 | 6855472 |
| `commit-io` | 0:09.78 | 2814016 |
| `rust-canon-roundtrip` | 0:36.00 | 11721524 |

Individual runtimes and RSS for **every primary suite and runner listed below** remain
unmeasured: the combined primary interval cannot be assigned to its members.
The individual `check-cert` modes likewise have no timings assigned here.
The following registered ignored suites have no per-invocation runtime/RSS
observation in these receipts:

`compile-determinism`, `fidelity-initstd`, `fidelity-flt`, `fidelity-mathlib`, `catalog-dedup`,
`serial-canon-roundtrip`, `parallel-canon-roundtrip`, `graph-cross`, `condense-cross`, `kernel-tutorial`,
`kernel-check-env`, `kernel-check-const`, `kernel-check-comppoly`, `kernel-check-primegaps`, `kernel-check-tauceti`,
`kernel-check-tauceti-reduction`, `rust-kernel-build-primitives`, `rust-kernel-build-prim-origs`, `tc-anon-diff`, `tc-init`,
`tc-tutorial`, `tc-roundtrip`, `tc-ingress-meta`, `tc-pins`, `tc-accel-diff`,
`mathlib-measure`, `dev-census`, `bridge-roundtrip`.

The special `cli`, `rust-compile` and `kernel-roundtrip-ns` diagnostic invocations
also have no runtime observation here. These are explicit measurement gaps,
not zero-duration or completed performance checks.

## Where checks run

[Ordinary CI](../.github/workflows/ci.yml) builds and lints Lean with warnings as
errors and runs release Rust Clippy/check. On non-push events it also runs the
primary tests, code-generation and toolchain checks, CLI and Ixon checks,
Rust formatting and release nextest tests. On push events those additional
checks are skipped and nextest uses `--no-run` to build the test binaries.
The Rust feature set for Clippy/check is
`ix-ffi/parallel,ix-ffi/net,ix-ffi/test-ffi,ixon/sharing-profile`.

[Merge tests](../.github/workflows/merge-tests.yml) divide ignored tests into
named partitions. The location labels below abbreviate those partition names. `Landing`
means the compiler package procedure later in this document; `manual` means the
suite is registered but is not invoked by those CI partitions or that baseline
landing list. A package can require additional manual checks.

### Primary compiler and checker suites

Every row here is included in ordinary primary CI and the full primary landing
run. These tests have assertions or fixtures in the linked source; they do not
have an automatically accepted failure baseline.

| Suite or runner | Input and assertion | Source |
| --- | --- | --- |
| `canon` | Name, universe and expression canonicalization roundtrips and hash controls. | [CanonM](../Tests/Ix/CanonM.lean) |
| `image-alpha-eq` | Exact raw name/level leaves, retained-cache controls and paired metadata in the general image alpha comparator. | [AlphaEq](../Tests/Ix/Compile/AlphaEq.lean) |
| `image-motive-eq` | Motive-slot universe aliases, unequal and unresolved neighbours, colliding parameter caches, universe arity/order and unchanged raw-alpha verdicts. | [MotiveEq](../Tests/Ix/Compile/MotiveEq.lean) |
| `cli-flags` | Long CLI flags parse under their public spelling; escaped spellings are refused beside valid neighbours. | [CliFlags](../Tests/Ix/CliFlags.lean) |
| `canon-clique` | Clique values decide before pinned recursive-argument positions; ties and the collapsing neighbour are checked. | [CanonClique](../Tests/Ix/Compile/CanonClique.lean) |
| `reserved-input` | Reserved input diagnostics select the least offending pretty name; the ordinary-name neighbour succeeds. | [ReservedInput](../Tests/Ix/Compile/ReservedInput.lean) |
| `clique-dag` | DAG helpers agree with the tree helpers on shared terms at different depths, fuel boundaries and fresh-variable streams. | [CliqueDag](../Tests/Ix/Compile/CliqueDag.lean) |
| `rewrite-retry` | Generic callbacks retain the no-site retry; the ordered production-style callback preserves its faithful and in-place results. | [RewriteRetry](../Tests/Ix/Compile/RewriteRetry.lean) |
| `compiler-reports` | Certified JSON reports preserve owning-address alias coverage, declines and blocked outcomes; malformed, incomplete and empty reports fail. | [KernelReportTests](../Tests/Ix/Compile/KernelReportTests.lean) |
| `compiler-index-safety` | Empty packing and out-of-range accesses fail; valid singleton packing and checked updates succeed. | [IndexSafety](../Tests/Ix/Compile/IndexSafety.lean) |
| `compiler-provenance` | Bridge ingress distinguishes referenced aliases from an unrelated alias at the same address. | [BridgeProvenance](../Tests/Ix/Compile/BridgeProvenance.lean) |
| `compiler-bridge-boundaries` | Bridge conversion refuses malformed/unresolved inputs and retains source identity across provisional IDs. | [BridgeBoundaries](../Tests/Ix/Compile/BridgeBoundaries.lean) |
| `compiler-bridge-scopes` | Dependent local scopes, push/pop and exception restoration retain the intended context; invalid scopes are refused. | [BridgeScopes](../Tests/Ix/Compile/BridgeScopes.lean) |
| `compiler-selected-closure` | Selected dependencies close logical units and compiler/checker support, with subset, singleton and fixed-point controls. | [SelectedClosure](../Tests/Ix/Compile/SelectedClosure.lean) |
| `graph-unit` | Expression and declaration references and graph edges match the specified small graphs. | [GraphM](../Tests/Ix/GraphM.lean) |
| `condense-unit` | SCC partitions, representatives and block-reference edges on small graphs. | [CondenseM](../Tests/Ix/CondenseM.lean) |
| `aux-gen-unit` | Expression, universe, recursor and source-auxiliary helper controls. | [ExprUtilsTests](../Tests/Ix/AuxGen/ExprUtilsTests.lean), [LevelsTests](../Tests/Ix/AuxGen/LevelsTests.lean), [RecursorTests](../Tests/Ix/AuxGen/RecursorTests.lean), [AuxSourceTests](../Tests/Ix/AuxGen/AuxSourceTests.lean) |
| `ground-unit` | Grounding helper controls. | [GroundTests](../Tests/Ix/GroundTests.lean) |
| `exact-sharing`, `exact-sharing-ffi` | Exact, uniform and tiered sharing controls; the FFI suite compares Lean/Rust bytes. | [SharingExact](../Tests/Ix/SharingExact.lean), [SharingUniform](../Tests/Ix/SharingUniform.lean), [SharingTiered](../Tests/Ix/SharingTiered.lean), [SharingExactFFI](../Tests/Ix/SharingExactFFI.lean) |
| `source-contract` | Source-contract resolution and driver behaviour; syntax/import checks also elaborate when Main is built. | [SourceContract](../Tests/Ix/SourceContract.lean), [Driver](../Tests/Ix/SourceContract/Driver.lean) |
| `bench-measures` | Benchmark measurement helper controls. | [BenchMeasures](../Tests/Ix/BenchMeasures.lean) |
| `prim-addrs`, `primitive-address-parity` | Primitive address checks and Lean/Rust primitive/original construction parity. | [PrimAddrs](../Tests/Ix/Kernel/PrimAddrs.lean), [BuildPrimitives](../Tests/Ix/Kernel/BuildPrimitives.lean), [BuildPrimOrigs](../Tests/Ix/Kernel/BuildPrimOrigs.lean) |
| `kernel-reader-roundtrip` | Compiled fixture closure through the certified reader and output translation, compared with the source translation; shape, pin and tamper controls. | [ReaderRoundtrip](../Tests/Ix/Kernel/ReaderRoundtrip.lean) |
| `kernel-read-cache` | Live and persisted read plans produce the same record rows; a different plan version is not reused. | [ReadCache](../Tests/Ix/Kernel/ReadCache.lean) |
| `decompile-unit` | Metadata-share scopes, original-head recovery and invalid-reference controls. | [Decompile](../Tests/Ix/Decompile.lean) |
| `tc-unit` | Kernel substrate, reduction, inference, declaration checks, ingress, roundtrip and canonical-order controls. | [Main's exact component list](../Tests/Main.lean), [Tc tests](../Tests/Ix/Tc/) |
| `image-gen` (runner) | Prototype source/canonical blocks: Lean-kernel acceptance of generated images, rules and rewritten definitions, plus the no-lift and wrong-order negative controls. | [Image](../Tests/Ix/Compile/Image.lean) |

The adjacent `ffi`, `ixon`, `ixon-syntax`, `import-ixe`, `catalog`, `meta-env`,
`getfileenv-body` and `commit` primary tests also run in the unfiltered primary
gate. Their registrations and assertions are in
[Main](../Tests/Main.lean), [FFI](../Tests/FFI.lean),
[Ixon](../Tests/Ix/Ixon.lean), [IxonSyntax](../Tests/Ix/IxonSyntax.lean),
[ImportIxe](../Tests/Ix/ImportIxe.lean), [Catalog](../Tests/Ix/Catalog.lean),
[MetaEnv](../Tests/Ix/MetaEnv.lean), [EnvBody](../Tests/Ix/EnvBody.lean) and
[Commit](../Tests/Ix/Commit.lean). `cli` and `rust-compile` are special top-level
dispatches, not ignored-suite names: `lake test --wfail -- cli` checks the CLI;
`lake test --wfail -- rust-compile` runs the Rust compile/decompile diagnostic.

### Ignored compiler suites and runners

Run each name with `lake test --wfail -- --ignored <name>`. A record mentioned
below is described in the record section. All other expected outcomes are
assertions in the test source; changing them requires a reviewed test change,
not an automatic re-record.

| Name | Units and assertion | Records | Placement |
| --- | --- | --- | --- |
| [`rust-canon-roundtrip`, `serial-canon-roundtrip`, `parallel-canon-roundtrip`](../Tests/Ix/CanonM.lean) | Imported test environment: Rust, serial Lean and parallel Lean canonicalization roundtrips. | None. | Compile pipeline; Landing additionally runs `rust-canon-roundtrip`. |
| [`graph-cross`](../Tests/Ix/GraphM.lean), [`condense-cross`](../Tests/Ix/CondenseM.lean) | Imported environment: Lean/Rust reference graphs and SCC results agree. | None. | Compile pipeline. |
| [`compile`](../Tests/Ix/Compile.lean) | Imported environment through both compilation implementations; compare compiled constants and metadata. | None. | Compile; Landing. |
| [`decompile`](../Tests/Ix/Decompile.lean) | Compile/decompile roundtrip and metadata-share parity. | None. | Decompile; Landing. |
| [`rust-serialize`](../Tests/Ix/RustSerialize.lean) | Rust serialization/deserialization roundtrip, compared with Lean serialization. | None. | Compile pipeline; Landing. |
| [`ixon-corpus`](../Tests/Ix/IxonCorpus.lean) | Whole imported environment: Rust compile bytes roundtrip through the pure Lean codec and agree with the Rust value parser. | No stored failure record. | Compile pipeline; Landing. |
| [`rust-decompile`](../Tests/Ix/RustDecompile.lean) | Serialized Rust compile/decompile pipeline; every reconstructed source constant's hash agrees. | None. | Compile pipeline; Landing. |
| [`validate-aux`](../Tests/Ix/Compile/ValidateAux.lean) | Shared aux-heavy fixture closure: regeneration, emission, no ephemeral leakage, class canonicity, both decompile paths and nested detection. | Fixture assertions. | Compile pipeline; Landing. |
| [`aux-gen-diff`](../Tests/Ix/Compile/AuxGenDiff.lean) | Per-block drift, nested expansion, selected generated patches and plans; full sequential/parallel driver parity, including metadata and hints. Individual auxiliary/red inventory buckets are diagnostic, not the whole acceptance predicate. | Inline kind filters and assertions. | Compile pipeline; Landing. |
| [`aux-source-identity`](../Tests/Ix/Compile/SourceIdentity.lean) | Actual source `casesOn`/`recOn` recognition on mutual/Prop controls; custom definitions with different types or the standard type and a different value. Applicable unguarded rewrites must be declined by production dispatch, while standard-body neighbors still optimize. The primary `aux-source-identity-unit` suite checks positional universes, open expressions and cache collisions. | No allowed mismatches. This does not yet gate custom-helper publication. | Compiler passes; Landing. |
| [`decompile-diff`](../Tests/Ix/Compile/DecompileDiff.lean) | Aux-heavy closure: source reconstruction and bidirectional coverage; all gated plain/aux/replay buckets must be zero. | None. | Compile pipeline; Landing. |
| [`aux-gen-closure`](../Tests/Ix/Compile/AuxGenClosure.lean) | Selected auxiliary and mutual-definition closures, Rust kernel checks, and packing an unstored-original case. | Inline success/refusal controls. | Compile pipeline; Landing. |
| [`canon-closure-aux`](../Tests/Ix/Compile/AuxGenClosureCanon.lean) | Completed/raw fixture closures against a reference compile, plus packed roots; raw incomplete-family refusals are explicit. | Inline refusal expectations. | Compile pipeline; Landing. |
| [`aux-cert`](../Tests/Ix/Compile/AuxCert.lean) | Standalone reproductions and neighbours: both CLIs, byte identity, all three checker legs, required/forbidden names. Default is local selected closure; `AUX_CERT_WHOLE=1` adds whole/local correspondence. | `AuxCert.fixtures`. | Compile pipeline; Landing. |
| [`canon-pass1`](../Tests/Ix/Compile/Canon.lean) | Shared fixture closure: actual/pure condensation, member classes, nested expansion/order/permutation, comparator controls and representative selection. | Inline assertions; no accepted mismatch record. | Compiler passes; Landing. |
| [`twins`](../Tests/Ix/Compile/Twins.lean) | All twin presentations: Lean/Rust addresses, no refusals, exact presentation-difference set after the suite's generated-name matching. | `NonCanonicalDefault.nonCanonical`. | Compiler passes; Landing. |
| [`clique-transport`](../Tests/Ix/Compile/Transport.lean) | Clique presentations: transport against Lean's encoding, Lean-kernel acceptance, order/recovered-specification and ownership controls. | `NonCanonical.transportOracle`; explained residual causes. | Compiler passes; Landing. |
| [`aux-oracle`](../Tests/Ix/Compile/Oracle.lean) | Block twins: regenerated auxiliaries against Lean's canonical presentation, including canonical-presentation checks. Unexpected, packaging and nested-order differences fail. | Oracle classes; relevant `NonCanonicalDefault` entries. | Compiler passes; Landing. |
| [`pass3`](../Tests/Ix/Compile/Pass3.lean) | AuxCert, image, definitional/PJ-pass fixtures, twins and aux corpus: complete names/refusals, decompilation, three checkers, compiled computation rules and display names. | `Pass3Kernels` tables and `NonCanonical.nonCanonicalPasses`. | Compiler passes; Landing. |
| [`pass3-cliques`](../Tests/Ix/Compile/Pass3Cliques.lean) | Clique-family closure: plans, names, decompilation, three checker legs, value pins and exact twin differences. | `NonCanonical.nonCanonicalOn`. | Compiler passes; Landing. |
| [`o11a-decline`](../Tests/Ix/Compile/O11aDecline.lean) | Withheld size instance and other side conditions: recorded decline cause, untouched surrounding behaviour and valid neighbours. | Inline cases/causes. | Compiler passes; Landing. |
| [`compile-caller-independence`](../Tests/Ix/Compile/CallerIndependence.lean) | Logical units with dependents versus unrelated constants: same `Named` and compiler records; explicit on-demand-auxiliary and refused-caller controls. | `expectedFailures`, `cliqueCallers`. | Compiler passes; Landing. |
| [`validate-lean`](../Tests/Ix/Compile/ValidateLean.lean) | Standalone fixtures through `ix validate-lean --local`: exact phase verdicts, failing counts, phase-9 value counts and skip controls. | `expected`, `pins`, `phase9Pins`, `phase9Controls`, `leanRejects`. | Compiler validation; Landing. |
| [`validate-lean-nc`](../Tests/Ix/Compile/ValidateLeanNC.lean) | Twin/prototype files: differing auxiliaries/images must be classified by the actual validator; unexplained and missing record coverage fail. | `defects`, default noncanonical entries and `ValidateLean` phase-4 pins. | Compiler validation; Landing. |
| [`adversarial-matrix`](../Tests/Ix/Compile/AdversarialMatrix.lean) | Forged associations, types, rules, values, provenance and missing dependencies: actual refusals beside accepted neighbours or a reasoned not-applicable row. | Inline case/label table, not a failure allowlist. | Compiler validation; Landing. |
| [`compile-schedule-identity`](../Tests/Ix/Compile/ScheduleIdentity.lean) | Twins and aux corpus: sequential, wave 1/2/4/16/32 and full pipeline 1/4/16; identical serialized environments, complete source emission and refusal results. `SCHED_LEGS=quick` is only a development subset. | None. | Compiler scheduling; Landing uses full tier. |
| [`compile-claim-conflict`](../Tests/Ix/Compile/ClaimConflict.lean) | Direct claim/merge APIs and a constructed conflicting closure: identical reclaims succeed, competing claims fail consistently across both compilers and Lean drivers. | Exact diagnostics in source. | Compiler scheduling; Landing. |
| [`compile-claim-order`](../Tests/Ix/Compile/ClaimOrder.lean) | Artificial arrival-order changes and source-family metadata: ownership follows source provenance. | Inline expected ownership/refusals. | Compiler scheduling; Landing. |
| [`changed-set`](../Tests/Ix/Compile/ChangedSet.lean) | Pass3/twin/clique units and Init+Std, at 1 and 32 workers: identical bytes/records, address and image/clique/inline/reserved-name coverage. | `initStdRejected` coverage sample; optional CLI record comparison. | Compiler records, parity and pack; Landing. |
| [`pass3-rust-parity`](../Tests/Ix/Compile/Pass3RustParity.lean) | Pass3 units, ownership cliques, O11a declines and corpus: equal named records excluding synthetic `Muts` entries, compile-failure names and noncanonical `(name, cause)` pairs; Rust pack bytes against Lean's closure oracle. | No accepted parity differences in the checked scope. | Compiler records, parity and pack; Landing fixtures and separate Init+Std file. |
| [`pack-units`](../Tests/Ix/Compile/PackUnits.lean) | Pack fixture: reference closure rather than the logical unit, retained constant bytes, correct root, reserved-name coverage and Lean pack oracle. Optional stored artifacts extend the run. | Inline roots and neighbours. | Compiler records, parity and pack; Landing. |
| [`clique-ownership`](../Tests/Ix/Compile/CliqueOwnership.lean) | Both member orders of user packing-shaped values/binders/relations: kernel-checked transport and value-sensitive probes; `mustTransport` controls reject gratuitous declines. | `cases`, probe values and `mustTransport`. | Compiler records, parity and pack; Landing. |
| [`clique-values-inverse`](../Tests/Ix/Compile/InverseRecursor.lean) | Twenty controls: inverse direction, malformed/incorrect permutations, kernel-checked dependent neighbour, a well-typed wrong closed permutation rejected by phase-9 values, every member/reached recursor of the ordinary SM.P0 compile, and an actual `List.rec` universe swap with its unchanged neighbour through the image reader and kernel-checked inverse definition; collapsed associations are refused. Values are explicitly relative to the stored image's inverse correspondence, not an inverse proof. | No rerecord; existing `ValidateLean.phase9Pins` remain strict and require reviewed updates if observed counts change. | Manual; required for the inverse-bridge package. Runtime/RSS unmeasured. |
| [`pass3-plan-cache`](../Tests/Ix/Compile/PlanCache.lean) | Sequential/wave runs with recomputed plan/view/image-cache hits: same bytes/failures, nonvacuous cache coverage, corrupted-entry controls. | None. | Compiler plan cache; Landing. |
| [`compiler-selected-closure-e2e`](../Tests/Ix/Compile/SelectedClosure.lean) | Selected versus whole output: complete named metadata, emission/refusal and decompile coverage, actual owning-record acceptance, subset-order bytes and Lean/Rust parity. | Inline fixture assertions. | Compiler closure and corpus; Landing. |
| [`compile-closure-whole`](../Tests/Ix/Compile/ClosureWhole.lean) | Init+Std selected roots versus whole compile: closed logical units, emitted names, identical `Named` entries and introduced references; local collapse fixture. | Inline root list; optional stored `CLOSURE_WHOLE_ON`. | Compiler closure and corpus; Landing. |
| [`compile-determinism`](../Tests/Ix/CompileDeterminism.lean) | Mutual fixture and Batteries: two independent CLI processes must write the same file SHA-256. | None. | Manual. |
| [`fidelity-initstd`, `fidelity-flt`, `fidelity-mathlib`](../Tests/Ix/CompileFidelity.lean) | Library `ix validate` reports must be nonempty, passed and have zero total failures, with successful process exit. | No expected-failure table. | InitStd: Miscellaneous; FLT/Mathlib: manual. |
| [`dev-census`](../Tests/Ix/Compile/DevCensus.lean) | Pass3 fixtures and Init+Std: reconstructed development calls, executable/instrumented-copy comparison, conditional core comparison, depths/levels and typing measurements. See the coverage limits below. | No new acceptance record. | Manual lane census. |
| [`bridge-roundtrip`](../Tests/Ix/CompileCert/BridgeRoundTrip.lean) | BlockDefs source/bridge export comparison ignoring hints, with at least one reader match; size-bounded Init+Std term comparison; moved-name/shifted-level negative controls. See the coverage limits below. | Inline controls. | Manual lane gate. |
| [`mathlib-measure`](../Tests/Ix/Compile/MathlibMeasure.lean) | `M1G_PHASE=compile`, `classify`, or `kernels`: retain library compile/changed-name records and checker coverage. It is measurement tooling, not a meaning theorem or substitute for library byte gates. | Supplied old/new artifacts and measured TSVs. | Manual. |

`pass3-rust-parity` reports synthetic `Muts` counts and whole-file
`BYTE-IDENTICAL` or `files differ` as diagnostics; neither determines its exit
verdict. The separate
`cmp`/`ALIGNED` library legs below enforce whole-file byte identity.
It defaults to at most **10 pack roots per unit**, with explicit
roots always included; the compiler comparison itself covers the whole selected
unit. `PARITY_FILE=Benchmarks/Compile/CompileInitStd.lean` changes the compiler
input to that whole environment. A run with `PARITY_PACK_MAX=0` and five explicit
roots must be reported as a five-root pack check. The current landing defaults
leave `PARITY_PACK_MAX` and `PARITY_PACK_ROOTS` unset. `pack-units` separately uses
`PACK_UNITS_MAX=2000` for its fixture and `PACK_UNITS_IXE_MAX=10` for large stored
artifacts. These bounds are coverage limits, not runtime budgets.

`dev-census` compares the memo-free core only for developments below 20,000
measured nodes. Typability is reported but is absent from the failure predicate;
its positive and negative typing controls still must pass. Caught fixture
compile refusals and the Init+Std compiler error branch are printed without
adding a problem. There is no minimum unit/development count. Retain and inspect
unit, development, core-checked, refused and untypable counts alongside exit
status; the census does not prove the general development-domain theorem.

`bridge-roundtrip` counts two export declines as equal and compares successful
fixture exports without hints. It requires a nonzero reader-match count, not a
match for every exported declaration. Init+Std terms at or above the 1,000,000
node tree cap are counted as skipped and excluded from its differing count.
Retain matched, declined and skipped counts; zero differences does not establish
complete reader coverage or acceptance of every term.

### Adjacent kernel and artifact checks

These registrations matter when a change crosses compiler output, ingress or
serialization. See [kernel verification](kernel.md) for the certified checker
and its trust/audit policy.

| Name | Assertion and input | Placement |
| --- | --- | --- |
| [`kernel-ixon-roundtrip`](../Tests/Ix/Kernel/Roundtrip.lean) | Compiled imported environment through Rust-kernel ingress/egress and roundtrip comparison. | Miscellaneous; Landing. |
| [`kernel-tutorial`](../Tests/Ix/Kernel/Tutorial.lean) | Registered good/bad tutorial declarations through compilation and Rust checking. | Miscellaneous. |
| [`kernel-check-env`, `kernel-check-const`](../Tests/Ix/Kernel/CheckEnv.lean) | Full imported environment or selected focus constants through the Rust checker. | Miscellaneous. |
| [`rust-kernel-build-primitives`](../Tests/Ix/Kernel/BuildPrimitives.lean), [`rust-kernel-build-prim-origs`](../Tests/Ix/Kernel/BuildPrimOrigs.lean) | Primitive and original-construction checks. | Miscellaneous. |
| [`tc-anon-diff`](../Tests/Ix/Tc/AnonDiff.lean), [`tc-init`](../Tests/Ix/Tc/InitScale.lean) | Executable Lean/Rust anonymous verdict parity on selected closures; `IX_TC_IXE` opts into a supplied stored artifact. | Tc kernel. |
| [`tc-tutorial`](../Tests/Ix/Tc/TutorialTc.lean) | Pure-Lean checker on tutorial cases, with the source-listed renaming/malformed-FFI exclusions. | Tc kernel. |
| [`tc-roundtrip`](../Tests/Ix/Tc/Roundtrip.lean), [`tc-ingress-meta`](../Tests/Ix/Tc/IngressMetaTests.lean) | Anonymous structural and metadata roundtrips, and metadata ingress controls. | Tc kernel. |
| [`tc-pins`](../Tests/Ix/Tc/Pins.lean), [`tc-accel-diff`](../Tests/Ix/Tc/AccelDiff.lean) | Per-pin timeout regressions and accelerated versus pure reduction. Slow pins require `IX_PINS_SLOW=1`. | Tc kernel; slow opt-in manual. |
| [`kernel-check-comppoly`](../Tests/Ix/Kernel/CheckCompPoly.lean), [`kernel-check-tauceti`](../Tests/Ix/Kernel/CheckTauCeti.lean) | Exact focus constants in supplied `comppoly.ixe` or `tauceti.ixe`. | Manual. |
| [`kernel-check-primegaps`](../Tests/Ix/Kernel/CheckPrimeGaps.lean), [`kernel-check-tauceti-reduction`](../Tests/Ix/Kernel/CheckTauCetiReduction.lean) | Self-contained reducer-facing fixtures through both executable kernels. | Manual. |
| [`catalog-dedup`](../Tests/Ix/CatalogDedup.lean), [`commit-io`](../Tests/Ix/Commit.lean) | Catalog deduplication and commit I/O integration assertions. | Miscellaneous; Landing additionally runs `commit-io`. |

`kernel-roundtrip-ns=A,B` is a special namespace-filtered roundtrip diagnostic.
`kernel-lean-roundtrip` is commented out in the registration table and is not an
available suite. Do not report it as run.

## Compiler-certification gate

`lake run check-cert` is the dedicated lane gate; it is not an ignored
`IxTests` suite. Its complete command list is in
[`lakefile.lean`](../lakefile.lean). It runs in merge tests' **Certified kernel**
partition and in both compiler and lane landings.

It strictly builds [`Ix.CompileCert.Audit`](../Ix/CompileCert/Audit.lean), the
executables and the listed test modules, then runs these
[`compile-cert-c1`](../Tests/Ix/CompileCert/Run.lean) modes:

| Modes | Coverage |
| --- | --- |
| `direct`, `blocks`, `groups`, `universes`, `expressions` | Direct correspondence and malformed association/block/group/universe/expression controls. |
| `source-install`, `source-models`, `source-normalized`, `source-coverage`, `source-projection-semantics`, `indexed` | Source installation, models, normalization, coverage, projections and indexed cases. |
| `projection-lowering`, `strong`, `sharing`, `strong-pins`, `strong-indexed` | Projection receipts, strong-model cases, sharing, regenerated source pins and indexed strong cases. |
| `compiled`, `changed`, `wplus-cost`, `changed-values` | Actual compiled artifacts, changed declarations, W+ fold/cost controls and value-row inputs. |
| `projection-support`, `strong-plan`, `strong-changed`, `strong-global`, `strong-changed-values` | Support and planned/executed strong cones, changed-value inclusion and global/cover controls on the generated artifacts. |

The script also invokes `compile-certify` on the produced BlockDefs, ChangedDefs
and changed-values artifacts: ordinary certification, `--strong`, zero row
budget, `--strong-plan`, `--refold`, and value-row scenarios. Finally it runs
`HelperNames`, `InstalledCaps`, `InstalledFields`, `InstalledRules`, `SourceBasis`
and `Support` with `lean --run`, and elaborates `AnnotEntry`, `AnnotNatOps`,
`AnnotReduceOps`, `AnnotSupport`, `InstalledImage`, `Telescope` and `ValueReceipt`.
Logs and generated fixtures are retained under `.lake/build/compile-cert`.

Every subprocess must exit successfully; each runtime check must print a nonempty summary. Review the
`[cert-audit]` root/axiom output as well as the test summaries. Preserve the
existing audit roots and permitted axiom sets; a changed audit is a proof/trust
review, not a failure baseline to regenerate indiscriminately.

For a library run, invoke the actual certifier separately:

```sh
lake build --wfail compile-certify
lake exe compile-certify --file Benchmarks/Compile/CompileInitStd.lean \
  /path/to/initstd-a3.ixe out/initstd-cert
lake exe compile-certify --file Benchmarks/Compile/CompileInitStd.lean \
  /path/to/initstd-a3.ixe out/initstd-strong --strong
```

Use the corresponding Mathlib source/artifact for a separately scheduled
Mathlib run. At this revision `--strong` includes value-level changed checks by
default; `--strong-changed` is an enabling alias. A plain invocation runs W, not
S. `--strong-plan` does not run S and emits no S verdict. Preserve per-name and
per-address classes, unsupported, blocked, rejected, missing and not-reached
counts; a process exit of zero alone is not an assertion that every source name
was certified. `--strong-roots`, `--strong-every` and cone budgets must be stated
in the result. See [the CLI definition](../Ix/CompileCert/CertifierMain.lean) and
[certification](compiler-certification.md) for their precise scope.

## Exact records and re-recording

A changed fixture, compiler, toolchain, checker or harness can change a record
for different reasons. Keep the old log/artifact, identify the cause per affected
name or class, and review the delta before editing the record. An unexpected
pass can indicate a stale row; it is not permission to delete unexplained rows.
Keep valid neighbours and coverage assertions. Do not replace named outcomes
with counts unless that record's existing semantics explicitly permits it.

| Record | What is checked; update path |
| --- | --- |
| [`NonCanonicalDefault.lean`](../Tests/Ix/Compile/NonCanonicalDefault.lean) `nonCanonical` | Default twin difference keys `(fixture, presentation A, presentation B, constant)` are exact in both directions. Rows also retain cause, addresses, source difference and kernel evidence. Generate suggestions with `twins`; inspect and edit only explained rows. |
| [`NonCanonical.lean`](../Tests/Ix/Compile/NonCanonical.lean) `transportOracle`, `nonCanonicalPasses`, `nonCanonicalOn` | Transport oracle/residual classification; default cause classification consults the pass/clique records; `pass3` checks pass-fixture differences and their address evidence, and `pass3-cliques` checks clique differences both ways. The removed legacy compiler record is history, not a current mode to regenerate. Run `clique-transport`, `twins`, `pass3` and `pass3-cliques` as relevant; review suggested rows/term logs. |
| [`Pass3Kernels.lean`](../Tests/Ix/Compile/Pass3Kernels.lean) `table` | Per unit/mode/checker/message class: exact names or counts. `metaOnly` requires certified acceptance; `varies` additionally relies on anonymous acceptance and the documented variability rule. `mayBeEmpty` is restricted to a varying row with an explicit cause. Use retained-output rechecks and the emitter below. |
| `Pass3Kernels.compileFailures`, `switchOnRefusals`, `decompileKnown` | Compile-root/refusal names and diagnostic fragments, dependent failures, and decompile exceptions are distinct from checker rows. Unrecorded or stale entries fail their checks. `PASS3_EMIT_FAILURES=1` prints root suggestions; classify and review them, including image-refusal rows. |
| [`ValidateLean.lean`](../Tests/Ix/Compile/ValidateLean.lean) `expected`, `pins`, `phase9Pins`, `phase9Controls`, `leanRejects` | Per-fixture phase failures and exact detail counts; transported-clique value counts; nonvacuous skips; source files rejected by Lean. Run with `VALIDATE_LEAN_KEEP`; inspect JSON/details and edit with the cause. There is no automatic updater. |
| [`ValidateLeanNC.lean`](../Tests/Ix/Compile/ValidateLeanNC.lean) `defects` | Named defect classification, existing noncanonical-record coverage and validator phase outcomes. Run `validate-lean-nc`; unexplained/missing coverage must be resolved, not recorded as a generic success. No automatic updater. |
| [`AuxCert.lean`](../Tests/Ix/Compile/AuxCert.lean) `fixtures` | Compile/refusal/xfail result, required diagnostic substring, named checker failures or exact uniform counts, and required/forbidden output names. A named expected failure that passes is stale. Preserve owning-record certified verdicts and the local/whole scope. `AUX_CERT_FAILURES` dumps rows; reviewed edits only. |
| [`Oracle.lean`](../Tests/Ix/Compile/Oracle.lean) `classify`, `recordedCause` | Semantic exception classes and same-family default record lookup, not a pinned total exception count. `UNEXPECTED`, `PACKAGING` and `NESTED-ORDER` fail. Run `aux-oracle`; do not expand classes just to accept a new mismatch. |
| [`ChangedSet.lean`](../Tests/Ix/Compile/ChangedSet.lean) `initStdRejected` | Historical twelve-name-fragment coverage sample: each is still claimed as transported/carried. This identifier is not a current claim that W+ rejects those names. Optional `CHANGED_SET_INITSTD` compares the entire CLI record byte for byte. Regenerate the CLI sidecar and run the comparison below; review sample changes manually. |
| [`CallerIndependence.lean`](../Tests/Ix/Compile/CallerIndependence.lean) `expectedFailures`, `cliqueCallers` | Explicit independence/refused-caller cases; stale expected failures fail. Run the whole suite and explain any edit. |
| [`CliqueOwnership.lean`](../Tests/Ix/Compile/CliqueOwnership.lean) `cases` | Source values, recursive-call oracles and mandatory-transport neighbours. They are semantic test inputs, not observations to overwrite after a failure. |
| [`AdversarialMatrix.lean`](../Tests/Ix/Compile/AdversarialMatrix.lean) case/cited-label/not-applicable tables | Each applicable row has a rejected negative and accepted neighbour or cited check; missing cited labels and uncovered rows fail. The separately cited `clique-ownership` suite must also run. No re-record command: add a checked case or justify a precise not-applicable reason. |
| Corpus `--expected FILE` | JSON rows contain exact `caseId`, `mode`, `phase`, complete `diagnostic` and nonempty `cause`. Duplicate/absent cases and invalid phases fail; a pass makes an expected failure stale. Infrastructure errors cannot be excused. Produce diagnostics with the corpus driver, then write/review the JSON and rerun. No automatic acceptance generator. |
| [`Ix/CompileCert/Audit.lean`](../Ix/CompileCert/Audit.lean) and imported audit manifests | Exact theorem/dependency and runtime audit roots. Run `lake run check-cert`; a new theorem is registered with its measured permitted axiom set. Preserve existing roots and explain every trust-surface change. |
| [`SourceNatOpPinData.lean`](../Ix/CompileCert/SourceNatOpPinData.lean) | Source-named Nat-operation declaration/certificate data. Generate with `source-pin-gen`; `strong-pins` in `check-cert` compares committed and regenerated data and runs controls. |
| [`IxC/Kernel/Ixon/PinData.lean`](../IxC/Kernel/Ixon/PinData.lean), [`NatOpPinData.lean`](../IxC/Kernel/Ixon/NatOpPinData.lean) | Serialized-artifact pins, prelude and Nat-operation certificates. Use `kernel-pin-gen` and the full recipe in [kernel regeneration](kernel.md#keys-pins-and-the-prelude); review actual data separately from source-provenance text. |

### Commands that produce record evidence

Use fresh output paths. The emitters print candidate Lean rows; they do not
approve or install them.

```sh
mkdir -p out/record-review
IX_TWINS_DUMP=out/record-review/twins \
IX_TWINS_IXE=out/record-review/twins.ixe \
  lake test --wfail -- --ignored twins

PASS3_KEEP=out/record-review/pass3 PASS3_FAILURES=out/record-review/rows.tsv \
PASS3_EMIT_FAILURES=1 lake test --wfail -- --ignored pass3
PASS3_RECHECK=out/record-review/pass3 PASS3_RECHECK_ANON=1 \
PASS3_RECHECK_TAG=review PASS3_FAILURES=out/record-review/recheck.tsv \
  lake test --wfail -- --ignored pass3
PASS3_EXPECT_EMIT=out/record-review/rows.tsv,out/record-review/recheck.tsv \
  lake test --wfail -- --ignored pass3

VALIDATE_LEAN_KEEP=out/record-review/validate \
  lake test --wfail -- --ignored validate-lean
AUX_CERT_FAILURES=out/record-review/aux-cert.tsv \
  lake test --wfail -- --ignored aux-cert
lake test --wfail -- --ignored validate-lean-nc aux-oracle clique-transport pass3-cliques

lake exe ix compile-lean Benchmarks/Compile/CompileInitStd.lean \
  --out out/record-review/initstd.ixe
CHANGED_SET_INITSTD=out/record-review/initstd.changed.json \
  lake test --wfail -- --ignored changed-set

lake build --wfail IxC.Kernel.PinGen.Certs source-pin-gen
lake exe source-pin-gen out/record-review/SourceNatOpPinData.lean
```

The changed-record path replaces the artifact extension with `.changed.json`
(`ChangedSet.pathFor`); check the path printed by `compile-lean` before supplying
it. For twins kernel evidence, produce the files that `IX_TWINS_KERNELS` reads:

```sh
mkdir -p out/record-review/twin-kernels
lake exe ix check-lean out/record-review/twins.ixe --anon \
  --fail-out out/record-review/twin-kernels/tc.fail
lake exe ix check-rs out/record-review/twins.ixe --anon \
  --fail-out out/record-review/twin-kernels/rs.fail
lake exe kernel-check-ixe out/record-review/twins.ixe \
  out/record-review/twin-kernels/cert.jsonl
IX_TWINS_KERNELS=out/record-review/twin-kernels \
  lake test --wfail -- --ignored twins
```

Retain each checker's exit, requested/checked coverage and full output as well as
these files. The loader uses executable-kernel failure sets to annotate candidate
rows; absence from a failure file alone does not demonstrate that a requested
name was checked. Certified annotations use actual `accept` rows; a documented
decline or blocked row is not accepted. Regenerate suggestions only against the
same pinned artifact/source, and review the evidence before installing them.

For varying Pass3 rows, repeat the meta recheck on the same kept artifacts with
fresh tags/output files and append those TSV paths to `PASS3_EXPECT_EMIT`.
The Lean meta leg uses `--clear-every 1`; do not silently replace it with a warm
worker schedule when attributing a count change.

For corpus generation, elaboration filtering, assembly, run/compare/matrix and
exact `--expected` handling, use the full
[compiler corpus procedure](compiler-corpus.md). CI runs `aux-shape-sweep
self-check` and `checker-support-regression`, not the broad generated shape sweep.

After corpus generation/filtering/assembly, a reviewed expectation file can be
supplied explicitly:

```sh
lake exe aux-shape-sweep run --dir out/corpus-reviewed \
  --revision EXACT_COMPILER_COMMIT --mode on --jobs 4 --workers 1 \
  --timeout 900 --expected out/corpus-expected.json
lake exe aux-shape-sweep compare --dir out/corpus-reviewed --mode on
lake exe aux-shape-sweep matrix --dir out/corpus-reviewed
```

`out/corpus-expected.json` is an array of objects with the five fields in
[`Corpus.Run.Expected`](../Tests/Ix/Compile/Corpus/Run.lean). Write the exact
observed diagnostic and a reviewed cause for each case; the driver does not turn
its output into a new expectation file automatically. Preserve its
`run-config.json`, all phase verdicts, source ownership and coverage records.

## Reference artifacts

The post-surgery-removal default byte references are external, immutable files;
they are not checked into this repository. Both are Ixon environment files.

| Reference | Bytes | SHA-256 |
| --- | ---: | --- |
| `initstd-a3.ixe` | 256128289 | `a2e22ee7f8d0fcf0d607047dda7d83749f20886f2d03f1cbaf2ede3a7d1ba676` |
| `mathlib-a3.ixe` | 2376572399 | `d0427adf7b995f7f48c6fe5fa069c5d3a3d5c10c6f061425729e87339f6bf6db` |

The inputs are [CompileInitStd](../Benchmarks/Compile/CompileInitStd.lean) and
[CompileMathlib](../Benchmarks/Compile/CompileMathlib.lean), with Lean 4.34.1,
Lean commit `5045d0056413266e57c625dcd7c365b10e377c52`, and, for the Mathlib
reference, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Build the benchmark imports before sealing a gate's input manifest. A newly built
import during the measured command changes that provenance even if the output
bytes match.

`links-a3` is a deployment directory of links, not a third serialized artifact
with a single `.ixe` hash. The reference inventory captured on 2026-10-08 has:

| Link in `links-a3` | Literal target | Resolved target's mode |
| --- | --- | --- |
| `initstd.ixe` | `../initstd-a3.ixe` | `0444` (read-only) |
| `mathlib.ixe` | `../mathlib-a3.ixe` | `0444` (read-only) |
| `certs.ixe` | `../certs-v4341.ixe` | `0664` (writable; not installed read-only) |

The certificate environment is **636608 bytes**, SHA-256
`6f15c4176891a706e5f236400fce2574d4c7de8a2fb2e275514914545c89fed7`.
Its writable mode is a recorded deployment limitation; the two library
references above are read-only. Preserve and verify the certificate hash before
and after pin generation rather than assuming permissions protect it.
The captured `.lake/envs` and `.lake/census` directories expose `initstd.ixe`,
`mathlib.ixe` and `certs.ixe`, each linking through `links-a3` to these same files.

An installation manifest must record every link name, literal and resolved
target, byte size, mode and SHA-256. Verify the resolved files, not just the
link-directory spelling. Do not silently fall back to an older reference set.
The `-a2` files are historical comparison inputs; the current compiler does not
reproduce the retired surgery mode.

To reproduce the byte comparisons, choose fresh output paths and use verified
read-only references:

```sh
lake exe ix compile Benchmarks/Compile/CompileInitStd.lean --no-build \
  --out out/initstd-rust.ixe
lake exe ix compile-lean Benchmarks/Compile/CompileInitStd.lean --rust-check \
  --out out/initstd-lean.ixe
sha256sum out/initstd-rust.ixe out/initstd-lean.ixe /path/to/initstd-a3.ixe
cmp out/initstd-rust.ixe /path/to/initstd-a3.ixe
cmp out/initstd-lean.ixe /path/to/initstd-a3.ixe
```

The Lean command must also report byte alignment with Rust. Repeat the two
backends separately for `CompileMathlib.lean`, comparing to `mathlib-a3.ixe`.
The full environment byte checks are separate from per-name parity, pack
sampling and certification. Retain output on any mismatch.

## Landing a package

The tracked manual entry point is
[`scripts/compiler-gate.py`](../scripts/compiler-gate.py) (Python 3.11+). It
implements the common procedure below without changing CI. It runs only when
invoked explicitly, and does not reserve a shared machine, transfer source,
download dependencies, retry failures, update records or publish a result.
Use an idle checkout and arrange the required machine reservation first.
Provision its locked root, benchmark, kernel and model dependencies before
running offline. Builds use the normal `.lake` and Cargo caches; the evidence
directory contains no newly built project or copied build cache.

Supply a reviewed full source manifest (standard `sha256sum` format, paths
relative to the checkout), its SHA-256, and the exact source commit. Include
the runner itself. Verify that the manifest describes that committed tree,
including any integration changes, before transfer. All references are explicit:
the two current libraries and certificate file have the hashes in
[Reference artifacts](#reference-artifacts); `--legacy-ref` and `--legacy-sha`
identify the historical Init+Std comparison input used by `pass3-lib`.
`--kernel-baseline` is a reviewed complete Init+Std checker JSONL, bound by
`--kernel-baseline-sha`. Its ordered addresses, names, kinds, outcomes and reasons
must agree exactly; only `micros` and `readMicros` are ignored. An intentional
checker change needs a separately reviewed baseline, never an automatic rerecord.

For example, from the checkout root, substitute actual reviewed paths and hashes:

```sh
python3 -B scripts/compiler-gate.py --phase core \
  --commit FULL_SOURCE_COMMIT --source-manifest /path/to/source.sha256 \
  --source-sha SOURCE_MANIFEST_SHA256 --benchmark-dir "$PWD/Benchmarks/Compile" \
  --initstd-ref /path/to/initstd-a3.ixe --mathlib-ref /path/to/mathlib-a3.ixe \
  --certs-ref /path/to/certs-v4341.ixe --legacy-ref /path/to/initstd-a2.ixe \
  --legacy-sha LEGACY_REFERENCE_SHA256 \
  --kernel-baseline /path/to/reviewed-initstd.jsonl --kernel-baseline-sha ROWS_SHA256 \
  --workers 32 --cargo-jobs 4 --out "$PWD/out/compiler-core-FRESH"
```

`core` runs the full primary suite, all 35 ignored suites listed below, the
Init+Std controls and bytes, pin checks, lint, certification and kernel/model
checks. `--extra-suite NAME` adds a package-specific ignored suite without
replacing that inventory. Run `--phase mathlib` with a fresh output directory
and the same source, references and worker settings for the separate reserved
Mathlib byte legs. Each partial result explicitly lists the other section as
pending; join their exact source/tool/native/import evidence when reviewing the
complete gate. `--phase all` runs both sections sequentially and starts Mathlib
only after every core stage passes. Library certification and other named
package obligations remain separate; this runner does not invent their scope.

Logs contain the Lean version, commit, command, actual command exit and complete
output. `planned-stages.json`, `stages.json`, `stages.tsv`, `result.json` and
`driver.rc` preserve each success, failure or explicit unrun stage. Required
evidence-write failures force nonzero. Source, references, dependency sources
and tools are rehashed afterward; complete compiled-import, native-library and
Lean-prefix trees are compared across each library compilation interval.
`LEAN_SRC_PATH` is inventoried separately: all recursive `.lean` candidates,
source-root package directories (including empty shadowing directories), ordered
search paths and Lean's two builtin source fallbacks remain pinned. Source links
are followed with explicit missing-root, dangling-source and cycle checks;
changing unrelated logs or non-source lock files does not change this inventory.
Tracked and dependency source checks remain complete. Input modules are built
before that interval. Outputs and full pin diffs are retained, including on a
mismatch; their hashes are in the result before any later manual cleanup.
The lane's existing `.lake/build/compile-cert` data and four kernel report files
are moved into clearly labeled `prior-*-details` directories before those checks.
Their new complete logs/tables are copied separately into the run's evidence,
including partial failures; old data cannot stand in for an unrun check.

Suite selection, diagnostic, rerecord and skip environment variables are
cleared. The schedule and pack suites retain their own worker/coverage matrix.
`--workers` sets the Lean library worker count and Rust scheduler/Rayon ceiling;
Rust may admit fewer workers. `--rust-check` runs serially to avoid overlapping
the backends. The default 100 GB free-space check is a startup floor, not a disk
or memory quota. These are correctness gates, not quiet benchmark measurements;
the Lean command includes its cached input build and the Rust command uses
`--no-build`. Stage elapsed times include verification and logging and are not
compiler-only measurements. A stale `.lake/compiler-gate.lock` is refused and requires manual
process inspection before removal.

Use an isolated landing checkout based on the current mainline, with the reviewed
package range and all conflict resolutions included. Gate the final tree rather
than reusing a predecessor's result. Keep its source fixed until the run and
postchecks finish. A lane-only package needs its strict build, the full primary
suite, `check-cert`, affected lane controls and the Init+Std byte tripwire.
A compiler package additionally uses the full compiler procedure below; changes
crossing the certified reader/order boundary also require `check-kernel`.

1. Build the standalone certified package and every later executable/module:

   ```sh
   lake -d IxC build --wfail
   lake build --wfail Ix IxTests ix kernel-check-ixe canon-census ixe-diff \
     IxSharingVerify aux-shape-sweep checker-support-regression kernel-pin-gen \
     compile-cert-c1 compile-certify Ix.CompileCert.ValueReceipt
   cargo fmt --check
   cargo clippy --release --workspace --all-targets \
     --features ix-ffi/parallel,ix-ffi/net,ix-ffi/test-ffi,ixon/sharing-profile -- -D warnings
   cargo test --release --workspace
   lake build --wfail IxTests ix kernel-check-ixe compile-certify
   ```

2. Run `lake test --wfail` without a primary filter. Run each of these ignored
   suites, retaining its individual exit and summary:

   ```text
   pass3-cliques validate-lean pass3 pass3-plan-cache twins canon-pass1
   clique-transport clique-ownership aux-oracle aux-cert validate-lean-nc
   adversarial-matrix decompile-diff compile-claim-conflict compile-claim-order
   compiler-selected-closure-e2e o11a-decline aux-source-identity compile-closure-whole
   compile-caller-independence changed-set pack-units validate-aux aux-gen-diff
   rust-decompile kernel-ixon-roundtrip pass3-rust-parity
   compile compile-schedule-identity
   rust-serialize decompile canon-closure-aux ixon-corpus aux-gen-closure
   commit-io rust-canon-roundtrip
   ```

   The last line and the serialization/closure additions are part of the
   compiler landing coverage even though not every one appears in the same CI
   partition. Run package-specific gates such as `dev-census` or
   `bridge-roundtrip` when the package requires them.

3. Run the independent corpus controls and full Init+Std compiler parity, with
   the default pack-root coverage:

   ```sh
   lake exe aux-shape-sweep self-check
   lake exe checker-support-regression
   PARITY_FILE=Benchmarks/Compile/CompileInitStd.lean \
     lake test --wfail -- --ignored pass3-rust-parity
   ```

   Unset `PARITY_ONLY`, `PARITY_PACK_MAX`, `PARITY_PACK_ROOTS` and all suite
   selection/debug variables for the full gate. Keep the full schedule tier.

4. Run both Init+Std byte comparisons above. Check the Lean plan-cache
   recomputation path explicitly:

   ```sh
   IX_PASS3_CHECK_PLANS=1 lake exe ix compile-lean \
     Benchmarks/Compile/CompileInitStd.lean --out out/initstd-plans.ixe
   sha256sum out/initstd-plans.ixe /path/to/initstd-a3.ixe
   cmp out/initstd-plans.ixe /path/to/initstd-a3.ixe
   ```

   Retain the recomputed-hit summary as well as the byte comparison. The retired-mode
   negative controls require both backends to refuse `IX_PASS3=off` and
   `IX_PASS3=bogus` with the documented diagnostics and no output; `compile-lean`
   exits 2 for these invalid settings. The deprecated `IX_PASS3=images` alias
   must print its no-effect note and preserve the default bytes. These are
   parser compatibility controls, not additional compiler modes.

5. Check the produced default artifact with `kernel-check-ixe`; regenerate the
   artifact pin files to scratch paths with `kernel-pin-gen` and compare them
   with the committed data. Preserve full diffs. The compiler byte-neutral
   gate permits only the exact Init-source provenance fields to differ; pin
   addresses, prelude/level/operation data and the certificate digest remain
   exact. In each file, only the Init digest in its header and `def source`
   may differ (exactly two matched fields per file, each a 64-digit lowercase
   hexadecimal SHA-256). The second digest in `NatOpPinData.source` identifies
   the certificate environment and is not normalized. Preserve all other
   bytes and reject missing or additional provenance matches. Its negative
   controls mutate actual pin data, Nat-operation data and
   the certificate digest, beside unchanged/provenance-only neighbours. The
   runner preserves input bytes before strict UTF-8 decoding; its eleven pin
   controls include CRLF and lone-CR rejection for each file through the actual
   file comparator, with unchanged LF and provenance-only valid neighbours.
   Preserve the historical old/new `ixe-diff` classification if that comparison
   is part of the package's reference migration evidence.

6. Finish the strict lint, certification and kernel/model gates and compare the
   toolchain files:

   ```sh
   lake lint -- --wfail
   lake run check-cert
   lake run check-kernel --with-model
   diff lean-toolchain Benchmarks/Compile/lean-toolchain
   diff lean-toolchain IxC/lean-toolchain
   diff lean-toolchain Models/SetTheory/lean-toolchain
   ```

7. Schedule the Mathlib byte legs separately, one library producer at a time on
   the shared build machine, with declared output/RAM requirements and enough
   free storage. Preserve exact source, executable, dependency/import and
   reference identities before and after. Run library certification when the
   package changes the lane or requires library acceptance; preserve all
   verdict classes. Release the machine slot only after terminal status and
   provenance/idle checks. Successful byte outputs may be removed after their
   hashes and comparisons are retained; mismatches remain evidence.

Check every stage, not only a final `DONE` line. Publish a hand-back containing the
exact base/tip range, changes, gate commands/logs, artifact identities, remaining
refusals and proof limitations. Recheck the mainline base before landing; if it
moved, integrate and validate the actual combined tree. Updating a test record,
reference or audit is part of the reviewed change, never an implicit repair of
a red gate.

## When a compiler change moves bytes

Stop the byte-neutral gate and retain both outputs. Determine whether the change
is expected before installing a new reference.

```sh
lake exe ixe-diff old.ixe new.ixe --names --tsv out/byte-moves.tsv
lake exe ixe-diff --originals new.ixe --names
```

The tool groups moved names and reports packaging, nested-order, cascade and
content classifications. Inspect root changes, additions/removals, metadata and
original forms; the diagnostic's class is evidence to review, not authorization
to change the contract. For library attribution, `mathlib-measure` can retain the
compiler's own block/clique/failure records and check the affected name set.

After an intentional migration is approved:

1. Run both compilers, full parity, relevant semantic/value and negative controls,
   the full compiler landing gate and both library byte legs on the new tree.
2. Regenerate pins from the new Init+Std and certificate artifacts using
   [kernel regeneration](kernel.md#keys-pins-and-the-prelude). Review all changed data;
   regenerate source pins if the source/toolchain changed and rerun `check-cert`.
3. Install newly versioned `-aN` artifacts read-only. Retain the previous set,
   output sizes, full SHA-256 digests, producing commands and input/build
   manifests. Create a new link set with an explicit resolved-target manifest;
   do not overwrite the old baseline to make a comparison pass.
4. Re-record only explained test deltas, including their source/permutation,
   compiler-payload and checker evidence. Rerun the exact suites after the edits.
5. Run the certified checker and the applicable compiler-certification modes on
   the new Mathlib artifact. Report unsupported/blocked/rejected/not-reached
   names separately; neither byte identity nor a nonempty accepted subset closes
   missing certification coverage.

## Toolchain, format and lane changes

Follow [the kernel toolchain procedure](kernel.md#on-a-toolchain-bump) and
[format procedure](kernel.md#on-a-format-change) first: keep all workspace
`lean-toolchain` files aligned, update matching library inputs, regenerate the
kernel pins and review the audit changes under their existing policy.

Then rebuild the compiler/native executables and imports, produce new library
artifacts, rerun both-compiler parity and the compiler/lane gate inventory, and
review every exact record above. Regenerate source-named pins with
`source-pin-gen` and check them through `check-cert`. A changed proof root or
trust dependency needs an explanation and the full affected audit, even when
serialized bytes do not move. A lane-only change still needs its actual
certification controls and byte tripwire; a compiler change still needs source
meaning/valid-neighbour checks beyond matching the two implementations.
