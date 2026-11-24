# CI and merge queue configuration

RunsOn CPU jobs use the default Spot policy by omitting `spot` from their
runner labels. This includes CPU benchmarks and the CUDA compilation check,
which does not run on a GPU. Future GPU benchmarks should explicitly request
`spot=false`. RunsOn may fall back to on-demand capacity when Spot is
unavailable or when provisioning an automatic recovery attempt.

Formal Aiur's CPU integration job exercises the CPU controls of
`formal-checks cuda` (`Tests/FormalChecks/Cuda.lean`). Actual CPU/CUDA proof and key parity, including
sharded IxVM, recursion, and aggregation, requires a GPU host running
`IX_TEST_CUDA=1 lake env lean --run Scripts/CheckFormal.lean`. The
[migration guide](formal-aiur-migration.md#cuda-and-native-builds)
documents the retained logs and report; the CUDA compilation job does not
provide hardware validation.

CI jobs request the `r7i+r8i+r7a+r8a` families and let RunsOn pick the size
from `cpu=`, so a Spot request can draw from several pools; exact r8i types
alone had no Spot capacity. Their Rust builds use the `portable` codegen mode
of the toolchain action, `x86-64-v4` plus `avx512vbmi2` and `gfni`, the
feature set every listed family shares, and their sticky lineages carry that
name so native artifacts never mix in. Valgrind builds `generic`, without
AVX-512, into the S3-backed actions cache under its own key. Benchmarks stay on exact `r8i.8xlarge` with
`native` codegen so their timings remain comparable.

Runner labels include the workflow run ID, job ID, run attempt, and, for
matrix jobs, the job index. This keeps concurrent jobs and recovery attempts
from claiming another job's matching runner. Matrix jobs use
`fail-fast: false` so an interrupted partition does not cancel its siblings.

Every RunsOn label uses the `ubuntu26-full-x64` image and sets `volume=`
explicitly so the root volume has room for toolchains, apt packages, and
container images; sticky disks hold only the declared cache paths. Jobs use
`volume=100gb`, and the Nix job `volume=150gb`.
Sticky disks restore with provisioned snapshot initialization; `lazy-init`
makes first reads of cached binaries and oleans slow enough to dominate jobs
that only run them.

## Test tiers

`lake run check-source-docs` rejects retired compiler API names, numbered
private work-queue labels and references to internal plan files in Lean,
Rust and Markdown sources. It runs scanner controls on every invocation and
uses no grandfather baseline. `lake run check-ci-filters` verifies that
`.github/workflows/ci.yml`'s `refinement:` and `kernel:` path filters cover
every project module in the SHA-256 transitive definitional closure manifests
(`circuit-composed`, `compile-correct`, and `check-bytes`) as well as the TCB
files `Ix/Address/Admission.lean` and `Ix/KernelDisplay/Peek.lean`. `lake lint`
runs both after the strict module build and coverage checks.

Lean test entries are split across three drivers sharing `Tests/Registry.lean`:

- **`IxTests` (`Tests/Main.lean`)**: host `primary`, `ci:cli`, `ci:compiler-closures`, `ci:binding-proof`, `ci:misc`, `ci:landing-initstd-cli`, and `ci:nightly`.
- **`IxVMTests` (`Tests/IxVMMain.lean`)**: IxVM circuit-verdict suites (`ci:ixvm`, `ci:nightly-ixvm`, and opt-in `manual` sweeps) — kept out of `host-build` so host-only PRs do not build or link the 22 IxVM circuit test modules.
- **`IxManualTests` (`Tests/ManualMain.lean`)**: manual-only benchmark, corpus, and differential runners (`lake lint` still typechecks every module).

The tier says where each entry runs:

| Tier | Driver & Where it runs | What it holds |
| --- | --- | --- |
| `primary` | `IxTests` (`lake test`): `ci.yml`'s `host-test-primary`, and Nix's `ix-tests` | the quick host suites (including pure-host `ixvm-pw-hints`, `ixvm-binder-data`, and `ixvm-differential-attribution`) |
| `ci:cli` | `IxTests`: `ci.yml`'s `host-test-cli` | the command-line integration tests |
| `ci:ixvm` | `IxVMTests`: `ci.yml`'s `ixvm-tier-tests`, on the S3-cached `ixvm.ixa` artifact | PR completeness, FFT cost pins, out-of-scope claims (`eval`, `reveal`, `user-axioms`, `assumed`), and Rust-host circuit-verdict smokes (`IX_AIUR_CIRCUIT_VERDICT`; `=0` for plain execution) |
| `ci:compiler-closures` | `IxTests`: `ci.yml`'s `host-test-closures` | selected closures against the whole environment, auxiliary closure addresses, checker-support grounding, packing, `cert-evidence-agreement`, and the certified checker's pinned subjects and acceleration inputs |
| `ci:binding-proof` | `IxTests`: `ci.yml`'s `binding-proof-cli`, on the cached `ixvm.ixa` and prebuilt Rust hosts | `ix prove-binding`, shard proofs assuming the binding, and composition/refusal checks (64 GiB budget) |
| `ci:misc` | `IxTests`: `ci.yml`'s `host-test-misc`, with the ZK voting prover | the tutorial, catalog and commit I/O |
| `ci:landing-initstd-cli` | `IxTests`: `ci.yml`'s `host-test-landing` | Init+Std through the `ix` binary: `ix compile-lean` with its report checks and reference digest pin (`Tests/Fixtures/initstd-reference.txt`), `ix check-lean` with bound roles admitted, `ix validate-lean` fidelity reusing that artifact (avoiding a second full Init+Std compile), and `ixvm-reader-coverage` |
| `ci:nightly` | `IxTests`: `nightly.yml` (scheduled daily on `main`) | whole-Init+Std pure-Lean BLAKE3 sweep (`admission-hash-diff-initstd`) and brute-force exact-sharing sweeps (`exact-sharing-full`) |
| `ci:nightly-ixvm` | `IxVMTests`: `nightly.yml` (scheduled daily on `main`) | full 24-term generated arithmetic `Claim.eval` suite (`ixvm-eval-full`; `Claim.eval` has no soundness proof yet) |
| `manual` | `IxVMTests` / `IxManualTests` by hand only | entries that need inputs outside the repository, take minutes or hours, diagnostics, or opt-in adversarial sweeps formally superseded by `circuitComposed` (`ixvm-exploits-full`, `ixvm-safe-references-full`, `ixvm-tagn-sweep`, `ixvm-arena-full`); each states its reason |

The manual runner that proves through the production `ix_aggr` circuit,
`aggregate-binding-reuse`, takes minutes of recursion and about 190 GB, three
quarters of a 32-CPU runner's memory, so it stays manual.
`binding-proof-cli` (`ci:binding-proof`) runs `aggregate-binding-reuse`'s
flow without its two aggregates: the binding proof, the shard proofs that
assume it, their composition with it, and the refusals without it; the
aggregation circuit's handling of the binding is tested in
`formal-aggregate-tests` (`Scripts/CheckFormal.lean`). Its proving budget is
64 GiB, so it runs in its own 32-CPU `ci.yml` job on the S3-cached `ixvm.ixa`
artifact and prebuilt Rust hosts.

`aggregate-toolchains` is also manual: it proves the committed library fixtures
from Lean 4.29.0, 4.33.1, 4.34.1 and 4.35.0 with one IxVM key, discharges each
piece's binding assumptions, and joins their roots into one catalog root.
It verifies that root against the catalog and checks refusals for missing
members. Run `lake build ix`, then `lake test -- aggregate-toolchains`, with
`zstd` available. Allow tens of minutes. `IX_TOOLCHAINS_MAX_RAM` sets the
aggregate jobs' RAM budget in GiB (default 140); the shard and shard-proof
commands use 64 GiB. The runner keeps its store and caches in a temporary
home directory. Its registration and manual-run reason live in
`Tests/Main.lean`; its full flow is in
[`Tests/AggrToolchains.lean`](../Tests/AggrToolchains.lean).

`lake test -- --tier <tier>` runs one tier; `--tier landing` runs the landing
partition. The registry's primary self-test, `ixtests-registry`,
fails when a CI tier has no entry, when no workflow runs a CI tier (comments
do not count), or when a workflow names a tier the registry does not define.
It also fails when an entry of `required` in `Tests/Main.lean` is missing,
registered twice or in another tier, and when that list names no entry of
some tier that runs in CI; moving a required check to `manual` therefore
means editing the list in the same change. The check of the workflows is
textual: a step disabled by an `if:` still counts. A merge-tests partition
must finish well within the merge queue's status-check timeout: split a tier
into two jobs before it approaches it.

The primary tier runs incrementally in `ci.yml`'s `host-test-primary` on every
host PR, while Nix CI evaluates all flake checks and builds the host checks
(`ix-lib`, `ix-cli`, `dev-shell`, `dev-shell-tools`) on PRs that touch Nix
packaging, toolchains, or lockfiles (the 16 `ixcc-*` checks run in IxCC's own
reusable workflow `ixcc.yml`, below). In `ci.yml`, `host-build`
builds non-Mathlib host targets once on the dedicated `ci-host` sticky lineage
and fans out to parallel test/lint jobs (`host-test-primary`, `host-test-cli`,
`host-audits-lint`, `host-test-landing`, `host-test-closures`, `host-test-misc`);
`formal-build-export` builds formal packages and Rust hosts once on `ci-formal`,
restores or exports `{ixvm,recursion,aggregate}.ixa` in parallel into the S3
cache, and fans out to `formal-unit-tests`, `formal-check`, `ixvm-tier-tests`,
and `binding-proof-cli`; `ixvm-refinement` and `certified-kernel` run in
parallel from `t=0` on their own sticky lineages (`ci-refinement`, `ci-kernel`).
Valgrind runs `ffi-tests` (without Mathlib) whenever Rust/FFI files change. The
certification statements' freeze, `Ix.Cert.Audit`, is built by `check-kernel`
and `lake lint`, not by the test binary.

## Path filtering, draft PRs, and required checks

`ci.yml`, `nix.yml`, and `bench-main.yml` use `dorny/paths-filter` so changes
only trigger the subsystems they affect (with conservative global triggers on
toolchains, `lakefile.lean`, `Cargo.*`, and workflow files). On **draft** pull
requests, `ci.yml` runs only the fast dev loop (`quick-checks`, `lints`,
`host-build`, `host-test-primary`, `host-test-cli`, `host-audits-lint`,
`rust-test`, `cuda-compile`); marking a PR **ready for review** runs the full
path-gated parallel DAG including `certified-kernel`, Init+Std & compiler
closures, `valgrind-ffi`, `ixvm-refinement`, `formal-check`, `ixvm-tier-tests`,
and `binding-proof-cli`. Pushes to `main` run build-only cache-warming steps so
sticky disks and the S3 `.ixa` cache stay fresh without re-running tests.

Because `runs-on/spot-retry-gate` requires every job in `job_results` to have
`result == "success"`, a lightweight `check-results` job sits before `ci-gate`
and `nix-gate`: it allows `skipped` only when `changes` intentionally gated
that job (rejecting failures, cancellations, and cascading skips) while
preserving RunsOn's automatic EC2 Spot interruption detection and retries.

The branch protection or ruleset for `main` should enable **"Require branches
to be up to date before merging"** (no separate merge queue needed) and require
these aggregate checks:

| Workflow | Required check |
| --- | --- |
| CI Jobs | `ci-gate / pass` |
| Nix CI | `nix-gate / pass` |

During the transition off the legacy merge queue, `merge-tests-stub.yml`
temporarily publishes `merge-gate / pass` on `pull_request` and `merge_group`;
once the ruleset drops `merge-gate / pass` and disables the merge queue, delete
`merge-tests-stub.yml`. Remove raw RunsOn job checks and `Nix Tests` from the
required-check list, and do not require `interrupted` or `Detect Spot interruption`.
Independent GitHub-hosted or security requirements (`CodeQL`) can remain.

## The certified compiler (IxCC)

`IxCC/` is a Lake package of its own (`«ix-cc»`). It requires the `IxCK`
package beside it (`../IxCK`, importing its Ixon v5 codec, role vocabulary,
tiered admission entry, executed typing core, host limit resolver, and—in the
separate `IxCCGrounding` library—the kernel's model statement) and Blake3
(`Blake3.Pure` only); the root package does not require it. Its
[CI guide](../IxCC/docs/ci.md) describes its 16 required checks (after retiring
the legacy `aiur` check), which the flake exposes as `ixcc-*`, with
`packages.ixcc` and `apps.ixcc`. IxCC's Nix expressions select their own
sources (`IxCC/nix/sources.nix`): `IxCC/`, the pinned `IxCK` closure its trust
ledger hashes and, for the ledger check, `flake.lock`, `.github/actions` and
`.github/workflows/ixcc.yml`. The host's source sets leave `IxCC/` out, so a
change on one side rebuilds nothing of the other.

The reusable workflow `.github/workflows/ixcc.yml` builds every `ixcc-*`
check, within a 60-minute job timeout. It first requires the flake's
evaluated `ixcc-*` checks to be exactly the trust ledger's `required_checks`
(the attributes of `IxCC/nix/checks.nix`), so a check dropped from or added
to the flake fails it. CI Jobs calls it when a pull request or `main` push
changes IxCC's inputs (the `Detect IxCC changes` path filter, covering `IxCC/**`,
`IxCK/{Ixon,Address,Kernel,Host,Resource}/**`, `IxCK/lakefile.lean`,
`IxCK/lake-manifest.json`, `IxCK/lean-toolchain`, and shared flake/workflow
files) and reports to `ci-gate` through `IxCC result`, which also succeeds
when the change does not reach IxCC. Merge tests calls it on every merge
group, as the `IxCC (certified compiler)` partition of `merge-gate`. Nix CI
evaluates the `ixcc-*` checks without building them. IxCC's trust ledger pins
`ixcc.yml` by its SHA-256 and audits the local actions it uses, with every
remote action pinned to a commit and listed in its `ci_actions`. It does not
audit ix's other workflows, which track `argumentcomputer/ci-workflows@main`
and `argumentcomputer/lean-update@dev` by branch. It records `flake.lock`'s
revisions and `IxCC/lean-toolchain`, and requires the root `lean-toolchain`
to equal IxCC's. So the weekly Rust update (`update-rust.yml`, which runs
`nix flake update`), a Lean update (`update.yml`) and a Dependabot bump of
`ixcc.yml`'s actions each fail `ixcc-trusted-extern-ledger` until the ledger
is updated in the same pull request: "Routine updates" in
[IxCC's ledger document](../IxCC/docs/trusted-extern-ledger.md) lists the
fields and the commands (`check-trusted-externs --record`, then
`tools/RecordLedgerPins.lean`, from `IxCC/`).

The repository-wide tools treat `IxCC/` as follows:

| Tool | IxCC |
| --- | --- |
| Root `lake build`, `lake test`, `lake lint` (`build-all`) | Not built: no root library or executable claims the `IxCC.` module root |
| `check-modules` | Not covered: `IxCC/` has its own lakefile, so it is another workspace. IxCC's `check-build-graph` inventories its modules. Its checks build the production library, every executable, the proof and fence aggregate `IxCCTests.Proofs`, and (separately, in `ixcc-grounding`) `IxCCGrounding`; the kernel-evaluation and artifact modules IxCC's CI guide lists as manual are built by no check |
| `check-source-docs` | Not scanned. Its rules name ix's retired compiler APIs and private plans, and IxCC's frozen records quote some of those names (recorded compiler output and the historical reference-check command of its fixture refreeze). IxCC's ledger scans its own sources and the pinned `IxCK` closure for `axiom`, `sorry` and every spelling of native evaluation it can see (`native_decide`, `decide +native`, `native := true`, the `ofReduceBool`-style axioms), inventories their externs and `@[csimp]` theorems, and enumerates the kernel closure's admitted `implemented_by` rulings |
| `kernel-layering`, `kernel-trust-surface` | Not applied: they fence `IxCK/Kernel/`. IxCC's ledger pins the exact `IxCK` closure it imports and rejects any other `IxCK` import; `check-build-graph` keeps the kernel's model (`IxCK.Kernel.Denotes` and its set theory) out of the production library and shared program build |
| `ixvm/ixvm-proof-gen --check`, `Scripts/CheckFormal.lean` | Not applicable: they cover formal Aiur and IxVM |
| Toolchain check (CI Jobs) | Compares `IxCC/lean-toolchain` and `IxCC/benchmarks/runner/lean-toolchain` (IxCC's trust ledger also requires the root toolchain to equal IxCC's) |
| `update.yml` | Includes the `IxCC` package and its benchmark runner |
| `.gitignore` | ix ignores `*.ixe` and `*.ixc/`, except under `IxCC/fixtures/`, where they are tracked closures and catalogs |
| `.gitattributes` | Marks IxCC's generated manifests, kernel artifacts and recorded fixture outputs |

## The kernel-bridge model (`Models/KernelBridge`)

`Models/KernelBridge` is a Lake workspace of its own that requires `IxCK` and
`IxCC` by path: a conditional simulation lemma between IxCC's source
evaluator and the kernel's reduction (its README states what it does and does
not prove; it does not establish source adequacy). `lake run
check-kernel-bridge`, from the root, builds it (its modules treat warnings as
errors; `--wfail` is not used because IxCC's modules emit deprecation
warnings) and checks that the 32 theorems its `Audit.lean` fences are exactly
the root lakefile's `kernelBridgeFences`. Merge tests run it in the kernel
partition on every merge group. CI Jobs runs it on pull requests and `main`
pushes whose changes reach it (the `kernel-bridge` output of the same path
filter: `IxCC/`'s Lean sources and Lake files, `IxCK/`, the model, the root
`lean-toolchain` and `lakefile.lean`, `ci.yml` and the local actions) and
reports through `Kernel bridge result`, as `IxCC result` does. It shares
IxCC's package directory, where Lake checks out and builds Blake3, and writes
IxCK's objects to `.lake/kernel`; both workflows keep `IxCC/.lake` and
`Models/KernelBridge/.lake` on the shared `ci-lean-test-x86-64-v4-100gb` sticky
disk. Its toolchain is in the toolchain check, and `update.yml` bumps it.

## Spot recovery

Each workflow that runs in the merge queue uses the official
[runs-on/spot-retry-gate](https://github.com/runs-on/spot-retry-gate) reusable
workflow, with all contributing jobs listed in `needs`. The gate requires
only `actions: read` and `checks: read`; the RunsOn GitHub App separately
needs permission to rerun workflows (`Actions: read and write`). Automatic
Spot retry stays enabled by default; do not add `retry=false` to these jobs.

On attempts 1 and 2, a failure annotated `EC2 Spot interruption` produces a
successful `interrupted` check while the required `pass` check stays pending.
RunsOn waits for the workflow attempt to finish, then reruns failed jobs and
their dependents. Successful independent jobs are retained. Attempt 3 reports
the ordinary aggregate result, so exhausted retries cannot leave the gate
pending indefinitely. Ordinary failures without that annotation fail the
gate; an annotation lookup error also fails it.

Merge-group attempts are never superseded by workflow concurrency. Configure
the merge queue's status-check timeout to cover the initial attempt, queue
delays, and up to two automatic reruns. That setting lives in GitHub, outside
these workflow files. Artifact uploads that may run again replace the old
artifact under the same name so a recovered job cannot fail on a duplicate
upload.

See [RunsOn's merge queue guidance](https://runs-on.com/docs/costs/spot-pricing/#merge-queues).

## Retired suites

Two groups of suites were retired:

- those that tested the deleted Rust compiler, Rust kernel and ShardMap;
- those whose property the certified compiler and kernel now prove.

The certification proves soundness, that what is accepted is correct. It does not prove completeness, that every valid input is accepted. Completeness, and behaviour at scale, are exercised by the real-corpus runs in the merge queue:

- `initstd-reference` compiles Init+Std, pins its bytes, and checks every constant with `ix check-lean`.
- `fidelity-initstd` reads back and decompiles every record of Init+Std.

Each entry below says what replaced the suite, or why it was dropped.

**Dropped, because the other side is deleted:**

- **The Rust differentials:** `rust-compile`, `rust-decompile`, `rust-serialize`, the `*-cross` and `*-canon-roundtrip` checks, `kernel-check-const`, `kernel-check-env`, `kernel-ixon-roundtrip`, `exact-sharing-ffi`, `shard-map`, and `check-kernel`'s codec differential (`kernel-codec`).

**Dropped, because a proof or a corpus run covers them:**

- **`compile-schedule-identity`** (landing). It compared three things: the wave fold at several widths, a test-only live-state reference schedule, and the streamed pipeline at 1, 4 and 16 workers. None of these comparisons is needed now:
  - The IO pipeline computes the fold by type: `reportIO` returns `{r // r = Ix.Cert.compileReport env}` (`Ix/Compile/ReadyCompile.lean`).
  - The fold's value doesn't depend on its width (`Ix.Cert.Schedule.compileEnvFold_width`).
  - No other path ran the reference schedule. It isn't proved that the wave-snapshot fold equals a fold that compiles one block at a time on live state (`Ix/Cert/Schedule.lean`), but nothing compiles that way.
- **`cert-compile-parity-initstd`** (landing). It compared `Ix.Cert.compile` with the IO pipeline and with the Rust compiler on Init+Std. The first equality is `reportIO`'s type, and the Rust compiler is deleted. `initstd-reference` pins the bytes of the Init+Std artifact.
- **The Batteries leg of `compile-determinism`.** `initstd-reference`'s pinned digest is the stronger check across processes at scale.
- **`check-kernel`'s level comparison.** `leqCore_sound` proves soundness, and the corpus runs exercise completeness.
- **`check-kernel`'s quotient Source on Init and Std.** The nominal-to-quotient Source bridge is proved (`Ix.LeanIngress.NominalQuotient`, `Ix.Cert.Quotient`), and `initstd-reference`'s compile runs the same ingress on Init+Std.
- **`check-kernel`'s Init+Std reader fidelity** (the first 20,000 records). `fidelity-initstd`'s phases 3 and 4 compare every record of Init+Std and require full source coverage.
- **`compile-claim-conflict`.** The compile is certified (`CompileCorrect`). The corpus compiles exercise its completeness.
- **`decompile` and `decompile-diff`.** `fidelity-initstd`'s phase 5 is the decompile round trip on Init+Std.
- **`kernel-read-cache`.** The read cache only serves `kernel-check-ixe`'s diagnostics. The user-axiom tests run its path.
- **Pre-proof IxVM soundness and hypothesis-validation suites** (`ixvm-guard-certificate`, `ixvm-rec-run-bounds`, `ixvm-alias-block`, `ixvm-value-records`, `ixvm-telescope-block`, `ixvm-family-records`, `ixvm-family-graph-records`, `ixvm-twin-pair`, `ixvm-alias-formers`, `AliasParamHeads`, `ixvm-role-member-census`, `ixvm-op-order-scan`, `ixvm-decl-check-must-reject`, `ixvm-advice-must-reject`, `ixvm-quot-advice-must-reject`, `ixvm-refusal-controls`, `ixvm-recgen`, `ixvm-guard-corpus`, and `ixvm-mutator`). These manual suites tested finite fixtures for soundness properties and intermediate obligations now unconditionally proved for all inputs by `IxVM.Refinement.Endpoint.circuitComposed` (zero residual hypotheses). Completeness, parity, FFT pins, and Rust-host/FFI/circuit-verdict smoke coverage remain in `ixvm-kernel-checks`, `ixvm-eval`, `ixvm-exploits`, `ixvm-must-reject`, `ixvm-model-advice`, `ixvm-ind-variations`, `ixvm-shape-guards`, `ixvm-field-reduction`, `ixvm-circuit-verdict`, and `ixvm-differential`.

**Replaced:**

- **`record-decoding`.** Its refusals moved into `kernel-record-check` (primary): orphan, noncanonical and oversized records, phase precedence, and a cache beside bad bytes. `kernel-check-ixe` passes host-decoded records straight to the certified step, so these refusals aren't covered by a proof. The parallel decoder's agreement with the serial one is proved (`Ix.RoleBinding.RecordDecoding.parallel_eq`, `recordStore_eq_parallel`).
- **`aiur-hashes`, `multi-stark`, `recursive-verifier`, and `ixvm-subst-boundaries`.** These drove the retired `Ix.Aiur.Protocol` in-Lean bytecode interpreter and legacy `aiur_circuit%` generated Rust modules. Their coverage moved to `u32_tests`, `library_tests` + `library_check` (BLAKE3 0..4097 bytes, U64 and byte gadgets), `formal-aggregate-tests`, `stark-verifier test` (digest, truncation, opening, width, claim, row-bound and fixed-height rejections), and the `ci:ixvm` suites against the compiled formal IxVM artifact.
