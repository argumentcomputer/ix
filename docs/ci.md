# CI and merge queue configuration

RunsOn CPU jobs use the default Spot policy by omitting `spot` from their
runner labels. This includes CPU benchmarks and the CUDA compilation check,
which does not run on a GPU. Future GPU benchmarks should explicitly request
`spot=false`. RunsOn may fall back to on-demand capacity when Spot is
unavailable or when provisioning an automatic recovery attempt.

Formal Aiur's CPU integration job exercises the CPU controls of
`formal-checks cuda` (`Tests/FormalChecks/Cuda.lean`). Actual CPU/CUDA proof and key parity, including
sharded IxVM, recursion, and aggregation, requires a GPU host running
`IX_TEST_CUDA=1 bash tools/ixvm/check-formal.sh`. The
[migration guide](formal-aiur-migration.md#cuda-and-native-builds)
documents the retained logs and report; the CUDA compilation job does not
provide hardware validation.

CI jobs request the `r7i+r8i+r7a+r8a` families and let RunsOn pick the size
from `cpu=`, so a Spot request can draw from several pools; exact r8i types
alone had no Spot capacity. Their Rust builds use the `portable` codegen mode
of the toolchain action, `x86-64-v4` plus `avx512vbmi2` and `gfni`, the
feature set every listed family shares, and their sticky lineages carry that
name so native artifacts never mix in. Valgrind builds `generic`, without
AVX-512, into the S3-backed actions cache under its own key, with S3-backed
sccache for Rust compilation. Benchmarks stay on exact `r8i.8xlarge` with
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
uses no grandfather baseline. `lake lint` runs it after the strict module
build and coverage checks.

Every Lean test entry is registered once, with its tier, in
`Tests/Main.lean` (the registry is `Tests/Registry.lean`). The tier says where
the entry runs:

| Tier | Where it runs | What it holds |
| --- | --- | --- |
| `primary` | `lake test` with no arguments: the `lean-test` job of CI Jobs, and Nix CI's `ix-tests` | the quick suites |
| `ci:cli` | a step of the `lean-test` job | the command-line integration tests |
| `ci:ixvm` | a step of the `lean-test` job, after `tools/ixvm/check-formal.sh`, on its claim artifact | claims through the formal IxVM program (`ixvm-proof test`) under the circuit verdict (every assertion checked, `IX_AIUR_CIRCUIT_VERDICT`; `=0` for plain execution): kernel verdicts, the exploit, arena, TagN, evaluation, binding, IO-ingress and circuit-verdict suites |
| `ci:compiler-closures` | a merge-tests partition | selected closures against the whole environment, auxiliary closure addresses, checker-support grounding, packing, the certified checker's pinned subjects and acceleration inputs, and the binding proof through the `ix` binary |
| `ci:misc` | a merge-tests partition, with the ZK voting prover | the tutorial, catalog and commit I/O |
| `ci:landing-initstd-cli` | a merge-tests partition | Init+Std through the `ix` binary: `ix compile-lean` with its report checks, whose artifact must match the reference digest in `Tests/Fixtures/initstd-reference.txt` and which `ix check-lean` must check with every role of the default table admitted; the Rust, pure and admission BLAKE3 on every record, blob and binding of that artifact; and `ix validate-lean` fidelity |
| `manual` | by hand only | entries that need inputs outside the repository, take minutes or hours, or are diagnostics; each states its reason |

The manual runner that proves through the production `ix_aggr` circuit,
`aggregate-binding-reuse`, takes minutes of recursion and about 190 GB, three
quarters of a 32-CPU merge-tests runner's memory, so it stays manual.
`binding-proof-cli` (`ci:compiler-closures`) runs `aggregate-binding-reuse`'s
flow without its two aggregates: the binding proof, the shard proofs that
assume it, their composition with it, and the refusals without it; the
aggregation circuit's handling of the binding is tested in
`formal-aggregate-tests` (`tools/ixvm/check-formal.sh`). Its proving budget is
64 GiB, so it runs in the merge queue, on a 32-CPU runner, rather than in every
pull request's `lean-test`.

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

The primary tier runs in two places per event: incrementally in `lean-test`,
and in Nix CI's sandbox from the Nix-built test binary on a fresh copy of the
tracked sources (the flake's one check, `ix-tests`; the Rust lints and tests
are `rust-test`'s). Nix CI's development shell only builds the library. In the
merge queue, the `build` job of Merge tests builds the partitions' targets and
the set-theory model using the CI sticky lineage and sccache. It records the
revision in `.lake/merge-build-revision` and saves its sticky snapshot.
Partitions use `sticky_save: false`, check the restored revision before any
local builds, and report a hit or miss in their logs and job summaries. A miss
warns and leaves Lake to build stale targets; it does not skip the tests.
There is no separate S3 archive handoff for these build outputs.

On `merge_group`, CI Jobs' `lean-test` also disables sticky saves so it cannot
replace the merge build's snapshot for the same queue ref. Its `main` push
runs still refresh the default-branch baseline. The workflows still duplicate
some compilation; the [build and cache design](ci-build-cache-design.md)
describes the proposed common producer.

Pushes to `ix.ci-merge-tests` run Merge tests against the pushed commit to
validate the upgraded RunsOn cache behavior. The branch filter does not enable
merge tests on other pushes. PR result comments remain specific to authorized
`!merge-tests` dispatches.

Valgrind runs `ffi-tests`, the `ffi`
suite as an executable of its own, whose import closure leaves out the test
binary's proofs. The certification statements' freeze, `Ix.Cert.Audit`, is
built by `check-kernel` and `lake lint`, not by the test binary.

Valgrind's generic Rust and Lake artifacts use S3-backed archive caches.
sccache also caches the Rust static libraries when a fresh checkout invalidates
Cargo's workspace fingerprints. Its keys include the compiler flags, keeping
generic and portable builds separate. A generic sticky cache would need its
own lineage and a build on `main` to seed the default-branch snapshot; the
portable CI lineage cannot supply compatible Rust artifacts.

## Required checks

The branch protection or ruleset for `main` must require these aggregate
checks in place of their individual job checks:

| Workflow | Required check |
| --- | --- |
| CI Jobs | `ci-gate / pass` |
| Nix CI | `nix-gate / pass` |
| Merge tests | `merge-gate / pass` |

Remove the raw RunsOn job checks, `Nix Tests`, and the old `Merge tests`
aggregate from the required-check list when enabling these gates. Requiring
an individual Spot job would still eject the PR as soon as it is interrupted.
Do not require the gates' `interrupted` or `Detect Spot interruption` checks.
Independent GitHub-hosted or security requirements can remain, provided they
also report the checks the merge queue expects.

CI Jobs and Nix CI run on both `pull_request` and `merge_group`. The
merge-queue test tiers and the certified kernel gate (`lake run check-kernel
--with-model`, a merge-tests partition) run against the merge group's synthetic
commit, or on an authorized `!merge-tests` comment. The pull-request-only stub
publishes `merge-gate / pass` so a PR can enter the queue before the
merge-queue suites run.
It never runs on `merge_group`, and merge-tests.yml never runs on
`pull_request`, so each commit shows one `merge-gate / pass` check under the
shared workflow name.

The stub runs nothing: a green `merge-gate / pass` on a pull request says
nothing about the merge-queue tiers, the certified kernel gate (the only job
that builds the standalone `IxC` package with its audits, and the set-theory
model) or Valgrind. They guard `main` only while `main` requires
`merge-gate / pass` and every merge goes through the queue, which are
repository settings these files cannot check. To run them on a pull request
before queueing it, comment `!merge-tests`.

`Report merge tests` runs only for authorized `!merge-tests` comments, after
the gate finishes. It reports a pending Spot retry when the gate succeeds
with unsuccessful test jobs, and updates the same comment after the retry.
The report does not contribute to the gate's verdict and is not a required
check. Gate failures, including detector errors, are reported as failures.
A newer `!merge-tests` on the same PR cancels the older run, whose comment then
reports it cancelled. A PR without a test merge commit, such as one that
conflicts with its base, gets a comment saying so instead of a test run.

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

**Replaced:**

- **`record-decoding`.** Its refusals moved into `kernel-record-check` (primary): orphan, noncanonical and oversized records, phase precedence, and a cache beside bad bytes. `kernel-check-ixe` passes host-decoded records straight to the certified step, so these refusals aren't covered by a proof. The parallel decoder's agreement with the serial one is proved (`Ix.RoleBinding.RecordDecoding.parallel_eq`, `recordStore_eq_parallel`).
- **`aiur-hashes`, `multi-stark`, `recursive-verifier`, and `ixvm-subst-boundaries`.** These drove the retired `Ix.Aiur.Protocol` in-Lean bytecode interpreter and legacy `aiur_circuit%` generated Rust modules. Their coverage moved to `u32_tests`, `library_tests` + `library_check` (BLAKE3 0..4097 bytes, U64 and byte gadgets), `formal-aggregate-tests`, `stark-verifier test` (digest, truncation, opening, width, claim, row-bound and fixed-height rejections), and the `ci:ixvm` suites against the compiled formal IxVM artifact.
