# CI and merge queue configuration

RunsOn CPU jobs use the default Spot policy by omitting `spot` from their
runner labels. This includes CPU benchmarks and the CUDA compilation check,
which does not run on a GPU. Future GPU benchmarks should explicitly request
`spot=false`. RunsOn may fall back to on-demand capacity when Spot is
unavailable or when provisioning an automatic recovery attempt.

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
uses no grandfather baseline. `lake lint` runs it after the strict module
build and coverage checks.

Every Lean test entry is registered once, with its tier, in
`Tests/Main.lean` (the registry is `Tests/Registry.lean`). The tier says where
the entry runs:

| Tier | Where it runs | What it holds |
| --- | --- | --- |
| `primary` | `lake test` with no arguments: the `lean-test` job of CI Jobs, and Nix CI's `ix-tests` | the quick suites |
| `ci:cli` | a step of the `lean-test` job | the command-line integration tests |
| `ci:compiler-closures` | a merge-tests partition | selected closures against the whole environment, auxiliary closure addresses, checker-support grounding, packing, the certified checker's pinned subjects and acceleration inputs, and the binding proof through the `ix` binary |
| `ci:misc` | a merge-tests partition, with the ZK voting prover | the tutorial, sharding, catalog and commit I/O, and the IxVM suite |
| `ci:landing-initstd-cli` | a merge-tests partition | Init+Std through the `ix` binary: `ix compile-lean` with its report checks, whose artifact must match the reference digest in `Tests/Fixtures/initstd-reference.txt` and which `ix check-lean` must check with every role of the default table admitted; the Rust, pure and admission BLAKE3 on every record, blob and binding of that artifact; and `ix validate-lean` fidelity |
| `manual` | by hand only | entries that need inputs outside the repository, take minutes or hours, or are diagnostics; each states its reason |

The manual runners that prove through the production `ix_aggr` circuit,
`aggregate-proof` and `aggregate-binding-reuse`, take minutes of recursion and
about 190 GB, three quarters of a 32-CPU merge-tests runner's memory, so they
stay manual. `binding-proof-cli` (`ci:compiler-closures`) runs
`aggregate-binding-reuse`'s flow without its two aggregates: the binding proof,
the shard proofs that assume it, their composition with it, and the refusals
without it; the aggregation circuit's handling of the binding is tested in
`ix-aggr` (primary). Its proving budget is 64 GiB, so it runs in the merge
queue, on a 32-CPU runner, rather than in every pull request's `lean-test`.

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
merge queue, the `build` job of Merge tests builds the partitions' targets once
on their sticky lineage, and the partitions start from its snapshot; each
partition's log says whether it did. Valgrind runs `ffi-tests`, the `ffi`
suite as an executable of its own, whose import closure leaves out the test
binary's proofs. The certification statements' freeze, `Ix.Cert.Audit`, is
built by `check-kernel` and `lake lint`, not by the test binary.

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
--with-model`, then `lake run check-kernel-bridge`, a merge-tests partition)
run against the merge group's synthetic commit, or on an authorized
`!merge-tests` comment. The pull-request-only stub
publishes `merge-gate / pass` so a PR can enter the queue before the
merge-queue suites run.
It never runs on `merge_group`, and merge-tests.yml never runs on
`pull_request`, so each commit shows one `merge-gate / pass` check under the
shared workflow name.

The stub runs nothing: a green `merge-gate / pass` on a pull request says
nothing about the merge-queue tiers, the certified kernel gate (the only job
that builds the standalone `IxCK` package with its audits, and the set-theory
model; the kernel-bridge model is also built on pull requests whose changes
reach it, below) or Valgrind. They guard `main` only while `main` requires
`merge-gate / pass` and every merge goes through the queue, which are
repository settings these files cannot check. To run them on a pull request
before queueing it, comment `!merge-tests`.

`Report merge tests` runs only for authorized `!merge-tests` comments, after
the gate finishes. It reports a pending Spot retry when the gate succeeds
with unsuccessful test jobs, and updates the same comment after the retry.
The report does not contribute to the gate's verdict and is not a required
check. Gate failures, including detector errors, are reported as failures.

## The certified compiler (IxCC)

`IxCC/` is a Lake package of its own (`«ix-cc»`). It requires the `IxCK`
package beside it (`../IxCK`, of which it imports only the Ixon codec) and
Blake3; the root package does not require it. Its
[CI guide](../IxCC/docs/ci.md) describes its 16 required checks, which the
flake exposes as `ixcc-*`, with `packages.ixcc` and `apps.ixcc`. IxCC's Nix
expressions select their own sources (`IxCC/nix/sources.nix`): `IxCC/`, the
codec closure its trust ledger hashes and, for the ledger check, `flake.lock`,
`.github/actions` and `.github/workflows/ixcc.yml`. The host's source sets
leave `IxCC/` out, so a change on one side rebuilds nothing of the other.

The reusable workflow `.github/workflows/ixcc.yml` builds every `ixcc-*`
check, within a 60-minute job timeout. It first requires the flake's
evaluated `ixcc-*` checks to be exactly the trust ledger's `required_checks`
(the attributes of `IxCC/nix/checks.nix`), so a check dropped from or added
to the flake fails it. CI Jobs calls it when a pull request or `main` push
changes IxCC's inputs (the `Detect IxCC changes` path filter) and reports to
`ci-gate` through `IxCC result`, which also succeeds when the change does not
reach IxCC. Merge tests calls it on every merge group, as the `IxCC
(certified compiler)` partition of `merge-gate`. Nix CI evaluates the
`ixcc-*` checks without building them. IxCC's trust ledger pins `ixcc.yml`
by its SHA-256 and audits the local actions it uses, with every remote action
pinned to a commit and listed in its `ci_actions`. It does not audit ix's
other workflows, which track `argumentcomputer/ci-workflows@main` and
`argumentcomputer/lean-update@dev` by branch. It records `flake.lock`'s
revisions and `IxCC/lean-toolchain`, and requires the root `lean-toolchain`
to equal IxCC's. So the weekly Rust update (`update-rust.yml`, which runs
`nix flake update`), a Lean update (`update.yml`) and a Dependabot bump of
`ixcc.yml`'s actions each fail `ixcc-trusted-extern-ledger` until the ledger
is updated in the same pull request: "Routine updates" in
[IxCC's ledger document](../IxCC/docs/trusted-extern-ledger.md) lists the
fields and the commands (`check-trusted-externs --record`, then
`tools/record-ledger-pins.jq`, from `IxCC/`).

The repository-wide tools treat `IxCC/` as follows:

| Tool | IxCC |
| --- | --- |
| Root `lake build`, `lake test`, `lake lint` (`build-all`) | Not built: no root library or executable claims the `IxCC.` module root |
| `check-modules` | Not covered: `IxCC/` has its own lakefile, so it is another workspace. IxCC's `check-build-graph` inventories its modules. Its checks build the production library, every executable and the proof and fence aggregate `IxCCTests.Proofs`, not every module: the kernel-evaluation and artifact modules IxCC's CI guide lists as manual are built by no check |
| `check-source-docs` | Not scanned. Its rules name ix's retired compiler APIs and private plans, and IxCC's frozen records quote some of those names (recorded compiler output and the historical reference-check command of its fixture refreeze). IxCC's ledger scans its own sources and the IxCK codec closure for `axiom`, `sorry` and every spelling of native evaluation it can see (`native_decide`, `decide +native`, `native := true`, the `ofReduceBool`-style axioms), inventories their externs and `@[csimp]` theorems, and refuses `implemented_by` in the codec closure |
| `kernel-layering`, `kernel-trust-surface` | Not applied: they fence `IxCK/Kernel/`. IxCC imports only the codec, and its ledger rejects any other `IxCK` import |
| `ix codegen --check` | Not applicable: it covers IxVM's generated Rust |
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
warnings) and checks that the theorems its `Audit.lean` fences are exactly
the root lakefile's `kernelBridgeFences`. Merge tests run it in the kernel
partition on every merge group. CI Jobs runs it on pull requests and `main`
pushes whose changes reach it (the `kernel-bridge` output of the same path
filter: `IxCC/`'s Lean sources and Lake files, `IxCK/`, the model, the root
`lean-toolchain` and `lakefile.lean`, `ci.yml` and the local actions) and
reports through `Kernel bridge result`, as `IxCC result` does. It shares
IxCC's package directory, where Lake checks out and builds Blake3, and writes
IxCK's objects to `.lake/kernel`; both workflows keep `IxCC/.lake` and
`Models/KernelBridge/.lake` on the sticky disk. Its toolchain is in the
toolchain check, and `update.yml` bumps it.

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
