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

Every Lean test entry is registered once, with its tier, in
`Tests/Main.lean` (the registry is `Tests/Registry.lean`). The tier says where
the entry runs:

| Tier | Where it runs | What it holds |
| --- | --- | --- |
| `primary` | `lake test` with no arguments: the `lean-test` job of CI Jobs, and Nix CI's `ix-tests` | the quick suites |
| `ci:cli` | a step of the `lean-test` job | the command-line integration tests |
| `ci:compile-pipeline` | a merge-tests partition | the Lean and Rust compilers against each other (input conversion, the reference graph and its condensation, serialization, decompilation, Lean's auxiliaries on closure-only environments) and the compilers' refusals |
| `ci:compiler-closures` | a merge-tests partition | selected closures against the whole environment, checker-support grounding, packing, admission of selected targets, and the certified checker's pinned subjects and acceleration inputs |
| `ci:compile`, `ci:decompile` | one merge-tests partition each | the whole test environment through the compiler, and back |
| `ci:misc` | a merge-tests partition, with the ZK voting prover | the Rust kernel on the test environment and the tutorial, Init+Std compile fidelity, sharding, catalog and commit I/O, the primitives, and the IxVM suite |
| `ci:landing-compilers` | a merge-tests partition | the Lean compiler's output independent of its schedule, on the fixture corpus; the Rust compiler's compile, serialize and decompile roundtrip over the test environment |
| `ci:landing-initstd` | a merge-tests partition | end-to-end checks on Init+Std: the certified compiler against the pipeline and the Rust compiler, role binding and evidence, a reading premise on every inductive, and the admission hash |
| `manual` | by hand only | entries that need inputs outside the repository, take minutes or hours, or are diagnostics, and the entries that assert the former canonical rewriting (runnable by name until the code they test is removed); each states its reason |

`lake test -- --tier <tier>` runs one tier; `--tier landing` runs the two
landing partitions. The registry's primary self-test, `ixtests-registry`,
fails when a CI tier has no entry, when no workflow runs a CI tier (comments
do not count), or when a workflow names a tier the registry does not define.
It also fails when an entry of `required` in `Tests/Main.lean` is missing,
registered twice or in another tier, and when that list names no entry of
some tier that runs in CI; moving a required check to `manual` therefore
means editing the list in the same change. The check of the workflows is
textual: a step disabled by an `if:` still counts. A merge-tests partition
must finish well within the merge queue's status-check timeout: split a tier
into two jobs before it approaches it.

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

CI Jobs and Nix CI run on both `pull_request` and `merge_group`. The ignored
tests and the certified kernel gate (`lake run check-kernel --with-model`, a
merge-tests partition) run against the merge group's synthetic commit, or on
an authorized `!merge-tests` comment. The pull-request-only stub publishes
`merge-gate / pass` so a PR can enter the queue before the ignored suites run.
It never runs on `merge_group`, and merge-tests.yml never runs on
`pull_request`, so each commit shows one `merge-gate / pass` check under the
shared workflow name.

`Report merge tests` runs only for authorized `!merge-tests` comments, after
the gate finishes. It reports a pending Spot retry when the gate succeeds
with unsuccessful test jobs, and updates the same comment after the retry.
The report does not contribute to the gate's verdict and is not a required
check. Gate failures, including detector errors, are reported as failures.

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
