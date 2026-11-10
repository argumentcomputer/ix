# CI and benchmark follow up work

Status as of 2026-11-09, implementation at `fa95cce6a`. The benchmark
subcommands, restored `fresh` option, and monthly Dependabot configuration
are committed. Forty focused benchmark tests, type-checking of the changed
Lean modules, parser-output checks, and workflow shell/cache checks passed.
Live CI and benchmark validation of this tip is still pending.

The current branch can be published for validation independently of the
larger [CI build and cache design](ci-build-cache-design.md). Completing that
design is separate work, not a prerequisite for the trial push.

## Choose the publication path

- [ ] Decide whether to publish `ci-merge-tests` separately or incorporate its
  changes into [formal-aiur-perf PR 681](https://github.com/argumentcomputer/ix/pull/681).
  This branch contains 22 commits above the **local** `formal-aiur-perf` at
  `f46880944`. The published PR was at `b00ebf68d` when checked; it is a
  different history. Refresh the relevant refs and reconcile the histories
  before updating that PR. Do not treat this branch as a direct continuation
  of its published tip.
- [ ] For a separate trial, publish to `ix.ci-merge-tests`, the remote branch
  named in [Merge tests' push trigger](../.github/workflows/merge-tests.yml).
  The local branch name is `ci-merge-tests`; pushing under that name would
  not exercise this trigger. The maintainer runs:

  ```sh
  git push -u origin HEAD:refs/heads/ix.ci-merge-tests
  ```

`InitStd-exec.ixes` is a generated, untracked shard manifest. It is not part
of the branch's source changes and does not need to be included in a push.

## Validate the current CI changes

- [ ] Record the trial commit, run URL, job results, and durations. Verify the
  merge-test partitions, certified-kernel checks, and Valgrind job execute.
- [ ] Check the deployed RunsOn version in the runner logs. For a warm run,
  verify every partition restores the producer's exact
  `.lake/merge-build-revision`; inspect its cache hit/miss summary and any
  repeated compilation. A green test result alone does not prove the cache
  handoff worked.
- [ ] Confirm the merge build is the only writer of its shared snapshot.
  Partitions and CI's `lean-test` must not replace it on the same merge-queue
  ref. Exercise missing/stale snapshots and retries; tests must still run.
- [ ] Exercise `!merge-tests` on an open PR: all jobs must use the resolved
  test SHA, a newer request must supersede the older request, and the result
  comment must report failures or cancellation. Merge-group runs must remain
  independent and supply their required checks.

See [CI configuration](ci.md) for the implemented workflow and required
check names.

## Validate benchmark modes and fresh runs

- [ ] Start with one constant, using
  `BENCH_CONSTANTS=Nat.add_comm BENCH_ENVS=none`, and exercise
  `!benchmark ixvm execute`, `!benchmark ixvm prove`, and
  `!benchmark ixvm compress fresh`. Verify that compress includes execution,
  proving, aggregation, root verification, KZG compression, and compressed
  proof verification. Confirm each stage appears in the result comment.
- [ ] Verify both revisions use the PR's benchmark driver and memory-cap
  script, while the measured binaries and compiler-keyed Aiur programs
  belong to the selected revision. Base runs must retain `--repo base`.
- [ ] Check that prove/compress requests measure their base stages instead
  of accepting execution-only Bencher rows. Confirm ordinary execute runs
  can still reuse a complete baseline.
- [ ] Exercise `!benchmark compile fresh BENCH_ENVS=InitStd`. Confirm fresh
  requests bypass stored baseline results, published binaries, `.ixe` files,
  and compile rows; rebuild measured products; and retain dependency caches.
  A cached head binary may parse the command, but must be replaced before
  measured jobs receive it.
- [ ] Check failure reporting: unavailable base results remain visibly
  missing, rejected PR rows fail the run, and completed rows survive an OOM
  or interrupted cell. Confirm fresh runs do not publish benchmark-product
  cache entries or upload measurements to Bencher.

The [benchmarking guide](benchmarking.md) describes command syntax, stage
metrics, memory limits, and the distinction between constant and env rows.

## Complete the larger cache redesign separately

- [ ] Replace overlapping CI and merge-test builds with one producer and
  an explicit dependency graph for their consumers. Share the target list
  so new consumer dependencies cannot be omitted from the producer.
- [ ] Preserve PR fast checks, on-demand merge tests, and required gates
  `ci-gate / pass`, `merge-gate / pass`, and `nix-gate / pass`. Keep the Nix,
  Rust, CUDA, benchmark, and generic Valgrind build contracts separate.
- [ ] Measure total job time, including provisioning and cache transfers,
  against the design's 15-minute ceiling, aiming for 10–12 minutes. Split or
  optimize expensive test groups, including IxVM, based on the new timings.
- [ ] If snapshot misses persist, inspect producer completion and consumer
  snapshot selection before choosing another transfer mechanism. An explicit
  S3 artifact handoff is not implemented in the current trial.

Record validation results and remaining failures here before rollout, with
links to the relevant runs. The detailed design and earlier measurements
remain in [CI build and cache design](ci-build-cache-design.md).
