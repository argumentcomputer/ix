# Trace-sharding PRs: handoff

State as of 2026-09-23. Two stacked ix PRs and two stacked multi-stark PRs
carry `sb/aiur-trace-sharding-gpu`; this file lists what is still open on
each and how the branches relate.

## Branches

| Repo | Branch | Base | Worktree | Status |
|---|---|---|---|---|
| ix | `sb/aiur-batch-proving` (PR #643) | `main` | `~/repos/ix.batch-proving` | local tip `a17b5f47`, two commits ahead of the pushed `7421baf2` plus a merge |
| ix | `sb/aiur-gpu-lanes` (PR 2) | `sb/aiur-batch-proving` | `~/repos/ix.gpu-lanes` | based on the old PR 1 tip `7421baf2`; needs rebasing |
| multi-stark | `sb/batch-proving` | `main` | `~/repos/multi-stark.batch-proving` | pushed; the first eight fork commits, `6495cd8..231942a` |
| multi-stark | `sb/trace-sharding-gpu` | `sb/batch-proving` | `~/repos/multi-stark.trace-sharding` | on the remote at `59df87a`; the PR is the 32 commits above the base |

The scratch worktree `~/repos/ix.gpu-merge` on `tmp/pr2-merge` holds the
merged PR 2 tree with a full Lean build; delete it when PR 2 is rebased.

## PR 1 (`sb/aiur-batch-proving`, ix #643)

Local commits not yet on the remote:

- `978a1a8b` merges main through #642. The batch-proving changes were
  ported onto the `MultiStark` library, `Ix/Aggr/*`, `Ix/Shard/*` and the
  split `crates/ffi/src/aiur/aggregate/*` modules. Verified: CI's clippy,
  rustfmt, `ix codegen --check`, the FFI aggregate tests, the primary Lean
  suites, `aggregate-proof`, `ixvm` (pins unchanged) and `shard-map`.
- `32fddd5e` adds `bench-typecheck --trace-shards [--max-ram GiB]`, the
  `ixvm-trace-shards` metric and the `BENCH_TRACE_SHARDS=<GiB>` passthrough
  key. Smoke-tested on a fresh 75-constant Init closure (both rows proved,
  verified, one shard each).
- `a17b5f47` merges main through #622 (the CI refactor). **Unverified**:
  main rewrote `bench-pr.yml`, `docs/benchmarking.md`, `BenchCmd.lean`,
  `BenchReport.lean`, `Ix/Meta.lean`, `Ix/Watchdog.lean` and the kernel
  crate; the merge was clean and the `BENCH_TRACE_SHARDS` entries survived
  in all four places, but nothing has been built on this tip.

To do, in order:

1. Verify the #622 merge on the tip:
   ```
   cd ~/repos/ix.batch-proving
   nix develop --command lake build ix bench-typecheck
   cargo clippy --workspace --all-targets --features ix-ffi/parallel,ix-ffi/net,ix-ffi/test-ffi -- -D warnings
   nix develop --command lake exe IxTests bench-measures cli aiur-prove
   nix develop --command lake exe ix codegen --check
   ```
   Read the merged `docs/benchmarking.md` config-key block and the
   `bench-pr.yml` header once by eye; main reflowed both files.
2. Push: `git push origin sb/aiur-batch-proving`.
3. Answer the review on #643 (arthurpaulino, 2026-09-23). Suggested substance:
   - Overall question, "fully migrate to the batch approach?": yes.
     `AiurProof` is `BatchProof`; a plain prove is a one-shard batch and
     `AiurSystem::verify` accepts nothing else.
   - `Benchmarks/Compile/restore-flt-cache.sh`: tracked on purpose,
     `docs/anthropic-flt-lake-cache.md` links it. It is the one unrelated
     commit in PR 1; drop `7421baf2`'s script and guide into PR 2's docs
     commit if the reviewer prefers.
   - `acceptance.rs` and the other tests forging through `prove_batch`
     only: follows from the first point, since a single `system.system.prove`
     proof can no longer be handed to `AiurSystem::verify`. The single-proof
     prover keeps its own tests in multi-stark.
   - `execute.rs` pointer base: one base per record for every width, entry
     `i` of each table at `base + i`. Bases across a batch are
     `r * pointer_stride(workers)`, `2^32 / next_pow2(workers)`, a fixed
     split of the u32 pointer space, so no table height is involved.
     Per-width bases would gain nothing because width is part of every
     memory message. The real limit is the kernel's u32 pointer comparison,
     `2^32 / workers` entries per table per record; the attempt to lift it
     (`036b21f1`) was reverted on the branch.
   - `kernel.rs` string FFI arguments: pre-existing style of
     `rs_shard_env_static` (`num_shards`, `ram_gib`, `balance_pct` were
     already strings); the PR added `layout` and `exec_ahead` the same way.
     Switching the numeric ones to `LeanNat` is a small self-contained
     change if wanted in this PR.
4. Run the benchmark once the base is on bencher:
   `!benchmark aiur BENCH_TRACE_SHARDS=<GiB>` (or add `fresh` to force a
   local base run). Without the key, every constant proves as a one-shard
   batch on both sides and the run measures only the batch protocol's fixed
   cost. Note the flag takes whole GiB; the smallest budget still fit the
   smoke constants in one shard, so the multi-shard path of the benchmark
   has not been exercised.
5. Optional follow-ups the reviewer may ask for: `LeanNat` arguments on
   `rs_shard_env_static`; moving the FLT cache script and guide to PR 2.

Untracked in the worktree: `docs/bencher-sharded-proving.md`, not written
by this work; leave it or commit it deliberately.

## PR 2 (`sb/aiur-gpu-lanes`)

The branch is the GPU half (lanes, GPU trace runtime, CUDA trace codegen,
sppark pin, SP1 terminal, docs and bench scripts) as five commits on the
old PR 1 tip. It must be rebuilt on the new PR 1 tip, and it will collide
with #642 in its own files, since `lanes.rs` and the subtree plan use
aggregate internals that now live in `aggregate/plan.rs`,
`aggregate/prove.rs` and `aggregate/scheduler.rs`, and `ProveCmd.lean`'s
lanes block and `AggregateCmd.lean`'s `--subtree` flag sit on the
restructured commands.

Recommended mechanics, the same as the first PR 2 cut:

1. In `~/repos/ix.gpu-merge`, merge `sb/aiur-batch-proving` into
   `tmp/pr2-merge` (it already contains the resolved main-into-GPU merge).
   Conflicts will be the #642 layout; port `lanes.rs`, the subtree plan
   (`leaves_under`, `split_frontier`, `subtree_plan` and its test) into the
   new modules, and re-add the lanes hooks to `ProveCmd.lean`,
   `AggregateCmd.lean` and `Ix/Aiur/Protocol.lean`.
2. Regenerate: `lake exe ix codegen`, `lake exe ix codegen --trace-bundle`,
   and the fixtures with
   `lake env lean --load-dynlib=.lake/packages/Blake3/.lake/build/lib/libBlake3_Blake3Rust.so --load-dynlib=.lake/packages/Blake3/.lake/build/lib/libBlake3_Blake3.so --run bench/aiur-trace-codegen-2026-09-16/Generate.lean`.
   Both `--check` forms and the fixture `--check` must pass.
3. Verify as before: CI's clippy, `cargo test --release -p aiur`, the
   primary suites plus `ffi` and `aiur-trace-plan`, `--ignored ixvm`,
   `--ignored shard-map`.
4. Recut the five commits on `sb/aiur-batch-proving` by path
   (`git read-tree --reset -u tmp/pr2-merge`, then `git reset` and
   `git add -A <paths>` per group), replacing `sb/aiur-gpu-lanes`.
5. Retarget or reopen the PR with base `sb/aiur-batch-proving`.

Things PR 2 already fixed that must not be lost in the recut:

- The trace codegen emits the six-u16-limb u32 comparison witness of #635
  on both the host and CUDA paths (`TraceCodegen.lean`, `TraceCuda.lean`,
  `trace_codegen.rs`).
- The Rust emitter is lint-clean by construction (tail expressions,
  infallible writers returning unit and wrapped in closures for the
  registry, elided zero offsets and shifts) in `Codegen.lean` and
  `TraceCodegen.lean`.
- FFI lint fixes in `lanes.rs`, `profile/metrics.rs` and `profile.rs`.
- The bench tree keeps only scripts, READMEs and summaries; the root
  `HANDOFF-recursion-fri-params.md` moved to
  `docs/recursion-fri-params-handoff.md`.

Not verifiable locally: the `cuda`, `cuda-trace-codegen` and SP1 guest
builds; there is no GPU or Succinct toolchain on this host. CI's
`cuda-compile` job covers the `cuda` feature.

## multi-stark

- `sb/batch-proving` is pushed; open its PR against `main` if not done.
- Open `sb/trace-sharding-gpu` against `sb/batch-proving`; retarget to
  `main` after the first merges. The local `multi-stark.trace-sharding`
  checkout was behind the remote; `git pull --ff-only` brings it to
  `59df87a`.
- tracing-texray `sb/per-span-peak` (`fedd785`) is pushed and pinned by ix
  only; it needs its own PR against texray's main.
