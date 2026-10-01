# Trace-sharding PRs: handoff

State as of 2026-09-23. Two stacked ix PRs and two stacked multi-stark PRs
carry `sb/aiur-trace-sharding-gpu`; this file lists what is still open on
each and how the branches relate.

## Branches

| Repo | Branch | Base | Worktree | Status |
|---|---|---|---|---|
| ix | `sb/aiur-batch-proving` (PR #643) | `main` | `~/repos/ix.batch-proving` | merged as `2ff0e5ce` |
| ix | `sb/aiur-gpu-lanes` (PR #644) | `main` | `~/repos/ix.gpu-lanes` | the GPU code and one document; the SP1 terminal, dated bench reports and planning documents stay on `sb/aiur-gpu-lanes-sp1-compress` as a reference |
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
   - `Benchmarks/Compile/restore-flt-cache.sh`: removed from the tree; the
     bucket keeps a copy and `docs/anthropic-flt-lake-cache.md` documents
     the restore.
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

## PR 2 (`sb/aiur-gpu-lanes`, #644)

Three code commits on `main` (the multi-stark pin and the
`cuda-trace-codegen` feature; the lanes scheduler, GPU trace runtime and
metrics; the trace codegen) and one document,
[`aiur-gpu-proving.md`](aiur-gpu-proving.md), which is the entry point
for building, running and benchmarking the GPU prover.

Everything else the GPU work produced is on `sb/aiur-gpu-lanes-sp1-compress`
and is not meant to merge: the SP1 terminal (`ix compress-root`,
`sp1-compress/`, its guest fixtures and the `IX_SP1` build switch), the
dated `bench/*-2026-09-*` reports with their logs and scripts, and the
planning and review documents. The fixture generator for the trace codegen
parity tests, `bench/aiur-trace-codegen-2026-09-16/Generate.lean`, lives
there too; `aiur-gpu-proving.md` §4 says how to run it.

Not verifiable locally: the `cuda` and `cuda-trace-codegen` builds; there is
no GPU on this host. CI's `cuda-compile` job covers the `cuda` feature and
checks the generated trace bundle.

## multi-stark

- `sb/batch-proving` merged as multi-stark #80 (`a155ee4` on `main`);
  ix pins that commit.
- Open `sb/trace-sharding-gpu` against `main`, rebased onto `a155ee4`
  (the squash of its base). The local `multi-stark.trace-sharding`
  checkout was behind the remote; `git pull --ff-only` brings it to
  `59df87a`.
- tracing-texray `sb/per-span-peak` merged as texray #4 (`6d50167` on
  `main`); ix pins that commit.
