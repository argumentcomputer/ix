# Incremental catalog proving

`ix catalog prove` certifies a compiled catalog and retains the corpus,
partition and proof references needed to certify a subsequent revision.
Lean/Lake builds and their olean caches continue to work normally. Proving
runs when publishing a snapshot, rather than during the editing loop.

## Baseline and subsequent commit

Build the library normally, then export a closed Ixon environment. For
example, `Export.lean` can import the library being certified. Run the
compile command in that library's Lake environment with the built `ix`
executable available on `PATH`:

```sh
lake env ix compile Export.lean --no-build --out A.ixe
ix catalog assemble A.ixc A.ixe --labels Library --pins 'git:<repo>@<commit-A>'
ix catalog prove A.ixc --allow-axioms axioms.txt --plan-only --json
ix catalog prove A.ixc --allow-axioms axioms.txt
```

GPU runs automatically use all visible devices, the available CPU threads,
and a host-memory budget derived from available RAM and remaining cgroup
capacity. Omit `--max-ram` for normal runs; `--max-ram 0` is equivalent.
Automatic budgeting still enforces memory admission, workspace reservations
and headroom.

`axioms.txt` is an independently reviewed allowlist of axiom declaration
addresses, one 64-character hex address per line; blank lines and `#`
comments are accepted. An omitted file means no axioms for a fresh
baseline. A catalog containing unapproved axioms is rejected before new
proving starts, with their addresses in the error. Review those
declarations rather than automatically approving everything in an export.
The same policy covers historical declarations retained in the corpus.

At commit B, build and export again, keeping A's catalog and the worker's
proof store and caches:

```sh
lake env ix compile Export.lean --no-build --out B.ixe
ix catalog assemble B.ixc B.ixe --labels Library --pins 'git:<repo>@<commit-B>'
ix catalog prove B.ixc --base A.ixc --plan-only --json
ix catalog prove B.ixc --base A.ixc
ix catalog verify-proof B.ixc --allow-axioms axioms.txt --json
```

B inherits A's axiom policy unless an explicit file is supplied; that
file must describe the same policy. `verify-proof` requires an independent
allowlist when the recorded policy is nonempty. A recipient must also
authenticate the expected catalog/source association separately: a proof
of Ixon checking does not prove that a particular source commit produced
those bytes.

The driver verifies A's certificate, merges A's retained corpus with B's
pieces, and partitions newly required blocks. It preserves old ownership
and the old aggregation subtree. Leaf proofs are looked up by exact claim
and verified before reuse; aggregate proofs reuse the existing aggregate
cache. CUDA builds use all visible GPUs, with leaf execution, proving and
aggregation pipelined through a shared host-memory pool. Budget-driven
splits are saved as B's final
partition. A new projection of an old mutual block can change its owner's
claim, which requires new evidence for that leaf.

Old versions remain in the anonymous corpus. The record separately binds
the current snapshot and verifies that all its addresses are covered.
Consequently, deleting a declaration or reverting to already certified
content can reuse the verified base root directly, without invoking the
prover or aggregator. This requires the same corpus root and partition,
and all recorded leaf wrappers to remain available and match their claims.
Missing or corrupt wrappers take the ordinary cache recovery path. The new
record binds the current snapshot even when its proof root is unchanged.
Changing a widely referenced declaration can still change many dependent
addresses and require substantial proving.

For example, editing `B` in a proved chunk `{A, B, C}` leaves that chunk
and its proof intact. The new versions of `B` and any dependents whose
addresses change go into new chunks, whose proofs are aggregated with the
retained evidence. Old declarations and mutually defined blocks keep their
ownership; chunk sizes for new content follow the existing partition and
memory-admission heuristics.

Repeating `ix catalog prove B.ixc` after success validates its artifacts and
root certificate and returns without invoking either prover or aggregator.
For C, use `--base B.ixc`. Keep each catalog manifest and its pieces immutable.

## Planning, interruption and persistent state

`--plan-only` creates or resumes a pending plan, and verifies the supplied
base certificate, without executing new checking claims or generating
proofs. Its JSON includes new subject counts, unchanged and changed base
claims, and each planned shard's claim and frontier size. Each claim has a
`retainedFromBase` flag determined by exact claim identity. `newClaims`
counts claims absent from the base, and `subjectsInNewClaims` counts their
subjects, including older subjects when a block's claim changes. The final
report recalculates these counts after any budget-driven splits.

These counts describe compatible statements, not guaranteed cache hits or
proofs generated: missing leaf objects can still require re-proving, while
claims absent from the base may already be cached from another run. Direct
base-root reuse reports `reusedBaseRoot: true` and `newProofs: 0`.

After an interruption, rerun the same command with the same catalog,
`--base` and profile. Completed leaf and aggregate proofs remain cached.
The driver restores leaf-index hints from completed records and from a
pending plan that finished its leaf phase; the existing prover checks
them before reuse. A catalog lock prevents concurrent drivers from
changing the same plan. Different catalog jobs can share caches, but
there is no cross-job claim coalescing yet.

```text
B.ixc/
  manifest
  Library.ixe
  proving.json                  # published only after verification
  proving/<profile-digest>/
    corpus.ixe                  # historical corpus plus current snapshot
    shards.ixes                 # persisted, possibly refined partition
    pending.json                # resumable state; never a certificate
    refined.ixes                # leaf prover's output manifest
```

`proving.json` uses schema `ix-catalog-proving/1`. It binds the exact
manifest hash, member/content roots, profile and axiom policy, base-record
digest, corpus hash/root, final partition hash, reconstructed leaf
subjects/frontiers and their proof addresses, and the aggregate root
proof address. Adding it does not change the catalog's logical roots.

Retain the catalog directories together with `~/.ix/store` and
`~/.ix/cache`. Proof references are addresses into that store; a catalog
directory by itself does not contain the proof objects. The aggregator
currently needs all final leaf wrappers even when an ancestor proof is
cached. Losing an intermediate aggregate cache increases join work;
losing leaf objects can increase checking proof work. Restoring just the
published root is insufficient for the next revision.

Each completed catalog contains the cumulative corpus and complete leaf
inventory needed to serve as the next base. It does not need older catalog
directories to reconstruct that history. Keeping the latest catalog or two
is sufficient for successive updates, provided the shared store retains
every proof object referenced by the retained catalogs. A proof's age alone
does not make it safe to remove: a recent catalog can still depend on a
much older chunk's proof.

The current profile pins the complete `ix` executable hash, Ixon object
format, structural threshold and accepted axiom set. This is conservative:
even a binary rebuild with unchanged checking semantics can require a
fresh profile. Use the same binary and `--structural-above` value for the
baseline, updates and verification. Budgets and scheduling flags are not
profile identities and can change between attempts:

- `--shards N` seeds N shards for new blocks; the default uses roughly
  16 MiB of serialized block bytes per initial shard. This is a heuristic,
  not a memory bound.
- `--lanes N` selects N visible CUDA devices; omission uses all of them.
  CUDA's `CUDA_VISIBLE_DEVICES` still determines device visibility.
- `--max-ram N` overrides automatic budgeting, for example to reserve more
  RAM for other jobs or compare runs at a fixed allowance. Positive values
  are GiB per GPU lane (process-wide on the CPU backend). Omission or zero
  detects a process-wide budget from available host RAM and remaining
  cgroup capacity, including ancestor limits. GPU lanes reserve workspace
  per device and 10% headroom before admitting records. The budget plans
  accounted memory; the operating system's process limit remains the hard
  memory backstop.
- `--exec-jobs N` sets executions per GPU lane; omission distributes the
  available CPU threads across the lanes. Concurrent records share one
  capacity pool and retain their charges through proving. Admission counts
  touched arena pages, including transparent huge pages, and hash-table
  growth. Large records can grow as other work releases capacity; claims
  exceeding the per-record ceiling are split and checkpointed.
- GPU lanes use trace sharding automatically. `AIUR_TRACE_SHARD_MAX_CELLS`
  bounds device trace size; host workspace planning can reduce it further.
  Reducing trace size does not reduce the underlying execution record.
- `--trace-shards` enables trace sharding in the CPU backend; `--jobs N`
  controls its aggregate concurrency.

`ix prove --ixe ... --ixes ...` also selects all visible GPUs for a full
manifest with multiple leaves and returns a verified aggregate root.
`--leaf-only` keeps individual leaf proving and its per-leaf output.

## Scope and validation

This implementation accepts fat, closed catalogs, including a single
member. It materializes a merged corpus and scans that corpus to validate
claims and coverage. Warm runs avoid new proof generation; they still do
host I/O, hashing, claim reconstruction and cryptographic verification.
CPU preparation, corpus growth and aggregate cost need measurement on
real successive commits.

`ix catalog verify` remains an artifact integrity check. Use
`ix catalog verify-proof` for the attached record and certificate. That
command currently needs the retained corpus and partition for the
coverage audit; it is not yet a compact, proof-only release verifier.

The driver does not provide release upload/download, a hosted API,
terminal compression, chunked catalog production, source elaboration,
olean correspondence auditing or automatic corpus checkpoints. The driver
requires every final leaf wrapper, including when a GPU lane reuses an
aggregate subtree, to bind its complete leaf inventory. The
[CSLib GPU handoff](aiur-gpu-proving.md#8-cslib-benchmark-handoff-2026-10-07)
contains measurements with older single-GPU scheduling and fixed memory
settings; those settings are not requirements for current catalog proving.
It also separates toolchain-specific exporters from one fixed proving
binary: replacing the prover during a Lean upgrade
would invalidate this implementation's executable-bound profile.

Focused Rust tests exercise planning, history retention, claim changes,
tampering rejection, axiom policy, locks and interruption recovery using
a simulated proof backend. They do not establish cryptographic proof
validity or warm proving performance. Real baseline/delta proving remains
an integration check against the existing prover and verifier.

The [synthetic CSLib v4.34.1 measurements](benchmarks/cslib-incremental-2026-10-07/summary.json)
cover four sequential local commits: adding a lemma, refactoring a proof,
refactoring a shared definition, and reverting that definition change.
All four full catalogs passed independent proof verification under the
same prover profile and axiom policy. The first three commits added 1, 4,
and 7 anonymous constants to the cumulative corpus, each requiring one
new leaf while preserving all prior claims. The revert added no constants
to the corpus and reused the preceding aggregate root without new proving.
Every warm repeat generated zero new proofs.

On two RTX PRO 6000 Blackwell GPUs with automatic host budgeting, the
catalog proving commands took 85.5, 99.0, 85.0, and 67.2 seconds; separate
planning commands took 54.9–66.4 seconds. The internal proving pipelines
took 19, 23, 22, and 2 seconds, respectively. Full-corpus validation and
artifact processing dominated these small changes. Peak proving-job host
memory ranged from 6.4 to 17.4 GiB. The
[per-proof metrics](benchmarks/cslib-incremental-2026-10-07/proof-metrics.csv)
and four patches accompany the summary; these localized edits do not
measure the cost of changing a widely used foundational definition.
