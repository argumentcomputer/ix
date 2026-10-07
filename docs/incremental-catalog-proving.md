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
and verified through `ix prove --skip-proven`; `ix aggregate` reuses its
existing aggregate cache. Budget-driven splits are saved as B's final
partition. A new projection of an old mutual block can change its owner's
claim, which requires new evidence for that leaf.

Old versions remain in the anonymous corpus. The record separately binds
the current snapshot and verifies that all its addresses are covered.
Consequently, deleting a declaration or reverting to already certified
content can require no new leaf proof. Changing a widely referenced
declaration can still change many dependent addresses and require
substantial proving.

Repeating `ix catalog prove B.ixc` after success validates its artifacts and
root certificate and returns without invoking either prover or aggregator.
For C, use `--base B.ixc`. Keep each catalog manifest and its pieces immutable.

## Planning, interruption and persistent state

`--plan-only` creates or resumes a pending plan, and verifies the supplied
base certificate, without executing new checking claims or generating
proofs. Its JSON includes new subject counts, unchanged and changed base
claims, and each planned shard's claim and frontier size. Retained claim
counts describe compatible statements, not guaranteed cache availability;
missing leaf objects can still require re-proving.

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

The current profile pins the complete `ix` executable hash, Ixon object
format, structural threshold and accepted axiom set. This is conservative:
even a binary rebuild with unchanged checking semantics can require a
fresh profile. Use the same binary and `--structural-above` value for the
baseline, updates and verification. Budgets and scheduling flags are not
profile identities and can change between attempts:

- `--shards N` seeds N shards for new blocks; the default uses roughly
  16 MiB of serialized block bytes per initial shard. This is a heuristic,
  not a memory bound.
- `--max-ram N` passes a GiB budget to proving and aggregation.
- `--trace-shards`, `--exec-jobs N` and `--jobs N` use the existing
  backend's trace-sharding and concurrency controls.

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
olean correspondence auditing or automatic corpus checkpoints. It does not
yet invoke `ix prove --lanes` or adopt a completed lane run as a baseline.
That path can reuse aggregate subtrees without collecting every final leaf
wrapper, while this driver needs the complete leaf inventory. The
[CSLib GPU handoff](aiur-gpu-proving.md#8-cslib-benchmark-handoff-2026-10-07)
therefore creates its baseline through this driver and tests real subsequent
commits with one GPU. That handoff separates toolchain-specific exporters
from one fixed proving binary: replacing the prover during a Lean upgrade
would invalidate this implementation's executable-bound profile.

Focused Rust tests exercise planning, history retention, claim changes,
tampering rejection, axiom policy, locks and interruption recovery using
a simulated proof backend. They do not establish cryptographic proof
validity or warm proving performance. Real baseline/delta proving remains
an integration check against the existing prover and verifier.
