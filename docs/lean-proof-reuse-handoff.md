# Lean compatibility and incremental proof reuse handoff

Updated: 2026-10-08.

## Checkpoint and working trees

Work stopped at the user's request to leave a handoff instead of continuing
tests or implementation. Do not automatically start another build, test run,
or benchmark from these instructions; resume when requested.

- Main checkout: `/home/sam/repos/ix`, branch `sb/l40s-proof-handoff`.
  This checkpoint began from `6269fd4e7e5b427c1a0ec5737d18b730b9ccd17b`.
- After the checkpoint, the user requested local commits. GPU scheduling,
  memory budgeting, and catalog reuse are committed in `48095fb6`; native
  primitive validation is committed in `1a732d4a`. The documentation commit
  containing this handoff follows those implementation commits.
- Lean upgrade worktree: `.lake/worktrees/lean-4.35`, branch
  `sb/lean-4.35-bumps`. Separate local commits are
  `162455bf46210df2c82dfdf3851c6ad748a0cd97` for v4.35.0-rc1 and
  `31528a0f88b2b1e51c0863ce222ef4a75e9c9a0d` for v4.35.0-rc2.
- Review worktree: `.lake/worktrees/l40s-primitive-review`, detached at
  `6269fd4e`. Its ignored `.lake/review/` directory
  contains earlier review fixtures and a snapshot of the performance diff.
- Immediately before the latest catalog edits, copies of `run.rs`,
  `tests.rs`, and `docs/incremental-catalog-proving.md` were saved under
  `/tmp/ix-catalog-retained-proof-before/`, preserving their relative paths.
  These copies are temporary review aids, not durable artifacts.
- No pushes were made. Never push; that remains the user's action.

## User priorities and design direction

Proving performance and predictable reuse boundaries take priority over
maximal reuse. The user accepts retaining the past version or two's
artifacts. Earlier handoff settings must yield to current performance
behavior: use all visible GPUs, leave CPU parallelism at its defaults, and
use automatic host-memory budgeting unless an explicit override is needed.
The old fixed `--max-ram 100` setting is not a CSLib requirement.

The agreed incremental approach is to retain existing proved chunks, prove
newly required content in reasonably sized chunks, and aggregate the old
and new evidence. No per-theorem proof granularity or extraction of smaller
proofs from an already-produced shard proof is required.

Within one compatible proving configuration:

```text
Old chunk:          {A, B, C}, with its existing proof
Edit:               B becomes B'
New chunk(s):       B' and dependents whose content addresses changed
New certificate:    retained proofs + new proofs + aggregation
Current snapshot:   the desired declarations covered by that corpus
```

The old `B` and its proof remain valid historical content. A dependent of
`B` that now references `B'` normally receives a new address and needs new
evidence too. There is no assumption that the changed declaration is the
only new address.

Current chunk ownership is at declaration-block boundaries. Mutual blocks
remain atomic. A new projection of an existing mutual block changes that
block's owner's claim and still requires new evidence for that leaf.
GPU trace sharding does not create independently reusable declaration
proofs. A generic verified subset-proof adapter is not implemented.

### Retention

Each completed catalog stores a cumulative corpus, final partition, and
complete leaf inventory. The next update can use that catalog directly;
it does not need to replay every ancestor catalog directory. Keeping the
latest catalog or two therefore fits the workflow.

The shared proof store has a different lifetime: retain every proof object
referenced by those catalogs, including proofs older than two revisions.
Keep the aggregate caches to avoid rebuilding old joins. A recent catalog
can retain much older declarations and proofs. No pruning or garbage
collection was implemented. See [artifact retention](incremental-catalog-proving.md).

### Compatibility policy

The production direction discussed is a complete, immutable compatibility
profile admitted before proving. It should fix primitive bindings, literal
interpretation, permitted reductions, and the checking/verifying identities
and proof parameters. Required validation failures should reject the
profile; optional behavior should be chosen as a fixed policy before the
run. Avoid proof compatibility depending on which acceleration happened
to validate during an execution.

This stricter primitive-profile policy is **not implemented**. Its
conservative first version can make a primitive-profile change require
re-proving all claims under the new profile. Smaller chunks do not by
themselves permit reuse across that boundary. Finer per-chunk semantic
contracts can be investigated later if measurements justify them.

The current catalog compatibility check remains stricter in another way:
it pins the entire executable hash, Ixon object format, structural
aggregation threshold, and axiom policy. Do not weaken that check before
its replacement authenticates every relevant semantic input. A Lean
version label alone neither establishes nor rules out compatibility.

The older finer-grained proposal in [primitive-bindings.md](primitive-bindings.md)
is research context. Its per-binding reuse and opportunistic fallback
policy should not be treated as the settled production design.

## Implementation present at this checkpoint

### Existing catalog path

[Planning](../crates/kernel/src/catalog_prove/plan.rs) merges the retained
corpus with the new snapshot, preserves old block ownership and the old
aggregation subtree, and partitions only new blocks. Proof lookup uses
exact claims, including both owned subjects and dependency assumptions.
The backend verifies cached evidence before using it. Catalog verification
audits that the current snapshot is covered by the certified retained
corpus; it still needs that corpus and partition.

### Catalog changes in `48095fb6`

Changes are in [run.rs](../crates/kernel/src/catalog_prove/run.rs),
[tests.rs](../crates/kernel/src/catalog_prove/tests.rs), and
[incremental-catalog-proving.md](incremental-catalog-proving.md).

- `reusable_base_root` enables direct reuse when the already-verified base
  has exactly the same corpus root and partition hash and its leaf wrappers
  are available and match the final claims. It binds a new snapshot record
  to that root without invoking either prover or aggregator.
- Missing or corrupt leaf artifacts fall back to the ordinary proving/cache
  recovery path. Existing profile, axiom, coverage, and publication checks
  remain in force. The root is verified against the resulting artifacts
  before the new record is published.
- `prove_and_aggregate` contains the existing ordinary path, including GPU
  lanes and exact-claim cache seeding. Its extraction supports sharing the
  final verification/publication steps with direct root reuse.
- `claim_summary` adds per-claim `retainedFromBase`, plus `newClaims` and
  `subjectsInNewClaims`. It recalculates the summary from final claims after
  any partition refinement. These are statement counts, not measured cache
  hits or proof-generation counts: an old claim can need recovery, and a
  new-to-base claim can already be cached elsewhere.
- Direct root reuse reports `reusedBaseRoot: true` and `newProofs: 0`.
  The ordinary path reports `reusedBaseRoot: false` without inventing a
  generated-proof count.

This optimization still performs corpus merging/scanning, hashing, wrapper
reads, and verification. It is not a compact proof-only verifier, and its
wall-clock improvement has not been benchmarked.

The catalog tests now simulate exact-claim cache reuse and track which
claims the simulated backend proves. They cover an edit and its changed
dependent inside one old chunk, ordinary and GPU-lane orchestration,
deletion/revert root reuse after deleting older catalog directories,
missing/corrupt leaf recovery, mutual-block projection invalidation, and
incompatible-profile rejection. The simulation does not run a STARK prover
or establish GPU performance.

### Earlier native primitive validation work

The Rust checker in `1a732d4a` can admit primitive bindings through semantic
contracts: Nat literal shapes, typed String expansion, and symbolic
recurrence checks for `Nat.pred`, `add`, `sub`, `mul`, `pow`, `beq`, and
`ble`. Validation isolates the operation from the shortcut it is trying to
justify. Tests cover swapped/forged operations, circular admission, invalid
literal interfaces, cache invalidation, and alternate String layouts.

Primitive profile schema 1 uses explicit present/absent roles and strict
canonical parsing. This work is native Rust only. The IxVM checker,
literal wire dependencies, witnesses, shard walks, proof claims, and catalog
compatibility mechanism have **not** been migrated. Loading such a profile
does not authorize GPU proof reuse across Lean versions. Dynamic native
admission/fallback still exists and needs reconciliation with the stricter
profile policy above.

## Validation and prior proof results

The last command was started just before the user's stop request:

```sh
RUSTUP_TOOLCHAIN=stable cargo test --locked --offline --release \
  -p ix-kernel --lib catalog_prove::tests:: -- --quiet
```

When cancellation was attempted, the process had already completed:
**21 passed, 0 failed**, with a 17.82-second warm release build and
0.01-second test execution. The exec session is complete. No subsequent
tests or builds were started. `rustfmt` completed on the two edited Rust
files before that run. This is the validation result for the latest catalog
changes; it is not a real proof-generation result.

Prior checkpoint results, not rerun during the handoff:

- 205 focused tests passed across `ix-common`, `ixon`, and `ix-kernel` for
  primitive profiles and native checking.
- Exported Init/Std environments for v4.35.0-rc1 and v4.35.0-rc2 passed the
  native literal and seven structural Nat-operation admission checks. Both
  produced profile
  `7bac5b5c18248ee46124550858a7dc13ac7e394fd81e4aef2f7f0b0eff63916c`.
  This was not a complete Init/Std typecheck or GPU proof.
- The separate Lean upgrade worktree recorded 83 IxVM cases and 249 parity
  checks passing for each bump; see its
  `docs/benchmarks/lean-4.35-upgrades/{rc1,rc2}.json`.
- The [CSLib v4.34.1 incremental report](benchmarks/cslib-incremental-2026-10-07/summary.json)
  records four certified synthetic commits: lemma addition, proof refactor,
  shared-definition refactor, and revert. The first three added 1, 4, and
  7 constants and one new leaf each while retaining all prior claims. The
  revert added no constants and reused the previous root. All warm repeats
  generated zero new proofs. These measurements precede the direct reuse
  optimization above; retain their original interpretation.
- [Per-proof metrics](benchmarks/cslib-incremental-2026-10-07/proof-metrics.csv)
  and [summary CSV](benchmarks/cslib-incremental-2026-10-07/summary.csv)
  accompany that report. The runs used two GPUs; current host preparation
  and corpus validation dominated the small deltas.

## Next steps after the user resumes work

1. Review the latest catalog diff against the saved pre-edit copies. Check
   the direct-reuse eligibility and shared publication path, especially
   exact partition matching, snapshot coverage, and artifact recovery.
   Additional focused cases worth considering are partition refinement
   during resume, final summary accuracy after splits, and a same-corpus
   update whose partition differs. Existing tests passing does not cover
   all of these cases.
2. Validate the optimization against a small real baseline/update/revert
   using one fixed proving binary and retained proof store. Record actual
   new/reused leaves, aggregate operations, root equality, planning and
   verification time, peak host memory, and both GPUs' activity. Use the
   existing CSLib exports where suitable; a fresh full CSLib proof is not
   necessary to review this change. Obtain agreement before a long build
   or proving/benchmark run. Changing the binary invalidates the existing
   executable-bound catalog profile.
3. Write the complete compatibility-profile contract before extending
   cross-version reuse: canonical identity, required admission checks,
   fixed acceleration policy, literal interpretation, permitted axioms,
   checker/verifier identities, and explicit rejection behavior. Retain
   useful parser fixes and adversarial native tests.
4. Implement the proof-side migration together across native checking,
   IxVM, object interpretation, dependency walking, witness construction,
   claims, and aggregation. Literal support is currently an implicit
   dependency in relevant paths. An ambient role table or type-shape
   check alone is insufficient evidence for changing primitive reductions.
   Preserve the conservative compatibility boundary until this is sound.
5. Establish the v4.34.1 baseline for that finalized checker/profile, then
   compare the rc1 and rc2 exports under the specified boundary. Keep Lean
   bumps separate and avoid changing CSLib source to accommodate a checker
   mismatch. The existing synthetic v4.34.1 source changes were an explicit
   incremental-proving experiment, not a toolchain compatibility workaround.

Use [the GPU guide](aiur-gpu-proving.md) and
[incremental catalog guide](incremental-catalog-proving.md) for commands.
Prefer their current automatic scheduling behavior over historical fixed
budgets. Do not cap CPU jobs or restrict the process to one GPU to make a
run appear cheaper. Do not run blanket dependency updates or push changes.
