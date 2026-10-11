# Workspaces and recovery

Use `jcb/x86` for the compiler integration tree. Keep new work in a named,
bounded task and close its temporary workspace after its source, useful evidence
and validation are recorded. Local `plans/` directories remain ignored; they
are not the sole durable home of useful source or indispensable evidence.

The October 2026 consolidation preserves source without adopting unfinished
checker or proof work. The production Lean/codec pins, theorem qualifications
and required checks remain those in [compiler design](compiler-design.md),
[the trust ledger](trusted-extern-ledger.md) and [CI coverage](ci.md).
Phase 1.5 and the first heap-slice objective remain incomplete.

## Recovery references

| Repository and reference | Checkpoint | Contents |
| --- | --- | --- |
| Compilatr.ix `jcb/phase15-research-2026-10-11` | `c59be1b227bdf7eb9d589c493074aa662ad8e31a` | Selected checker inputs, proof foundations/reviews, unfinished successors and the optional recovery tool. |
| Compilatr.ix `jcb/pre-cleanup-history-2026-10-11` | `dbc09f330e19015df0eee49af586a7acc65e0b74` | Original donor histories, branch-name map, source/evidence dispositions and retained ignored files. Its tree is an archive, not a combined compiler. |
| ix `jcb/compilatrix-resource-wip-2026-10-11` | `83f1c0c48790010499b2311a33bc25ccaaec802c` | Older resource checker and fixtures, preserved as WIP. |
| ix `jcb/compilatrix-donor-history-2026-10-11` | `a55a06d2dd69a14e2463d57e170a4e843c24ff23` | Optimization histories and the source-only untested A6d kernel draft. The tree equals `83f1c0c4`; additional parents preserve history without integrating it. |

These are immutable recovery checkpoints. Later source changes need their own
commits and validation. Preserve the existing Ixby archive and useful toolchain
and phase references. Do not infer implementation equivalence from matching
commit subjects or from a history-preservation merge.

The active `ix-certify-compile` workspace has its own owner and task. Its source,
working revision and publication are independent of this cleanup. The shared
ix Git/jj store also serves other projects and must remain available to them.

## Restore selected research

Check out the research reference separately from the integration tree. From
that checkout, use the pinned Lean 4.34.1 environment:

```sh
nix develop -c lake -d research build research-recovery
nix develop -c lake -d research exe research-recovery verify
nix develop -c lake -d research exe research-recovery restore /path/to/recovery-checkout
```

The optional package's `research/README.md` and `packages.tsv` identify package
status and prerequisites. Its manifest authenticates 6,047 selected files and
the restore command refuses differing existing destinations. A fresh GitHub
clone of `c59be1b2` built the tool, verified all digests and restored all listed
files. This establishes source/evidence recovery; it is distinct from proof
elaboration, checker acceptance and native execution.

Keep original source and receipts byte-identical. Original builders contain
historical absolute paths and artifact guards; relocation needs a separate
recipe and a fresh result. G1's selected checker overlays and G2's production
codec environment are different dependencies and must not be interchanged.
Uncompiled linked-construction drafts and design-only dependent transports
retain those statuses. Q06 still fails at the selected 500,000-step/depth-256
limits; preserving a diagnostic or a proof prerequisite does not close that gate.

## Restore historical work

Fetch the history reference and consult its `README.md`, `branches.tsv`,
`checkpoints.tsv` and disposition tables. Every original local Compilatr.ix
branch tip is reachable from `dbc09f33`, including the separately committed
repin donor snapshot `7100f2f`. Selected ignored source/evidence is either
stored under `files/BLOB` or already present as a Git blob in the named donor
repository. The tables give the original path and blob identity needed to
recover it without overwriting a live workspace.

Both history checkpoints were fetched into an independent recovery clone.
All 2,594 retained source/evidence occurrences passed source-hash, copied-byte
and Git-blob availability checks there. Generated compiler output and
superseded intermediate files have explicit omission dispositions. Source and
assertions in the original donor commits remain recoverable.

Before retiring another workspace, check its actual filesystem, nested
repositories, ignored source, symlinks and consumers. A clean jj recorded
working change is insufficient: inspect files without silently snapshotting
another session's work. Retain useful source on a verified pushed reference,
then remove the clean worktree with its VCS command. Remove obsolete local
names only after verifying their exact tips remain in a published recovery
reference. Never remove the shared repository store with a workspace.

## Validation and continuation

The cleanup adds no compiler semantic change. The integration candidate must
pass the complete required local surface before publication:

```sh
nix flake check -L --max-jobs 1 --cores 12
```

On x86-64 Linux this includes all 16 required checks: the shared builds,
complete proof/fence and trust/build-graph inventories, pipeline suites,
native behavior, RC runtime/certificate controls and deterministic steps.
Record the exact tested commit/tree, toolchain, cache state and command result.
Source-only or documentation checks cannot stand in for that integration run;
local store reuse does not establish hosted or cold-store timing.

The local cleanup queue and detailed measurements remain under
`plans/cleanup-and-consolidation-2026-10-11/`. After cleanup, retain one concise
continuation record naming published revisions, recovery results, remaining
acceptance gates and the next G1/G2 work. Resume implementation only when
requested; preservation and workspace retirement do not resume it.
