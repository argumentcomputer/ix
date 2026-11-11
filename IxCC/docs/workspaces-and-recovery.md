# Workspaces and recovery

IxCC is developed in ix, under `IxCC/`; its standalone history is preserved
there by the subtree merge. Keep new work in a named, bounded task and close
its temporary workspace after its source, useful evidence and validation are
recorded. Local `plans/` directories remain ignored; they
are not the sole durable home of useful source or indispensable evidence.

The October 2026 consolidation preserves source without adopting unfinished
checker or proof work. The production Lean/codec pins, theorem qualifications
and required checks remain those in [compiler design](compiler-design.md),
[the trust ledger](trusted-extern-ledger.md) and [CI coverage](ci.md).
Phase 1.5 and the first heap-slice objective remain incomplete.

## Recovery references

| Reference | Checkpoint | Contents |
| --- | --- | --- |
| ix, resource WIP checkpoint | branch `jcb/compilatrix-resource-wip-2026-10-11` (outside this repository's history) | Older resource checker and fixtures, preserved as WIP. |
| ix, donor-history checkpoint | branch `jcb/compilatrix-donor-history-2026-10-11` (outside this repository's history) | Optimization histories and the source-only untested A6d kernel draft. Its tree equals the resource checkpoint's; additional parents preserve history without integrating it. |

These are immutable recovery checkpoints, both ix commits. Later source changes
need their own commits and validation. Preserve the existing Ixby archive and useful toolchain
and phase references. Do not infer implementation equivalence from matching
commit subjects or from a history-preservation merge.

The active `ix-certify-compile` workspace has its own owner and task. Its source,
working revision and publication are independent of this cleanup. The shared
ix Git/jj store also serves other projects and must remain available to them.

## Retiring a workspace

Before retiring another workspace, check its actual filesystem, nested
repositories, ignored source, symlinks and consumers. A clean jj recorded
working change is insufficient: inspect files without silently snapshotting
another session's work. Retain useful source on a verified pushed reference,
then remove the clean worktree with its VCS command. Remove obsolete local
names only after verifying their exact tips remain in a published recovery
reference. Never remove the shared repository store with a workspace.

## Validation and continuation

The cleanup adds no compiler semantic change. The integration candidate must
pass the complete required local surface before publication: every `ixcc-*`
check of ix's flake ([development and validation](development-plan.md#validation-commands)
has the command; `nix flake check` at ix's root runs them with ix's own).
On x86-64 Linux these are all 16 required checks: the shared builds,
complete proof/fence and trust/build-graph inventories, pipeline suites,
native behavior, RC runtime/certificate controls and deterministic steps.
Record the exact tested commit/tree, toolchain, cache state and command result.
Source-only or documentation checks cannot stand in for that integration run;
local store reuse does not establish hosted or cold-store timing.

The local cleanup queue and detailed measurements remain under
`plans/cleanup-and-consolidation-2026-10-11/`. After cleanup, retain one concise
continuation record naming published revisions, recovery results, remaining
acceptance gates and the next Phase 1.5 work. Resume implementation only when
requested; preservation and workspace retirement do not resume it.
