# Repository working conventions

## Start with the current work

For workspace cleanup, start at
[the cleanup index](plans/tasks/workspace-cleanup/README.md).
Keep the cleanup inventory and queue together in that task directory.
Reconcile previous sessions before starting another implementation lane.
Older handoffs are dated evidence, not competing queues. A request to inventory
or organize work does not resume paused jobs.

Use jj. This workspace shares repository history with other workspaces; always
identify the intended workspace and revision. Use `--ignore-working-copy` for
read-only inventory. An empty recorded working commit does not establish that
the filesystem has no uncommitted or ignored work.
Use John C. Burnham <john@agathic.com> for both author and committer when
recording repository changes.

## Working documents and scratch files

**Default to the untracked `plans/` directory for agent-created documents and
scratch work.** This includes plans, inventories, reviews, handoffs, research
notes, diagnostic scripts, intermediate data, logs and temporary source copies.
Use `plans/tasks/<topic>/` to keep a task's material together. Create only the
files and subdirectories that the task needs.

- Keep `plans/` ignored. Do not force-add it or unignore it wholesale.
- Update the existing task document instead of creating another overlapping
  status report. Link to evidence rather than copying its narrative repeatedly.
- Prefer task-local scratch paths under `plans/` over loose files in the
  repository root, source directories, home directory or `/tmp`.
- Use `/tmp` when a tool or an existing reviewed protocol requires it. Record
  the path and preserve anything needed to resume or audit the task in `plans/`.
- Being ignored does not mean being disposable or backed up. Preserve unique
  source, evidence and dependencies before retiring their original locations.

Requested product documentation belongs in its established tracked location,
such as `docs/`; production code and tests belong in their normal directories.
This root `AGENTS.md` is repository guidance. These are deliberate exceptions
to the scratch-document default.

## Lean is the default scripting language

**Write new automation in Lean.** Prefer Lean for filesystem inventories, data
processing, validation, reporting, orchestration and one-off utilities. Do not
default to Python, Bash, Perl, awk, JavaScript or another scripting language
because the task is small or temporary. Keep such Lean tools under `plans/`
unless they are deliberately becoming maintained project tooling.

Direct invocations of existing tools such as `rg`, `jj`, `sha256sum`, `ssh`
and `rsync`, and the minimal command wrappers required to invoke them, are
fine. Put substantial control flow and data transformation in Lean.

Use another language only for a concrete constraint, such as a required tool
interface or a narrow change to an existing implementation. Briefly record the
reason in the task notes; familiarity alone is not a reason. Reuse existing
Lean libraries and keep small utilities small.

## Prefer Lean data and Ixon to JSON

Use typed Lean structures, inductives and `.lean` data files for internal
inventories, manifests, configuration and other structured working data.
Use Ixon when an existing encoding fits the data and binary interchange or
content addressing is useful. Keep human explanations in Markdown.

JSON remains appropriate for an established external schema, tool protocol or
existing consumer that requires it. Do not introduce it by habit. Do not build
a new serialization framework merely to avoid a small required JSON boundary.

Keep receipts, manifests and scripts byte-identical while they are being used
to validate retained work. Relevance review may retire obsolete packets and
their outputs; do not archive all historical data by default. Keep useful
source in commits and retain only evidence that serves a concrete purpose.

## Preserve execution and proof boundaries

For the 2026-10-10 cleanup session, the owner authorizes local inventory
scripts, builds and tests, consolidation into one commit history, and retirement
of redundant workspaces after preserving their work. This supersedes the older
cloud-only build/test restriction for this session. The cloud box is unavailable;
do not depend on it or start remote jobs.

Scope is ix-certify-compile and its identified compiler workspaces. Compilatr.ix
and other separate projects are excluded, including their dependencies and
build caches. Consolidate relevant source into one branch with meaningful
commits; discard obsolete work and data instead of retaining blanket archives.

Preserve the old cloud capture and unresolved reservation as historical facts.
They do not block local consolidation. If remote work later resumes, its
full-workspace wrapper excludes `plans/` and uses deletion semantics: review
explicit staging for any required tool, and never pass it a small scratch
directory or replace a pinned wrapper during organization work.

Keep source readiness, executed checks, accepted evidence, integration and
publication as separate facts. Do not weaken theorem domains, tests or gates
to simplify cleanup. Preserve donor history and unique source; do not modify
`IxC/**` under the current compiler-work scope.
