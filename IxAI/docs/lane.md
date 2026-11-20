# Lane and the agentic part of the plan

Lane (`github.com/argumentcomputer/lane`, read-only clone at `~/repos/clones/lean-ai/lane`,
`main` at `cf1af8c`, 2026-11-19) is Argument's Lean 4 workbench for parallel theorem proving by
coding agents. This doc records what it is, how it fits `plan.md`, `ixvc.md` and `rl.md`, and the
changes to Lane that the fit needs. Lane is in-house, so changing it is an option.

## What Lane is

One Lean 4.34.1 executable (`lane`, ~5k lines of Lean in `Lane/` and `Main.lean`) plus a
~200-line Rust crate (`crates/lane-ffi`, over Argument's `lean-ffi`) for Unix-socket framing and
`symlink`. MIT/Apache-2.0. No Lake dependencies beyond core Lean.

Two runtime roles of the same binary:
- **Server** (`lane server start`, `Lane/Server/Runtime.lean`): one per repository, bound to the
  exact root (`.lane/repository-root`), single-threaded accept loop on `.lane/server.sock`
  (length-framed, 64 MiB cap). It owns metadata and lane files and never elaborates Lean.
- **Clients** (every other command, `Lane/Prove/*`): parse, elaborate and check in-process with
  `Lean.Elab.runFrontend` against the project's compiled `.olean`s (search path from `LEAN_PATH`,
  else `lake env printenv LEAN_PATH` cached in `.lane/lean-path`; `Core.lean:386`). Compilation
  load is spread over client processes, so the server is not a build bottleneck.

### Data model (all plain files under `.lane/`, `Lane/Server/Storage.lean`)

| Object | Representation |
|---|---|
| Lane | `lanes/<n>/` with sequential integer IDs (never reused within a `.lane`'s life). State is the presence of `finished`/`discarded`/`submitted` marker files. |
| Logical file | Overlay read order: `lanes/<n>/files/<path>` → base snapshot → canonical repo (`readLogicalFile?`). Deletions and creations are marker trees (`deleted/`, `base-absent/`). |
| Base | `lanes/<n>/bases/<path>`: canonical bytes at first divergence; `submit` refuses if canonical changed since. |
| Snapshot | `snapshots/<n>/files/`: a full copy (Git-visible files only, `copyProjectSnapshot`), plus `lane` and `parent`. Created by `checkpoint`, `fork`, `finish`. |
| Fork | `fork` checkpoints the parent and starts a child whose `base-snapshot` is that snapshot (immutable merge ancestry). |
| Collaboration | Per-lane `claims/` (targets `decl:`, `file:`, `module:`, `goal:`, `task:`; exclusive across lanes), `notes/`, `activity/` (append-only kind/detail records), `obligations/` (proofs displaced by `theorem-to-sorry`). |
| Journals | `submissions/<lane>`, `merges/…`: backups replayed on server restart (`recoverSubmissions`, `recoverMerges`). |
| Credentials | `admin-token` (main agent), `sessions/<token>` → lane (delegated workers). |

The protocol is space-separated verbs with hex-encoded arguments (`READ`, `WRITE <expected>
<new>`, `FORK`, `FINISH`, `CLAIM`, `MERGEBATCH`, `SUBMIT`, …). Writes are compare-and-swap on the
**full previous file text** (`readFileVersioned` returns the contents as the version). Responses
are JSON with `api_version: 1`.

### Roles and capabilities

The main agent holds the admin token: `new`, `fork`, `delegate`, `revoke`, `merge`, `submit`,
`clean`. `delegate` mints a 256-bit random token bound to one lane and writes a session file
(lane, token, scratch dir, environment bindings). Workers run `lane --session-file F <cmd>`;
`Main.lean:workerLaneCommand` and `Runtime.lean:workerRequestAllowed` restrict them to that lane
and to observe/edit/claim/note/finish verbs. `finish` freezes the lane, checkpoints it and revokes
its sessions.

### Proving and checking

- `prove` (`Core.lean:419`): locate the declaration with Lean's parser, elaborate
  `prefix ++ ":= " ++ proof` (declaration-local), then the whole module with the proof spliced in,
  then CAS-write. On a stale write it rebases up to 8 times if only other declarations changed;
  a change to the target declaration is a conflict.
- `prove-session` (`Analysis.lean:441`): elaborates the unchanged prefix once with Lean's
  incremental `Language.Lean.process` snapshots and checks NDJSON candidates
  (`{"proof": …, "persist": bool}`) against it; re-prepares if the lane file moved.
- Inspection: `goals` (pretty-printed goals parsed back from diagnostics text), `context`,
  `probe --term|--tactic`, `info --at`, `premises` (`getUsedConstants` of the elaborated value),
  `dependencies`, `find --name|--type`, `sorries`, `diagnostics`, `trace`.
- Declaration-level edits: `insert/replace/delete/move-decl`, `rename` (resolved identifier
  ranges), `simplify`, `theorem-to-sorry`, `sorrify`, `extract-sorry/goal/have`.
- `verify` (`Analysis.lean:90`): policy check of one declaration: `--no-sorry`, `--no-new-axioms`
  (`collectAxioms` vs the canonical file), `--no-unsafe`, `--expected-type T`, and `--affected`.
- `--affected` (`Extraction.lean:484`, `validateAffectedProject`): computes the reverse import
  closure of the lane's changed modules and re-elaborates it in dependency order into a temporary
  olean root layered over the project's build (`overlayOutputDirs` symlink overlay).
- `merge` (`Source.lean:646`, `declarationAwareMerge`): three-way per theorem against the fork's
  base snapshot; text outside declaration commands must be equal (after layout compaction); any
  conflict aborts. `submit` = `validateAffectedProject` in the main agent's process, then a
  journaled write of the lane's files into the real repository.

### What Lane does not do

- **No scheduling.** It never spawns agents, has no job queue, priorities or leases. The main
  agent (e.g. a Claude Code session) spawns workers and hands each a session file; claims are the
  only coordination primitive.
- **No OS isolation.** Elaboration runs with `Lean.enableInitializersExecution` and whatever IO a
  proof or file runs (`run_tac`, `#eval`, `initialize`). A worker shares the user's uid, so it can
  read `.lane/admin-token` and write canonical files; the README says so and delegates
  containment to the caller's sandbox.
- **No content addressing, Ix, Ixon or BLAKE3.** Versions are full texts, IDs are counters,
  snapshots are copies, merge equality is textual.
- **No trusted validation boundary.** `WRITE` (including `--unchecked`) is a worker verb and the
  server stores what it is sent; "validated" in a worker's response is self-reported. Only checks
  the main agent re-runs (`verify`, `submit`'s affected rebuild) count.
- **No fuel.** Elaboration uses Lean's default options (`{}`), so the default heartbeat limit
  applies, but nothing bounds `#eval` loops or wall time, and the fuel used is not reported.

### Maturity

8 commits, all code by one author (Arthur Paulino), one merged PR (#1, 2026-11-19: Lean 4.34.1, multi-package
Lake search path, olean overlay for `--affected`, Git-only snapshots, `--unchecked`), no issues.
CI: `lean-action` then `tests/all.sh` (shell suites over temp repos: integration, merge, recovery,
collaboration, prove-session, semantic actions). PR #1 was driven by a swarm on a ~5,500-module
workspace with in-repo path dependencies, the shape of Ix (Aiur, IxVM, IxC as path packages). Its
listed gaps: `verify` cannot target a declaration whose file imports a changed module;
declaration-level commands and merges see only theorems (structures, imports, `def` edits conflict
"outside declaration commands"); `--unchecked` writes report `containing_module`; `verify` lists
the standard axioms as new unless `--no-new-axioms` is given.

Toolchain coupling: Lane loads project oleans in-process, so its Lean must equal the project's.
Lane, Ix (`ix.ci-merge-tests`, `ix.ixai-aiur`) and `ix/bundle` are on 4.34.1; this project's root
is 4.34.0, so Lane cannot serve it without a 4.34.0 build of Lane or a toolchain bump here.

## Fit with the plan

| Plan piece | What Lane already provides | Gap |
|---|---|---|
| `ixvc` orchestration (shared store instead of worktrees; hand over a change address) | Logical lanes over one checkout and one `.lake` build: no worktrees, no duplicated build artifacts, which is `ixvc.md`'s first motivation. Fork/finish/merge/submit is a branch–handoff–merge–ref-move cycle; CAS writes; per-declaration three-way merge; claims, notes and activity as coordination data; capability-scoped workers. | Text, not Ixon; versions are bytes and counters, not addresses; conflicts abort instead of being stored; history is a chain of copied snapshots, not a Merkle DAG; no claims or certificates attached to a handoff; one server per repository, not one store per machine. |
| Local-mode cluster (train → witnesses → prove → aggregate → PLONK → record) | Nothing for GPU or proving jobs. A reusable pattern: single owner process, Unix socket, capability tokens, journals with restart recovery. | No job model. Lane should not become the job runner; the two should share job/result formats and the store. |
| Proof-search agent over deterministic Ix tactics, speaking Ixon | Nothing in the core: Lane is a JSON shim over Lean's impure elaborator, the thing the decision puts outside the core. Useful as the LLM-facing harness for baselines on the same goals, and as a source of goal/tactic/outcome traces until Ix's elaborator exists. `prove-session` already has the request/response shape of an agent step. | Goals are pretty-printed text, not terms or addresses; no tactic-level stepping (whole proofs only, `probe` for one tactic); no fuel accounting; no outcome cache. |
| IxBench baselines via sub-agents | A ready tool harness for tool-using Opus sub-agents on proving tasks: per-agent lanes and session files, `goals`/`probe`/`prove`, `verify --no-sorry --no-new-axioms` as the acceptance check, `premises` for used-premise extraction. | Answer-key leakage: canonical sources and `.lane` are readable by workers; results are not recorded as addressed, checkable items. |
| Heavy-job gate (`ix/heavy.sh`) | — | `heavy.sh`'s busy check matches `lake build`, `lean `, `cargo build`, `rustc`, `nvcc`, `ix prove|compress|aggregate`; in-process elaboration under a `lane` process is invisible to it (only the load-average check sees a swarm). `verify --affected` and `submit` can rebuild a large reverse closure. |
| Environment tiers | — | Lane's elaboration is tier 3 (uncertified, must be conventionally sandboxed). It moves toward tier 1 only by swapping its frontend for Ix's pure elaborator. |

## Proposed changes to Lane

In order of value per effort. File pointers are in the clone.

1. **Addresses for bytes.** BLAKE3 every file version and snapshot.
   - `Storage.lean`: a blob store `.lane/blobs/<blake3>`; lane files, bases and snapshots become
     manifests `path → address`, and a snapshot's address is the BLAKE3 of its canonical manifest
     (Merkle root). `copyProjectSnapshot`/`copyTree` stop copying (119 MB per fork on the large
     project) and dedupe across lanes.
   - `Runtime.lean` `READ`/`WRITE`/`DELETE`/`MERGEBATCH`: CAS on the expected address, not the
     full text (`Client.lean:VersionedSource.expectedSource`). Halves request size and makes
     versions printable.
   - Hash with the same BLAKE3 Ix uses (`Ix/Address.lean`: `Address.blake3`, or the `Blake3`
     package Ix requires), so a Lane blob address equals an `ixvc` Blob address.
2. **A change record at handoff.** `finish` (`Lanes.lean:checkpointLane`, `Runtime.lean` `FINISH`)
   writes an immutable, addressed record: parent snapshot address, result snapshot address,
   per-declaration edits (name → old/new command-text address, classified proof-only /
   body-only / statement / added / deleted from the parser views in `declarationViews`), the
   worker's notes as context, and the `verify` records below. The main agent merges by change
   address; `merge` takes either a lane ID or a change address. This is the `ixvc` Change object
   with text-level edits, and a later drop-in for Ixon edits.
3. **Verification records the main agent can trust.** `verify` (`Analysis.lean:90`) emits a
   canonical record `(snapshot address, declaration, policy, toolchain, result, axioms)` and
   stores it by address; JSON keys sorted and timing fields moved out of the hashed part (as
   IxBench keeps wall clock outside its digest). `submit` gains `--require` to demand records for
   every changed declaration, recomputed in the main agent's process, never taken from the worker.
   Separately: remove `WRITE`/`--unchecked` from worker verbs or mark such files `unchecked` in
   the change record so they cannot be mistaken for validated.
4. **An admission hook to Ix.** A per-repository config (`.lane/config.json`, read by
   `submitValidated`, `Analysis.lean:67`) naming commands run after the affected rebuild:
   `ix compile --consts-file` over changed modules, then `ix check` of the changed constants,
   with the resulting Ixon addresses and check-claim addresses written into the change record.
   Later, link Ix as a Lake dependency (same Lean 4.34.1, same `lean-ffi`) and compile the
   elaborated `Environment` in-process with `Ix/CompileM.lean`, so `verify` returns Ixon
   addresses directly.
5. **Address-based merge equality.** In `declarationAwareMerge` (`Source.lean:646`), fall back to
   Ixon addresses when command texts differ: formatting-only or alpha-equivalent edits stop
   conflicting, and a proof-only edit on one side commutes with anything that keeps the
   statement. Extend declaration views beyond theorems (`Core.lean:declarationViews`) to `def`,
   `structure`, `inductive`, instances and the import block.
6. **Conflicts as data.** `merge` records a conflict object (name, base, both sides) in the
   target lane instead of throwing; `submit` refuses while any is open. Matches `ixvc.md`'s merge.
7. **Heavy-job integration.** A `heavy` prefix in the repo config used for `verify --affected`,
   `submit` and `check`, run as a child `lane` process (`lane _validate …`) so the gate wraps it;
   and a server-side elaboration slot count (`LEASE`/`UNLEASE` verbs) so a swarm self-limits.
   On this machine the busy pattern in `ix/heavy.sh` should also match `lane (prove|verify|submit|
   check|merge)`; that is a one-line change in this project, not in Lane.
8. **Fuel and determinism of outputs.** `--max-heartbeats N` on every elaborating command,
   passed as `maxHeartbeats` in `runFrontend`'s options and echoed in the result; no wall-clock
   timeouts in anything that feeds a label or reward (`plan.md`: labels use spec-defined fuel).
9. **Worker containment.** Keep the admin token outside the repository (e.g. a runtime dir or an
   inherited fd), put scratch dirs outside `.lane`, and ship a `lane worker-exec` wrapper that
   runs a worker under bubblewrap with the repository read-only, `.lane` hidden except the socket
   and its own scratch dir, and no network. Lane cannot prevent bypass today; this makes the
   capability model real for tier-3 use.
10. **Structured goals.** `goals` and `probe` return goals from the info tree (as
    `semanticGoalAt` already does for `--at`), with hypotheses and target as terms; with change 4,
    each goal also gets an Ixon address of its type in context, which is the key the proof-search
    cache uses.

11. **Outcome records, keyed by change.** A decision model around Lane (`docs/decision-library.md`,
    "Decisions inside an agent harness") learns from what happened to a finished change: was it
    merged, did the submission containing it pass `submit --require …` with its declarations
    unedited, or was it changed or discarded in review. On `a97befb` none of this is recorded
    against the change:
    - a merge leaves activity `lane.merged` (detail: target lane ID) and `lane.absorbed-source`
      (`Transactions.lean:316-319`) and a `merged-into` file; the change address appears only in
      conflict records (`source_change`);
    - `submit` stores per-declaration verify records keyed by the submitting lane's tree root,
      only with `--require` or an `ix` binary, and only before a refusal on the checks; a broken
      affected rebuild stores nothing; the outcome and its error code are only in stdout; success
      leaves the `submitted` marker and activity `lane.submitted` with a list of paths;
    - `DISCARD` leaves activity `lane.discarded` with an empty detail;
    - activity records carry a counter, a kind and a detail: no time, no origin, no address.

    The proposal: three canonical, timing-free records in the blob store, written by the server
    only on admin-token requests (the main agent's process; a worker's report is not an outcome),
    and filed under the address of the change record they concern, `.lane/outcomes/<change>/
    <record address>`:
    - `lane-merge-v1` from `MERGEBATCH` when the source lane has a change record: `change`,
      `target_before` and `target_after` (the target lane's tree roots around the merge), `paths`,
      `conflicts` (addresses of the conflicts it opened). The target also gets
      `lanes/<n>/merged-changes/<change>`.
    - `lane-submit-v1` from a new admin verb `SUBMITREC`, sent by `submitValidated` at each of its
      three ends (rebuild broken, checks failed, `SUBMIT` answered): `state` (the lane's tree root
      when the submission started), `required`, `accepted`, `code` (`null`,
      `AFFECTED_PROJECT_INVALID`, `REQUIRED_CHECKS_FAILED` or `SUBMIT_REFUSED`), `verify` (the
      verify record addresses). The server adds `changes`: the lane's merged changes and its own
      change if it has one, and files the record under each.
    - `lane-discard-v1` from `DISCARD` of a lane with a change record: `change`.
    - `lane outcomes <change-address>` (admin verb `OUTCOMES`) lists them.

    A label is then computed offline, from records only: a change is *clean* if a merge record
    exists and a later accepted submit record of the target has, for every declaration in the
    change's `edits`, the same command text in its `state` tree as in the merge's `target_after`
    tree (both are manifests in the blob store); *edited in review* if accepted with any of those
    declarations changed; *refused* if only refused submissions exist; *discarded* if a discard
    record exists. No existing record format changes.

    Left out: the legacy `MERGE` verb (`mergeLane`, unused by the CLI) and merges completed by
    journal replay after a crash (`recoverMerges`) write no merge record; a change merged into an
    intermediate lane that is finished and merged again is linked to the final submission only
    through the intermediate change's records. Heartbeats are still not stored: a cascade or
    budget-ladder label needs `fuel` written into the verify record, a format change (`lane-verify-v2`).
12. **Classification by the main agent.** A change record's `edits` are computed by the finishing
    client (`Validate.lean:266-288`) and, for a delegated lane, are a worker's report
    (`reported_by: worker`). The code to re-derive them is already in the fork: `laneChangeContents`
    and `laneEdits` (`Change.lean:75-102`) run in any client process with the admin token, and
    `submit --require` already runs them in the main agent's process against the recorded bases
    (`Analysis.lean:108-109`). Missing: a `lane classify <lane|change>` that runs them against the
    change's base, compares with the record's `edits`, and stores a `lane-classification-v1`
    record (`change`, `edits`, `outside_declarations`, `unclassified`, `agrees`) as another outcome
    of the change. About 60 lines with a test; not implemented. Until then a gate must treat
    `reported_by: worker` edits as unclassified, as `IxAIDecide/LaneGate.lean` does.

Changes 1–3 are self-contained in Lane and need no Ix. Change 4 is the bridge.

## Implemented in fork

Changes 1–8 are on branch `ix-addresses` of a local fork at `~/repos/forks/lane`
(`upstream` = `argumentcomputer/lane`, not pushed; tip `a97befb`, all of `tests/all.sh` passing,
including `tests/addresses.sh` and `tests/ix_merge.sh`, the latter against the `ix` built from
`ix.ci-merge-tests`). Changes 1–3, 7 and 8 end at `dfc15b8`; 4–6 are `ee9c130` (declaration merge
and conflicts), `633a96b` (Ix admission and Ixon-address merge equality), `830bb4b` (tests) and
`a97befb` (docs):
- **1.** `.lane/blobs/<blake3>` blob store; lane files and bases are refs; snapshots are canonical
  manifests whose address is the Merkle root (no copying on fork/checkpoint). BLAKE3 is the
  `blake3` 1.8.7 crate behind one `lane-ffi` function and `Lane/Address.lean`, the crate Ix's
  `Blake3.Rust` wraps; Lean tests check the BLAKE3 spec vectors. Reads return addresses and
  `WRITE`/`DELETE`/`MERGEBATCH` compare-and-swap on them. Older `.lane` homes are refused.
- **2.** `finish` stores a canonical change record (base and result roots, files with reported
  validation, per-declaration edits for theorems, defs, abbrevs, instances, opaques, axioms,
  structures and inductives, classified added/removed/proof_only/body_only/statement/modifiers/
  layout, notes, obligations, verify-record addresses). `lane change <lane|address>`; `merge`
  accepts a change address. The edits are classified by the finishing client and labelled
  `reported_by`.
- **3.** `verify` emits and stores a canonical, timing-free record keyed by the lane tree's root.
  `submit --require no-sorry,no-new-axioms,no-unsafe,no-native,standard-axioms` rechecks every
  changed declaration in the main agent's process from the affected rebuild's environments.
  Unchecked writes need `delegate --allow-unchecked`, and change records mark them.
- **4.** With an `ix` binary (`"ix"` in `.lane/config.json` or `LANE_IX`), changed declarations
  are compiled with `ix compile --no-build --consts` against the rebuilt imports and checked with
  `ix check-lean --allow-declined`, inside the heavy prefix. Each gets a canonical
  `lane-ix-check-v1` record (Ixon address, IxC outcome and detail, BLAKE3 of the `.ixe`, ix
  version). `submit` attaches it to every changed declaration's verify record and
  `--require ix-checked` refuses unless IxC accepts each; `finish --admit` (or `admit_at_finish`)
  stores `ixon`, `ix_outcome` and the check record's address per edit in the change record
  (client-reported, like the edits). Ix is still a subprocess, not a Lake dependency.
- **5.** `declarationAwareMerge` runs over the declaration inventory (`Lane/Prove/Inventory.lean`:
  theorems, defs, abbrevs, instances, opaques, axioms, structures, inductives), so edits to
  different declarations of any kind compose. When both sides changed one declaration differently
  and `ix` is configured, both module versions are compiled and equal Ixon addresses are not a
  conflict. The import block is still outside-declaration text that must agree.
- **6.** A merge applies everything else and records each conflict as a canonical
  `lane-conflict-v1` blob (path, declaration, kind, base/target/source text addresses, source
  change) opened in `lanes/<n>/conflicts/<address>`; the target becomes `conflicted` and refuses
  `finish` and `submit` (it still takes writes, merges and delegation, and `gc` keeps it).
  `lane conflicts`, `lane resolve <lane> <address|--all> [--take source|target]`, and
  `merge --abort-on-conflict` for the old fail-without-mutation behaviour. Change records list
  conflicts and their resolutions.
- **7.** The affected rebuild runs in a child `lane _validate` through `LANE_HEAVY_PREFIX` or
  `heavy_prefix` in `.lane/config.json` (e.g. `ix/heavy.sh`). No elaboration slots
  (`LEASE`/`UNLEASE`) yet.
- **8.** `--max-heartbeats N` on every elaborating command sets Lean's `maxHeartbeats` and, by
  elaborating synchronously, reports `fuel.heartbeats` deterministically.

Change 11 is on branch `outcome-records` of the same fork (one commit on `a97befb`, `f9a048d`,
not pushed): 105 lines in `Lane/` and `Main.lean`, `tests/outcomes.sh` (merge, refused and
accepted submit, discard, and a worker refused) and its entry in `tests/all.sh`. It has **not been
built or tested**: on 2026-11-20 the build and the suites `outcomes`, `addresses`, `merge`,
`semantic_actions`, `submission_recovery`, `collaboration`, `integration` did not run (the
heavy-job queue was hours long). Treat the branch as a draft until `lake build lane` and those
suites pass.

Building the fork here needs `LIBCLANG_PATH=/usr/lib/llvm-21/lib CLANG_PATH=/usr/bin/clang-21`
for `lean-ffi`'s bindgen (the clang bundled with Lean 4.34.1 comes first on `PATH`). Changes 9
and 10 are not started.

## Determinism and certificates

What survives as is:
- CAS semantics, journaled submit and merge, capability-scoped workers (advisory without change 9).
- Lean's kernel acceptance in the main agent's process, which is the same check `lake build` gives.
- Per-declaration three-way merge, which matches `ixvc`'s per-name merge in shape.

What does not survive without changes:
- Identity: lane, snapshot and record IDs are counters, local to one `.lane` and reset by
  `clean`; nothing names a result across machines. Changes 1–2 fix this for bytes.
- Determinism of records: responses mix results with timings (`prepare_ms`, `attempt_ms`) and
  order-dependent IDs; change 3 separates a hashed core.
- Trust: a worker's "accepted" is self-reported and its elaboration can run arbitrary code. The
  certificate route replaces this: at admission the main agent (or the local cluster) compiles the
  changed constants to Ixon, `ix check`s them out of circuit, and certifies at checkpoints
  (`ixvc.md`, Checking and certificates). Once a change carries `checkEnv`/`catalog` claims, how a
  worker produced its proof no longer matters, as with the untrusted GPU trainer.
- Source vs content: Lane works on text and Ixon addresses cover only semantics, so a Lane change
  maps to many byte-level versions with one semantic address. Until Ix's elaborator records
  tactic scripts as metadata, Lane's text is the source of truth for tactic proofs and Ixon is the
  checked content; the change record holds both.

## Integration path

0. **Now, no Lane changes.** Use Lane for parallel proof sub-agents in a 4.34.1 project this
   pipeline owns: `~/repos/ix.ixai-aiur` (refinement lemmas such as the step-only world
   restriction) or `ix/bundle`. One server in that repo root; one forked, delegated lane per
   Opus sub-agent; the main session merges, runs `verify --no-sorry --no-new-axioms --affected`
   and `submit` through `ix/heavy.sh`, then the existing `ix compile`/`ix check`/certify scripts.
   Replaces worktrees for those agents. Preconditions: start the server unsandboxed (it `setsid`s
   a child and listens on a Unix socket); add `lane` to `heavy.sh`'s busy pattern; never start a
   Lane server in `~/repos/ix.ci-merge-tests` (it writes `.lane/` and `.gitignore`).
1. **Baselines with tools.** A new IxBench baseline kind: Opus sub-agents with Lane tools on
   proving items, scored by `verify` in the main process and recorded as
   `(statement address, proof BLAKE3, Ixon proof address, check result)`, digest without wall
   clock or tokens. Items must have no proof on disk the worker can read: generated statements
   (M2b-style, from a seed committed after the run is set up) or a statements-only bundle repo,
   with the worker sandboxed away from Mathlib sources and `.lane` internals. For M2, `premises`
   of accepted proofs on held-out theorems gives a tool-using frontier comparison to the scorer's
   rankings.
2. **Addresses in Lane** (changes 1–3, 8). Lane handoffs become addressed changes with
   verification records; agents exchange change addresses instead of lane IDs and transcripts.
3. **Admission through Ix** (change 4, then 5–6). Lane's `submit` is the `ixvc` admission step:
   Ixon addresses and check claims in every change; certify at checkpoints with the existing
   pipeline. Lane's blob store points at the Truth Mines store.
4. **Lane as `ixvc`'s agent front end.** `ixvc` owns objects, refs and the store per machine;
   Lane keeps the Lean-semantic operations, sessions and capabilities, and its server becomes a
   client of the `ixvc` control plane (ref CAS instead of `submit` writing files). The local-mode
   cluster accepts `verify --affected` and certification as jobs by address, so one owner
   schedules them with GPU work.
5. **Proof search.** When Ix's pure elaborator and tactics exist, Lane's `runFrontend` calls
   become calls into it: grading moves from tier 3 to tier 1, `prove-session` steps become
   fuel-bounded, cacheable `(env, goal, tactic, fuel)` facts, and the same interface serves the
   IxAI proof-search agent (speaking Ixon) and LLM agents (through the JSON shim).

## Risks

- Toolchain lockstep: Lane, Ix and the target project must share one Lean version; a bump in any
  one breaks in-process elaboration. This project's root (4.34.0) is already out of step.
- Linking Ix into Lane (change 4, library route) pulls Ix's Rust archives and multiplies Lane's
  build cost; the CLI route avoids it at the cost of a process per admission.
- Containment: until change 9, a worker can read the admin token, edit canonical files and run
  arbitrary code; Lane is only safe with trusted workers or an external sandbox.
- Load: many in-process elaborations escape the heavy gate's process match; `--affected` on a
  module near the root of a large project rebuilds most of it.
- Merge scope: only theorems are declaration-merged; real swarms edit `def`s, structures and
  imports and will hit "conflict outside declaration commands".
- Maturity: one author, few months old, no external users, text protocol with substring-matched
  success (`"ok":false` searches in `Main.lean`). Expect API churn.
- Divergence: if Lane grows its own content-addressed history independently of `ixvc`, there are
  two version-control models; changes 1–2 should use `ixvc`'s object formats from the start.

## Open questions

- Is Lane `ixvc`'s front end (Lean-semantic ops, sessions) with `ixvc` as the backend, or does
  `ixvc` absorb Lane's operations? This doc assumes the first.
- Server scope: one per repository (Lane today) or one per machine over a shared store (`ixvc`)?
- Does Argument want Lane's verbs over Ixon constants (goals and probes on a stored constant, no
  source), which needs Ix's elaborator to record tactic scripts as metadata?
- How should a Claude Code sub-agent's sandbox be set up so its Lane calls reach the socket while
  canonical sources, `.lane` and answer keys stay unreadable, given that repo-local `.claude/`
  configuration is not allowed here?
- Which statement classes make honest tool-using baselines, given that a tool-using model can call
  `decide` on many kernel-decidable M2b items?
