# Ix version control and cluster

A content-addressed version control system and compute cluster built on Ixon, for people and
agent swarms working on one shared store. It follows Unison's model (names as metadata, immutable
namespaces, hash-keyed edits, conflicts as data, computations shipped by hash) and Unison Cloud's
architecture (a control plane plus a self-organising data plane), and adds what Ix uniquely has:
certificates that make every result checkable by anyone. Pointers to all sources are in
`references.md`.

## Why

- Agents coordinate through Git worktrees and transcripts today. Worktrees multiply build
  artifacts (this machine has run out of space from them), Git diffs text rather than meaning,
  and a transcript is a slow, lossy way to hand work to another agent.
- At agent scale, Anthropic (Scion) and OpenAI (Pando) both moved to server-centric,
  content-addressed backends with metadata APIs separate from lazy content fetch. Neither makes
  the content checkable: CI is still re-run and trusted.
- Ixon already gives alpha-invariant, deduplicated, BLAKE3-addressed declarations, a shared
  store, and claims (`checkEnv`, `catalog`, `contains`, `reveal`) with 584-byte certificates.

## Data model

### Objects

All objects are Ixon, addressed by BLAKE3, stored once in the shared Ix store.

- **Constant**: an Ixon declaration. Its address covers only semantic content.
- **Metadata**: names, binder information and, with Ix's own elaborator, source-level information
  attached to constants: tactic scripts, docstrings, comments, formatting. Metadata is addressed
  separately, so renaming, re-commenting or reformatting never changes a constant's address.
  `ix decompile` already recovers Lean constants from Ixon plus metadata; extended with recorded
  tactic scripts and layout, it recovers source, so there is no separate source layer to keep in
  sync. Until Ix's elaborator records tactics, proofs decompile to terms.
- **Namespace**: an immutable map from names to constant addresses, plus a metadata map.
  Hashed like any object.
- **Blob**: raw BLAKE3-addressed bytes, for content that is not (yet) Ix: Rust, CUDA, data,
  docs. Transitional; the aim is that Ix-compiled code needs none.
- **Context**: the plan, transcript or reasoning behind a change, as a blob or structured object,
  linked from the change that it explains. Agents hand each other a change address, not a
  transcript.
- **Change**: one history node:
  - parents (one, or two for a merge);
  - the resulting namespace root;
  - edits, keyed by constant address: old address → new address, each classified (below);
  - context address;
  - claim addresses: what is asserted about the result, and certificates if produced.

  A change's address is the BLAKE3 of all of the above, so history is a Merkle DAG, as Unison's
  causals are.
- **Conflict**: a name bound to two or more addresses, stored as data in a namespace (as in
  Unison and Jujutsu) and resolved by a later change. A namespace with conflicts cannot be
  released.

### Refs

Mutable names for changes: `main`, release branches, per-agent branches. A ref moves only by
compare-and-swap on the control plane (Scion: one row). Everything else is immutable.

## Edits and propagation

Ixon addresses include definitions' bodies and dependents reference constants by address, so an
edit changes the address of everything downstream, as in Unison. What differs is when dependents
are guaranteed to still check:

| Edit | Dependents | Action |
|---|---|---|
| Theorem proof changed, statement unchanged | Always still check: typing depends only on the statement (proof irrelevance) | Propagate automatically. A cheap "same-type substitution" certificate can replace re-checking dependents. |
| Definition body changed, type unchanged | Usually still check, but proofs that unfold the definition (`rfl`, `decide`) may break | Propagate, re-check the affected closure. |
| Type or statement changed | Need updating | Unison's update flow: a branch, the broken dependents in a scratch file, a `todo` frontier ordered from the edges of the dependency graph inward. |
| Rename, docs, comments, formatting | Unaffected: metadata only | No semantic change. |

The invariant, as in Unison: the namespace on every ref always type-checks.

## Merge

Three-way, per name, against the merge base in the change DAG:
- edits to different constants commute;
- the same edit on both sides is not a conflict;
- different edits to the same name produce a conflict object;
- after merging names, dependency closures are re-checked; a merge that type-checks per side can
  still fail jointly (one side changes a statement, the other adds a use of the old one), which
  re-checking catches.

Formatting, import order and declaration order never conflict, because they are not content.

## Checking and certificates

Two levels, by cost:

1. **Check** (every change): `ix check` of the changed closure, out of circuit. Deterministic, the
   same result on every machine. Results are cached by address, so unchanged constants are never
   re-checked, by anyone, ever: Unison's "no builds", extended across machines.
2. **Certify** (checkpoints, releases, anything leaving the machine): a `catalog` claim over the
   environment's `checkEnv` claims, aggregated and compressed to PLONK. Shard proofs are cached by
   address (`~/.ix/cache`), so a new checkpoint re-proves only shards whose contents changed.

Commit rates at agent scale (Scion: 30,000 merges a day) are far above proving rates, so
certification happens at checkpoints, not per change.

## Cluster

### Local mode (first)

On one machine there is no one to distrust, so control plane and worker are one server that owns
the GPU and the store: a queue of jobs by address, GPU training emitting weights and witnesses,
proving (Aiur steps, IxVM shards with cache hits, aggregation, PLONK), then recording the result
and certificate and moving the ref. One owner of the GPU serialises GPU work instead of separate
gated scripts contending for it. Verification stays: it costs milliseconds, catches our own bugs
(a GPU trainer disagreeing with the spec), and the certificate is the product for anyone the
result is handed to. Job and result formats are the same as below, so the split costs nothing to
add later.

### Distributed mode

Unison Cloud's split, with trust replaced by proof, once machines or people that are not trusted
join.

### Control plane

- refs and their compare-and-swap; authentication; membership; quotas;
- admission: a ref update is accepted only if the change's claims check: every change has a
  check record, and protected refs (`main`, releases) require a certificate, which verifies in
  milliseconds;
- metadata APIs (history, blame, dependents, merge bases, search by type) served from indexes
  derived from the change DAG, so most clients never fetch content;
- synchronous, acknowledged invalidation to workers when refs move, as cloud-api does for nimbus
  (sequence-numbered events, per-node acknowledgements, a deadline). Content-addressed caches
  never need invalidating; only names do.

### Data plane

Workers run jobs by address:
- a job is `(function address, input address, fuel, capabilities)`; capabilities are the effects
  the job may use, as Unison abilities restrict remote code;
- a worker fetches missing objects from the store by address (Nimbus ships code inside the
  serialized value; here code and data are both store objects);
- a worker returns the result address plus evidence: a check record, an Aiur witness package, or a
  certificate. The control plane verifies before accepting. Nimbus trusts its nodes; this
  cluster does not need to, so untrusted GPU workers and other organisations' clusters are safe
  to use.

Deployment identity is the Ixon address of the code, not a hash of serialized bytes (Unison Cloud
keys deployments by SHA-256 of the serialized payload, separate from its definition hashes), so a
certificate can name exactly what was deployed.

### Store

One shared store per machine and one per cluster, with lazy fetch by address between them.
Agents on a machine share it instead of separate worktrees, so build artifacts exist once. Until
Ix's elaborator loads environments directly from the store, Lean still needs `.olean` files to
elaborate; a shared content-addressed build cache covers that gap.

## How IxAI uses it

- **Training**: datasets are namespace or Merkle roots; a run is the job
  `train(spec, config, dataset)`; its certificate `train spec config D = W` is the claim on the
  change that records `W`. Model lineage (data, traces, model, next model) is change history with
  proofs.
- **Inference and search**: tactic outcomes keyed by `(env, goal, tactic, fuel)` are store objects,
  so one agent's search result is every agent's cache hit.
- **Orchestration**: an agent publishes a change (edits, context, claims) and hands over its
  address. The receiver fetches lazily, reads the context, and checks the claims instead of
  re-reading a transcript. Across people and organisations this goes through the control plane,
  with `reveal` and commitment claims for proving properties of code that is not disclosed.

## Open questions

- Elaboration determinism: the same source must give the same addresses; Ix's own elaborator is
  where to guarantee it.
- The exact metadata schema for tactic scripts and layout, and decompile fidelity for them.
- A cheap certificate for same-type theorem substitution, so proof edits never re-check
  dependents.
- Dependency versions side by side (Unison's `lib`): two Mathlib versions coexisting by address,
  and tooling to consolidate them.
- Garbage collection and retention in a shared store.

## First steps

1. Change, namespace, conflict and context objects as Ixon, in the Truth Mines store.
2. A local ref file with compare-and-swap; `ixvc commit`, `log`, `diff` (per name, by address),
   `merge` (three-way per name, then closure re-check).
3. Admission via `ix check`; a checkpoint command producing a `catalog` certificate.
4. Use it for this project's parallel agents (refinement proofs, GPU trainer, premise data):
   merge their work by address instead of through worktrees.
5. Then the control plane and a worker that runs `ixai` jobs by address and returns witnesses.
