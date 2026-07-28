# Lazy fault-in: address-keyed constants in the IxVM kernel

Design for removing the ingress-prediction problem from sharded checking.
Written after the frontier-stub approach was implemented and disproven; the
measurements that motivate it are in this document's final section.

## The problem

An Aiur shard's `CheckEnv` claim ingresses its owned blocks' entire
transitive reference closure. Measured across four environments, that
accounting is what fails to scale — the same bytes are re-ingressed and
re-hashed shard after shard:

| env | duplication | floor RAM | shards @250 GiB |
|---|---|---|---|
| Init | 56x | 174.8 GiB | 699 |
| InitStd | 509x | 482.9 GiB | 11,749 |
| Lean | 1,778x | 538.2 GiB | 56,293 |
| Mathlib | 1,667x | 3,829.7 GiB | 227,150 |

InitStd and Lean are infeasible at any box size under this accounting.

## Why the stub approach failed

The frontier-stub design ingressed a frontier constant as a type-only
axiom, dropping its value so its references were never followed. Modelled
offline it gave 699 -> 34 shards and a 174.8 -> 14.6 GiB floor.

It does not work, because the set of constants a shard may only *mention*
(safe to stub) versus must *compute with* (must be whole) cannot be
predicted:

- The `.ixprof` delta graph records what reduction unfolded during one
  profiling run. The packer honours it exactly — verified: across all 35
  shards, **zero** stubbed blocks are delta targets of fully-ingressed
  blocks.
- Recording is not the gap either: both unfold sites in the Rust kernel
  (`whnf.rs` `delta_unfold_one` and `try_delta_unfold`) call
  `record_delta_target`, and def-eq's lazy delta goes through the former.
- Yet every shard fails at `Infer.lean`'s `k_check` — `k_is_def_eq`
  returns 0 because reduction needs to unfold a stub.

Stubbing a definition turns it into an axiom, which has no definitional
height, which changes lazy-delta's unfold-order decisions. The measurement
perturbs the thing it measures. Prediction is out.

## The economic fact that shapes the design

A constant's type and value live in ONE serialized blob under ONE content
address, and `load_verified_constant` blake3-hashes the whole blob to
verify it. **There is no way to obtain a type without hashing the value.**

So stubbing never saved bytes per constant — `axiomatize_frontier` runs
after the load. Its entire saving came from not walking a stub's
references, i.e. a smaller SET.

Lazy fault-in saves the same way: a smaller set, discovered instead of
predicted. Per touched constant the cost is identical. The two approaches
therefore target the same economics, and lazy fault-in should land near the
same numbers — correctly.

## Why address-keyed, and why "static positions, lazy content" is not an option

`KExprNode.Const(G, List<KLevel>)` holds a positional index into a
materialized `top: List<&KConstantInfo>`, threaded through 195 signatures
across 8 kernel modules (Inductive 82, DefEq 29, CanonicalCheck 22, Whnf
21, Primitive 16, Infer 15, Check 10) with 75 `list_lookup(top, idx)`
sites. Aiur has no mutable state, so a faulted-in constant has nowhere to
go in that table.

Keeping positions but faulting in content is incoherent: assigning
positions needs `block_kernel_size(members)` for mutual blocks, which needs
the constant's content. The table cannot exist until everything is loaded.
The only escape is a host-supplied layout the kernel verifies, which adds a
soundness surface of the same class as the const/blob confusion already
found in the audit.

Address-keyed is therefore the only coherent design, and it is better on
the merits:

| | positional (today) | address-keyed |
|---|---|---|
| identity | index into a materialized list | content address |
| primitive dispatch | `find_addr_idx_safe`, linear scan | `address_eq`, O(1) |
| ref resolution | `addr_pos_map` + `pos_map` + `canonicalize_pos_map` + `block_start_map` + `build_addr_tree` + `compute_layout` | local: `Expr.Ref(i)` -> `Const(c.refs[i])` |
| reordering attacks | guarded by `check_canonical_block_sort` | impossible by construction |

The refactor is mostly deletion: those signatures thread `top`/`addrs`
precisely to resolve positional indices, so most lose two parameters rather
than gain one, and the whole layout/pos-map subsystem goes away.

Two mechanisms must survive in new form:

- **Canonicalisation.** IXON can encode the same logical inductive under
  several wrapper addresses; `canonicalize_pos_map` exists for that.
  It becomes a memoized `canon_addr(addr)` applied where identity is
  compared.
- **Mutual-block references.** `Expr.Rec(i)` names a member by index and
  resolves to the member's synthesized projection address;
  `cprj_content_addr` is the existing precedent for computing one
  in-circuit.

## Resolution

    fn get_const(addr: Addr) -> &KConstantInfo

reads ch 2, blake3-verifies against `addr`, deserializes, and converts with
every `Expr.Ref(i)` becoming `Const(c.refs[i])`. Aiur memoizes function
calls, so repeat resolutions are free — the circuit statistics' cache-hit
accounting is the same mechanism.

## The claim gets simpler

A lazily-faulting shard cannot enumerate its ingress set, so the current
three-root claim stops making sense — and stops being needed:

    CheckEnv(env_root, owned_root)
      = every constant named by owned_root typechecks, assuming every
        other constant of the env rooted at env_root is well-typed.

Stubs, assumption trees, `stubbed_blocks`, and the per-shard ingress
computation all disappear. Aggregation gets cleaner: `shardsCover` already
enforces that owned sets partition the env, so the union of shard claims
discharges every assumption against one env root.

This needs **per-fault membership proofs**. `load_assumption_tree` today
reads a whole tree and merkle-folds it; over a 631k-leaf env that is ~20 MB
hashed per shard, a floor in itself. Instead each fault-in carries a merkle
inclusion path on a new channel, folded to `env_root`: ~20 hashes against a
constant whose own bytes cost far more.

## Sequencing

0. **Measure touched-vs-closure** per block in the Rust kernel, which is
   already lazy — an instrumentation counter, not a redesign. Gates the
   whole plan and yields the cost-model input the packer needs, since
   ingress can no longer be predicted.
1. **Address-keyed `Const`, eager driver.** Change the representation, add
   `get_const` / `canon_addr`, but keep pre-loading so behaviour is
   unchanged and the existing codegen/interpreter parity harness plus the
   64 pinned FFT fixtures verify the refactor.
2. **Make the driver lazy.** Delete the pre-load; claim shape unchanged.
3. **New claim + merkle-path membership**; delete the stub machinery.
4. **Packer and cost model** rebuilt on measured touched-bytes.

Step 1 is the bulk and the risk; `Inductive.lean` carries the heaviest
positional reasoning about constructor and recursor indices.

## Step 0 result: the gate is passed

Lazy fault-in's saving is exactly "closure minus touched". Measured by
instrumenting `try_get_const` to record every constant CONSULTED while
checking one constant (`IX_TOUCH_STATS=1 ix profile`), over a 400-block
sample of Init:

| | median | mean | max |
|---|---|---|---|
| constants touched | 19 | 37 | 277 |
| reference-closure blocks | 273 | 631 | 3,401 |
| touched / closure | **0.090** | — | p90 0.79 |

Checking a block consults ~9% of its reference closure at the median. The
saving is roughly an order of magnitude, and it needs no prediction: the
kernel faults in exactly what it touches.

Caveats on the ratio, which is approximate rather than exact:

- `touched` is counted per CONSTANT while the closure is per BLOCK, and a
  block may hold several constants.
- `touched` includes primitives and synthetic entries that are not in the
  reference closure at all, which is why a few samples exceed 1.0.
- It measures a whole-env profiling run. Per-constant checking is the same
  computation in a shard, so the set should transfer — but the figure that
  finally matters for shard count is the UNION of touched sets over a
  shard's owned constants, which overlaps more than the per-constant sets
  do. That union is not yet measured; recording full touched sets rather
  than counts would give it, and would also supply the cost model Step 4
  needs.
