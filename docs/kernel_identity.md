# Kernel term identity vs. Ixon content addressing

Ix has **two distinct identity layers**, and they serve different masters.
This document records the boundary between them — in particular why the
kernel's switch from per-node blake3 hashing to intern-assigned uids
(`1e3029d`, 2026-06) does not affect the proof-carrying-code story, and
what a future feature must do if it ever needs cryptographic identity at
sub-constant granularity.

## Layer 1: Ixon content addresses (external, cryptographic, in proofs)

The unit of cryptographic identity is the **constant**. A constant's
`Address` is the blake3 hash of its alpha-invariant Ixon serialization
(see `docs/Ixon.md`); blobs (the bytes behind `Nat`/`String` literals)
are addressed the same way. Everything that leaves the kernel speaks
this language:

- `Constant.refs` point at constant and blob `Address`es.
- `KId.addr` — the identity the typechecker certifies — is the Ixon
  `Address`.
- The Zisk guest's committed claim is built from `Address`es:
  `subject_root` / `assumptions_root` are `merkle_root_canonical` over
  the certified / assumed constant addresses (`crates/kernel/src/claim.rs`,
  `zisk/guest/src/main.rs`), and `env_hash` is blake3 over the exact env
  payload.
- Aggregation (`Claim::CheckEnv`, the `Contains` discharge) resolves
  assumption leaves against subject roots **by address**, and the
  cross-run proof store is keyed by address (content-addressed: the same
  constant has the same address in every env).
- Address↔bytes binding is enforced by `Address::hash(bytes) == addr`,
  verified at first materialization (`ixon::lazy::LazyConstant::get`).
  Every constant the kernel certifies is necessarily materialized, so
  everything that can enter a subject root has passed the check.

**Merkle inclusion proofs for individual constants live entirely in this
layer** and are unaffected by anything below: proving "address `A` is in
this proof's subject root" is an inclusion path in a tree whose leaves
are constant addresses.

The trust chain, end to end:

```
claim roots  ──Merkle──▶  constant Addresses
             ──verify──▶  serialized constant bytes   (blake3 binding)
             ──parse───▶  terms the kernel typechecked
```

## Layer 2: kernel node identity (internal, ephemeral, never serialized)

Inside one checker run, the kernel needs cheap identity for the
**in-memory expression/universe nodes** (`KExpr`/`KUniv`) churned out by
substitution, WHNF, and def-eq — for the hash-consing intern table, the
whnf/infer/def-eq cache keys, and quick equality. These objects are
ephemeral: they are never serialized, never compared against Ixon
addresses, and are torn down when the `KEnv` clears.

Historically this layer ALSO used blake3: every constructed node hashed
`(variant tag ‖ child hashes)`. That was a *separate scheme* from Ixon
addressing (a Merkle-DAG over node tags, not blake3-of-serialization) —
the two were never interchangeable — and it cost ~20% of all guest
cycles on reduction-heavy constants in the Zisk prover.

Since `1e3029d`, layer-2 identity is an **intern-assigned `u64` uid**
(`crates/kernel/src/env.rs::Addr`):

- Uids come from a process-global counter and are **never reused**, so
  `uid(a) == uid(b)` implies "same construction event or same
  intern-table canonical value" — i.e. structural equality. Stale cache
  keys can only miss, never alias.
- The intern table keys on **shallow structural keys**
  (`ExprKey`/`UnivKey`: variant tag + child uids + semantic payload),
  mirroring exactly what the old content hash covered — display names,
  binder info, and mdata are excluded, so interning semantics are
  unchanged.
- `PartialEq` for `KExpr`/`KUniv` is structural with the uid fast path:
  canonical-vs-canonical comparison is O(1), and completeness-critical
  `==` sites are unaffected. `hash_eq` remains the fast-but-incomplete
  uid check for cache/quick-path callers, where a false negative only
  costs a fallback.
- Soundness direction: caches and def-eq quick paths rely only on the
  affirmative ("equal uid ⇒ equal term"), which holds by construction.
  An imperfect intern hit-rate degrades performance, not correctness.

Nat/Str literal nodes keep their blake3 **blob** `Address` (that is
layer-1 data riding on the node, used by `refs`/assumption filtering).

## The boundary rule

> Anything that crosses the kernel boundary — claims, public values,
> proof-store entries, assumption sets — is identified by Ixon
> `Address`. Kernel uids must never escape into a serialized artifact.

This held before the change (nothing consumed the old expr hashes
outside the kernel) and is now structurally enforced by the type split:
`Address` (32-byte content hash) vs `Addr = u64` (kernel uid) vs
`CtxAddr` (blake3 digests for local-context cache keys, fed by uids,
also internal-only).

## Future: sub-constant commitments

If a feature ever needs cryptographic identity for **subterms** (e.g.
Merkle inclusion of a specific expression inside a constant's body,
rather than inclusion of a constant in a claim), expression-level
content hashes no longer exist precomputed. The right move is to compute
them at that boundary: a one-time egress pass over the relevant term —
either the old `(tag ‖ child hashes)` Merkle-DAG scheme or blake3 over
the Ixon serialization of the subterm. That is cheap where it is needed
and keeps the per-node cost out of the prover's hottest loop. No current
artifact (claims, aggregation, reuse, inclusion proofs at constant
granularity) needs it.
