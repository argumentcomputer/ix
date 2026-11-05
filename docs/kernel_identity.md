# Kernel term identity vs. Ixon content addressing

Ix has **two distinct identity layers**, and they serve different masters.
This document records the boundary between them: why the checker's internal
term identity does not affect the proof-carrying-code story, and what a
future feature must do if it ever needs cryptographic identity at
sub-constant granularity. The checker is the certified IxC kernel
([kernel](kernel.md)); its executed term operations are in
`IxC/Kernel/Expr.lean` and `IxC/Kernel/Cached/`.

## Layer 1: Ixon content addresses (external, cryptographic, in proofs)

The unit of cryptographic identity is the **constant**. A constant's
`Address` is the blake3 hash of its alpha-invariant Ixon serialization
(see `docs/Ixon.md`); blobs (the bytes behind `Nat`/`String` literals)
are addressed the same way. Everything that leaves the kernel speaks
this language:

- `Constant.refs` point at constant and blob `Address`es.
- The checker reads every record and blob under its Ixon `Address`.
- Claim roots are built from `Address`es: Merkle roots
  (`Ix.Merkle.merkleRootCanonical`) over the certified and the assumed
  constant addresses.
- Aggregation (`CheckEnv` claims, the `Contains` discharge) resolves
  assumption leaves against subject roots **by address**, and the
  cross-run proof store is keyed by address (content-addressed: the same
  constant has the same address in every env).
- Address↔bytes binding is checked before anything is decoded: the
  certified entry authenticates every record and every blob as the hash of
  the bytes stored under it (`Admission.authenticate`; [kernel, "The
  certified entry"](kernel.md#the-certified-entry)). Host tools that load an
  `.ixe` lazily check the same binding at first materialization
  (`ixon::lazy::LazyConstant::get_at`).

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

### Definition dependency admission

External dependency addresses are pinned by the constant's bytes:
constructing a cycle between blocks would require solving a hash preimage.
Cycles inside a block go through local `Rec` slots and need an explicit
check. IxC's reader (`IxC/Kernel/Ixon/Reader.lean`) applies the safety
policy to every member of a definition block first, then orders the block
so that every member follows the members it names (`defOrder`). A safe
block with no such order is declined as a mutually recursive definition
block: like Lean's kernel, the checker has no safe mutual definitions. A
member that names itself is checked before it is added, where the
reference does not resolve.

Consequently, checking one declaration need not traverse the expression
trees of its entire external dependency closure. Those declarations remain
assumptions until their own work items are checked, as in the proof claim
model above.

## Layer 2: kernel node identity (internal, ephemeral, never serialized)

Inside one checker run, the kernel needs cheap identity for the
in-memory expression nodes churned out by substitution, WHNF and def-eq:
for memo keys, cache keys and quick equality. These objects are ephemeral:
they are never serialized, never compared against Ixon addresses, and die
with the run.

IxC has one expression type, `Ix.Kernel.Expr`, whose nodes carry derived
data as Lean `@[computed_field]`s: a hash, the loose bound- and
free-variable bounds and a level-parameter flag, packed into one word
(`Expr.data`; `IxC/Kernel/Cached/ExprNodes.lean`). There is no hash-consing
table. Terms are shared by Lean's own structure sharing: an operation
returns unchanged children by reference, so a result shares every unchanged
subterm with its input.

- **Equality is decided, not assumed.** The executed equality follows the
  official kernel: pointer equality first, then the computed hashes, then
  structural descent (`IxC/Kernel/Expr.lean`). Every branch returns
  `Decidable (a = b)`. Pointer equality is a fast path for equal terms and a
  hash mismatch one for unequal terms; an equal hash decides nothing.
- **The equality memo is verified.** An entry is the pair of objects a
  completed descent proved equal, with the proof. A probe finds a
  candidate by the packed address pair (`beqKey`) and then checks the
  candidate by identity, so a key collision between distinct pairs costs an
  entry, never an answer.
- **Memo keys are terms.** The scope and definedness walks key their memos on
  `Expr` itself (`Std.HashMap Expr α`: hashing off the cached field,
  pointer-first equality); the substitution walks key theirs by address
  (`IxC/Kernel/Cached/ExprOpsC.lean`).
- **Trust.** That the stored word agrees with the function defining it is
  the code generator's guarantee, not a theorem of this repository:
  `@[computed_field]` is implemented with `implemented_by`. It is the one
  entry of the trust census in `IxC/Kernel/Cached/ExprNodes.lean`.

Before IxC, this layer belonged to the retired Rust kernel: per-node blake3
hashes at first, then intern-assigned `u64` uids from a process-global
counter, with a hash-consing intern table keyed by shallow structural keys
([retired Rust](retired-rust.md)).

## The boundary rule

> Anything that crosses the kernel boundary — claims, public values,
> proof-store entries, assumption sets — is identified by Ixon
> `Address`. The checker's node hashes and object addresses must never
> escape into a serialized artifact.

## Adversarial model

The natural worry about non-cryptographic internal identity is collision:
*if two subterms had the same internal hash, a def-eq or WHNF cache hit
could return a result for the wrong term.* Here a collision costs time,
not soundness:

- An equal hash never decides equality: the descent continues
  structurally, so a collision makes a comparison slower, not wrong.
- Hash maps keyed by `Expr` compare keys with that decided equality, so a
  bucket collision causes an extra comparison, not a wrong hit.
- The equality memo checks every candidate by identity before using it.
- Object addresses are not content: an input cannot choose them, and
  nothing serializes them.

An adversarial environment can choose term contents, and so can grind
contents to collide hashes and flood buckets. That slows the checker,
which is spending its own cycles; it does not change an answer.

## Future: sub-constant commitments

If a feature ever needs cryptographic identity for **subterms** (e.g.
Merkle inclusion of a specific expression inside a constant's body,
rather than inclusion of a constant in a claim), the checker's node hashes
are not it: they are not cryptographic, and no artifact carries them. The
right move is to compute that identity at the boundary: a one-time egress
pass over the relevant term, for example blake3 over the Ixon serialization
of the subterm, or a `(tag ‖ child hashes)` Merkle-DAG. That is cheap where
it is needed and keeps the per-node cost out of the prover's hottest loop.
No current artifact (claims, aggregation, reuse, inclusion proofs at
constant granularity) needs it.
