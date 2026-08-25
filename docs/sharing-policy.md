# Ixon v2 sharing policy freeze

Status: Compilatrix's local policy is frozen as
`compilatrix/ixon-v2-sharing/1`. External catalog ingress separately
recognizes `ix/ixon-v2-sharing@6f18ea907b78d06f7dc0917c43beb385561c35f4`.
That v2 capture revision has Git tree
`c09cfe3df1ee6ff92009672cc9077b4b7e2db63a`; the frozen transcript has BLAKE3 fingerprint
`19aa227e6be89cbabef37366bdc3a48fcf1d8f856892054511ae6b6fcf1db4ce`.
Last reviewed and recaptured 2026-08-25.

These are compressor-policy regression identifiers, not constant addresses.
Ixon v2 carries binder modes natively. Compilatrix's local compressor
deliberately strengthens ix with maximal-telescope safety and an exact
serialized-byte deletion audit. The catalog boundary does not normalize
production artifacts into that stronger spelling: it reproduces and checks
the exact pinned ix compressor, then hashes the stored serialization.

## Baseline and vectors

The pinned ix sharing suite compares the Lean and Rust sharing count and
complete rewritten body/table vectors. Its six directed cases are represented
directly in ix's native v2 syntax and in Compilatrix's ordinary-Lean fragment:
every `lam` carries `Uses.many`, and every `all` carries
`Uses.many`/`Owned.shared`.

[`Tests.lean`](../Tests.lean) records the captured ix output and required local
output as exact `Compression` values:

| Case | ix table | local table | Classification |
| --- | ---: | ---: | --- |
| `simple` | 1 | 1 | exact |
| `content-hash` | 1 | 1 | exact |
| `recursor` | 0 | 0 | exact |
| `forall-imp-sharing` | 2 | 2 | exact |
| `forall-imp-real` | 8 | 5 | intentional local strictness delta: the exact audit removes three nested entries; both sides use their captured v2 order |
| `flip` | 2 | 1 | intentional local strictness delta: the inner `all` is a non-maximal suffix, so sharing it would split the canonical telescope |

`Tests.lean` also freezes the upstream framed input and output bytes for all
six cases. Every runtime case checks those independent literals against the
transcribed ix value, exact local raw output, exact pinned-ix recompression,
both inline-recovery paths, and the declared parity/delta relation. The ix
output must satisfy the common structural invariant and the external
exact-image predicate. The local output must additionally satisfy the
direct-use layer 1 rule, deletion-local optimality, the stronger
all-entries-pay diagnostic, and local layer-2 recompression canonicality. The
checked local compressor is compared to its raw output so its certified
identity fallback cannot hide a policy regression.

The same capture freezes two complete constant byte/address pairs: the
110-byte all-modes `goldenV2` fixture with a shared table, and a small axiom.
Both decoded back to the original ix values; ix's Rust writer agreed
byte-for-byte with its Lean writer for both. These are raw wire/hash captures:
their synthetic out-of-range local universe indices intentionally fail
`DecodeCheck.checkedWF`, so the strengthened semantic `address?` API rejects
them even though their BLAKE3 digests remain frozen.

The fingerprint transcript is canonical binary data in fixed case order. It
contains a one-byte parity/delta classification followed by framed input
expressions, the captured ix bodies/table, and the required local bodies/table
for each case. Names are descriptive and are not hashed. All expressions use
the real v2 serializer.

## Local and external exact-image policies

`Sharing.layer1WF` is Compilatrix's local cheap invariant: sharing is
backward-only and non-alias, body references are in bounds, and every table
entry has at least two direct uses across later entries and bodies. Local
`compress?` / `canonical` add maximal-spine protection and an exact serialized-
byte deletion audit. `Constant.addressCheckedWith` admits only that image.

The pinned ix compressor can first share a child and then share its parent,
leaving the child with one direct table use. Its output remains safe and
deterministic, but can fail the local direct-use rule. `Sharing.structuralWF`
therefore names only the common safety core: backward-only non-alias entries
and in-bounds body references. It is sufficient for total share elimination;
it is not, by itself, an identity rule.

`Sharing.compressIxonV2?` reconstructs the upstream decision and table order
on structural representatives. In particular, it preserves ix's historical
effective-size heuristic, which sums per-AST-node header sizes and therefore
overestimates flattened application, lambda, and forall spines. Unlike the
local compressor, it performs neither the maximal-telescope filter nor the
post-compression deletion audit. Structural equality authorizes rewrites and
canonical bytes break digest ties, so hash collisions cannot silently merge
different expressions.

`Sharing.ixonV2Canonical` expands a candidate constant and requires exact
recompression to its stored bodies and table. The bounded form applies the
same layer-1-work and expanded-input limits as the local recognizer.
`DecodeCheck.decodeIxonV2CheckedWith` combines the structural parser with all
wire and local evaluator checks, and `Constant.addressIxonV2CheckedWith`
combines it with the exact-image predicate before hashing `ser c`. Thus
catalogs preserve production ix addresses without admitting arbitrary DAG
spellings or weakening the local Compilatrix policy.

The byte-exact Std contact in
[`fixtures/ixon-std-contact`](../fixtures/ixon-std-contact) exercises this
path on 54 production constants in addition to the six directed sharing
vectors. Its roots, counters, and downstream outcome are recorded in
[`corpus-contact.md`](corpus-contact.md).

## Reproduction

The 2026-08-25 capture was made from a clean `git archive` of the exact tree
above, never from the dirty development checkout. A temporary v4.33.1 runner
imported `Ix.Ixon`, `Ix.Sharing`, `Tests.FFI.Ixon`, and `Tests.Ix.Sharing`,
linked ix's `test-ffi` library, and:

1. ran ix's complete Lean/Rust sharing suite successfully;
2. serialized the two constant fixtures with `Ixon.serConstant`, checked the
   same bytes through `rsEqConstantSerialization`, decoded them, and hashed
   them with `Address.blake3`;
3. framed each sharing input and `Ix.Sharing.applySharing` result using the v2
   expression writer.

The emitted literals are the `IxRebaseline` data in `Tests.lean`; the capture
runner was intentionally temporary. To re-pin, archive the new exact commit,
repeat those three operations using the fixture constructors in `Tests.lean`,
and review every changed literal. Then run:

```sh
nix flake check path:.
```

That check verifies the captured bytes, local raw encode/decode/hash agreement,
semantic-gate rejection of the synthetic fixtures, the intended compressor
deltas, and the policy fingerprint under
Compilatrix's pinned toolchain. The obsolete v4.31 shell/subproject harness was
deleted when these vectors landed.

## Change protocol

Any intentional local policy change must update all of the following in one
review:

1. `Sharing.compressorPolicyId`;
2. the exact ix/local vectors, capture literals, and relation labels in
   `Tests.lean`;
3. the transcript fingerprint above and in `Tests.lean`;
4. this delta table and the canonical-sharing design note;
5. downstream constant-address fixtures affected by recompression.

An upstream ix revision change additionally requires a clean-archive capture,
the upstream Lean/Rust checks above, review of the pinned ix sharing, codec,
and FFI source set, an `ixonV2PolicyId` update, exact external-recognizer
agreement on all six vectors, and regeneration/review of the production
catalog fixture if any committed bytes or addresses change.
