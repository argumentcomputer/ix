# Ixon v2 wire format

Status: implemented by `Compilatrix/Ixon`, 2026-08-14. Integers below are
unsigned. Multi-byte integers are little-endian.

This document specifies the bytes hashed by Compilatrix. It is normative for
the current prototype together with the exact 110-byte fixture in
`Compilatrix/Ixon/Const.lean`. Sharing-table validity is specified in
[`canonical-sharing.md`](canonical-sharing.md). Primitive cursor-relative
specifications support laws for all five top-level codecs. Accepted-byte
canonicality is global for `Address`, `Univ`, `Expr`, `ConstantInfo`, and
`Constant`. Roundtrip is global for `Address` and `Univ`, restricted to the
exact u64-count-representable domain for `Expr` and `ConstantInfo`, and also
requires decoder-enforced sharing validity for `Constant`. Rejection guards
and the fixture additionally pin malformed-input behavior and exact bytes.

## Versioning decision

Ixon objects do **not** carry an in-band magic or version byte. The first byte
is one of the existing `TagN` headers. This preserves the ix format family and
avoids a redundant hash roll merely to repeat envelope metadata in every
Merkle-DAG node.

The store/protocol namespace must therefore select the decoder explicitly as
`wireFormatId = "ixon-v2"`; v1 and v2 addresses must not be mixed in an
unlabelled resolver.
A future v3 uses a distinct external format identifier and necessarily rolls
all affected content hashes. Adding an in-band prefix later would itself be a
new format version.

The v1-to-v2 semantic change is confined to binder mode bytes: v1 values are
re-encoded, not decoded ambiguously as v2.

## Canonical tag headers

A `TagN` byte contains an `N`-bit flag, one `large` bit, and `7-N` small-size
bits:

```
[ flag:N | large:1 | small-size-or-byte-count-minus-one:7-N ]
```

| Header | Flag bits | Small sizes | Large threshold |
| --- | ---: | ---: | ---: |
| `Tag0` | 0 | 0–127 | 128 |
| `Tag2` | 2 | 0–31 | 32 |
| `Tag4` | 4 | 0–7 | 8 |

For a large header, the low field is `byteCount - 1`, followed by 1–8 bytes
containing the size as a trimmed little-endian `u64`. A decoder rejects:

- a byte count greater than 8 before consuming its payload;
- a non-minimal byte count;
- a large form whose size fits the small form;
- EOF; and
- bytes remaining after the requested top-level value.

## Primitive values

- `Address` is exactly 32 bytes. Its length invariant is enforced by the Lean
  type, not merely checked by the serializer.
- Standalone booleans are exactly `0` or `1`.
- Arrays are encoded as a `Tag0` element count followed by the elements.

The variable-width integer substrate has pure canonical encoders and decoders.
`u64LEBytes_of_decode` proves byte-for-byte re-encoding for every payload of at
most eight bytes, and `u64OfLEBytes_encoded` proves decoding of every minimally
encoded `UInt64`. The `Tag0`/`Tag2`/`Tag4` writers and readers compose these
lemmas into cursor-relative encoder-to-decoder specifications (with the
declared flag-width preconditions for `Tag2` and `Tag4`).

## Universe levels

Universes use `Tag2`:

| Flag | Size | Payload | Value |
| ---: | --- | --- | --- |
| 0 | 0 | none | `zero` |
| 0 | `n > 0` | one universe | `n` successive `succ` nodes around the base |
| 1 | 0 only | two universes | `max` |
| 2 | 0 only | two universes | `imax` |
| 3 | variable index | none | `var` |

A successor header may expand at most `maxSuccExpansion` nodes
(currently 4096). A longer source run is uniquely chunked: every non-final
header has size 4096 and its base is another `succ` chunk; the final header's
base is not `succ`. Thus a short header with a `succ` base and any oversized
header are rejected. `getUniv_bounded` proves the per-header invariant
recursively through chunks, `max`, and `imax`; total expansion is consequently
linear in the input length rather than an unbounded request from one `u64`.
`Univ.roundtripLaw` and `Univ.canonicalLaw`, proved compositionally in
`Univ.lean`, cover every universe tree, every canonical split of a successor
run, and every byte string accepted by the strict universe decoder.

## Expressions

Expressions use `Tag4`. Size is the inline index/count unless stated
otherwise.

| Flag | Form | Payload |
| ---: | --- | --- |
| `0x0` | `sort` | size = universe-table index |
| `0x1` | `var` | size = de Bruijn index |
| `0x2` | `ref` | size = universe-argument count; `Tag0` ref index, then indices |
| `0x3` | `recur` | as `ref`, using the current mutual block |
| `0x4` | `prj` | size = field index; `Tag0` type-ref index, then value |
| `0x5` | `str` | size = blob-ref index |
| `0x6` | `nat` | size = blob-ref index |
| `0x7` | `app` | size = argument count; base, then arguments |
| `0x8` | `lam` | size = binder count; binders, then body |
| `0x9` | `all` | size = binder count; binders, then codomain |
| `0xA` | `letE` | size = `nonDep` (0/1); type, value, body |
| `0xB` | `share` | size = sharing-table index |

Application, lambda, and forall counts must be nonzero. Their runs are
maximal: an application base may not be `app`, a lambda body after the encoded
telescope may not be `lam`, and likewise for `all`.

A lambda binder is `[uses:u8][domain:Expr]`. A forall binder is
`[mode:u8][domain:Expr]`, where:

```
mode = uses | (owned << 2)
```

`Uses` values are `erased=0`, `linear=1`, `affine=2`, `many=3`.
`Owned` values are `unique=0`, `shared=1`. Lambda bytes above 3 and forall
bytes above 7 are invalid.

`Expr.canonicalLaw` proves that every byte string accepted as an expression is
exactly the result of canonically re-encoding that expression. The converse
`Expr.roundtripLaw` assumes `Expr.wireWF`: recursively, every `ref`/`recur`
universe-argument count and every flattened `app`/`lam`/`all` run fits a
`UInt64`. This condition is necessary because Lean arrays and inductive
spines are mathematically unbounded, while the wire stores their counts as
u64. It imposes no additional syntactic restriction beyond representability.

## Constants

`ConstantInfo` starts with `Tag4`:

- flag `0xC`: a mutual block; size is the `MutConst` count;
- flag `0xD`: one constant; size selects `defn=0`, `recr=1`, `axio=2`,
  `quot=3`, `cPrj=4`, `rPrj=5`, `iPrj=6`, or `dPrj=7`.

A complete `Constant` is:

1. `ConstantInfo`;
2. sharing count + expressions;
3. reference count + 32-byte addresses;
4. universe count + universes.

After parsing the sharing table, the decoder enforces its layer-1 semantic
invariant:

- every body `.share` is in bounds;
- entry `i` references only entries `< i`;
- no entry is a bare `.share` alias;
- every entry is used at least twice across later entries and all embedded
  constant bodies.

Accepted tables are therefore finite DAGs and cannot mint addresses through
cycles, aliases, dead entries, or single-use entries. This is not yet exact
compressor-image canonicality: two different profitable DAGs may still inline
to the same bodies. The semantic address boundary therefore runs the layer-2
compressor and requires an exact body/table recompression fixpoint; this
expensive check deliberately remains outside byte decoding.
`shareFree_inlineExpr_of_layer1` proves that inlining any accepted embedded
body eliminates every `.share`; `inlineBodies_shareFree` packages that result
for a complete constant.

Nested payloads are:

- `Definition`: packed `(kind << 2) | safety`, level count, type, value.
  Kinds are `defn=0`, `opaq=1`, `thm=2`; safety is `unsafe=0`, `safe=1`,
  `partial=2`. All other packed bytes are rejected.
- `Recursor`: packed booleans `k | (isUnsafe << 1)`, then levels, params,
  indices, motives, minors, type, and counted rules. A rule is field count +
  RHS expression.
- `Axiom`: canonical boolean, levels, type.
- `Quotient`: kind byte (`type=0`, `ctor=1`, `lift=2`, `ind=3`), levels,
  type.
- `Constructor`: canonical unsafe boolean, levels, constructor index,
  params, fields, type.
- `Inductive`: canonical unsafe boolean, levels, params, indices, type, and
  counted constructors.
- A projection stores its member index (and constructor index for `cPrj`)
  followed by its 32-byte block address.
- `MutConst` has a one-byte tag: definition 0, inductive 1, recursor 2.

`ConstantInfo.wireWF` recursively requires every embedded expression and
every counted rule, constructor, or mutual-member array to fit the wire's u64
counts. `Constant.wireWF` extends this to the sharing, reference, and universe
tables. `ConstantInfo.roundtripLaw` proves roundtrip under the former;
`Constant.roundtripLaw` proves it under `Constant.wireWF` together with
`Constant.sharingWF = true`. Both `ConstantInfo.canonicalLaw` and
`Constant.canonicalLaw` are unconditional over every byte string their strict
decoders accept.

At the semantic identity boundary, `Constant.InlinedView` records the
non-expression constant shape, fully inlined bodies, refs, and universes.
Exact layer-2 sharing makes this view injective. On `Constant.Addressable`
values (`wireWF` plus canonical sharing),
`Constant.inlinedView_eq_iff_address?_eq` relates view equality to address
equality under an explicit pairwise `Address.Blake3NoCollision` premise; no
global hash-injectivity axiom is assumed.

## Totality and codec laws

The universe and expression writers are structurally recursive, including
their maximal-spine helpers. Their decoders are total functions fueled by
remaining input bytes; every recursive descent first consumes a header byte.
No Ixon codec definition is `partial`.

`RoundtripLaw` and `CanonicalLaw` in `Serialize.lean` are the formal global
obligations. `ser_injective_of_roundtrip` proves that the former entails
injective serialization; `accepted_bytes_unique_of_canonical` states the
one-spelling consequence of the latter. `PutSpec` and `GetSpec` provide the
cursor-relative, prefix/suffix-preserving layer used to compose those proofs.
The fixed-width `Address` codec has proofs of both global laws in
`Address.roundtripLaw` and `Address.canonicalLaw`; universe levels have both in
`Univ.roundtripLaw` and `Univ.canonicalLaw`. Expressions have the global
`Expr.canonicalLaw`; their custom `Expr.RoundtripLaw`, proved by
`Expr.roundtripLaw`, is restricted to `Expr.wireWF` because the mathematical
source type can exceed the wire's u64 count range. `ConstantInfo` has the same
shape of conditional roundtrip theorem and a global canonicality theorem. Raw
`Constant` intentionally remains able to represent malformed tables for
encoder→decoder rejection fixtures, so `Constant.RoundtripLaw` requires both
`Constant.wireWF` and `Constant.sharingWF`; `Constant.canonicalLaw` remains
global because successful decoding itself establishes those restrictions.
