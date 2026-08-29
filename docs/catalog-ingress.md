# ix catalog ingress

Last reviewed 2026-08-25.

`Compilatrix/Ixon/Catalog.lean` is the corpus boundary between ix-exported
artifacts and the checked compiler pipeline. It consumes bytes rather than
performing filesystem I/O:

```lean
Catalog.loadWith limits manifestBytes pieceBytes
Catalog.load manifestBytes pieceBytes
```

`Compilatrix/Ixon/CatalogIO.lean` is the bounded on-disk adapter:

```lean
CatalogIO.loadDirWith limits directory
CatalogIO.loadDir directory
```

It reads an exact self-contained `.ixc` directory, then delegates all semantic
validation to the pure loader. The standalone contact harness runs that path
and the checked program pipeline:

```sh
lake exe catalog-contact -- path/to/catalog.ixc
```

The positional `pieceBytes` array mirrors the files in a self-contained `.ixc`
directory. For the fat profile, entry `i` is `<members[i].label>.ixe`. For the
chunked profile, entry `i` is
`<members[chunks[i].owner].label>.chunk<i>.ixe`. Labels are validated as bare
filename stems before a caller needs to resolve them: empty labels, `.`, `..`,
NUL, `/`, and `\` are rejected.

On success, `Loaded.constants` is the sorted, deduplicated
`List (Address × Constant)` accepted directly by `Pipeline`; `Loaded.blobs`
is the corresponding sorted raw-byte blob union. Blob interpretation remains
an evaluator configuration decision. `Loaded.stats` records the exact
aggregate ingress charges.

## Manifest v1

The parser mirrors ix's `.ixc/manifest` framing:

```text
"IXC\0\0\0\0\0"
version:u32le = 1
flags:u32le                 bit 0 = chunked; every other bit rejected
members_root:Address
content_root:Address
member_count:u32le
member[member_count]
storage
future_trailing_bytes
```

Each member carries `env_root`, `const_count`, three u16-length-prefixed UTF-8
strings (`label`, `toolchain`, `source_pin`), u32 dependencies, and an optional
preimage address. Dependencies must point strictly backward, so manifest order
is topological. This ingress is stricter than ix's current catch-all preimage
reader: only option tags 0 and 1 are accepted.

A fat storage section has exactly one `(file_hash, file_bytes)` row per
member. A chunked section starts with a u32 row count; every row carries
`(chunk_root, file_hash, file_bytes, owner)`, with the owner in range. Bytes
after storage are retained verbatim for forward compatibility. The parser
always recomputes `members_root`, including ix's canonical-set behavior when
member roots repeat.

All fixed-width integers are little-endian. Addresses are 32 bytes. Strings
cannot exceed the u16 framing bound.

## Anonymous `.ixe` boundary

Each storage unit is parsed through the same anonymous semantic prefix used
by ix's `get_anon` reader:

1. `Tag4(flag=0xE, version=2)`, stored environment root, optional `main`, and
   strictly ascending assumptions;
2. content-addressed blobs;
3. strictly ascending `(address, Tag0-length-prefixed constant bytes)` rows;
4. delta-coded anonymous hints.

Sections 4–6 (names, named metadata, and comments) occur after this prefix.
Compilatrix is nameless and never consults them, so it retains that tail as
opaque `Piece.metadata` instead of parsing it. The manifest file hash still
binds every tail byte. Truncation inside the semantic prefix is rejected;
syntax inside an unused metadata tail is deliberately outside this boundary.

Blob payloads must hash to their stored addresses. Every constant payload
must first hash to its row address, then pass
`DecodeCheck.decodeIxonV2CheckedWith`, then pass
`Constant.addressIxonV2CheckedWith`. The latter enforces wire
representability, local evaluator bounds, the exact compressor image of the
pinned ix revision, and the same semantic BLAKE3 address. This deliberately
performs more validation than a shallow catalog index.

The external recognizer is intentionally distinct from Compilatrix's local
`decodeCheckedWith` / `addressCheckedWith` policy. Pinned ix can retain a
nested sharing entry with only one direct use after sharing its parent, while
the local policy deletes it and also protects maximal telescope spellings.
Catalog ingress therefore checks the common safety invariant—backward-only,
non-alias sharing with in-bounds body references—and exact upstream
recompression. Arbitrary acyclic DAG spellings are still rejected, and the
stored bytes are hashed without normalization or readdressing. The two policy
identifiers and their parity vectors are recorded in
[`sharing-policy.md`](sharing-policy.md).

Ix also collapses singleton recursive blocks to standalone definitions or
recursors while retaining `.recur 0`. Local validation consequently gives
standalone `.defn` and `.recr` values a singleton self environment; other
standalone constant kinds still have none.

The recomputed canonical Merkle root over the constant addresses must equal
the `.ixe` header root. A declared `main` must occur in that piece. Fat pieces
must have no assumptions: they are self-contained member closures.

## Roots, coverage, and duplicates

The loader verifies all four commitment levels:

- each storage unit's file size and full-file BLAKE3;
- each `.ixe` environment root;
- each manifest member root and count; and
- the catalog `content_root` over the constant-address union.

For fat catalogs, a piece is a member, so its root/count must match the member
row exactly. Overlap between member closures is expected. An identical
address/payload pair is deduplicated in the final union; the same address with
different bytes is rejected as a conflicting content binding.

For chunked catalogs, constants are partitions: any address appearing in two
chunks is a hard error, diagnosed before member coverage checks. Chunks are
then grouped by owner, and each owner's complete address set must reconstruct
that member's root and count. This owner-wise check is stronger than accepting
a catalog which happens to match only the global content root.

Blobs use content-addressed union semantics in both profiles: identical
address/payload pairs deduplicate, while a conflicting payload is rejected.

## Store-wide coherence

`Catalog.validateStore` runs after the complete constant union exists. It
checks invariants unavailable to a one-object decoder:

- every constructor's stored `cidx` equals its array position;
- every `iPrj`, `cPrj`, `rPrj`, and `dPrj` block address resolves;
- the target is a mutual block;
- the member index is in range and has the required kind; and
- a constructor projection's constructor index is in range.

The loader does not require every ordinary expression reference to be present:
assumption/open-boundary policy is separate. It specifically closes the
projection/member channel that would otherwise become evaluator stuckness or
an eraser layout mismatch.

## Aggregate limits

In addition to the per-constant decode/address limits, `Catalog.Limits`
defaults to:

| Counter | Default |
| --- | ---: |
| manifest bytes | 16 MiB |
| members | 4,096 |
| dependency edges | 65,536 |
| storage units | 16,384 |
| aggregate piece bytes | 1 GiB |
| decoded constant entries | 32,768 |
| aggregate constant payload bytes | 1 GiB |
| decoded blob entries | 32,768 |
| aggregate blob payload bytes | 1 GiB |
| assumptions | 65,536 |
| hints | 32,768 |
| stored expression units | 2,097,152 |
| fully expanded body units | 2,097,152 |
| aggregate layer-1 charge | 134,217,728 |
| constants in the deduplicated union | 16,384 |

Work counters include repeated constants in fat member closures because those
bytes are independently decoded and checked. The union limit is separate.
Every count/length is checked before its input-driven loop or allocation, and
every failure carries `Work.Exceeded { metric, actual, limit }`. Compiled
regressions pin exact-limit acceptance and one-below rejection, fat overlap,
chunk duplicates, manifest/piece truncation, file and inner-object hash drift,
projection member bounds, and constructor ordinals. A separate golden vector
freezes the canonical Merkle root from an actual ix-produced 19-member
catalog, including order independence and duplicate-leaf elimination.

This is a bounded in-memory ingress API. Multi-gigabyte streaming/mmap
adapters and chunk-wise certificate scheduling remain future scalability work;
raising the defaults does not make those architectural costs disappear.

## Filesystem boundary and first production contact

`CatalogIO.loadDirWith` parses and bounds the manifest before resolving piece
names. It rejects symlinks and other non-regular inputs, validates each
declared and observed piece size before the full read, enforces the aggregate
piece-byte limit as it goes, then lets `Catalog.loadWith` recheck sizes and all
hashes. A concurrently replaced file can still cause a transient allocation
between metadata inspection and reading; eliminating that TOCTOU allocation
requires the future streaming/mmap adapter, while the pure size/hash gate
still prevents acceptance of changed content.

The first byte-exact production contact is the bounded Std closure under
[`fixtures/ixon-std-contact`](../fixtures/ixon-std-contact). Its provenance,
roots, complete measured counters, upstream Rust-checker result, and current
pipeline outcome are frozen in [`corpus-contact.md`](corpus-contact.md) and
exercised by the compiled `tests` binary.
