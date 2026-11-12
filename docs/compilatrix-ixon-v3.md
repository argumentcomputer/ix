# Compilatrix handoff: Ixon v4

This package describes the Ix producer and its checked fragment. Compilatrix
has not been changed or tested by this work. Consume the versioned data and
validation interfaces below before enabling ownership or locality optimizations.
(The file name keeps the v3 suffix from the handoff that introduced the
contract model.)

## Breaking format

- **Environment format: 4.** The `.ixe` header byte is `0xE4`, and the
  protocol identity is **`ixon-v4`**. Version-3 files and objects are
  rejected.
- **One integer code, TagN.** TagN replaces Tag0, Tag2 and Tag4 everywhere
  ([Ixon](Ixon.md#integer-encoding-tagn)). Values below 128, 32 or 8 (for
  flag widths 0, 2 or 4) encode to the same single byte as in v3. Larger
  values encode differently, for example `Share(8)` = `B8 00`. TagN is
  bijective, so readers do not perform a non-minimal-integer check.
- **Canonical sharing.** The sharing table and every `Share` occurrence are
  part of the canonical bytes, built by the two-phase construction
  ([Ixon](Ixon.md#sharing-system)). A consumer that re-encodes a constant
  must use the same construction to reproduce its address.
- **Contracts are unchanged from v3.** Twelve expression variants and the
  existing declaration headers remain. Lambda binder contracts use four
  bits, and forall input/result contracts use six. Let header values (flag
  `0xA`) encode `nonDep` in bit 0 and `borrowShared` in bit 1. A binder byte
  precedes its type, initializer, and body.
- **Catalogs.** Catalog manifests use version **2**, with object-format byte
  `4` and validator byte `1` after the flags. They describe erased-typing
  claims.
- **Claims and proofs.** Their payloads include format and validator bytes
  after the header. The Catalog and Resource claim headers are `E8 00` and
  `E8 01`.
- **Primitive addresses** have changed. Do not reuse v3 pins or infer an
  object's version from raw constant bytes.

See the [schema](Ixon-v4.md), [wire format](Ixon.md),
[text syntax](ixon-text-v3.md), and [source frontend](source-contracts.md).

## Validation contract

The resource-v1 validator and its claims are retired: `ix compile` runs the
uncertified mode checker (`Ix.ModeCheck.checkArtifact`, see
[resource checking](resource-checking.md)) on annotated source, and no claim
carries its verdict. Optional metadata and cached materializations grant no
semantic facts.

| Interface | Status |
| --- | --- |
| Lean/Rust codecs, equality, hashing, sharing, FFI, text | V4 (TagN, canonical sharing); text grammar version 3 |
| Lean source compilation | Mode-checked annotated definitions (uncertified checker) |
| Decompilation | Reconstructs committed contracts; unsupported metadata rewrites reject |
| Resource claims | Retired (resource-v1) |
| IxVM codecs and structural revelation | Read and write v4 (TagN); preserve every contract field |
| IxVM Check/CheckEnv | Erased-lean-v1; contracts do not strengthen that statement |
| IxVM Resource proofs | Explicitly unsupported |
| Compilatrix backend | External migration required; support not inferred from these fixtures |

Annotated inductive/constructor/recursor generation and nonidentity compiler
surgery reject before emission. The native projection fragment requires closed,
transparent fields with many usage. See [resource checking](resource-checking.md)
for the mode model and the checker.

## Fixture package

The [fixture directory](../Tests/Fixtures/ixon-v4/) contains:

| File | Purpose |
| --- | --- |
| `expressions.txt` | Independently authored canonical expression bytes and addresses |
| `text.tsv` | All binder/arrow modes and both let kinds |
| `claims.tsv` | Claim bytes and BLAKE3 digests for every variant |
| `primitives.tsv` | Regenerated v4 primitive identities |

Run `lake exe ixon-v4-tests` from the repository root for codec, FFI, source,
decompiler, catalog, and VM checks. The generated file `claims.tsv` must equal
its producer's output byte for byte. Scratch files live in `$IX_IXON_V4_DIR`
(default `/tmp`; set it when two checkouts run these executables at the same
time). `lake exe ixon-v4-primitives` writes the primitive closure there
(`ixon-v4-primitives.ixe`) and fails if `primitives.tsv` differs from the live
addresses; `ixon-v4-tests --primitives` then validates that closure.
`--export-fixtures` writes `claims.tsv` to `ixon-v4-fixtures/` in the scratch
directory; copy it into the fixture directory only after validation.

The formal gates are `lake -d IxC build --wfail` (the Ixon codec contracts
under `IxC/Ixon/Verify`, including the TagN laws, with their audit
`IxC/Ixon/Audit.lean`) and `lake build --wfail IxSharingVerify` (the
canonical sharing construction, `IxSharingVerify`, with its audit). The mode
checker is uncertified.
