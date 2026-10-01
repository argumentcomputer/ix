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

<!-- PENDING: [format][ids][route] every item above depends on the format switch, the identifier bump and the compiler routing (plan §0b-2, §2, §3). At 93e2895c the producer writes TagN integers under version 3 and v3 identifiers, with heuristic sharing. -->

See the [schema](Ixon-v4.md), [wire format](Ixon.md),
[text syntax](ixon-text-v3.md), and [source frontend](source-contracts.md).

## Validation contract

`Ix.Resource.validate` and Rust `ix_kernel::resource::validate` check canonical
addressed bytes, reference closure, resource rules, and erased Lean typing.
`makeClaim` and `checkClaim` additionally bind the complete constant-set root
and the canonical profile address. Profile identity includes assumptions,
shareable representations, selection behavior, literal pins, and checker limits.
Optional metadata and cached materializations grant no semantic facts.

| Interface | Status |
| --- | --- |
| Lean/Rust codecs, equality, hashing, sharing, FFI, text | V4 (TagN, canonical sharing); text grammar version 3 |
| Lean/Rust source compilation | Resource-checked annotated definitions and admitted interfaces |
| Decompilation | Reconstructs committed contracts; unsupported metadata rewrites reject |
| Native resource admission and Resource claims | Implemented with explicit profiles |
| IxVM codecs and structural revelation | Read and write v4 (TagN); preserve every contract field |
| IxVM Check/CheckEnv | Erased-lean-v1; contracts do not strengthen that statement |
| IxVM Resource proofs | Explicitly unsupported |
| Compilatrix backend | External migration required; support not inferred from these fixtures |

Annotated inductive/constructor/recursor generation and nonidentity compiler
surgery reject before emission. The native projection fragment requires closed,
transparent fields with many usage. See [resource checking](resource-checking.md)
for higher-order capture, recursion, loan, and normalization limits.

## Fixture package

<!-- PENDING: [ixvm] the IxVM codec update (plan §5); the interface table above states the target. -->

<!-- PENDING: [fixtures] the package is regenerated for v4 through its producers, never relabelled: the directory becomes Tests/Fixtures/ixon-v4/, `ixon-v3-tests` / `ixon-v3-primitives` are renamed or retargeted, and the /tmp paths below change with them (plan §5, §6). At 9611c3b6 the directory holds the v3 package. Update every path in this section when that lands. -->

The [fixture directory](../Tests/Fixtures/ixon-v3/) contains:

| File | Purpose |
| --- | --- |
| `expressions.txt` | Independently authored canonical expression bytes and addresses |
| `text.tsv` | All binder/arrow modes and both let kinds |
| `resource.tsv` | Accepted and rejected resource programs |
| `addressed.tsv` | Addressed declarations and a canonical profile |
| `claims.tsv` | Claim bytes and BLAKE3 digests for every variant |
| `primitives.tsv` | Regenerated v4 primitive identities |
| `handoff/accepted.ixe` | Complete anonymous closure with a linear local identity |
| `handoff/rejected-local-escape.ixe` | Type-correct closure whose local input escapes |
| `handoff/profile.bin` | Canonical resource profile with no external assumptions |
| `handoff/accepted.claim` | Native resource claim for the accepted closure |
| `handoff/manifest.json` | Exact file hashes and subject/profile/claim identities |

Both binary environments must decode and pass erased typing. Resource admission
must accept the first and reject the second. Changing any committed contract,
subject, or profile must invalidate the associated identity. Reading the claim
is not validation, and its bytes are not an IxVM resource proof.

Run `lake exe ixon-v3-tests` from the repository root for codec, FFI, source,
resource, decompiler, catalog, and VM checks. `--primitives` additionally checks
the generated primitive closure at `/tmp/ixon-v3-primitives.ixe`.
`--export-handoff` writes the deterministic handoff files under
`/tmp/ixon-v3-handoff`; copy them into the fixture directory only after validation.

The formal gates are `lake build IxCompileVerify IxTcVerify Ix.Resource.Audit`.
Resource theorems cover the executed quantitative and state-transition
invariants. They do not constitute a verified allocation backend or a proof of
the entire resource checker against a machine operational semantics.
