# Compilatrix handoff: Ixon v3

This package describes the Ix producer and its checked fragment. Compilatrix
has not been changed or tested by this work. Consume the versioned data and
validation interfaces below before enabling ownership or locality optimizations.

## Breaking format

- Environment format: **3**, protocol identity **`ixon-v3`**.
- Twelve expression variants and the existing declaration headers remain.
- Lambda binder contracts use four bits; forall input/result contracts use six.
- Let Tag4 sizes encode `nonDep` in bit 0 and `borrowShared` in bit 1. A binder
  byte precedes its type, initializer, and body.
- Catalog manifests use version **2**, with object-format byte `3` and validator
  byte `1` after the flags. They describe erased-typing claims.
- Claim and proof payloads include format and validator bytes after Tag4.
- Primitive addresses have changed. Do not reuse v2 pins or infer an object's
  version from raw constant bytes.

See the [schema](Ixon-v3.md), [wire format](Ixon.md),
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
| Lean/Rust codecs, equality, hashing, sharing, FFI, text | V3 |
| Lean/Rust source compilation | Resource-checked annotated definitions and admitted interfaces |
| Decompilation | Reconstructs committed contracts; unsupported metadata rewrites reject |
| Native resource admission and Resource claims | Implemented with explicit profiles |
| IxVM codecs and structural revelation | Preserve every v3 contract field |
| IxVM Check/CheckEnv | Erased-lean-v1; contracts do not strengthen that statement |
| IxVM Resource proofs | Explicitly unsupported |
| Compilatrix backend | External migration required; support not inferred from these fixtures |

Annotated inductive/constructor/recursor generation and nonidentity compiler
surgery reject before emission. The native projection fragment requires closed,
transparent fields with many usage. See [resource checking](resource-checking.md)
for higher-order capture, recursion, loan, and normalization limits.

## Fixture package

The [fixture directory](../Tests/Fixtures/ixon-v3/) contains:

| File | Purpose |
| --- | --- |
| `expressions.txt` | Independently authored canonical expression bytes and addresses |
| `text.tsv` | All binder/arrow modes and both let kinds |
| `resource.tsv` | Accepted and rejected resource programs |
| `addressed.tsv` | Addressed declarations and a canonical profile |
| `claims.tsv` | Claim bytes and BLAKE3 digests for every variant |
| `primitives.tsv` | Regenerated v3 primitive identities |
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
