# Ixon v2 sharing policy freeze

Status: frozen as `compilatrix/ixon-v2-sharing/1`. The provenance baseline is
ix revision `c98bb74106017e518c705b2567f022e89f732393`; the frozen transcript has
BLAKE3 fingerprint
`8c712eab0db958befe94bda3a40998debe172243dd5771f62d0cd915074f5097`.
Last reviewed 2026-08-14.

This is a compressor-policy regression identifier, not a constant address and
not a claim that v1 and v2 bytes are interchangeable. Ixon v2 adds binder mode
bytes and deliberately strengthens the compressor with structural keys,
maximal-telescope safety, and an exact serialized-byte deletion audit.

## Baseline and vectors

The pinned ix sharing suite runs 46 assertions. Six cases each compare the
Lean and Rust sharing count and complete rewritten body/table vectors. The
same six inputs are translated mechanically into Compilatrix's Lean fragment:
every `lam` receives `Uses.many`, and every `all` receives
`Uses.many`/`Owned.shared`.

[`Tests.lean`](../Tests.lean) records both the translated ix output and the
required v2 output as exact `Compression` values:

| Case | ix table | v2 table | Classification |
| --- | ---: | ---: | --- |
| `simple` | 1 | 1 | exact after mode annotation |
| `content-hash` | 1 | 1 | exact after mode annotation |
| `recursor` | 0 | 0 | exact after mode annotation |
| `forall-imp-sharing` | 2 | 2 | exact after mode annotation |
| `forall-imp-real` | 8 | 5 | intentional v2 delta: exact audit removes three stale nested entries; surviving mode-bearing representatives use v2 order |
| `flip` | 2 | 1 | intentional v2 delta: the inner `all` is a non-maximal suffix, so sharing it would split the canonical telescope |

Every runtime case checks exact raw output, checked-compressor agreement (so
the certified identity fallback cannot hide a policy regression), ix and v2
inline recovery, the declared parity/delta relation, layer 1, exact deletion
optimality, the stronger all-entries-pay diagnostic, and layer-2
recompression canonicality.

The fingerprint transcript is canonical binary data in fixed case order. It
contains a one-byte parity/delta classification followed by framed input
expressions, the pinned ix bodies/table, and the required v2 bodies/table for
each case. Names are descriptive and are not hashed. All expressions use the
real v2 serializer.

## Reproduction

Against a clean checkout of the pinned ix revision, run:

```sh
scripts/check_ix_sharing_baseline.sh /path/to/ix
nix build .#checks.x86_64-linux.tests --print-build-logs
```

The first command verifies the revision and the cleanliness of ix's sharing
sources, builds its `test-ffi` feature, and creates an isolated Lean 4.31
runner. It executes the upstream Lean/Rust suite without the unrelated
`Tests.Main` environment-body fixture and prints the six exact ix vectors.
Only ignored build artifacts are touched in the ix checkout. The second
command checks the transcribed vectors, intended v2 deltas, and fingerprint
under Compilatrix's pinned toolchain.

## Change protocol

Any intentional policy change must update all of the following in one review:

1. `Sharing.compressorPolicyId`;
2. the exact ix/v2 vectors and relation labels in `Tests.lean`;
3. the transcript fingerprint above and in `Tests.lean`;
4. this delta table and the canonical-sharing design note;
5. downstream constant-address fixtures affected by recompression.

An upstream ix revision change additionally requires rerunning the isolated
Lean/Rust gate and reviewing the pinned ix sharing, codec, and FFI source set
enforced by the script.
