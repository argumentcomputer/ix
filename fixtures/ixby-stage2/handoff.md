# Fixed Stage 2 guest configuration for the Init benchmark

Use the current grouped native benchmark target, not the runtime-generated
keys in a test wrapper. This is an implementation/benchmark target, **not a
claim of completed production-security approval**.

The existing immutable input files are in the original checkout:

| `AggregateConfig` field | Value |
| --- | --- |
| `ixvmKey` | Raw bytes of `/home/jcb/projects/00/ix/Tests/Fixtures/Aggregate/singleton-grouped-2026-09-09/ixvm.vk` |
| `verifyClaimEntry` | `Ix.Ixby.Goldilocks.reduce 755` (`verify_claim`) |
| `aggregateKey` | Raw bytes of `/home/jcb/projects/00/ix/Tests/Fixtures/Aggregate/singleton-grouped-2026-09-09/aggr.vk` |
| `aggregateEntry` | `Ix.Ixby.Goldilocks.reduce 243` (`ix_aggr`) |

Input byte pins:

- `ixvm.vk`: 744159 bytes; BLAKE3 `3983867e9f70a82d990ea65e15265da105617317b95b4b1482e7a7b854ca8063`.
- `aggr.vk`: 181630 bytes; BLAKE3 `75452941bc0dbe4a861c88c792067f34d7864f0460f305858a0a004ec409406e`.
- Allowed identity: 80 bytes; BLAKE3 `224668baa32c9e827a1751513d8976836f6e3d9aba3f1b3cca5c9cbd1b7ff19b`.

The identity preimage is exactly
`BLAKE3(ixvm.vk) || u64le(755) || BLAKE3(aggr.vk) || u64le(243)`.
The authoritative target record is
`/home/jcb/projects/00/ix/flock-stage3/CURRENT-GROUPED-TARGET.json`.
The fixture was reverified in a fresh native process on 2026-09-13, including
all recorded byte digests, equality to both generated native keys, and both
native proofs. The root/claim in that singleton fixture is **not** the Init
claim: only the value-independent keys and entrypoints are reused.

## Guest definition

Import `Ix.MultiStark.Verify.Source` from this worktree. Generate
`frozenIxvmKey : Array UInt8` and `frozenAggregateKey : Array UInt8` as checked
constant data from the raw files **at build time**. They are not guest inputs,
and loading or generating them must not remain in the runtime dependency
closure. The following definition then has exactly two runtime arguments:

```lean
open MultiStark.Verify

def initBenchmarkSourceConfig : SourceConfig := {
  aggregate := {
    ixvmKey := frozenIxvmKey
    verifyClaimEntry := Ix.Ixby.Goldilocks.reduce 755
    aggregateKey := frozenAggregateKey
    aggregateEntry := Ix.Ixby.Goldilocks.reduce 243
  }
  decode := {
    bytes := 16777216
    vector := 1048576
    items := 2097152
  }
  verifier := {
    queries := 1024
    foldArity := 256
    transcript := {
      observationBytes := 16777216
      sampleAttempts := 64
    }
  }
}

def initStage2Guest (publicClaim proofBytes : Bytes) : Option Bytes :=
  claimBytesWrapper initBenchmarkSourceConfig publicClaim proofBytes
```

These explicit parser/verifier resource limits are the current source
defaults, not the cryptographic protocol parameters. The pinned native keys
encode 100 queries, log blowup 2, cap height 0, binary FRI, constant final
polynomial, no commit grinding, and 20 query-grinding bits. Keep function
grouping enabled and the default aggregate lookup policy; do not substitute
the ungrouped or experimental minimum-opening-width fixtures.

`publicClaim` is canonical `CheckEnv(root, none)` transport (34 bytes);
`proofBytes` is the raw native multiproof, **not** the enclosing `Ixon.Proof`
wrapper or expanded prover advice. Success returns exactly `some publicClaim`;
failure returns `none`. The Init root remains a public runtime input. Use the
explicit Option/byte ABI when lowering; do not assume Lean's constructor
layout is the Flock output ABI.

The compiled result must pin both key byte strings, all configuration values,
the full source/callee closure, target program/profile, and input/output ABI.
Report lowering/admission and source-image certification separately: an
example-input execution agreement is not an all-input compiler-refinement
certificate. If the completed Init root exceeds these fixed resource bounds,
reject it and version the configuration explicitly rather than silently
increasing the limits or making them runtime parameters.
