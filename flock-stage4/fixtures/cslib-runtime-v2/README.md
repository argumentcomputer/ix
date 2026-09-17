# Compiled CSLib Stage 2 verifier, runtime revision 2

Copied unchanged on 2026-09-17 from Compilatrix's
`plans/ixby-runtime-v2/handoff/cslib`, with compiler checkout HEAD
`191b2a9e8baf46e736ce4de6746b6b2a6374b673`. These are the actual newly compiled
artifacts, using format 1 and semantics 2. The program contains 672 functions
and 5,816 blocks, with source entry `MultiStark.Verify.claimBytesWrapper`.

| File | Bytes |
| --- | ---: |
| [program.ixby](program.ixby) | 1,005,374 |
| [input.ixbi](input.ixbi) | 4,813,238 |
| [output.ixbo](output.ixbo) | 49 |
| [profile.ixfp](profile.ixfp) | 184 |
| [expected.statement](expected.statement) | 32 |

Program SHA256:

```text
7cdc4a7000011a2d9a18324b5d127bcdb13bc3842100fb4b69355ea162c133b5
```

Expected statement `S`:

```text
606c7970ae81d1773249b6652dd1a31b685ea2b0d54fc73bd4fd786ae808caeb
```

All five file lengths, SHA256 values, and BLAKE3 values matched the
[compiler integration record](../../../flock-stage3/profile/cslib-runtime-v2/compiler-integration.json).
IxBy's native CLI independently decoded the program to reproduce the exact
profile and computed the same statement. A separate `b3sum` calculation checked
every domain-separated P/B/I/O/S commitment.

The compiler's complete reference observer reports **360,337,913 logical
transitions** and exact agreement with the independent expected output.
The imported observer took 72.61 seconds. This is reference execution evidence;
no complete CSLib Flock proof is included. IxBy additionally ran the first
200,000 native microsteps for physical batch occupancy measurements.

See the [retained evidence and reproduction commands](../../../flock-stage3/profile/cslib-runtime-v2/README.md)
and [ranked optimization opportunities](../../../docs/IxbyPerformance.md).
