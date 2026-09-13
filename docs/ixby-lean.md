# Experimental typed Lean frontend

`Compilatrix.Ixby.LeanFrontend.compile` lowers retained pure monomorphic LCNF
declarations to an ordinary `Ix.Ixby.Program`. Lean's compiler performs typed
proof erasure and specialization before this entry point. The resulting image
passes the unchanged reference machine's whole-program validator. Unknown
runtime externs are rejected.
Packed byte capacity must be below 2³², matching the target byte-index ABI.

This frontend has no source-refinement certificate. It is separate from the
checked anonymous Ixon pipeline and cannot produce an `IxonCompilation`.
Compiling the retained Lean source does not establish correspondence with the
original anonymous Ixon source address. Constructor identities are local
layout identifiers, not authenticated source declaration digests.

## Runtime representations

Naturals retain their exact mathematical value. An optional low Word32 cache
supports byte indexing and word operations; it does not replace Nat arithmetic.
Division and remainder produce uncached values, which arithmetic propagates
without converting them. Byte and word operations compute the cache when needed.
Tests include values beyond 64 bits, truncated Nat subtraction,
division and remainder by zero, and UInt8/UInt32 wraparound and shift counts.
Conversion between representations consumes four bits at a time through
comparisons with literals, using only ordinary reference instructions.
The USize lowering uses 64-bit source semantics.

Ordinary immutable arrays use binary trees. Byte inputs use packed scalar
bytes, and concatenations use balanced trees of byte blocks. Polymorphic
updates first widen packed storage to ordinary values, so mapping bytes to
larger naturals, constructors, or closures preserves their representations.
Calls, partial applications, lifted joins, constructors, case analysis, and
tail calls use the corresponding reference instructions.

The optional Stage2 wire lowering emits reference instructions for the pinned
little-endian helpers, single-byte writer, and specialized canonical byte
comparison. The original writer still checks its byte limit. General array
comparison callbacks are not replaced. BLAKE3 lowers to the reference BLAKE3
primitive. No host invocation of the Stage2 source verifier supplies an Ixby
execution result.
Goldilocks arithmetic currently uses the exact Nat primitives in the emitted
image.

The current cryptographic profile and canonical codec reject Nat values and
Nat instructions. Consequently this image currently runs under the reference
limits and cannot be exported with that profile. The Nat/profile extension is
an upstream task. This is distinct from the source-refinement obligation.
The current image needs canonical support for `Scalar.nat` and the seven
primitives `natAdd`, `natSub`, `natMul`, `natDiv`, `natMod`, `natEq`, and `natLt`.
Their arithmetic must retain the reference semantics, including truncated
subtraction, division by zero, and the explicit Nat bit capacity.

## Tests and Stage2 adapter

```sh
lake exe check-ixby-lean
lake exe stage2-ixby fixtures/ixby-stage2 compile /tmp/stage2-inventory.json
lake exe stage2-ixby fixtures/ixby-stage2 valid
nix build .#checks.x86_64-linux.ixby-lean
```

Run these executables through Lake so they can load the retained compiler
declarations. Direct binary invocation requires the equivalent `LEAN_PATH`.

The focused suite compares 1,945 actual reference executions with independently
executed Lean source results. It covers arithmetic, proof-bearing Fin values,
closures, arrays, byte-block balancing and mutation, wire limits, exact byte
outputs, canonical comparison, and a 10,000-iteration tail call under an
eight-continuation limit.

`stage2-ixby` compiles the unchanged retained `claimBytesWrapper` and an explicit
adapter containing both original fixed keys, entrypoints 755/243, and the
original source configuration. Only two raw scalar byte arrays enter the
image: the public claim and private proof. The adapter returns raw claim bytes
on `some` and erased on `none`. The host checks fixture identities and
decompresses the retained test proof before execution.

The runner accepts `valid`, `claim-mismatch`, `empty-proof`, `truncated-proof`,
`trailing-public`, `trailing-proof`, `wrong-claim-kind`, and `malformed-proof`.
Each case executes the compiled program and compares its actual result with
the expected raw bytes or erased value. A step-limit failure is a failed test.
All eight cases passed on the compiled reference image:

| Case | Actual result | Reference transitions |
| --- | --- | ---: |
| Valid proof | Exact 34-byte claim | 5,774,758,723 |
| Changed claim root | Erased | 2,076,855,592 |
| Empty proof | Erased | 122,254,401 |
| Truncated proof | Erased | 673,177,152 |
| Trailing public byte | Erased | 247 |
| Trailing proof byte | Erased | 673,197,277 |
| Wrong claim kind | Erased | 390 |
| Malformed proof | Erased | 122,254,420 |

The [retained inventory](../fixtures/ixby-stage2/reference-inventory.json)
contains 675 functions, 6,677 blocks, 146 constructor layouts, and entry 674.
Independent fresh compilations reproduced it byte for byte. The Nix gate
compares that inventory, runs the focused suite, and replays the valid proof
plus the empty, malformed, trailing-public, and wrong-kind cases.

The optional compile report records all emitted functions, constructor layouts,
instructions, primitives, and static frame maxima. It is an inventory of the
in-memory image, not a substitute for the pending canonical program encoding.

Long runs pause between batches of one million reference transitions.
`Runtime.runChunk_run` proves that a chunk followed by the remaining reference
execution equals the upstream evaluator with their combined fuel. This proves
the runner's chunking equation, not the compiler's source correspondence.
Runtime limits are explicit reference capacities; they are not measured Flock
resource requirements or evidence of executor soundness.
