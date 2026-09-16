# Nat/Word32 integration, program semantics 1

Compilatrix emits the breaking IXBF program revision with direct Nat/Word32
conversions from Ixby revision `d4405b3ceb82e6d4cce19e48186f3272f8482e04`.
The compiler remains on Lean 4.33.0. The [vendor record](../vendor/ixby/upstream.json)
gives every retained file's revision and digest; the experimental crypto
profile/codec files stay at their prior revision.

## Wire and runtime contracts

Programs use format 1, semantics 1. IXFI input and IXFO output remain format 1,
semantics 0. Old program headers are rejected even for old opcodes. The
[complete binary specification](ixby-binary.md) assigns unary opcodes 45 and 46
to `natToWord32` and `word32ToNat`. Nat conversion validates the entire source
before taking its low 32 bits; reverse conversion validates the exact unsigned
Nat result. Arity, scalar limits and types retain their reference error order.

The generated three-argument helpers preserve their names and function indices:

```text
toWord(n, weight, acc)       = acc + n.toUInt32 * weight  // Word32 arithmetic
fromWordLoop(w, weight, acc) = acc + w.toNat * weight     // Nat arithmetic
```

Each body has three primitive instructions, a return block, and six locals.
The nibble helpers remain in the inventory but these bodies no longer call
them. General weights and accumulators remain covered by the execution proofs
and exact-body certificates. Reverse conversion needs its intermediate
`w.toNat` to fit even when the weight is zero, and the weight must fit even
when `w` is zero. Its ordinary `weight = 1, acc = 0` certificate now needs
32 Nat bits instead of the old loop's 33 bits. Existing conservative public
local/continuation bounds remain sufficient; direct helper execution needs no
new continuation frame.

## Regenerated programs and measurements

The retained [Stage2 image](../fixtures/ixby-stage2/stage2.ixby) is 1,002,199
bytes with 681 functions, 6,748 blocks and 146 constructor layouts. Its two
keys and entrypoints 755/243 are unchanged. Required checks reproduce its
bytes and inventory and run the valid proof plus all seven rejection cases.
The [typed frontend record](ixby-lean.md#reproduction-and-tests) gives their
exact transition counts.

A separate CSLib image was recompiled with its retained 751,155-byte IxVM key,
188,866-byte aggregate key, and entrypoints 766/243. Its SHA-256 is
`60db6f5a93e98149042aa5b1622e2f2bf303b5434cc513edfcabfb34299adfb1`
and its length is 1,016,431 bytes. An independent decoded comparison confirms
that only functions 0 (`toWord`, 13 → 4 blocks) and 1 (`fromWordLoop`, 10 → 4)
changed. All 679 other bodies, constructor layouts, limits, entry and function
identities match the prior image.

The full reference observer reproduced the retained CSLib output bytes exactly:

| Measurement | Previous image | Semantics 1 image |
| --- | ---: | ---: |
| Complete reference transitions | 2,268,502,805 | 2,033,412,182 |
| `toWord` block evaluations | 58,111,555 | 12,645,068 |
| `fromWordLoop` block evaluations | 73,176,276 | 4,924,840 |
| `nibbleWord` block evaluations | 39,752,784 | 0 |
| `nibbleNat` block evaluations | 69,482,646 | 0 |

The measured reduction is **235,090,623 transitions (10.36%)**. The helper
rows count block evaluations; complete transitions also include return/apply
control. The new run observed at most 65 Nat bits, 73 locals and 647
continuations, matching the prior maxima. It took 343.50 seconds locally while
other builds and verification ran. This records a logical transition reduction;
it does not establish a wall-clock or proving speedup.

The [machine-readable integration record](../fixtures/ixby-stage2/nat-word32-integration.json)
contains source/artifact digests, the full primitive census, helper counts,
profile bytes and independently recomputed commitments `P`, `B`, `I`, `O`, `S`.
The new CSLib statement is
`6e8b833efbe2c8a04b2a9f053620e8f2e372b9144f91ec8c0a1083b459096496`.
The local export at `plans/ixby-nat-word32/handoff/cslib/` contains the program,
inventory, exact retained input/output, 184-byte profile and expected statement.
The ignored export and detailed observer log are local measurement artifacts;
the digest record is retained in the repository.

## Conversion fixture and validation

The [seven-step fixture](../fixtures/ixby-stage2/conversions-v1/README.md)
converts `2^65 + 37` to Word32 and back, adds five, then emits `[42, 0, 0, 0]`.
Compiler serialization matches the independent upstream generator byte for
byte. A separate IXFP encoding and BLAKE3 calculation reproduces the profile,
all commitments and statement
`ecc83e788c114efa6d11fd2a0621fc3472303b38f5ce1de9953e6be684e62e37`.
A fresh native process accepted the handoff's existing 499,443-byte complete
recursive proof for this statement. Setup took 133.13 seconds and verification
19.04 seconds. The existing prover executable and proof were reused, with
their exact digests recorded; neither was rebuilt or regenerated here.

The focused suites cover all 47 opcodes and reject 47–255, legacy program
headers, wrong value headers, non-unary arity, wrong source types, Nat source
and result limits, and exact I/O bytes. Kernel-checked examples cover zero,
wide-source truncation, source limits and the largest Word32 result. Runtime
cases also cover one, `2^32 - 1`, `2^32`, `2^65 + 37` and the declared 4096-bit
boundary. Weighted helper tests and the complete
number/field/word/array certificates exercise the generated bodies. Required
CI retains all previous proof assertions and adds the two primitive-evaluation
fences, standalone fixture execution and frozen-byte comparisons.

```sh
lake build check-ixby-binary check-ixby-lean CompilatrixTests.Proofs
lake exe check-ixby-binary /tmp/ixby-conversions
lake exe check-ixby-lean
nix build .#checks.x86_64-linux.ixby-lean
```

The reference machine supports arbitrary-size Nats within its declared limit.
The paged prover still restricts physical Nats to immediate Nat128 and requires
at least a 128-bit semantic limit. Small-fixture verification does not establish
a CSLib proof, arbitrary-precision proof arithmetic, or universal refinement
of the typed source frontend. Unboxed numbers, persistent arrays and byte
builders are separate future changes.
