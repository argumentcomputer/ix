# Single-dispatch array reads

`Array.getInternal` dispatches once on native arrays, packed bytes, or writer
buffers, then checks the length and reads the element. Removing the nested
`Array.size` call and second dispatch saves four logical transitions per
successful read. The retained CSLib execution drops from **299,248,427 to
276,667,563 transitions**, a reduction of **22,580,864 (7.55%)**, with identical
49-byte output. Together with [leaf-call inlining](ixby-inline.md), this is
23.22% below the 360,337,913-transition runtime revision 2 baseline.

These measurements describe the array-read change at revision `e048fa0`.
The subsequent [FRI fusion](ixby-fri-fusion.md) preserves these helper bodies
and contracts while further reducing both Stage2 workloads.

## Behavior and certification

The [emitter](../Compilatrix/Ixby/Runtime/Array.lean) keeps full Nat bounds
checks before Word32 byte addressing. Packed views retain their stored length,
including its existing validation behavior. Writer buffers validate their
length before the index and freeze only after the bounds check succeeds.
Out-of-range reads retain the existing trap.

The certificate checks the complete new
[function body](../Compilatrix/Ixby/Runtime/Native/Code/Array.lean), including
all branches and dead code. The existing `arrayGet_returns` and
`packedGet_returns` contracts retain their names and premises. Stronger
contracts prove reads with arbitrary caller continuations and no spare stack
slot. [Additional kernel proofs](../Compilatrix/Ixby/Runtime/Native/ArrayRead.lean)
cover writer results, out-of-range indices, malformed packed payloads behind
an out-of-range stored bound, and writer length errors before index validation.

| Successful helper entry through halt | Previous transitions | Current transitions | Previous / current locals |
| --- | ---: | ---: | ---: |
| Native array | 11 | 7 | 8 / 8 |
| Packed bytes | 11 | 7 | 10 / 9 |
| Writer buffer | 13 | 9 | 11 / 10 |

The removed call also removes one temporary continuation reservation. Fuel,
local-capacity and continuation exhaustion therefore need not coincide with
the previous implementation. Exact boundary tests cover the reduced costs.
Other semantic limits are unchanged. Whole-program maximum locals remain 66.

This change updates the certified runtime implementation and reproves its
helper contracts. The inliner's whole-image theorem still certifies its own
separate pass with the new runtime prefix protected; it does not prove an
old-runtime to new-runtime transformation. General typed LCNF source
refinement and complete CSLib native proving remain open. Seven new exact
[axiom fences](../CompilatrixTests/Fences/IxbyArrayRead.lean) use only ordinary
Lean logic, preserving all 2,760 prior assertions and all 107 runtime/wire
body checks. No reference primitive, ABI, or native interface changes.

## Measurements and validation

| Retained workload | Inlined baseline | Single dispatch | Saved |
| --- | ---: | ---: | ---: |
| CSLib | 299,248,427 | 276,667,563 | 22,580,864 |
| Stage2 valid | 593,867,713 | 544,834,777 | 49,032,936 |

These are reference-machine transition counts, not wall-time or native prover
speedups. Each newly compiled image differs from its baseline only at function
62. The binaries grow by 39 bytes and six blocks: Stage2 is 991,082 bytes and
CSLib is 1,005,314 bytes. Both have 672 functions and 5,822 blocks.
Artifact identities, case counts and proof scope are recorded in
[array-read.json](../fixtures/ixby-stage2/array-read.json).

The focused gate retains 40,839 source-oracle helper cases, 900 bounds
rejections, and caller checks for all 107 helpers. It rejects 2,258 certificate
mutations, including 1,416 structurally admitted images. It adds 22,680
comparisons with the previous complete helper body using both reference and
chunked evaluators, including invalid payloads, stored lengths, large indices,
and scalar/byte limits. The suite checks 90 local resource boundaries and 501
exact transition formulas, each with a one-less-fuel rejection. Both baseline
and inlined typed-source suites retain 4,585 comparisons. All eight Stage2
serialized execution cases remain required.

```sh
lake exe check-ixby-lean
lake build CompilatrixTests.Proofs
lake exe stage2-ixby fixtures/ixby-stage2 compile /tmp/stage2.ixby
lake exe stage2-ixby fixtures/ixby-stage2 valid /tmp/stage2.ixby
nix build .#checks.x86_64-linux.ixby-lean
nix flake check
```

`compile-baseline` disables ordinary leaf-call inlining while retaining the
current single-dispatch runtime. The earlier
[inlining record](../fixtures/ixby-stage2/inlining.json) and
[runtime revision 2 record](ixby-runtime-v2.md) remain historical measurements.
