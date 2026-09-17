# Shift-by-one and fixed-width integer writes

The Stage2 runtime now halves directly when a Nat shift count is one, and the
pinned `MultiStark.Verify.Codec.Wire.writeNat` is bound to a certified body
that compares against precomputed bounds for the widths the codecs use. The
repeated-squaring power that previously built `2 ^ (8 * width)` for every
write, and the generic shift loop for every shift by one, are no longer run.

| Workload | Previous transitions | Current transitions | Saved |
| --- | ---: | ---: | ---: |
| Stage2–CSLib | 227,780,761 | 217,047,989 | 10,732,772 (4.71%) |
| Stage2–singleton fixture | 458,512,092 | 441,279,047 | 17,233,045 (3.76%) |

Both runs preserve their exact outputs. Four singleton rejection cases also
become cheaper because they canonicalize the fixed key before rejecting:
changed claim 189,023,757 to 180,235,326; empty and malformed proof
23,553,991 to 19,130,844; truncated proof 122,667,736 to 118,244,589; trailing
proof 122,669,930 to 118,246,783. The two early rejections keep 107 and 58.
These are logical reference-machine counts; native proving and wall-time
improvements are unmeasured. The singleton fixture is a smoke proof, not a
full Init verification claim. The baseline is revision
`c1543bfbcb0b8af98e06bd59c808041622d4b7b7`. Artifact identities and execution
evidence are in [shift-width.json](../fixtures/ixby-stage2/shift-width.json).

## Helper bodies and certificates

The earlier CSLib profile counted 695,401 `Nat.shiftRight` calls, all with
count one, and 95,507 `writeNat` calls, mostly at width 2 from key nodes and
width 8 from vector prefixes. Lean's LCNF constant folder rewrites `n / 2`
into `n >>> 1`, so the shifts come from source divisions as well as explicit
shifts. The [number emitter](../Compilatrix/Ixby/Runtime/Number.lean) now gives
`Nat.shiftRight` (function 21) a compare on the count: one divides by two and
returns; every other count enters the unchanged loop. A nonzero shift by one
costs 5 transitions from entry through halt instead of 12.

The [wire emitter](../Compilatrix/Ixby/Runtime/Wire.lean) installs
`MultiStark.Verify.Codec.Wire.writeNat` (function 111), which compares the
width with 2, 8, 1 and 4 in that order and tail-calls the range helper
`Ixby.Runtime.wireNatRange` (function 110) with the matching literal bound;
any other width still multiplies and calls the certified power loop. The
range helper compares the value with the bound, then either calls the
existing little-endian encoder and tail-calls the existing byte writer, or
returns the source's `integerRange` error. The source order is preserved: the
range check precedes the byte-limit check. The vendored verifier and its
provenance pins remain unchanged.

The [complete body templates](../Compilatrix/Ixby/Runtime/Native/Code/Wire.lean)
are checked against every emitted and decoded Stage2 image. The
[shift contract](../Compilatrix/Ixby/Runtime/Native/NatLoops.lean)
`natShiftRight_returns` is re-proved for the new body with its previous
statement and premises, using `n >>> 1 = n / 2` on the direct path and the
unchanged loop contract otherwise. The [writer proofs](../Compilatrix/Ixby/Runtime/Native/WireNat.lean)
establish:

- `fixed_width_bounds`: the four literal bounds equal `2 ^ (8 * width)`.
- `wireNatRange_rejects` and `wireNatRange_encodes`: below the bound the
  helper reaches the byte writer's entry with the encoder's result and the
  original state, with the encoder call as an explicit path premise; at or
  above it, the helper returns the integer-range error without encoding.
- `writeNat_fixed_reaches_range` and `writeNat_general_reaches_range`: each
  fixed width reaches the helper with its bound, and every other width reaches
  it with the power loop's result under that loop's own premises.
- `writeNat_encodes` and `writeNat_rejects`: the composed source semantics for
  every width.

Rejection costs 6 transitions in the range helper and 9, 11, 13 or 15 through
the writer at widths 2, 8, 1 and 4; the general width adds the power loop.
The shift wrapper needs 4 locals, the writer 9 and the helper 7, plus one
continuation slot for the encoder call. Eight new exact
[axiom fences](../CompilatrixTests/Fences/IxbyWireNat.lean) use only `propext`,
`Classical.choice`, and `Quot.sound`, preserving all 2,781 prior assertions.
The 96 other runtime helpers, the ten earlier wire helpers, the two row-hash
helpers, their public theorem premises, and the inliner's separate
complete-image certificate are unchanged; the inliner now protects the
112-function prefix. The integer-range error layout, previously registered by
the compiled source, is now registered by the installed writer at layout
index 12, so the layouts between move up by one. No upstream source,
reference primitive, runtime ABI, native interface, toolchain, or new axiom is
introduced.

As with the wire and row-hash helpers, these are helper-body certificates
against the reference machine and the pinned source definitions, checked
alongside the frontend's differential source oracle. General typed LCNF
source-to-Ixby refinement remains open. Resource exhaustion need not occur at
the same point in the shorter execution.

## Artifacts and validation

The singleton image is 991,071 bytes; the CSLib image is 1,005,303 bytes.
Each has 670 functions, 5,824 blocks, and 140 constructor layouts: the source
`writeNat` body is replaced by the two certified helpers. Maximum frame size
remains 66 locals. The inliner selects 948 ordinary call sites. Both decoded
images retain limits, the unchanged helper bodies, and the source reader up
to renumbering.

`check-ixby-lean` now runs 42,707 source-oracle helper executions, 111 caller
cases, 109 resource cases, and 531 exact transition formulas, and rejects
2,408 certificate mutations (1,509 structurally admitted). The new cases
cover widths zero through nine against the source writer through writer
buffers and packed states, the range helper with explicit bounds, byte-limit
and integer-range rejections, local, continuation and Nat-bit limits, the
64-bit literal's capacity, and the shift wrapper's exact costs at every
count. The typed source suite adds 528 `wireNatWrite` comparisons through the
source-compiled and installed paths, for 5,121 differential executions. The
existing inliner, FRI, row-hash, binary, and eight serialized Stage2
execution gates remain required.

```sh
lake exe check-ixby-lean
lake build CompilatrixTests.Proofs
lake exe stage2-ixby fixtures/ixby-stage2 compile /tmp/stage2.ixby
lake exe stage2-ixby fixtures/ixby-stage2 valid /tmp/stage2.ixby
nix build .#checks.x86_64-linux.ixby-lean
```

`compile-no-fri` and `compile-baseline` retain the new runtime prefix; their
pinned hashes are updated. Historical inlining, array-read, FRI and row-hash
measurement records remain unchanged.
