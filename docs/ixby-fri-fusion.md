# FRI coordinate loop fusion

The Stage2 compiler selects a direct array loop for FRI point reduction.
It removes the two array-to-list conversions, list length scans, zipped
coordinate pairs, and tuple accumulator from the coordinate traversal.
Width checks and denominator validation retain the pinned source order.

| Workload | Previous transitions | Fused transitions | Saved |
| --- | ---: | ---: | ---: |
| Stage2–CSLib | 276,667,563 | 254,245,163 | 22,422,400 (8.10%) |
| Stage2–singleton fixture | 544,834,777 | 500,247,577 | 44,587,200 (8.18%) |

Both runs preserve their exact outputs. These are logical reference-machine
transition counts; native proving and wall-time improvements are unmeasured.
The singleton fixture is a smoke proof, not a full Init verification claim.
The baseline is revision `e048fa0a4783f1b773b454e3d036c66f06511d22`, including
ordinary leaf-call inlining and single-dispatch array reads.
Artifact identities and execution evidence are in
[fri-fusion.json](../fixtures/ixby-stage2/fri-fusion.json).
The subsequent [certified row hash](ixby-row-hash.md) retains this source
equality and its selection checks while further reducing both workloads.

## Source equality and selection

The [implementation](../Compilatrix/Ixby/Stage2/Fri.lean) carries power and
value separately and reads coordinates in increasing index order. The
[kernel proofs](../Compilatrix/Ixby/Stage2/FriSound.lean) establish:

- `reduceLoop_eq_pairs`: every array suffix equals the original zipped-list
  fold, for arbitrary initial power and value.
- `reduceLoop_eq_coordinates`: matching arrays return the original result.
- `reduceCoordinates_eq`: the complete coordinate functions agree,
  including width rejection.
- `reducePoints_eq`: the pinned `MultiStark.Verify.Fri.reducePoints` and
  the replacement are equal as functions, for all arguments. This includes
  empty rows, empty opening lists, zero denominators, error ordering, and
  alpha-power continuation across multiple openings.

The vendored verifier and its provenance pins remain unchanged. The typed
frontend's optional `sourceEqualities` parameter names equality theorems;
callers do not provide arbitrary source/target name pairs.
[Selection](../Compilatrix/Ixby/Lean/Replacement.lean) requires an actual
closed theorem whose type is exactly an equality of two safe definitions,
with no universe parameters, no extra axioms beyond ordinary Lean logic,
available non-extern LCNF bodies, and equal monomorphic calling arity.
The source and target names come directly from that theorem's type.

Requests are limited to 32 entries. Duplicate sources, chains, cycles, and
overrides of installed runtime bodies reject the entire optional request.
Rejection retains the original compilation and records the reason. The
Stage2 adapter additionally requires the expected replacement to be accepted
and used: the source name must resolve to the exact target function slot.
Its manifest records both names and the equality theorem.

This is a kernel proof of **source-function equality**. General Lean proof
erasure, monomorphization, LCNF lowering, and source-to-Ixby refinement remain
outside the experimental frontend's certificate boundary. It does not add
an Ixby-to-Ixby simulation or a whole-verifier source certificate. Resource
exhaustion need not occur at the same point in the shorter execution.

The existing inliner still checks its complete input/output images after
source lowering, with the runtime prefix protected. All 107 runtime/wire
body certificates run on the selected image and decoded binary. The current
helper bodies and their public theorem premises are unchanged. Four new exact
[axiom fences](../CompilatrixTests/Fences/IxbyFri.lean) preserve all 2,767 prior
assertions; they use only `propext`, `Classical.choice`, and `Quot.sound`.
No upstream source, reference primitive, runtime ABI, native interface,
toolchain, or new axiom is introduced.

## Artifacts and validation

Both images shrink by 96 bytes, three functions, and eleven blocks. The
singleton image is 990,986 bytes; the CSLib image is 1,005,218 bytes. Each has
669 functions, 5,811 blocks, and 140 constructor layouts. Maximum frame size
remains 66 locals. The inliner selects 955 ordinary call sites.

`check-ixby-fri` compares 420 source cases with original, fused, and
subsequently inlined Ixby images, using both reference and chunked execution.
The cases cover width/length mismatches, empty inputs, zero denominators,
multiple points, nontrivial starting accumulators, alpha zero/one, and a
full-width Nat rejection. Compiler checks exercise exact target binding,
extra-axiom rejection, missing/extern LCNF, changed calling arity, overlapping
requests, protected helpers, request limits, and complete-image fallback.

The focused gate is included in `check-ixby-lean`; the four proof fences are
in `CompilatrixTests.Proofs`. Existing helper, source, binary, inliner and
eight serialized Stage2 execution gates remain required. Fresh repeated
compilation and an independent binary reader check the frozen artifact.

```sh
lake exe check-ixby-fri
lake build CompilatrixTests.Proofs
lake exe stage2-ixby fixtures/ixby-stage2 compile /tmp/fused.ixby
lake exe stage2-ixby fixtures/ixby-stage2 compile-no-fri /tmp/no-fri.ixby
lake exe stage2-ixby fixtures/ixby-stage2 compile-baseline /tmp/baseline.ixby
nix build .#checks.x86_64-linux.ixby-lean
```

`compile-no-fri` retains inlining and reproduces the previous binary exactly.
`compile-baseline` disables both optional transformations and retains its
previous byte identity. Historical inlining and array-read measurement
records remain unchanged.
