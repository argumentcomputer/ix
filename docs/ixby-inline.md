# Certified ordinary leaf-call inlining

Stage2 export replaces ordinary calls to single-operation helpers with their
substituted operation. On the retained CSLib workload, this removes **61,089,486
logical transitions (16.95%)**, from 360,337,913 to **299,248,427**, with identical
49-byte output. The image contains 954 rewritten call sites and is 99 bytes
smaller. These are logical execution counts, not native proving or wall-time
speedup claims.

These measurements describe the inlining change at revision `1eaa245`.
The subsequent [single-dispatch array-read change](ixby-array-read.md) retains
these inlining certificates. [FRI source fusion](ixby-fri-fusion.md) follows it
and retains the inliner's separate complete-image certificate.

## Checked transformation

[`Inline.optimize`](../Compilatrix/Ixby/Inline/Optimize.lean) proposes a
deterministic rewrite. Its independent
[`check`](../Compilatrix/Ixby/Inline/Check.lean) validates both complete programs
and returns a certificate indexed by their actual code, semantic limits, and
protected prefix. It checks every function and block, including unreachable
code. A leaf has exactly two blocks: one copy, primitive, constructor, or
projection, followed by return of that operation's result. All call arguments
must be readable, including unused arguments. Substitution preserves argument
order, duplication, literals, and erased values.

Only ordinary `letOp (call ...)` instructions change. Function signatures,
entry points, block counts and indices, local-frame contracts, constructors,
and all other instructions remain equal. Tail calls are deferred. Stage2
protects functions 0–107: all 97 runtime helpers, the source `readBytes` target,
and ten wire helpers. Existing complete-body certificates check the selected
image again.

Policy version 1 has an enable flag, protected-prefix length, and a structural
producer budget of 1,000,000 declarations, blocks, and operands. This budget
limits candidate production, not certificate checking or guest execution.
Disabled, unsupported, exhausted, unchanged, or rejected attempts return the
admitted original with a checked certificate. An invalid original is an error.

## Kernel guarantees and resource accounting

[`Sound.lean`](../Compilatrix/Ixby/Inline/Sound.lean) proves these contracts for
every checked pair, arbitrary inputs, and successful finite executions:

| Direction | Guarantee |
| --- | --- |
| Original → selected | Same output with the same semantic limits and fuel. |
| Selected → original | Same output with at most `4 * fuel` and one additional continuation slot; all other limits unchanged. |
| Existing baseline specification | Every successful selected result equals the baseline's specified successful result. |

The whole-machine proofs cover ordinary and tail calls, mutual and self
recursion, closures, overapplication, and arbitrary continuations. They use
the actual reference steps and operand semantics, without a caller-supplied
semantic oracle. A contracted invocation removes three transitions. Fuel
exhaustion and continuation exhaustion are therefore not equated between
programs. In particular, the selected program can succeed with zero available
continuation slots where the original needs one. Reflection states that cost
explicitly.

The checker and proof roots have 111 exact
[axiom fences](../CompilatrixTests/Fences/IxbyInline.lean), using only ordinary
Lean logical axioms. All 2,649 previous fences remain unchanged. There are no
new axioms, admitted proofs, native proof decisions, primitives, or FFI interfaces.
The general typed LCNF-to-Ixby source-refinement boundary remains open; this
pass certifies the transformation between Ixby programs.

## Export and validation

[`optimizeImage`](../Compilatrix/Ixby/Inline/Image.lean) runs after the frontend
finishes the image and updates its builder slots alongside the program.
Stage2 encodes the selected program, decodes it, and rechecks that actual
decoded program against the original, including all helper certificates.
The manifest records policy, status, work, and the original binary's BLAKE3.
`compile-baseline` exports the original through the same validation path.

```sh
lake exe check-ixby-inline
lake build CompilatrixTests.Proofs
lake exe stage2-ixby fixtures/ixby-stage2 compile /tmp/stage2-inline.ixby
lake exe stage2-ixby fixtures/ixby-stage2 compile-baseline /tmp/stage2-original.ixby
nix build .#checks.x86_64-linux.ixby-lean
```

The focused suite checks primitive and projection errors, large naturals,
constructors, argument substitution, recursion, dynamic application, fuel and
capacity boundaries, rejected mutations, all fallback modes, and binary
rechecking. It also reruns 4,585 independent typed-source comparisons on
selected images, retaining all runtime and wire certificates. The existing
`check-ixby-lean` gate includes this suite. All eight Stage2 binary cases remain
required gates. Artifact identities and execution measurements are retained
in [inlining.json](../fixtures/ixby-stage2/inlining.json).

The [runtime revision 2 record](ixby-runtime-v2.md) remains the historical
baseline, including its separate native fixture proof. A complete native proof
for the inlined CSLib program has not been generated.
