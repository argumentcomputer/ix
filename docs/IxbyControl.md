# IxBy: authenticated scalar CEK execution

The control-flow backend proves input-dependent branches, direct and self
calls, tail calls, recursion, and caller resumption under one program-independent
Aiur/FRI interpreter key. It retains immutable scalar values and local frames.
It does not change the [wire format or semantic revision](IxbyEncoding.md),
both still 0, or modify Compilatrix or production claims.

The [first straight-line backend](IxbyAiur.md) remains a regression baseline.
The control backend has its own fixed profile and key; its larger admitted
fragment does not silently broaden the old backend's acceptance policy.

A separate [immutable-object backend](IxbyObjects.md) now adds constructors,
projections, and constructor cases, including proved recursive list map. This
document retains the scalar-only control profile and its measurements.

## Scope and capacities

`Ix/Ixby/Aiur/Control.lean` implements the constrained interpreter.
`Aiur/Fragment.lean` defines `controlProfile` and the optional host convenience
check `validateControlFragment`. Verification never trusts that host check.

Supported instructions are `letOp`, `ret`, `branch`, `tailCall`, and
`tailCallSelf`. Operations are `copy`, the same 20 scalar primitives as the
straight-line backend, `call`, and `callSelf`. Inputs, literals, and outputs
can be Bool, Word32, canonical Goldilocks or extension elements, or erased.
Branch conditions must be Bool; numeric truthiness is not accepted.

Function/block entries need not be zero. Successors need not follow wire
order. Forward calls, mutual recursion, backward block successors, and unused
functions/blocks are allowed, subject to whole-image structural admission.
Unused code can contain dynamic type errors, as in the reference semantics,
but cannot contain malformed references or excluded instructions.

| Fixed parameter | Bound |
| --- | --- |
| Functions / constructors | 8 / 0 |
| Blocks per function / locals per frame | 64 / 64 |
| Operands / entry arguments / input nodes | 16 each |
| Saved continuations / value depth | 16 / 1 |
| Complete program bytes | 16,384 |
| Complete input / output bytes | 1,024 each |
| Reference transitions | 256 |
| Nat bits / string bytes / byte-array bytes | 0 / 0 / 0 |

These are experimental capacities, not production sizing or security policy.
All capacities are committed by the existing profile encoding. Circuit
constants and the profile digest are generated from that same profile.
Constructors, projections, constructor cases, closures/PAPs, general application,
byte values, and the remaining 15 crypto primitives are still excluded. Nat,
String, and `caseNat` are excluded by the crypto profile itself. BLAKE3 is used
for artifact authentication, not yet as an exposed guest primitive.

## Authentication, admission, and execution

The public statement remains `(P, B, I, O)`, packed as eight injective 32-bit
limbs per digest. Only raw program and input bytes are advice, on channels 0
and 1 with key `[0]`. There is no supplied decoded code table, execution trace,
frame, return stack, primitive result, or output witness.

1. Range-check advice lengths before iteration and every byte before storing
   it. Authenticate the complete program and input with the existing
   domain-separated BLAKE3 framing.
2. Decode every function and block into immutable lists in wire order. Check
   headers, tags, scalar canonicality, collection capacities, local operands,
   and primitive arities while decoding. Consume the complete image.
3. Check every decoded block against the complete function table: function
   entries, call targets and arities, both branch targets, and successor-frame
   contracts. Admission includes unused functions and untaken branches.
4. Decode the full input, enter the selected function, and run `ic_machine`
   with fixed fuel and an empty continuation. Every instruction fetch comes
   from the authenticated decoded tables, with bounded logical indices.
5. Encode the actual terminal value canonically, enforce output capacities,
   and check its commitment against the caller's expected `O`.

Function, block, and operand tables retain wire order. Locals are reverse
ordered: appending a value is one immutable `Cons`, and absolute local `i`
is read at `count - (i + 1)` after checking `i < count`. Argument evaluation
builds a reversed local list without reversing the logical argument order.
Physical memory pointers are backend-private and are not used to decide
semantic equality or to replace program identity.

A direct call saves the caller's function, successor block, and original
locals. That saved frame has one fewer local than the successor requires;
only resumption appends the returned value and checks the successor frame.
A tail call replaces the current frame and leaves the entire saved stack
unchanged, including when it is already at capacity.

Fuel follows the reference machine exactly: an instruction return produces a
return control state; popping a continuation or halting requires another
transition. Every recursive machine call decrements fuel. Neither a guest
call nor a return resets fuel, and exhaustion is never accepted as termination.

Lookups currently use bounded immutable lists, not constant-cost random-access
ROM. Aiur memoizes repeated lookup and primitive queries. The whole-machine
query includes fuel and continuations, so this implementation does not claim
memoization of an entire repeated guest computation across callers.

## What is formally established

`Ix/Ixby/Aiur/Refinement.lean` is a pure, separately importable logical contract.
Its 27 public kernel-checked lemmas establish:

- Frame encoding/decoding, list/array order and sizes, guarded absolute-local
  lookup, argument accumulation, and immutable local extension.
- The complete reversed continuation stack's representation in the reference
  state, including saved caller identities and locals.
- Reference transitions for pure lets, branches, direct/self calls, tail calls,
  instruction returns, caller resumption, and empty-stack termination.
- Continuation overflow and exact transition/fuel accounting, including why
  a return instruction needs two transitions to finish an empty-stack run.

Transition lemmas take the relevant reference lookup, read, primitive-result,
entry, and frame-check equations as explicit hypotheses. They do not assert
that the circuit establishes those equations. The logical lists are finite
values, not a certified decoding of arbitrary field-valued pointer graphs.

The missing circuit refinement must connect canonical image decoding, memory
lookups and finite list representations, bounded field counters, and primitive
gadgets to these lemmas, then connect the accepted constraints to
`Codec.Evaluates`. Aiur compiler correctness, the lookup/memory argument, and
cryptographic assumptions remain explicit obligations. No custom axiom,
`sorry`, FFI oracle, or `native_decide` is used in the representation module.
Proof verification and differential tests are not that soundness theorem or
a complete malicious-witness audit. Security/privacy properties still require
review before deployment.

## Host interface and checks

`ScalarSystem.buildControl commitmentParameters friParameters` selects the
control backend. It uses the same `execute`, `prove`, `verify`, and `verifyBytes`
adapter as the original scalar system. Verification constructs the claim from
the caller's expected statement and receives no execution advice. The existing
preflight-before-proving and checked/canonical native proof decoding protections
are retained; this is not a new production proof envelope.

```sh
lake build --wfail Ix.Ixby.Aiur.Refinement IxbyControlTests IxbyAiurTests
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyControlTests
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyControlTests --execute-only
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyControlTests --stats
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyAiurTests
```

The control suite has 232 checks, including 50 proved workloads across 40 guest
images and a separately built verifier with the same key. Its execution-only
subset has 171 checks. Three examples also run through Aiur's source interpreter.
Coverage includes both branch outcomes, asymmetric argument order, nested caller
restoration, nonzero entries, backward successors, mutual and self recursion,
50 tail calls, full-stack tail calls, and exact function/local/argument/stack/fuel
capacities. The 115 malformed/excluded/nonterminal artifact tests use matching
raw commitments and bypass host admission and reference execution. Additional
checks reject non-byte advice, non-u32 lengths, changed commitments, malformed
proofs, and a callee result substituted for the caller's actual result.

The original 209 scalar-backend checks and 263 reference/crypto/codec checks
remain separate regressions. `Tests/Main.lean` includes execution-only
`ixby-control`; full proving is the opt-in `ixby-control-prove` suite.

## Initial costs (test parameters only)

The 2026-09-10 local run used an AMD Ryzen 9 7950X3D and eight Rayon threads.
Commitment parameters were `logBlowup = 2`, `capHeight = 0`; FRI used 64 queries,
no proof of work, `logFinalPolyLen = 0`, and `maxLogArity = 1`. These settings
are test fixtures, not a reviewed soundness/security recommendation.

The full 232-check `--stats` run took 25.00 seconds wall time and peaked at
909,996 KiB RSS (about 0.87 GiB). Other local checks ran concurrently, so this
is an observation, not an isolated throughput benchmark. Per-workload timing
was 249–537 ms, including reference fixture creation, preflight execution,
proving, serialization/deserialization, and independent verification. Serialized
proofs were 2,388,825–2,658,757 bytes. A preceding smaller 44-workload run was
faster; no speedup/regression claim should be inferred from these timings.

The system has 51 function circuits, seven memory tables, and two byte tables.
Selected deterministic trace counts from `--stats` are:

| Workload | Code bytes | Machine raw / padded rows | Width-6 memory raw / padded rows |
| --- | --- | --- | --- |
| Branch, helper call, caller resumption | 237 | 8 / 8 | 5 / 8 |
| Sum with 16 saved callers | 171 | 116 / 128 | 18 / 32 |
| Sum with 50 tail calls | 156 | 254 / 256 | 2 / 2 |

The machine table has committed width 96. Width-6 memory has committed width
15 and is shared by function-list and continuation-list nodes: both payloads
flatten to four fields before the list tag/tail. It is not a continuation-only
allocation count. Tail calls avoid saved frames but still produce local and
execution trace rows; they do not imply constant total prover memory.

The fixed `Bytes2` table still has 65,536 rows and committed width 24. The three
FFT-work surrogates are approximately 131.82, 132.58, and 135.44 million,
respectively, with zero whole-machine cache hits in these examples. These are
neither native timings nor Flock non-native-field cost estimates. Larger code
tables, structured values, real verifier workloads, and controlled measurements
are needed before selecting optimizations or freezing capacities.

## Next work

Constructor values, projections, and pattern matching are implemented by the
separate [object slice](IxbyObjects.md). Closures/PAPs and general application,
byte handling, and the remaining crypto primitives are still pending. The
shared let-hoisting issue has a tested repair, documented in the object slice;
continue the circuit-to-reference proof and
malicious-witness work alongside those changes. Full verifier workloads,
Flock-oriented costs and shape policy, source compilation certification, and
Stages 3/4 remain separate milestones. Compilatrix is unchanged.
