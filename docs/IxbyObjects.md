# IxBy: authenticated immutable objects

The object backend adds constructor creation, projection, and constructor
pattern matching to [scalar CEK control](IxbyControl.md). Recursive list map,
tail-recursive list fold, nested object calls/returns, and shared immutable
values now have real Aiur/FRI proofs under one program-independent object key.
The earlier scalar and control profiles remain separate regression baselines.

This is experimental: [wire and crypto semantic revision](IxbyEncoding.md)
remain 0. No Compilatrix lowering, production claim, authorized deployment key,
Flock interpreter, or terminal SNARK is introduced.

## Supported fragment and fixed capacities

`Ix/Ixby/Aiur/Objects.lean` implements the interpreter.
`Aiur/Fragment.lean` defines `objectsProfile` and the optional host convenience
check `validateObjectsFragment`; the circuit independently checks admission.

All control-slice instructions and its 20 scalar primitives remain available.
New operations are `construct` and `project`; the new instruction is `caseCtor`.
Values are immutable constructors, Bool, Word32, canonical Goldilocks/extension
scalars, or erased. Literals remain scalar/erased operands, not object advice.
Closures/PAPs, general application, byte scalars, and the other 15 crypto
primitives remain excluded. Nat, String, and `caseNat` remain outside crypto v0.

| Fixed parameter | Bound |
| --- | --- |
| Functions / constructor declarations | 8 / 16 |
| Blocks per function / locals per frame | 64 / 64 |
| Operands, arguments, or constructor fields | 16 |
| Saved continuations | 16 |
| Nodes across the input forest / in the output tree | 128 each |
| Input/output value depth | 32 |
| Complete program bytes | 16,384 |
| Complete input / output bytes | 8,192 each |
| Reference transitions | 256 |
| Derived intermediate object rank | 288 |

All semantic capacities come from the same committed
profile used by the reference codec. Rank 288 is derived as `valueDepth +
maxSteps`, not a new wire parameter. These are test capacities, not production
sizing or reviewed security policy.

## Authentication and object representation

The public statement is still `(P, B, I, O)`. Only raw program/input
bytes are advice. The interpreter authenticates those bytes, admits the full
image, executes it, serializes the actual terminal value, and checks `O`.
Decoded tables, object pointers, ranks, continuations, output values, and
instruction traces are not supplied as advice.

Constructor declarations retain wire order. Each semantic name consists of a
32-byte block digest, u32 member, and u32 tag. The circuit compares all ten
injective little-endian u32 limbs, never reduced eight-byte chunks or physical
pointers. Every declaration is checked for duplicate names, including unused
declarations with different arities. Input names resolve to that unique table
index; output serialization recovers the original full name from the table.

`ISValue` holds either an `IBValue` atom or an inline constructor record:
`(constructorIndex, fieldsPointer, fieldCount, rank)`. Fields and locals are
immutable reverse-ordered lists. Projection first checks `index < count`,
then reads `count - (index + 1)`. Erased projection returns erased for every
u32 index, including `0xffffffff`; scalar projection fails. Constructor cases
reject atoms, including erased, and append fields in declaration order.
All alternatives are admitted, including untaken ones: valid constructor
indices, unique alternatives, and exact successor-frame sizes are required.
Unexecuted dynamic type errors remain allowed, as in the reference semantics.

Atoms have rank 1. `is_make`, used for both inputs and runtime construction,
checks declaration arity and computes `1 + max(child ranks)`, with an empty
maximum of 0. It does not accept rank advice. Bounded natural ranks strictly
decrease along object-child edges. Each field-list walk is bounded by its
checked count and requires Nil at its end. The intended invariant uses
functional memory consistency, not increasing allocation addresses or unique
content addresses: equal cells at different pointers are allowed.

Input/output node budgets are shared across all siblings and roots. A child
decrements depth, while a sibling keeps its parent's child-depth budget.
Output serialization visits reverse fields while prepending bytes, producing
canonical declaration order. A shared object is unfolded at each occurrence
and charged each time; the 128-node budget is not a distinct-pointer count.

I/O limits do **not** apply to every intermediate value. Tests construct an
intermediate rank-95 object while returning a depth-32 input, and build a
255-node shared tree before projecting a valid 127-node result. Copies,
projections, and control transfers cannot increase the maximum known rank;
one constructor transition can increase it by at most one. This motivates
the separate derived bound of 288 without shrinking the reference fragment.
Normal calls, tail calls, return/pop transitions, and fixed fuel retain the
control slice's semantics; no call resets fuel or continuation depth.

## Formal contract and remaining bridge

`Aiur/ObjectsRefinement.lean` has 25 public kernel-checked lemmas. Its `Ref`
contains an arbitrary physical field-list pointer, and its functional `Heap`
may contain cycles or duplicate cells. `ClosedRanked` states the local
declaration, arity, bounded-list-read, computed-rank, and child-closure checks
for live references. It does not assume that the heap is already a finite tree.

`ranked_heap_represents` derives a finite logical IxBy value for each live
reference. The child relation is well-founded, and `no_ranked_cycle` excludes
nonempty cycles. Other lemmas cover construction, reverse-field projection,
constructor-name/index correspondence under unique declarations, case
selection, field binding, erased projection, and reference case transitions.
The earlier 27 frame/stack/control lemmas remain reusable.

The first numeric connection uses Aiur's **pure** Goldilocks model: bounded
natural embedding is exact, its comparison model reflects natural order,
and incrementing the maximum allowed rank cannot wrap. The module imports
no FFI oracle and uses no custom axioms, `sorry`, or `native_decide`. Inspected
theorems depend only on Lean's standard logical axioms.

These are conditional representation results, not a complete
constraints-to-`Codec.Evaluates` theorem. Work remains to establish the typed
memory view and live-reference invariant from actual traces, connect every
decoder/fetch/primitive/transition, and prove the compiler and lookup/memory/
range/hash gadgets refine their models. Honest proofs and malformed-artifact
tests do not substitute for a complete malicious-witness audit or reviewed
cryptographic assumptions. The rank-growth theorem explicitly assumes the
per-transition growth bound; the whole interpreter trace proof is still open.

### Compiler issue found and repaired

The shared `Source.Term.hoistLets` pass formerly hoisted continuation lets across
`assertEq` without protecting caller-local shadowing. Initially both program
and input tails were named `rest`: compiled code checked the input tail twice
and accepted trailing program bytes, while source interpretation rejected them.

The initial workaround used distinct `programEnd` and `inputEnd` names. The
shared [normalizer](../Ix/Aiur/Stages/Source.lean) now freshens caller and callee
scopes, keeps assertion/IO continuations after their operations, and sequences
complete earlier arguments before later hoisted prefixes. The object entry
again uses `rest` for both tails: the existing source/native regressions reject
trailing bytes 0, 1, and 255 with matching commitments, testing the original
failure without relying on the workaround.

[Compiler regressions](../Tests/Aiur/Hoisting.lean) cover explicit results and
failure stages, IO order, nested scopes, inline calls, alternative patterns,
and generated-looking names. This is an implemented, tested repair, **not a
compiler correctness proof**. Existing compiled circuits and verifying keys
must be rebuilt; neither the IxBy wire revision nor Rust/protocol code changed
as part of this repair.

## Reproduction and coverage

```sh
lake build --wfail Ix.Ixby.Aiur.ObjectsRefinement IxbyObjectsTests IxbyControlTests IxbyAiurTests
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyObjectsTests
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyObjectsTests --execute-only
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyObjectsTests --stats
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyControlTests
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyAiurTests
```

`ScalarSystem.buildObjects commitmentParameters friParameters` selects this
backend; the existing `execute`, `prove`, `verify`, and `verifyBytes` adapter
is reused. Verification takes the caller's expected statement and no execution
advice. Native proving retains preflight, and untrusted proof decoding retains
size, parse, and exact reserialization checks. This is not a new proof envelope.

The suite passes 530 checks, including 66 proved workloads across 55 guest
images and a fresh verifier with the same key. Execution-only has 453 checks.
Coverage includes recursive map at 16 saved frames, tail fold of 31 elements,
all 20 primitives in structured results, full constructor names, each of the
ten identity limbs, reordered declarations, asymmetric fields, nonzero entries,
64-local case binding, intermediate/I/O distinctions, and shared-tree budgets.

The 378 malformed/excluded/nonterminal artifacts have matching raw commitments
and bypass host/reference admission. Unused-code mutations preserve the valid
entry's input/output; all admission/runtime negatives must fail before the
output-commitment check, avoiding false coverage from an unrelated wrong result.
Malformed input-value tests return erased, so output admission cannot mask a
missing input check.
Additional checks cover source execution,
the compiler regression, byte/range advice, malformed proving requests, all
four changed statement digests, and corrupted/truncated/trailing proofs.
The 704 earlier scalar/control/reference/crypto/codec checks also pass: **1,234
targeted runtime checks total**, not counting theorems as runtime tests.
`Tests/Main.lean` exposes execution-only `ixby-objects` and opt-in
`ixby-objects-prove` alongside the earlier suites.

## Initial costs (test parameters only)

The timing/proof-size measurements below are the original pre-repair run.
After the shared hoisting repair, all 530 checks pass, and the three reported
deterministic row/width/FFT-cost examples are unchanged. Rebuilding a circuit
can still change its key and serialized proof bytes; these historical timings
are not a new isolated benchmark of the repaired compiler.

The 2026-09-10 local run used an AMD Ryzen 9 7950X3D and eight Rayon threads.
Commitment parameters were `logBlowup = 2`, `capHeight = 0`; FRI used 64 queries,
no proof of work, `logFinalPolyLen = 0`, and `maxLogArity = 1`. These are test
settings, not a deployment security recommendation.

The full 530-check `--stats` run took 20.98 seconds wall time and peaked at
1,038,568 KiB RSS (about 0.99 GiB). Per-workload timings were 181–279 ms, including
fixture creation, preflight, proving, serialization/deserialization, and fresh
verification. Serialized proofs were 2,532,768–3,253,210 bytes. These are
full-suite observations, not isolated throughput
measurements or evidence of a speedup over the smaller backends.

The fixed system has 71 function circuits. Selected deterministic rows are:

| Workload | Code / input / output bytes | Machine raw / padded | Width-8 memory raw / padded | Output-value rows |
| --- | --- | --- | --- | --- |
| Recursive map, length 16 | 393 / 873 / 869 | 100 / 128 | 154 / 256 | 33 |
| Tail fold, length 31 | 336 / 1,644 / 14 | 96 / 128 | 226 / 256 | 1 |
| Shared output, 128 unfolded nodes | 453 / 18 / 3,272 | 9 / 16 | 38 / 64 | 128 |

Committed widths are 103 for the machine, 17 for width-8 memory, and 78 for
output-value serialization. Width-8 cells are shared by value/local/field and
operand lists, so these are not isolated object-allocation counts. Width-6
function/continuation memory has 18/32, 2/2, and 2/2 raw/padded rows respectively.
The actual flattened sizes are `ISValue = 6`, constructor declaration and block
payloads = 11, frame/function payloads = 4, and alternative payloads = 2.

The shared-output example needs only seven `is_make` rows but 128 output-value
rows: internal sharing does not erase external tree serialization work. The
fixed `Bytes2` table still has 65,536 rows and committed width 24. FFT-work
surrogates are approximately 151.26, 151.89, and 166.08 million, with zero
whole-machine cache hits. These are not Flock non-native-field estimates.

Next: continue the actual trace/AIR refinement and hostile-witness work, then add closures/PAPs,
general application, and the remaining byte/crypto operations explicitly.
Full verifier workloads and certified Compilatrix integration remain separate.
