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

### Checked concrete-memory reconstruction

`Aiur/ObjectsMemory.lean` now connects the logical heap to the Lean bytecode
evaluator's actual width-bucketed memory. Its executable decoder follows the
current compiler layout, not the wire encoding:

| Value or cell | Flat field layout |
| --- | --- |
| `ISValue.Atom` | `[0, atomTag, a, b, c, d]` |
| `ISValue.Ctor` | `[1, constructorIndex, fieldsPointer, fieldCount, rank, 0]` |
| `ListNode.Cons<ISValue>` | `[0, ISValue's six fields, tailPointer]` |
| `ListNode.Nil<ISValue>` | Eight copies of `1` |

Bool must be 0 or 1; all four Word32 bytes must be below 256. Field and
extension coefficients retain their full canonical Goldilocks values, and
pointer/index/count/rank interpretation does not narrow to u32. Inactive
fields of applied constructors must be zero. Nullary constructor references
use **tag padding** in `Lower.toIndex`: the `IBValue.Erased` payload is five
copies of `4`, and Nil is padded with `1`, not zero. Concrete-layout tests
exercise this distinction against compiled code.

`reconstruct` checks every reachable constructor's declaration, arity, exact
field-list length and Nil terminator, and computed rank. The field bound 16
is checked before walking a list. Recursive depth and a shared remaining-node
budget bound reconstruction, including repeated occurrences of a shared DAG.
Its node budget is diagnostic and caller-selected, not a new I/O admission
rule; the derived rank bound remains 288. Valid intermediate objects can
therefore be reconstructed with more than 128 nodes or depth 32.

The module has 10 kernel-checked lemmas. `bytecode_heap_load_iff` relates a
typed cell to the evaluator's actual `memLoad` and successful layout decoding.
`reconstruct_sound` proves that successful reconstruction yields the existing
`Represents` relation and a finite logical value, without a `ClosedRanked`
premise. Other lemmas establish numeric exactness, local checks and bounds,
pointwise child representation, and decreasing/shared budgets. All 10 theorem
axiom audits use only Lean's standard logical axioms; none relies on FFI
execution, custom axioms, `sorry`, or `native_decide`.

This is a checked memory interpretation, **not** a production verifier or an
execution/AIR soundness theorem. Reconstruction success is its explicit
premise; success has not yet been derived from arbitrary interpreter traces.
The lower-level decoder takes a declaration array; the table layer below now
checks its correspondence and uniqueness. Establishing those checks from the
interpreter's authenticated parsing still remains open. Malformed or cyclic
unreachable cells and duplicate cells at distinct pointers are allowed.

`Tests/IxbyObjectsMemory.lean` adds 126 checks. Typed fixtures call the real
compiled `is_make` and `is_project`, retain Lean evaluator memory for decoding,
and compare 14 native flat outputs. The native test adapter changes only the
selected helper's entry flag; pointer-bearing internal signatures cannot be
public source entries. It does not construct proofs or alter production keys,
and flat-output parity is not a claim of native heap equivalence. Coverage
includes malformed tags/padding/ranges/pointers/counts, cyclic spines and child
graphs, exact shared budgets, rank 288, and larger-than-I/O intermediates.

Forged-memory helper tests also make the invariant boundary explicit: a local
`is_make` call can accept a forged child's in-range rank while recursive
reconstruction rejects that child. Such memory is not production advice;
this test documents why local checks alone do not establish child closure.

### Concrete tables and immutable-store preservation

`Aiur/ObjectsStore.lean` adds 13 public kernel-checked lemmas. Unlike a
preservation assumption about an abstract heap, `mem_store_preserves` proves
that the Lean evaluator's actual `memStore` preserves every existing readable
cell, at every width. It uses the invariants carried by `IndexMap`, covering
both appended and content-deduplicated cells. `mem_store_load` proves exact
readback at the returned natural address. Converting that address to a field
has a separate theorem with an explicit Goldilocks-bound premise.

The store lemmas transport existing field lists, `Represents` relations, and
successful reconstruction—including the exact remaining node budget. They
also establish the field-list and logical-construction contract for a newly
stored Cons cell. `eval_store_preserves_representation` covers a successful
**actual bytecode Store instruction**, including its register update. These
are not yet preservation theorems for all bytecode instructions or complete
compiled `is_make` executions, nor proofs of the AIR memory argument.

`Aiur/ObjectsTable.lean` adds 11 public kernel-checked lemmas and a concrete
table decoder. `ISCtorDecl.Mk` is tagless and occupies eleven fields; a Cons
cell is `[0, eight digest limbs, member, tag, fieldCount, tailPointer]` at width
13, and Nil is thirteen copies of 1. All ten identity limbs must be u32.
Natural packing is bounded and injective for fixed-length bounded limb lists;
there is no Goldilocks reduction of the 256-bit digest or narrowing of metadata.
The reader checks the 16-declaration and 16-field capacities, exact terminal
Nil, declaration order, and uniqueness of full semantic names even when their
arities differ. Unreachable cells and duplicate physical cells remain allowed.

`reconstructProgram` uses the existing canonical program decoder, compares the
entire concrete table with that program's declarations, and reconstructs the
value in the matching constructor namespace. `reconstruct_program_sound`
establishes the canonical program-encoding equation, concrete table agreement,
unique IDs, and logical value representation. Table decoding and this complete
checked reconstruction are also preserved by actual `memStore` operations.
All 24 new public theorem axiom audits use only Lean's standard logical axioms.

This diagnostic does **not** authenticate the program commitment or prove
that the program produced the value. Tests explicitly demonstrate that a
different valid function body with the same declarations can represent the
same value. The outstanding work is to prove the compiled parser establishes
the checked table relation, initialization establishes valid live references,
and every interpreter transition maintains the representation and reference
execution relation; the compiler/gadget/AIR and commitment links remain open.

`Tests/IxbyObjectsTable.lean` adds 191 checks: malformed concrete tables, every
identity limb and Nil padding field, duplicates, exact capacities, eight
checks against compiled `is_read_ctors`, and five complete compiled `is_run`
fixtures with memory inspection. The latter include parsed and runtime-created
objects, case binding, erased input, and an empty table. They check same-width
and other-width stores, readback, content reuse, actual Store instructions,
valid-program/table mismatches, and the representation/execution distinction.
The tests add no new FRI workloads and do not change the production interpreter,
profiles, wire format, or keys.

### Bytecode parser proof components

`Aiur/ObjectsParser.lean` adds 22 public kernel-checked lemmas. Its `BytePrefix`
relation describes exact width-3 Cons cells containing genuine bytes and
field-valued tail pointers. It describes a consumed prefix, not a complete
stream: the endpoint may point into the following artifact, and is returned
without narrowing or an extra read. Actual stores preserve this relation;
exposing a newly allocated pointer as a field retains an explicit bound.

Executable structural certificates check the actual function bodies for
`ib_byte`, standalone `ib_u32`, and the **zero-count path only** of
`is_read_ctors`. Their soundness uses decidable structural equality, not an
assumed lawful bytecode `BEq` or a compiler-correctness axiom. Tests check the
certificates against both the full production compilation and a pruned one
with different callee indices. This validates these emitted shapes; it is
not a general theorem about source compilation.

The byte-reader theorem describes actual `evalBlock` behavior, including
function-return handling. The Call theorem additionally proves caller-register
restoration. The u32 theorem consumes four certified bytes, preserves memory
and I/O, and agrees with the existing codec's little-endian numeric packing.
Bounds cover every intermediate field operation, not just the final u32.
The byte reader itself does **not** range-check: a separate theorem proves
what a successful actual `u8RangeCheck` instruction establishes. Connecting
the complete advice loader to `BytePrefix` remains an obligation.

The zero-count parser theorem establishes the checked empty-table relation
at its actual output pointer, including canonical 13-field Nil padding and
content-deduplicating allocation. A separate final-Cons-store theorem extends
a checked tail table with a fresh semantic name in forward order. The
nonzero recursive parser path, ten-limb identity reader, and duplicate-ID
traversal still need to establish that theorem's premises. The zero-count
certificate intentionally leaves the default branch unconstrained; it must
not be used as a certificate for the full declaration parser.

All 22 axiom audits use only Lean's standard logical axioms. The 387 new
`Tests/IxbyObjectsParser.lean` checks include every byte value, u32 boundaries
and bit positions, exact suffix/state preservation, malformed cells, callee
and instruction mutations, and fresh/deduplicated empty tables. Explicit
counterexamples show why byte ranges and the nonzero-branch proof are needed:
forged non-bytes can wrap to a plausible u32, and a function passing only the
zero-count certificate can have an invalid nonzero branch. These are diagnostic
fixtures, not additional production advice or FRI workloads.

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
must be rebuilt. The checked-in generated Rust kernels for IxVM, MultiStark,
and ixAggr must also be regenerated after this shared compiler change. This
regeneration was initially omitted, causing `lake exe ix codegen --check` to
report all three files stale; the snapshots are now refreshed. No IxBy wire
revision or handwritten Rust/protocol implementation change is required.

After changing the shared Aiur compiler, run `lake exe ix codegen`, rebuild
the native test runner, and run the content and generated/interpreter parity
checks. Checking content alone does not rebuild a previously linked test binary:

```sh
lake exe ix codegen
lake build --wfail IxTests ix
lake exe ix codegen --check
RAYON_NUM_THREADS=8 .lake/build/bin/IxTests --ignored ixvm
RAYON_NUM_THREADS=8 .lake/build/bin/IxTests recursive-verifier ix-aggr
```

## Reproduction and coverage

```sh
lake build --wfail Ix.Ixby.Aiur.ObjectsRefinement IxbyObjectsTests IxbyControlTests IxbyAiurTests
lake build --wfail Ix.Ixby.Aiur.ObjectsMemory IxbyObjectsMemoryTests
lake build --wfail Ix.Ixby.Aiur.ObjectsStore Ix.Ixby.Aiur.ObjectsTable IxbyObjectsTableTests
lake build --wfail Ix.Ixby.Aiur.ObjectsParser IxbyObjectsParserTests
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyObjectsMemoryTests
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyObjectsTableTests
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyObjectsParserTests
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
The separate `ixby-objects-memory`, `ixby-objects-table`, and
`ixby-objects-parser` suites add 126, 191, and 387 checks respectively,
bringing current targeted runtime coverage to **1,938 checks**.
They add no FRI proof workloads and do not change the
530-check object baseline or its measurements below.

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

Next: compose the byte/u32 contracts through the ten-limb identity reader,
duplicate-ID traversal, and nonzero recursive declaration parser. Establish
the input byte-prefix invariant from admission and connect the resulting table
to the canonical program image. Then establish successful reconstruction for
live values from initialization and complete transitions. Immutable Store
preservation and the zero-count parser path are proved; full execution and
trace/AIR contracts remain open. Continue hostile-witness work before adding
closures/PAPs, general application, and the remaining byte/crypto operations.
Full verifier workloads and certified Compilatrix integration remain separate.
