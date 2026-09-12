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

`Aiur/Objects/Refinement.lean` has 25 public kernel-checked lemmas. Its `Ref`
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
no FFI oracle. The checked-in [trust manifest](../Ix/Ixby/Audit.lean) covers the
reference and proof modules with exact allowances for 314 public theorems and
a broader scan of 3,058 theorem declarations. CI permits only Lean's standard
logical axioms; no custom, native-decision, or sorry allowance is present.

These are conditional representation results, not a complete
constraints-to-`Codec.Evaluates` theorem. Work remains to establish the typed
memory view and live-reference invariant from actual traces, connect every
decoder/fetch/primitive/transition, and prove the compiler and lookup/memory/
range/hash gadgets refine their models. Honest proofs and malformed-artifact
tests do not substitute for a complete malicious-witness audit or reviewed
cryptographic assumptions. The rank-growth theorem explicitly assumes the
per-transition growth bound; the whole interpreter trace proof is still open.

### Checked concrete-memory reconstruction

`Aiur/Objects/Memory.lean` now connects the logical heap to the Lean bytecode
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
pointwise child representation, and decreasing/shared budgets. These are kernel-checked
proofs over the evaluator model, not evidence from FFI execution.

This is a checked memory interpretation, **not** a production verifier or an
execution/AIR soundness theorem. Reconstruction success is its explicit
premise; success has not yet been derived from arbitrary interpreter traces.
The lower-level decoder takes a declaration array; the table layer below now
checks its correspondence and uniqueness. Establishing those checks from the
interpreter's authenticated parsing still remains open. Malformed or cyclic
unreachable cells and duplicate cells at distinct pointers are allowed.

`Tests/Ixby/Aiur/Objects/Memory.lean` adds 126 checks. Typed fixtures call the real
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

`Aiur/Objects/Store.lean` has 16 public kernel-checked lemmas. Unlike a
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

`Aiur/Objects/Table.lean` has 11 public kernel-checked lemmas and a concrete
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

This diagnostic does **not** authenticate the program commitment or prove
that the program produced the value. Tests explicitly demonstrate that a
different valid function body with the same declarations can represent the
same value. The outstanding work is to prove the compiled parser establishes
the checked table relation, initialization establishes valid live references,
and every interpreter transition maintains the representation and reference
execution relation; the compiler/gadget/AIR and commitment links remain open.

`Tests/Ixby/Aiur/Objects/Table.lean` adds 191 checks: malformed concrete tables, every
identity limb and Nil padding field, duplicates, exact capacities, eight
checks against compiled `is_read_ctors`, and five complete compiled `is_run`
fixtures with memory inspection. The latter include parsed and runtime-created
objects, case binding, erased input, and an empty table. They check same-width
and other-width stores, readback, content reuse, actual Store instructions,
valid-program/table mismatches, and the representation/execution distinction.
The tests add no new FRI workloads and do not change the production interpreter,
profiles, wire format, or keys.

### Bytecode parser proof components

`Aiur/Objects/Parser.lean` has 22 public kernel-checked lemmas. Its `BytePrefix`
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
what a successful actual `u8RangeCheck` instruction establishes. The bounded
loader connects actual loading to `BytePrefix` under explicit
metadata/address and storage bounds.

The zero-count parser theorem establishes the checked empty-table relation
at its actual output pointer, including canonical 13-field Nil padding and
content-deduplicating allocation. A separate final-Cons-store theorem extends
a checked tail table with a fresh semantic name in forward order. The
nonzero recursive parser composition in `Objects/Declarations.lean` below
establishes that theorem's premises from a bounded byte-derived prefix.
The zero-count certificate intentionally leaves the default branch
unconstrained; it must not certify the full declaration parser.

`Tests/Ixby/Aiur/Objects/Parser/Readers.lean` checks include every byte value, u32 boundaries
and bit positions, exact suffix/state preservation, malformed cells, callee
and instruction mutations, and fresh/deduplicated empty tables. Explicit
counterexamples show why byte ranges and the nonzero-branch proof are needed:
forged non-bytes can wrap to a plausible u32, and a function passing only the
zero-count certificate can have an invalid nonzero branch. These are diagnostic
fixtures, not additional production advice or FRI workloads.

### Compiled identity-reader composition

`Aiur/Objects/Identity.lean` has 20 public kernel-checked lemmas. The actual
`is_read_id` body inlines ten u32 readers; calling the standalone word-reader
theorem would not certify its register layout. The proof handles the
seventeen-register stride of each inlined word, composes the actual `runOps`
semantics, and structurally checks all 130 operations and eleven outputs.
The byte-reader callee is looked up and certified in the same toplevel.
Certificates pass for both full and pruned production compilations, including
relocated callee indices. This remains a certificate for those emitted shapes,
not a general compiler-correctness theorem.

Given a range-safe `BytePrefix`, the checked reader consumes exactly forty
bytes into ten exact u32 limbs. Grouping into words is proved to cover every
byte sequence of that length. The output decodes through the existing concrete
`decodeId`: the first eight limbs retain the full 256-bit digest, followed by
the member and tag. Their natural values agree with the existing little-endian
byte codec, without field reduction or integer narrowing. The complete memory
and I/O buffer are unchanged, and the full-field suffix pointer is returned
without loading it. The actual Call theorem also restores the caller's prior
registers and accounts for the nested byte-call fuel.

`Tests/Ixby/Aiur/Objects/Parser/Identity.lean` covers every identity
instruction and output position, all forty truncation and malformed-tag positions, each limb's
u32 boundaries and bit positions, actual byte-codec agreement at a nonzero
offset, unreadable intermediate/suffix pointers, memory/I/O preservation,
and actual Call argument/output/fuel failures. Forged non-bytes demonstrate
both an out-of-range limb and a wrapped, apparently valid semantic name;
another fixture shows why certifying the actual byte callee is necessary.
These remain diagnostic tests, not new production advice or proof workloads.

The bounded loader below establishes `BytePrefix`, and the bounded
declaration-parser induction is also proved below. Binding its resulting table
to the authenticated whole canonical program image remains open. The identity
component alone does not establish those connections or an AIR-to-reference theorem.

### Exact comparison and bounded duplicate traversal

`Aiur/Objects/Equality.lean` and `Objects/Unique.lean` add 37 public
kernel-checked lemmas. The comparator certificate binds the actual twenty
subtraction/zero-test operations, nine products, and output register.
Field subtraction and the emitted zero test distinguish arbitrary canonical
Goldilocks limbs. For successful `decodeId` results, the u32 bounds make
little-endian packing injective, so raw ten-limb equality is exactly equality
of the complete semantic digest, member, and tag. The actual Call theorem
returns the corresponding Boolean field and preserves prior caller state.

The uniqueness certificate checks all three emitted match layers, the padded
Nil assertion, the duplicate assertion, the counter decrement, both return
selectors, and both callee indices in the same toplevel. `DeclSpine` describes
a finite, exact-length raw declaration list ending in thirteen copies of 1.
With a counter below the field modulus and sufficient call fuel,
`unique_spine_eval` proves fresh-ID success and assertion failure for a
duplicate at any position. It does not assume limb ranges or distinct physical
pointers. Successful execution leaves memory and I/O unchanged.

`read_declarations_spine` derives that raw spine and each semantic name from
the existing table decoder. `checked_unique_table` uses the profile's
sixteen-constructor limit to discharge the no-wrap counter bound and gives
the exact semantic freshness result. `checked_unique_call` also restores all
caller registers: a successful no-output Call returns the identical state.
The table-decoding premise is explicit in this component; the declaration
parser below establishes it. Admission and whole-program binding remain open.
Both constraint flags share the Lean Call semantics, not an asserted AIR relation.

The identity/comparison and `Parser/Unique.lean` tests cover every comparator instruction/limb, full-field boundaries, all table lengths through
sixteen and every duplicate position, count mismatches, all Nil padding fields,
Call failures, full-field pointers, and full/pruned structural certificates.
Out-of-range limbs and a forged comparator demonstrate why range and callee
certificates remain necessary. Malformed-spine/cycle checks are regressions,
not a general proof for arbitrary malformed memory. These add no FRI workloads
and change no interpreter, compiler, wire format, or key.

### Complete bounded declaration-parser composition

`Aiur/Objects/Declarations.lean` has 23 public kernel-checked lemmas and uses
the allocation/I/O lemmas in `Objects/Store.lean`. `checkDeclarations` checks
both emitted branches, all 28 nonzero operations, argument and output
registers, and selectors. `checkDeclarationCode` also resolves and certifies
the byte, identity, comparison, uniqueness, and recursive parser functions in
the same toplevel. Full and pruned production compilations pass, including
relocated callees. The old zero-only checker remains intentionally partial.

`checked_declarations_eval` proves exact acceptance/rejection for a
`BytePrefix` of `44 * count` genuine bytes, with `count ≤ 16`, sufficient call
fuel, and `bucketSize before 13 + count + 1 ≤ goldilocksModulus`.
Each record contains the complete ten-word identity and one u32 field count;
record grouping covers every byte sequence of the required length. Semantic
digest/member/tag/field values agree with the existing little-endian byte
codec. The actual UInt32 comparison agrees with the natural field limit
because genuine bytes supply the u32 bound.

Acceptance is exactly distinct full semantic IDs and field counts at most 16.
The induction composes the actual identity read, inlined field read, arity
assertion, recursive Call, certified duplicate traversal, and final Cons store.
Neither a decoded tail table nor freshness is assumed at the public endpoint.
`checked_declarations_table` establishes the existing `readTable` relation in
forward wire order and preserves all prior readable cells and I/O. The store
model allows content deduplication; its allocation bound proves that returned
field-valued pointers do not wrap. The full-field suffix is returned unchanged
without requiring a readable cell or Nil there.

`checked_declarations_reject` rejects an unsupported arity or a duplicate at
any depth. This classification assumes a complete byte-derived prefix; it is
not a theorem for arbitrary malformed memory, mismatched counts, or truncated
input. Assertion errors expose no post-state, so no rollback property is
claimed. `checked_declarations_call` appends exactly the table and suffix
pointers while preserving prior caller registers and I/O. Both constraint
flags have that Lean evaluator behavior, not an asserted unconstrained AIR
relation.

`Tests/Ixby/Aiur/Objects/Parser/Declarations.lean` covers full/pruned
execution, every supported arity, all ten identity limbs and maximal digests,
all record counts through sixteen, deep duplicate pairs, invalid arities at
every position, all 132 truncation and malformed-tag positions in a three-record
prefix, exact new/deduplicated stores, suffix and caller-state preservation,
Call failures, every parser operation, and every required callee certificate.
Counterexamples show the remaining admission boundary: the standalone parser
can accept seventeen constructors, or a forged non-byte arity that wraps the
UInt32 comparison, although `readTable` then rejects the result. A forged
comparator likewise demonstrates why the complete callee bundle matters.

The loader establishes genuine loaded bytes and preserves
the table-capacity premise; the program-prefix contract derives
constructor-count admission. Initial capacity discharge and correspondence
with the authenticated whole canonical program image remain separate.
These proofs do not establish compiler, hash, gadget,
trace, or AIR correctness and add no production advice, FRI workloads, or keys.

### Bounded raw-advice loading and parser composition

`Aiur/Objects/Admission.lean` has 28 public kernel-checked lemmas and uses
the other-width allocation bound in `Objects/Store.lean`. `checkAdviceReader` binds
both branches of the actual `ib_read_advice`, including the I/O read, byte range
check, address/count updates, recursive Call, and exact Nil/Cons stores.
`checkLoader` binds the complete `ib_load` metadata lookup, UInt32 limit check,
assertion, Call, and return. `checkLoaderCode` resolves and checks both functions
in the same toplevel; full and pruned production compilations pass with relocated
indices. Input arity and block selectors are checked; evaluator-irrelevant
layout bookkeeping is not an AIR certificate.

`AdviceSlice` identifies a finite sequence of raw **field-valued** arena entries
at successive natural addresses. It assumes availability, not byte validity.
`checked_advice_eval` proves that the actual recursive reader succeeds exactly
when all consumed fields are below 256, otherwise failing at the byte range
check. `checked_load_eval` adds the length guard, whose assertion failure occurs
before byte reading. The corresponding Call contracts preserve caller registers
and perform exactly the modeled content-deduplicating stores. Standalone rejection
lemmas need neither a readable tail nor recursive-call fuel when the length guard
or next field already fails. Errors carry no post-state; no rollback is claimed.

The bounds are explicit: for `N` raw entries at `start`, `start + N < p`,
`N < 2^32`, and `limit + 1 < 2^32`, where `p` is the Goldilocks modulus.
The metadata lookup must identify that start and length. Body fuel `N` suffices
for the reader, `N + 1` for the loader, and `N + 2` for a loader Call. Extra
fuel is permitted. `checked_extended_load` instantiates the contract for the
actual `IOBuffer.extend` operation, including an already-populated channel;
it does not assume host conversion of the raw fields to UInt8.

With `bucketSize before 3 + N + 1 ≤ p`, `checked_load_admission` derives a
`ByteStream` from successful execution: the genuine-byte prefix plus its readable
Nil cell. No byte-validity premise or fresh-address assumption is used there.
Loading adds at most `N + 1` width-3 cells, preserves all prior successful reads
and all I/O, and leaves every other width bucket unchanged. Initial space is
still a premise; the theorem bounds growth rather than validating arbitrary
initial memory.

`loaded_declarations` composes successful loading with the actual declaration
reader at a byte sequence identified as a declaration prefix plus suffix.
The loader supplies the genuine-byte premise and preserves the initial width-13
space bound. Parsing accepts exactly valid arities and distinct full IDs,
establishes the semantic table, and preserves prior reads/I/O; invalid declarations
produce the proved assertion failure. The constructor count remains bounded
explicitly by sixteen. This is **not** a certificate for the `is_run` magic/revision,
entry/count prefix or its continuation, nor for canonical whole-program decoding,
function-table admission, digest binding, initialization, compiler, gadgets,
trace, or AIR correctness.

Forged-metadata regressions make the Lean-evaluator boundary concrete: natural
indices/lengths at `p` can wrap to zero on field conversion, a length of `2^32`
can pass the UInt32 guard and later fail I/O, and `limit = 2^32 - 1` wraps the
comparison's upper bound. These are not native-backend or AIR soundness claims;
they explain why the theorem cannot infer arbitrary natural metadata bounds
from this evaluator's cast-based comparison alone.

`Tests/Ixby/Aiur/Objects/Parser/Admission.lean` covers every byte value, full/pruned
compilations, exact and relaxed limits, nonzero arena offsets, full-field channel
keys, unread non-byte prefixes/suffixes, every invalid-field and truncation
position in a 33-entry arena, all declaration counts through sixteen, invalid
arities and duplicates after loading, fresh/deduplicated storage, caller/fuel
boundaries, certificate mutations, and forged metadata. The former forged
non-byte arity fixture now fails in the loader. No interpreter, compiler, wire
format, production advice, FRI workload, or key changes are involved.

### Actual program header and constructor-admission prefix

`Aiur/Objects/ProgramPrefix.lean` has 18 public kernel-checked lemmas.
`checkProgramPrefix` binds the input arity and exactly the first sixty
operations of the actual compiled `is_run`: four magic-byte checks, revision
zero, little-endian u32 entry and constructor count, the constructor-capacity
guard, and the declaration-reader Call. `checkProgramCode` resolves that
runner and all five declaration-reader dependencies in the same toplevel.
Full and pruned production compilations pass with their actual callee indices.
The remaining operations and final control are deliberately unrestricted.

`checked_header_eval` proves the actual sixteen-byte read and guards, preserving
all memory and I/O. Magic is exactly `IXBY`, revision is exactly four zero
bytes, and the genuine u32 count is accepted exactly when it is at most sixteen.
The count bound is a conclusion of the compiled check, not a premise. The entry
is retained as a full u32; its later function-table range check is not claimed
here. `group_header_bytes` represents every sixteen-byte sequence, including
malformed headers, and the word values agree with the existing little-endian
codec. Rejection of an invalid header occurs before the declaration Call and
requires no declaration bytes, table-space bound, or recursive-call fuel.

`checked_program_prefix` composes those checks with the complete declaration
reader. For an identified sequence of `N` records whose length equals the
header's count, it accepts exactly a valid header, supported arities, and distinct
full IDs. The uniform initial bound `bucketSize before 13 + 17 ≤ p` covers the
at-most-sixteen declarations plus Nil; stores may reuse existing cells.
Body fuel `N + 3`, with arbitrary extra fuel, suffices. Success establishes the
semantic table in wire order, preserves every prior readable cell and all I/O,
and adds at most `N + 1` width-13 cells.

The exact post-prefix map has 73 registers: program/input pointers at 0/1,
entry at 48, count at 65, table pointer at 71, and unconsumed suffix at 72.
`checked_program_continuation` passes this proved state to the original suffix
operations and control. It does **not** conclude that those operations succeed.
`loaded_program_prefix` supplies the genuine-byte premise from successful
checked advice loading under the earlier metadata/address and byte-space
bounds; it preserves the suffix's readable stream and initial reads/I/O.

`Tests/Ixby/Aiur/Objects/Parser/ProgramPrefix.lean` covers every magic-byte
value, every revision and entry bit, counts through sixteen and oversized u32
counts, all header truncation/tag positions, invalid declarations at every
position, exact new/deduplicated storage, full-field pointers, loader composition,
codec agreement, fuel boundaries, all prefix operations and required callees.
Positive suffix/control mutations and failing continuations explicitly test
the prefix-only certificate boundary. Initial/whole-admission resource
discharge, function-table admission, authenticated canonical whole-program
binding, initialization, full transitions, and compiler/hash/gadget/trace/AIR
refinement remain open. No production code, wire, advice, FRI workload, or key changes.

### Function-count and function/block header admission

`Aiur/Objects/CodeHeaders.lean` has 27 public kernel-checked lemmas. The
certificate extends the program prefix and checks both the complete zero branch
and a bounded nonzero prefix of each list reader. It also binds the exact next
Call, including its argument registers, output arity, callee index, and constraint
flag. `checkHeaderCode` resolves the earlier six functions plus the function and
block readers in one toplevel; full and pruned production compilations pass.

The proved prefixes stop before these next Calls:

| Actual body | Proved operations | Derived bounds | Next Call arguments | Post-prefix registers |
| --- | --- | --- | --- | --- |
| `is_run` | 83 | constructors ≤16; functions 1–8 | `is_read_functions [80, 89, 97]` | 98 |
| `is_read_functions`, nonzero | 60 | arity ≤16; blocks 1–64 | `is_read_blocks [54, 63, 2]` | 71 |
| `is_read_blocks`, nonzero | 19 | locals ≤64 | `is_read_instr [10, 2, 19]` | 25 |

The executable shape checks include those next Calls, so they bind 84, 61,
and 20 operations respectively. Later operations and final controls remain
unrestricted. The instruction target's existence, body, and semantics are
not certified here; `checkHeaderCode` is not a whole-image validator.

`checked_program_headers` composes the previous constructor-table proof with
the actual function-count read, upper-bound guard, nonzero guard, and self-zero
initialization. It derives the new count bound rather than assuming it. Success
retains program/input at registers 0/1, program entry at 48, constructor count
at 65, and constructor table at 71; function bytes start at 80, function count
is at 89, and self zero is at 97. `program_function_arguments` identifies the
exact next Call arguments. The original remaining body receives that precise
state; it can still reject or return an invalid result.

For nonzero list counts, `checked_function_header` reads twelve genuine bytes
and checks both arity limits, including the redundant local-capacity check,
then requires a nonempty block count at most 64. The full u32 function entry
is preserved without claiming it is a valid block index. Every twelve-byte
sequence has the proved header grouping. `checked_block_header` reads four
genuine bytes and enforces the local bound. Both contracts preserve all memory,
I/O, the remaining counter, and the full-field self value. One unit of body Call
fuel suffices; neither contract needs instruction/block payload bytes or an
allocation premise. Invalid headers reject before the next Call. Valid ones
pass their exact register state to the original continuation, not to an assumed
successful parser.

`checked_empty_list` covers both real zero-count branches: six ones for a
function-list Nil and thirteen for a block-list Nil. It proves exact stores,
outputs, caller-body registers, readable field-valued pointers, I/O preservation,
and preservation of every prior read under `bucketSize before width + 1 ≤ p`.
It requires no readable byte pointer or body Call fuel. Deduplication is allowed;
the block-list Nil can reuse the constructor-list Nil in the shared width-13
bucket. No rollback state is asserted on errors.

`loaded_program_headers` supplies genuine bytes from actual successful checked
advice loading, preserves the function-byte suffix stream and constructor table,
and derives both program counts under the earlier metadata/address, byte-space,
and initial constructor-space bounds. It does not require the suffix to contain
a valid function table. Initial/whole-admission allocation discharge remains open.

`Tests/Ixby/Aiur/Objects/Parser/CodeHeaders.lean` full/pruned cases exhaust
all 17 supported arities × 64 nonempty block counts and all 65 local counts,
exercise all entry bits and truncation/tag positions, and check exact Nil/new/
deduplicated state, both program counts, loader composition, full-field pointers,
codec-prefix agreement, and certificate mutations. Controlled continuations
demonstrate exact Call handoffs without implying successful downstream admission.
Forged non-byte arity/local words at `2^32` and count words at `2^32 + 1` can pass
the Lean evaluator's cast-based guards; the actual loader rejects those fixtures.
These document the genuine-byte premise, not native/AIR soundness claims.

The header contracts do not certify instruction decoding or complete recursive
block/function-table admission. The following scalar/operand contracts cover
leaf readers, not those larger obligations.

### Complete scalar and leaf-operand decoding

`Aiur/Objects/Scalars.lean` has 27 public kernel-checked lemmas and
`Aiur/Objects/Operands.lean` adds 13. Their structural certificates check the
complete bodies of `ib_field`, `ib_scalar`, and `ic_read_operand`, including all
operations, Call targets/arguments/output sizes/flags, match tags and ordering,
default branches, return selectors and every output register. The combined
bundle resolves those functions and `ib_byte` in the same bytecode toplevel;
it is tested against both full compilation and pruned, relocated indices.
Evaluator-irrelevant metadata is intentionally ignored. These are Lean bytecode
contracts, not a compiler, native implementation, gadget, or AIR soundness proof.

The field reader's eight inputs are genuine `UInt8` bytes, including encodings
at or above `p = 18446744069414584321`. `field_guard_exact` proves that the actual
emitted `gl_lt_p` arithmetic accepts exactly values below `p`: all four high bytes
being 255 requires all four low bytes to be zero. `packed_field_mod` separately
proves packing modulo `p`; `canonical_field_exact` removes that reduction only
after the guard. `field_bytes_codec` identifies the unreduced natural with the
existing little-endian codec helper. No canonical-input assumption hides rejection.

`checked_scalar_reader` covers every supported scalar form and rejects invalid
Boolean bytes or noncanonical field components. Both extension components are
checked independently. Unknown scalar tags fail before reading any payload.
Success yields the five-field `IBValue` followed by the exact suffix pointer:

| Wire scalar | Five-field output |
| --- | --- |
| Boolean | `[0, bit, 0, 0, 0]` |
| Word32 | `[1, byte0, byte1, byte2, byte3]` |
| Field | `[2, field, 0, 0, 0]` |
| Extension | `[3, component0, component1, 0, 0]` |

`scalar_flat_decoded` proves reconstruction through the concrete `decodeAtom`,
including its padding checks. Erasure is not an accepted standalone scalar wire
tag: the operand reader's erased branch produces the repeated-tag value instead.
Local operands produce `[0, index, 0, 0, 0, 0]`; literals prepend `1` to the
scalar layout; erased operands produce `[1, 4, 4, 4, 4, 4]`. The exact suffix is
the seventh result. `decodeOperand` checks these six-field layouts and reconstructs
the semantic operand; frame membership is a separate admission property.

`checked_operand_reader` accepts a local exactly when its genuine u32 index is
below the supplied u32 frame count. The count premise is explicit, with the
earlier checked block header supplying the stronger bound of 64. Literal and
erased branch lemmas do not require that frame-count bound. Invalid literal
payloads and unknown operand tags are rejected; the unknown branch does not read
the payload. These leaf readers allocate nothing and preserve memory and I/O.
Actual checked Call lemmas append exactly the returned fields to the original
caller registers. Sufficient uniform body fuel is `fuel + 1` for fields,
`fuel + 2` for scalars, and `fuel + 3` for operands, with one more for their Calls;
the simpler scalar and operand branches also have smaller exact fuel contracts.

`loaded_operand` composes actual successful checked advice loading with parsing
an identified operand prefix. It derives genuine bytes, proves the semantic
operand on success, and preserves the exact unconsumed byte stream, memory after
loading, original I/O, and all reads predating loading. The earlier metadata,
address, byte-space, length and limit premises remain explicit, as does the
u32 frame bound. It does not prove that this prefix occupies the right position
inside a canonical program. Errors carry no state; no rollback claim is made.

`Tests/Ixby/Aiur/Objects/Parser/Operands.lean` checks include all Boolean
bytes, all Word32 byte positions, all field boundary byte positions, paired
extension boundaries, local-count/index boundaries, codec differential checks,
every truncation/malformed-cell position in representative readers, minimum fuel,
actual Call failure modes, padding, unknown tags, and loaded valid/invalid operands.
Structural mutations bind every checked operation and dispatch edge; changing an
instruction implementation still passes the leaf certificate, documenting its scope.
Forged non-byte memory can pass raw Word/field readers or the cast-based local
guard while violating byte/representation premises. The actual loader rejects
every tested non-byte position. These fixtures are Lean evaluator diagnostics,
not claims about native execution or AIR constraints.

Next are operand-list and instruction decoding, complete recursive block/function
table construction, cross-table entry/target/arity validation, and authenticated
canonical whole-program binding. Initialization, full transitions, compiler/hash/
gadget/trace/AIR refinement, and whole-admission resource discharge remain separate.

### Compiler issue found and repaired

The shared `Source.Term.hoistLets` repair and all three regenerated native
kernels landed upstream in [PR #628](https://github.com/argumentcomputer/ix/pull/628).
The current IxBy branch depends on that change; its diff against `main` has no
production Aiur compiler or Rust-kernel changes.

The original bug hoisted a continuation's shadowing binding across an assertion.
With both program and input tails named `rest`, compiled execution checked the
input tail twice and accepted trailing program bytes, while source execution
rejected them. The repaired [normalizer](../Ix/Aiur/Stages/Source.lean) freshens
caller/callee scopes, sequences strict arguments, and preserves assertion/I/O
order. The object entry again uses the original shadowed names, and matching-
commitment regressions reject trailing bytes 0, 1, and 255 in source and native
execution.

[Hoisting regressions](../Tests/Aiur/Hoisting.lean) retain additional scope,
evaluation-order, failure-stage, and independent proof-round-trip coverage
beyond the tests ported upstream. This is regression evidence, not a compiler
correctness theorem. Future compiler changes require regenerating kernels and
rebuilding native test binaries; a content check alone cannot refresh an
already linked executable.

```sh
lake build --wfail IxTests ix
lake exe ix codegen --check
RAYON_NUM_THREADS=8 .lake/build/bin/IxTests --ignored ixvm
RAYON_NUM_THREADS=8 .lake/build/bin/IxTests recursive-verifier ix-aggr
```

## Reproduction and coverage

```sh
lake build --wfail Ix.Ixby.Audit Tests.Ixby.Audit IxbyObjectsTests \
  IxbyObjectsMemoryTests IxbyObjectsTableTests IxbyObjectsParserTests
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyObjectsMemoryTests
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyObjectsTableTests
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyObjectsParserTests
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyObjectsTests
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyObjectsTests --execute-only
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyObjectsTests --stats
```

`System.buildObjects commitmentParameters friParameters` selects this
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
The memory, table, and parser suites contain 126, 191, and 23,832 checks.
Across the reference/crypto/codec, conformance, and proof-enabled scalar/control/
object suites, current IxBy coverage is **25,383 runtime checks**, including
155 proved workloads. These counts exclude kernel theorems and the separate
hoisting regressions.

All suites use LSpec and defer compilation/check construction until selection.
The parser facade compiles the full and pruned interpreters once and passes them
to its focused component modules; splitting tests does not multiply compilation.
The shared backend harness preserves expected-statement binding, independent
verifier construction, checked proof decoding, and key-stability checks. The
object suite separately enforces rejection stages and explicit reference results.

`Tests/Main.lean` exposes execution-only `ixby-objects`, opt-in
`ixby-objects-prove`, and the three conformance selectors above. The merge-queue
matrix selects all three IxBy proving suites and `aiur-hoisting-prove`.
The theorem trust gate and its negative checks also run in regular CI.

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

## Remaining proof obligations

- Certify operand-list and instruction decoding, recursive block/function-table
  construction, and cross-table entry/target/arity validation.
- Bind those tables and identified byte prefixes to the authenticated canonical
  whole program, discharging initial and whole-admission resource bounds.
- Establish valid live references from initialization and preserve successful
  reconstruction and reference execution through every interpreter transition.
- Prove compiler, primitive/hash gadget, native trace, lookup/memory, and AIR
  refinement under explicit cryptographic assumptions.

The loader and checked headers discharge the local byte/count premises stated
above; leaf readers supply exact layouts and Call contracts. None establishes
the complete whole-program or execution-soundness bridge. Continue hostile-
witness analysis before expanding to closures/PAPs, general application, and
the remaining byte/crypto operations. Full verifier workloads and certified
Compilatrix integration remain separate work.
