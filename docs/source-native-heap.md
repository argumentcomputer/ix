# Compositional allocating CFG selection

The `physical-leaf-cfg/1` attachment selects bounded allocating **physical
IxIR₂ CFGs** and emits certified x86-64 ELF. Allocation, reuse, parallel edge
copies, joins, and nonrecursive direct calls compose through instruction and
function certificates. Caller values and reuse reservations can survive an
allocating callee. The native result is a scalar, and every allocated cell
and outstanding reservation is reclaimed before return.

[`PhysicalHeap.compileSourceExport`](../Compilatrix/X86/PhysicalHeapExport.lean)
consumes an ordinary validated source attachment and follows its uncaptured
module export. The universal
[`Exported.sourceNatReturns`](../Compilatrix/X86/PhysicalHeapSourceObject.lean)
theorem derives actual IxIR₁ closure application, physical invocation, and
execution of the emitted ELF from successful Ixon runtime application. It
proves `word.toNat = sourceNat`, exact counters, reclamation, caller-register
restoration, and preservation of every byte outside the finite workspace.
Its premises are the retained checked compilation and selection, successful
source entry/application, the existing sharing/oracle conditions, Word
arguments of the right arity, and the workspace ABI below. Lower-level
execution certificates and callee summaries are conclusions of the proof.

## Admitted fragment

| Boundary | Contract |
| --- | --- |
| Root values | Zero, one, or two exact unsigned 64-bit Nat arguments; one scalar Nat result. Source exports have one or two runtime arguments. |
| Internal values | Exact Word scalars, erased values, and owned leaf pointers. Helpers can accept or return leaves. |
| Leaves | At most two scalar Nat fields; unique ownership or a shared node with reference count one. No pointer fields or duplicated node owners. |
| Instructions | Moves, scalar/erased retains, release/drop, allocation, fetch, unique take/free, shared reset, credit reuse, discard, and direct calls. |
| Edges | Simultaneous value and credit transfers, permutations, joins, and a predecessor Nat prepended on successor edges. |
| Branches | Exact zero/predecessor Nat peeling; one-constructor switches; the present arm of a credit branch whose reservation is known live. |
| Calls | Nonrecursive calls to earlier checked parameter profiles. Both physical `call` and `tailCall` use a real native CALL and a restoring epilogue. |
| Ownership | All function parameters are owned. Borrowed parameters, shared-node retains, nested heaps, and remaining owners/credits at scalar return are rejected. |

There is no primitive addition in this fragment. Positive Nat peeling
subtracts one exactly; zero takes its separate edge. Literals and runtime
arguments must fit a Word, so successful results do not wrap. General
arithmetic overflow remains the separate
[scalar arithmetic attachment](source-native-scalar.md)'s contract.

The selector bounds value positions to 16, credit positions to four, and
simultaneous transfers to 12 staged copies. Each activation has 32 spill
slots. Source functions have at most 128 blocks and 128 instructions per
block; expansion has depth 128 and a shared 4,096-point work budget. There
are at most 32 constructor identities and 32 admitted function profiles,
including separate scalar/node/erased profiles for the same declaration.
Each profile has at most two parameters. Calls and CFG expansion are acyclic;
non-topological block numbering and joins are allowed. The root's conservative
bound is at most 64 fresh allocations and 1,048,576 physical control steps.
Joins may duplicate native continuations; this pass does not optimize them.

Selection proves successful-run preservation, not termination of arbitrary
source programs. A single-constructor switch and a known-present credit
branch need no native tag test under that contract. The public snapshot path
also requires the ordinary complete ownership validator. Other declarations
can be outside the selected fragment; discovery conservatively follows calls
in every block of each selected declaration. PAP creation, higher-order
application, externs, recursion, runtime captures, and general occupied input
heaps remain outside the selected body.

## Workspace ABI

The exported symbol is `compilatrix_heap_cfg`. RDI and RSI hold the scalar
arguments, RDX initially holds the workspace base, and RSP points to the
external return-address word at the top of that workspace. A caller must
install this stack; an ordinary C call on an unrelated stack does not meet
the ABI. On return, RAX holds the result, RDX is zero, the System V saved
registers are restored, and RET advances RSP by eight bytes.

[`HeapArena.Workspace`](../Compilatrix/X86/HeapWorkspace.lean) is one aligned,
nonwrapping readable/writable region of **`8 * (272 + 34 * D + 2)` bytes**,
where `D > selected entry index`. Its base is 16-byte aligned. The first 272
words hold a 16-word header and 64 four-word leaf cells. Each activation
above the arena has 32 spill words, saved RBP, and a native return word. The
last two workspace words hold saved R15 and the external return address.
The adapter saves R15 before installing the arena base. The depth bound
counts admitted parameter profiles and can exceed the actual call depth.

| Header word | Meaning after successful return |
| --- | --- |
| 0 | Cursor in bytes: `32 * fresh cells used` |
| 1 | Caller-supplied capacity in cells, unchanged |
| 2–5 | Exact allocation, free, reuse, and RC-operation counts |
| 6–8 | Exact reset attempts, hot resets, and reused payload units |
| 9 | Outstanding reservations, zero |
| 10–15 | Unchanged caller words |

A cell has a free/reserved/live tag, two field words, and a padding word.
Every used cell's tag is zero at return. The cursor never exceeds the
selected allocation demand. Fresh allocation advances the cursor; only an
explicit credit reuses a cell. Freed cells are not placed on a general free
list, and this bound makes no fragmentation claim.

The source adapter accounts for the consumed exported PAP with an initial
allocation/free/RC count of one. That dead IxIR₁ slot occupies no native leaf
cell. Raw physical snapshots start at zero. These are exact resource
observations, including the source application prefix, not truncated Word
approximations. The selected control bound proves the counters cannot wrap.

The entry guard requires `allocation demand ≤ header[1] ≤ 64`. An invalid
capacity returns RAX zero and RDX one before initializing the arena or
entering an activation. [`Compiled.rejectsCapacity`](../Compilatrix/X86/HeapReject.lean)
proves actual ELF return, caller restoration, unchanged heap words, and
unchanged outside bytes. The gate additionally compares every workspace word
on rejection. Mapping/alignment are ABI premises; this entry does not probe
or allocate the mapping. Missing or unwritable activation memory traps in
the executable model and has separate negative checks.

## Proof and identity

`PrimitiveCode` and `Code` retain syntax, schema, kind, placement, edge, and
callee evidence without runtime input. The simulation relates physical
owners, reservations, scalar fields, heap counters, and suspended callers
to native memory. `Code.simulate` composes the actual instruction/edge/call
steps; `Output.summaries` closes the induction over earlier callees.
`Output.physicalReturns` starts from a successful physical invocation and
derives finite workspace execution and complete reclamation.

The fixed spill placement is the first delivered A1 slice.
[`HeapCopies`](../Compilatrix/X86/HeapCopies.lean) proves staging followed by
commit implements simultaneous copies without destroying sources. The call
proof preserves caller slots and suspended credits while a callee uses a
disjoint activation and the common arena. The proof composes through checked
prologues, epilogues, instruction streams, and the complete parsed ELF
interpreter. A general register allocator and its validator remain future
work.

[`Compiled.policyReturns`](../Compilatrix/X86/PhysicalHeapObject.lean) handles
`suspendedCallsV1` physical execution. `Compiled.physicalReturns` transports
the existing baseline run into that policy. The shared source-application
bridge derives the actual PAP dispatch and invocation from the retained
source compilation; source theorems then use the physical-to-object result.
`SourceResult` retains the source value relation, actual IxIR₁ application
and invocation, and the final heap observation.

Objects use the **complete canonical IxIR₂ artifact root**, with the ELF
provenance kind `ixir2`. The root binds every function body, schema, layout
preimage, dependency, and policy field through the
[I2 snapshot format](ixir2-wire.md). `compileSnapshot` and
`compileSnapshotExport` consume checked decoded artifacts. The independent
reload executable receives only persisted bytes, root, entry, and mode;
it does not import the source fixture module or regenerate a source program.

Fourteen axiom fences cover copies, calls, physical simulation, source-to-ELF,
and rejection. Twelve use the ordinary `propext`, `Classical.choice`, and
`Quot.sound` basis; the two source endpoints retain the existing compiler
Blake3 boundary. No new axiom or native interface is introduced. The local
reference ISA, immutable executable-text model, system linker/loader, and
compiler/runtime seed retain their existing trust obligations.

## Reproduction and evidence

```sh
lake build source-native-heap heap-snapshot-object check-source-native-heap
.lake/build/bin/check-source-native-heap \
  --fixture .lake/build/bin/source-native-heap \
  --consumer .lake/build/bin/heap-snapshot-object \
  --cc cc --harness fixtures/source-native-heap/native_harness.c
```

| Family | Origin and exercised behavior | Result on `(a,b)` | Fresh cell demand |
| --- | --- | --- | --- |
| `leaf-call` | Source builder returns a unique leaf to a consuming helper | `a` | 1 |
| `branch-call` | Source Nat branches call allocating/consuming helpers | `a = 0 ? b : a - 1` | 1 |
| `caller-live` | Source caller retains a leaf across a Nat helper | `a - 1` | 1 |
| `nested-alloc` | Source caller retains a leaf while another helper allocates | `a` | 2 |
| `shared-pair` | Source allocates two runtime fields, projects, and releases | `b` | 1 |
| `unique-diamond` | Physical take, suspended credit, allocating call, permutations, join, reuse | `a = 0 ? b : a - 1` | 2 |
| `hot-credit` | Physical reset, suspended credit, allocating call, present branch, reuse/reset/discard | `a` | 2 |
| `leaf-switch` | Physical constructor branch, take, and credit discard | `a` | 1 |
| `arena-limit` | Physical nested calls use exactly the 64-cell limit | `a` | 64 |

Five synthetic Ixon sources pass through the ordinary compiler. Their 95
boundary applications compare Ixon, IxIR₀, IxIR₁, physical IxIR₂, typed x86,
and actual parsed ELF execution, including maximum Words. Four additional
physical fixtures supply the reuse/credit/join cases that the ordinary
source lowering does not yet produce. All nine yield 171 object runs,
roundtrip complete snapshots, and reproduce byte-identical ELF in separate
consumer processes.

The gate rejects 19 unsupported CFGs, two legacy call-local credit policies,
27 changed frame/guard/stream certificates, and 43 insufficient-capacity or
workspace cases. Its independent Lean decoder and artifact oracle import no
compiler, selector, encoder, or evaluator. They check full snapshot contents,
layout hashes, source/export bindings, ELF structure/provenance, profile
maps, fixed arithmetic/resource formulas, and 182 deliberate corruptions.
Two fresh producers must agree on all 28 files; the reviewed report prevents
identical producer corruption from becoming a new expectation. The reload
consumer rejects another 36 corrupt byte/root/entry inputs.

On x86-64 Linux, a C oracle makes **774 linked native calls**: 19 boundary,
64 deterministic random, and three rejected-capacity inputs per object. It
checks exact counters, complete reclamation, reused fields, saved registers
before the bridge restores them, caller frames, stack restoration, unused
words, and a guarded workspace. Other configured platforms run artifact and
modeled-execution checks without claiming native execution. The Nix gate is
`source-native-heap`; this is correctness evidence, not a performance study.
