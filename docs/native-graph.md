# Shared selection and native certificates

Physical heap and source object compilation now preserve joins through
selection, native emission, and certificate checking. The object APIs default
to `HeapTarget.Emission.graph`, policy `heap-cfg-graph/1`. The previous `.shared`
and `.tree` paths remain selectable with their original selector and artifacts.

For the fixed checked IxIR₂ join family, the graph path admits 42 joins. At
eight joins it selects 33 nodes and checks 33 native certificate rows; the
previous shared emitter selects and checks a tree of 1,276 nodes. Both produce
the same 47 native blocks and identical ELF bytes. At 42 joins the graph has
169 nodes, 210 edges, depth 127, and 217 native blocks. The 43-join input has
130 source blocks and exceeds the unchanged 128-block source bound.

See the [reference measurements](performance/native-graph-2026-09-12/README.md)
for phase costs, representation sizes, process memory, and retained replay.
This scaling family begins at checked IxIR₂. The separate allocating source
and physical CFG fixtures exercise ownership, calls, copies, and workspace
preservation through the same graph compiler.

## Selection and resource bounds

[`PhysicalHeap.Graph`](../Compilatrix/X86/PhysicalHeapGraph.lean) represents
nodes with explicit child indices. A context contains the source block,
instruction position, and complete scope: available and consumed value kinds
plus live credit layout identities. The cache is separate for each function
and parameter profile. Hashes choose buckets; full context equality chooses
an entry. Neither hash injectivity nor cache correctness is a proof premise.

The [proposer](../Compilatrix/X86/PhysicalHeapGraphBuild.lean) discovers nodes
in dependency order and detects active contexts. The independent
[node checker](../Compilatrix/X86/PhysicalHeapGraphCheck.lean) selects the actual
source instruction, checks the proposed operation and every child's exact
context, and requires children to precede their parent. Duplicate contexts,
forward/missing references, incompatible branch results, and wrong ownership
scopes are rejected. Return, call, primitive, constructor, and credit-branch
checks retain the existing source semantics.

Each node caches its result kind, allocation demand, physical control bound,
and depth. The allocation/control formulas are proved equal to those used
by the existing simulation. Branch demand uses a maximum; calls include the
earlier callee's summary. A cached child still contributes its full depth,
including when reached along a longer path.

Default graph budgets per profile are 4,096 nodes, 8,192 edges, and depth 128.
These count the graph rather than unfolded paths. Source functions still have
at most 128 blocks and 128 instructions per block. The limits of 32 profiles,
32 constructor identities, two arguments, 16 value slots, four credit slots,
twelve staged copies, 64 allocations, and 1,048,576 physical control steps
remain. General recursion and cyclic CFGs remain outside this slice.

## Native certificate and proof reuse

[`HeapGraph`](../Compilatrix/X86/HeapGraph.lean) emits and checks one native
certificate row per selected node. Each row supplies native block references;
the selected node supplies its operation and child indices. Local checks
cover the complete instruction list, operand/slot validity, simultaneous
copies, branch transfers, callee entries, prologues, epilogues, and capacity
adapter. Complete function/node coverage and function order are checked.
`checkCandidate_program` pins the exact proposed native program.

The implementation constructs one existing `Tree` constructor per source
node and one existing `Plan` constructor per checked native row, referring to
already constructed children. These values share memory. The new compiler
uses graph indices and summaries; it does not recursively compute `Tree.nodes`,
allocation/control summaries, `Plan.tree`, tree equality, or `Plan.matches`.
The corresponding recursive verification facts follow from the checked local
facts in erased proofs. Calling legacy recursive inspectors on these values
can still expand their logical trees; graph inspection avoids that traversal.

The result has the existing `HeapTarget.Output` and `PhysicalHeap.Compiled`
types. Their physical and source-to-ELF theorems, caller ownership, suspended
credits, exact counters, reclamation, saved registers, finite workspace,
outside-memory preservation, and capacity rejection apply without changing
their statements. The new graph checker fences use `propext`, `Classical.choice`,
and `Quot.sound`, the existing physical proof basis. Source composition retains
its existing BLAKE3 boundary. No axiom, allocator, ABI, or native interface is
added.

## API and replay

`PhysicalHeap.compile`, `compileSnapshot`, `compileExport`,
`compileSnapshotExport`, and `compileSourceExport` take
`emission := .graph` and `graphLimits := {}` by default. Pass `.shared` for the
previous shared emitter with tree selection, or `.tree` for original tree
emission. Graph limits apply to the graph path. The low-level graph entry
points are `PhysicalHeap.Graph.select`, `HeapGraph.emitCandidate`, and
`HeapGraph.checkCandidate`.

The persisted-only consumer keeps its legacy tree default:

```sh
heap-snapshot-object SNAPSHOT ROOT ENTRY source|physical|export OUTPUT graph
```

Append `--name SYMBOL` when needed. The consumer validates canonical snapshot
bytes, reconstructs and checks the graph, and emits the exact object.
Provenance continues to bind the input snapshot. Reports identify the compiler
strategy separately; shared and graph compilation can produce identical
object identities.

The benchmark retains `.selection.json` and `.plan.json` inspection files,
their byte sizes and hashes. They expose graph structure and native references
without expanding trees. They are diagnostic formats, not stable certificate
codecs or proof recovery inputs. Retained replay uses canonical IxIR₂ bytes
and the ordinary compiler checker.

## Validation and limits

The `native-graph` Nix gate compares two fresh ten-object runs with reviewed
artifacts. It includes shared/graph pairs at 2, 8, and 9 joins, then graph-only
10, 16, 32, and 42. It checks physical, typed native, parsed ELF, persisted-only
recompilation, complete file identity, and 330 guarded linked calls. Independent
inspection rejects 80 corruptions. Every source point and native block/node
also receives mutations through the ordinary compiler checkers.

Exact graph limits admit 42 joins; lowering each node, edge, or depth budget
by one rejects it. A separately proposed eight-join graph exercises the longer
cached-path depth check. Another fixture reaches the same source block with
scalar and owning-node scopes, checks both distinct continuations, and verifies
four executions with exact counters and caller restoration.

The allocating heap gate runs graph mode over five ordinary source and four
physical fixtures: 95 source applications, 171 ELF executions, nine persisted
reloads, and 774 linked calls. Their artifacts match the previous shared
goldens. The graph selector retains eighteen prior admission rejections and
admits the thirteen-join fixture previously rejected for expansion. The legacy
nineteen-rejection audit still runs.

This change addresses selected graph and certificate growth. It does not
establish linear whole-compiler complexity: source discovery/profile finishing,
encoding/checking, snapshot processing, and legacy consumers retain their own
costs and bounds. The emitted bytes on overlapping inputs are unchanged, so
no runtime throughput improvement is claimed.
