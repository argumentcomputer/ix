# Borrowed functions with runtime arguments

B2 selects borrowed entries from an accepted source function before the caller
supplies an argument. Structural proofs cover every admitted runtime heap,
including arbitrary shared descendants. At the exported owned entry, borrowing
saves exactly two executed RC operations, fully reclaims the input, and
preserves peak live heap use. The wrapper adds one control transition.

Nine synthetic Ixon functions exercise zero through eight forwarding calls.
Each compiled artifact serves eight runtime inputs through both a direct call
and an owned PAP application: 144 baseline/borrowed comparisons. The finite
matrix checks the implementation; selection and the universal preservation
theorems do not use it.

## Source and selection

[`Borrow.Runtime.compileValidated`](../Compilatrix/Borrow/Runtime.lean) runs
the ordinary validated source compiler, retains its entire attachment, and
applies `Borrow.Runtime.select`. The selector accepts an existing attachment
as well. Invalid source is a compiler error. Every optional rejection returns
the exact checked baseline.

The [source generator](../Compilatrix/Borrow/RuntimeSource.lean) exports B1's
shared tag-reading function without its closed application. Five canonical
Ixon constants contain the declaration group and projections; the only scalar
literals are the branch results 11 and 22. No runtime argument is embedded in
the source or supplied to selection. The function reads the outer constructor
tag twice through an acyclic chain. Zero returns 11; successor returns 22 and
fetches its field without inspecting its contents. This remains a synthetic
source family and does not claim further upstream or Std acceptance.

The selector reuses B1's bounded inference and exact whole-program rewrite.
[`OpenCheck`](../Compilatrix/IxIR2/Borrow/OpenCheck.lean) additionally checks:

- every inferred parameter summary, baseline body, borrowed body, and original
  owned wrapper against inductively recognized reader/forward/twice shapes;
- every callee lookup in those bodies, equal structural depth and result
  schema, and complete coverage of the proposed summary set;
- the unchanged nullary module export and PAP factory, still exporting the
  original owned entry, and an exported body with a proved RC benefit.

The source checker recognizes the corresponding graph in the actual compiler's
raw erased declarations, using the same branch results and chain depth. It
derives source function/application behavior by induction. Target recognition
similarly constructs function proofs; neither side requests a simulation
callback or evaluates a supplied input.

Default limits are 32 candidates, 16 rounds, 256 inference attempts, and 32
units of source and target structural depth. These bound compiler/checker
work, not argument size or runtime fuel. Fixture depth `d` produces `d + 2`
summaries and attempts over two rounds. Disabled selection, exhausted
inference, and exhausted source or target structural recognition all retain
the complete baseline. General recursive SCCs, mixed or multiple parameters,
effects, and allocating reader bodies remain outside this structural family.

## Input and lifetime contracts

[`Open.Input`](../Compilatrix/IxIR2/Borrow/OpenResources.lean) states the
owned-entry contract: the argument points to a shared zero node with no fields
or a shared successor node with one arbitrary runtime value. The entire heap
has `RootOwnership` under that one external shared root and satisfies the
allocation-order invariant. Allocation accounting is balanced and the saved
peak is at least the current live-node count. Descendants can be shared DAGs;
there is no bound on their size in the theorem.

The complete-reclamation result uses this whole-heap ownership contract.
It does not promise to free separately owned caller data. Borrowed-entry
lifetime preservation has a broader domain: it needs only the constructor
view in the caller's store and supports other roots and aliases.

[`OpenControl`](../Compilatrix/IxIR2/Borrow/OpenControl.lean) and
[`OpenSim`](../Compilatrix/IxIR2/Borrow/OpenSim.lean) derive actual `Eval.Step`
and `Eval.Steps` paths for the reader, each forwarding call, the repeated read,
and the owned wrapper. They support halting or resuming a saved caller with
an arbitrary remaining continuation stack. Every borrowed prefix preserves
the exact store, including fields, refcounts, and resource counters. Lender
ownership and constructor-view facts therefore remain available after return
for a later take/reset. A positive checked caller borrows, then performs a
hot reset and complete release; local tail-lender death and reset-dependent
borrow candidates remain rejected.

For owned calls, the proofs first cancel the baseline retain/release pair
against the actual heap worker. Existing root-ownership reclamation constructs
sufficient final deep-release fuel internally. The baseline and optimized
outputs are identical except for exactly two RC ticks. Both have zero live
nodes, equal allocation/free counters, and every heap slot empty. Neither
execution allocates, so the entry's existing peak remains unchanged. This
counts live heap nodes; occupied bytes and stack capacity retain the F1 gate.

[`RuntimeInput`](../Compilatrix/Borrow/RuntimeInput.lean) gives a constructive
caller adapter for every finite zero/successor chain with an arbitrary Nat
scalar leaf. `Argument.input` proves the required ownership and ordering;
`Tree.counts` proves its allocation, live-node, and peak counts. This adapter is
separate from compilation. The abstract input theorem also admits heaps beyond
those constructed by the adapter.

## Public preservation interfaces

[`RuntimeSim`](../Compilatrix/Borrow/RuntimeSim.lean) projects the erasure
certificate from the actual validated source attachment, including mutual
member scope, and composes source application with the structural target
proof. Its source premises remain the existing oracle relation, sharing
well-formedness, represented argument, and successful Ixon evaluation and
application. No function simulation is assumed. Only the outer tag/arity must
correspond across the source and target payloads because the function does not
observe the field's contents.

The principal interfaces are:

- `Open.Entry.steps`, `lenderLifetime`, and `total`: reusable calls and
  continuations, exact-store borrowed prefixes, and constructed owned runs
  with complete reclamation.
- `Open.Certificate.strictImprovement`, `controlCost`, and `runFunctions`:
  two fewer RC operations, one additional owned-entry control transition,
  and successful public runner equations on every admitted heap.
- `Runtime.Source.Shape.applies`: total erased-source behavior for every
  admitted argument, derived from the checked graph.
- `Runtime.Certified.sourcePreservation`, `runtimePreservation`, and
  `sourceToRuntime`: original-source agreement, actual target paths, and a
  composed theorem for both `Eval.runFunction` results and their resources.
- `Runtime.Selection.valid` and `fallbackExact`: checked selection and exact
  baseline retention on every optional failure.

Fifteen new [axiom fences](../Compilatrix/Fence.lean) cover these interfaces,
the heap cancellation law, and input construction/counts. Ten use only the
existing logical axioms; five indexed source interfaces also retain the
existing addressed-source BLAKE3 dependency. There is no new axiom, native
reflection proof, FFI, oracle, or runtime assumption.

## Measured costs

For the caller-built chain matrix, let `d` be forwarding depth, `K` the number
of input heap nodes, `s` be 0 for zero or 1 for successor, and `q` be 1 when the
chain ends in a scalar leaf, otherwise 0. Allocation counts include building
the argument outside the function. RC counts begin at zero after construction.

| Owned direct entry | Baseline | Borrowed |
| --- | ---: | ---: |
| Result | `11 + 11s` | `11 + 11s` |
| RC operations | `K + 2` | `K` |
| Allocations / frees | `K / K` | `K / K` |
| Final live nodes | 0 | 0 |
| Peak live heap nodes | `K` | `K` |
| Control transitions | `2d + 10 + 2s` | `2d + 11 + 2s` |
| Heap-work units | `K + q + 2` | `K + q + 1` |
| Stored declarations | `d + 4` | `2d + 6` |
| Stored blocks | `d + 7` | `2d + 9` |
| Stored instructions | 7 | `2d + 9` |

The dynamic PAP caller adds one allocation/free, one RC operation, one
heap-work unit, three control transitions, and one peak live node to both
paths. Its caller declaration is separate from the stored compiled-program
size table. The owned export and PAP factory remain checked parts of the
compiled artifact.

Runtime inputs include zero, scalar payloads 0, 1, and `2^256 + 19`, constructor
chains of 2, 9, and 33 nodes, and a 17-node chain ending in scalar 4096.
Direct RC counts range from 3→1 to 35→33. A separate nine-node input with
three external root aliases exercises each borrowed entry. All its prefixes
preserve the store; the caller subsequently releases all three owners and
reclaims the heap. The universal two-tick difference applies more broadly
than the chain-specific absolute cost formulas in the table.

The producer prints compilation and structural checking times separately from
deterministic artifacts. Representative local runs for all nine functions
took 8–12 ms to compile and 2–4 ms to check. Complete diagnostic snapshots, with
all execution prefixes, total about 19 MiB. These measurements do not establish
a native latency improvement. The actual scalar x86 selector rejects both
programs at `missingConstructorSchema`; native shared RC and borrowed calls
remain unsupported, so there is no same-family native measurement.

## Reproducibility and rejection gate

```sh
lake build source-borrow-runtime check-source-borrow-runtime
./.lake/build/bin/check-source-borrow-runtime \
  --fixture .lake/build/bin/source-borrow-runtime
```

The producer compiles/selects each function once per process, then supplies
all its arguments. It records original Ixon and raw erased-source application
results, complete compiler attachments, summaries and validation work, initial
caller heaps, both actual target outcomes, and every physical execution
prefix for direct/PAP calls and aliased lenders.
These observations use 1,000 source, control, and heap-work units; those test
budgets are absent from the selecting compiler's interface.

The [independent checker](../scripts/CheckSourceBorrowRuntime.lean) compares all
ten files from two fresh processes, checks pinned source/export roots and
constant-byte hashes, independently reconstructs every borrowed body and
wrapper, constructs each input heap from the argument description, and runs
a separate interpreter over every frame, continuation, heap slot, and work
counter. It imports no compiler, optimizer, validator, or evaluator.

Eight structural/lifetime guards retain all twelve B1 ownership/resource
negatives. Four source fallback policies apply to each of the nine functions.
Twenty deliberate artifact corruptions must fail, including altered wrappers,
borrowed signatures, initial ownership, registers and deep-release work,
aliased-lender refcounts, resources, source bytes, and fallback programs.
The checker, helper, and [reviewed matrix](../fixtures/source-borrow-runtime/expected.json)
are integrity-pinned; the `source-borrow-runtime` Nix check runs the gate.

The 2026-09-08 delivery passed the 686-job local build, all thirteen compiled
regression gates, and all fifteen Nix checks on x86_64 Linux.
