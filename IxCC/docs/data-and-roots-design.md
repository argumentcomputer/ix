# Data, roots and effects

Written 2026-11-09. **Status: planned**, except where a line says
*implemented*. This document designs the data the compiler must support
beyond `Nat` and first-order constructors (DR1–DR5), the interface of compiled
roots and compile claims (DR6–DR8), and effects (DR9). Bignums have their own
[design](bignum-design.md), closures theirs ([closures](closures-design.md)),
and the semantic obligations theirs ([certification](certification-design.md)).
The [roadmap](roadmap.md) owns the phases and exit criteria.

Every item states the motivating target, the current state, the options and
a recommendation, the proof obligation, the effect on the trusted base, its
dependencies, a size marked as an estimate, and an exit criterion.

Sizes are estimates in lines of Lean (code plus proof). Their basis is the
size of the nearest existing IxCC component (measured with `wc` on
2026-11-09: `Fir/` 3.8k, `Own/` 9.5k of which `Own/Plain/` 6.1k, `Cfg/Rc/` and
`Rt/Rc/` 28.6k together, `Rt/` 21.9k), scaled by the number of operations
or rules each item adds.

## DR1. Heap completion

**Status: in progress** (Phase 2). The bounded plain-RC route is
implemented; the rest is planned.

**Motivation.** K2 and K3 (lists and trees), every flagship, and the cells
that closures (P8), arrays and bignums need.

**Current state.**
- *Implemented.* Immortal cells, bump-allocated and never freed
  ([`Rt/Layout.lean`](../IxCC/Rt/Layout.lean)).
- *Implemented.* The plain-RC route: shared constructors with 1 to 254
  fully scanned fields and tags up to `Rt.maxTag`, every one whose layout
  the counted heap allocates (`CellLayout.ok` of `CellLayout.ofFields`,
  [`Cfg/Rc/Native.lean:62`, `:81`](../IxCC/Cfg/Rc/Native.lean)); 71
  size classes with free lists, one-cell bump refill, allocation by layout
  and the general iterative release
  ([`Rt/Rc/Gen/Procs.lean`](../IxCC/Rt/Rc/Gen/Procs.lean), below); the
  ownership checker, which admits any placement of `inc` and `dec` it can
  type (heap stage 2, below; the producer writes the canonical one);
  `Plain.checked_program_refines`
  ([`Own/Plain/Proof/Candidate.lean:12`](../IxCC/Own/Plain/Proof/Candidate.lean))
  and the object theorem `Recheck.RcReplay.sound`
  ([`Recheck/Rc/Proof/ObjectSound.lean:37`](../IxCC/Recheck/Rc/Proof/ObjectSound.lean)).
  `List.reverse` from Lean's library compiles and runs through it
  ([`fixtures/rc/real-source`](../fixtures/rc/real-source/README.md)).
- *Implemented (heap stage 1).* The runtime of general cell layouts and
  the pipeline's switch to it: 71 size classes and cell layouts
  ([`Rt/Rc/Classes.lean`](../IxCC/Rt/Rc/Classes.lean): `classWords`, the
  least fitting class `classFor` with `classFor_spec` and its waste
  bounds); allocation by layout, the general release and the uniqueness
  test ([`Rt/Rc/Gen/Procs.lean`](../IxCC/Rt/Rc/Gen/Procs.lean),
  [compiler design, "Runtime"](compiler-design.md#runtime)); and their
  proofs over a general heap invariant (`Rt/Rc/Gen/Proof/`, 97 modules):
  `AllocatorReady.reserve_total`, `release_caller_complete(_frame)`,
  `increment_caller_complete`, `Init.cxInit_ready` (all 71 free-list heads
  recorded), `isUnique_spec` (the test answers `Own.Rc.uniqueOf` and writes
  nothing), `Procs.LiveCell.toGen`, `Procs.HeapLive.toGen` (the bounded
  route's cells are cells of the general invariant), and the facts of the
  fully scanned cells the pipeline allocates (`Gen/Proof/Scanned.lean`:
  `fieldsClass n`, classes 2–44), and the in-place reuse lemmas
  ([below](#in-place-reuse)). 301 exact axiom fences
  (`IxCCTests/Fences/RtRcGen/`). The pipeline emits `Gen.alloc` and
  `Gen.dec` for every plain-RC program; the proof bridge's `HeapState`
  carries `Gen.AllocatorReady maxClass`
  ([`Cfg/Rc/Proof/Native/Activation.lean`](../IxCC/Cfg/Rc/Proof/Native/Activation.lean)),
  and the readback and projection facts take the heap's cells to be fully
  scanned (`Readback.Scanned`, `CtorOk.scanned`: the constructor table has
  no scalar field yet). The bounded route's release `Rt.Rc.Procs.dec` and
  its proofs (`Rt/Rc/Proof/`) stay as a library nothing emits; its
  increment `Procs.inc` is still the one the pipeline calls. The general
  release costs a little more than the bounded one on cells of fewer than
  three scanned fields ([below](#the-general-releases-cost)).
- *Implemented (heap stage 2, two landings of three).* An ownership
  checker that judges any placement of `inc` and `dec`, not only the
  canonical one: `Own.Plain.checkOwned` and `checkContractOwned`
  ([`Own/Plain/Owned.lean`](../IxCC/Own/Plain/Owned.lean)), with
  `checkOwned_refines` and `checkContractOwned_refines` (an accepted map
  refines Fir's `evalCall`: the conclusion of `checked_program_refines`) and
  `checkOwned_reclaims` (the conclusion of `checked_program_reclaims`)
  ([`Own/Plain/Proof/Owned/Program.lean`](../IxCC/Own/Plain/Proof/Owned/Program.lean)),
  and `checkPlainMap_checkOwned` (every map `checkPlainMap` accepts, it
  accepts; [`Own/Plain/Proof/OwnedAccepts.lean`](../IxCC/Own/Plain/Proof/OwnedAccepts.lean)),
  from which `checked_program_refines`, `checked_contract_program_refines`
  and `checked_program_reclaims` are re-derived with their statements
  unchanged. The plain-RC verifier admits ownership certificates with it,
  behind a work budget (`Anf.maxCapturedWork`) and a parameter total
  (`Anf.maxParamTotal`), and `Recheck.RcReplay.sound`
  keeps its statement; the producer still writes the canonical placement, so
  every compiled object is unchanged ([below](#the-ownership-checker)).
- *Not implemented.* Scalar fields in compiled programs (the runtime above
  has them; the constructor table has none, and `Cfg.Rc.Native` and
  `Rt.Lower` refuse a constructor with scalar fields until DR2 produces
  them); reset/reuse and in-place update (the uniqueness test and the
  in-place reuse lemmas are proved, but no pass emits a reuse: heap stage 4,
  after stage 2's placement makes cells unique at their last use); static
  reuse from `unique` contracts; borrowed parameters beyond the zero-RC
  policy selection; inline fast paths (each RC operation calls a runtime
  procedure today, `rt_rc_inc` of `Rt.Rc.Procs` or `rt_rc_dec` of
  `Rt.Rc.Gen`); static constant objects (closed
  constructor trees as immortal read-only cells, `Rhs.const` in the Fir
  design, [`Fir/Syntax.lean:29-31`](../IxCC/Fir/Syntax.lean)). The Own IR
  has no `reset`, `reuse` or credit forms
  ([`Own/Syntax.lean:14-20`](../IxCC/Own/Syntax.lean)).

**The general heap invariant.** The planned statements of stage 1 use names
with an `L` suffix; the code keeps the bounded route's names in the
namespace `Rt.Rc.Gen`:

| Plan | Code |
| --- | --- |
| `Layout`, `Layout.ok`, `Layout.cls?` | `Rt.Rc.CellLayout`, `.ok`, `.cls?` |
| `LiveCellL`, `HeapLiveL`, `ArenaPartitionL` | `Gen.LiveCell`, `Gen.HeapLive`, `Gen.ArenaPartition` |
| `PendingCursorL`, `CursorChainL` | `Gen.PendingCursor`, `Gen.CursorChain` |
| `ReleaseInvariantL`, `AllocatorReadyL` | `Gen.ReleaseInvariant`, `Gen.AllocatorReady` |
| `allocL`, `decL`, `isUnique` | `Gen.alloc`, `Gen.dec`, `Gen.isUnique` |
| `LiveCell.toL` | `Procs.LiveCell.toGen` |

Beyond the plan's statements, the invariant carries what the proofs needed:
- a cell's fields as one clause with a per-position encoding (`fieldWord`:
  a value word for a scanned field, the raw word of a `Nat` literal below
  2⁶⁴ for a scalar position), from which `LiveCell.scanned` and
  `LiveCell.scalar_values` derive the plan's two clauses;
- scalar positions as literal tokens a release step may drop
  (`ScalarTokens`, `dropAll_scalars`, `Balance.drop_scalars`; the release
  step `ReleasePoint.Move` drops them: `ReleasePoint`, `FramePointScalar`,
  `RecycleLive`, `RecycleDetailed`);
- `ReleaseInvariant.cursor_layout` and `cursor_scan`, beside the bounded
  route's `cursor_class`: a suspended parent has a valid layout and its scan
  byte (the release's loads of the scan count, `CursorLoads`, and the
  invariant's preservation through detach, advance and recycle);
- `PendingCursor.layout`, `arity` and `scalars` (the scalar tail of a
  finished parent is dropped as tokens when it is recycled,
  `FramePointRecycle`, `RecycleLive`), `remaining` (the countdown in the count word) and
  `header_low` (the scan, class and tag bytes kept while the cell is
  pending), in `Cursor`, `CursorPreserve` and `CursorLoads`;
- `ArenaPartition.valid` with `1 ≤ classWords cls ≤ 2²⁶` (the arithmetic
  of slot bounds) and `ArenaPartition.bounded`, every slot's class at most a
  parameter `cmax` (allocation's `reserve_total` takes `cls ≤ cmax`).  The
  pipeline instantiates `cmax` at 71 (`maxClass`), where `bounded` follows
  from `valid`; it stays because removing the parameter would restate every
  theorem of the 93 modules for no gain;
- the five recycle lemmas (`pending_free_separation`, `recycle_chain(s)`,
  `pending_not_free`, `recycle_distinct`, `recycle_free_placed`) for any
  slot that is not free, so the recycling of a scalar-only cell (a live
  slot) reuses them.

#### In-place reuse

Proved (heap stage 1, part 3), used by nothing yet: the facts a reuse pass
(heap stage 4, Lean's `reset`/`reuse`) and DR3's in-place update will rest
on. Abstractly a reuse is a release of one cell followed by an allocation:
`Own.Rc.reuseCell H l b'` kills the unique cell `l` and appends `b'` with
one reference ([`Own/Rc/Reuse.lean`](../IxCC/Own/Rc/Reuse.lean)).
`reuseCell_balance` (exact counts: the old cell's field tokens return to
the caller, the new cell's are taken from it), `reuseCell_heapOk` (order)
and `reuseCell_readback` (every token the caller held and every old field
reads back as before; the new location reads back as `b'` over the old
values) hold when the caller's token for `l` is among balanced tokens, `l`
has one reference, and the old fields and the caller's other tokens equal,
location by location, the new fields and the tokens it keeps (`hmass`;
literals are free). Physically
([`Gen/Proof/InPlace.lean`](../IxCC/Rt/Rc/Gen/Proof/InPlace.lean)),
`inPlace_ready`: rewriting the cell's storage (`Gen.writeCell`: a
one-reference header at the old class, then the new words) on an
`AllocatorReady` heap gives `AllocatorReady` again, for the reused heap,
with the fresh location mapped to the old address, the slot relabelled, and
no free list, bump pointer or other cell changed.

A reuse site must establish: the cell unique with the caller's token among
the balanced ones (what `isUnique_spec` answers), `hmass`, a valid layout
of the old cell's class (`hlayout`, `hclass`), and a word for every new
field (`hwords`: a value word at a scanned position, a literal below 2⁶⁴ at
a scalar one). The plan asked for a word at the scalar positions only
(`hscalars`); that statement was false (a scanned string literal or `Nat`
≥ 2⁶³ is stored as 0, which the release then takes for a cell), and the
general premise is the one the allocation path already has. The invariant
gained nothing.

Two limits, recorded and not pursued: a cell cannot be reused at a layout
of a smaller class, because the invariant ties a cell's header class to its
layout's (`LiveCell.header`, `ArenaPartition.live`; physically harmless, it
would need a slot class separate from the layout class); and static
children are outside the invariant (`HeapLive` admits only dynamic cells
and `Balance` gives a static location no token), so reuse says nothing
about them until static objects exist (stage 6). Controls:
`IxCCTests.Rt.Rc.GenReuseControls` (`tests-rt-rc controls`: the instances,
and as negative controls a scanned field without a word, a shared cell and
a larger class) and `GenNativeControls.reuse` (`tests-rt-rc native`).

#### The general release's cost

On today's layouts (1–31 scanned fields, class `fields + 1`) `Gen.dec`
executes `3 − n` more Lir steps, and `4 − n` more x86 instructions, than
`Procs.dec` per freed cell of `n` scanned fields: up to 3 steps (4
instructions) more for cells of fewer than three scanned fields, fewer for
four or more. The extra instructions: a branch on the scan byte, for
cells without scanned fields (+1 step; x86 `test` and `je`), and a reload of
the class byte when a cell is recycled, since the loop now loads the scan
count instead of the class (+1; x86 `movzx`); against one subtraction fewer
for each field after the first (the bounded release's `class − 1`).
Measured on the same cell graphs, the procedures as emitted (critical edges
split): Lir steps on the interpreter, x86 instructions on the byte machine
running the object the backend writes behind one export wrapper (wrapper
included); both procedures end in the same memory on every graph. The Lir
counts are pinned by `tests-rt-rc controls`.

| Graph | Lir steps, bounded → general | x86 instructions, bounded → general |
| --- | --- | --- |
| list of 1,000 cells (x86: 100) | 31,005 → 32,005 (+3.2 %) | 4,139 → 4,339 (+4.8 %) |
| chain of 1,000 one-field cells (x86: 100) | 19,005 → 21,005 (+10.5 %) | 2,739 → 3,039 (+10.9 %) |
| tree of 1,023 two-field nodes (x86: 127) | 31,718 → 32,741 (+3.2 %) | 5,246 → 5,500 (+4.8 %) |
| tree of three-field nodes | 0 | +1.8 % |
| tree of four-field nodes | −2.1 % | 0 |
| one cell of 31 immediates | 384 → 356 (−8.7 %) | 486 → 459 (−6.4 %) |
| one cell of 31 unique two-field children | 1,345 → 1,348 (+0.2 %) | 1,757 → 1,792 (+1.9 %) |
| a shared cell (one decrement) | 10 → 10 | 47 → 47 |
| a list of 1,000 (x86: 100), then a shared tail | +3.2 % | +4.8 % |

Accepted for stage 1, with one release procedure rather than two, on a gate
of whole-program executed instructions (at most 2 % worse anywhere), which
the switch passed. x86 instructions executed by whole programs, counted by
valgrind (cachegrind) on executables IxCC writes, at the bounded release and
at the general one (2026-11-12, HC; the benchmark programs at the tip
`37871be1e`): rbmap (1,000 to 100,000) −0.23 %, binarytrees (depth 10 to
18) +0.48 %, const_fold (15, 17) +0.26 %, list-qsort (500 to 10,000) +0.54
to +0.86 %, queue (1,000 to 5,000,000) +0.59 %; every registered root under plain RC that an executable
runs (177 roots, 1,724 cases): 157 unchanged, 20 between +0.03 % and
+1.59 % (`Resource.twoVars`), every result the same.
**Open for heap stage 3** (inline fast paths): two variants, measured on the
same graphs but not proved. `asc`, the count word holding the next field's
index with the end test `j = scan` (field order kept): `3 − 2n` steps and
`4 − 2n` instructions per freed cell (lists −4.7 % steps, 0.0 %
instructions; one-field chains +5.2 %, +7.3 %). `desc`, the count word
holding the scan count and counting down to 1 (fields visited 0, then
`scan − 1` down to 1): `3 − 3n` and `4 − 3n` (one-field chains 0.0 % steps,
+3.6 % instructions; every other graph below the bounded release). `asc`
changes the cursor's count-word clause and the step lemmas of the release's
blocks 7, 8 and 12 (15 of the 93 proof modules mention the countdown);
`desc` also changes the order of visits, which reaches the cursor's suffix
and its correspondence with the abstract release's worklist.

**Options for the ownership checker.** (i) Keep "equal to the canonical
producer": safe, but leaves no room for optimisation. (ii) The proved static
linear typing of Own described under
[Ownership](compiler-design.md#ownership-reference-counting-and-reuse).
(iii) Per-function translation validation of RC placement.
**Recommendation: (ii)**, keeping (i) as the always-accepted fallback, as
the compiler design already intends. (iii) duplicates (ii) with weaker
reuse.

#### The ownership checker

(ii) for today's syntax (heap stage 2: the checker in its first landing, the
verifier switched to it in the second). The judgement types `Own.Plain.Code` as it is, against its Fir body, with no
syntax or certificate change: on one path each variable in scope is an
*immediate* (a literal, `□` or a field-less constructor, on which every
action is free), *owned* with `n` tokens, or *borrowed* (a projection's
result not yet incremented, valid until the next release). `inc x 1` adds a
token (a borrowed variable becomes owned); `dec x` takes one and is a
release, which ends every borrow, as a non-tail call is; a consuming use (a
constructor field, a call or tail-call argument, `x := y`, a returned or
jumped value) takes one token per occurrence; a read (`case`, `proj`, a
primitive's argument) needs the variable available and takes nothing; after
a primitive, the arguments its signature marks (`primImmArgs`: today every
argument of every primitive, all on `Nat`) are immediates. At `ret`, `tcall`
and `jmp` every token must have been consumed, a jump also taking one token
of each variable the target join captures; a join body starts with one token
per captured non-immediate and per parameter. A `case`'s branches are checked
from the same context: Own has no merge point. The proof is an induction on
the ownership code over a typing context (`OwnedState`, `owned_refines`,
[`Own/Plain/Proof/Owned/`](../IxCC/Own/Plain/Proof/Owned/Simulation.lean));
reclamation follows from refinement and the producer-independent
`call_heap_shape`, as for the canonical map; 25 exact fences
([`IxCCTests/Fences/OwnOwned.lean`](../IxCCTests/Fences/OwnOwned.lean)): the
refinement, reclamation and canonical-acceptance theorems on `propext`,
`Classical.choice` and `Quot.sound`, as the landed `checked_program_refines`.
`tests-own-owned` runs it on every registered corpus
root: the canonical and a liveness placement accepted and run under a
refinement oracle, the negative controls refused, and a site-directed
mutation campaign whose accepted mutants must run clean
([CI](ci.md#suite-costs)).

Known properties: a path that ends in `trap` may keep tokens it holds (a
trap ends the whole run, and `ResultRel.trap` has no heap clause; an
embedding with recoverable traps would need `trap` to require none, as
`checkContractOwned_refines`'s docstring says); and only unit increments are
admitted.

**In the verifier.** Plain-RC certificate admission
(`Own.Plain.Certificate.admit`; `admitContract` for the contract-aware
domain) and the program gate (`Cfg.Rc.checkProgram`) run the checker where
they compared the proposed map with the canonical one (`checkPlainMap`). The
verifier therefore accepts what it refused before: any placement the checker
types, for example one that drops a variable right after its last use, moves
a value into its last consuming use, lets a join capture only what its body
uses, increments a projected (borrowed) variable later than at once, acts on an
immediate, or lists a join's captured variables in another order
(`tests-rc-certificate` runs each through the verifier and natively; a
reordered captured list is validated even with the canonical certificate's
backend decisions, and its object is the canonical one's byte for byte: the
captured order does not reach the lowered code). A refusal names the checker's first reason (`own.cert.check:
ownership proposal refused: <reason>`). What makes it sound is
`Recheck.RcReplay.sound`, with its statement unchanged: the Cfg activation
layer it rests on (`Activation`, `PhysicalAtClock`, `eval_physical`,
`checked_physical`, [`Cfg/Rc/Proof/Native/`](../IxCC/Cfg/Rc/Proof/Native/PhysicalSimulation.lean))
is restated over the checker's typing context instead of the canonical
producer's state, with one step per `inc` and per `dec` and a captured-token
step at jumps, and the canonical simulation's proofs are deleted. Nothing
admitted before is refused within the budget: `admit_of_checkPlainMap` and
`checkScopedProgram_owned` ([`Cfg/Rc/Proof/Owned/Admission.lean`](../IxCC/Cfg/Rc/Proof/Owned/Admission.lean)),
from canonical acceptance. The producer still writes the canonical placement,
so every compiled object and certificate is unchanged; a liveness placement
in the producer is the next landing. The contract side (`checkContractOwned`,
Fir's contract list, `zeroRcBinder`'s linear and affine cases) is expected to
be reworked when pull request #678 brings the owner's new annotation design
(modes stored in records and read by position, the `linear` and `affine`
cases retired, Fir's contract list retyped).

**The work budget.** A jump takes one token of every variable its target
join captures, and a join may capture its whole lexical scope and be jumped
to from every branch, so the checker's work is quadratic in the body. Before
the checker runs, admission sums that work over the decoded map
(`capturedWork`: at each jump the target's captured list, at each join
declaration its own; a linear walk) and refuses past `Anf.maxCapturedWork` =
2²⁰ = 1,048,576 with `own.cert.budget`, naming the measured work and the
limit. Acceptance is monotone in the limit (`admit_mono`): a refusal is
policy, not soundness. The worst cases under the limits that already hold
before the check (the middle end's node budgets, 64 MiB of certificate text,
JSON depth 512), measured on the build box, one function unless stated:

| Map | Captured tokens | Before: `checkPlainMap` | `checkOwned` | Now |
| --- | ---: | ---: | ---: | --- |
| a join capturing 2,049 parameters, 8,191 jumps (16,383 Anf nodes) | 16.8 M | 24.0 s | 8.0 s | refused by the budget |
| the same, scope from an outer join's parameters, 7,166 jumps | 14.7 M | 21.6 s | 6.1 s | refused by the budget |
| 4,096 joins each capturing 2,049 parameters (37.6 MB certificate) | 8.4 M | 0.54 s | 8.6 s | refused by the budget |
| 256 functions, each a join capturing 2,049, 127 jumps | 66.6 M | 98.7 s | 34.9 s | refused by the budget |
| 4,096 such functions (2²⁰ program nodes) | 1.07 G | over 900 s | 603 s | refused by the budget |

Unit costs of `checkOwned`: 0.48 to 0.57 µs per captured token at a jump,
about 1.0 µs per captured entry at a declaration, about 0.1 µs per action;
so a map within the budget checks in about a second at most, and its actions
(at most 64 MiB of text) in about 0.6 s. The registered corpus needs at most
1,925 (`Machines.fibMain`, canonical placement; 145 with a liveness
placement), 545 times below the limit. Measured against the program's Anf nodes, the
captured work is at most 0.75 times them on the corpus (`Machines.echo`, 1,316 tokens for 1,754
nodes; `Machines.fibMain` 0.52), 0.16 on the largest programs (`Natural.fibMain`, 8,459 nodes;
`Closures.stateLoop`, 11,536 nodes, captures nothing), 0.04 on the benchmark closures and 0.04
with a liveness placement; since the limit equals `Anf.maxProgramNodes`, a program reaches it only
with more than one captured token per node.
A legitimate program can exceed the budget: `fixtures/rc/budget`'s `fanOver`
(forty-one functions, each a join capturing 200 values jumped to from 127
leaves: 1,049,600 canonical captured tokens). Under `--rc on` it is refused
(`cert: own.plain: own.cert.budget: …`, the work and the limit) and no object
is written; under `--rc auto` it compiles under the immortal policy, and the
line `rc policy: immortal (plain RC refused: cert: own.plain: own.cert.budget:
…)` names the work and the limit. A liveness placement lowers the quantity,
since a join then captures only what its body uses: 1,039,104 for the same
program, within the limit. The limit is not settable at invocation yet (a
mechanism to raise the verifier's limits as `IXCC_<LIMIT>` is being built).
Its twin within the limit, `fanUnder` (1,044,352 tokens), compiles under plain
RC with a certificate within the certificate text's limits (nesting 410 of 512,
54,727,677 bytes of 64 MiB), since its roots call the fan functions in parts of
two; in parts of ten or eleven the callers' `inc`s of the shared argument
nested its certificate 2,208 deep, which `check-cert` refused and which the
compiler, reading its certificates back since 2026-11-12, would decline
([compiler design](compiler-design.md#middle-end-budgets), "Certificate text and
decode limits"). So a program the front end produces can meet the
captured-work budget before the text limits.
The source-domain check the checker runs first (`programDomain`,
`contractProgramDomain`: fresh parameters, every body's lexical scope and
every call's arity) is linear in the program it reads up to a logarithm: it
keeps the scope as a `Src.NatSet` and reads a callee's arity through
`Fir.Program.fun?` ([`Own/Plain/ScopeSet.lean`](../IxCC/Own/Plain/ScopeSet.lean)),
proved equal to the former list forms (`programDomain_eq_list`); the list
forms cost about the square of a function's parameters (85.4 s on 4,096
functions of 2,049 parameters, 6.6 s with the sets; the verifier's steps from
Fir on such a program 267 s and 33 s).
The verifier is not slower for the change: over every root of the 12 registered manifests under
`--rc on` (202 certificates, the CLI's `run` time, eight at once on the shared build box), 4.15 s in
all and 1.33 s for the slowest (`Closures.stateLoop`), against 4.31 s and 1.50 s with the canonical
comparison (an earlier pair of runs: 4.06 s and 1.32 s against 4.96 s and 1.99 s; the difference is
within the box's noise).

**The parameter total.** Parameters, a function's and a join point's, cost no
Anf node (a join counts one node whatever its arity), so the node budgets do
not bound them, while the domain check and the checker walk every one, three
times per certificate. Admission therefore counts them first
(`Own.Plain.Certificate.paramTotal`, over the numbered functions and the join
points their bodies declare; a linear walk, 1.4 ms at the limit) and refuses a
program past `Anf.maxParamTotal` = 2²⁰ = 1,048,576 with `own.cert.params`, the
total and the limit, before it decodes the certificate; acceptance is monotone
in the limit (`admit_params_mono`), and `RcReplay.runFront_paramTotal` states that
every run of the check judges a program within it. The zero-RC route's check
(`Recheck.runWithContracts`, after `Recheck.run`) refuses the same first. At the
limit one run of the domain check takes 0.76 s (512 functions of 2,048
parameters) to 0.93 s (64 functions each declaring 8 joins of 2,048), and the
verifier's steps from Fir 3.9 s and 4.6 s. The registered corpus reaches 240
(`Closures.stateLoop`; every join point the passes make has one parameter), the
benchmark closures 386 (`const_fold`). The producer is not expected to reach
the limit from an artifact (an argument from the code, not a proof: after its
last `prune` every parameter but a root's is matched by an argument at a call,
which costs Anf nodes; [roadmap, "Hardening"](roadmap.md#hardening)); under
`--rc on` a program past it would be declined with no object, under `--rc auto`
compiled under the immortal policy with the reason printed. The limit bounds
the domain check, the checker's entries and the plain-RC lowering's work per
parameter; it does not bound the relevance check against the canonical
annotator (Stage A), which runs on the source first (linear in the source's
parameters since 2026-11-13), the plain-RC back end's per-function term
(`Xv.Validate`, about the sum of the squares of the functions' sizes, which the
canonical map's `dec` per parameter makes grow with the parameters), the
layout's function-count term (`Backend.lay`, linear in the functions and call
sites since 2026-11-13), or the RC policy selection (linear in the function
count since 2026-11-13); all four are measured in the
[roadmap](roadmap.md#hardening), the second open, with the check run three times
per certificate and the certificate text's JSON depth (512, which a function's
canonical ownership code passes at about 510 levels of nesting).

**The zero-RC route's check.** `Recheck.Artifact.checkContractOwn` checks the
contract-aware domain and the Boolean pins (`contractProgramDomain`,
`checkBoolPins`). It used to build the canonical map and compare it with
itself, which always holds (`Own.Plain.checkContractPlainMap_canonical`), so the
same verdict now comes without the map, whose construction is quadratic in a
join's captured list; `Artifact.checkContractOwn_iff` keeps its statement.

**Statics.** Closed constructor trees (and, after P8, field-less closure
constructors) become immortal cells in the object's read-only data instead
of being rebuilt at each use; K3's `binarytrees` needs this for parity, and
string literals (DR4) and large `Nat` literals (bignums) reuse it.

**Proof obligation.** Generalise `Plain.checked_program_refines` to "a
program the Own checker accepts refines its Fir program up to heap
isomorphism", relative to Fir's semantics; extend the Cfg.Rc and Rt.Rc data
refinement (the heap invariant `HeapState`, with `AllocatorReady` and
`HeapCtorOk`) to scalar fields, reuse, the
uniqueness test and immortal read-only cells, and the ELF writer to a
read-only data section under the existing object checks. It composes into
`Recheck.RcReplay.sound` with unchanged statement.

**Trusted base.** No change.

**Dependencies.** None upstream. DR2–DR4, P8 and the bignum cells depend on
scalar fields and general layouts.

**Size [estimate].** 20–40k lines, by comparison with the bounded route
(`Own/Plain/` 6.1k plus `Cfg/Rc/` and `Rt/Rc/` 28.6k).

**Exit.** K0 (`List.reverse`) refrozen with the final Phase 1.5 producer;
the K2 and K3 programs of
[`benchmarks/fixtures`](../benchmarks/fixtures/README.md) frozen as Ixon
closures, compiled under `--rc auto` and certified, with `rbmap_fbip`'s
annotated twin measured against the plain one.

## DR2. Fixed-width integers and `Int`

**Status: in progress** (Phase 3, stage W1 done: the word operations as primitives, tagged at run
time; below, "Stage W1"). A closure `ix compile` compiles with its defaults (a selected closure)
runs its word operations as primitives; the grounding's word case, stage W2 (raw words) and `Int`
remain.

**Motivation.** BLAKE3 and `qsort` (K4); the bignum library's limbs; IxCK,
whose executable closure uses `UInt64`, `UInt8`, `USize` and `Int`
throughout (occurrences in the 79 modules of the import closure of
`IxCK.Kernel.Cached.Installed`, `IxCK.Kernel.Admission` and the Ixon reader:
`UInt64` 219, `UInt8` 137, `Int` 70, `USize` 7); IxOS, where addresses and page-table
entries are 64-bit words.

**Before stage W1** (and still, for a closure compiled without the word equations). Erasure unboxes
single-field structures ([Relevance and
erasure](compiler-design.md#relevance-and-erasure)), so `UInt64` (a structure
over `BitVec 64`, over `Fin (2^64)`) arrives at Lir as a tagged `Nat`, and its operations compile
from their reference bodies. **Every** `UInt64` operation then fails natively with `natOverflow`
([`Rt/Layout.lean:35`](../IxCC/Rt/Layout.lean)), on every input, `3 + 4` included: each body
computes `x % 2^64` with `2^64` a `Nat` (`BitVec.ofNat`, `Fin.Internal.ofNat`), which has no tagged
word. (An earlier version of this paragraph said only values at or above `2^63` fail.) `UInt8`,
`UInt16` and `UInt32` work, their sizes fitting; compiled, the middle end inlines their bodies and
folds the constants.
Fir has a `word` representation that nothing selects
([`Fir/Syntax.lean:70-77`](../IxCC/Fir/Syntax.lean)). `USize`'s width comes
from `System.Platform.getNumBits`, an `@[extern]` opaque in Lean's
`Init/Prelude.lean`. `Int` is an ordinary inductive (`ofNat`, `negSucc`)
over `Nat`. No committed fixture exercises any of these types.

**Options.**
- (a) Compile the reference bodies (modular `Nat` arithmetic). Correct and
  needs no new trust, but slow, and `UInt64` overflows the tagged word.
- (b) **Primitives in the unfolding table** (`prim f op`, pinned by address
  and type as `Nat`'s are), whose meaning is the pinned Lean body, plus a raw
  64-bit representation selected by a checked representation annotation,
  with `box`/`unbox` where a raw word meets a uniform position.
- (c) Take Lean's `@[extern]` C implementations as the meaning. Rejected:
  it adds the C runtime's behaviour to the trusted base.

**Recommendation: (b)**, staged.
1. `UInt8/16/32`, `Char` and `Fin n` stay tagged immediates (their values
   fit 63 bits); add primitives for speed only.
2. `UInt64` and `USize` get the raw-word representation where a checked
   annotation justifies it, and a boxed 64-bit cell at uniform positions.
   `USize` is fixed at 64 bits through the interpretation table of DR5.
3. `Int` first compiles as ordinary data through its reference bodies
   (needs only DR1). Then a signed small representation and primitives;
   large values use the bignum library (Phase 4).

**Stage W1** (words as primitives, tagged at run time; the data-types plan's first stage). What
exists (`Table.Config.words`, on by default):
- the exact meaning `WordOp.eval` of every operation of `UInt8` to `UInt64`
  ([`Src/Word.lean`](../IxCC/Src/Word.lean)), tested against Lean's C implementations and, by the
  kernel's `decide`, against the reference bodies;
- SrcEval's rule F6w (contract version 2, [evaluator interface](evaluator-interface.md)) and the
  table entry `word w op thm`. The rule reads a word only when its number is below the width's
  size, so it is stuck on a tower only a false proof builds (the reference body would compute
  on it), and every tower it builds is in range (`WordOp.eval_word_lt`). The entry names the
  constant at the operation's pinned address
  (`src-tables.tsv`'s `word` rows), and `thm` a stored theorem whose statement is the operation's
  equation over `Nat`'s operations on `UIntN.ofNat x` (and `y`); `ofNat`'s theorem is the
  *reducing bridge* `∀ x (h : Nat.le (Nat.succ (x % size)) size), ofNat x = tower (x % size) h`
  ([`Src/Table/Word.lean`](../IxCC/Src/Table/Word.lean)). An earlier draft's bridge, below the
  size only, constrained nothing above it (a key returning `5` there satisfied it);
  `IxCCTests/Src/Words.lean` refutes that key with the reducing bridge;
- the theorems, which `ix compile` adds by default with its equations for every word operation the
  compile's roots reach outside theorems (`Ix/Compile/WordEquations.lean`; below) and names, with the operation, in its output's `theorems`
  list; the sidecar carries the list with addresses ([corpus](corpus.md), "The sidecar"), and the
  producer proposes a word entry from it only, so ingress, which reads only what a program
  reaches, finds each theorem and reads it with its proof once its operation is reached (a
  proposal's theorem is a proof seed); `checkWord` refuses a theorem read by its statement, as
  `checkEqn` does, and its axiom-closure walk sees the proof; a tampered theorem is refused by
  the kernel's acceptance at ingress (`tests-src`, `WordRules.tampered`);
- the harness (`tests-src`): on every boundary case of every primitive operation at every width,
  F6w's result equals SrcEval's own run of the operation's Lean 4.34.1 reference body (21,996
  cases), and on a tower at or above the size F6w is stuck (1,216 cases);
- the decisions (`decEq`, `decLt`, `decLe`) stay reference bodies, not primitives: their bodies
  reduce to `Nat`'s decisions and never build `2^64`. A primitive decision would need, in the
  grounding, that every element of `Decidable p` in the model is one of its two constructors'
  images, which no law states;
- erasure ([`Lam.Erase.wordForm`](../IxCC/Lam/Erase/Term.lean)): a `word` entry erases to the Lam
  word primitive on its strict arguments, and its wrapper to the primitive over the wrapper's
  binders. A tower erases to its number because its three constructors unbox at field 0;
  erasure checks this per width, at the operation's width and at its result width
  (`Input.wordUnboxAtB`), and declines (`erase-word`) where it fails. The relevance annotation
  covers those constructors because a word entry lists them as its runtime references
  (`Src.Program.runtimeRefs`; before, a root's program annotated only the constructors its
  decisions match on, and the check failed on every root of the words fixture compiled alone).
  The proof's relations carry the fact (`SatR.word`, `WrapR.word`), and F6w meets the primitive on
  the towers' numbers (`Lam.Erase.Proof.word_value_sim`, through `vr_word` and `vr_mkWord`).
  `tests-src` checks this on every harness case in each root's program compiled alone, and
  `tests-pipeline` runs each root, compiled alone, at every level and natively against Lean's own
  operations;
- below Lam ([`Lam.Prim.word`](../IxCC/Lam/Syntax.lean)): the word primitive `word w op`, whose
  meaning `Lam.wordSem` is `eval`'s number on words below the width's size (`ofNat`'s argument
  any `Nat`) and is stuck elsewhere, as F6w is, so every pass below Lam owes agreement only in
  range. Anf, Fir, Own and Cfg carry it as they carry the `Nat` primitives (generic in
  `Prim.sem`; constant folding included). Rt lowers it on tagged words
  ([`Rt.Lower.word`](../IxCC/Rt/Lower.lean)): `div`, `mod`, `land`, `lor`, `xor` are the `Nat`
  codes; below width 64 every other operation computes a word congruent to the tagged result
  modulo `2^(w+1)` and masks it, and never fails; at width 64 it computes the untagged wrapped
  result and fails with `natOverflow` unless it is below `2^63`. The expansion is proved once,
  against a heap-free core (`Rt.Proof.PrimCore`, `word_core`; the arithmetic in
  `Rt.Proof.WordArith`), and each route's simulation follows from the core by one lemma (the
  immortal route's `Rt.Proof.prim_word`, the plain-RC bridge's `Bridge.Scalar.prim_word`); the
  code uses only Lir forms selection already has, so selection, allocation and the validators
  need no new case. `tests-rt` runs every operation at every width on its boundary numbers
  against `eval` at Lir and at every backend level, with planted mutations of the code as
  controls.

**The pattern for new primitives.** A primitive's expansion is a scalar computation: it reads its
operands' words, binds its result, and touches no memory and no heap. So it is proved once, against
the heap-free core `Rt.Proof.PrimCore` (from registers holding the operands' tagged words, Lir runs
from the expansion's start to its end with the memory unchanged, binds the result's word and keeps
every other register below the supply, or fails with a resource), and each route's simulation
relation follows from the core by one lemma (`Rt.Proof.rhsSim_of_core` for the immortal route's
`RhsSim`, which assumes the immortal heap invariant; the plain-RC bridge's `rhsSim_of_core` for its
own, which has none and keeps the memory). A direct transfer between the two relations does not
exist as they are stated (each assumes what the other cannot supply), which is why the core is
stated without either. The arrays', strings' and later primitives' expansions follow this pattern;
the 16 `Nat` primitives still have one proof per route, and their restatement over the core is a
clean-up item on the [roadmap](roadmap.md) (Phase 3, "For the x86 back end").

One limit stays after W1, by design, and is an open item: a `UInt64` is native only below
`2^63`. A word is a tagged immediate, so a width-64 result at or above `2^63` fails with
`natOverflow`, as a `Nat` does. Stage W2 is planned to lift it with raw unboxed words (direction
chosen 2026-11-13): raw 64-bit words in registers and frames, and a cell of one scalar word where
a word meets a uniform position, so that a width-64 result needs no tag bit. Its design section,
still to be written, must settle:
- the scalar cell and its overlap with Phase 2's scalar fields;
- the representation analysis in Fir;
- how RC insertion skips raw variables;
- the raw case of Rt's value relation;
- the landings.

A second limit is closed. The decisions stay reference bodies, and `x < y` at `x = 2^63 − 1`
used to fail with `natOverflow`: `Nat.lt` is `x + 1 ≤ y`, and the `Nat` `x + 1` reached `2^63`.
Since 2026-11-13 the shrink walk turns `natBle [x, m]`, where `x = y + 1` is known, into
`natBlt [y, m]` (`Anf.Walk.succBle`), which compares the tagged words. So `<` and `>` work at
the boundary for `Nat` and every width. `≤` never built `x + 1`. `natBle m (y + 1)` has no
simpler form and stays. Primitive decisions, a table entry per decision justified by a stored
theorem fixing what it denotes as a `Decidable` value, remain a design for after the grounding's
word case; the boundary no longer needs them.

**What stage W1 means for a user.** `ix compile` on a selected closure (`--consts`,
`--consts-file`, `--local`, `--module`) adds the word equations by default, with its unfolding
equations, so such a closure runs its word operations as primitives (F6w, the Lam word primitive,
Rt's tagged lowering) and no hint is printed. A closure without them (compiled with
`--no-equations` or `--no-word-equations`, a whole environment compiled without `--equations`, or
one frozen before this default) has no word entry: its word operations run their reference bodies,
as before W1, and `ixcc compile` says so in one `hint:` line on standard error,
naming the first operations the program reaches at run time (`--stats` prints each); the hint
changes no object, certificate or exit status. A program with a word entry is outside the grounded
fragment (`noWord`, below) until the grounding's word case is proved. A `UInt64` is native only
below `2^63`, and the comparisons are reference bodies (the two limits above, as the
[roadmap](roadmap.md) records).

Not yet: the grounding. The grounding check refuses a word entry (`Faith.noWord`, conjunct
`noWord`, temporary): the word case of the fundamental lemma is not proved. Besides what the stored equations say (`mem` and
`eq_equality` make each hold in every model; `nat_accel` evaluates its right side), that case needs
the result tower typed in the model: its constructors' stored types mention
`OfNat.ofNat Nat 64 _`, `2 ^ w` through `HPow` and `LT.lt Nat instLTNat`, which no stored
equation speaks of. The grounding's direct route decides them by its conversion (δ, `proj_ctor`,
`nat_accel`; measured on the words closure), so no law or further stored theorem is expected.
The input towers' range needs no fact: F6w reads only towers below the size. When that case is
proved, `noWord` gives way to a check that every word entry's facts hold.

**Which word operations get equations.** `ix compile` adds the equation of every word operation
the compile's roots reach by a dependency walk that follows the values of definitions and opaques
and the rules of recursors, and enters no declaration type, no theorem and no word operation, with
the bridges each statement mentions (`Ix.Compile.WordEquations.reachedOutsideTheorems`,
`neededFor`). Types are excluded because a type never runs and following them reaches far: through
`autoParam`'s type, which mentions `Lean.Syntax`, every `for` loop would reach `String` and `Char`
and with them `UInt32` and `UInt8` operations. Theorems are excluded because a proof never runs: a
closure reaches word operations through proofs alone (an `omega` termination proof reaches some,
through Lean's auxiliary proof theorems), and those get none. The walk is not IxCC's relevance
analysis: it is a superset of what IxCC runs in most cases (an operation in a binder's type or an
irrelevant argument of a value gets an equation too many, harmless), and it can miss an operation
IxCC runs (one reached only through a theorem, as a `csimp` redirect's target is), in which case
the hint names it.

Measured on the registered families (`regenerate.sh` with these defaults): two closures moved, and
were refrozen, `phase1-decline`'s `panic` and `strings`. Their string code runs, so they gain the
word equations of the `Char` and UTF-8 operations it reaches (`panic`: `UInt32.ofNat`,
`UInt32.toNat`, `UInt8.ofNat`; `strings`: `UInt32.lor`, `UInt32.ofNat`, `UInt32.shiftLeft`,
`UInt8.land`, `UInt8.ofNat`, `UInt8.toUInt32`). IxCC's verdict and full error output on both roots
are unchanged under `--rc off`, `on` and `auto`: both are refused at admission for a string literal
in a relevant position. The roots-only fixtures (`kernel-hints`, `src-diag`, `src-sortpoly`, `erased-blocks`) compile
with `--no-equations`, which their provenance records; their closures are unchanged. Open: when
string literals are admitted, these two closures run word primitives and become the first
registered roots that do; and the cost of the equations on a whole environment (Init+Std) is not
measured: measure it and decide whether the default should cover a whole-environment compile.

SrcEval needs one rule for raw words to be sound: a bounded construction
whose erased proof is false (for example `UInt64.ofNatLT n h` with
`n ≥ 2^64`) is stuck rather than evaluated, so a compiled range guard fails
only where the source is stuck, which the `GoesWrong` disjunct covers.

**Proof obligation.**
- Per primitive, a *conservativity lemma*: the primitive's meaning equals
  the pinned body's, proved in Lean against the body, relative to SrcEval.
  (The existing `Nat` primitives are pinned by address and type only; their
  agreement with the kernel bodies is tested, not proved. The same lemma
  shape closes that gap.)
- Fir's value relation gains `nat n ~ word w ↔ n = w.toNat`, inside
  `Fir.convert_correct`; the representation checker's soundness is a
  subject-reduction lemma over Anf.
- One lowering lemma per operation at Lir, and one selection lemma per new
  x86 rule. The table has `mul`, `div`, shifts, rotates, `bswap`, `movzx`
  and `movsx` rows, and no `adc`/`sbb`
  ([x86 instructions](x86-encoded-instructions.md)).

**Trusted base.** New x86 rows join the existing table and its
hardware-differential gate. The `USize` width is an interpretation entry
(DR5).

**Dependencies.** DR1 (boxed 64-bit cells are cells with a scalar field).

**Size [estimate].** 10–20k lines: a representation checker, one
conservativity lemma and one lowering lemma per primitive (several dozen
primitives), and the Fir value-relation change, by comparison with `Rt/`
above.

**Exit.** K4's `blake3` (`Blake3.Pure` from `argumentcomputer/Blake3.lean`,
known-answer vectors) and `qsort` (`UInt32`, `Array`); a boundary family like
`phase1-boundary` for every fixed-width operation at 2^63 and 2^64.

## DR3. Arrays and byte arrays

**Status: planned** (Phase 3).

**Motivation.** Every flagship: IxCK uses `Array` and `ByteArray`
(`Address` is a 32-byte `ByteArray`), IxOS buffers, the bignum limbs,
K4's `qsort`, `unionfind` and `hashmap`.

**Current state.** Not supported. In Lean's `Init/Prelude.lean`, `Array α`
is a structure over `toList : List α` and `ByteArray` a structure over an
`Array UInt8`; their operations are `@[extern]` definitions whose bodies work
on the list. Compiling those bodies would give linked lists with linear-time
indexing.

**Options.** (a) Compile the reference bodies (correct, asymptotically
slow). (b) **Array objects as a runtime representation**: a cell with size,
capacity and elements (`ByteArray` packs bytes), with primitives for
`size`, `get`, `set`, `push`, `pop`, `extract`, `copySlice` and the
fixed-width byte reads, each pinned and specified by its reference body on
`toList`; in-place update when the array is unique, at run time by a
uniqueness test with copy on share, or statically from a `unique` contract
or certified inference. (c) Trust Lean's C array runtime. Rejected, as in DR2.
**Recommendation: (b).**

**Proof obligation.** Per primitive, a conservativity lemma against the
reference body (on `toList`), stated at the SrcEval level and independent of
the heap invariant, so that the x86 runtime and an evaluator's write-once
memory both rest on it and the [spine](certification-design.md#sp-2-widening)
gains one adequacy case per primitive; an Own rule for in-place `update` of a unique
array; the heap invariant gains array cells (size, capacity, elements, raw
bytes for `ByteArray`), with one lemma per runtime procedure (growth,
copy-on-share); readback of `ByteArray` results.

**Trusted base.** No change.

**Dependencies.** DR1 (scalar fields, large objects, the uniqueness test);
DR2 for `UInt8` and `UInt64` elements.

**Size [estimate].** 10–20k lines: array cells in the heap invariant, the
in-place update rule in Own, and one lemma per primitive and runtime
procedure, by comparison with the RC route's `Cfg/Rc/` and `Rt/Rc/`.

**Exit.** K4 `qsort`, `unionfind` (`Array` and `StateT`) and `hashmap`; a
root taking and returning a `ByteArray` through the byte ABI (DR6).

## DR4. Strings

**Status: planned** (Phase 3).

**Motivation.** Error values (the import closure above has 245
occurrences of `msg!`), `panic!` messages, certificate parsing in a self-hosted checker,
K4's `deriv`.

**Current state.** A string literal in a relevant position is declined at
admission and at erasure (`unsupported` in
[`Src/Admit.lean:24`, `:155`](../IxCC/Src/Admit.lean); `erase-string` in
[`Lam/Erase/Term.lean:565-566`](../IxCC/Lam/Erase/Term.lean));
`Decline.stringLength` and `Decline.withPanic` record it
([`Decline.lean:42-46`](../fixtures/corpus/phase1-decline/src/Decline.lean)).

**Design.** In Lean's `Init/Prelude.lean`, `String` wraps the UTF-8 bytes in a
`ByteArray` with an erased validity proof, so a string is a `ByteArray` at
run time once DR3 exists, and string functions compile from their Lean bodies.
Literals become static `ByteArray` objects (the statics of DR1).
**Recommendation:** strings through DR3 and statics; no string-specific
primitive until a K4 row needs one.

**Proof obligation.** SrcEval's string literal (exact, as today) relates to
its static object by the `ByteArray` readback.

**Trusted base.** No change; the loader assumption already covers mapped
sections.

**Dependencies.** DR1 (statics), DR3.

**Size [estimate].** 2–4k lines; statics are counted under DR1.

**Exit.** K4's `deriv`; `Decline.stringLength` and `Decline.withPanic`
compile (the latter returning the `Inhabited` default, which is the
kernel meaning of `panic!`; printing the message is not part of the
semantics).

## DR5. Library structures and opaque constants

**Status: planned** (Phase 3).

**Motivation.** `Std.HashMap` and `HashSet` are pervasive: IxCK threads 13
memo maps through its cached state (`IxCK/Kernel/Cached/StateC.lean`).

**Current state.** Nothing compiles them. Two obstacles besides DR1–DR3:
`mixHash` (hashing of products) and `String.hash` are `@[extern]` opaques
without bodies, and `USize` indexing reaches `System.Platform.getNumBits`,
also opaque. IxCC rejects extern opaques that are not admitted runtime
services ([Source semantics](compiler-design.md#source-semantics-and-replacements));
SrcEval is stuck on them.

**Options.**
- (a) **Compile from the Lean definitions**, with an *interpretation table*
  that gives each needed opaque a fixed Lean function (`getNumBits ↦ 64`,
  `mixHash ↦` a Lean transcription of Lean's C mixer), used by SrcEval and
  compiled like any code. The theorem then holds relative to that
  interpretation, which the compile claim must record. No C enters the
  trusted base, but the statement in the kernel's models is restricted to
  models that interpret the opaques that way.
- (b) Admit `HashMap` operations as primitives with a specification and a
  hand-proved runtime implementation. A large new runtime surface per
  structure.
- (c) Change the consumer: IxCK (or any target) uses a hash-free map
  (`Std.TreeMap`) or removes hashed computed fields. No interpretation needed,
  at a cost in the target's own code.

**Decided (2026-11-10):** (a), with the interpretation recorded in the claim
(decision 2 of 2026-11-10 in the [roadmap](roadmap.md#decisions-of-2026-11-10));
(c) remains available to a target, such as IxCK, that wants a statement
without interpretations. (b) is not planned. How this reads against the
[grounded statement](end-to-end.md) is to be confirmed (DC-2 in the
[roadmap](roadmap.md#decisions-to-confirm)); the default reading is that
recorded interpretations stay in compile claims as statements relative to the
interpretation, kept separate in the table and the image from evaluation
through a stored value (`opaqueByValue`), and that both are excluded from the
grounded statement, since IxCK's model keeps no value law for opaques.

**Proof obligation.** For (a): SrcEval and the table check accept an
interpreted opaque only through the recorded entry; a compile claim's statement
relative to the interpretation quantifies over the models that agree with
it; the grounded statements of the
[certification design](certification-design.md) exclude interpreted opaques. Hash-map functional correctness is not
the compiler's obligation: it compiles the library's code, whatever it
computes.

**Trusted base.** (a) adds one assumption per interpreted opaque: that
"meaning" is read relative to the recorded function. It adds no native code.

**Dependencies.** DR1–DR3, P8 (`BEq`/`Hashable` dictionaries), DR2's `USize`.

**Size [estimate].** 2–4k lines for the interpretation table and claim
field; the library itself is compiled, not written.

**Exit.** K4's `hashmap`; a corpus root over `Std.HashMap` with `String`
keys.

## DR6. Structured roots and the byte ABI

**Status: planned** (Phase 3).

**Motivation.** IxCK's entry takes bytes and returns a verdict; the IxOS
monitor takes and returns state and messages; any general user passes data,
not a list of naturals.

**Current state.** A root receives `Nat` arguments only, at most five
(`maxParams`, [`Recheck/Cert.lean:37`](../IxCC/Recheck/Cert.lean); the
`rt.params` decline). The linked object's input is `Nat × List Nat`
(`Recheck.sound`, [`Recheck/Proof/Soundness.lean:50`](../IxCC/Recheck/Proof/Soundness.lean)).
Compile claims require level-monomorphic roots with all-`Nat` parameters,
and results that are scalars or field-less enumerations on the immortal and
zero-RC policies, or first-order constructor trees found by
`Readback.discover` on the plain-RC policy
([`CompileClaim.lean:269-304`](../IxCC/CompileClaim.lean)).

**Options.**
- (a) **A byte ABI**: a root may take `ByteArray` arguments and return a
  `ByteArray`; the caller writes bytes into the region and passes a
  pointer; any structure is decoded and encoded by compiled Lean code inside
  the program.
- (b) Heap arguments: the caller builds first-order constructor trees in
  the region with a proved encoder, the inverse of today's readback.
- (c) Both.

**Recommendation: (a) first**, then (b) where measured. With (a) the only
new ABI fact is the layout of one object kind, and every decoder is covered
by the compiler's own theorem. (b) saves a decode pass but needs an encoder
per first-order type with a `readback (encode v) = v` lemma.

**Proof obligation.** The input side of the object theorem changes from
`Nat × List Nat` to a list of first-order argument values, with a
precondition that the driver placed each `ByteArray` (or tree) in the region
as the heap invariant requires; the driver contract (`X86.Driver.Ok`) gains
that clause; results read back through the existing tree readback plus the
`ByteArray` case.

**Trusted base.** The driver model (`x86-phase1-runtime-driver-model` in the
[ledger](trusted-extern-ledger.md)) grows to the new calling convention;
the standalone executable's shell and the native suites' test shell and host
(`IxCCTests/Exe/TestShell.lean`, `IxCCTests/Rt/Native.lean`) must agree with it.

**Dependencies.** DR1, DR3.

**Size [estimate].** 3–6k lines.

**Exit.** A root `ByteArray → ByteArray` (a parser into a tree and back)
compiles, certifies and round-trips natively, as a test executable; the five-argument
limit no longer binds, because one argument can carry a structure.

## DR7. What the compile claim binds

**Status: planned** (Phase 3).

**Current state.** `CompileClaim` holds `env`, `target`, `policy`,
`abiArity` and `elfHash` ([`CompileClaim.lean:98-103`](../IxCC/CompileClaim.lean)).
The verifier recomputes the root's readback type from the program and checks
it; the claim itself does not carry the ABI. IxCC and ix encode `abiArity` with the
same Ixon v4 `N0` code, and the compile claim has its own tag, 13 (`E8 05`),
distinct from the role-binding section's 11. The decoders
still accept any arity below 2^64; a verifier refuses one that is not the
root's parameter count.

**Design.** Replace `abiArity` with an ABI
descriptor: per parameter and for the result, a first-order type over the
environment's inductives by address (`Nat`, an inductive, `ByteArray`, a
fixed-width word), plus the interpretation entries of DR5 and the selected
policy. A verifier then knows how to call the object without recomputing
anything from the certificate. Composition with the proofs that discharge the
grounded statement's premises needs two more fields, planned earlier in SP-0
of the [certification design](certification-design.md#sp-0-same-bytes-and-the-conditional-statement):
the role table and the digest of the checked source program's image.

**Proof obligation.** `verifyBytes_*_sound` state their conclusion at the
descriptor's types; the descriptor must equal what `Recheck.Root` discovers,
which the verifier checks.

**Trusted base.** No change; ix's `Ix.Claim` codec changes in step with IxCC.

**Dependencies.** DR6, DR5.

**Size [estimate].** 1–3k lines across IxCC and ix.

**Exit.** A claim for an DR6 root verifies in both IxCC and ix; the claim
codec's round-trip tests cover arities and descriptors above 127.

## DR8. Universe polymorphism and type parameters at roots

**Status: planned** (decision only).

**Recommendation.** Keep roots level-monomorphic and free of type
parameters. A user who wants to compile a polymorphic definition writes a
monomorphic `entry` (as the benchmark fixtures already do), and the claim's
target is that constant. Inside a program, polymorphism costs nothing:
erasure is level-exact per profile, and types are erased.

**Cost to change later.** Accepting a polymorphic root would mean binding
the instantiation (levels and type arguments) in the claim and checking it
against the readback type; about 1–2k lines [estimate], no new trust.

## DR9. Effects and IO

**Status: planned** (state-machine roots), **research** (traced IO).

**Motivation.** The IxOS monitor and any program that interacts.

**Current state.** Compiled programs are pure. The theorems are already
stated in a traced shape so that events can be added without restating
them (decision D-1: `TLang` in
[`Sem/TracedTransform.lean`](../IxCC/Sem/TracedTransform.lean), `TSim` in
[`Sem/TracedSim.lean`](../IxCC/Sem/TracedSim.lean)); every level runs with an
empty environment and no events. Lean's `IO` actions bottom out in
`@[extern]` opaque constants with no kernel body, so `IO` code cannot be
compiled.

**Options.**
- (a) **State-machine roots.** The program exports
  `step : State → Request → State × Response`, a pure function. A small
  host (the native suites' test shell and its Lean host today, a standalone
  executable's request shell later, the IxOS tender on bare metal) performs the
  effects and calls `step` repeatedly, passing the returned state back in.
  Correctness per call is the existing pure theorem; across calls it is a
  session theorem over returned and re-passed heap values.
- (b) **Traced events.** Effects are events answered by an oracle, the
  evaluators carry the trace, and the statement becomes trace refinement for
  every oracle. This is what D-1 prepared.

**Recommendation: (a) now, (b) later.** (a) needs no new semantics and is
the MirageOS-style split the IxOS design already uses. (b) is needed only
for programs that must interleave effects within one computation.

**Proof obligation.** (a): a session theorem in which each call's state
argument is the previous call's owned result. Today's operations exist for
numeric roots: `Returned.release_public`
([`Recheck/Rc/Proof/PublicRelease.lean:46`](../IxCC/Recheck/Rc/Proof/PublicRelease.lean))
and `recycled_entry` ([`Recheck/Rc/Proof/Reentry.lean:33`](../IxCC/Recheck/Rc/Proof/Reentry.lean)).
They need a heap argument (DR6) and an induction over the session. (b): the
traced simulation through every level, an oracle-indexed source semantics,
and an event-preserving x86 call into the host.

**Trusted base.** (a): the host is outside the theorem, as the test shell is
now; for IxOS the tender is a new ledger row. (b): the event interface
becomes a specification assumption.

**Dependencies.** DR6 and DR1 for (a).

**Size [estimate].** (a) 3–6k lines; (b) not estimated.

**Exit.** (a): a corpus state machine (a counter map over `ByteArray`
requests) runs a session of at least 1,000 calls in a test executable with its
values checked against Lean's interpreter, and the session theorem is
fenced.

**Standalone executables (2026-11-14).** The owner decided that compiled
programs run as standalone executables with no C driver
([standalone executables](standalone-executables-design.md)). That design
puts both options over one platform interface (arguments, write, read, exit,
clock): option (a) is its first stage, with the "small host" now an
IxCC-written shell on Linux and the IxOS tender on bare metal, never a C
driver; option (b) is its later stage, in which the program calls platform
procedures (machine-level code generated from Lean, the only place the
system-call instruction appears) and each call is a traced event, which is
what ordinary Lean `IO` needs. A numeric form of (a), on `Nat` states with no
heap carried across calls, can come before DR6: implemented as X2
([standalone executables](standalone-executables-design.md#x2-as-implemented)),
with the session theorem over the linked-object model.
