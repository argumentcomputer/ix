# Data, roots and effects

Written 2026-11-09. **Status: planned**, except where a line says
*implemented*. This document designs the data the compiler must support
beyond `Nat` and first-order constructors (D1–D5), the interface of compiled
roots and compile claims (R1–R3), and effects (E1). Bignums have their own
[design](bignum-design.md), closures theirs ([closures](closures-design.md)),
and the semantic obligations theirs ([certification](certification-design.md)).
The [roadmap](roadmap.md) owns the phases and exit criteria.

Every item states the motivating target, the current state, the options and
a recommendation, the proof obligation, the effect on the trusted base, its
dependencies, a size marked as an estimate, and an exit criterion.

Sizes are estimates in lines of Lean (code plus proof). Their basis is the
size of the nearest existing IxCC component (measured with `wc` on
2026-11-09: `Fir/` 3.8k, `Own/` 9.5k of which `Own/Plain/` 6.1k, `Cfg/Rc/` and
`Rt/Rc/` 28.6k together, `Rt/` 21.9k) and the per-item estimates of the
pre-merge systems plan (untracked, `plans/systems/` in the Compilatr.ix
workspace).

## D1. Heap completion

**Status: in progress** (Phase 2). The bounded plain-RC route is
implemented; the rest is planned.

**Motivation.** K2 and K3 (lists and trees), every flagship, and the cells
that closures (P8), arrays and bignums need.

**Current state.**
- *Implemented.* Immortal cells, bump-allocated and never freed
  ([`Rt/Layout.lean`](../IxCC/Rt/Layout.lean)).
- *Implemented.* The bounded plain-RC route: shared constructors with 1 to
  31 fully scanned fields and tags up to `Rt.maxTag`
  ([`Cfg/Rc/Native.lean:62`, `:81`](../IxCC/Cfg/Rc/Native.lean)); size-class
  free lists with one-cell bump refill and iterative release
  ([`Rt/Rc/Procs.lean`](../IxCC/Rt/Rc/Procs.lean)); a checker that requires
  the proposed ownership map to equal the canonical producer's
  (`checkPlainMap`, [`Own/Plain/Check.lean:225`](../IxCC/Own/Plain/Check.lean));
  `Plain.checked_program_refines`
  ([`Own/Plain/Proof/Candidate.lean:12`](../IxCC/Own/Plain/Proof/Candidate.lean))
  and the object theorem `Recheck.RcReplay.sound`
  ([`Recheck/Rc/Proof/ObjectSound.lean:37`](../IxCC/Recheck/Rc/Proof/ObjectSound.lean)).
  `List.reverse` from Lean's library compiles and runs through it
  ([`fixtures/rc/real-source`](../fixtures/rc/real-source/README.md)).
- *Not implemented.* Scalar fields in cells; constructors with more than 31
  fields and a large-object path; reset/reuse and the runtime uniqueness
  test; static reuse from `unique` contracts; borrowed parameters beyond the
  zero-RC policy selection; inline fast paths (each RC event is a procedure
  call today, 2026-11-08 review A5-8); static constant objects (closed
  constructor trees as immortal read-only cells, `Rhs.const` in the Fir
  design, [`Fir/Syntax.lean:29-31`](../IxCC/Fir/Syntax.lean)). The Own IR
  has no `reset`, `reuse` or credit forms
  ([`Own/Syntax.lean:14-20`](../IxCC/Own/Syntax.lean)).

**Options for the ownership checker.** (i) Keep "equal to the canonical
producer": safe, but leaves no room for optimisation. (ii) The proved static
linear typing of Own described under
[Ownership](compiler-design.md#ownership-reference-counting-and-reuse).
(iii) Per-function translation validation of RC placement.
**Recommendation: (ii)**, keeping (i) as the always-accepted fallback, as
the compiler design already intends. (iii) duplicates (ii) with weaker
reuse.

**Statics.** Closed constructor trees (and, after P8, field-less closure
constructors) become immortal cells in the object's read-only data instead
of being rebuilt at each use; K3's `binarytrees` needs this for parity, and
string literals (D4) and large `Nat` literals (bignums) reuse it.

**Proof obligation.** Generalise `Plain.checked_program_refines` to "a
program the Own checker accepts refines its Fir program up to heap
isomorphism", relative to Fir's semantics; extend the Cfg.Rc and Rt.Rc data
refinement (heap invariant, `ObjAt`) to scalar fields, reuse, the
uniqueness test and immortal read-only cells, and the ELF writer to a
read-only data section under the existing object checks. It composes into
`Recheck.RcReplay.sound` with unchanged statement.

**Trusted base.** No change.

**Dependencies.** None upstream. D2–D4, P8 and the bignum cells depend on
scalar fields and general layouts.

**Size [estimate].** 20–40k lines, by comparison with the bounded route
(`Own/Plain/` 6.1k plus `Cfg/Rc/` and `Rt/Rc/` 28.6k).

**Exit.** K0 (`List.reverse`) refrozen with the final Phase 1.5 producer;
the K2 and K3 programs of
[`benchmarks/fixtures`](../benchmarks/fixtures/README.md) frozen as Ixon
closures, compiled under `--rc auto` and certified, with `rbmap_fbip`'s
annotated twin measured against the plain one.

## D2. Fixed-width integers and `Int`

**Status: planned** (Phase 3).

**Motivation.** BLAKE3 and `qsort` (K4); the bignum library's limbs; IxCK,
whose executable closure uses `UInt64`, `UInt8`, `USize` and `Int`
throughout (grep counts in the 2026-11-09 IXCC-ROUTE review: `UInt64` 196,
`UInt8` 118, `Int` 49, `USize` 7); IxOS, where addresses and page-table
entries are 64-bit words.

**Current state.** There are no fixed-width primitives. Erasure unboxes
single-field structures ([Relevance and
erasure](compiler-design.md#relevance-and-erasure)), so `UInt64` (a structure
over `BitVec 64`, over `Fin (2^64)`) arrives at Lir as a tagged `Nat`; a value
at or above 2^63 then fails with `natOverflow` ([`Rt/Layout.lean:35`](../IxCC/Rt/Layout.lean)).
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
   `USize` is fixed at 64 bits through the interpretation table of D5.
3. `Int` first compiles as ordinary data through its reference bodies
   (needs only D1). Then a signed small representation and primitives;
   large values use the bignum library (Phase 4).

SrcEval needs one rule for raw words to be sound: a bounded construction
whose erased proof is false (for example `UInt64.ofNatLT n h` with
`n ≥ 2^64`) is stuck rather than evaluated, so a compiled range guard fails
only where the source is stuck, which the `GoesWrong` disjunct covers.

**Proof obligation.**
- Per primitive, a *conservativity lemma*: the primitive's meaning equals
  the pinned body's, proved in Lean against the body, relative to SrcEval.
  (The existing `Nat` primitives are pinned by address and type only; their
  agreement with the kernel bodies is tested, not proved. The same lemma
  shape closes that gap: 2026-11-08 review A2-9.)
- Fir's value relation gains `nat n ~ word w ↔ n = w.toNat`, inside
  `Fir.convert_correct`; the representation checker's soundness is a
  subject-reduction lemma over Anf.
- One lowering lemma per operation at Lir, and one selection lemma per new
  x86 rule. The table has `mul`, `div`, shifts, rotates, `bswap`, `movzx`
  and `movsx` rows, and no `adc`/`sbb`
  ([x86 instructions](x86-encoded-instructions.md)).

**Trusted base.** New x86 rows join the existing table and its
hardware-differential gate. The `USize` width is an interpretation entry
(D5).

**Dependencies.** D1 (boxed 64-bit cells are cells with a scalar field).

**Size [estimate].** 10–20k lines, from the systems plan's range-checker,
representation and fixed-width items (RL1a, RL1b, NU0, NU1).

**Exit.** K4's `blake3` (`Blake3.Pure` from `argumentcomputer/Blake3.lean`,
known-answer vectors) and `qsort` (`UInt32`, `Array`); a boundary family like
`phase1-boundary` for every fixed-width operation at 2^63 and 2^64.

## D3. Arrays and byte arrays

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
or certified inference. (c) Trust Lean's C array runtime. Rejected, as in D2.
**Recommendation: (b).**

**Proof obligation.** Per primitive, a conservativity lemma against the
reference body (on `toList`); an Own rule for in-place `update` of a unique
array; the heap invariant gains array cells (size, capacity, elements, raw
bytes for `ByteArray`), with one lemma per runtime procedure (growth,
copy-on-share); readback of `ByteArray` results.

**Trusted base.** No change.

**Dependencies.** D1 (scalar fields, large objects, the uniqueness test);
D2 for `UInt8` and `UInt64` elements.

**Size [estimate].** 10–20k lines, from the systems plan's memory-control
item (MM1) and the pre-merge roadmap's runtime item RT-3.

**Exit.** K4 `qsort`, `unionfind` (`Array` and `StateT`) and `hashmap`; a
root taking and returning a `ByteArray` through the byte ABI (R1).

## D4. Strings

**Status: planned** (Phase 3).

**Motivation.** Error values (IxCK builds 245 `msg!` strings, IXCC-ROUTE
§2.2), `panic!` messages, certificate parsing in a self-hosted checker,
K4's `deriv`.

**Current state.** A string literal in a relevant position is declined at
admission and at erasure (`unsupported` in
[`Src/Admit.lean:24`, `:155`](../IxCC/Src/Admit.lean); `erase-string` in
[`Lam/Erase/Term.lean:565-566`](../IxCC/Lam/Erase/Term.lean));
`Decline.stringLength` and `Decline.withPanic` record it
([`Decline.lean:42-46`](../fixtures/corpus/phase1-decline/src/Decline.lean)).

**Design.** In Lean's `Init/Prelude.lean`, `String` wraps the UTF-8 bytes in a
`ByteArray` with an erased validity proof, so a string is a `ByteArray` at
run time once D3 exists, and string functions compile from their Lean bodies.
Literals become static `ByteArray` objects (the statics of D1).
**Recommendation:** strings through D3 and statics; no string-specific
primitive until a K4 row needs one.

**Proof obligation.** SrcEval's string literal (exact, as today) relates to
its static object by the `ByteArray` readback.

**Trusted base.** No change; the loader assumption already covers mapped
sections.

**Dependencies.** D1 (statics), D3.

**Size [estimate].** 2–4k lines; statics are counted under D1.

**Exit.** K4's `deriv`; `Decline.stringLength` and `Decline.withPanic`
compile (the latter returning the `Inhabited` default, which is the
kernel meaning of `panic!`; printing the message is not part of the
semantics).

## D5. Library structures and opaque constants

**Status: planned** (Phase 3), the interpretation table **research**.

**Motivation.** `Std.HashMap` and `HashSet` are pervasive: IxCK threads 13
memo maps through its cached state (`IxCK/Kernel/Cached/StateC.lean`).

**Current state.** Nothing compiles them. Two obstacles besides D1–D3:
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
  at a cost in the target's own code (IXCC-ROUTE recommends this for IxCK
  for other reasons).

**Recommendation:** (a) for generality, recording the interpretation in the
claim; (c) for IxCK if its owners want an unconditional statement. (b) is
not planned. Whether a claim may carry an interpretation at all is an owner
decision ([roadmap](roadmap.md#open-decisions)).

**Proof obligation.** For (a): SrcEval and the table check accept an
interpreted opaque only through the recorded entry; the stage-2 statements
of the [certification design](certification-design.md) quantify over models
that agree with the interpretation. Hash-map functional correctness is not
the compiler's obligation: it compiles the library's code, whatever it
computes.

**Trusted base.** (a) adds one assumption per interpreted opaque: that
"meaning" is read relative to the recorded function. It adds no native code.

**Dependencies.** D1–D3, P8 (`BEq`/`Hashable` dictionaries), D2's `USize`.

**Size [estimate].** 2–4k lines for the interpretation table and claim
field; the library itself is compiled, not written.

**Exit.** K4's `hashmap`; a corpus root over `Std.HashMap` with `String`
keys.

## R1. Structured roots and the byte ABI

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
([`CompileClaim.lean:187-226`](../IxCC/CompileClaim.lean)).

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
`fixtures/x86/runtime_driver.c` must agree with it.

**Dependencies.** D1, D3.

**Size [estimate].** 3–6k lines.

**Exit.** A root `ByteArray → ByteArray` (a parser into a tree and back)
compiles, certifies and round-trips through the C driver; the five-argument
limit no longer binds, because one argument can carry a structure.

## R2. What the compile claim binds

**Status: planned** (Phase 3).

**Current state.** `CompileClaim` holds `env`, `target`, `policy`,
`abiArity` and `elfHash` ([`CompileClaim.lean:95-101`](../IxCC/CompileClaim.lean)).
The verifier recomputes the root's readback type from the program and checks
it; the claim itself does not carry the ABI. Two encoding defects are open
(2026-11-09 review B4-2: IxCC and ix encode `abiArity` differently from 128
up; B4-3: the claim reuses a tag of the role-binding section).

**Design.** Fix B4-2 and B4-3 first. Then replace `abiArity` with an ABI
descriptor: per parameter and for the result, a first-order type over the
environment's inductives by address (`Nat`, an inductive, `ByteArray`, a
fixed-width word), plus the interpretation entries of D5 and the selected
policy. A verifier then knows how to call the object without recomputing
anything from the certificate.

**Proof obligation.** `verifyBytes_*_sound` state their conclusion at the
descriptor's types; the descriptor must equal what `Recheck.Root` discovers,
which the verifier checks.

**Trusted base.** No change; ix's `Ix.Claim` codec changes in step with IxCC.

**Dependencies.** R1, D5.

**Size [estimate].** 1–3k lines across IxCC and ix.

**Exit.** A claim for an R1 root verifies in both IxCC and ix; the claim
codec's round-trip tests cover arities and descriptors above 127.

## R3. Universe polymorphism and type parameters at roots

**Status: planned** (decision only).

**Recommendation.** Keep roots level-monomorphic and free of type
parameters. A user who wants to compile a polymorphic definition writes a
monomorphic `entry` (as the benchmark fixtures already do), and the claim's
target is that constant. Inside a program, polymorphism costs nothing:
erasure is level-exact per profile, and types are erased.

**Cost to change later.** Accepting a polymorphic root would mean binding
the instantiation (levels and type arguments) in the claim and checking it
against the readback type; about 1–2k lines [estimate], no new trust.

## E1. Effects and IO

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
  host (a C driver today, the IxOS tender on bare metal) performs the
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
They need a heap argument (R1) and an induction over the session. (b): the
traced simulation through every level, an oracle-indexed source semantics,
and an event-preserving x86 call into the host.

**Trusted base.** (a): the host is outside the theorem, as the C driver is
now; for IxOS the tender is a new ledger row. (b): the event interface
becomes a specification assumption.

**Dependencies.** R1 and D1 for (a).

**Size [estimate].** (a) 3–6k lines; (b) not estimated.

**Exit.** (a): a corpus state machine (a counter map over `ByteArray`
requests) runs a session of at least 1,000 calls in the C driver with its
values checked against Lean's interpreter, and the session theorem is
fenced.
