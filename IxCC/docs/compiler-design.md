# Compiler design

This reference holds the enduring architecture and design constraints. The
[roadmap](roadmap.md) owns priorities, delivery state and acceptance gates.
Normative wire and trust contracts remain in their focused specifications:
- [Ixon v4](ixon-v4.md);
- [x86 instructions](x86-encoded-instructions.md);
- [x86 streams and objects](x86-stream-objects.md);
- the [trust ledger](trusted-extern-ledger.md).

Reviewed 2026-10-08; pass identifiers and the plans for later extensions
added 2026-11-09. The scalar pipeline and a bounded checked plain-RC
path are implemented. General ownership optimizations and later heap features
below remain extensions. Source adequacy, Phase 1.5 producer integration,
final fixture refreeze and full promotion validation remain open. The earlier pipeline, its IRs
and their contracts are on branch `jcb/ixby-archive`.

Where this document describes something not yet built, the section or row
says *planned*. The designs of the planned extensions are in their own
documents (see [Planned extensions](#planned-extensions)).

## Principles

- **Lean semantics, verified checkers.** IxCC is written and proved
  in Lean. Expensive analyses and profitability heuristics may be untrusted
  only when a proved checker validates their output, or when the
  transformation is proved correct for every heuristic choice. A rejected
  optimisation falls back to a checked baseline; invalid input is an error.
- **Contracts are lower bounds.** Ixon usage, ownership, locality and
  borrow contracts are part of source identity.
  - The compiler honours every written contract and never weakens one.
  - It may establish a *stronger* guarantee (unique, local, borrowed,
    erased, one-shot) only through a proved checker on the compiled program.
  - Inferred guarantees never change Ixon bytes or addresses.
- **Small, separately proved passes.** Each pass has one responsibility and
  its own simulation. Core relations carry values and memory, not exact
  counters or costs. Cost, space and leak-freedom are separate, optional
  theorems.
- **Executable semantics.** Every IR has an executable, clocked semantics, so
  it can be tested differentially before and alongside its proofs.
- **No new axioms.** Public theorems use only `propext`, `Classical.choice`
  and `Quot.sound`, each with an exact fence. Runtime services, the ISA model
  and build inputs are recorded in the trust ledger.

## Correctness statement

For a compiled root `f` with first-order argument and result types:
- If the native entry returns `r` on inputs `xs`, then either `r` reads
  back as a value `v` and `f xs` denotes `v`, or the source evaluator goes
  wrong on `f xs` (gets stuck or traps), in which case nothing is claimed.
  This is CompCert's "safe source" condition; a planned shape typing
  removes it.
- For a source that does not go wrong, every other outcome is an explicit
  resource failure (heap, stack, or Nat overflow until bignums) or an
  unfinished run. Nat overflow is a target failure: every IR above Lir has
  exact `Nat`.

This is partial correctness plus safety; termination is not claimed. The
statement is established in two stages:
1. **Against the source evaluator.** Its rules form the published semantic
   contract.
2. **Against every model of the environment accepted by ix-certified's
   `Ix.Kernel`.** A single adequacy theorem relates evaluator results to
   denotations.

**What is proved (Phase 1, stage 1).** `Recheck.sound`
(`IxCC/Recheck/Proof/Soundness.lean`) states the correctness
statement at stage 1 for the object the checked compiler path writes. Its
two hypotheses:
- `Recheck.run cfg P c = .ok a`: the recheck path accepted source `P`
  with certificate `c` and produced artifact `a`;
- `D.Ok n`: a driver `D` meets the driver contract, plain arithmetic on
  the region, stack and return address for an object with `n` bytes of
  text. `Recheck.driver_exists` shows that one exists for every artifact.

For every such `D` and every input (a root and its arguments), the object
linked under `D` (`X86.Linked`: `cx_init`, then the root's export found by
its ELF symbol, run on the byte machine) satisfies three clauses:
1. If it returns an observation `w`, then either the checked source
   returns a value whose view is `w`, or the source goes wrong.
2. If the source does not go wrong, the object never goes wrong.
3. If the source times out at every clock, the object times out at every
   clock or ends in a resource failure.

"Goes wrong" (`Front.GoesWrong`) has three cases: the source gets stuck,
it traps, or it returns a value that the root's view does not accept at
the root's result type. Lean's typing excludes the third case, but the
recheck path does no type checking and readback goes by tag, so stage 1
keeps it.

Only the root's result is observed, read back at its first-order type;
Phase 1 programs are scalar and pure. The theorem uses only the three
standard axioms. Reading it as a fact about the native executable rests
on three specification assumptions in the
[trust ledger](trusted-extern-ledger.md):
- `X86.Driver`/`X86.Linked` model `runtime_driver.c` and the linker's
  symbol lookup (`x86-phase1-runtime-driver-model`);
- the byte machine is the processor (`x86-v0-local-semantics`), and the
  system loader maps the object as `ELFRead` parses it
  (`x86-v0-elf-writer`);
- SrcEval is the source's meaning (stage 2 is not proved).

The separate `Recheck.compiled_sound` theorem now derives those same stage-1
guarantees from success of the actual byte-input `Recheck.compile`.
`compile_parts` retains the exact ingress/producer/replay chain, and
`compile_bytes` identifies the emitted bytes with its checked object. These
statements expose the existing native BLAKE3 dependency through ingress and the
relevance producer; their exact fences are separate from the standard-axiom
replay fences. The source remains the artifact's checked Src program. Pure
decoding and this composition theorem do not establish kernel-model adequacy.
See the [compile boundary](compile-boundary.md).

**Bounded plain-RC path.** The separate
[`IxCC.Recheck.RcReplay`](../IxCC/Recheck/Rc/Replay.lean) API
provides serialized `Cert` values and `run`; the separate
[`produce`](../IxCC/Recheck/Rc/Produce.lean) entry constructs candidates. Its
[`object_refines` and `sound`](../IxCC/Recheck/Rc/Proof/ObjectSound.lean)
prove the same SrcEval-relative return, safety and divergence clauses for the
actual emitted RC object. The final premises remain successful `run` and
`X86.Driver.Ok`; `driver_exists` proves that the driver contract is inhabited.
The source `GoesWrong` qualification and the source/processor/loader/driver
assumptions above remain explicit. The theorem is about accepted replay,
not a stronger theorem for ingress or `produce`.

The complete constructor tree is observed at the root's discovered first-order
result type. This path composes actual initialization, checked source and
ownership code, borrowed projection followed by explicit acquisition, native
allocation/count/release effects, fused branches, calls, layout and the existing
backend/object proofs. It keeps finite heap/count/stack/Nat failures explicit;
no premise assumes successful target execution or an immortal heap. Its
single-call object language initializes before calling the selected root.
The separate release/reentry operation contract is described under
[Runtime](#runtime).

Validation retains the earlier abstract-Cfg gates independently of the native
certificate path: `IxCCTests.Cfg.Rc.Proofs` checks all 29 original
marker/map/scope/bounds examples, and `tests-cfg-rc` executes complete value/heap,
timeout and bridge ownership controls. They are test dependencies of the
required proof/runtime checks, not imports of the compiler algorithms.

`tests-pipeline-rc` follows the actual serialized RC certificate through all
available IR evaluators and the emitted bytes, comparing complete values to
independent source-level list/pair formulas. Test-side counters observe the
production RC Cfg stepper and distinguish executed allocation/retain/release
events from final heap totals. Native controls compare the C decoder and Lean
memory readback, reject independently corrupted emitted objects before linking,
and separate root heap exhaustion from initializer refusal using successful
neighbors. These bounded regression gates add no correctness premise or native
cost theorem; their portable and native modes have separate required checks.

The recheck path separately authenticates resource profile bytes and selected
equation bindings with pure hashing. This establishes the identity of supplied
data; it does not establish resource safety. The native resource-admission API
is separate from `compile`. See the [compile and recheck boundary](compile-boundary.md)
for the declaration-level dependency inventory and the obligations of a
future theorem about `compile`.

The required source suite tests resource-bound `csimp` rejection with an
otherwise valid redirect that is accepted without a resource context.
The ownership suite also uses authentic historical annotated/plain recursive
`len` fixtures: both reach complete Src and Fir results; the annotated case
passes checked immortal Own, and the plain twin passes checked plain RC Own.
The annotated erased parameter remains outside the plain-RC domain. These
consumer regressions authenticate retained bytes and preserve the refusal
boundary; they do not establish arbitrary profile semantics or final producer
admission. Their provenance is recorded in the
[historical fixture directory](../fixtures/ownership/historical/annotated-recursion-cb68/README.md).

The required Lam suite also checks sixteen synthetic evaluation-order cases
through `Src.Recheck.run`, lazification and erasure. Checked direct cases demand
only the selected minor and dispatch before evaluating an extra argument;
ordinary wrappers evaluate their strict arguments before entering the body.
Both evaluators must match explicit value, trap or timeout expectations at two
clocks. These controls establish the tested consumer behavior; their synthetic
types and addresses supply no kernel admission or resource-profile verdict.

**Upstream certification boundary.** The October 8
[roadmap assessment](roadmap.md#phase-15-priorities-after-the-certification-work)
distinguishes byte/source association (W/W+), strong-model pullback for
direct/raw source cones (S), and the weaker public-value-model endpoint for
supported changed-value cones (S+a). All relate an upstream source installation
to an admitted Ixon environment under their own premises. Composition here
still needs authenticated decoding, the selected unfolding-table interpretation,
the resource-contract/relevance relation and a SrcEval adequacy theorem.
Upstream metadata erasure does not prove ownership-contract preservation.

**Statement shape (decision D-1).** Per-level and pipeline theorems are
stated in the traced shape of `IxCC.Sem`, so IO can be added without
restating them:
- A traced language runs a program on an input under an abstract
  environment and returns, at every clock, the result with the events
  performed so far (`TLang`, `Traced`).
- The traced simulation `TSim` has three clauses: forward, a timeout clause
  whose target trace is a prefix of the source's, and progress (the target
  keeps up with the source's events). `TRefines` compares traced behaviours
  up to resource failure.
- Phase 1 levels are pure and lift (`TSim.ofPure`, `Refines.ofPure`,
  `Transform.lift`), with the environment `Unit` and no events. Concrete
  events, the oracle and refusal are the IO design's choices.

**Evaluator interface.** Simulation proofs reason through each evaluator's
bind-form unfolding lemmas (one equation per rule, sequencing as
`Result.bind`), with the combinators of `IxCC.Sem` (`Agrees.bind`,
`Result.Dom.bind`, `ClockMono.bind`, `SimUpTo.bind` and the `Result.bind`
inversions), never by unfolding the evaluator's `match`. Moving an
evaluator to a traced, environment-reading monad then changes its unfolding
lemmas and adds one case, not the per-construct proofs.

## Pipeline

| IR | Form | Semantics | Main obligation |
| --- | --- | --- | --- |
| **Src** | Closed, relevance-annotated kernel terms from Ixon v4 plus an unfolding table | Clocked big-step environment machine. It never evaluates irrelevant positions and calls lazy constants by name. | Adequacy against `Ix.Kernel`'s model |
| **Lam** | Erased λ-calculus: □, constructors, `case`, recursive definitions, primitives, `trap`; binder contracts retained | Clocked big-step | Erasure simulation |
| **Anf** | A-normal form with join points, known calls, and (until P8) local functions and unknown calls | Clocked big-step | Logical relation, clock-indexed on computations; heuristic-parametric rewrites |
| **Fir** | First order: top-level functions, known calls, join points, tail calls. No closures: Anf → Fir declines them until P8 (planned) defunctionalises them in Anf; there are no closure objects, `pap` or `apply` ([closures design](closures-design.md)) | Clocked big-step | Forward simulation |
| **Own** | Explicit ownership. Implemented: the immortal fragment and `Own.Plain`'s `inc`/`dec` actions. Planned: borrowed parameters, reset/reuse credits, unique and local kinds | Clocked big-step over an abstract RC heap | Proved ownership checker ⇒ refinement of Fir |
| **Cfg** | Blocks with parameters over the same operations | Clocked small-step | The single big-step → small-step bridge |
| **Lir** | Words, memory, compare-branch, calls, runtime procedures | Clocked small-step | Heap → memory data refinement |
| **Xv / Xl** | x86-shaped operations on virtual registers, then on registers and slots | Small-step | One lemma per selection rule; allocation validator |
| **x86** | Typed x86: frames, ABI, layout | `X86.Eval` | Frame layout, layout, and generic `SafeSteps` into E1/E2 |

### Pass identifiers

Code comments and certificates name the Lam and Anf passes P0 to P9. The
identifiers come from the pre-merge design note on erasure and the middle
end (note 02 §8, untracked, not in this repository); this table is now their
definition.

| Id | Pass | Module | Status |
| --- | --- | --- | --- |
| P0 | Erasure, Src → Lam | [`Lam.Erase`](../IxCC/Lam/Erase.lean) | Implemented |
| P1 | ANF conversion, Lam → Anf; join point for every non-tail `case` | [`Anf.Convert`](../IxCC/Anf/Convert.lean) | Implemented |
| P2 | Shrink: the rewrite rules of [`Anf.Walk`](../IxCC/Anf/Walk.lean), iterated per global | [`Anf.Shrink`](../IxCC/Anf/Shrink.lean) | Implemented |
| P3 | Inlining of listed callees and CAFs | [`Anf.Inline`](../IxCC/Anf/Inline.lean) | Implemented, bounded |
| P4 | Specialisation on masked arguments, with a fixed-parameter checker | [`Anf.Specialize`](../IxCC/Anf/Specialize.lean) | Implemented, bounded |
| — | Pruning of globals unreachable from the roots | [`Anf.Prune`](../IxCC/Anf/Prune.lean) | Implemented |
| P5 | Dead parameters (worker/wrapper; the key `GKey.worker` exists) | — | Planned |
| P6 | Contification, arity raising, uncurrying | — | Planned |
| P7 | Measured extras: accumulators, multi-value returns, common subexpressions, float-in | — | Planned, each when a measurement asks for it |
| P8 | Closed-world defunctionalisation | — | Planned, Phase 2 ([design](closures-design.md)) |
| P9 | Dispatch narrowing by untrusted flow facts | — | Planned, Phase 2–3 ([design](closures-design.md#p9-and-the-flow-oracle)) |

The implemented schedule is in [`Anf.Pipeline`](../IxCC/Anf/Pipeline.lean);
P1 has no certificate data, P2 to P4 read their choices from the
certificate.

### Middle-end budgets

The middle end's certificate chooses which callees are inlined where, how many
shrink rounds run and which call sites are specialised, and on the byte-level
verifiers the claimant also chooses the program. Without bounds one certified
step could ask for work and recursion far beyond its input: a single `inline`
step on a 1.1 KB closure asked for about 16.8 million copied bindings and made
`ixcc check-cert` abort with a stack overflow (review of 2026-11-09, item 2).
The replay therefore refuses a step, with an ordinary `anf.replay` error, as
soon as it passes one of these budgets ([`IxCC/Anf/Budget.lean`](../IxCC/Anf/Budget.lean)):

| Budget | Bounds | Value | Largest committed value | Headroom |
| --- | --- | --- | --- | --- |
| `maxGlobalNodes` | one global, after P1 and after every step, and after every shrink round | 65,536 | 2,507 | 26× |
| `maxProgramNodes` | the whole program at the same points, and the running total while an inline or shrink step rewrites its globals | 1,048,576 | 4,935 | 212× |
| `Walk.maxCopy` | the nodes one walk walks again: inlined callees, β-reduced local functions, inlined join points, case-of-case alternatives | 65,536 | 1,583 (inline), 2,860 (shrink) | 22× |
| `Walk.maxFires` | rule firings in one walk | 8,192 | 500 | 16× |
| `Specialize.maxWork` | the work charged for the call sites a specialisation step examines | 67,108,864 | 1,615,803 | 41× |
| `Specialize.maxNodes` | the nodes of the specialisations those sites may build | 1,048,576 | 3,209 | 326× |

The counts stop early (`Exp.nodesUpTo` walks a worklist and stops past its
cap), so checking a budget costs no more than the budget. The largest values are
measured by `tests-corpus`, which replays the honest certificate of every
committed program step by step (every root of every corpus family, and `k1.ixe`,
`src-sortpoly`, `src-diag`, the ownership fixtures and the RC real-source
closure with all their roots: 158 programs) and fails if any reaches its budget.

A walk's native recursion depth is at most its input's nodes plus its copies,
so a refused step needs at most about 130,000 walk frames: `ixcc check-cert`
refuses R1's amplifiers within an 8 MiB Lean stack (`LEAN_STACK_SIZE_KB=8192`).
The front end before the middle end is not bounded this way: a closure whose P1
output holds a 65,535-node global needs more than 8 MiB (and at most 16 MiB) of
stack before the size check refuses it. Under shrink, the census counts read at
each binding walk the rest of its body, so one shrink round on a global of `n`
nodes still costs up to order `n²` steps.

## Source semantics and replacements

The source evaluator's rules:
- β and ζ;
- δ, either by the kernel body or by an unfolding-table entry;
- ι by recursor rules, with induction hypotheses left unevaluated;
- projection;
- Nat and String literal primitives with exact semantics;
- `Quot`;
- the cast family, which reduces to the minor premise;
- `False.rec`, which traps.

**Unfolding-table entries.** Each is proposed by untrusted metadata and
checked against the admitted closure.

| Entry | Meaning |
| --- | --- |
| `eqn f thm` | Unfold `f` through a kernel-accepted `thm : ∀ xs, f xs = rhs`, usually `f.eq_def`. Structural, well-founded, mutual and `partial_fixpoint` recursion then compile as direct recursion. |
| `csimp f g thm` | Use `g` for `f` through a kernel-accepted `thm : @f = @g`. |
| `case T` | `T.casesOn` becomes a primitive case. |
| `inline f` | Unfold matchers and `@[inline]`/`@[macro_inline]` definitions. |
| `lazy f` | Pass arguments by name (`ite`, `dite`, `cond`, `Bool.or`, …). |
| `prim f op` | Compute `f` with a primitive. The checker pins `f` by address and type; that the primitive's meaning equals the pinned kernel body is tested, not yet proved (a stage-2 obligation, [certification design](certification-design.md#c4-stage-k-semantic-adequacy-s8)). |

In the model, an accepted equation theorem forces its two sides to denote the
same value, so every table entry preserves meaning. When an equation is
missing, the kernel body is compiled instead: correct, but eager.

Rejected: `partial` and `unsafe` definitions, and extern opaques that are not
admitted as ledgered runtime services. `implemented_by` compiles the
reference body.

## Relevance and erasure

**The annotation.** Each binder, argument, let, constructor field and
constant is marked relevant, proof or type.
- An untrusted analysis produces it.
- A proved structural checker verifies its consistency: irrelevant binders
  have no relevant uses, call sites match callee parameters, constructor and
  projection fields agree. Prop eliminators are classified from kernel
  data (subsingleton with index-carried fields, or empty), not by address.
- Only two facts are soundness premises: every node is tagged, and every
  dropped constructor field is built from an irrelevant argument. The
  other checks give early, precise rejection.

**Why a wrong annotation is safe.** Marking a position irrelevant only makes
evaluation lazier, and the structural checks prevent erased code from
needing a value that was never computed. A wrong but consistent annotation
can make compilation fail or the source evaluator get stuck; it cannot make
the evaluator produce a wrong result. A stuck run falls under the
safe-source condition of the correctness statement.

**Erasure** then:
- replaces irrelevant arguments with □ but keeps every binder slot
  (dropping parameters of globals is a later Anf worker/wrapper pass), and
  drops irrelevant constructor fields;
- turns casts into identities;
- unboxes single-field structures (`Fin`, `Subtype`, `BitVec`, `UInt64`, …);
- represents field-free enums as immediates.

## Ownership, reference counting and reuse

The design in this section up to the plain-RC paragraph is the Phase 2
target and is **planned**: the untrusted passes, the linear-typing checker,
the checked fallback and the guarantee table are not built. What is
implemented is the conservative plain-RC route described from "The first
plain-RC implementation" on ([data design, D1](data-and-roots-design.md#d1-heap-completion)).

**Untrusted passes place reference-counting operations:**
- borrow inference;
- liveness-based dup/drop;
- drop and reuse specialisation;
- reset/reuse by shape and size class, with credits confined to one frame;
- `inc` coalescing.

**The proved checker** is a static linear typing of Own:
- owned values are consumed exactly once on every path;
- borrowed values are never consumed without an `inc`;
- unique values are never duplicated and come only from fresh allocation,
  unique parameters or unique results;
- credits are affine;
- static objects are never unique.

A checked program refines its Fir program up to heap isomorphism. When the
checker rejects the optimised output, the plain dup/drop output is used.

The first plain-RC implementation lives in `Own.Plain` and `Own.Rc`.
In the top-level compiler and claim/SIP verifiers
(`Own.Plain.selectRcPolicyForSrc` in `IxCC/Recheck/Rc/Produce.lean`),
`--rc auto` enriches the lowered `Fir.Program` with contracts from the
relevance-erased `Src.Program` (`enrichFirContracts`, propagating `.many`
defaults to unannotated functions) and inspects whether the resulting program is
zero-RC (`zeroRcProgram`); if so, it selects `.zeroRc` and uses the immortal
backend (`Recheck.run`). Otherwise it selects `.plainRc` and routes through the
bounded plain-RC replay path (`Recheck.RcReplay.run`), as `--rc on` does; when
the plain-RC certificate cannot be produced or its replay refuses it (for example
for a contract-annotated program outside the plain-RC domain, `!programDomain P`),
`RcReplay.produceAuto` falls back to `.immortal` (`AutoCompiled.immortal`, which
carries the refusal): the zero-RC-format certificate on the immortal backend,
rechecked by `Recheck.run`. `--rc auto` prints the policy it compiled under, and
`CompileClaim.produce`/`makeClaim` bind it in the claim. `--rc on` has no
fallback. On the plain-RC route, `Plain.checkPlainMap` (and
`Plain.checkContractPlainMap`, which validates against explicit per-parameter
borrow and return-ownership contracts) conservatively requires the complete
proposed function map to equal the canonical producer's map, including its trie
shape. It checks all numbered callees, lexical scopes, arities, ordinary shared
contracts, scanned constructor fields and fieldless resolved Boolean pins. Calls
execute that same checked map. A proposal outside this domain is explicitly
declined. This is the initial checker; the general ownership optimizations above
remain later work.

`Plain.checked_program_refines` proves Fir-relative execution from concrete
input denotations and exact external/root/heap-edge counts. Successful results
denote the complete Fir value, carry one owned output token, and preserve
successful external-root denotations. Source-stuck behavior retains the existing
qualification. With an initially ordered heap, `checked_program_reclaims`
also proves every cell dead after the output's final release when no external
owners remain. Ordering excludes disconnected reference cycles; numerical
balance alone does not prove their reclamation. The separate checked RC path
now composes these ownership invariants through
`Cfg.Rc`, the ordinary Lir runtime and certificate/object replay. The scalar
path and its public API remain available.

**Ixon resource admission** is an early diagnostic, not a compile gate: it may
reject annotated matchers and recursors that the ownership checker accepts.
It is not a premise of the compiler's theorems. Immediates satisfy every
ownership kind, so a literal may flow into a `unique` position.

| Guarantee | Effect in generated code |
| --- | --- |
| unique | No RC traffic and no sharing test; fields move; in-place reuse |
| shared | Dynamic RC; reuse guarded by a runtime uniqueness test |
| borrowed | No `inc`/`dec` for the view or anything projected from it |
| local | Borrowed convention now; region or stack allocation later, once measured |
| one-shot closure | Captures move; the closure cell is freed or reused without a test (closures are constructor cells after P8) |

None of these effects is implemented yet. Today a written contract can make
a binder irrelevant (`0`), and the contracts decide whether `--rc auto`
selects the zero-RC policy, as described above; they do not change the RC
operations the plain route places.

## Runtime

**Representation.**
- Words are immediates when the low bit is set: small `Nat` as `2n+1`,
  enums and other field-free constructors, `Bool`, `Char`, `UInt8/16/32`,
  and □.
- Objects carry one 8-byte header (scan count, size class, 16-bit tag,
  32-bit RC), followed by scanned fields, then scalar fields. Scalar fields
  are planned; every implemented layout is fully scanned.
- `UInt64` is raw in registers and scalar fields once a checked
  representation annotation exists (planned,
  [D2](data-and-roots-design.md#d2-fixed-width-integers-and-int)); until then
  it is a tagged `Nat`, and a value at or above 2^63 fails as `Nat` does.

**Services.**
- Allocation uses size-class free lists refilled by bump pointer from a heap
  region the caller supplies.
- Inline fast paths for allocation, `inc`, `dec` and the uniqueness test are
  planned. Today each RC operation calls a runtime procedure, and there is no
  uniqueness test because there is no reuse yet.
- Freeing is iterative.
- `Nat` overflow is an explicit failure until certified limb bignums land
  ([bignum design](bignum-design.md)).

The runtime is ordinary Lir code under the same proofs. It links no C runtime
and does not depend on GMP.

The implemented bounded route uses
[`Rt.Rc.Procs`](../IxCC/Rt/Rc/Procs.lean),
[`Cfg.Rc.Native`](../IxCC/Cfg/Rc/Native.lean) and
[`Cfg.Rc.Public`](../IxCC/Cfg/Rc/Public.lean). It admits table-bound,
fully scanned shared constructors with at most 31 fields and the existing tag
bound; fieldless constructors use immediates. Unsupported layouts, contracts
and malformed ownership/control maps are explicit declines. Allocation and
iterative release preserve the size-class free lists and bounded arena.
General scalar-field layouts, reset/reuse optimizations and stronger written
ownership contracts are outside this first route.

A successful physical source completion carries one owned output token.
`Returned.release_public` in
[`PublicRelease`](../IxCC/Recheck/Rc/Proof/PublicRelease.lean) executes
the actual exported `cx_drop` on that exact represented word and restores full
allocator readiness. The caller observes the complete result before dropping
it; the `.word` export representation passes the original word unchanged,
including immediates. Ownership comes from the return invariant, never from
successful readback or a header inspection. With no external owners, the
ordered-heap invariant proves complete reclamation.

[`recycled_entry`](../IxCC/Recheck/Rc/Proof/Reentry.lean) starts another
numeric root from that reached heap without resetting the bump pointer or
free lists. The emitted drop export also has its existing backend ABI
simulation under `EntryBase`. These are operation-composition results, not an
unconditional theorem that every successful arbitrary `DriverSession` trace
owns each returned word: source-stuck behavior retains `GoesWrong`, and general
session iteration also needs the whole-call budget-word frame. The required
native regression separately exercises 168 calls/drops on three objects with
one initialization per bounded arena, independent complete-value decoders
and exact reclaimed-address checks.

## Backend

**Lir operands.** Each operand's constraints (use or definition, early or
late, any/register/stack/fixed/reuse) are derived from the operation's
semantics.

**Selection** is rule-based, with one lemma per rule against the typed x86
semantics. It covers:
- addressing modes and `lea`;
- fused compare-and-branch with inversion;
- short immediates;
- tagged `Nat` arithmetic with an overflow branch;
- `test` for tags;
- `setcc`/`cmov`.

Flags never live across instructions except in fused pairs.

**Register allocation.**
- An untrusted linear scan with splitting proposes per-operand locations,
  move edits and block-entry states.
- A proved validator checks them: location contents, parallel moves,
  clobbers, fixed and reuse constraints, the allocatable set, and the
  calling convention.
- Spilling every value is the fallback.

**Frames and ABI.**
- The internal calling convention is private; exported entries use SysV.
- Callee-saved registers come from the allocation, and leaf functions are
  frameless.
- The frame layout is checked, and prologues check the stack limit.
- Calls use native `call`/`ret`; tail calls become jumps.

**Layout.**
- A checked block permutation, fall-through, branch inversion and tunnelling.
- rel8 comes from untrusted relaxation, range-checked in E2.

## x86 model and trust

**The model.** The typed x86 machine and byte evaluator share one
declarative instruction table: operands, flag effects, write policy, safety
conditions and encoding. E1 proves encoding and decoding per encoding class.
E2 validates complete streams and ELF objects.

**Trust in the table.**
- Now: a hardware-differential gate and an independent decoder gate.
- Later: agreement with the pinned Sail x86 model
  ([reference-model record](x86-reference-model.md)).

## Bootstrap and trust

Upstream Lean is the Gen-0 seed for the compiler and its checkers. Its
kernel, code generator, runtime, host compiler, Nix inputs and native
dependencies are recorded bootstrap provenance.

Four obligations stay distinct:
1. adequacy of the source evaluator against `Ix.Kernel`'s model, which remains
   to be proved here; upstream model certification supplies interfaces for it;
2. correctness of the executable compiler and checkers;
3. the remaining runtime, ISA, linker and loader assumptions, and Gen-0
   provenance, each with its own inventory;
4. statement faithfulness: roots are identified by their Ixon v4 addresses,
   with source maps and any replacements bound to the certified artifact.

## Planned extensions

Each extension has a design document with its motivation, current state,
options, proof obligation, trust effect, dependencies, size estimate and
exit criterion. The [roadmap](roadmap.md#plan) orders them.

| Extension | Status | Design |
| --- | --- | --- |
| Higher-order code: P8 defunctionalisation, P9 | Planned (Phase 2) | [Closures](closures-design.md) |
| Heap completion: scalar fields, large and static objects, reuse, ownership checker | In progress (Phase 2) | [Data, roots and effects](data-and-roots-design.md#d1-heap-completion) |
| Fixed-width integers, `Int`, arrays, byte arrays, strings, library structures | Planned (Phase 3) | [Data, roots and effects](data-and-roots-design.md) |
| Structured roots, the byte ABI, the claim's ABI descriptor, state-machine effects | Planned (Phase 3) | [Data, roots and effects](data-and-roots-design.md#r1-structured-roots-and-the-byte-abi) |
| Bignums: a limb library compiled by IxCC | Planned (Phase 4) | [Bignums](bignum-design.md) |
| Front-end theorem, shape typing, stage L, stage K | Planned and research (track C) | [Certification depth](certification-design.md) |
| Scale and usability | Planned (Phase 5) | [below](#scale-and-usability) |

## Scale and usability

**Status: planned** (Phase 5). The budgets are implemented; the rest is
planned.

**Motivation.** The flagship targets are far larger than any program the
compiler has seen. The certified kernel's executable closure is about 1,270
definitions for the checker and about 1,870 with admission and the Ixon
reader, before the parts of `Init` and `Std` it uses (grep counts, upper
bounds, 2026-11-09 IXCC-ROUTE review). The largest committed programs fit
the budgets with headroom between 16× and 326× ([Middle-end
budgets](#middle-end-budgets)), but they are small.

**Current state.**
- *Implemented.* The middle-end budgets above are fixed constants,
  independent of the input's size. A step may hold at most 64
  specialisation decisions with masks of at most 64 parameters
  ([`Recheck/Run.lean:173`](../IxCC/Recheck/Run.lean)).
- The front end before the middle end has no node budget (see the budget
  section above).
- Reported superlinear steps (2026-11-08 review, not re-measured at this
  head): a shrink round costs up to order `n²` in a global's size (census
  reads, above); one walk round was about quadratic (16,000 bindings in
  25.6 s); `encodeK`, which kernel evaluation of the recheck runs (native
  code runs `encode` through `encodeK_csimp`), is quadratic in the program's
  text; `selectRcPolicy` was cubic in let-alias chains; frame `Nodup`
  checks are quadratic. Erased type checking (`V3.Tc.checkEnv`) took about
  30 s on a 1 MB closure, against milliseconds for `Recheck.run`, so the
  roadmap's 10 s target is missed with type checking on.
- The producer `ixcc compile` ran past 180 s on a 917-byte input with heavy
  sharing, where `check-cert` is bounded (2026-11-09 review, open question 3).
- Declines carry a `stage: code` and a message (for example
  `fir.closures`); `lake exe census` reports the first failing stage per
  declaration ([corpus](corpus.md)). Messages name constants by Ixon
  identity, not by Lean source position.

**Design.**
1. **Budgets proportional to input.** Replace fixed caps by limits that
   scale with the closure's size (a constant factor of the input's nodes),
   keeping the fixed caps as an upper bound for hostile inputs, so a large
   honest program is not refused while a hostile certificate still cannot
   amplify its input.
2. **Linear-time passes on the recheck path.** Incremental census counts in
   shrink, linear walks, an indexed encoder for kernel evaluation, linear
   RC-policy selection, set-based `Nodup` checks. Each is a refactor of a
   proved pass, with the existing theorem restated.
3. **Per-function recheck and caching.** Check certificates per global or
   per strongly connected component, and cache accepted results by content
   address, so recompiling after a change rechecks only what changed.
   Cached entries are oracle outputs that the consuming checker re-validates.
4. **Faster ingress.** Run the erased type checker once per closure root
   and reuse its result across compilations of the same closure; separately,
   adopt the certified kernel for admission when its interfaces allow (the
   coordination item in the [roadmap](roadmap.md#coordination)).
5. **Diagnostics.** Every decline names the Lean constant (through the named
   environment ix can produce beside the anonymous one), the stage, the
   construct, and what would lift it (for example "a closure captured 40
   variables; the plain-RC route allows 31").
6. **Library coverage.** A *library census*: run `census` over the
   public declarations of `Init` and `Std` that a general user reaches
   (`Nat`, `Int`, `UIntN`, `Fin`, `Char`, `List`, `Array`, `ByteArray`,
   `String`, `Option`, `Except`, `StateT`, `ReaderT`, `ExceptT`, `ForIn`,
   `Std.HashMap`, `Std.TreeMap`, `toString`/`repr`) and track, per
   declaration, the first stage that declines it. Floats, `Task`, `IO` and
   `partial` definitions stay outside (`partial_fixpoint` compiles through
   its equation).

**Proof obligation.** Items 1, 2 and 5 restate existing checkers' theorems
for new implementations. Item 3 needs a composition theorem: a program whose
globals were checked separately, under the same table and annotation, has
the whole-program guarantees. Item 4 changes nothing proved.

**Trusted base.** No change; a cache adds nothing because every hit is
rechecked.

**Dependencies.** None for items 1, 2, 5 and 6; item 3 needs per-function
certificates.

**Size [estimate].** Items 1, 2 and 5: 3–6k lines; item 3: 5–10k lines;
item 6: a tool of about 0.5k lines over the existing census.

**Exit.** K6 (`liasolver`, `parser`, and a subset of the certified kernel)
compiles and certifies; a closure of at least 2,000 definitions compiles and
rechecks with no budget refusal, within a compile-time target set after the
first measurement; the library census is published with its decline counts.
