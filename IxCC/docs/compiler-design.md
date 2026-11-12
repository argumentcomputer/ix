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
and their contracts are on branch `jcb/ixby-archive` of the pre-merge
`argumentcomputer/Compilatr.ix` repository.

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
  and `Quot.sound`, each with an exact fence; theorems that mention ingress or
  the producer (`verifyBytes_*_sound`, `Compiler.compile_sound`, …) also show
  the existing native Blake3 evaluation axiom, recorded in the trust ledger
  ([compile boundary](compile-boundary.md)). Runtime services, the ISA model
  and build inputs are recorded in the trust ledger.

## Design decisions

Code comments cite these decisions by number. Each entry describes the code
as it is; the numbers are kept because comments throughout the tree use
them.

- **D-1. Traced statement shape.** Per-level and pipeline theorems are
  stated in the traced shape of `IxCC.Sem`, and proofs reason through each
  evaluator's bind-form unfolding lemmas, so that adding events changes the
  unfolding lemmas, not the per-construct proofs (the paragraphs "Statement
  shape" and "Evaluator interface" under [Correctness
  statement](#correctness-statement)).
- **D3. Relevance is a checked annotation.** Relevance is never written into
  Ixon bytes. An untrusted annotator (the certified kernel's, over the accepted
  environment: `Src.KernelFront.Kernel.annotateChecked`) proposes a
  class for every binder, argument, let, constructor field and constant; the
  annotation travels in the certificate beside the bytes, and the recheck
  path decides it with `Relevance.check` (proved in
  `Relevance.Proof.check_sound`) and `Relevance.checkCanonical`
  ([Relevance and erasure](#relevance-and-erasure)).
- **D10. Own runtime.** Allocation, reference counting, the `Nat`
  procedures and the entry wrappers are Lir code, lowered and proved with
  the program. There is no C or Lean runtime and no GMP in the trusted base;
  the driver supplies one heap region, and the context register points into
  it ([Runtime](#runtime)).
- **D12. Constants without usable kernel semantics.** `partial` and
  `unsafe` constants are rejected (`Src.Admit` codes `partial` and
  `unsafe`). A definition marked `implemented_by` or `@[extern]` that has a
  body compiles that body (or a pinned primitive). An `@[extern]` opaque is
  rejected (`opaque`) unless the unfolding table lists it in `opaqueByValue`,
  the allowlist of opaques evaluated through their stored value, such as
  `Lean.opaqueId`. Recorded interpretations of other opaques are planned
  ([library structures](data-and-roots-design.md#dr5-library-structures-and-opaque-constants)).
- **D16. Contracts are lower bounds.** Written usage, ownership, locality
  and borrow contracts are honoured exactly. Untrusted analyses may propose
  stronger guarantees, which only a proved checker can accept, and nothing
  inferred changes Ixon bytes or addresses ([Principles](#principles)).
  Src and Lam carry contracts without reading them in their semantics.
- **D17. Produce and recheck.** The untrusted producer (`Recheck.produce`
  and the producers it calls) makes every heuristic choice natively and
  records it in a certificate (`Recheck.Cert`); `Recheck.run` re-runs the
  proved passes on the recorded choices and checks proposals with proved
  validators, and never searches. A pass on the recheck path has one of two
  *styles*:
  - *style P*: proved once, for every value of its certificate data, and
    re-run;
  - *style V*: a proved validator checks the producer's output, and a
    rejection is an error unless a checked fallback exists.

  Lemmas used only inside the soundness proofs are *never evaluated*.
  Everything `Recheck.run` calls is written so that Lean's kernel can
  evaluate it (the `KernelEval` test modules run it with `decide +kernel`):
  structural recursion or explicit fuel rather than well-founded recursion,
  persistent `Nat`-keyed maps and sets (`Src.NatMap`, `Src.NatSet`) rather
  than hash maps, and lists rather than array indexing. Where a faster
  native twin exists, a `@[csimp]` theorem proves it equal and the trust
  ledger lists it (for example `encodeK_csimp`). The producer has none of
  these constraints.
- **D18. Level-exact relevance.** Each relevance position's `proof` class
  holds under a condition on the constant's universe levels (the zero
  condition of its type's sort). SrcEval decides it at the concrete levels it
  carries; `Relevance.check`, `Src.Admit` and erasure decide it per universe
  *profile* (which levels are zero), and erasure emits one global per
  constant and profile (`GKey.const c prof`). Sort-polymorphic code at
  `Sort 0` therefore passes □ exactly where its position is a proof. A
  constant reached at more than one profile is declined
  (`Relevance.profileSplit`).
- **D19. Keys.** Source identity is the dense `Src.CId` that ingress
  assigns to each constant. Every global carries a structural `Key.GKey`
  (`const`, `byName`, `recStar`, `wrapper`, P4's `spec`, `worker`, reserved for the
  planned P5, P8's `lam` and `dispatch`, and the closures step's `entry`, a
  root's entry at its declared parameter count), and every `con`,
  `case` alternative and `proj` in Lam and Anf a checked `Key.CtorKey`, so a
  run that confuses constructors is stuck in the source and key-based
  rewrites need no typing theorem. Keys compare structurally; no pass treats
  two things as equal because their addresses are. Erasure maps
  `Decidable.isFalse`/`isTrue` to `Bool.false`/`true`.
- **D20. No indirect calls** (decided 2026-11-10). Every call and jump the
  compiler emits is direct: the instruction table has no indirect branch
  row, the Ring-0 admission argument relies on that, closures are compiled
  by defunctionalisation with compare-tree dispatch ([closures
  design](closures-design.md)), and the IxOS monitor reaches SIP entries
  through a ledgered tender ([roadmap](roadmap.md#decisions-of-2026-11-10)).

## Identifier schemes

Short identifiers used in code comments and these documents, and where each
is defined.

| Identifiers | Meaning | Defined in |
| --- | --- | --- |
| D-1, D3 … D20 | Design decisions | [Design decisions](#design-decisions) |
| style P, style V | How a pass is checked on the recheck path | D17 above |
| P0 … P9 | Lam and Anf passes | [Pass identifiers](#pass-identifiers) |
| stage S, stage K, stage L | Statements relative to SrcEval (what is proved today); against the certified kernel's models; per program, about the Lean function | [Correctness statement](#correctness-statement), [certification design](certification-design.md) |
| E1–E9, A1–A3, F1–F8 | SrcEval's rules | the module header of [`Src/Semantics.lean`](../IxCC/Src/Semantics.lean) |
| tier S (S1–S4), tier C (C0–C6) | The relevance checker's soundness facts and consistency rules | the module header of [`Src/Relevance/Check.lean`](../IxCC/Src/Relevance/Check.lean) |
| E1, E2 | The x86 encoding layers: per-form encoder and decoder; complete streams and ELF objects | [x86 instructions](x86-encoded-instructions.md), [x86 streams and objects](x86-stream-objects.md) |
| K0 … K6 | Benchmark rungs | [roadmap](roadmap.md#benchmark-rungs) |
| Phase 0 … 5 | Delivery phases | [roadmap](roadmap.md#phases) |
| IxOS-0 … IxOS-4, IxCK-1 … IxCK-3 | Steps of the two flagship targets | [roadmap](roadmap.md#flagship-targets) |
| DR1 … DR9 | Items of the data, roots and effects design | [data, roots and effects](data-and-roots-design.md) |
| CD1 … CD4 | Items of the 2026-11-09 certification plan, now redistributed | [certification design](certification-design.md) |
| SP-0 … SP-2, SP-A, SP-N | The spine's milestones | [certification design](certification-design.md#the-spines-work), [roadmap](roadmap.md#milestones) |
| EV-0 … EV-2 | The evaluator interface's milestones | [evaluator interface](evaluator-interface.md) |
| AR-1, AR-2; XB-1, XB-2; HD-0 … HD-3; RL-1 … RL-4 | Milestones of the Aiur routes, the x86 back half, hardening, and repository and landing | [roadmap](roadmap.md#milestones) |
| DC-1 … DC-3, DO-1 … DO-22 | Decisions to confirm and open decisions | [roadmap](roadmap.md#decisions) |
| Stage A | The byte-level verifiers' requirement that the certificate's relevance annotation equal the kernel annotator's output (`inp.kernel.annotateChecked`) on the certificate's table (`Recheck.checkCanonicalRelevance`) | this table |
| S0, S1, S2 (x86) | Steps of the Sail reference-model route | [x86 reference model](x86-reference-model.md) |
| S1–S12, N1–N14, `B*-*`, `R*-*` | Findings of the 2026-11 reviews | Each document that cites one says what the finding is |
| RE-0 … RE-3; DC-4, DO-23 … DO-27 | Resource-soundness milestones; decision-register entries added on 2026-11-14 | [resource soundness](resource-soundness-design.md), [roadmap](roadmap.md#decisions) |
| X0 … X6, X0-P; DO-28 … DO-36 | Standalone-executable milestones; decision-register entries on executables | [standalone executables](standalone-executables-design.md), [roadmap](roadmap.md#decisions) |

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

Code comments call the first stage *stage S* and the second *stage K*. A
third route, *stage L*, states per program that the compiled code computes
the Lean function itself; the plan leads with stage K and keeps stage L as a
side product (to confirm; [certification design](certification-design.md)).

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
keeps it. At a root that `checkImmortalRoot` accepts, the view accepts every
result of the shape the root's declared type describes (a `Nat`, a pinned
`Bool` constructor, or a constructor of the result enumeration:
`Recheck.ResultShape`), so the third case means a result off that shape
(`Recheck.Artifact.goesWrong_immortalRoot`). Erasure registers a
constructor-table row for every constructor a root's result can hold, so
this holds for a root compiled alone too. The converse fails for the view,
which relabels by table tag a constructor of another type; the shape view
(`Recheck.Front.shapeView`) accepts only results of the shape, and the same
three clauses hold with it, its third case being exactly a result off the
shape (`Recheck.ShapeClaim`). At a root that `checkPlainRcRoot` accepts, the
plain-RC view accepts every constructor tree of the root's declared
first-order type (`Recheck.PlainShape`), so there too the third case
means a result off that shape
(`Recheck.RcReplay.Artifact.goesWrong_plainRoot`). That SrcEval returns a
result of that shape is not proved: that is type preservation for SrcEval.

Only the root's result is observed, read back at its first-order type;
Phase 1 programs are scalar and pure. The theorem uses only the three
standard axioms. Reading it as a fact about the native executable rests
on three specification assumptions in the
[trust ledger](trusted-extern-ledger.md):
- `X86.Driver`/`X86.Linked` model how a caller loads the object and calls
  its exports: the standalone executable's shell, and the test executables the
  native suites run (`x86-phase1-runtime-driver-model`);
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
events from final heap totals. Native controls compare two decoders of the
native memory (an independent decoder and `Rt.readback`), reject independently
corrupted emitted objects before they run,
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
The ownership suite's annotated fixtures are the programs the `ix` of this
repository accepts (`fixtures/ownership/verdicts.json` records the others):
none is recursive. `ix compile` takes no resource profile and writes no
checked equation pair, and it refuses the annotated recursive `len` of OS-04 at
its resource admission ("external resource interface is absent from the bound
profile"), so the suite has no annotated recursive program.

The required Lam suite also checks sixteen synthetic evaluation-order cases
through table and relevance rechecking, lazification and erasure. Their
placeholder types justify no irrelevant tag, so they run through the recheck
path without `Relevance.checkCanonical` (the test-only `recheckNoCanonical`),
and the suite asserts separately that the production `Src.Recheck.run`
either accepts each or refuses it only through `checkCanonical`. Checked direct cases demand
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
| **Fir** | First order: top-level functions, known calls, join points, tail calls. No closures: P8 (the closures step, the middle end's last) defunctionalises them in Anf, so Anf → Fir never declines a program for them; there are no closure objects, `pap` or `apply` ([closures design](closures-design.md)) | Clocked big-step | Forward simulation |
| **Own** | Explicit ownership. Implemented: the immortal fragment and `Own.Plain`'s `inc`/`dec` actions. Planned: borrowed parameters, reset/reuse credits, unique and local kinds | Clocked big-step over an abstract RC heap | Proved ownership checker ⇒ refinement of Fir |
| **Cfg** | Blocks with parameters over the same operations | Clocked small-step | The single big-step → small-step bridge |
| **Lir** | Words, memory, compare-branch, calls, runtime procedures | Clocked small-step | Heap → memory data refinement |
| **Xv / Xl** | x86-shaped operations on virtual registers, then on registers and slots | Small-step | One lemma per selection rule; allocation validator |
| **x86** | Typed x86: frames, ABI, layout | `X86.Eval` | Frame layout, layout, and generic `SafeSteps` into E1/E2 |

### Pass identifiers

Code comments and certificates name the Lam and Anf passes P0 to P9. This table
is their definition.

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
| P8 | Closed-world defunctionalisation | [`Anf.Defun`](../IxCC/Anf/Defun.lean), run by the closures step [`Anf.Pipeline.closures`](../IxCC/Anf/Pipeline/Closures.lean) after the certificate's steps, with each root entered at its declared parameter count ([`Anf.Entry`](../IxCC/Anf/Entry.lean)) | Phase 2: on the compile and recheck path, proved (`Anf.Defun.correct`, `Anf.Pipeline.Proof.closures_correct`) and composed into the end-to-end theorems on the inputs they cover ([design](closures-design.md#proof-obligation)) |
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
`ixcc check-cert` abort with a stack overflow.
The checker therefore refuses an input or a step, with an ordinary error, as
soon as it passes one of these fixed budgets
([`Src/Syntax.lean`](../IxCC/Src/Syntax.lean),
[`Recheck/Run.lean`](../IxCC/Recheck/Run.lean),
[`Anf/Budget.lean`](../IxCC/Anf/Budget.lean),
[`Anf/Walk.lean`](../IxCC/Anf/Walk.lean),
[`Anf/Specialize.lean`](../IxCC/Anf/Specialize.lean)):

| Budget | Bounds | Value | Largest committed value | Headroom |
| --- | --- | --- | --- | --- |
| `Src.maxTermDepth` | the depth of a source term: per expression at ingress (`Ingress.depthBudget`, share expansions included and a reused share's height checked against the depth left, `Ingress.convH`), and erasure's nesting (`Lam.Erase.termFuel`) | 2,048 | 299 | 6.8× |
| `Recheck.maxSrcVisits` | with `Src.maxTermDepth`, `Recheck.checkSrc`'s check of a program built without ingress: its term nodes counted as trees (a shared term at each use) | 268,435,456 | 33,211,435 | 8.0× |
| `Anf.maxLamNodes` | each Lam global, before ANF conversion (P1) | 16,384 | 1,145 | 14× |
| `Anf.maxLamDepth` | each Lam global's depth, before P1 | 2,048 | 134 | 15× |
| `Anf.maxGlobalNodes` | each Anf global, after P1, after every step and after every shrink round | 16,384 | 9,083 | 1.8× |
| `Anf.maxDepth` | each Anf global's depth, at the same points | 2,048 | 1,543 | 1.3× |
| `Anf.maxProgramNodes` | the whole program at the same points, and the running total while an inline or shrink step rewrites its globals | 1,048,576 | 25,749 | 41× |
| `Anf.maxBackWork` | the back end's work (`Anf.backWork`: each global's nodes squared, plus its nodes and its `case`s' squared alternative counts times the constructor table's length), at the same points | 268,435,456 | 158,498,608 | 1.7× |
| `Walk.maxCopy` | the nodes one walk walks again: inlined callees, inlined join points, case-of-case alternatives (but the first selection of each alternative of a pending join point, a move) and a local function's second and later β-expansions (its first is a move, `Walk.betaFires`) | 8,192 | 6,955 (inline), 1,375 (shrink) | 1.2×, 6.0× |
| `Walk.maxWalkDepth` | the walk steps on the native stack at once (`Here.lvl`, which a continuation inherits from the point that calls it) | 3,072 | 1,571 | 1.9× |
| `Walk.maxFires` | rule firings in one walk | 8,192 | 801 | 10× |
| `Walk.maxWalkWork` | the work one walk does (`Fires.work`, charged before every step of the walk) | 10,000,000 | 3,706,721 | 2.6× |
| `Anf.maxStepWork` | the walk work of one inline or shrink step, over all its walks | 45,000,000 | 28,843,161 | 1.5× |
| `Specialize.maxWork` | the work charged for the call sites a specialisation step examines | 67,108,864 | 3,179,143 | 21× |
| `Specialize.maxNodes` | the nodes of the specialisations those sites may build | 1,048,576 | 3,209 | 326× |

The committed values are `tests-corpus`'s survey of every committed program
(172 measured, 2026-11-11), which also checks every walk against the visit
bound of the copy count (`steps ≤ nodes + copied`: 5,409 walks).

**Headroom.** Six budgets are within twice the largest committed value. The
survey prints, beside each maximum, the first program that reaches it:

| Budget | Value | Largest committed value | Headroom | Reached by |
| --- | --- | --- | --- | --- |
| `Walk.maxCopy`, in an inline walk | 8,192 | 6,955 | 1.18× | `phase1-machines`, `Machines.fibMain` |
| `Anf.maxDepth` | 2,048 | 1,543 | 1.33× | `phase1-machines`, `Natural.fibMain` |
| `Anf.maxStepWork` | 45,000,000 | 28,843,161 | 1.56× | `phase1-machines`, `Natural.fibMain` |
| `Anf.maxBackWork` | 268,435,456 | 158,498,608 | 1.69× | `phase1-machines`, `Machines.fibMainHO` |
| `Anf.maxGlobalNodes` | 16,384 | 9,083 | 1.80× | `phase1-machines`, `Machines.fibMain` |
| `Walk.maxWalkDepth` | 3,072 | 1,571 | 1.96× | `phase1-machines`, `Natural.fibMain` |

All six are reached by the numeric state-machine family, the largest
committed programs, so a program somewhat larger meets them first: a walk
past `maxCopy` is refused (the producer then retries the inline round without
that caller, see "The producer" below), a shrink round that would take a
global past `maxDepth`, a walk past `maxWalkDepth` or a step past
`maxStepWork` is not taken (the global keeps the rounds before it, less
shrunk), an inline round past any of them is not taken, and a program past
the node or back-end work budget after a shrink step, or deeper than
`maxDepth` after P1, is refused. The three that
`Natural.fibMain` reaches come with the middle end's inline-round retry and
its pending join entry, which make that program first order: with neither,
on the same tree, its deepest global is 596 deep, its deepest walk 754 steps
and its largest step's walk work 7,063,134; with the pending entry forced
off (the retry kept) 1,187, 1,220 and 15,358,362 (the retry inlines more, and the pending entry moves each
selected alternative into the `case` arm that jumped to it).

That visit bound (a walk takes at most its global's nodes plus `maxCopy`
steps) is argued in `Anf/Walk.lean`'s module note and checked by the step
counter `Fires.steps` on every walk of every committed program and on the
hostile shapes of `tests-recheck`; it is not a Lean statement and is not
proved. It says how much a walk may visit and emit relative to its input; it
is not what bounds the verifier. What bounds the verifier's work and stack,
whatever the certificate asks, are the budgets the walk enforces: its work
(`maxWalkWork`, charged before every step), its depth on the native stack
(`maxWalkDepth`), its firings (`maxFires`) and its copies (`maxCopy`, refused
before the body is walked), the step's work (`maxStepWork`), and the size
budgets after every round. The
`phase1-machines` family, registered after the previous survey (169
programs), raised most of them; the walk's move accounting then lowered the
largest copy in a shrink round from 7,712 to 1,375.

The certificate's shape is bounded as well (`Recheck.checkMidCert`, `Recheck.CertJson`,
`Src.Hints.checkJsonText`): at most 64 middle-end steps, 64 shrink rounds per
global, 64 callees per inlining caller, 64 specialisation decisions with masks of at
most 64 parameters, case-of-case and small-join thresholds of at most 512 and
64, and JSON nested at most 512 deep. A specialisation site counts its value
trees only up to `Specialize.maxTreeWork` (8,192) before charging them.

The counts stop early and walk explicit worklists (`Exp.nodesUpTo`,
`Exp.depthUpTo`, `lamNodesUpTo`, `lamDepthUpTo`, `Recheck.srcWithin`; a walk's
charges stop at the budget left), so checking a budget costs no more than the
budget and is safe on any depth. The largest values are measured by
`tests-corpus`, which replays the honest certificate of every committed program
step by step (every root of every corpus family, and `k1.ixe`, `src-sortpoly`,
`src-diag`, the ownership fixtures and the RC real-source closure with all their
roots: 172 programs reach the middle end, 20 more are declined before it) and
fails if any value reaches its budget.

**Native stack.** A Lean program runs `main` on a thread whose stack is
`LEAN_STACK_SIZE_KB` (`ulimit -s` does not change it). The `ixcc` executable's
default is far above 8 MiB; the depth budgets are set at least four times below
the depth at which each recursive traversal on the verifier path overflows an
8 MiB stack (`LEAN_STACK_SIZE_KB=8192`, `tests-recheck --probe*`), measured per
nesting constructor:

| Traversal | Nesting shape | Overflows at 8 MiB | Budget |
| --- | --- | --- | --- |
| ingress (`conv`) | any | never (its own fuel) | `maxTermDepth` 2,048 |
| front end (installation, the relevance checks, `checkCanonical`, `Lazify`) | constructor, application, `let`, type chains | above 32,768 | 2,048 (16×) |
| erasure | constructor chain / applications / `let` / types | 8,960 / 14,080 / above 32,768 / above 32,768 | 2,048 (4.4×) |
| `Lam.modesOk` (in erasure) | application (argument) / `case` / scrutinee / constructor / λ | 35,202 / 44,142 / 75,625 / 105,163 / 131,593 | `maxLamDepth` 2,048 |
| P1 (`Anf.convert`) | application (argument) / `case` and scrutinee / constructor / application (function) / projection / `tick` / `let` value / `let` body / λ | 9,451 / 13,825 / 17,712 / 44,142 / 48,028 / 66,296 / 75,625 / 88,062 / 131,593 | 2,048 (4.6×) |
| a walk (steps on the stack) | single-alternative `case` / `tick (case …)` / two-alternative `case` / join point / binding / `tick` | about 12,290 (FV), and per MiB: 1,771 / 2,848 / 1,817 / 2,212 / 2,607 / above 3,072 | `maxWalkDepth` 3,072 (4×); globals start at most `maxDepth` 2,048 deep |
| Fir to x86 | single-alternative `case` / two-alternative `case` / `tick (case …)` / join points / bindings / `tick` | above 16,383 / 8,192 / 8,192 / 8,192 / 8,191 / 16,383 (all that was tried) | `maxDepth` 2,048 (4×) |

The walk is the tightest: four times below its threshold leaves `maxDepth`
1.3 times the deepest committed Anf global and `maxWalkDepth` 1.9 times the
deepest committed walk, the room an 8 MiB stack allows. Ingress converts a share once
and reuses the term; it keeps the term's height and checks it against the
depth left wherever the share is reused, so no ingested term is deeper than
`maxTermDepth`. The program-level verifiers (`Recheck.run`,
`CompileClaim.verifyProgram`, `checkClaimProgram`, `Ring0Sip.verifyProgram`)
assume their `Src.Program` came from ingress, and say so; a host that builds
one some other way runs `Recheck.checkSrc` first (it is not on the recheck
path, where the kernel-evaluated tests would pay about 0.2 ms per tree node). `tests-recheck` runs
every verifier entry point in a child process with `LEAN_STACK_SIZE_KB=8192` on the inline
amplifiers, on generated deep and wide inputs at and past each budget, on a
term whose shares are reused deeper than their first use, and on chains of every nesting
constructor at Lam and Anf (at the depth budget and one level past it, through
the middle end's replay, a shrink step and the back end), and on a walk whose
copy brings it to its depth budget and one step past it.

*Width.* The depth budgets bound recursion on term structure; recursion along a
list whose length the input or the certificate controls is bounded another
way. Stage A compares the certificate's annotation with the re-derived one by
`Src.Relevance.Ann.eqb`, a loop over the term list and each tag list (the
derived list equality it replaced took a stack frame per element, so a
560-byte closure whose honest certificate holds a 262,142-entry tag list
aborted `ixcc check-cert` on an 8 MiB stack). The other list-shaped parts of
the input and the certificate were run at the widest the budgets admit, from
bytes, through `verifyBytes`, `checkClaim`, `Ring0Sip.verifyBytes` (typed and
untyped) and `check-cert`, on a 2 MiB stack, a quarter of the target: the
annotation's tag list (524,286 entries, the most the annotator's node budget
admits), 16,371 constants and globals with their table and annotation
entries, a certificate with a 2,500,000-entry JSON array (25 MB), sidecars
with 300,000 roots and 1,000,000 equation entries; and from Anf, through the
back end, 16,000 globals, functions of 16,384 blocks, 125-way switches and
200 values live at once. All ran within 2 MiB, so any recursion along those
lists has at least four times the headroom an 8 MiB stack needs. Constructor
fields (at most 254), switch arms (125), certificate steps and decisions (64),
and parameters, arguments and join parameters (bounded by the depth budget,
2,048) are short. `tests-recheck` keeps a representative of each in its 8 MiB
child. Frame slots (4,096), the certificate's order lists and Ixon's
reference, sharing and universe tables (4,096 each) were later run at their
limits and one past them and behave the same.

*Certificate caps.* Every list the certificate carries is bounded by
quantities of the program it is checked against, and the bound is checked
before the first reader of the list walks it, by a loop (linear in the list,
in constant stack). A padded certificate is refused for the cost of reading
it once, and the work a certificate within the caps can ask for is the
program's, times the constants below. Ratios are per function; the committed
values are measured by `tests-corpus`, which fails if any reaches its cap.

| Certificate part | Cap | Largest committed value | Checked in |
| --- | --- | --- | --- |
| table columns (`resolve`, `recKind`, `lazy`, `inline`, `opaqueByValue`) | constants of the program, each named at most once per column | exact | `Table.ofCert` (`TableCert.keysOk`), the first reader on every verifier path |
| annotation records (`consts`, `ctors`) | constants of the program | exact | `Recheck.checkRelevanceKeys`, after `Table.ofCert` |
| annotation node tags | each runtime term (a value, an `eqn` body, a recursor rule) named at most once, of a constant of the program; its tags cover the term exactly | exact | `checkRelevanceKeys`; installation |
| middle-end steps | 64 steps; shrink: at most one round count per global of the program at that step, each at most 64; inline: at most one caller per global, 64 callees each; specialisation: 64 decisions with masks of at most 64 | exact | `checkMidCert` and the decoder; `Anf.Pipeline.Step.run` |
| allocation shape | one output per function; per block one location list per instruction and per terminator, one location per operand | exact | `Xv.Validate.sizeOk`, the first statement of `Validate.func` |
| allocation edits at one position | 160, plus two per operand of the instruction there and of the one before (a reload per use, a store per definition) | 10 in all | `sizeOk` (16×) |
| allocation edits | 10 per register mention or block | 0.58 | `sizeOk` (17×) |
| allocation facts, per block | a location plus one per register: 8 entries per register mention of the function; locations distinct and registers strictly increasing (both allocators merge a location's entries, which leaves the state the same) | 1.33 per mention | `sizeOk` (6×; a structural bound: an honest block names each register live into it in a few locations, the all-slots fallback at most twice its live registers) |
| frame slots | the function's register mentions plus 16, and 4,096 | the mentions plus 0 | `sizeOk`; the decoder (`maxAllocSlots`) |
| frame layouts | one per function; cells 8-aligned, inside a frame of at most 2^20 bytes, in strictly increasing order (a single pass; it implies they are distinct) | exact | `Stacking.run`, `FrameLayout.check` |
| block order | one group per layout group; each block at most once, in its group | exact | `Order.check`, one pass over the list |
| plain-RC ownership code | decoded against the source's control tree, at most 4,096 deep, and equal to the canonical code | exact | `Own.Plain.Certificate.admit` |
| the whole certificate | 64 MiB of JSON nested at most 512 deep | | `checkJsonText` |

Native `ixcc check-cert` on the allocation's two former outliers, in `tree 9`'s
first function, at 2 MiB, 8 MiB and the default stack alike: 100,000
self-moves at one position (they took a stack frame each and aborted an 8 MiB
stack) are refused by the cap in 0.2 s, 164 MB; a fact of 100,000 registers
(23.6 s at 8 MiB before, and an abort at 2 MiB) is refused by the fact cap in
0.13 s, 117 MB. At the caps: a fact of 98,224 registers is refused by the
edge check in 0.15 s, 115 MB, and 164 self-moves at one position are accepted
in 0.19 s, 97 MB. The validator's register sets are built and compared in linear time
on the strictly increasing lists `sizeOk` requires (`VSet.ofListTR`,
`subsetTR`, `insertTR`, proved equal to the definitions the proofs use), and
`Alloc.takeAt` is a loop (`takeAtTR`).

What remains: the validator's work is still the product of a block's
instructions and its abstract state (each definition forgets its register in
every location, `AState.forget`, and each edge rebinds the target's
parameters over the state). A state that its incoming edges justify holds at
most one set per location (16 registers, at most 4,096 slots, the outgoing
cells); only a block checked before all its predecessors starts from
unjustified facts, which the fact cap bounds by 8 entries per register
mention of its function. P1 (`Anf.convert`) at the Lam node budget needs more
than 2 MiB of stack, so `tests-recheck` runs the program-shaped inputs in its
8 MiB child and the certificate- and sidecar-sized ones (the widths above,
the allocation caps, and the table, annotation, inline and shrink caps at and
one past each) in both an 8 MiB and a 2 MiB child.

**Work.** Under shrink, the census counts read at each binding walk the rest of
its body, so a round reads up to the global's depth times its nodes. The walk
therefore charges every step before taking it (`Walk.stepCost`: one, plus the
environment entries its atoms resolve and the join point it looks up, and
under shrink the nodes of the expression it stands on, the body of a jump's
target and the levels the known-primitive search reads), refuses past
`maxWalkWork`, and the inline and shrink steps refuse once their walks' work
passes `maxStepWork`. A certificate holds at most 64 steps. The back end (Fir to
x86) is linear in a function's nodes but for `Cfg.lower`'s block counts,
`Lir.Func.splitCriticalEdges`' predecessor counts and `X86.Layout.tunnel`'s
chains (quadratic in a function's blocks or depth) and the constructor table's
searches (`Rt.checkSwitches` per pair of a switch's alternatives): `backWork`
bounds them all. Measured on the box with each back-end level of the verifier timed
(`tests-recheck --probe-back`, with the producer's allocation, frames and
order), on programs at `maxBackWork`: 64 globals of 2,047 nested
single-alternative cases take 12.4 s (`Cfg.lower` 4.3 s, `Rt.lower` 1.4 s,
`X86.Layout.tunnel` 6.6 s); sixteen globals of two-alternative cases 3.6 s;
270 smaller ones 3.4 s; one comb of eight 2,047-level chains 2.3 s; chains of
join points 1.9 s; 300 globals of 200 values live at once 0.1 s (allocation,
its validator, frame layout, the encoder and the stream checker stay linear
there; on objects of megabytes the encoder, the stream check and the ELF
writer grow about quadratically in the text, as the paragraph "The producer"
below measures);
2,000 125-way cases, fifteen times past the budget, 13.9 s, 11.8 s of it
`Rt.checkSwitches`. A 16,383-level global, now refused by `maxDepth`,
took 12.8 s. With the middle end's worst certificate (64 shrink steps each
just under `maxStepWork`, 10.7 s), `checkSrc` (it refuses about 5·10⁸ tree
nodes in 4.3 s) and the front end on a program at `maxSrcVisits` (about 6 s
and 4.3 GB per 10⁸ tree nodes before it refuses an empty certificate, so about
16 s and 12 GB at the budget), the stages add up to about 45 s for the
slowest certificate the budgets admit or refuse. That sum is an estimate from
stages measured separately, not a measurement, and it leaves out typing.
Measured from bytes as single certificates (native `ixcc check-cert`,
2026-11-10, before the switch to the kernel front end), typing at ingress
dominated: an honest root of the committed
`fixtures/corpus/phase1-scalar/scalar.ixe` (1,543 constants) was accepted in
51.8 s, 51.7 s of it the erased checker's typing (0.46 s without it). Since the
switch the certified kernel's acceptance takes about a second and a half on
the largest committed closures; its fuel bounds each call's recursion, not its
work, so no budget bounds the acceptance of a whole closure (the [kernel front
end](kernel-front-end-design.md#resource-bounds)). Of the inputs built to stress the other stages, the
slowest accepted is a closure of 8,006 constants (`tests-recheck --write-wide
DIR many 8000`) with its honest certificate padded to 64 middle-end steps and
its allocation edits at the caps, 7.8 s and 167 MB, 4.7 s of it ingress. A
closure of 16,371 constants is refused for want of back-end parts after 19.5 s
and 155 MB, 16.6 s of it typing; in process, with the producer's back end added
(`tests-recheck --probe run many 16370`), it takes 54 s, the producer
included. No certificate near the front-end, middle-end, back-end and
allocation limits at once has been built.

**The producer.** The producer (`Recheck.produce`, `RcReplay.produceWith`,
`ixcc compile`) is untrusted, so no budget is a soundness premise for it; it
keeps to the re-run's budgets so that it fails as fast as the re-run would
and never hands the re-run a certificate past them. Its middle end
(`Anf.Pipeline.produce`) runs the re-run's size, depth and back-end work
check (`checkGlobalNodes`) after P1 and after every shrink step and refuses
there with the re-run's message, before its back end runs; it takes each
inline round and specialisation through the re-run's own step
(`Pipeline.Step.run`) and does not take one the re-run refuses (an inline
round it refuses is retried once without the callers whose walk the re-run
refuses alone, `Budgets.retryInline`; if the run with that retry then fails
in the middle end, `Anf.Pipeline.produce` runs again without it, and if it
fails at any stage, `ixcc compile` and `Recheck.compileInputRetry` do, so
neither of these refuses a program that compiles without the retry; the
other producers, `Recheck.produce` and the claim producer among them, fall
back only for a failure in the middle end); a global's
shrink rounds stop where the re-run would refuse the next one
(`Shrink.fixpointWithin`: a walk past its budgets, a global past
`maxGlobalNodes` or `maxDepth`, the step past `maxStepWork`); and it keeps to
the certificate's caps on steps (`Pipeline.maxSteps`), callees per caller and
specialisation decisions. The shrink walk's pending join entry (case-of-case
as a move) is not a producer decision: the walk chooses it from the source
and its own state, the certificate does not record it, and the re-run
chooses again; a producer that deviated (a test-only switch,
`Shrink.Budgets.pendForce`, makes one) is refused wherever the re-run's walk
derives another program from its certificate, and accepted, less optimised,
where it derives the same (`tests-corpus` asserts both). Its oracles are
near-linear in the program: the
recursive-global search is Tarjan's algorithm (it was a reachability walk from
every global); the block order is near-linear in a group's blocks
(`Order.produce`: it was quadratic, and exponential in the two-way branches
of a loop body, whose loop search expanded a block once per path to it); and
the allocation driver (`Alloc.runProducer`) does not validate every function
a second time. On a closure of n small functions (`tests-recheck --perf-write
DIR fns N`) the producer takes 2.0, 9.7 and 20.1 s at 100, 500 and 1,000
functions, linear, and the checker 1.7, 17.4 and 56.6 s: `Backend.finish`
(`Stream.encodeK` and `ELF.writeCheckedK`) grows about quadratically in the
text across functions, while its allocations grow linearly. 2,001 functions
of 63 constructors each compile and are accepted (producer 18.9 s, checker
55.6 s); 2,001 of 127 are past `maxBackWork` and are refused by the producer's middle end in 2.5 s
(the producer used to run its whole back end, 45 s, before the re-run
refused them). On the committed programs the producer takes at most about 4 s,
nearly all of it the relevance annotator on `tags125` (then the erased checker's
annotator, 3.5 s, which Stage A of `check-cert` re-ran); their compile time was
otherwise the erased typing at ingress (35 to 75 s on each 1 MB closure on the shared box, and 240
to 310 s on the 3.7 MB `strings` decline fixture), which `check-cert` ran as
well; the certified kernel's acceptance that replaced it takes 0.03 to 3 s on
the same closures (measured 2026-11-11, [kernel front end](kernel-front-end-design.md#measurements)). `tests-recheck --producer` compares the
rewritten oracles with reference copies of the code they replaced and checks
that the producer's work, counted in allocations, grows near-linearly on
scaling inputs (and times the block order against the code it replaced, whose
quadratic scans allocate little); the measurements are in the
[producer's performance record](performance/producer-2026-11-10/README.md).

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
| `prim f op` | Compute `f` with a primitive. The checker pins `f` by address and type; that the primitive's meaning equals the pinned kernel body is tested, not yet proved (a lemma of the spine's SP-0, [certification design](certification-design.md#sp-0-same-bytes-and-the-conditional-statement)). |

In the model, an accepted equation theorem forces its two sides to denote the
same value, so every table entry preserves meaning. When an equation is
missing, the kernel body is compiled instead: correct, but eager.

Rejected: `partial` and `unsafe` definitions, and extern opaques that are not
admitted as ledgered runtime services. `implemented_by` compiles the
reference body.

SrcEval's clock bounds the nesting depth of its charged rules (δ, β, ι,
`case`, forcing a by-name slot, `Quot.lift`), not their number. The unit of
SrcEval's work, one charged rule application, is defined in
[Source steps](source-steps.md), with its counter and the `src-steps` tool.

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
plain-RC implementation" on ([data design, DR1](data-and-roots-design.md#dr1-heap-completion)).

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

**Source contracts are untrusted hints** (owner, 2026-11-14). The usage,
ownership and locality contracts written in Lean source are checked upstream
only by ix's resource checker, which has no soundness theorem, and the
kernel's model reads none of them. Nothing in the table above may rest on
them: the ownership checker verifies each written contract as a lower bound
on IxCC's own representation before the compiler acts on it (a unique
parameter at every call, a unique result at every return, a borrow and a
local value where they are used), as the relevance checker re-checks erasure
today, and a contract it cannot verify is refused (the default of
an open decision, DO-25 in the [roadmap](roadmap.md#open-decisions)). In
particular a source uniqueness annotation selects in-place update only through that
verification. The source-level check stays a front-end diagnostic; the
source-level resource theorem is planned separately ([resource
soundness](resource-soundness-design.md)).

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
  [DR2](data-and-roots-design.md#dr2-fixed-width-integers-and-int)); until then
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

**The callers, and no C driver.** `X86.Driver` and `X86.Linked` model how a
caller loads a compiled object and calls `cx_init` and a root, and the ledger
assumption `x86-phase1-runtime-driver-model` says the callers realise that
model. The owner decided (2026-11-14) that standalone executables are a target
with no C driver. Implemented: `ixcc compile --exe` writes the executable
itself, with the object's text byte for byte and a start-up shell written as
typed x86 in Lean that sets up the calls from a fixed static layout (below,
[Standalone executables](#standalone-executables)); the system-call
instruction appears only in the shell, never in compiled program text. The
test suites run objects the same way (X1): as executables IxCC writes with a
test shell that serves a host in Lean, which does what the C runtime driver
did until then, so no gate runs a compiled program through C. Planned: the
shell proved and the platform procedures through which programs perform
effects ([standalone executables](standalone-executables-design.md)).

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
- Calls use native `call`/`ret`; tail calls become jumps. A tail call passes
  its arguments in the seven argument registers only (it reuses the caller's
  frame, which has no outgoing stack cells), so `Fir.lower` lowers a call in
  tail position of more arguments to another function as a call and a
  return (`Fir.Lower.tailCall`): a frame per such call, so a loop through one
  uses stack in every iteration (`Closures.stateLoop`: 32 bytes per iteration
  on the immortal route, 96 under plain RC), and a long enough loop ends with
  the stack-exhaustion status, not a different value. Proper tail calls with
  stack-passed arguments, or dropping erased parameters (P5), would remove
  it ([roadmap](roadmap.md), "Internal tail calls").

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

## Standalone executables

`ixcc compile ... --exe FILE [--stack BYTES] [--region BYTES]` also writes a
static Linux x86-64 executable that runs the first root on decimal arguments
and prints its result, with no C compiler, C library, linker or C driver
([`IxCC/Exe.lean`](../IxCC/Exe.lean), [`IxCC/X86/Exe/`](../IxCC/X86/Exe); the
[standalone executables design](standalone-executables-design.md) plans the
rest).
- **The file** (`X86/Exe/Write.lean`): an `ET_EXEC` image of the ELF header,
  four program headers (the file read and execute at `0x400000`; a zero-filled
  read-write segment at `0x10000000` holding the program stack and then the
  region; the object's provenance note; no executable stack), the note, the
  object's text byte for byte, read-only data and the shell. The object must
  have no relocations. `X86.Exe.check` (`X86/Exe/Validate.lean`) reads it back
  with an independent reader (`X86/Exe/Read.lean`) and refuses it unless every
  part, gap and header is as planned and both of the shell's calls land on
  their exports.
- **The shell** (`X86/Exe/Shell.lean`, `X86/Exe/Code.lean`): platform code
  written as typed x86 and encoded by the compiler's encoder. Its instruction
  type adds the system call and calls of the object's exports to the typed
  instructions, outside the program instruction table, which keeps no
  system-call row. It confines the process with a seccomp filter, parses
  exactly the root's parameter count of decimal numerals (status 2 for a wrong
  count, 3 for a non-numeral, 67 for a numeral of `2^64` or more), calls
  `cx_init` and the root by direct calls, and prints the value or a message
  with status `64 + s` for the wrapper's status `s`. It is trusted code
  (ledger entry `x86-linux-exe-shell`).
- **The contract** (`X86/Exe/Layout.lean`): `Layout.driver_canonicalOk` proves
  that every layout the writer accepts gives the shell's calls a driver
  keeping `Driver.CanonicalOk`; that the shell's code realises that driver is
  not proved.
- **The fragment** (`Exe.fragment`): roots with at most five `Nat`
  parameters returning a `Nat` (printed `n`) or a constructor without fields
  (printed `#k`, as `Rt.renderObs` prints it), on any policy. Other roots are
  refused (`exe.params`, `exe.result`).
- **The test executables** (X1): the writer and its check take any *frame*
  (the embedded shell and data, the exports it calls, the zero-filled
  segments); the production executable is one frame. The native suites write
  each object with another, the test shell (`IxCCTests/Exe/TestShell.lean`,
  test code): confined to `read` from standard input, `write` and `exit`, it
  serves binary requests (call an export with sentinels in the callee-saved
  registers, read or write the region), and a host in Lean does what the C
  runtime driver did, decoding each result with `Rt.readback` and with an
  independent decoder. No gate runs a compiled program through C.
- **Numeric state machines** (X2, `--exe FILE --machine`): the first root is a
  step `Nat → Nat → Nat` of a state and an event whose result packs the next
  state and a request (`IxCC/Exe/Machine.lean`: the argument block's next
  byte, one byte written to standard output or error, or an exit); a generic
  shell (`X86/Exe/Machine.lean`, the same for every machine) calls `cx_init`
  and the step once per request, performs the request and passes its answer
  back as the next event. It parses and renders nothing: a program does that
  in Lean compiled with it (`lib/IxccExe.lean`). The region is a segment of its
  own; the session theorem is proved over the linked-object model
  ([design](standalone-executables-design.md#x2-as-implemented)).

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
| Higher-order code: P8 defunctionalisation, P9 | In progress (Phase 2): P8 on the compile and recheck path, proved; the known-dispatch rule and P9 planned | [Closures](closures-design.md) |
| Heap completion: scalar fields, large and static objects, reuse, ownership checker | In progress (Phase 2) | [Data, roots and effects](data-and-roots-design.md#dr1-heap-completion) |
| Fixed-width integers, `Int`, arrays, byte arrays, strings, library structures | Planned (Phase 3) | [Data, roots and effects](data-and-roots-design.md) |
| Structured roots, the byte ABI, the claim's ABI descriptor, state-machine effects | Planned (Phase 3) | [Data, roots and effects](data-and-roots-design.md#dr6-structured-roots-and-the-byte-abi) |
| Bignums: a limb library compiled by IxCC | Planned (Phase 4) | [Bignums](bignum-design.md) |
| End-to-end certification: the shared spine (same bytes and the conditional statement, adequacy and progress), the x86 and Aiur routes | Planned and research (the spine) | [End-to-end](end-to-end.md), [certification](certification-design.md) |
| The evaluator contract and the Src image for the Aiur evaluator route | Planned (first) | [Evaluator interface](evaluator-interface.md) |
| Shape typing, stage L | Planned, off the critical path | [Certification](certification-design.md) |
| Resource bounds for the verifier against dishonest input | Planned | [Hardening](hardening-design.md) |
| Scale and usability | Planned (Phase 5) | [below](#scale-and-usability) |
| Standalone executables with no C driver | In progress: the first milestone (roots of `Nat` parameters, a ledgered shell) and the native gates on IxCC-written test executables (X1) implemented, [above](#standalone-executables) | [Standalone executables](standalone-executables-design.md) |

## Scale and usability

**Status: planned** (Phase 5). The budgets are implemented; the rest is
planned.

**Motivation.** The flagship targets are far larger than any program the
compiler has seen. The import closure of the certified kernel's checker
(`IxCK.Kernel.Cached.Installed`) has 53 modules and 1,264 `def` and `abbrev`
lines; with admission and the Ixon reader it has 79 modules and 1,868, before
the parts of `Init` and `Std` it uses (counted by following `import` lines;
upper bounds). The largest committed programs fit
the budgets with headroom between 2.4× and 326× ([Middle-end
budgets](#middle-end-budgets)), but they are small: a global of more than
16,384 nodes or 2,048 levels, or a term more than 2,048 deep, is refused today
whatever the certificate; the nesting budgets cannot grow much while a
verifier must fit an 8 MiB stack.

**Current state.**
- *Implemented.* The budgets above are fixed constants, independent of the
  input's size, set from 8 MiB stack measurements. A step may hold at most 64
  specialisation decisions with masks of at most 64 parameters
  ([`Recheck/Run.lean:173`](../IxCC/Recheck/Run.lean)).
- The front end before the middle end is bounded by depth (`depthBudget`,
  `termFuel`) and, before P1, by `maxLamNodes`.
- Superlinear steps found by measurement in November 2026 (not re-measured
  since): a shrink round reads up to order `n²` nodes in a global's size (census
  reads, above; now charged to the walk's work budget); one walk round was about quadratic (16,000 bindings in
  25.6 s); `encodeK`, which kernel evaluation of the recheck runs (native
  code runs `encode` through `encodeK_csimp`), is quadratic in the program's
  text; `selectRcPolicy` was cubic in let-alias chains; frame `Nodup`
  checks are quadratic. Erased type checking (`V3.Tc.checkEnv`) took about
  30 s on a 1 MB closure, against milliseconds for `Recheck.run`, so the
  roadmap's 10 s target was missed with type checking on; the certified
  kernel's acceptance that replaced it takes about a second and a half on the
  largest committed closures.
- The producer `ixcc compile` was once seen to run past 180 s on a 917-byte
  input with heavy sharing; it now keeps to the re-run's budgets and refuses
  a share DAG of depth 16 at the Lam node budget in about a second, and its
  own cost is near-linear in a closure's definitions ([the
  producer](#middle-end-budgets), the paragraph "The producer"). On large
  closures the compile time is now the checker's `Backend.finish`, about
  quadratic in the object's text, and the kernel's acceptance at ingress.
- Declines carry a `stage: code` and a message (for example
  `rt.params`); `lake exe census` reports the first failing stage per
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
4. **Faster ingress.** Run the certified kernel's acceptance once per
   closure root and reuse its result across compilations of the same closure
   (it is the whole closure's, so one run serves every root).
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
