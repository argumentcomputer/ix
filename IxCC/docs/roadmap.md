# IxCC roadmap

Reworked 2026-11-10 around one goal, end-to-end certification for the x86
and Aiur back ends grounded in Ixon and the certified kernel IxCK. This page
owns priorities, delivery state, acceptance criteria and the decision
register. [End-to-end certification](end-to-end.md) states the theorems the
plan aims at; [compiler design](compiler-design.md) explains the
architecture; [development and validation](development-plan.md) explains how
to land a change; the [documentation guide](README.md) indexes contracts and
evidence.

[Workspaces and recovery](workspaces-and-recovery.md) records the recovery
checkpoints. Their preservation does not select a
new producer or close the implementation acceptance gates below.

## Mission

A generally useful compiler for Lean code, with certification that is
end to end for both back ends, grounded in Ixon and IxCK, and hardened against
dishonest input:
- **x86-64**, with performance competitive with Lean → Clang: if the compiled
  object returns `w` on first-order inputs, then `w` reads back as what the
  claimed constant applied to the inputs denotes, in every model with the
  kernel's laws of IxCK's reading of the closure of that constant and the
  theorems its compilation used. Every other outcome is an
  explicit resource failure (heap, stack, or `Nat` overflow until bignums
  land) or a run that has not finished.
- **Aiur**, first through a fixed evaluator circuit that runs IxCC's source
  evaluator over a serialized image of the checked source program (built and
  proved on the IxVM side), and later by per-program compilation: if the proof
  verifies, the evaluated term denotes the readback of the evaluator's result
  in every such model. This discharges the evaluation axioms that
  `native_decide` and `bv_decide` emit.

Both rest on one *spine* above the source evaluator: the Ixon bytes and a
named constant, IxCK's model (with its laws) of the closure of that constant
and the theorems the unfolding table names, the checked source program, and
the source evaluator's meaning in that model
([end-to-end certification](end-to-end.md#the-shared-spine)). Two links of the
spine are premises about content addresses rather than IxCC theorems: that the
closure has a model with the laws (restated on 2026-11-11 from "IxCK accepts
the environment"), and that the checked source program is faithful to IxCK's
reading of it, with typing derivations for what it runs. IxVM proofs (or a
native kernel run) discharge them, and claims about the same seeds compose by
aggregation; IxCC proves the rest: the source evaluator's soundness and
progress for the kernel's models. Today's
theorems are relative to the source evaluator on the source IxCC's front end
built, with an escape when that source goes wrong; the spine is the critical
path from there to the goal.

Compiled programs are also to run as **standalone executables with no C in
the trusted base**: IxCC writes the executable itself, and the start-up and
system-call logic is self-hosted, a small proved machine-level layer generated
from Lean with as much as possible of it Lean source compiled by IxCC
([standalone executables](standalone-executables-design.md)).

## Current state (2026-11-10)

Tree: this branch at its tip. Phase 1's scalar compiler and the bounded
plain-RC route are implemented and proved relative to SrcEval; the spine is
not started; the Aiur routes are not started in this tree.

**Proved, relative to SrcEval** (`Recheck.sound`,
[`Recheck/Proof/Soundness.lean`](../IxCC/Recheck/Proof/Soundness.lean); the
byte-level `verifyBytes_*_sound` and their root-shape corollaries,
[`CompileClaim/Proof.lean`](../IxCC/CompileClaim/Proof.lean)): an accepted
object refines SrcEval on the checked source `a.src`, unless that source goes
wrong; at a claim's root on the immortal and zero-RC policies, the view
rejects only a result off the root's declared shape
([`Recheck/Proof/RootShape.lean`](../IxCC/Recheck/Proof/RootShape.lean)).
5,800 exact axiom fences ([CI guide](ci.md)).

**Since the 2026-11-09 review**, on this branch:
- the relevance checks run on every program (`checkCanonical`,
  [`Src/Recheck.lean`](../IxCC/Src/Recheck.lean)), and the byte-level
  verifiers re-derive the certificate's annotation (Stage A);
- the front-end lemmas cover the whole axiom closure of every `eqn` and
  `csimp` theorem (`checkAxiomClosure_sound`) and every mode change of
  `Lazify` (`Lazify.run_modeEq`); the Ring-0 frame theorem rests on admission;
- fixed budgets bound the middle end's replay, the nesting depth of every
  stage and the back end's work; every recursion on the verifier path fits an
  8 MiB stack; every certificate list is capped in program quantities
  ([Middle-end budgets](compiler-design.md#middle-end-budgets));
- result-shaped values at immortal and zero-RC claim roots are tagged and
  read back (the root-shape corollaries above);
- the conditional kernel bridge ([`Models/KernelBridge`](../../Models/KernelBridge/README.md))
  is stated as conditional and gated (`lake run check-kernel-bridge`); the trust
  ledger pins the 16 required checks and an integrity rule;
- `main` was merged in.

**Not proved** (the [certification design](certification-design.md#what-is-proved-today)
lists the chain link by link): that IxCC's reading of the bytes is IxCK's; that
the target names IxCK's constant; any semantic fact about the front end (S6);
SrcEval's adequacy for IxCK's model (S8). IxCK's acceptance of the whole
artifact is concluded by every byte-level theorem (ingress runs it, since the
kernel front end's switch) but is not the grounded statements' first premise
(the closure of the seeds under the default table), and the `GoesWrong` escape
can be chosen by a dishonest certificate.

**In progress, not yet in this tree:** the result-type rows of roots compiled
alone and a shape view that makes the third `GoesWrong` clause an equivalence
on the immortal routes, with constructor-tree shapes for plain-RC roots; the
port of the equations export to this repository's
`ix`, with a flag that wrote the unbound envelope IxCC then read (removed after
the role-bound refreeze), as the first phase of regenerating the fixtures from
this tree; a SrcEval step counter for
the IxVM workstream's first measurement (EV-0; the evaluator's clock is a depth
bound, not a step count); producer speed.

**In this tree, on the compile and recheck path:** P8, closed-world
defunctionalisation ([closures design](closures-design.md)), as the middle
end's closures step after the certificate's steps: a program with no
residual closure whose roots take their declared parameter counts passes it
unchanged; otherwise each root whose Anf parameter count is not its declared
count gets an entry at the declared count, and P8 removes every closure.
`fir.closures` is unreachable after it. The end-to-end theorems hold on every
input of exactly its root's declared count, and on every input of a program
the step leaves unchanged (every program that compiled before the step was
added with its roots at their declared counts), so they say what they said
before for those programs ([closures design](closures-design.md#proof-obligation)).

**Current integration surface:**

| Component | Scope |
| --- | --- |
| Scalar & top-level compiler | Src-to-ELF recheck path (`Recheck.sound`), top-level `Compiler.compile` (`--rc auto\|on\|off`, `Compiler.compile_sound`), `CompileClaim` (`verifyProgram_*_sound`, `verifyBytes_*_sound`, `*_rootShape`), `Ring0` (`verifyRing0Sip_sound`), certificate/artifact checks and native pipeline suites |
| Bounded plain RC | `Recheck.RcReplay` API (`RcReplay.run`, `RcReplay.sound`, `recycled_session`); exact ownership/certificate replay (`checkPlainMap` / `checkContractPlainMap`), ordinary Lir recycling runtime, SrcEval-relative object theorem, complete per-stage/native values, executed RC event counts and heap-failure/corruption controls; final producer integration remains open |
| [Ixon v4 ingress](ixon-v4.md) | ix's v4 codec with canonicity evidence and pure-BLAKE3 authentication, resource admission, claim binding; both envelopes, the role-bound one with its role table authenticated and its pinned identities read from it ([byte contract](byte-contract.md)) |
| [x86 target model](x86-encoded-instructions.md) | Typed x86 AST and machine, E1 per-form encoder/decoder and execution laws, E2 [streams and ELF objects](x86-stream-objects.md), [stream checking](stream-checking.md), the [reference-model record](x86-reference-model.md) |
| [Legacy Aiur model](aiur-backend.md) | A verifier-side model of an earlier Aiur bytecode: vocabulary, wire format, semantics, static checks, counter analysis, memory and rank AIRs. Neither Aiur route uses it ([repository and landing](#repository-and-landing)) |
| Standalone executables | `ixcc compile --exe`: a static Linux x86-64 executable of a root with `Nat` parameters and a `Nat` or field-less result, written by IxCC with no C, linker or driver; the shell is ledgered, the layout's driver contract proved ([design](standalone-executables-design.md#x0-as-implemented)) |
| Tools | Trust ledger, build-graph manifest, check helpers |

### Earlier state, as recorded on 2026-11-09

Phase 1's scalar pipeline is implemented: Src evaluation through checked
erasure, middle-end transformations, register allocation and ELF emission.
`Recheck.sound` covers objects accepted by `Recheck.run` under
`X86.Driver.Ok`, relative to SrcEval. Its return clause allows source
`GoesWrong`; safety requires excluding that case. The
[correctness statement](compiler-design.md#correctness-statement) records the
precise scope and native-model assumptions. Source adequacy against the
certified kernel's model remains open.

ix's [`Models/KernelBridge`](../../Models/KernelBridge/README.md) package does
not close it. It proves a conditional simulation lemma: given a kernel
environment storing the `Nat` basis and a user-supplied relation between Src
constants and kernel terms, a successful `Src.run` on `Nat` literals is
matched by kernel `Red` reduction of the related term, which then denotes the
same literal in every model where it is readable and graded. Its environment
and kernel term are not derived from a compile claim's environment or target,
and the relation can be built only for definitions without type arguments,
numerals, typeclass operations, `match` or recursion (of the 69 fixture roots
surveyed in its README, only the identity `Abi.nat1`). Recursive
programs need a denotational step for equation and csimp resolutions in place
of kernel reduction.

The actual scalar compiler entry point now has a composition theorem:
`compile_parts` exposes successful ingress, production and certificate replay;
`compiled_sound` derives the same SrcEval-relative object guarantees from
successful `compile`. Its seven separate fences retain the existing native
BLAKE3 dependency. This closes the entry-point composition gap, while source
adequacy, source safety and the Phase 1.5 acceptance gates remain open.

Lean 4.34.1 and Ixon v4 landed on October 3. Phase 1.5's later resource-checker
and equation/profile-binding work remains unfinished. The consumer changes
have been recovered into the integration tree; focused checks and all 14
required local Nix checks passed on the earlier consumer/readback snapshot. No final
replacement producer has been selected or
refrozen. The latest retained contract-sensitive typing experiments fail the
original acceptance gates on the `cold79` and `Q06` workloads (resource-checker
inputs from the Phase 1.5 work; they are not kept in this repository); upstream
compiler certification does not discharge those obligations. Phase 2
groundwork now includes bounded
constructor-result signature discovery, dynamic-header readback laws, and
a promoted checked plain-RC compiler with size-class recycling and iterative
release. `Recheck.RcReplay.sound` composes accepted replay through the actual
Lir runtime and emitted object, relative to SrcEval and the existing driver
and source `GoesWrong` contracts. Complete output ownership, public raw-word
release and reentry on the reached heap have operation proofs. The focused
compiled production gates pass, including 168 same-arena calls/drops with
complete C/Lean values and all allocated addresses reclaimed. This is a
bounded shared-constructor route, not general Phase 2 ownership optimization.
The promoted proof/fence, trust/build-graph and all 16 required local Nix checks
pass on the 2,343-file snapshot, including the ten required RC behavior
commands. That local run with the existing store took 25m 02.062s; it does not establish
hosted CI or cold-store timing. Final producer and fixture refreeze gates
remain open.

The later consumer regressions are installed and pass focused execution.
The source suite now runs 8,529 assertions, including nine discriminating
resource-bound `csimp` controls and pinned SrcEval step counts
([source steps](source-steps.md)). The dated OS04 annotated/plain recursion
records that once added Src/Fir/Own observations of an annotated recursive
program were retired with the kernel front end's step 4 (2026-11-11, DO-18):
they were unbound, and the `ix` of this repository cannot write a role-bound
successor ([CI coverage record](ci.md)).

The Lam suite additionally passes 134 evaluation-order assertions; its default
run has 28,188 assertions. Sixteen synthetic cases pass actual
table/relevance rechecking (without `checkCanonical`, which their placeholder
types cannot satisfy), lazification and erasure before independently
checking Src and Lam outcomes. They distinguish direct-case demand, strict
wrappers and overapplication order, while retaining the separate resource
profile compatibility and final producer obligations.

The active goal combines Phase 1.5 completion with the first Phase 2
slice: real `List.reverse` through checked plain reference counting,
allocation/reclamation, the composed SrcEval-relative proof and native tests.
Independent heap foundations can proceed alongside producer repairs; final
real-source integration requires the reviewed producer and consumer gates.
General K2/K3 coverage and ownership optimizations remain later Phase 2 work.

The remaining combined acceptance gate is the Phase 1.5 resource and consumer gate
at the October 9 selected cap of 500,000 charged steps per declaration/equation
and depth 256, a reviewed final producer with
reproducible fixture refreeze and verdict review, and complete proof/fence,
trust, build-graph and Nix checks at that final integration head. Historical producer bytes still
back the current RC fixture. Neither the bounded heap result nor upstream
certification discharges those remaining obligations, so Phase 1.5 and the
combined goal are not marked complete.

Optimization toward the previous 100,000-step target remains follow-up work.
Fresh validation admits the isolated Lean cold action at 438,235 steps, but
full public Q06 still returns `Budget` at declaration 740 in both Lean and Rust.
Repair at the selected 500,000 cap remains required. Historical failures and
larger-budget diagnostics retain their original meaning, including the separate
1,934,024-step Rust measurement of declaration 740. A subsequent diagnostic
replays the actual Rust action with matching result and full checker state:
it exhausts all 500,000 steps with depth fuel still available. No optimization
has yet restored full Q06 acceptance.

The September 29 reset, retired pipeline, Ixby backend and Stage2 fixture are
preserved on `jcb/ixby-archive` of the pre-merge `argumentcomputer/Compilatr.ix`
repository, with their former gates and measurements.

The required surface includes pipeline suites, proof/fence and trust audits,
corpus and deterministic-step checks, and x86 decoder/hardware checks. The
[CI guide](ci.md) records their coverage and platform conditions. The checked-in
pre-promotion inventory contains 4,367 exact axiom assertions. Promotion adds
979 exact fences (923 base, eight release/reentry supplements and 48 restored
earlier proof-gate assertions), totaling 5,346 while preserving every existing
assertion. All 29 original Cfg pure examples and the 16 runtime/bridge cases
with bounded timeout checks are also retained. The augmented complete proof
aggregate and all16 required local Nix checks passed on the2337-file promotion
snapshot in23m25.126s with the existing local store. The subsequent
`tests-pipeline-rc` supplement adds four required modes for complete IR/native
observations, actual RC event counts, object-only corruption and real-source
heap exhaustion; all four passed in isolated staging before integration.
Every later integration tree requires the same full validation surface.
Final selected-budget producer acceptance/review/refreeze remains open; no
hosted-CI or cold-store timing is claimed.

## The fragment compiled and proved today

- **Input.** An Ixon v4 closure, role-bound or not, and an unfolding table
  (`eqn`, `csimp`, `case`, `inline`, `lazy`, `prim`, `opaqueByValue`).
  Admission rejects `partial` and `unsafe` definitions, extern opaques and
  relevant axioms; erasure declines string literals in relevant positions.
  IxCC reads the role-bound envelopes this repository's `ix compile` writes,
  with pinned identities from their role tables ([byte
  contract](byte-contract.md)); every committed closure a compile path reads is
  role-bound, written by this repository's `ix` ([corpus](corpus.md)).
- **What ingress reads** (since 2026-11-12). Only the records its seeds
  reach (`Src.Ingress.reach`: every root the sidecar names, not only the chosen
  ones; the pinned identities; the resource context's addresses; the equation
  theorems of the sidecar's proposals on reached subjects and the resource
  equations, with their proofs), a theorem's proof only where an equation
  theorem's closure reaches it; IxCC's consumer budget (depth 256 with a
  `share` node a leaf, 4,096 entries per list) applies to those, so a record
  nothing reaches (a structure's `mk.injEq`, a large proof a string function's
  termination argument cites) no longer refuses the closure: a structure of
  254 fields compiles again, and so do programs whose closures carry an
  over-budget proof. Every record is still accepted by the certified kernel
  and bounded in depth as stored (2,560, shares expanded; not the terms the
  kernel builds) ([compile boundary](compile-boundary.md)). Before, from the
  role-bound refreeze (2026-11-11), the decoder refused a whole closure for any
  record over the budget. A claim is verified with the sidecar it was made with.
- **`csimp` proposals** (a known gap, since 2026-11-12). A table entry may name
  only a theorem ingress read with its proof, which is a theorem a sidecar
  proposal names; the `ixcc/k1-equations/1` sidecar carries `eqn` proposals
  only, so no `csimp` entry verifies from a sidecar (none did in practice: the
  producer proposes only what the sidecar gives). The remedy: the sidecar
  carries `csimp` proposals (`ix compile` exporting a `@[csimp]` theorem with
  its two constants), which `Seeds.of` already takes as proof seeds.
- **Long literal lists** (measured 2026-11-12, the same before and after the
  change above). Lean refuses a list or array literal of 3,000 elements at its
  default `maxRecDepth`; raised, it splits the literal with `let`s (51 deep),
  and IxCC declines it, at 3,000 elements in the middle end (`anf.produce`: a
  Lam global exceeds the node budget) and at 5,000 at `ingress: decode` (a list
  over IxCC's 4,096-entry budget). An explicit chain `a :: b :: … :: []` of
  3,000 or 5,000 elements is as deep as it is long (3,005 and 5,005 with
  shares expanded) and is declined at `ingress: decode`: past IxCC's depth
  budget (256, a `share` a leaf) and past the depth one record may have before
  the kernel (2,560). Compiling such programs needs the kernel to walk deep
  terms without overflowing its stack (the kernel package's work, "Hardening")
  and IxCC's budgets to grow with it.

- **Values.** `Nat`, exact above Lir and at run time a tagged word below
  2^63 (a larger value is the resource failure `natOverflow`); constructors
  of inductive types; □. Fixed-width integers have no representation of
  their own (erasure unboxes them to `Nat`); `UInt8` to `UInt32` work, but
  every `UInt64` operation fails natively with `natOverflow` on every input,
  since its reference body computes modulo the `Nat` 2^64 (measured,
  [DR2](data-and-roots-design.md#dr2-fixed-width-integers-and-int)). Stage W1
  makes the word operations primitives; so far SrcEval's rule F6w, its table
  entry and check, and the stored equations `ix compile --equations --word-equations` adds and
  names exist behind a switch that is off (`Table.Config.words`), so nothing
  compiles differently yet. There are no arrays, byte arrays or strings.
- **Higher-order code**: bounded inlining and specialisation (P3, P4)
  remove what they can; the closures step (P8, Phase 2) turns any remaining
  closure into a constructor cell and every unknown call into a call of a
  dispatcher, so no program is declined for its closures (`fir.closures` is
  unreachable).
- **Memory.** Immortal cells, or the plain-RC route: shared constructors
  with 1 to 254 scanned fields (no scalar fields yet), 71 size classes with
  free lists, iterative release (`--rc auto|on|off`).
- **Roots.** Level-monomorphic, at most five `Nat` parameters; results that
  are `Nat` or enumerations (immortal and zero-RC policies) or first-order
  constructor trees (plain RC). A compile claim covers root index 0.
- **Internal tail calls.** The internal calling convention passes seven
  arguments in registers and the rest on the stack, but a tail call passes at
  most seven (the allocation validator's `convention` check: a tail call
  reuses the caller's frame, which has no outgoing stack cells for it). So
  `Fir.lower` keeps a call in tail position as a tail call only within seven
  arguments, or when it calls its own function (a jump to the entry), and
  lowers one of more as a call and a return (`Fir.Lower.tailCall`, since
  2026-11-11; before, register allocation declined it, `alloc.fallback`). That
  costs a frame per such call: a loop through one uses stack in every
  iteration and a long enough one ends with the stack-exhaustion status
  (status 2), never a different value. Erasure keeps every binder slot,
  erased type and instance parameters included, so monad-transformer code has
  functions of eight parameters (`StateT.bind`, `StateT.map`), and the
  closures step's dispatchers call a closure's function in tail position: a
  `StateT`-over-`Except` loop through the library's `StateT.bind`
  (`fixtures/corpus/phase2-closures`, `Closures.stateLoop`) compiles this way
  and uses 32 bytes of stack per iteration on the immortal route, 96 under
  plain RC (its last case: 150 iterations end with the stack status in an
  8 KiB stack); the same loop with the stack's `Monad` instance written for
  it, `Closures.stateLoopSE`, has proper tail calls. K3 `rbmap` and
  `const_fold` compile for the same reason. What removes the frame is proper
  tail calls with stack-passed arguments (the caller's incoming argument area
  must hold the callee's: a convention change in Xl's semantics, the
  validator and stacking, with their proofs), or dropping the erased
  parameters (P5), which brings `StateT.bind` to four.
- **Evaluation order of a match.** Lean elaborates a `match` with a catch-all
  through a sparse casesOn (`T…._sparseCasesOn_N`) whose arms are ordinary
  arguments, and compiles it as a `cases`. Since 2026-11-12 the table gives
  each one a `lazy` row, found by its shape (`Table.checkSparseCases`), so
  only the chosen arm runs, as in Lean's code; before, every arm ran first,
  which made K2 `queue` quadratic (598 s at 100,000 elements under plain RC;
  now 0.10 s, and 4.65 s at 5,000,000 against Lean's 0.22 s, the rest a
  constant factor of `List.rec` with closures) and made an unchosen arm's stack
  or heap failure the program's (`fixtures/corpus/phase2-closures`, fixture
  `sparse`; [performance/sparse-cases-2026-11-12](performance/sparse-cases-2026-11-12/README.md)).
  **A known difference from Lean's cost model remains:** Lean's code
  generator also inlines `@[inline]` definitions (such as `Option.elim`,
  whose `none` value is an ordinary argument) and floats a pure `let` into
  the one branch that uses it (LCNF's `floatLetIn`); IxCC does neither, and
  its middle end cannot move a call that may not return into a branch, so
  such a value is computed on every path (not measured). **A known cost of
  the step model:** an argument of a sparse casesOn that is already a value (a
  λ arm, a variable major) is passed by name too, and costs SrcEval one forced
  slot per use (K3 `const_fold` +4.9 % charged steps at `n = 10`; its compiled
  code is byte-identical). The remedy is the value-shaped exemption: pass such
  arguments strictly, in `Lazify` (not marking them by name) and in erasure
  (accepting a strict value at a `lazy` position) together. **Unchecked:** a
  pinned `lazy` row may still stand beside an entry that replaces the
  definition's body (`eqn`, `csimp`, `case`, `prim`); only a sparse casesOn's
  row is refused there (`Table.lazyResolveOk`). No committed table has such a
  pairing.
- **Proved.** For an accepted certificate, the object refines SrcEval on the
  checked source `a.src`, with the `GoesWrong` escape, under the x86, loader
  and driver assumptions of the [trust ledger](trusted-extern-ledger.md); at
  immortal and zero-RC claim roots the view case of the escape means a result
  off the root's declared shape. The stuck and trap cases remain, and a
  dishonest certificate can choose them.
- **Not proved.** That `a.src` is the ingested program's meaning (S6), that
  SrcEval agrees with the certified kernel's model (S8), that IxCC reads the
  bytes as IxCK does. (IxCC's erased type checker, of which nothing was
  proved, is deleted.) See the
  [certification design](certification-design.md).

## Plan

Revised 2026-11-10. The goal is the one in [Mission](#mission). The plan has
one critical path, the spine, and several tracks beside it.

```text
                  Ixon bytes + named constant + the table's theorems (the seeds)
                                      │  (i) their closure has a model with the laws:
                                      │      IxVM checkEnv claim on the seeds, or native run ── premise
                                      │  IxCC reads the same bytes, same hash, same roles     ── SP-B
                          checked source program (= the image, digest D)          ── EV-2
                                      │  (ii) faithful to IxCK's reading, and typed:
                                      │      lowering claim, or native check                 ── premise
                                      │  valid table entries, primitives, readback            ── SP-0
                                      │  SrcEval soundness + progress                         ── SP-A, SP-1
            ┌─────────────────────────┴─────────────────────────┐
   x86: proved pipeline, E1, E2/ELF                Aiur (i): evaluator circuit E over the image
   (implemented; driver and ISA models             (IxVM side; IxCC owes EV-1, EV-2, the clauses)
   to retire or prove: XB-1, XB-2)                 Aiur (ii): Fir → formal Aiur per program (AR-2, later)
```

The pipeline to x86 and its staged scope:

```text
Ixon v4 → Src (relevance-annotated kernel terms + unfolding table)
        → Lam (erased λ-calculus)
        → Anf (join points; shrink, inline, specialise; P8 defunctionalisation, in progress)
        → Fir (first order, known calls only) → Own (explicit RC, borrow, reuse)
        → Cfg (control-flow graph) → Lir (words, memory, runtime)
        → Xv (x86 on virtual registers) → Xl (allocated) → typed x86 → E1 → E2/ELF
```

### Tracks

- **The spine (SP), critical path.** Ground the source evaluator in IxCK:
  byte compatibility first (SP-B: IxCC consumes exactly the bytes the kernel's
  claims are about), then the conditional statement (SP-0), the typing-transport
  question and an adequacy spike (SP-A), adequacy and progress on a first
  fragment (SP-1), widening (SP-2), and the native discharge of the premises
  (SP-N), whose kernel-based front end replaced the erased checker as the
  only front end at the switch's step 3 (the owner's decision of
  2026-11-11; the checker's code is deleted, step 4), with the kernel's blow-up on chains of `let` fixed
  in the kernel package on this branch in parallel (landed). Kernel acceptance and the image's faithfulness are premises
  that IxVM proofs (or a native kernel run) discharge, not IxCC theorems.
  Designed in the [certification
  design](certification-design.md#the-architecture-premises-discharged-by-proofs).
- **The evaluator interface (EV), first.** What the Aiur evaluator route needs
  from IxCC before any proof: step counts (EV-0), the evaluator contract
  (EV-1), the image format with a deterministic producer and its interfaces
  (EV-2). Designed in the [evaluator interface](evaluator-interface.md).
- **The Aiur routes (AR).** AR-1, the evaluator circuit, is the IxVM
  workstream's; AR-2, per-program compilation to formal Aiur, is research and
  unscheduled ([end-to-end](end-to-end.md#aiur-form-ii-per-program-compilation-later)).
- **The x86 back half (XB).** The C driver is off the execution path
  (XB-1, the same work as IxOS-0; done with X1) and replace the instruction-set assumption
  by agreement with the Sail model (XB-2, the [reference-model
  route](x86-reference-model.md)).
- **The native route's breadth (Phases 2–5).** Heap completion and closures,
  data and roots, bignums, scale. No longer the spine; each phase lists what it
  adds to the spine's obligations and what the Aiur routes get from it.
- **Hardening (HD).** Resource bounds for the verifier, a property no
  correctness theorem gives ([hardening design](hardening-design.md)).
- **Repository and landing (RL).** Fixtures regenerated from this tree,
  adaptation to the certified-IxVM work when it lands, the legacy Aiur code,
  the pull request and the squash ([below](#repository-and-landing)).
- **Side products.** Shape typing (CD2) for confinement without semantics and
  for typing Fir for formal Aiur; stage L (CD3) for the bignum library and the
  IxOS monitor. Neither grounds anything in IxCK.
- **Resource soundness (RE).** What usage, ownership and locality
  annotations guarantee, a theorem of its own that the kernel-model grounding
  cannot supply: the resource checker's confirmed hole closed (RE-0), IxCC's
  ownership checker verifying the annotations it acts on (RE-1, Phase 2), an
  instrumented source evaluator and a first-fragment theorem (RE-2), widening
  (RE-3) ([below](#resource-soundness)).
- **Standalone executables (X).** Executables written by IxCC with no C
  driver, C library or linker: a typed-x86 shell and the executable writer
  (X0), proved (X0-P), the native gates moved off the C driver (X1, the
  redefined XB-1), then effects in stages over one platform interface (X2 to
  X5), and the IxOS tender as a second platform (X6)
  ([below](#standalone-executables)).

### Milestones

Sizes are estimates, with their basis; calendar figures assume one
experienced engineer per line of work. *Owner* is the default, subject to the
[open decisions](#open-decisions).

| Id | Content | Depends on | Exit test | Size [estimate] and basis | Owner | The neighbouring workstream can rely on |
| --- | --- | --- | --- | --- | --- | --- |
| RL-2 | Adapt to the certified-IxVM work when it lands: merge `main`, rename pass, re-recorded digests, inventories and ledger | that work landing | the root build and all 16 `ixcc-*` checks pass on the merge | days to two weeks: the last merge of `main` took about a day | IxCC | — |
| SP-B | **Byte compatibility, the spine's first milestone**: IxCC consumes exactly the bytes the kernel's claims, and those of a consumer proving claims about role-bound environments, are about, identified by the same `(root, role table)` ([byte contract](byte-contract.md)). *Implemented:* role-bound envelopes read, the binding authenticated and decoded against the kernel's role vocabulary, the version read and kept; pinned identities from the role table; projection records accounted; role-bound fixtures whose root and role table equal the kernel's host statement; one hash, every address IxCC computes being pure BLAKE3, so the byte-level fences rest on the standard axioms only; the compile claim names the role table beside the root (validator 7; the former payload refused), on both sides of the codec; a registered role-bound family, a required gate; `ix compile` binds every role whose constant its artifact holds, including those only the certificates' closure brings in, so the kernel admits its role-bound output whole. every committed family refrozen in the role-bound form by the tree's own tools (`tools/regenerate.sh`, 2026-11-11), and `ix compile --unbound` removed (`ix compile` writes the role-bound envelope only, as on `main`). *Remaining:* none | — | a compile claim and a kernel claim about the same role-bound artifact name the same `(root, role table)`; the registered role-bound family passes `corpus check` and `tests-corpus` with the unbound family's results; byte-level fences on the standard axioms only (all three met) | under 2k lines: the reading 0.6k, the hash, the claim field and the gate about 0.6k (implemented); the refreeze, data | IxCC | IxCC reads the same bytes as its claims, under the same hash and role table |
| EV-0 | SrcEval step counts (a counting twin of SrcEval; the clock is a depth bound): implemented ([source steps](source-steps.md): `src-steps`, pinned rows in `tests-src`, the tables of every committed family); the IxVM experiment's families wait for their closures | — | K1 tables and the IxVM experiment's families, reproducible | about 0.4k lines; days | IxCC | the common unit for its first measurement |
| EV-1 | The evaluator contract, version 1: version, rule anchors, changelog, pin check; closed-term entry points | — | entries agree with `Src.run` on K1; an unversioned change fails the pin check | 0.3–0.6k lines and documents; weeks | IxCC | a frozen SrcEval to prove the circuit against, and a differential oracle |
| EV-2 | The image, version 1, with shared subterms: format, deterministic producer, round trip, interfaces (role table, readback to Ixon, budgets) | EV-1 | theorems fenced; round trip over every committed closure in a gate; byte-identical images on two machines; digests committed | codec 0.5k, proofs 1–2k, interfaces 0.5–1.5k; 1–3 months (IxCC's Aiur wire format, 1.3k with proofs) | IxCC | a stable program identity and the circuit's input format |
| SP-0 | The conditional statement: the claim also binds the image digest, so that the target and `D` fix the seeds; the laws as an explicit structure of hypotheses about a model (named as on the IxVM side); the faithfulness and typing clauses; soundness and progress as separate propositions; the conditional x86 and evaluator statements with both as explicit hypotheses; the table (`eqn`, `csimp` from `mem` and `eq_equality`; `case` from δ and ι), primitive, `let` and readback lemmas in every model with the laws | SP-B | the conditional statements fenced; role-bound K1 fixtures verify under the new claim format | 6–13k lines; 2–4 months (IxCK's reader 1.3k and IxCC's ingress 0.3k for the reading; the lemma estimates of the certification design; 2–4k more if the `Nat` operations' meaning must be derived on IxCC's side) | IxCC | IxCC reads the same bytes as its claims, under the same hash and role table; the `eqn`/`csimp` and primitive lemmas for its own discharge path |
| SP-A | The typing-transport question is answered (2026-11-11: a model gives no typing for subterms, so typing derivations join premise (ii)); the spike: soundness on K1's `fib`, then `decide (fib 10 = 55)`, with the derivations from the kernel's runs | — | the spike theorem fenced or a stop report | 1–3 months | shared | whether SP-1 is engineering |
| SP-1 | Soundness and progress on the first fragment, by a semantic relation indexed by the kernel's types, discharging SP-0's hypotheses ([certification design](certification-design.md#sp-1-adequacy-and-progress-on-the-first-fragment) compares it with a simulation by kernel reduction). **In progress** since 2026-11-11 as [the grounding library](certification-design.md#the-grounding-library-sp-1-in-progress) (`IxCCGrounding`, required check `ixcc-grounding`): G1a and G1b landed: soundness at a root on first-order arguments (`rootSound`, with `fib` and `decide (fib 10 = 55)` as instances), from checks run on the bytes, over every model with the laws as hypotheses, under `SitesOk`, F5's meaning proved by the generic `case` lemma; G2a landed: the direct route discharges the typing hypothesis at every site of both instances (`fibRoot`, `decideRoot` have none) and of every measured closure the check accepts (elsewhere it remains at the sites the direct route refuses); two laws (constructor canonicity, the projection of a constructor) restricted on 2026-11-11 to families that are not propositions, both false as first landed in a proof-irrelevant set model, and the laws not yet shown to have a model (canonicity scheduled by no one); G2b landed: ι and `Nat` arithmetic on literals in the conversion (`iota_rule` and `nat_accel` added to the laws the direct route rests on), string literals, `imax u u` in the level comparison, two fuel levels per nested argument, a renaming-tolerant `case` shape: on the corpus the direct route refuses 22 sites in four closures (262 before) and the check accepts 24 closures (22 before); G3's first step landed: the direct route's cost profiled and fixed (constants looked up in a table of the reading, a telescope's width costing no fuel): `sitesDirectB` on `tags125` 48.7 s instead of 624 s interpreted, all 418 of its sites accepted (171 before), `tests-grounding` 1.4 s instead of 5.4 s, and on the 49 closures that load the direct route refuses 21 sites in three; G3's parts A and B landed: recursors enter the checked set by class (`declOk` admits a class once its case of the fundamental lemma is proved; a new conjunct `recShape` checks each recursor's stored shape, its type a binder for every argument SrcEval takes), a recursor head in the relation, the landed root theorems kept as corollaries; G3's part C landed: the class of the built-in `Eq.rec` admitted, F3's meaning there proved from ι and the model's `Eq` law (a checked `EqRecBasis`: its type and rule as F3 reads them), so the check accepts 29 of the 49 closures that load (24 before); G3's part D, first step, landed: the field-less recursors without parameters (class `flat`, `Bool.rec`) admitted, F2's meaning there proved from ι and level-parameter irrelevance alone (canonicity only where such a recursor's constructor has level parameters, none measured; checked facts `RecTele`, `RecProg`, `RecCtorsRaw`), so the check accepts 31 of the 50 closures that load; what remains: a model of the laws, `ResultTag` (a checked hypothesis that rejects some roots), and the rest of G3 (rule bodies that apply a minor premise to a field, part E, which the `tags` closures need, then recursors with parameters, `List.rec`, where F2 needs canonicity, then the rest of the recursors, and the rest of the residue: projections out of a bound variable, as recursion compiled through `brecOn` makes them, need a typing derivation or a model fact the laws do not state), G4 (widening, which meets that shape as soon as recursors enter the checked set), G5 (progress) | SP-0, SP-A; the external dependencies of XK | both [exit tests](certification-design.md#the-first-grounded-fragment) | 14–30k lines; 6–12 months after SP-A (erasure's simulation, 10.1k) | shared, IxCC leading | the model fact that discharges an evaluation axiom, given the circuit's refinement and the two premises |
| XK | **External dependencies of the spine** (none in this repository; listed for tracking): the IxVM consistency theorem's eight obligations proved; its claimed environment fixing kinds and values; its derivations exposed or the lowering claim proving typing; the rules' soundness over the public model; the projection of a constructor and the `Nat` operations on literals as public laws; constructor canonicity across parameters and levels (asked 2026-11-11; else a relation carrying types on IxCC's side); public level irrelevance; "the annotation pass preserves denotation"; the table restriction lemma | the certified-IxVM work | each stated on the kernel or IxVM side | theirs | kernel and IxVM workstreams | — |
| SP-2 | Widening: `Quot`, nested inductives, strings, data primitives, plain-RC results, other roots | SP-1, the phases | per item | per item | IxCC | wider images |
| SP-N | Native discharge of the premises, for x86 consumers without IxVM proofs: IxCK run natively (since 2026-11-11, existence by the logical entry on the closure of the seeds under the IxVM claim's table, DO-37, the kernel front end's KF-4), the image's faithfulness and typing discharged against IxCK's reading (DO-6), and the erased checker replaced by IxCK in the producer and on the native verifier path (decided 2026-11-14; in progress, as a kernel-based front end in new modules beside the existing one, designed in the [kernel front end](kernel-front-end-design.md); the switch in progress: its step 2, moving what is not typing out of the checker, and its step 3, the kernel front end the only front end, done 2026-11-11). Decided by the owner on 2026-11-11 ([decisions](kernel-front-end-design.md#decisions)): the switch proceeds now; the kernel's blow-up on chains of `let` is fixed in the kernel package on this branch, in parallel, and has landed (on a hostile `let` chain the kernel front end's acceptance took 52.2 s at 30 `let`s against the erased checker's 0.19 s, and takes 28 ms with the fix); the kernel's level walks on shared levels are memoised, and the level comparison itself (coNP-hard for levels with `imax`) stays exponential on some small constants until its planned call budget. the front end passes the artifact's own reducibility hints to the kernel's entry and reading (2026-11-12, as `ix check-lean` does: without them the kernel computes its own heights, and a one-line `rfl` proof Lean checks in a millisecond took time exponential in a literal's width; hints are advice, no theorem depends on them, and a hostile hint can make the kernel slow or decline, never accept something else). Working defaults, awaiting the owner's confirmation: IxCC's reading checked natively against IxCK's (DO-6 (c)), the kernel's tiered entry, the artifact's own prelude; unbound environments are refused, which follows from the switch | SP-B; SP-0 for the statement; for the switch's step 3, the role-bound refreeze (RL-1 phase 2, in progress); before the branch merges, the kernel's fix of its blow-up on `let` chains (KF-3, in parallel on this branch) | the x86 statement with both premises discharged in one native run; the erased checker deleted | 2–6k lines (built: about 1.5k; the switch deletes about 13.3k) | IxCC | — |
| AR-1 | The evaluator circuit, its refinement of SrcEval, the lowering claim, aggregation | EV-1, EV-2 (unproved deployment); SP-0, SP-1 (proofs) | the IxVM workstream's | that workstream's estimates: the circuit 5–10k lines of formal Aiur, its refinement 10–25k, the lowering check 3–8k | IxVM workstream | — |
| AR-2 | Fir → formal Aiur with a backward simulation, one object enumeration per program, small `Nat` below 2^56 | RL-2 (formal Aiur in this repository), a key-derivation story or a standalone customer; CD2 optional | K1 through per-program circuits | 8–15k lines for the `Nat` and tree fragment (a spike outside this tree; the IxVM side estimates 10–25k) | unassigned | — |
| XB-1 | = IxOS-0, as redefined on 2026-11-14 (DO-34): IxCC-written executables replace the C runtime driver in the native gates, out of process, with no C and no in-process trampoline (X0 then X1 of [standalone executables](#standalone-executables)); first planned as a host loader calling an object's entries through a trampoline. Done with X1 | X0 | as X1 | as X0 and X1 | IxCC | — |
| XB-2 | Agreement with the Sail x86 model (S0, S1, S2) | — | as in the [reference-model route](x86-reference-model.md) | research | IxCC | — |
| HD-0 | A budget on a closure's typing; a required fuzzing check | — | the check required; typing bounded per closure | under 1k lines and the gate; weeks | IxCC | — |
| HD-1 | Typing off the verifier path: the erased checker replaced by the certified kernel (decided 2026-11-14, done within SP-N) | SP-N | the verifier path and the producer call no erased-checker function | — | IxCC | — |
| HD-2 | One work budget threaded through the verifier; a total-work theorem | SP-0 | the theorem fenced | 2–5k lines | IxCC | — |
| HD-3 | No recursion over input-sized data; every entry point at the budgets on 2 MiB | — | the gate | 1–2k lines | IxCC | — |
| RL-1 | Fixtures regenerated from this tree. Phase 1 (equations export, unbound envelope, a trial family): done. Phase 2: the role-bound refreeze by `tools/regenerate.sh` and commit-hash provenance replaced by descriptions: done (2026-11-11); before the merge, a final regeneration on the merged state, checked by `tools/regenerate.sh --check` | DO-15 to DO-20 | `corpus check` and the suites pass on every regenerated family; no tracked file cites a commit outside this repository or of this branch's history | phase 2 changes every closure, sidecar, census and manifest, the pinned tables and generated artifacts | IxCC | regenerable fixtures |
| RL-3 | Retire the legacy Aiur model (about 5.8k lines) and the vendored snapshot (about 3.5k), superseded or contradicted by the formal Aiur package: tests, fences, tools, fixtures, the `ixcc-aiur` check, its ledger scopes and pins, docs | RL-2, DO-14 | all required checks pass without them | a deletion and inventory updates | IxCC | — |
| RL-4 | The pull request, after the certified-IxVM work finalizes; the squash | RL-1 phase 2, RL-2 | review | — | IxCC | — |
| Phase 2 | Heap completion (DR1) and closures (P8) | Phase 1.5's final producer for K0 | [Phase 2](#phase-2-heap-and-closures) | 25–50k lines (DR1 20–40k, P8 5–9k) | IxCC | nothing the evaluator needs |
| Phase 3 | Data and interface (DR2–DR9, P9) | Phase 2 | [Phase 3](#phase-3-data-and-interface) | 30–60k lines (the DR items' estimates) | IxCC | the data primitives' meaning lemmas at the SrcEval level |
| Phase 4 | Bignums | DR1–DR4 | [Phase 4](#phase-4-bignums) | 14–26k lines (bignum design) | IxCC | a shared `Nat` specification |
| Phase 5 | Scale and usability | — | [Phase 5](#phase-5-scale-and-usability) | 8–16k lines | IxCC | — |
| CD2 | Shape typing | — | as in [CD2](certification-design.md#cd2-source-safety-a-checked-shape-typing) | 5–7k lines | IxCC, when IxOS-4 or AR-2 needs it | — |
| CD3 | Stage L translator | SP-0 | a K1 prototype | not estimated | IxCC, when Phase 4 or IxOS-4 needs it | — |

**In parallel.** SP-B first; from the start also EV-0, EV-1 then EV-2; SP-0 once SP-B has fixed the bytes; SP-A; HD-0 and
HD-3; RL-1; Phase 2's P8 milestone 1 and heap work. RL-2 interrupts whatever is
running when the certified-IxVM work lands. SP-1 starts when SP-A has
answered and SP-0 has stated what it must prove. The proposed order of priority is DO-7.

### The spine and the IxVM workstream's requirements

The IxVM workstream has stated what it needs from IxCC. Most of it is the
spine or the evaluator interface:

| What the IxVM workstream needs | Where in this plan |
| --- | --- |
| SrcEval as a normative, versioned semantics with executable entry points (first deployment) | EV-1 |
| An image format with a deterministic producer and a round-trip theorem (first deployment) | EV-2 |
| The interfaces: BLAKE3 addresses, pinned identities from the role binding, readback to an Ixon expression, budgets as constants, universe profiles (first deployment) | EV-2; the role-bound envelope and role table read in SP-B (implemented) |
| SrcEval step counts for its first measurement | EV-0 |
| The front-end clauses as a checklist another program can run, with the irrelevance clause stated against the kernel's typing judgement | the faithfulness premise: SP-0 defines the clauses (the irrelevance clause and its converse against the kernel's typing), the kernel circuit's lowering claim checks them; the [faithfulness](evaluator-interface.md#faithfulness) checklist |
| Adequacy on a fragment with `Decidable` and proof fields, test `decide (fib 20 = 6765)` (its critical path) | SP-A, SP-1 |
| `eqn` and `csimp` entries valid in the model, stated once for both sides | SP-0 |
| The `Nat` primitives' meaning lemmas | SP-0; the data primitives' in Phase 3 and SP-2 |
| Determinism of the producer, the table selection and the annotator | EV-2 |
| Stored-value opaques kept separate from recorded interpretations | DC-2 |
| Certificates for optimised images; a lowering to formal Aiur; kernel-evaluable checking paths | later: [evaluator interface](evaluator-interface.md#later), AR-2, D17 |

It does not need the x86 back end, linking or the trust ledger, the compile
claim, stage L or P8.

### Phases

| Phase | Deliverable | Closes with | State | Adds to the spine | Gives the Aiur routes |
| --- | --- | --- | --- | --- | --- |
| 0 | Reset and foundations: first gates back, the ix `eq_def` export, design notes (not kept in this repository), a declarative x86 instruction table with compact encodings, hardware-differential and decoder gates, first-wave fixtures, census, Lean/Clang measurement rows | — | Done | — | — |
| 1 | Scalar vertical slice from real Lean source to certified ELF, with register allocation, loops and recursion (`fib`, `for` loops, Ackermann, `tak`, `gcd`) | K1 | Done: K1 certified relative to SrcEval | the first fragment's x86 exit test | — |
| 1.5 | Reviewed resource checking, address-bound equation/profile selection and contract transport; assess upstream certification before the final producer repin | Existing K1 and annotated/plain fixtures | In progress | — | — |
| 2 | Heap and closures: general RC (scalar fields, large objects, static objects, reset/reuse, `unique`/`borrow`, inline fast paths, the Own checker); P8 defunctionalisation; P5/P6 when measured | K0 (real `List.reverse`), K2 (lists), K3 (trees); `Decline.composeClosure` | In progress: the bounded plain-RC route and the `List.reverse` regression are implemented; P8 is on the compile and recheck path (the closures step), with `Decline.composeClosure` compiled and certified | nothing: every item is below SrcEval | nothing: the evaluator has closures natively and its own memory |
| 3 | Data and interface: fixed-width integers and small `Int`, arrays and byte arrays with in-place update, strings, interpreted opaques, P9; the byte ABI, the claim's ABI descriptor, state-machine roots | K4 | Planned | new primitives and string rules: a new contract and image version, one meaning lemma each, new adequacy cases | the same meaning lemmas, stated at the SrcEval level, for a write-once-memory implementation |
| 4 | Bignums: the limb library compiled by IxCC; large `Int` | K5 | Planned | nothing above SrcEval (`Nat` is exact there) | a shared `Nat` specification with the evaluator's in-circuit `Nat` |
| 5 | Scale and usability: input-relative budgets, linear-time recheck passes, per-function rechecking and caching, diagnostics, library census | K6; a closure of at least 2,000 definitions | Planned | — | larger images |

The 2026-11-09 table's track C (CD1–CD4) is replaced by the spine; CD2 and CD3
are side products in the milestone table.

### Benchmark rungs

| Rung | Programs | State |
| --- | --- | --- |
| K0 | Real `List.reverse` on `List Nat` | Runs through the bounded plain-RC route ([`fixtures/rc/real-source`](../fixtures/rc/real-source/README.md)); final producer refreeze open |
| K1 | `fib`, `sum-loop`, `ackermann`, `tak`, `gcd`, and `collatz`, `prime-count`, `even-odd`, `sfib` | Certified and measured |
| K2 | `nqueens`, `queue`, `reverse`, `foldl`, `list-qsort` | Sources and twins in [`benchmarks/fixtures`](../benchmarks/fixtures/README.md); no frozen Ixon closures yet |
| K3 | `rbmap`, `rbmap_checkpoint`, `const_fold`, `binarytrees` (total), `rbmap_fbip` with its annotated twin | As K2 |
| K4 | `deriv` (`String`), `qsort` (`UInt32`, `Array`), `unionfind` (`Array`, `StateT`), `blake3` (`Blake3.Pure`), `hashmap`, `nat_repr` | Not started |
| K5 | factorial, big Fibonacci, π digits, e digits | Not started |
| K6 | `liasolver`, `parser`, a subset of the certified kernel (`Ix.Kernel.Level` first) | Not started |

**Performance targets** are provisional and frozen per rung after first
data:
- K1: geomean ≤ 1.3× Lean → Clang and ≤ 1.5× idiomatic C at `-O2`;
- K2/K3 plain sources: ≤ 1.2× Lean → Clang;
- annotated twins: ≤ 1.0×;
- K4: ≤ 1.3×;
- K5 and K6: set after the first measurements;
- no row above 2×;
- ≤ 10 s to compile and check each suite program.

### Phase 2: heap and closures

- **Heap completion** ([DR1](data-and-roots-design.md#dr1-heap-completion)):
  scalar fields, constructors beyond 31 fields and large objects, static
  objects, reset/reuse with a uniqueness test, static reuse from `unique`
  contracts, borrowed parameters, inline RC fast paths, and the proved Own
  checker with the canonical plain producer as its fallback. Stage 1
  (general cell layouts, the uniqueness test, the in-place reuse lemmas)
  done: the pipeline emits the general runtime (`Rt.Rc.Gen`: allocation by
  layout, `Gen.dec` as the one release) for constructors of 1 to 254
  scanned fields, within +1.6 % of the bounded route's executed
  instructions on every measured program; reuse of a unique cell in place
  is proved to keep the heap invariant (`inPlace_ready`,
  [DR1](data-and-roots-design.md#in-place-reuse)), but no pass emits a
  reuse yet (stage 4, after stage 2's placement). Stage 2 (the proved Own
  checker), first landing: the checker `Own.Plain.checkOwned` over today's
  syntax with refinement, reclamation and canonical acceptance proved, as a
  library that nothing in production calls
  ([DR1, "The ownership checker"](data-and-roots-design.md#the-ownership-checker));
  next, the Cfg activation layer restated over its typing context and the
  recheck switched to it, then a liveness placement. **Open for stage 3**
  (inline fast paths): the general release executes up to 3 Lir steps (4
  x86 instructions) more per freed cell than the bounded route's for
  cells of fewer than three scanned fields, fewer for four or more (lists
  +3.2 % steps, +4.8 % instructions; chains of one-field cells +10.5 %,
  +10.9 %), from a branch for scalar-only cells and a reload of the class
  byte; two cheaper variants (`asc`, `desc`) are measured but not proved
  ([DR1, "The general release's cost"](data-and-roots-design.md#the-general-releases-cost)).
- **P8** ([closures design](closures-design.md)): defunctionalisation,
  dispatchers, the known-dispatch shrink rule, `Anf.Defun.correct`. Started
  at the owner's request (2026-11-10) for the native route's generality,
  although the evaluator route does not need it. On the compile and recheck
  path as the closures step, with each root entered at its declared
  parameter count; proved and composed into the end-to-end theorems on the
  inputs they cover ([closures design](closures-design.md#proof-obligation)).
  Open: the known-dispatch shrink rule (and the shrink after the pass that
  waits for it), P9, and dispatchers past about 510 closure keys.
- **P5 and P6** only where K2/K3 measurements show the need.
- *For the spine:* nothing. Every item is below SrcEval.
- *For the Aiur routes:* nothing; the evaluator has closures natively and its
  own memory.
- *Depends on:* Phase 1.5's final producer for the K0 refreeze.
- *Exit:* K0 refrozen with the final producer; K2 and K3 frozen, compiled
  under `--rc auto` and certified, measured against their targets, with the
  annotated twins against the plain sources; `Decline.composeClosure` and the
  new higher-order corpus roots of the closures design compile and certify.

### Phase 3: data and interface

- **Fixed width and small `Int`** ([DR2](data-and-roots-design.md#dr2-fixed-width-integers-and-int)),
  **arrays and byte arrays** ([DR3](data-and-roots-design.md#dr3-arrays-and-byte-arrays)),
  **strings** ([DR4](data-and-roots-design.md#dr4-strings)),
  **library structures and interpreted opaques** ([DR5](data-and-roots-design.md#dr5-library-structures-and-opaque-constants)).
- **Roots**: the byte ABI ([DR6](data-and-roots-design.md#dr6-structured-roots-and-the-byte-abi)),
  the claim's ABI descriptor ([DR7](data-and-roots-design.md#dr7-what-the-compile-claim-binds)),
  monomorphic roots ([DR8](data-and-roots-design.md#dr8-universe-polymorphism-and-type-parameters-at-roots)),
  state-machine roots ([DR9](data-and-roots-design.md#dr9-effects-and-io)).
- **P9** and the flow oracle, if K4 shows dispatch cost.
- *For the spine:* the new primitives and string rules are new SrcEval rules,
  so a new version of the [evaluator contract](evaluator-interface.md) and the
  image format, one meaning lemma per primitive (a conservativity lemma
  against its reference body on `toList`), and new adequacy cases (SP-2). The
  meaning lemmas are stated at the SrcEval level, independently of the x86
  heap invariant.
- *For the Aiur routes:* the same meaning lemmas, on which a write-once-memory
  implementation of arrays and strings can rest as the x86 heap implementation
  does. Without them an evaluator runs the reference bodies, which are
  quadratic.
- *Depends on:* Phase 2's scalar fields, large objects and uniqueness test;
  P8 for library code over dictionaries.
- *Exit:* K4 compiles, certifies and is measured; BLAKE3 passes its
  known-answer vectors; a `ByteArray → ByteArray` root round-trips through
  the driver; a state-machine session of 1,000 calls passes.

### Phase 4: bignums

- The limb library and the bignum representation ([bignum design](bignum-design.md)).
- *For the spine:* nothing above SrcEval, where `Nat` is already exact.
- *For the Aiur routes:* the evaluator has its own in-circuit `Nat`
  arithmetic over its field; the library shares its specification with it,
  and where possible its algorithms' proofs, rather than duplicating them.
- *Depends on:* DR1–DR4; a proof route for the library's layer 3 (stage L, or
  an explicit ledger assumption until then, as the design says).
- *Exit:* K5 compiles, certifies and matches Lean; `natOverflow` is retired
  with its gate map; the library theorems are fenced.

### Phase 5: scale and usability

- [Scale and usability](compiler-design.md#scale-and-usability).
- *For the spine:* larger fragments and closures; the grounded theorem's
  composition per function if per-function rechecking lands.
- *Depends on:* nothing for budgets, linear passes and diagnostics;
  per-function certificates for incremental rechecking.
- *Exit:* K6 compiles and certifies; a closure of at least 2,000 definitions
  compiles and rechecks with no budget refusal within a compile-time target
  set after its first measurement; the library census is published.

### Hardening

Soundness against a dishonest certificate is what the theorems give once the
spine removes the `GoesWrong` escape; resource bounds for the verifier are a
separate property, planned in the [hardening design](hardening-design.md):
HD-0 (a closure-wide typing budget and a fuzzing gate) now, HD-1 (typing off
the verifier path) with SP-0, HD-2 (one work budget and a total-work theorem)
and HD-3 (no recursion over input-sized data) after it. On the proof-system
routes a hostile input costs the prover, not the verifier. IxCK's typing core
was exponential on certain chains of `let` (fixed in the kernel: the cause was
its universe levels), and still is on some universe-level comparisons (the
comparison is coNP-hard for levels with `imax`); with the switch IxCC's
verifier runs IxCK itself, so the kernel's planned call budget in that
comparison is that verifier's guard.

A known crash on hostile input remains (2026-11-12; HD-3's class). The
envelope decodes every record with the kernel package's canonical decoder
(`Ixon.Canonical.deConstant`) before any depth bound runs, and that decoder
recurses natively on an expression's nesting: a record of unshared nesting
within the 1 MiB record budget aborts `ixcc compile` and `ixcc check-cert`
with a stack overflow, at about 30,000 levels on a 2 MiB stack and 100,000 on
8 MiB (measured with `LEAN_STACK_SIZE_KB`; on this branch and on the tip
before it alike), whether or not any root reaches the record. The kernel's
own byte entry decodes the same way. The fix belongs to the kernel package
(a depth limit inside its decoder) or to the envelope (a scan of the bytes
for nesting depth before decoding); neither is made yet. The envelope's depth
bound (`V3.withinKernelDepth`) limits the records as stored, after that
decoder, and not the terms the kernel builds while typing them.

### Resource soundness

Usage (`0 1 &`), ownership (`!`) and locality (`~`, `let borrow`)
annotations are checked today by ix's resource checker, an executable
analysis with no stated semantics and no soundness theorem; the kernel's model
reads no contract; no IxCC theorem takes the checker's acceptance as a
premise. IxCC re-checks erasure itself and gives the other annotations no
run-time meaning yet, so nothing compiled depends on them. The owner decided
(2026-11-14) that source annotations are untrusted hints, verified by IxCC's
own ownership checker wherever the compiler acts on them, and that resource
soundness is a theorem of its own about an instrumented source evaluator
([resource soundness design](resource-soundness-design.md)).

| Id | Content | Depends on | Exit test | Size [estimate] | State |
| --- | --- | --- | --- | --- | --- |
| RE-0 | Close the confirmed hole: result contracts re-labelled through a theorem the checker did not analyse and a cast | — | the relabelling programs refused, as regression tests | small | Done: the checker types theorem proofs and erased terms with contracts ([resource soundness](resource-soundness-design.md)) |
| RE-1 | IxCC's ownership checker verifies written unique and borrow contracts at both ends (a unique parameter at every call, a unique result at every return, a borrow where it is used); in-place update only on verified uniqueness | Phase 2's ownership checker (DR1) | the relabelling programs get no in-place update even with the hole re-opened; annotated K2/K3 twins verified | 2–4k lines beyond the checker itself | Planned (Phase 2) |
| RE-2 | An instrumented source evaluator (reference counts, regions, a use counter per binding) that refines SrcEval; a resource checker on the Src program actually evaluated; the property of each annotation, on a first-order fragment | EV-1 | the refinement and the properties fenced; verdicts compared with ix's checker on the ownership suite | 8–20k lines | Planned |
| RE-3 | Widening: closures as cells, eliminators, recursion through equations, locality with tail calls | RE-2; P8 | per item | per item | Planned |

*Depends on:* Phase 2 for RE-1; the evaluator contract (EV-1) for RE-2, which
instruments it and checks the same Src program the spine grounds; not on the
spine's adequacy work. For a source-level statement to survive the kernel's
conversion, result contracts must become part of a type's identity, as input
contracts already are: a decision for the kernel's owners (DO-24). *For the
native route:* in-place update, elided reference counting and stack allocation
only where RE-1 verified. *For the evaluator route:* write-once memory has
nothing to optimise; the annotations mean something there only through RE-2.

**No end-to-end test of contract-annotated recursive programs (since
2026-11-11).** IxCC's path for them is: contracts written in the source, a
resource context in the equations sidecar (the profile and the checked
equation pairs of the annotated recursive definitions), the table selecting
each annotated equation only against its checked pair, and the producer
choosing plain RC or zero RC accordingly. No committed input takes that path:
this repository's `ix compile` has never written a resource context or checked
equation pairs (the producer that did is on the unmerged branch
`jcb/usage-ownership`, preserved as
`origin/jcb/compilatrix-resource-wip-2026-10-11`), so
neither an annotated recursive fixture nor the dated one it replaced (an
earlier producer's, unbound, which the kernel front end refuses) can be
produced; `ix` refuses OS-04's annotated `len` at its resource admission. What
still covers the pieces: the resource binding's checks and refusals on
synthetic contexts (`tests-src`, `tests-own --only resource-records`), the
resource checker on the role-bound `OS16-plain` closure (`tests-ixon-v3`), the
non-recursive annotated fixtures through every Own level (`tests-own`), and
the refusal tests with contracts written into programs in memory
(`tests-pipeline`'s OS16-contract part, `rc-runtime`'s mixed-contract case),
whose recheck-path replays still run. Production code that no committed input
reaches: the annotated branch of `Src.Table.equationBody` (with
`Src.Resource.requirePair`), `Src.Resource.validateContext` and the
checked-pair loop of `Src.Resource.selected` (a program with a resource
context), and the reading of a present resource profile and checked pairs in
`Src.Hints.resourceOfJson`; the producer's zero-RC choice on a heap program
whose written contracts allow it is exercised only on programs built in
memory. What would make the test possible: `ix compile` writing a resource
context (a profile option and the checked pairs in its sidecar), then a
role-bound annotated recursive fixture in the ownership family.

### Standalone executables

Decided by the owner (2026-11-14): standalone executables are a target, with
no C driver; the start-up logic is self-hosted. Until X1 a compiled object ran
only inside a C runtime driver (364 lines of C, linked by the system linker,
on the C library), modelled by the ledger assumption
`x86-phase1-runtime-driver-model`; X0 and X1 replaced it with executables IxCC
writes. The certified program stays pure; IxCC
writes a static executable containing the object's text byte for byte, a small
shell written as typed x86 in Lean and encoded by IxCC's own encoder, and a
zero-filled segment for the stack and the region; the shell establishes the
driver contract from the fixed layout. Effects come in stages over one
platform interface (arguments, write, read, exit, clock), first as requests a
state-machine root returns as data, later as calls to platform procedures
treated as traced events; the system-call instruction lives only in platform
code, never in compiled program text, so the same program text can run as a
Linux process or under the IxOS tender
([standalone executables design](standalone-executables-design.md)).

| Id | Content | Depends on | Exit test | Size [estimate] | State |
| --- | --- | --- | --- | --- | --- |
| X0 | `ixcc compile --exe` for `Nat` roots (and results without fields): executable writer and checker, typed-x86 shell with the system call outside the program table, static layout with the driver contract proved; the shell ledgered (`x86-linux-exe-shell`). The per-call registers in the driver model move to X0-P | — | every corpus root of the fragment as an executable agrees with the manifest, SrcEval, ByteEval and the C driver, under a seccomp filter, with only `prctl`, `seccomp`, `write` and `exit` | 2–3.5k lines; 3–6 weeks (measured: 1.5k lines with tests) | Implemented ([as implemented](standalone-executables-design.md#x0-as-implemented)) |
| X0-P | The shell proved; a return address and register file per call in `X86.Driver`; the `Nat` executable theorem; the driver-model assumption retired for executables | X0 | the theorem fenced | 3–6k lines; 2–4 months | Implemented for X2's machine shell: the shell theorem (`shell_sound`) and the executable theorems (`machine_exe_sound`, `Rc.machine_exe_sound`) fenced, against three platform specifications (the loader's post-state, the system calls, the processor, which promises nothing where the byte machine does not say what the processor does), a memory fault or divide error ending the process, and the environment they describe (no tracer, no inherited seccomp filter or supervisor, no outside writer, one thread); safety only, faults allowed anywhere; `--exe`'s parsing shell still ledgered ([design](standalone-executables-design.md#x0-p-the-shell-proved)) |
| X1 | The redefined XB-1 and IxOS-0: IxCC-written test executables replace the C runtime driver in every native gate, out of process, with no trampoline and no C | X0 | the native suites pass with the C driver off the execution path and no C compiler in their inputs | 1–2k lines; 2–4 weeks after X0 | Implemented ([as implemented](standalone-executables-design.md#x1-as-implemented)): the C drivers are deleted; no gate runs a compiled program through C |
| X1b | No C at all: the four remaining C test harnesses (linker acceptance of relocatable objects, unwinding, the processor differential) replaced by objects and executables IxCC writes; no C source in the tree and no C compiler in any check's inputs (decided 2026-11-11; [what each needs](standalone-executables-design.md#the-c-drivers-removed)) | X1 | the `x86-elf-object` and `x86-hardware` checks pass with no C compiler in their inputs, with the same assertions | not estimated | Planned, not urgent |
| X2 | Numeric state machines: a generic request shell, parsing and rendering in Lean, the session theorem on `Nat` states | X0 (X0-P for the proof) | a 1,000-call session against Lean's interpreter; the theorem fenced | 2–4k lines | Implemented: `ixcc compile --exe --machine`, the `IxccExe` library, `fib` end to end, the session theorem fenced over the linked-object model, sessions of more than 1,400 calls agreeing with Lean's interpreter ([design](standalone-executables-design.md#x2-as-implemented)) |
| X3 | Batch byte executables: arguments and input bytes in, output bytes and an exit code out | Phase 3 (DR2, DR3, DR6) | byte-identical to Lean-compiled executables over a corpus | 2–4k lines beyond the DR items | Planned |
| X4 | Interactive executables: state-machine roots with heap states; platform interface version 1; a seccomp filter of exactly it | DR1, DR6, DR9 (a) | a 1,000-call session; the state-machine theorem fenced | 4–8k lines | Planned |
| X5 | Lean `main : IO` over a recorded subset: traced events, platform calls, interpretations of `IO`, start-up logic in Lean | X4, DR2–DR5, P8, DC-2 | the benchmark fixtures' `main` functions compile unchanged and print what Lean's executables print | 10–25k lines (weak basis) | Research |
| X6 | The platform interface implemented by the IxOS tender: one program text, two platforms | X4, IxOS-1 | the same outputs on both | with IxOS-2 | Planned |

*Depends on:* nothing for X0 and X1; Phase 3 for X3; DR1, DR6 and DR9 for X4;
the interpretation question (DC-2) and P8 for X5. *Composes with the spine:*
the executable's statement replaces "the linked object returns `w`" by "the
executable exits after writing `w`", and the driver model by the loader's
post-state and the platform's system-call model. *X1, done:* every native suite
ran both the C driver and the test executables, line by line, with no
disagreement; then the C drivers, their pins and the C link paths went.

*A possible later hardening of the machine shell (not part of X0-P, not
planned):* an instruction certain to fault right after the `exit` block's
`syscall` (today the block jumps back to itself), so that an `exit` that
returns (under a tracer or an inherited seccomp filter, which the shell
proof's environment assumption excludes) ends the trace instead of repeating
the call. It would change the shell's bytes, so it needs its own proof
update and artifact comparison.

### Repository and landing

- **RL-1, fixtures from this tree.** Every committed fixture is regenerated
  by this repository's `ix`, role-bound, with no external producer
  provenance (done 2026-11-11). One command does it, `tools/regenerate.sh`
  ([corpus](corpus.md), "Refreezing"), and `tools/regenerate.sh --check`
  says whether the committed fixtures are current and self-contained (no
  commit or path outside the repository cited); it is run once more on the
  final merged state before the merge (#678 changes the role table, so every
  closure changes again). The closures grew: the selection adds recursors,
  whole logical units and checker support (DO-20); equation counts grew; no
  source, root, case, value or decline changed, except the boundary family's
  field limit, restated at 49/50 fields (a defect since removed: "What
  ingress reads" above; the family is back at 254/255 fields). The typing
  bundles went with the erased checker, and IxCC's catalog support is retired
  (DO-16). The unbound flag, with no user left, is removed: `ix compile` writes
  the role-bound envelope only, as on `main`.
- **RL-2, the certified-IxVM work.** It has priority and lands first; this
  branch adapts to whatever it does: a second merge of `main`, the rename
  pass, re-recorded digests, inventories and ledger, and the move to its formal
  Aiur package as the Aiur target.
- **RL-3, the legacy Aiur model.** `IxCC/Aiur` (about 5.8k lines) and the
  vendored snapshot ([`Vendor/upstream.json`](../IxCC/Vendor/upstream.json),
  about 3.5k) model a bytecode that neither Aiur route uses; the formal Aiur
  package supersedes or contradicts all of it. Frozen now; retired with RL-2
  (DO-14): its tests, fences and tools, its fixtures, the `ixcc-aiur` check and
  its entry in the ledger's required checks, the ledger's three Aiur scopes and
  their pins, the build-graph inventories and the [legacy docs](aiur-backend.md).
  The formal Aiur package is self-contained (Mathlib only, at the same
  toolchain), so a later per-program backend (AR-2) would be a separate package
  depending on it and on IxCC.
- **RL-4, landing.** No pull request for this branch until the certified-IxVM
  work finalizes. The branch is squashed when it lands, so nothing may depend
  on the commit hashes of its history.

### Flagship targets

**The IxOS flagship: the monitor and driver compiled through `ixcc`.** IxOS runs
admitted programs as software-isolated processes (SIPs) in Ring 0 and its
monitor is itself Lean code compiled by IxCC. The monitor is a state-machine
root (DR9), and a small ledgered *tender* performs privileged operations and
the calls into SIP entries, because compiled code has no indirect calls
(decision 4 of 2026-11-10; D20). IxOS-0 to IxOS-2 do not depend on the spine;
IxOS-3 compiles the verifier as SP-0 leaves it; IxOS-4 depends on SP-1 (or CD2).

| Step | Content | Prerequisites | Exit | State |
| --- | --- | --- | --- | --- |
| IxOS-0 | The platform interface and its Linux implementation as the reference host, with no in-process trampoline and no C: X0 and X1 of [standalone executables](#standalone-executables), extended by X4; the tender's implementation of the interface moves to IxOS-2 (X6). Redefined on 2026-11-14 (DO-34, also XB-1) from a host loader that mapped an object and called its entries through a ledgered trampoline in place of linking the C runtime driver | none | as X1 | In progress (X0 and X1 implemented; X4 planned) |
| IxOS-1 | Fuel metering in prologues and at back edges with a new resource status; Ring-0 frame preservation on every outcome, not only on return | none | Fenced theorems; the session gate with fuel exhaustion | Planned |
| IxOS-2 | A minimal monitor: SIP table, region allocation, request dispatch to the tender, admission by claim digest and external evidence | Phase 2 (P8, DR1), DR2, DR3, DR6, DR9 | The monitor's `step` certified; a host-harness session of SIP calls | Planned |
| IxOS-3 | Admission inside the monitor: `CompileClaim.verifyBytes` compiled by IxCC | Phases 2–5 (bignums for 256-bit address comparisons, strings for certificate parsing, scale for the checker's closure); after SP-0, the verifier it compiles takes kernel acceptance as a premise | An IxCC-compiled `check-cert` agrees with the Lean-compiled one on every committed certificate and the hostile-input regressions | Planned |
| IxOS-4 | Certification: confinement without the source-safety premise (SP-1's progress once its fragment covers the monitor, or CD2); CD3 on `step` and on `verifyBytes` | SP-1 or CD2; CD3 | "Admitted by the compiled monitor ⇒ accepted by the Lean verifier" as a theorem | Research |

**The kernel flagship: the certified kernel compiled through `ixcc`** (native
x86). Its steps do not depend on the spine except IxCK-3; whether this route
also helps the IxVM workstream is not part of this plan.

| Step | Content | Prerequisites | Exit | State |
| --- | --- | --- | --- | --- |
| IxCK-1 | `Ix.Kernel.Level` (`IxCK/Kernel/Level.lean`: fuelled, mutually recursive level comparison using `Int` offsets) | Phase 2, DR2 | Compiles, certifies, and agrees with the Lean-compiled functions on generated level pairs | Planned |
| IxCK-2 | The checker, through the reference fold `checkDeclsPure` or the cached fold: records of closures, monad polymorphism, `HashMap`, `Array`, `ByteArray`, `UInt64`, `USize`, `Int`, strings, exact `Nat` | Phases 2–5; DR5's interpretation table, or IxCK without `mixHash` and `getNumBits` | Differential agreement with Lean-compiled IxCK on its smoke environment and claim fixtures; certified relative to SrcEval | Planned |
| IxCK-3 | "The object accepts ⇒ `checkDecls` accepts" as a Lean theorem, then IxCK's soundness | CD3 at IxCK's scale, or SP-1 widened to IxCK's closure plus a reflection step with no design | The composed theorem fenced | Research |

### Dependencies in brief

```text
SP-B → SP-0 → SP-1 → SP-2                  (the spine; SP-A in parallel, gates SP-1)
SP-B → SP-N (the kernel front end, in progress); SP-0 → SP-N's statement
premises (i), (ii): discharged by IxVM proofs (external) or by SP-N
EV-0;  EV-1 → EV-2                         (no dependencies; first)
EV-1, EV-2 → AR-1 deployment (IxVM side);  SP-0, SP-1 → AR-1 proofs
SP-N → HD-1;  SP-0 → HD-2;  HD-0, HD-3: none
SP-1 → the x86 and Aiur grounded statements
Phase 1.5 → Phase 2 → Phase 3 → Phase 4;  Phase 3 → SP-2 (data primitives)
CD2 → AR-2, IxOS-4;  SP-0 → CD3 → bignum layer 3, IxOS-4, IxCK-3
Phase 2, Phase 3 → IxOS-2;  Phase 4, Phase 5 → IxOS-3, IxCK-2
RL-1 phase 2, RL-2 → RL-4;  RL-2 → RL-3
IxOS-0 (= XB-1), IxOS-1, XB-2: no prerequisites
```

### Phase 1.5 priorities after the certification work

The upstream `jcb/ix-certify-compile` revision inspected on October 8 (a
revision outside this repository's history) provides several distinct
certification interfaces in `Ix/CompileCert`:

| Route | Established interface | Remaining boundary |
| --- | --- | --- |
| W (`checkIndexed_sound`) | Exact admitted bytes correspond to independent source exports, with closed source, name-map and whole-block/group coverage | Syntactic association alone does not establish model pullback |
| W+ (`checkIndexed'_sound`, `model_equations`, `model_statement`) | Changed declarations meet checked statement/equation obligations | Equation satisfaction alone does not establish a unique denotation or changed-block semantics |
| S (`StrongCone.sound`) | For direct/raw cones, every strong target model induces a strong installed-source model with annotation/value pullback | Source normalization, projection receipts and the connection to SrcEval remain explicit |
| S+a (`StrongCone'.sound`) | For supported changed-value cones, every strong target model induces a public installed-source value model, value pullback, capability laws and universal rule simulation | Excludes changed blocks, image recursors and type-row cases; does not supply the full annotation, tower or native-Nat model |

These are per-input certificates with their stated premises. Upstream's full
compiler proof through L4 and broader S coverage remain unfinished. Its export
erases Lean metadata/binder information, so these results do not certify the
resource contracts consumed here. The production dependency remains the
codec-only pin documented in [Ixon v4](ixon-v4.md).

The semantic statements quantify a set-theory model. Host Lean-environment
capture, the intended export reading, accepted projection-lowering witnesses
and correspondence to executed runtime remain explicit trust boundaries.

1. **Reconcile the candidate before integration.** Record the exact source
   revision, binary, libraries, toolchain, profiles, source cone, map, support
   rows and artifact bytes. The inspected upstream working copy is older than
   its bookmark; later status reports are not evidence about those checked-out
   files. Keep compiler-output changes separate from checker-only changes.
2. **Run a bounded certification pilot.** Exercise a consumer-relevant cone
   through direct/raw S and, separately, changed-value S+a with its explicit
   `--strong-changed` option. Check the exact theorem endpoint, a valid neighbor,
   and corrupted map/type/value/support data; retain unsupported outcomes.
   Use a separate validation target so the full kernel and its tests do not
   enter the production codec dependency. This gates adoption of certification
   interfaces; checker-only improvements retain their existing acceptance gates.
3. **Finish the existing resource and consumer gates.** Validate the selected
   500,000-step/depth-256 limits, all cast-bypass controls, Lean/Rust parity,
   equation/profile bindings, and contract transport (D16), including the check
   that an `eqn` entry does not drop contracts. W/S acceptance cannot replace
   these checks. Reassess the stalled engine against the selected upstream
   interfaces before choosing another optimization experiment.
4. **Review, freeze and validate the combined result.** Perform the final
   producer review, reproducible fixture refreeze, verdict review and complete
   consumer proof/trust/Nix checks. Checker-only changes retain the existing
   unannotated bytes; canonicalization/repacking changes require their own
   recorded refreeze with source roots, oracle values and step counts checked.
5. **Compare the semantic proof routes using the pilot.** The kernel-model
   route (stage K) and per-program Lean theorem route (stage L) can now be
   assessed against concrete upstream endpoints. Neither is selected or
   complete; both still need a bridge from the admitted environment, selected
   equations and relevant contracts to SrcEval. The first heap slice retains
   the current SrcEval-relative statement while that stronger bridge is open.

## Decisions

The register has four parts: the standing design decisions; decisions taken
with a date; decisions to confirm, where new information strains an earlier
one; and open decisions. The plan above is written with each *default*; the
owner settles the last two groups.

### Standing design decisions

| Decision | Summary |
| --- | --- |
| Source | Ixon (v4 since 2026-10-03) is the only input. Written contracts are lower bounds. The compiler honours them exactly, and may infer stronger guarantees (unique, local, borrowed, erased, one-shot) only when a proved checker certifies them; inferred facts never change Ixon bytes or addresses. |
| Semantic anchor | Stated against the source evaluator today; the goal is every model with the kernel's laws of IxCK's reading of the closure of the target and the table's theorems, with that model's existence and the image's faithfulness and typing as premises discharged by proofs, and an accepted equation theorem holding in the model so that the replacements it justifies are sound ([certification design](certification-design.md)). |
| Recursion and replacements | Compiled through kernel-checked equation theorems (`f.eq_def`, `@[csimp]`) collected in an unfolding table, not by recovering structure from `brecOn` or `WellFounded.fix`. `partial` and `unsafe` definitions are rejected; `implemented_by` compiles the reference body. |
| Erasure | An untrusted relevance annotation. `Recheck.front` decides it with the structural checker (`Relevance.check`, proved in `Relevance.Proof.check_sound`) and with `Relevance.checkCanonical`, which re-derives each position's class from the declaration types and refuses an irrelevant tag it cannot justify. The byte-level verifiers (`CompileClaim.verifyBytes`, `Ring0Sip.verifyBytes`, `ixcc check-cert`) also re-run the kernel annotator (`inp.kernel.annotateChecked`) on the ingested program with `cert.table` and require the certificate's annotation to equal its output (`Recheck.checkCanonicalRelevance`); the program-level verifiers and `Recheck.run` do not. Neither `annotate` nor `checkCanonical` has a theorem; under the premise architecture the relevance clause is checked against the kernel's typing judgement by whoever holds the types, and these checks stay as IxCC's early refusals. |
| Middle end | Clocked big-step semantics for functional IRs, with a fuel-indexed logical relation and heuristic-parametric passes. Forward simulations below. |
| Ownership | Untrusted RC, borrow and reuse passes; one proved ownership checker; fallback to plain RC. Ixon resource admission is a diagnostic gate, not a proof premise. |
| Backend | Rule-based selection with one lemma per rule; an untrusted linear-scan allocator with a proved validator; a private internal calling convention with SysV at exports; fall-through layout; the existing E1/E2/ELF. |
| x86 trust | A declarative instruction table. Hardware-differential and XED/LLVM-MC gates first; the Sail agreement proof later. |
| Runtime | Written in the compiler's own low-level IR and proved: an 8-byte header, single-threaded RC, size-class free lists, iterative free, tagged 63-bit small `Nat`. No C runtime and no GMP in the trusted base. |
| Profiles | One production profile. Instrumentation, cost and space results are optional layers outside the core relations. |
| Closures | Closed-world defunctionalisation in Anf (P8), after inlining and specialisation, with untrusted flow facts narrowing dispatch (P9). Fir stays first order; no closure objects, `pap`, `apply` or indirect calls ([closures design](closures-design.md)). |
| Bignums | Decided by the owner on 2026-11-09: new Lean implementations of the standard multi-precision algorithms, each proved against `Nat` and compiled by IxCC; several references consulted, GMP for behaviour only ([bignum design](bignum-design.md)). |
| Roots and effects | Roots stay level-monomorphic; structured data crosses the boundary as bytes; interacting programs are state machines driven by a host ([data, roots and effects](data-and-roots-design.md)). |

### Decisions of 2026-11-10

The owner settled four questions this plan had left open. Decisions 1, 2 and 4
stand; decision 3 is contradicted by later analysis and is under review
(DC-1).

1. **Closures stay inside a program.** No closure crosses a program boundary
   (a SIP boundary included), and higher-order libraries are compiled into
   each program that uses them. Closed-world defunctionalisation is therefore
   complete for every program IxCC compiles, and no code-pointer closure
   representation is planned ([closures design](closures-design.md)).
2. **Claims may carry interpretations of opaque constants.** A compile claim
   may record a fixed meaning for an `@[extern]` opaque such as `mixHash` or
   `System.Platform.getNumBits`, so `Std.HashMap` compiles from its Lean
   definitions; the statement then holds relative to the recorded
   interpretation ([DR5](data-and-roots-design.md#dr5-library-structures-and-opaque-constants)).
   Its reading against the grounded statement is DC-2.
3. **Stage L first** *(under review: DC-1; the plan is written with the
   kernel-model route leading).* The proof-producing translator (CD3) was to
   be built first and semantic adequacy (CD4) to be a research spike.
4. **No indirect calls in compiled code.** Every call and jump IxCC emits is
   direct; the IxOS monitor reaches SIP entries through a ledgered tender,
   and no indirect-call row is added to the instruction table. The closure
   design (dispatch by compare trees), the Ring-0 admission argument (no
   indirect branch rows) and the IxOS flagship rely on this
   ([Design decisions](compiler-design.md#design-decisions)).

The owner also decided, on the same day:
- **The goal**: end-to-end certification for both the Aiur and the x86 back
  ends, grounded in Ixon and IxCK; a generally useful compiler; hardened
  against dishonest input.
- **Self-contained documents**: tracked documents cite only what is in this
  repository; the pre-merge design notes are not imported.
- **The certified-IxVM work has priority**: it lands first, and this branch
  adapts to whatever it does; no pull request for this branch until it
  finalizes.
- **The squash**: this branch is squashed when it lands, so nothing may depend
  on the commit hashes of its history.
- **Fixtures from this tree**: every fixture is regenerated by this
  repository's `ix`, with no external producer provenance. This settles three
  questions of the regeneration work: the manifests' producer fields record
  that the producer is this repository's `ix` and keep the binary digest as a
  record, not a pin, with the regeneration gate as the provenance check (a
  `corpus` tool change); the Ixon v4 fixture package is adopted from this
  repository (six of its eleven files change, including the handoff
  environment, and the `tests-ixon-v3` and `check-ixon-v3` baselines move);
  and every commit-hash citation in a tracked file is replaced by a
  description (RL-1).
- **P8 now**: Phase 2's closures were started at the owner's request, for the
  native route's generality, although the evaluator route does not need them.

### Decisions of 2026-11-13 and 2026-11-14

- **Byte compatibility first** (2026-11-13): byte compatibility between IxCC
  and the kernel's artifacts is the spine's first milestone, and IxCC will read
  role-bound environments. IxCC reads them (implemented: the
  [byte contract](byte-contract.md) says which bytes and how they are
  identified), and `ix compile --unbound` was a bridge, removed once the
  fixtures were refrozen in the role-bound form (this settles DO-19; both done).
- **Root arity** (2026-11-13, fixed 2026-11-14): a root is called with
  exactly its declared parameter count, and the compiler makes its entry at
  that count; the end-to-end theorems are stated for inputs of exactly that
  count, and for every input of a program the closures step leaves unchanged.
- **Source annotations are untrusted hints** (2026-11-14): IxCC's own
  ownership checker, on IxCC's intermediate representation, is the soundness
  basis for anything the compiler does with ownership: a unique parameter is
  verified at every call and a unique result at every return, and a borrow and
  a local value are verified where they are used, as erasure is re-checked
  today. The source-level resource check stays as a front-end diagnostic. A
  source uniqueness annotation selects in-place update only through that
  verification, never by being trusted ([resource
  soundness](resource-soundness-design.md#layer-1-annotations-are-untrusted-hints-ixccs-ownership-checker-verifies-them)).
- **Resource soundness is its own theorem** (2026-11-14), with its own place in
  the certification plan; the kernel-model grounding cannot supply it, since
  the model sees no contracts. It is operational: for each annotation, a
  usage-soundness property of an instrumented source evaluator (a heap with
  reference counts, regions, and a use counter per binding), checked on the
  program actually evaluated or compiled, starting with a first-order
  fragment. On the route that runs the evaluator in a proof system, which has
  no ownership level below it, this theorem is what gives annotations a
  meaning ([resource soundness](resource-soundness-design.md#layer-2-a-source-level-resource-theorem)).

### Further decisions of 2026-11-14

- **Standalone executables**: a target, with no C driver; "we should be able
  to self-host that logic" ([standalone
  executables](standalone-executables-design.md); the track is
  [above](#standalone-executables)).
- **Exact root arity**: a root is called with exactly its declared number of
  parameters, and the compiler generates the entry at that arity, as Lean's
  own compiler does for exported functions. This supersedes "no longer than"
  of 2026-11-13 and settles DO-23.
- **The certified kernel as IxCC's type checker**: IxCC's erased type checker
  is to be replaced by the certified kernel in both the producer (the
  relevance annotator, early diagnostics) and the native verifier path, with
  an enumerated ledger exception for the kernel's `implemented_by` sites, as
  the native-discharge milestone (SP-N). This settles DC-4, and the checker's
  part of DC-3: the checker is replaced rather than kept in untrusted
  production, so there is one type checker, the proved one. Its design is a
  separate kernel front-end document. Since the switch's step 3 (2026-11-11)
  it is the only front end: every compile path's ingress is the kernel's
  acceptance, the per-claim typing flag is gone, and the erased checker is
  deleted (step 4).
- **The standalone-executables design**: accepted as proposed, which settles
  DO-28 to DO-36 as their defaults. "Self-host" means a pure certified program
  plus a small machine-level layer that IxCC generates and later proves, never
  C; a static layout; requests returned as data first and platform calls
  later, over one platform interface; the system-call instruction only in
  platform code; seccomp self-confinement on; an executable claim binds the
  executable's hash, the platform and the shell version; XB-1 and IxOS-0 are
  redefined as executables replacing the C driver; numeric state machines
  before Phase 3; Lean `IO` through platform calls. The first executable
  milestone (X0) is implemented.

### The restatement of 2026-11-11

What the certified IxVM work's typing claims conclude (a model of the claimed
environment, not acceptance by a kernel entry; the closure of the claim's
seeds, not an artifact; the default role table only) made the first premise
the wrong shape. The plan above is restated on these lines
([certification design](certification-design.md#the-restatement-of-2026-11-11)).

**Settled by it** (follows from the facts, not a choice):
- the first premise is the existence of a model, with the laws, of the
  kernel's reading of the closure of the seeds; the seeds are the target and
  every theorem the unfolding table names;
- the pairing with an IxVM claim is by those seeds and the table, through one
  `checkEnv` claim in the default context, not by `(H, ρ)`; a `checkEnv` over
  a whole `ix compile` artifact is refused (it holds `partial` records), so it
  is never the pairing;
- IxCC's statements are over every public `Model` with the laws, not over the
  kernel's internal invariant;
- typing derivations of what the evaluator runs are part of the second premise
  (a model gives no typing for subterms);
- soundness and progress are separate obligations: the evaluator route needs
  soundness, the x86 claim both;
- images used to discharge a grounded claim carry no stored-value opaques
  (agreed with the IxVM side: the public model keeps no value for an opaque),
  which settles DC-2's stored-value part.

**Opened by it**: DO-37 to DO-41 below.

### The kernel front end's switch (2026-11-11)

- **The switch proceeds now.** IxCC's front end moves to the certified
  kernel on both the producer and the verifier path, and the erased checker
  is deleted ([the switch](kernel-front-end-design.md#the-switch)), without
  waiting for a work budget in the kernel's typing core. This replaces the
  working default that held the switch on that budget.
- **The kernel's blow-up on chains of `let` is fixed in the kernel package on
  this branch**, in parallel with the switch (KF-3). The fix has landed (the
  ∀ rule's universe level; 28 ms where it took 52 s at 30 `let`s). What
  stays exposed since the switch's step 3 is a closure whose universe-level
  comparison is exponential (it is coNP-hard for levels with `imax`; the
  kernel's level walks on shared levels are memoised), which can hold the
  byte-level verifiers as long as its author chooses; the planned guard is
  a call budget in the kernel's level comparison (KF-3;
  [resource bounds](kernel-front-end-design.md#resource-bounds),
  [hardening](hardening-design.md#external-dependencies)).
- **The fixtures were refrozen in the role-bound form** (RL-1 phase 2), and
  the switch's step 3 followed (the kernel admits only role-bound
  environments): the front end over the kernel is the only one; steps 4 and 5
  (the deletion, the ledger) are next.

What remains a working default, awaiting confirmation, is listed with the
[kernel front end's decisions](kernel-front-end-design.md#decisions): the
native check of the clauses (DO-6 (c)), the tiered entry and the artifact's
own prelude. The closure run for premise (i) (DO-37) was decided the same
day.

### Decisions to confirm

| Id | Question | Options | Default | Why | Cost to change later |
| --- | --- | --- | --- | --- | --- |
| DC-1 | The order of the certification routes (decision 3) | (a) stage L first, as decided; (b) the kernel-model route leads (SP-A, SP-1), stage L becomes a side product; (c) both at equal priority | (b) | Stage L relates the object to a host Lean function and does not ground anything in IxCK or apply to a term inside an environment; the IxVM workstream's critical path is adequacy | Low: stage L has not started; reverting later costs the spike's months |
| DC-2 | How decision 2 reads against the grounded statement | (a) interpretations allowed in compile claims as statements relative to the interpretation, kept separate in table and image from evaluation through a stored value (`opaqueByValue`), and both excluded from the grounded statement; the evaluator route refuses both for discharging axioms; (b) add an opaque value law to IxCK and state grounded results over models restricted to it; (c) no interpretations: targets avoid opaques | (a); its stored-value part settled 2026-11-11 (no stored-value opaques in a grounded image, agreed with the IxVM side) | IxCK's model keeps no value equation for opaques, so neither kind holds in every model with the laws; an evaluation axiom must hold in every model, so a relative statement cannot discharge one | Low now (nothing implemented); meanwhile code that reaches an allowlisted opaque (today `Lean.opaqueId`) cannot be discharged; (b) later restricts every grounded statement that uses it |
| DC-3 | IxCC's guarantees conditional on kernel acceptance supplied externally (an IxVM typing proof or a native IxCK run) and on faithfulness supplied by the party holding the kernel's reading, rather than on IxCC's own type checking; and then the per-claim typing flag and the erased type checker | (a) as stated, the flag removed from claims' meaning and the checker kept only in untrusted production (the relevance annotator, early diagnostics), off the verifier path; (b) as stated, the checker kept on the verifier path as an optional filter; (c) prove the erased checker sound instead | (a) for the guarantees; for the checker, **decided** 2026-11-14 under DC-4: replaced by the certified kernel, not kept in untrusted production | A soundness proof for 12,700 lines of checker costs about what IxCK's own verification cost, and acceptance is already proved for IxCK; typing dominates verification time (51.7 s of 51.8 s on the committed scalar closure) and is unbounded per closure | Medium: the byte-level Stage A re-derivation uses the checker's expressions and conversion, so retiring it means porting or dropping that check |
| DC-4 (decided 2026-11-14: (a)) | Does IxCC obtain type information (for the relevance annotator, `checkCanonical` and the byte-level re-derivation) by calling the certified kernel instead of its own erased checker? | (a) call IxCK and delete the erased checker; (b) keep the erased checker in untrusted production only (DC-3's default) | **Decided** (2026-11-14): (a), in the producer and on the native verifier path, with an enumerated ledger exception for the kernel's `implemented_by` sites; in progress within SP-N; until the switch the erased checker stays as untrusted production code | One type checker instead of two, and the proved one; (a) deletes the erased checker rather than merely moving it off the verifier path | Medium: IxCC's dependency on IxCK grows beyond its codec, and IxCK's typing cost (its blow-up on chains of `let`) enters the producer |

### Open decisions

| Id | Question | Options | Default | Why | Cost to change later |
| --- | --- | --- | --- | --- | --- |
| DO-1 | Will IxCC co-own the adequacy spike on the `Decidable` fragment, ahead of stage L, and who works on it? | IxCC owns; IxVM owns; co-own | Co-own, ahead of stage L: IxCC owns the SrcEval side and the relation, the IxVM workstream the IxCK model facts it needs, with people on both; the spike runs `fib`, then `decide (fib 10 = 55)` so that the `Decidable` case is tested early | Both workstreams' critical path; each holds half of the expertise | Low |
| DO-2 | Who owns the image format? | IxCC, IxVM reviewing; IxVM, IxCC reviewing | IxCC, as a module over `Src.Syntax` alone, versioned with SrcEval; the IxVM workstream reviews every version and owns the evaluator's reader | It serializes `Src.Program` and must change with it; a second reading of Src would diverge | Medium once images are in circuits: a format change is a new key's worth of work on the IxVM side |
| DO-3 | Can the relevance clause be stated against the kernel's typing judgement, for an external checker to discharge? | yes; no (consumers re-derive the annotation with IxCC's annotator, which must then be specified) | Yes, in both directions ([CD1](certification-design.md#cd1-the-front-end-theorem)) | The party with the types can decide it; IxCC's own classifier has no theorem | Low |
| DO-4 | Are SrcEval's `irr` decisions at concrete levels stable enough to freeze? | freeze version 1 now; wait for Phase 3 | Freeze version 1 for the Phase 1 fragment now; the mechanism is stable, the rule set is not: strings (E9), DR2's words and bounded-construction rule, DR3's arrays, DR5's interpretations and the stored-value opaque question (DC-2) come as later versions with a changelog | Nothing pending changes version 1's rules | Low: a version bump |
| DO-5 | Data primitives' meaning lemmas at the SrcEval level, independent of the x86 heap invariant? | yes; per implementation | Yes, in a module below the runtime (DR3 and DR4 already plan conservativity lemmas against reference bodies, relative to SrcEval) | One specification for the x86 heap and a write-once memory | Low |
| DO-6 | How is the image's faithfulness discharged, per route? | (a) the kernel circuit's lowering claim; (b) IxCC's ingress rebuilt on IxCK's reader, so one reading by construction; (c) a native check of the clauses against IxCK's reading | (a) on the evaluator route; on x86, (a) where the consumer aggregates with IxVM proofs, and on the native path (SP-N, in progress since the decision of 2026-11-14 to take type information from the kernel, DC-4) (c), the working default of the [kernel front end](kernel-front-end-design.md#decisions), awaiting the owner's confirmation; (b) was the earlier default. Since 2026-11-11, on every route the image is compared with the kernel reader's term (`let`s kept), and the premise includes typing derivations (DO-40) | (a) reuses what IxVM builds anyway. (b) and (c) both import IxCK's reader, widening IxCC's dependency on IxCK beyond its codec; given that, (b) leaves one reading on the verifier path where (c) keeps two and compares them; IxCC's own decoder stays in the untrusted producer | Medium: (b) rewrites the verifier's ingress over IxCK's regrouped blocks |
| DO-7 | Priority, given limited capacity and the certified-IxVM work first | — | RL-2 when that work lands; then SP-B; EV-0 to EV-2; SP-0 and SP-A; SP-1; Phase 2 continuing at reduced pace (P8 milestone 1, heap completion); HD-0; RL-1 phase 2 when its decisions are taken; Phases 3–5, CD2 and CD3 when a consumer needs them | The spine and the IxVM interface are the goal's critical path; Phase 2 serves the native route's breadth | Low: an ordering |
| DO-8 | Is per-program Aiur lowering on the plan before a key-derivation story exists? | schedule it; keep it designed and unscheduled | Unscheduled | A per-program key's provenance cannot be checked in a circuit today, so its claims would add per-program trust | Low |
| DO-9 | The first grounded fragment's exit test | evaluator form; x86 form; both | Both: `decide (fib 20 = 6765)` through SrcEval on its image, and the K1 `fib` compile claim, then every K1 root | One test per route over the same spine | Low |
| DO-10 | Does the metered verifier (HD-2) precede or follow the spine? | before SP-0; after SP-0 | HD-0 now; HD-1 with SP-N; HD-2 and HD-3 after SP-0 | SP-0 changes the verifier's front; the dominant unbounded cost (typing) leaves the verifier with it | Low |
| DO-11 | How the compile claim binds what composition needs | new claim fields (root, role table, image digest); a companion claim | New fields in the compile claim (the role table: implemented in SP-B, validator 7; the image digest with SP-0); the certificate stays unbound, documented as affecting meaning until SP-0's table lemmas and SP-1's progress hold. Since 2026-11-11 the pairing is by the seeds (the target and the theorems `D` names) and the table, so `D` is what makes the claim pair; `env` (`H`) and `roleTable` (`ρ`) stay, meaning what IxCC read, and no field changes before `D` joins (DO-41) | Composition by aggregation needs the addresses in one claim | Medium: the claim codec is shared with ix |
| DO-12 | What happens to `Models/KernelBridge`? | keep as a record; delete now; keep until SP-1 | Keep with its gate until SP-1, reuse its literal-denotation layer where useful, then remove | Its approach cannot reach recursion and is not the route | Low |
| DO-13 | May evaluation axioms be discharged by reductions Lean's kernel lacks (δ by accepted equation theorems)? | yes; no | Yes: SP-0's lemma (from `mem` and `eq_equality`, with the theorem a seed) makes it sound in every model with the laws; the IxVM workstream's rules now have such a rule (an equation's proof rewrites its left side) | SrcEval recurses through equation theorems; without this the evaluator route covers no well-founded recursion | Low for IxCC; it is the IxVM workstream's rule |
| DO-14 | The legacy Aiur model (`IxCC/Aiur`, about 5.8k lines; the vendored snapshot, about 3.5k) | retire; re-pin; keep | Retire when the certified-IxVM work lands (RL-3) | The formal Aiur package supersedes or contradicts every part of it; neither route uses its bytecode | Low: a deletion; the one idea worth keeping (memory functionality from the memory polynomials) goes to formal Aiur's owners as a note |
| DO-15 | IxCC's primitive table lacks this repository's `String.back` and has a `String.Legacy.back` that Lean 4.34.1 lacks | adopt this repository's table; keep IxCC's and retire the regeneration step | Adopt (follows from fixtures from this tree); moot once the certified kernel replaces the erased checker (DC-4, decided 2026-11-14) | One table, regenerable | Low |
| DO-16 | The catalog fixtures cannot be regenerated: this repository's assembler takes only role-bound members | keep frozen with the pin described; an IxCC-side assembler; regenerate after SP-B | **Retired** (2026-11-11, the kernel front end's step 4): IxCC's catalog support (the reader, the validator-1 admission, its four fences, the catalog step of `ixcc-ixon-v3`, the two frozen catalogs and their tests) is deleted. Validator 1 certified erased typing, which the deleted checker gave; ix retired validator 1 (its readers refuse it), and nothing outside IxCC's own tool, tests and frozen catalogs read it. Reading catalogs again means building against ix's current validator | No new assembler to maintain | Low |
| DO-17 | Does the fixture regeneration gate block CI? | blocking; a report | A report until this branch lands, blocking afterwards with the refreeze procedure documented (the certified-IxVM work lands first, so it is never blocked) | A blocking gate makes every `ix` change that alters these bytes refreeze IxCC in the same pull request | Low |
| DO-18 | Dated records whose producing commits are not in this repository (the historical annotated-recursion ownership records) | keep, described; retire | **Retired** (2026-11-11, the kernel front end's step 4): the records were unbound, which the kernel front end refuses, and this repository's `ix` refuses their source (OS-04) at its resource admission and writes no resource profile or checked pair, so no role-bound successor exists; what they tested is in the [CI coverage record](ci.md) | They were evidence for a retained refusal boundary; their reading (the erased checker, the earlier annotator and ingress) is deleted | Low |
| DO-19 | The unbound-envelope flag, or IxCC reading role-bound environments | — | **Closed** by the decision "byte compatibility first" (2026-11-13): IxCC reads role-bound envelopes (SP-B, implemented); `ix compile --unbound`, the committed fixtures' bridge, was removed once they were refrozen in the role-bound form (SP-B) | — | — |
| DO-20 | The regenerated closures are larger (this repository's root selection adds recursors, whole logical units and checker support) | accept; add a plain-dependency closure to `ix` for IxCC | Accept | A second closure semantics in `ix` would be maintained for fixtures only; the larger closures pass ingestion and the suites unchanged | Low; kernel-evaluated recheck tests may slow |
| DO-21 | Does the image the evaluator reads keep subterms shared? | a flat tree; a DAG with each distinct subterm once | The shared form for the evaluator, with the tree form as the specification of content | A flat image is about 6 times the closure for a small program and about 21 times for the one-megabyte closures, measured outside this tree, and a circuit hashes all it reads | Medium: a second canonical-order argument in the codec proofs |
| DO-22 | Universe profiles in the image: one term per constant and profile, as the IxVM workstream asked, or Src's one level-polymorphic term with level-exact conditions | per profile; per constant | Per constant, the reader deciding the level conditions at concrete levels | Smaller; it is what SrcEval reads; the decision is one scan of a short list | Low before the format is frozen |
| DO-23 (decided 2026-11-14: the entry is generated at the declared arity) | Are roots η-expanded to their declared type's arity? Under exploration | η-expand; keep roots as written, with the compiled arity pinned to the declared parameter count (2026-11-13) | Keep the pin until the exploration reports | The arity decision of 2026-11-13 already fixes what the theorems quantify over | Low |
| DO-24 | Result contracts in a type's identity, so that a source-level resource statement survives the kernel's conversion (a decision for the kernel's owners, in IxCK and the IxVM kernel) | compare result contracts in conversion; forbid non-default result contracts wherever conversion can see them | Compare them in conversion, as input contracts already are | It closes the class of hole the resource checker's confirmed hole belongs to, as Idris 2 did for multiplicities; RE-1 does not need it | Medium for the kernels: a result contract on λ nodes, or λs checked against their expected ∀ |
| DO-25 | When IxCC's ownership checker cannot verify a written contract on an internal function | refuse the program; compile as if the contract were absent | Refuse, with a diagnostic naming the contract (D16: contracts honoured exactly) | Dropping is sound for memory in a closed-world compile but silently discards what the source asked for | Low |
| DO-26 | Which arguments an erased parameter erases (ix's checker erases wherever the head's type exposes an erased binder; IxCC only at constant and β-redex heads) | IxCC decides relevance from the head's type at every application; ix's checker grades erased only where IxCC erases | IxCC widens, with its relevance checker's rule extended | Erasing more evaluates less, and the kernel already forces a λ reaching an erased variable to have an erased binder | Low |
| DO-27 | When the source-level resource theorem (RE-2) is scheduled | after EV-1, in parallel with RE-1; on demand, when a claim on the evaluator route first states a resource property | On demand, with RE-1 first | The native route's memory safety needs RE-1 only; on the evaluator route annotations optimise nothing | Low |
| DO-28 (decided 2026-11-14: the default) | Does "self-host that logic" mean a pure certified program plus a small proved machine-level layer that IxCC generates from Lean, never C, with the system-call residue never compiled from Lean source? | yes; require the residue in Lean source too | Yes | The system-call instruction in compiled text would break Ring-0 admission; the residue is a few instructions per call, proved | Low |
| DO-29 (decided 2026-11-14: the default) | Stack and region: a static zero-filled segment sized when the executable is written, or mapped at start-up | static; mapped | Static | No system call, strict confinement possible, the driver contract decidable on constants | Low: the mapped variant is three more calls and their model |
| DO-30 (decided 2026-11-14: the default) | Effects: requests returned as data first, platform calls as traced events later, over one platform interface | as stated; platform calls only; requests only | As stated | Requests need nothing new in the pipeline; Lean `IO` needs platform calls | Low |
| DO-31 (decided 2026-11-14: the default) | The system-call instruction only in platform code, as a platform-only row the program checker refuses | as stated; allow it in program text | As stated | Program text stays admissible under the IxOS tender's Ring-0 check | Low |
| DO-32 (decided 2026-11-14: the default) | Executables confine themselves with seccomp (strict while the interface is `write`/`read`/`exit`, then a filter of exactly the interface) | on by default; off by default | On by default | The kernel interface after start becomes as small as the theorem's model | Low |
| DO-33 (decided 2026-11-14: the default) | What an executable claim binds | the object's claim plus the executable's hash, platform, shell version, entry convention and layout; less | As stated; a verifier rebuilds the executable deterministically | Every input to the executable's bytes is bound | Medium: the claim codec is shared with ix |
| DO-34 (decided 2026-11-14: the default) | Redefine XB-1 and IxOS-0 as IxCC-written executables replacing the C runtime driver, out of process, dropping the in-process trampoline | redefine; keep the host loader | Redefine | The trampoline is C or assembly in the Lean process, which the owner's decision excludes | Low |
| DO-35 (decided 2026-11-14: the default) | Numeric state machines (X2) on today's fragment before Phase 3 | before; after | Before, if Phase 3 is more than about six months away | They need no heap across calls, so the session theorem is available early | Low |
| DO-36 (decided 2026-11-14: the default) | Lean `IO` through platform calls with recorded interpretations, or by transforming `main` into a state machine | platform calls; a continuation-passing transformation | Platform calls; revisit if IxOS programs must never call out | Keeps ordinary Lean `main` unchanged; the transformation would need closures and a whole-program rewrite | Medium |
| DO-37 (decided 2026-11-11: (a)) | How premise (i) is discharged natively | (a) the logical entry run on the closure of the seeds, under the IxVM claim's table and the committed prelude (KF-4); (b) the tiered whole-artifact acceptance, with three restriction lemmas (models, table and prelude, derivations) | (a) | One statement for both routes, no restriction lemmas; one more kernel run over a subset of the records already checked, and a ported closure walk (0.3–0.6k lines) | Low: (b) is lemmas, not behaviour; (a)'s code is small |
| DO-38 (decided 2026-11-11: (c) preferred, which is also the IxVM side's preference, with (a) as the fallback; the artifact tables were measured to be restrictions of the default one on every committed role-bound closure) | How a compile claim's artifact table meets the IxVM claim's default table | (a) a restriction check plus a reading lemma beside the kernel's reader; (b) `ix compile` writes the default table into every artifact; (c) the IxVM side widens its theorem to every admitted table | (a), asking the kernel side for the lemma; (c) noted as the IxVM side's option | (a) changes no artifact; (b) makes every artifact carry every role's support and certificate closure (larger files, and the kernel must admit roles whose constants are absent); (c) is a change to their statement's scope | Low: the check is a pure function of two tables |
| DO-39 (decided 2026-11-11: (a); the law is scheduled on the IxVM side, over all literals) | The `Nat` operations' meaning on literals | (a) a public law on the kernel side; (b) IxCC derives it from δ, ι and the role specifications, by induction | (a), with (b) as the fallback if the law is not scheduled before SP-1 | The kernel's internal invariant already carries the recurrences; a law is a small step there and serves IxVM's own discharge path; (b) costs IxCC 2–4k lines | Low |
| DO-40 (decided 2026-11-11: (b), the working view on both sides) | Where the typing derivations of premise (ii) come from on the IxVM route | (a) the IxVM claim exposes its records over the kernel's rules for the claimed environment; (b) the lowering claim proves typing for the image's positions | (b), with (a) asked as well | The lowering claim already checks the relevance clause with the circuit's own inference, which is typing; (a) changes the consistency statement | Medium: it fixes what the lowering claim states |
| DO-41 (decided 2026-11-11: (a)) | Do the compile claim's fields change? | (a) no change now; the image digest joins with SP-0 and with the target determines the seeds; (b) add the seeds' tree root or the kernel table's address now | (a) | `env` and `roleTable` keep a true meaning (what IxCC read); the seeds are a function of the target and `D`; a field added before the image exists would be unfilled | Medium: the claim codec is shared with ix |

## Coordination

- **The IxVM workstream.** It owns the evaluator circuit, its refinement of
  SrcEval, the kernel circuit's lowering claim and the aggregation; IxCC owns
  the evaluator contract, the image and its interfaces (DO-2), the
  faithfulness and typing clauses, and soundness and progress (DO-1 for the
  spike). IxVM's consistency theorem (an accepted claim's closure has a model;
  today a reduction to eight per-layer obligations), which discharging premise
  (i) by an IxVM proof relies on, and the fix to IxCK's typing core on chains
  of `let`, are that workstream's, as are the external dependencies listed as
  XK.
- **ix / certify-compile.** Reconcile equation export, compiler hints and
  source-contract transport with the new compiler passes and their closure,
  changed-block and definition-group coverage requirements. Reproduce the
  consumer's former recursor and proof-closure blockers on an identified
  candidate before marking them resolved.
- **Certified checker and model.** IxCK's public `Model`, with the laws the
  certified IxVM work is adding to it, is the target of the grounded
  statement; IxCC asks the kernel side for the laws and lemmas listed as XK.
  Codec compatibility and the adopted Lean 4.34.1
  toolchain already have their own pins; IxCC now imports IxCK's tiered
  admission entry and executed typing core (the [kernel front
  end](kernel-front-end-design.md)), recorded in the trust ledger with the
  kernel's own `implemented_by` rulings as an enumerated exception.

## Measurement

The [benchmark design](benchmark-plan.md) defines comparison rules. The first
rows are:
- IxCC;
- `lean-clang` (the same Lean source through Lean's bundled Clang at `-O3`);
- `clang-idiomatic` (natural C or C++ twins).

GCC, CompCert, CakeML, OCaml and Koka are reference rows. Correctness and
deterministic step counts run in CI; timing runs locally with paired A/B
sessions. [Historical reports](performance/README.md) are retained.
