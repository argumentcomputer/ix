# IxCC roadmap

Reviewed 2026-11-09 against the current integration tree. This page owns priorities,
delivery state and acceptance criteria. [Compiler design](compiler-design.md)
explains the architecture; [development and validation](development-plan.md) explains
how to land a change; the [documentation guide](README.md) indexes contracts
and evidence.

[Workspaces and recovery](workspaces-and-recovery.md) records the recovery
checkpoints. Their preservation does not select a
new producer or close the implementation acceptance gates below.

## Mission

Certified compilation from Ixon v4 (ix's content-addressed Lean kernel
terms, with their usage, ownership, locality and borrow contracts) to x86-64,
with performance competitive with Lean → Clang.

The target theorem:
- If the compiled native code returns `r` for first-order inputs `xs`, then
  `r` reads back as a value whose denotation equals that of the Lean
  definition applied to `xs`, in every model of the checked environment.
- Every other outcome is an explicit resource failure (heap, stack, or Nat
  overflow until bignums land) or a run that has not finished.

The theorem is stated first against the published source evaluator, then
against the model of ix-certified's `Ix.Kernel`, and, for programs a
proof-producing translator processes, against the Lean function itself
([certification design](certification-design.md)).

## Current state (2026-11-09)

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
surveyed in the 2026-11-09 review, only the identity `Abi.nat1`). Recursive
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
original cold79/Q06 acceptance gates; upstream compiler certification does not
discharge those obligations. Phase 2 groundwork now includes bounded
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
The source suite now runs 8,514 assertions, including nine discriminating
resource-bound `csimp` controls. Authentic historical OS04 annotated/plain
recursion adds 36 complete Src/Fir/Own observations and 48 counted ownership
assertions. The annotated case uses checked immortal Own and retains its
explicit plain-RC erased-contract refusal; the plain twin uses checked plain
RC Own. These fixtures supplement the required consumer coverage; they do
not replace the selected producer's paired matrix or final family refreeze.

The Lam suite additionally passes 118 evaluation-order assertions, bringing
its local default run to 26,168 assertions. Sixteen synthetic cases pass actual
table/relevance rechecking, lazification and erasure before independently
checking Src and Lam outcomes. They distinguish direct-case demand, strict
wrappers and overapplication order, while retaining the separate resource
profile compatibility and final producer obligations.

The active goal combines Phase 1.5 completion with the first Phase 2
slice: real `List.reverse` through checked plain reference counting,
allocation/reclamation, the composed SrcEval-relative proof and native tests.
Independent heap foundations can proceed alongside producer repairs; final
real-source integration requires the reviewed producer and consumer gates.
General K2/K3 coverage and ownership optimizations remain later Phase 2 work.

The remaining combined acceptance gate is G1's resource/consumer requirements
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
preserved on `jcb/ixby-archive`, with their former gates and measurements.

**Current integration surface:**

| Component | Scope |
| --- | --- |
| Scalar & top-level compiler | Src-to-ELF recheck path (`Recheck.sound`), top-level `Compiler.compile` (`--rc auto\|on\|off`, `Compiler.compile_sound`), `CompileClaim` (`verifyProgram_*_sound`, `verifyBytes_*_sound`), `Ring0` (`verifyRing0Sip_sound`), certificate/artifact checks and native pipeline suites |
| Bounded plain RC | `Recheck.RcReplay` API (`RcReplay.run`, `RcReplay.sound`, `recycled_session`); exact ownership/certificate replay (`checkPlainMap` / `checkContractPlainMap`), ordinary Lir recycling runtime, SrcEval-relative object theorem, complete per-stage/native values, executed RC event counts and heap-failure/corruption controls; final producer integration remains open |
| [Ixon v4 ingress](ixon-v4.md) | ix's v4 codec with canonicity evidence and pure-BLAKE3 authentication, catalog-v2 admission, erased typing, resource admission, claim binding |
| [x86 target model](x86-encoded-instructions.md) | Typed x86 AST and machine, E1 per-form encoder/decoder and execution laws, E2 [streams and ELF objects](x86-stream-objects.md), [stream checking](stream-checking.md), the [reference-model record](x86-reference-model.md) |
| [Aiur target](aiur-backend.md) | Pinned bytecode vocabulary, wire format, semantics, static checks, counter analysis, memory and rank AIRs |
| Tools | Trust ledger, build-graph manifest, check helpers |

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

- **Input.** An Ixon v4 closure and an unfolding table (`eqn`, `csimp`,
  `case`, `inline`, `lazy`, `prim`). Admission rejects `partial` and `unsafe`
  definitions, extern opaques and relevant axioms; erasure declines string
  literals in relevant positions.
- **Values.** `Nat`, exact above Lir and at run time a tagged word below
  2^63 (a larger value is the resource failure `natOverflow`); constructors
  of inductive types; □. Fixed-width integers have no representation of
  their own (erasure unboxes them to `Nat`, so a `UInt64` at or above 2^63
  fails like a `Nat`); there are no arrays, byte arrays or strings.
- **Higher-order code** only where bounded inlining and specialisation
  (P3, P4) remove it; any remaining closure is declined at Anf → Fir
  (`fir.closures`).
- **Memory.** Immortal cells, or the bounded plain-RC route: shared
  constructors with 1 to 31 scanned fields, size-class free lists, iterative
  release (`--rc auto|on|off`).
- **Roots.** Level-monomorphic, at most five `Nat` parameters; results that
  are `Nat` or enumerations (immortal and zero-RC policies) or first-order
  constructor trees (plain RC).
- **Proved.** For an accepted certificate, the object refines SrcEval on the
  checked source `a.src`, with the `GoesWrong` escape, under the x86,
  loader and driver assumptions of the [trust ledger](trusted-extern-ledger.md).
  **Not proved:** that `a.src` is the ingested program's meaning (S6), and
  that SrcEval agrees with the certified kernel's model or with Lean (S8).
  See the [certification design](certification-design.md).

## Plan

Revised 2026-11-09. The goal is a generally useful compiler for Lean code,
with certification. Two flagship targets make that concrete: the IxOS
monitor and driver compiled through `ixcc`, and the certified kernel (IxCK)
compiled through `ixcc` ([Flagship targets](#flagship-targets)).

The pipeline and its staged delivery scope:

```text
Ixon v4 → Src (relevance-annotated kernel terms + unfolding table)
        → Lam (erased λ-calculus)
        → Anf (join points; shrink, inline, specialise; P8 defunctionalisation, planned)
        → Fir (first order, known calls only) → Own (explicit RC, borrow, reuse)
        → Cfg (control-flow graph) → Lir (words, memory, runtime)
        → Xv (x86 on virtual registers) → Xl (allocated) → typed x86 → E1 → E2/ELF
```

### Phases

| Phase | Deliverable | Closes with | State |
| --- | --- | --- | --- |
| 0 | Reset and foundations: first gates back, the ix `eq_def` export, design notes, a declarative x86 instruction table with compact encodings, hardware-differential and decoder gates, first-wave fixtures, census, Lean/Clang measurement rows | — | Done |
| 1 | Scalar vertical slice from real Lean source to certified ELF, with register allocation, loops and recursion (`fib`, `for` loops, Ackermann, `tak`, `gcd`) | K1 | Done: K1 certified relative to SrcEval |
| 1.5 | Reviewed resource checking, address-bound equation/profile selection and contract transport; assess upstream certification before the final producer repin | Existing K1 and annotated/plain fixtures | In progress |
| 2 | Heap and closures: general RC (scalar fields, large objects, static objects, reset/reuse, `unique`/`borrow`, inline fast paths, the Own checker); P8 defunctionalisation; P5/P6 when measured | K0 (real `List.reverse`), K2 (lists), K3 (trees); `Decline.composeClosure` | In progress: the bounded plain-RC route and the `List.reverse` regression are implemented |
| 3 | Data and interface: fixed-width integers and small `Int`, arrays and byte arrays with in-place update, strings, interpreted opaques, P9; the byte ABI, the claim's ABI descriptor, state-machine roots | K4 | Planned |
| 4 | Bignums: the limb library compiled by IxCC; large `Int` | K5 | Planned |
| 5 | Scale and usability: input-relative budgets, linear-time recheck passes, per-function rechecking and caching, diagnostics, library census | K6; a closure of at least 2,000 definitions | Planned |
| C | Certification depth, a track beside Phases 2–5: C1 front-end theorem, C2 shape typing, C3 stage L, C4 stage K | Per item, below | C1–C3 planned, C4 research |

**Changes from the previous table** (Phases 0 to 1.5 are unchanged):
- Closures move from Phase 3 to Phase 2. The design is closed-world
  defunctionalisation in Anf, so closures are constructor cells under the
  same RC as other data and arrive with it, as the code comments already
  say ("P8, Phase 2"); K2 and K3 sources may need them.
- Scale and tooling move from Phase 4 to a Phase 5 of their own, since both
  flagships need them and they do not depend on bignums.
- The semantic obligations (S6, S8, `GoesWrong`) become an explicit track
  with exit criteria instead of the single "stage 2" sentence.
- The two flagship targets are added as milestones.

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

- **Heap completion** ([D1](data-and-roots-design.md#d1-heap-completion)):
  scalar fields, constructors beyond 31 fields and large objects, static
  objects, reset/reuse with a uniqueness test, static reuse from `unique`
  contracts, borrowed parameters, inline RC fast paths, and the proved Own
  checker with the canonical plain producer as its fallback.
- **P8** ([closures design](closures-design.md)): defunctionalisation,
  dispatchers, the known-dispatch shrink rule, `Anf.Defun.correct`.
- **P5 and P6** only where K2/K3 measurements show the need.
- *Depends on:* Phase 1.5's final producer for the K0 refreeze.
- *Exit:* K0 refrozen with the final producer; K2 and K3 frozen, compiled
  under `--rc auto` and certified, measured against their targets, with the
  annotated twins against the plain sources; `Decline.composeClosure` and the
  new higher-order corpus roots of the closures design compile and certify.

### Phase 3: data and interface

- **Fixed width and small `Int`** ([D2](data-and-roots-design.md#d2-fixed-width-integers-and-int)),
  **arrays and byte arrays** ([D3](data-and-roots-design.md#d3-arrays-and-byte-arrays)),
  **strings** ([D4](data-and-roots-design.md#d4-strings)),
  **library structures and interpreted opaques** ([D5](data-and-roots-design.md#d5-library-structures-and-opaque-constants)).
- **Roots**: the byte ABI ([R1](data-and-roots-design.md#r1-structured-roots-and-the-byte-abi)),
  the claim's ABI descriptor with the encoding fixes of the 2026-11-09
  review ([R2](data-and-roots-design.md#r2-what-the-compile-claim-binds)),
  monomorphic roots ([R3](data-and-roots-design.md#r3-universe-polymorphism-and-type-parameters-at-roots)),
  state-machine roots ([E1](data-and-roots-design.md#e1-effects-and-io)).
- **P9** and the flow oracle, if K4 shows dispatch cost.
- *Depends on:* Phase 2's scalar fields, large objects and uniqueness test;
  P8 for library code over dictionaries.
- *Exit:* K4 compiles, certifies and is measured; BLAKE3 passes its
  known-answer vectors; a `ByteArray → ByteArray` root round-trips through
  the driver; a state-machine session of 1,000 calls passes.

### Phase 4: bignums

- The limb library and the bignum representation ([bignum design](bignum-design.md)).
- *Depends on:* D1–D4; C3 for the library's layer-3 proof (until then an
  explicit ledger assumption, as the design says).
- *Exit:* K5 compiles, certifies and matches Lean; `natOverflow` is retired
  with its gate map; the library theorems are fenced.

### Phase 5: scale and usability

- [Scale and usability](compiler-design.md#scale-and-usability).
- *Depends on:* nothing for budgets, linear passes and diagnostics;
  per-function certificates for incremental rechecking.
- *Exit:* K6 compiles and certifies; a closure of at least 2,000 definitions
  compiles and rechecks with no budget refusal within a compile-time target
  set after its first measurement; the library census is published.

### Certification track

| Item | Content | Depends on | Exit | State |
| --- | --- | --- | --- | --- |
| C1 | Front-end theorem (S6): table, relevance canonicity, `Lazify`, pins | — | Five checker lemmas fenced; a corollary of `Recheck.sound` exposing them | Planned |
| C2 | Checked shape typing on Src: progress and preservation | C1 | `GoesWrong`-free corollaries of `Recheck.sound` and of Ring-0 admission for shape-checked programs, on K1 and the corpus | Planned |
| C3 | Stage L: a proof-producing translator from Lean constants to SrcEval behaviour | C1; ix's certified Lean-to-Ixon compile | `fib`, `gcd`, `ackermann` with "the object's result is `f xs`"; then the bignum library | Planned (prototype), research (IxCK scale) |
| C4 | Stage K: semantic adequacy of SrcEval in the certified kernel's models (S8), replacing the conditional bridge | C1 | A spike on `fib` with the environment taken from the claim bytes; a size estimate after it | Research |

Details and the obligations each extension adds are in the
[certification design](certification-design.md). Recommended order: C1 and
C2 first, then the C3 prototype, with C4 as a research spike in parallel.

### Flagship targets

**F1. The IxOS monitor and driver compiled through `ixcc`.** IxOS runs
admitted programs as software-isolated processes (SIPs) in Ring 0 and its
monitor is itself Lean code compiled by IxCC. In this plan the monitor is a
state-machine root (E1) and a small trusted *tender* performs privileged
operations and the calls into SIP entries, because compiled code has no
indirect calls.

| Step | Content | Prerequisites | Exit | State |
| --- | --- | --- | --- | --- |
| F1.0 | A host loader that maps an object and calls its entries through a minimal ledgered trampoline, with readback in Lean, in place of linking `runtime_driver.c` | none | The K1 and RC suites pass through it with the C driver removed from the execution path | Planned |
| F1.1 | Fuel metering in prologues and at back edges with a new resource status; Ring-0 frame preservation on every outcome, not only on return | none | Fenced theorems; the session gate with fuel exhaustion | Planned |
| F1.2 | A minimal monitor: SIP table, region allocation, request dispatch to the tender, admission by claim digest and external evidence | Phase 2 (P8, D1), D2, D3, R1, E1 | The monitor's `step` certified; a host-harness session of SIP calls | Planned |
| F1.3 | Admission inside the monitor: `CompileClaim.verifyBytes` compiled by IxCC | Phases 2–5 (bignums for 256-bit address comparisons, strings for certificate parsing, scale for the checker's closure) | An IxCC-compiled `check-cert` agrees with the Lean-compiled one on every committed certificate and the hostile-input regressions | Planned |
| F1.4 | Certification: C2 for confinement without the source-safety premise; C3 on `step` and on `verifyBytes` | C2, C3 | "Admitted by the compiled monitor ⇒ accepted by the Lean verifier" as a theorem | Research |

**F2. The certified kernel compiled through `ixcc`** (native x86; the
2026-11-09 IXCC-ROUTE review argues against this route for IxVM's Aiur
circuits, which is a separate question).

| Step | Content | Prerequisites | Exit | State |
| --- | --- | --- | --- | --- |
| F2.1 | `Ix.Kernel.Level` (`IxCK/Kernel/Level.lean`: fuelled, mutually recursive level comparison using `Int` offsets) | Phase 2, D2 | Compiles, certifies, and agrees with the Lean-compiled functions on generated level pairs | Planned |
| F2.2 | The checker, through the reference fold `checkDeclsPure` or the cached fold: records of closures, monad polymorphism, `HashMap`, `Array`, `ByteArray`, `UInt64`, `USize`, `Int`, strings, exact `Nat` | Phases 2–5; D5's interpretation table, or IxCK without `mixHash` and `getNumBits` | Differential agreement with Lean-compiled IxCK on its smoke environment and claim fixtures; certified relative to SrcEval | Planned |
| F2.3 | "The object accepts ⇒ `checkDecls` accepts" as a Lean theorem, then IxCK's soundness | C3 at IxCK's scale (or C4 plus a reflection step with no design) | The composed theorem fenced | Research |

### Dependencies in brief

```text
Phase 1.5 ─► Phase 2 (D1 heap, P8) ─► Phase 3 (D2–D5, R1–R3, E1, P9) ─► Phase 4 (bignums) ─► F1.3, F2.2
                     │                         │                                ▲
                     └──────────► F1.2 ◄───────┘                    C3 ─────────┘ (bignum layer 3)
Phase 5 (scale) ─► F1.3, F2.2, K6
C1 ─► C2 ─► F1.4 ;  C1 ─► C3 ─► F1.4, F2.3 ;  C1 ─► C4 (research)
F1.0, F1.1: no prerequisites
```

### Phase 1.5 priorities after the certification work

The upstream `jcb/ix-certify-compile` revision inspected on October 8 is
`fc058f9357da4e14fd3ff9e4d506f417faf7957a`. It provides several distinct
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
   500,000-step/depth-256 limits, all R2-1 cast-bypass controls, Lean/Rust parity,
   equation/profile bindings, and D16/CX-2 contract transport. W/S acceptance cannot replace
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

| Decision | Summary |
| --- | --- |
| Source | Ixon (v4 since 2026-10-03) is the only input. Written contracts are lower bounds. The compiler honours them exactly, and may infer stronger guarantees (unique, local, borrowed, erased, one-shot) only when a proved checker certifies them; inferred facts never change Ixon bytes or addresses. |
| Semantic anchor | Stated against the source evaluator first, then `Ix.Kernel`'s model: an accepted equation theorem holds in the model, so replacements it justifies are sound. |
| Recursion and replacements | Compiled through kernel-checked equation theorems (`f.eq_def`, `@[csimp]`) collected in an unfolding table, not by recovering structure from `brecOn` or `WellFounded.fix`. `partial` and `unsafe` definitions are rejected; `implemented_by` compiles the reference body. |
| Erasure | An untrusted relevance annotation. `Recheck.front` decides it with the structural checker (`Relevance.check`, proved in `Relevance.Proof.check_sound`) and with `Relevance.checkCanonical`, which re-derives each position's class from the declaration types and refuses an irrelevant tag it cannot justify. `Relevance.annotate` is not re-run on the recheck path, and `checkCanonical` has no theorem yet. |
| Middle end | Clocked big-step semantics for functional IRs, with a fuel-indexed logical relation and heuristic-parametric passes. Forward simulations below. |
| Ownership | Untrusted RC, borrow and reuse passes; one proved ownership checker; fallback to plain RC. Ixon resource admission is a diagnostic gate, not a proof premise. |
| Backend | Rule-based selection with one lemma per rule; an untrusted linear-scan allocator with a proved validator; a private internal calling convention with SysV at exports; fall-through layout; the existing E1/E2/ELF. |
| x86 trust | A declarative instruction table. Hardware-differential and XED/LLVM-MC gates first; the Sail agreement proof later. |
| Runtime | Written in the compiler's own low-level IR and proved: an 8-byte header, single-threaded RC, size-class free lists, iterative free, tagged 63-bit small `Nat`. No C runtime and no GMP in the trusted base. |
| Profiles | One production profile. Instrumentation, cost and space results are optional layers outside the core relations. |
| Closures | Closed-world defunctionalisation in Anf (P8), after inlining and specialisation, with untrusted flow facts narrowing dispatch (P9). Fir stays first order; no closure objects, `pap`, `apply` or indirect calls ([closures design](closures-design.md)). |
| Bignums | Decided by the owner on 2026-11-09: new Lean implementations of the standard multi-precision algorithms, each proved against `Nat` and compiled by IxCC; several references consulted, GMP for behaviour only ([bignum design](bignum-design.md)). |
| Roots and effects | Roots stay level-monomorphic; structured data crosses the boundary as bytes; interacting programs are state machines driven by a host ([data, roots and effects](data-and-roots-design.md)). |

## Open decisions

These need the owner. Each has the default this plan assumes and what a
later change would cost.

| Decision | Default | Cost of changing later |
| --- | --- | --- |
| Must closures cross a program boundary, or higher-order libraries be compiled separately? | No: boundaries pass first-order data and higher-order libraries are compiled into each program | Code-pointer closures at the boundary only: a new object kind, an indirect-call row with a target-validity premise, an extended Ring-0 argument; about 6–9k proof lines [estimate] ([closures design](closures-design.md#fallback-code-pointer-closures)) |
| May a compile claim carry interpretations of opaque constants (`mixHash`, `getNumBits`)? | Yes, recorded in the claim, so `Std.HashMap` compiles from its Lean definitions | Refusing them later makes such claims unverifiable and pushes targets (IxCK) to remove hashed fields; allowing them later is a claim-format change ([D5](data-and-roots-design.md#d5-library-structures-and-opaque-constants)) |
| Which route to Lean's meaning first: stage L (C3) or stage K (C4)? | C3 first, C4 as a research spike | Small: C1 and C2 serve both; the cost is the order in which the flagships get their end statements |
| Is the IxOS tender (privileged operations and calls into SIP entries) a ledgered component, or are indirect calls certified? | Ledgered tender | A certified indirect call later needs the same row and premise as the first decision |
| Should the pre-merge design notes (`plans/x86-v2/00`–`06`, about 5.8k lines, untracked) be added to the repository as historical records? About 480 code comments cite them | Yes, under `docs/design-notes/` with a header marking them historical and superseded where the tracked documents differ | Otherwise every citation must be rewritten against the tracked documents |

## Coordination

- **ix / certify-compile.** Reconcile equation export, compiler hints and
  source-contract transport with the new compiler passes and their closure,
  changed-block and definition-group coverage requirements. Reproduce the
  consumer's former recursor and proof-closure blockers on an identified
  candidate before marking them resolved.
- **Certified checker and model.** Evaluate W/S interfaces at a fixed revision,
  their supported domains and trust premises; derive the evaluator-adequacy
  bridge separately. Codec compatibility and the adopted Lean 4.34.1 toolchain
  already have their own pins; a full-checker dependency is a separate change.

## Measurement

The [benchmark design](benchmark-plan.md) defines comparison rules. The first
rows are:
- IxCC;
- `lean-clang` (the same Lean source through Lean's bundled Clang at `-O3`);
- `clang-idiomatic` (natural C or C++ twins).

GCC, CompCert, CakeML, OCaml and Koka are reference rows. Correctness and
deterministic step counts run in CI; timing runs locally with paired A/B
sessions. [Historical reports](performance/README.md) are retained.
