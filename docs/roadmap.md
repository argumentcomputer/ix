# Compilatr.ix roadmap

Reviewed 2026-10-08 against the `dd7863c` baseline and the current integration tree. This page owns priorities,
delivery state and acceptance criteria. [Compiler design](compiler-design.md)
explains the architecture; [development and validation](development-plan.md) explains
how to land a change; the [documentation guide](README.md) indexes contracts
and evidence.

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
against the model of ix-certified's `Ix.Kernel`.

## Current state (2026-10-08)

Phase 1's scalar pipeline is implemented: Src evaluation through checked
erasure, middle-end transformations, register allocation and ELF emission.
`Recheck.sound` covers objects accepted by `Recheck.run` under
`X86.Driver.Ok`, relative to SrcEval. Its return clause allows source
`GoesWrong`; safety requires excluding that case. The
[correctness statement](compiler-design.md#correctness-statement) records the
precise scope and native-model assumptions. Source adequacy against the
certified kernel's model remains open.

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
| Scalar compiler | Src-to-ELF recheck path, `Recheck.sound`, certificate/artifact checks and native pipeline suites |
| Bounded plain RC | Separate `Recheck.RcReplay` API; exact ownership/certificate replay, ordinary Lir recycling runtime, SrcEval-relative object theorem, complete per-stage/native values, executed RC event counts and heap-failure/corruption controls; final producer integration remains open |
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

## Plan

The pipeline and its staged delivery scope:

```text
Ixon v4 → Src (relevance-annotated kernel terms + unfolding table)
        → Lam (erased λ-calculus) → Anf (join points; shrink, inline, specialise)
        → Fir (closure-converted, first order) → Own (explicit RC, borrow, reuse)
        → Cfg (control-flow graph) → Lir (words, memory, runtime)
        → Xv (x86 on virtual registers) → Xl (allocated) → typed x86 → E1 → E2/ELF
```

| Phase | Deliverable | Benchmark rung |
| --- | --- | --- |
| 0 | Reset and foundations: first gates back, the ix `eq_def` export, design notes, a declarative x86 instruction table with compact encodings, hardware-differential and decoder gates, first-wave fixtures, census, Lean/Clang measurement rows | — |
| 1 | Scalar vertical slice from real Lean source to certified ELF, with register allocation, loops and recursion (`fib`, `for` loops, Ackermann, `tak`, `gcd`) | K1 |
| 1.5 | Reviewed resource checking, address-bound equation/profile selection and contract transport; assess upstream certification before the final producer repin | Existing K1 and annotated/plain fixtures |
| 2 | Heap: constructors, reference counting, reset/reuse, allocator; `unique`/`borrow` twins | K0 (real `List.reverse`), K2 (lists), K3 (trees) |
| 3 | Closures, fixed-width integers, arrays, bytes, strings (`qsort`, `unionfind`, BLAKE3, `deriv`) | K4 |
| 4 | Bignums, scale, objects and tooling, applications | K5, K6 |

**Performance targets** are provisional and frozen per rung after first
data:
- K1: geomean ≤ 1.3× Lean → Clang and ≤ 1.5× idiomatic C at `-O2`;
- K2/K3 plain sources: ≤ 1.2× Lean → Clang;
- annotated twins: ≤ 1.0×;
- K4: ≤ 1.3×;
- no row above 2×;
- ≤ 10 s to compile and check each suite program.

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
| Erasure | An untrusted relevance annotation checked by a proved structural checker. A wrong but consistent annotation can only make a compile fail, never produce a wrong result. |
| Middle end | Clocked big-step semantics for functional IRs, with a fuel-indexed logical relation and heuristic-parametric passes. Forward simulations below. |
| Ownership | Untrusted RC, borrow and reuse passes; one proved ownership checker; fallback to plain RC. Ixon resource admission is a diagnostic gate, not a proof premise. |
| Backend | Rule-based selection with one lemma per rule; an untrusted linear-scan allocator with a proved validator; a private internal calling convention with SysV at exports; fall-through layout; the existing E1/E2/ELF. |
| x86 trust | A declarative instruction table. Hardware-differential and XED/LLVM-MC gates first; the Sail agreement proof later. |
| Runtime | Written in the compiler's own low-level IR and proved: an 8-byte header, single-threaded RC, size-class free lists, iterative free, tagged 63-bit small `Nat`. No C runtime and no GMP in the trusted base. |
| Profiles | One production profile. Instrumentation, cost and space results are optional layers outside the core relations. |

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
- Compilatr.ix;
- `lean-clang` (the same Lean source through Lean's bundled Clang at `-O3`);
- `clang-idiomatic` (natural C or C++ twins).

GCC, CompCert, CakeML, OCaml and Koka are reference rows. Correctness and
deterministic step counts run in CI; timing runs locally with paired A/B
sessions. [Historical reports](performance/README.md) are retained.
