# Compilatr.ix roadmap

Reviewed 2026-09-29. This page owns priorities, delivery state and
acceptance criteria. [Compiler design](compiler-design.md) explains the
architecture; [development and validation](development-plan.md) explains
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

## Current state (2026-09-29): reset

The compiler is being rebuilt. The earlier pipeline:
- read Ixon v2;
- tied its source semantics to no kernel;
- certified only single-program families through nine x86 selectors with no
  register allocation.

It, the Ixby backend and the Stage2 fixture left main on 2026-09-29. They
remain, with every former gate and measurement, on branch
`jcb/ixby-archive`.

**What remains in main:**

| Component | Scope |
| --- | --- |
| [Ixon v4 ingress](ixon-v4.md) | ix's v4 codec with canonicity evidence and pure-BLAKE3 authentication, catalog-v2 admission, erased typing, resource admission, claim binding |
| [x86 target model](x86-encoded-instructions.md) | Typed x86 AST and machine, E1 per-form encoder/decoder and execution laws, E2 [streams and ELF objects](x86-stream-objects.md), [stream checking](stream-checking.md), the [reference-model record](x86-reference-model.md) |
| [Aiur target](aiur-backend.md) | Pinned bytecode vocabulary, wire format, semantics, static checks, counter analysis, memory and rank AIRs |
| Tools | Trust ledger, build-graph manifest, check helpers |

The required check surface is empty and returns gate by gate
([CI guide](ci.md)).

## Plan

The pipeline being built, with each layer's proof technique:

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

## Decisions

| Decision | Summary |
| --- | --- |
| Source | Ixon (v4 since 2026-10-03) is the only input. Written contracts are lower bounds. The compiler honours them exactly, and may infer stronger guarantees (unique, local, borrowed, erased, one-shot) only when a proved checker certifies them; inferred facts never change Ixon bytes or addresses. |
| Semantic anchor | Stated against the source evaluator first, then `Ix.Kernel`'s model: an accepted equation theorem holds in the model, so replacements it justifies are sound. |
| Recursion and replacements | Compiled through kernel-checked equation theorems (`f.eq_def`, `@[csimp]`) collected in an unfolding table, not by recovering structure from `brecOn` or `WellFounded.fix`. `partial` and `unsafe` definitions are rejected; `implemented_by` compiles the reference body. |
| Erasure | An untrusted relevance annotation checked by a proved structural checker. A wrong but consistent annotation can only make a compile fail, never produce a wrong result. |
| Middle end | Clocked big-step semantics for functional IRs, with a fuel-indexed logical relation and heuristic-parametric passes. Forward simulations below. |
| Ownership | Untrusted RC, borrow and reuse passes; one proved ownership checker; fallback to plain RC. v3 resource admission is a diagnostic gate, not a proof premise. |
| Backend | Rule-based selection with one lemma per rule; an untrusted linear-scan allocator with a proved validator; a private internal calling convention with SysV at exports; fall-through layout; the existing E1/E2/ELF. |
| x86 trust | A declarative instruction table. Hardware-differential and XED/LLVM-MC gates first; the Sail agreement proof later. |
| Runtime | Written in the compiler's own low-level IR and proved: an 8-byte header, single-threaded RC, size-class free lists, iterative free, tagged 63-bit small `Nat`. No C runtime and no GMP in the trusted base. |
| Profiles | One production profile. Instrumentation, cost and space results are optional layers outside the core relations. |

## Coordination

- **ix.** Realize and export equation and `csimp` theorems, compiler hints,
  distinct identities for extern opaques, and extended closure roots.
- **ix-certified (`Ix.Kernel`).** Accept v3 contract bits, move to Lean
  4.34, and provide a stable denotation interface for the evaluator-adequacy
  proof, followed by string literals and mutual/nested inductives.

## Measurement

The [benchmark design](benchmark-plan.md) defines comparison rules. The first
rows are:
- Compilatr.ix;
- `lean-clang` (the same Lean source through Lean's bundled Clang at `-O3`);
- `clang-idiomatic` (natural C or C++ twins).

GCC, CompCert, CakeML, OCaml and Koka are reference rows. Correctness and
deterministic step counts run in CI; timing runs locally with paired A/B
sessions. [Historical reports](performance/README.md) are retained.
