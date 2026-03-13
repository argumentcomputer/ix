# Ix Theory Documentation

This directory contains formalization plans for the Ix system — from the kernel
typechecker through the compiler pipeline, ZK layer, and proof system.


## Documents

| Document | Summary |
|----------|---------|
| [kernel.md](kernel.md) | NbE-based kernel typechecker: substitution algebra, evaluation, quoting, definitional equality, typing judgment, verification bridge |
| [compiler.md](compiler.md) | Content-addressed compilation pipeline: canonicalization, SCC condensation, Ixon serialization, sharing analysis, alpha-invariance |
| [zk.md](zk.md) | Zero-knowledge layer: commitments, selective revelation, claims (Eval/Check/Reveal), IxVM circuits |
| [bootstrapping.md](bootstrapping.md) | Self-certifying verification: kernel circuit → `vk_ix` → certify arbitrary circuits |
| [aiur.md](aiur.md) | Formal verification framework for Aiur circuits: adapting Clean (circuit proofs) and ArkLib (protocol proofs) |


## Dependency Graph

```
kernel.md ──→ compiler.md ──→ zk.md ──→ bootstrapping.md ──→ aiur.md
    │                           │              │
    │   CheckClaim depends on   │              │
    │   kernel correctness ─────┘              │
    │                                          │
    │   kernel circuit is the primary          │
    │   circuit to verify ─────────────────────┘
```

Each document lists its prerequisites at the top.


## Reading Paths

**Motivation-first** (why this matters, then how it works):
1. [bootstrapping.md](bootstrapping.md) — the big picture: self-certifying ZK
2. [kernel.md](kernel.md) — the foundation: what "correct" means
3. [compiler.md](compiler.md) — content addressing and serialization
4. [zk.md](zk.md) — commitments and claims
5. [aiur.md](aiur.md) — making circuit proofs concrete

**Bottom-up** (foundations first):
1. [kernel.md](kernel.md) — type theory and NbE soundness
2. [compiler.md](compiler.md) — compilation and alpha-invariance
3. [zk.md](zk.md) — ZK layer on top of the compiler
4. [bootstrapping.md](bootstrapping.md) — how it all enables `vk_ix`
5. [aiur.md](aiur.md) — the proof framework that makes bootstrapping work


## Unified Formalization Tiers

All formalization work across the five documents, with dependencies:

| # | Tier | Document | Depends on |
|---|------|----------|------------|
| K1 | Core type theory (NbE soundness, typing judgment) | kernel.md | — |
| K2 | Reduction soundness (delta, iota, K, projection, quotient) | kernel.md | K1 |
| K3 | Inductive types (positivity, recursors, universe constraints) | kernel.md | K2 |
| K4 | Metatheory (strong typing, unique typing, consistency) | kernel.md | K3 |
| K5 | Verification bridge (Kernel2 → Theory translation) | kernel.md | K4 |
| K6 | End-to-end (addDecl soundness) | kernel.md | K5 |
| C1 | Serialization roundtrip (serialize/deserialize identity) | compiler.md | — |
| C2 | Alpha-invariance (de Bruijn → same bytes) | compiler.md | C1 |
| C3 | Sharing correctness (semantics-preserving) | compiler.md | C1 |
| C4 | Compilation roundtrip (compile/decompile equivalence) | compiler.md | C1, C2, C3 |
| C5 | Content addressing (determinism, injectivity mod Blake3) | compiler.md | C1, C2 |
| Z1 | Commitment soundness (hiding + binding) | zk.md | C5 |
| Z2 | Claim soundness (Eval/Check/Reveal) | zk.md | K1+, C5 |
| Z3 | Selective revelation correctness | zk.md | Z1 |
| Z4 | ZK circuit equivalence (Aiur = native) | zk.md | A1+ |
| Z5 | End-to-end ZK soundness | zk.md | Z1–Z4, K6, C5 |
| A1 | Op-level circuit soundness | aiur.md | — |
| A2 | Control flow soundness (selectors, match) | aiur.md | A1 |
| A3 | Compositional soundness (blocks, functions, subcircuits) | aiur.md | A1, A2 |
| A4 | Lookup and memory soundness | aiur.md | A1 |
| A5 | Protocol soundness (multi-STARK, FRI) | aiur.md | — |
| A6 | End-to-end Aiur soundness | aiur.md | A1–A5 |

The bootstrapping argument (bootstrapping.md) requires K6 + Z5 + A6 — all tiers complete.


## Lean/Rust Equivalence

Several components have parallel Lean and Rust implementations that must agree:

| Component | Lean | Rust | Verification approach |
|-----------|------|------|-----------------------|
| Kernel typechecker | `Ix/Kernel2/` | `src/ix/` | kernel.md Tier 5 (verification bridge) |
| Compiler pipeline | `Ix/CompileM.lean` | `src/ix/compile.rs` | Testing + future formal bridge |
| Ixon serialization | `Ix/Ixon.lean` | `src/ix/ixon/` | Testing + compiler.md Tier 1 |
| Aiur constraints | `Ix/Aiur/Compile.lean` | `src/aiur/constraints.rs` | Testing + aiur.md Tier 1 |

The kernel bridge is the most critical and is planned in detail (kernel.md Part XII).
The compiler and Aiur Rust verifications are future work beyond the current formalization scope.
