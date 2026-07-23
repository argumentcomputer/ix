# Ix pipeline benchmarks: pure-Lean vs Rust

Head-to-head timings for every stage of the Ix pipeline across three
environments, comparing the pure-Lean implementation (`Ix.CompileM` /
`Ix.DecompileM` / `Ix.Tc`) against the Rust implementation
(`crates/compile` / `crates/kernel`).

## Methodology

- Single machine, 32 hardware threads; both implementations use their
  default parallelism (32 workers) where the stage is parallel.
- Single-run wall-clock timings as reported by each tool's own
  instrumentation (these are minutes-long batch operations, not
  microbenchmarks; run-to-run variance is small relative to the
  gaps of interest).
- Lean-file elaboration (`getFileEnv`) is excluded everywhere — both
  sides time their core operation after the environment is in memory.
- The two implementations are **output-equivalent by construction**:
  compilation is byte-identical (`ix compile-lean --rust-check` ALIGNED)
  and decompilation is hash-identical against the canonicalized source,
  so every row compares identical work.
- The Lean implementation is the *correctness reference*; its
  performance is reported, not optimized (per the alignment ground
  rules, Lean-side performance work is out of scope).
- Sources: `Benchmarks/Compile/CompileInitStd.lean`,
  `Benchmarks/Compile/CompileLean.lean`,
  `Benchmarks/Compile/CompileMathlib.lean`.

## Environments

| Environment | Source constants | Checkable constants | Named entries | `.ixe` size |
|---|---|---|---|---|
| InitStd | 89,771 | 105,492 | 106,425 | 315,700,850 B |
| Lean | 188,999 | 188,999 | 192,026 | 470,157,016 B |
| Mathlib | 736,624 | 736,624 | 743,838 | 3,152,009,710 B |

## Compilation (env → Ixon constants)

Rust: `ix compile` (compile + serialize + write, the `##benchmark##`
line). Lean: `ix compile-lean` — the pipeline phases are reported
separately; "compile" here is the block-compilation phase (the direct
counterpart of Rust's compiler core), with the full pipeline
(canon → graph → ground → condense → compile → serialize) in
parentheses.

| Environment | Lean compile (full pipeline) | Rust compile+serialize+write | Byte-identical? |
|---|---|---|---|
| InitStd | 39.9 s (84.8 s) | 4.75 s | ALIGNED |
| Lean | 85.0 s (161.5 s) | 8.31 s | ALIGNED |
| Mathlib | 646.5 s (1,058.6 s) | 56.2 s | 49-byte divergence under investigation¹ |

Lean pipeline phase breakdown:

| Environment | canon | graph | ground | condense | compile | serialize |
|---|---|---|---|---|---|---|
| InitStd | 3.4 s | 1.4 s | 14.9 s | 3.2 s | 39.9 s | 22.0 s |
| Lean | 4.8 s | 1.7 s | 18.8 s | 4.7 s | 85.0 s | 46.6 s |
| Mathlib | 39.0 s | 14.2 s | 138.5 s | 27.5 s | 646.5 s | 193.0 s |

¹ `ix diff` localizes the Mathlib divergence to two constants
(`Lists.Equiv.below.rec` / `Lists'.Subset.below.rec` — a Prop-level
mutual `.below.rec` over the nested `Lists`/`Lists'` family) plus their
address ripples; every other constant in the 3.15 GB env is
byte-identical. Root cause (reproduced in-gate by alpha-identical
namespace clones of the `Lists` family): the Rust compiler collects a
mutual block's `.below` inductives by iterating
`patches: FxHashMap<Name, _>` (`mutual.rs:794`), so the *generation
order* of the joint `.below.rec` recursor block — which bakes motive
order and rule concatenation into the block bytes — follows FxHash
bucket order over the (name-dependent) key set. Rust itself therefore
emits different bytes for alpha-identical content depending on name
hashes (a canonicity violation independent of the Lean port); the Lean
pipeline iterates its own `Std.HashMap` layout and agrees with Rust's
order only coincidentally. Every other aux phase is order-insensitive
(per-member-independent generation + canonical class sort), which is
why a 3.15 GB env diverges in exactly one multi-`.below` mutual block.

## Serialization (in-memory env → `.ixe` bytes)

Lean: the `serialize` phase of `ix compile-lean` (`Ixon.serEnv`).
Rust: `Env::put` is not separately reported by `ix compile` in this
configuration — the Rust serialize+write cost is included in the
compilation totals above.

| Environment | Lean `serEnv` | Rust `Env::put` |
|---|---|---|
| InitStd | 22.0 s | (within 4.75 s compile total) |
| Lean | 46.6 s | (within 8.31 s compile total) |
| Mathlib | 193.0 s | (within 56.2 s compile total) |

## Deserialization (`.ixe` bytes → in-memory env)

Lean: `ix validate-lean` phase 2 (`Ixon.deEnv` parse **plus** a
byte-exactness re-serialization — the parse alone is not separately
instrumented; the reported figure is parse + reser). Rust: `Env::get`
is not separately reported either; the figure is derived as
`ix check-rs` total wall time minus its reported check time (load +
parse + ingress setup).

| Environment | Lean deEnv (+reser) | Rust env load (derived) |
|---|---|---|
| InitStd | 31.8 s | ~3.9 s |
| Lean | 55.3 s | ~5.7 s |
| Mathlib | TBD³ | ~30.3 s |

³ Lean phase-2 deserialization at Mathlib scale runs inside
`ix validate-lean`, which is deferred until the below.rec divergence
fix lands (footnote ¹).

## Decompilation (Ixon env → source constants)

Rust: `ix decompile` (the decompile pass over a `.ixe`). Lean:
`ix validate-lean` phase 5 — the full decompile driver (Pass 1 →
flags → Pass 2 aux regeneration/recovery) *plus* the hash comparison
against the canonicalized source (comparison overhead ~5 s at 205k
constants). Lean decompilation is dominated by Pass 2's kernel bridge
(regeneration re-infers through `Ix.Tc`).

| Environment | Lean decompile (+compare) | Rust decompile |
|---|---|---|
| InitStd | 305 s | 6.70 s |
| Lean | 1,317 s | 12.68 s |
| Mathlib | TBD | 221.0 s |

## Typechecking (`.ixe` through the kernel, meta mode)

Rust: `ix check-rs`. Lean: `ix check-lean`. Same constants checked,
full verdict parity.

| Environment | Constants | Lean `check-lean` | Rust `check-rs` | Ratio |
|---|---|---|---|---|
| InitStd | 105,492 | 64.8 s (~1,630/s) | 24.1 s (~4,380/s) | 2.7× |
| Lean | 188,999 | 78.1 s (~2,420/s) | 35.0 s (~5,400/s) | 2.2× |
| Mathlib (meta) | 736,624 | —² | 357.7 s (~2,060/s) | — |
| Mathlib (anon)² | 640,658 | 1,014.7 s (~630/s) | 234.0 s (~2,740/s) | 4.3× |

² At Mathlib scale the meta-mode Lean run exceeds memory (default
worker config keeps warm caches; both a 32-worker meta run and a
32-worker anon run without cache clearing were OOM-killed while
swap-thrashing). The anon row uses the scale configuration from the
`Ix.Tc` Mathlib-tier validation: 16 workers, `--clear-every 50`
(whole-worker-state renewal every 50 items; RSS plateaus ~42 GB) —
**640,658/640,658 passed, zero failures, full verdict parity**. Anon
mode dedups alpha-identical constants, hence the smaller count.

## Validation (end-to-end pipeline self-check)

The two validators are not phase-for-phase comparable (Rust's
`ix validate` runs the 8-phase aux_gen validation incl. double
compile/decompile and alpha-equivalence; Lean's `ix validate-lean` runs
compile → serde → kernel anon+meta roundtrips → decompile), so both
are reported as end-to-end wall times with their phase tables.

`ix validate-lean` (pure Lean, all phases):

| Phase | InitStd | Lean | Mathlib |
|---|---|---|---|
| 1 compile | 81.2 s | 176.9 s | TBD |
| 2 serde (byte-identical) | 31.8 s | 55.3 s | TBD |
| 3 kernel anon roundtrip | 459.0 s | 450.2 s | TBD |
| 4 kernel meta roundtrip | 13.1 s | 16.1 s | TBD |
| 5 decompile (hash-identical) | 305.0 s | 1,317.4 s | TBD |
| **total** | **~14.8 min** | **~33.6 min** | TBD |

`ix validate` (Rust, 8-phase aux_gen validation: compile → congruence →
leak check → alpha/cross-namespace canonicity → double decompile →
roundtrip fidelity → nested detection), end-to-end wall excluding
elaboration:

| Environment | Rust `ix validate` | Result |
|---|---|---|
| InitStd | 43.9 s | 0 failures |
| Lean | 100.0 s | 0 failures |
| Mathlib | 998.1 s | 0 failures |

Note: `ix validate` checks Rust's pipeline against itself, so it is
self-consistent by construction and does not detect the cross-
implementation below.rec ordering divergence of footnote ¹ (which is
itself a *within-Rust* canonicity violation, but one that `validate`'s
twin checks only surface when a twinned fixture pair exercises a
multi-`.below` mutual block).
