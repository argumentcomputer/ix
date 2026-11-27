# IxCCAiur

`IxCCAiur` is the certified compiler bridge from [IxCC](../IxCC/README.md)'s
first-order intermediate representation (`IxCC.Fir`) to [Formal Aiur](../Aiur/README.md)
(`Aiur.Program`), enabling pure annotated Lean 4 programs to compile directly to
multi-STARK, single-circuit STARK, and KZG/PLONK circuits without per-circuit
refinement proofs and without expanding the trusted computing base.

It is a standalone Lake package (`ix-cc-aiur`) so that `IxCC` and `IxCK` remain
strictly Mathlib-free while `IxCCAiur` composes `IxCC` with `Aiur` (which uses
Mathlib's algebraic field hierarchy). Nothing in `Ix`, `IxCK`, or `IxCC`
imports `IxCCAiur`.

For the full soundness chain, optimization architecture, multi-endpoint
compression design, and CPU benchmark tables, see
[docs/ixcc-aiur-compiler.md](../docs/ixcc-aiur-compiler.md).

## Compilation pipeline

```text
Pure Lean 4 (+ open scoped Ix.Circuit)
  ─ix compile --circuit-schedule-out --circuit-guesses-out→
    CLOSURE.ixe + SCHEDULE.json + GUESSES.json (Ixon addresses unchanged)
  ─IxCC.Recheck.ingress / frontAuto + Recheck.produceFir + Recheck.runFir→
    IxCC.Fir.Program (rechecked front-half certificate)
  ─IxCCAiur: GuessLower → TypedLower + Peephole → InlineFuse →
             PartialEval → FieldLower / CompressionIntrinsics / WitnessIO→
    Aiur.Modules.Program (Goldilocks | BN254 Fr | BLS12-381 Fr)
  ─Aiur.Modules.prepare + TypedWorld.check + Aiur.Optimized (+ DegreeBudget)→
    PACKAGE.ixa (v3) + PACKAGE.ixa.pin.json (+ optional ADVICE.ixa)
  ─Provers & Exporters→
    • Multi-chip Goldilocks STARK:  crates/aiur/examples/ixcc_prove.rs
    • Endpoint 1 Single-Circuit:    wide_export / tiling_export2 --single-circuit
                                    → crates/aiur/examples/single_circuit_prove.rs
    • Endpoint 2 BLS12-381 PLONK:   plonk_export --bls12-381 → tools/gnark (BLS12-381 SCS)
    • Endpoint 3 BN254 L3 Stages:   wide_export / tiling_export2 / plonk_export
                                    → crates/proof-compression (ix-aiur-stages-v1)
```

## Package layout

### Core lowering, simulation, and certification (`IxCCAiur/IxCCAiur/`)

| Module(s) | Role |
|---|---|
| `FirFacts.lean`, `Lower.lean`, `Gadgets.lean`, `Backward.lean` | Base `IxCC.Fir` → `Aiur.Generic.Program` lowering, `UInt8`/`UInt64` and `wDivmod` (`ixcc.divmod64`) gadget soundness, and backward simulation. |
| `World.lean`, `Compose.lean`, `Claim.lean`, `Progress.lean`, `Instance.lean` | World check (`World.checkWorld`), composition with `IxCC.Recheck.runFir`, source-progress elimination (`Progress.checkShape`), and public claim theorems. |
| `CompiledCert.lean` | Composes `IxCCAiur` soundness with Formal Aiur's `Aiur.Audit` into self-contained `Cert` and `TypedCert` compiled-artifact certificates. |
| `Schedule.lean`, `ScheduleJson.lean`, `Hints.lean` | Ingests `"ixcc/circuit-schedule/1"` JSON sidecars (inline, noinline, group, unroll, lanes, budget, range-table, static, repr, intrinsic, split-fastpath, guess metadata) and Lean evaluator hint dispatch. |
| `TypedRep.lean`, `TypedLower.lean`, `TypedGadgets.lean`, `TypedWorld.lean`, `Peephole.lean` | Shape-directed unboxed lowering (`Field`, `UInt8`, `UInt32`, `UInt64`, flat tuples/enums), 30-function `.u32`/`.u64` body checker (`checkU32Functions`), and verified peephole rewrites (`add3`, `rotr8`/`16`, `xor_rotr7`/`12`, byte shifts). |
| `TypedBackward.lean`, `TypedClaim.lean` | Full backward simulation (`typed_backward_sound`, `typed_circuit_sound_goldilocks`) and source-level claim theorems (`typed_accepted_nat`, `typed_accepted_enum`) for typed unboxed lowering. |
| `InlineFuse.lean`, `InlineFuseProof.lean` | Sharing-aware function inlining, let-flattening, peephole, and dead-function pruning with full backward simulation. |
| `PartialEval.lean`, `PartialEvalProof.lean` | Heap-dereferencing compile-time partial evaluation collapsing static verifier keys and DAGs into straight-line arithmetic with backward simulation. |
| `FieldLower.lean`, `FieldLowerProof.lean` | Native ambient `Field` intrinsic lowering (`field.{add,sub,mul,neg,inv,div,is_zero,eq}`) over Goldilocks, BN254 `Fr`, and BLS12-381 `Fr`, downgrading pure-field circuits to `TableTier.none` (0 fixed rows). |
| `GuessLower.lean`, `GuessLowerProof.lean` | Tier-2 non-deterministic `guess f c θ [θc]` lowering to checked `"ixcc.guess.<fn>"` hint calls with backward soundness. |
| `Blake3Spec.lean` | Standalone Tier-1 `Aiur.Library.Blake3` world specification (24 `EvalFn` contracts, zero `IxVM` imports). |
| `WitnessIO.lean` | Checked `StarkIO` (`stark.io.*`) and `KzgIO` (`kzg.io.*`) witness-stream ingress modules and existential NP backward soundness (`witness_stream_exists`, `witness_wrapper_sound`, `witness_wrapper_assertOk_sound`). |
| `CompressionIntrinsics.lean` | Multi-field compression intrinsics (`goldilocks.*` native/emulated with BLS12-381/BN254 no-wrap bounds, `blake3.*`, `stark.io.*`, `kzg.io.*`), custom `--entry-name` / `--assert-ok` ABI aliasing (`aliasEntry_sound`), and deduplicated 3-field linker (`linkedProgramWith`). |
| `Fib.lean`, `Gcd.lean`, `Roots.lean` | Kernel-discharged `Instance.accepted_nat` end-to-end instances (`fib`, `gcd`, `evenOdd`, `sfib`, `tak`). |
| `Driver.lean`, `Main.lean` | Executable driver (`ixcc-aiur`), BLAKE3 pin JSON generator (`PACKAGE.ixa.pin.json`), and cross-evaluator agreement checks. |
| `Audit.lean` | Complete `#guard_msgs` theorem-signature and `#print axioms` audit surface (verified by `leanchecker IxCCAiur.Audit`). |

### Pure annotated Lean 4 examples and compression verifiers

All files in `IxCCAiur/Examples/` and `IxCCAiur/Compression/` import **only**
`Ix.Compile.CircuitContract` (plus their sibling wire module) — zero `MultiStark`,
`Aiur`, `IxCC`, or `Mathlib` imports — and preserve 100% identical Ixon content
addresses with or without `Ix.Circuit` attributes.

| File | Description |
|---|---|
| `Examples/Blake3Block.lean` | Zero-annotation pure Lean 4 BLAKE3 compression function (`UInt32` arithmetic). |
| `Examples/MmcsPure.lean` | Batched MMCS Merkle opening verifier. |
| `Examples/KzgAlgebraPure.lean` | KZG algebraic OOD/LogUp frame verifier demonstrating `--partial-eval --field-lower` static VK specialization. |
| `Examples/CurveOpsPure.lean` | Single-source multi-curve BN254 (`4×80b`) and BLS12-381 (`5×80b`) `Fq`/`G1` arithmetic with 5 kernel-admitted `checked def` guesses. |
| `Examples/FriPure.lean` | Protocol `v6` cubic extension $\mathbb{F}_p[X]/(X^3-X-1)$ and multi-arity FRI verifier. |
| `Examples/MultiStarkV6Pure.lean` | Unified 4-pillar Protocol `v6` Multi-STARK verifier (keyed BLAKE3/compact transcript, MMCS, AIR+LogUp OOD, cubic FRI + 3 Tier-2 guesses). |
| `Compression/StarkWire.lean`, `Compression/CompressWrapPure.lean` | Full-modulus 64-bit Goldilocks ($p = 2^{64} - 2^{32} + 1$) `CompressWrap` / `CompressGL` wire decoder and verifier (`"ix/compress-wrap/v1\0"`). |
| `Compression/KzgWire.lean`, `Compression/KzgPackedPure.lean` | Single-source BN254 and BLS12-381 production packed-SHPLONK KZG verifier (`CompressNarrowFixed::step_v1`, `CompressFinalNarrow::verify_accumulator_v1`, 18/22 affine-u80 terminal words). |

## `ixcc-aiur` CLI reference

```sh
lake -d IxCCAiur exe ixcc-aiur CLOSURE.ixe [EQUATIONS.json | --equations EQUATIONS.json] \
  [--root NAME|ADDR|NAME=ADDR] [--args N,N,...] [-o PACKAGE.ixa] [--advice-out ADVICE.ixa] \
  [--exec] [--typed] [--inline-fuse] [--partial-eval] [--field-lower] \
  [--field goldilocks|bn254|bls12-381] [--degree-budget] [--log-blowup N] \
  [--enable-guesses] [--skip-aiur-eval] [--schedule SCHEDULE.json] \
  [--entry-name NAME] [--assert-ok] [--emulate-goldilocks] [--link-blake3] [--witness-io] \
  [--no-inline] [--pair-table] [--stats]
```

| Flag | Effect |
|---|---|
| `CLOSURE.ixe` | Anonymous Ixon closure emitted by `ix compile`. If `EQUATIONS.json` is omitted, `Driver.frontAuto` auto-discovers equations via `Src.AutoHints`. |
| `--root SPEC` | Selects the root declaration (`NAME`, hex `ADDR`, or `NAME=ADDR`). Export `0` of the selected root becomes the circuit entry. |
| `--args N,N,...` | Concrete `Nat` arguments used for FIR vs. Aiur cross-evaluation agreement and (with `--exec`) baked into the execution package. |
| `-o PACKAGE.ixa` | Writes a v3 `.ixa` package (`IXAIURP\0` program package by default, or `IXAIURX\0` with `--exec`) plus `PACKAGE.ixa.pin.json` (`"ixcc-aiur-pin/1"`). |
| `--advice-out ADVICE.ixa` | Emits the unmodified pre-guess bytecode package so `ixcc_prove --advice` and `single_circuit_prove --advice` can answer all `"ixcc.guess.<fn>"` channels generically. |
| `--typed` | Enables shape-directed unboxed lowering (`TypedLower` + `Peephole`). |
| `--inline-fuse` | Enables certified `InlineFuse` (sharing-aware inlining, let-flattening, peephole, dead-function pruning). |
| `--partial-eval` | Enables certified `PartialEval` (compile-time specialization of static heap/VK inputs). |
| `--field-lower` | Enables certified `FieldLower` (`@[circuit_intrinsic "field.*"]` → native ambient `Field` ops, downgrading pure-field circuits to `TableTier.none`). |
| `--field TARGET` | Target prime field: `goldilocks` (default), `bn254`, or `bls12-381`. |
| `--degree-budget` | Enables quotient-aware `Aiur.Optimized.DegreeBudget` using `--log-blowup N` (default `2`) to select the optimal optimizer `maxDegree`. |
| `--enable-guesses` | Rewrites kernel-verified Tier-2 `checked def` / `@[circuit_guess]` functions to checked `"ixcc.guess.<fn>"` hint calls. |
| `--schedule SCHEDULE.json` | Loads `"ixcc/circuit-schedule/1"` JSON sidecar produced by `ix compile --circuit-schedule-out`. |
| `--entry-name NAME` | Exports a custom qualified ABI alias (e.g. `CompressWrap::verify_root`, `CompressNarrowFixed::step_v1`) wrapping `Prog::main0`. |
| `--assert-ok` | Used with `--entry-name`: asserts `Prog::main0(...) == 1` and returns unit `()`. |
| `--emulate-goldilocks` | Links `Aiur.Library.Field.Goldilocks.Emulated` for `goldilocks.*` intrinsics over BN254 or BLS12-381. |
| `--link-blake3` | Explicitly links `Aiur.Library.Blake3` and enables `blake3.*` intrinsic lowering. |
| `--witness-io` | Explicitly links `WitnessIO` (`StarkIO` / `KzgIO`) and enables `stark.io.*` / `kzg.io.*` intrinsic lowering. |
| `--skip-aiur-eval` | Skips Lean-side Aiur fuelled evaluation (keeps FIR evaluation) for large circuits where execution is delegated directly to the Rust prover. |
| `--no-inline`, `--pair-table`, `--stats` | Disables auto-inlining, forces the 65,536-row byte-pair table, and prints per-chip `(columns, calls, memory)` statistics. |

## Build, audit, and example commands

Build the library, CLI, and verify the axiom audit surface via `leanchecker`
(after the root workspace dependencies are present):

```sh
lake -d IxCCAiur build IxCCAiur ixcc-aiur
lake -d IxCCAiur env leanchecker IxCCAiur.Audit
```

Compile and prove an example end-to-end (pure Lean → `.ixe` + schedule → `.ixa` + `.pin.json` → STARK proof):

```sh
# 1. Compile pure Lean to Ixon closure + sidecar schedule
lake exe ix compile --no-build IxCCAiur/Examples/MultiStarkV6Pure.lean \
  --out /tmp/v6.ixe \
  --circuit-schedule-out /tmp/v6.schedule.json

# 2. Lower & optimize to Formal Aiur (.ixa + .ixa.pin.json + advice package)
lake -d IxCCAiur exe ixcc-aiur /tmp/v6.ixe \
  --root MultiStarkV6Pure.entryVerifyV6Compact \
  --args 1 \
  --typed --inline-fuse --enable-guesses --degree-budget \
  --schedule /tmp/v6.schedule.json \
  --exec -o /tmp/v6.ixa --advice-out /tmp/v6.advice.ixa --stats

# 3. Prove, verify, and run wrong-claim / wrong-hint negative controls
cargo run --release -p aiur --features parallel --example ixcc_prove -- \
  /tmp/v6.ixa --advice /tmp/v6.advice.ixa --pin /tmp/v6.ixa.pin.json
```

> **Note on `Compression/*.lean` with `ix compile --no-build`:**
> `CompressWrapPure.lean` imports `IxCCAiur.Compression.StarkWire` and
> `KzgPackedPure.lean` imports `IxCCAiur.Compression.KzgWire`. When invoking
> `ix compile --no-build`, first compile the wire module `.olean` into
> `IxCCAiur/.lake/build/lib/lean/IxCCAiur/Compression/` (`lake env lean -o ...`)
> and prepend `IxCCAiur/.lake/build/lib/lean` to `LEAN_PATH`.
