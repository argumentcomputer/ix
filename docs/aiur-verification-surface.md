# Aiur compression: verification surface

> **Historical (2026-11-15).** This document is the audit taken before the consolidation. Stop-list items 1, 2, 4, 5 (v1 and the Rust-only v2 layout path) and 8 were done, and item 6 for the packed policy; see §5 of [aiur-compression-architecture.md](aiur-compression-architecture.md).

Status: audit, 2026-11-15. Read-only inventory of the worktree
`ix.aiur-compression-active`: HEAD `4e27c5fcd`, its uncommitted and untracked
changes, the fork `~/repos/forks/multi-stark-shared-fixed` (uncommitted) and
`tools/gnark`.

**Policy.** Two parts may stay outside Lean:
- the cryptography layer (multi-stark/plonky3: STARK, FRI, LogUp, PCS), which
  is under separate formal verification;
- the final trusted endpoint (gnark PLONK protocol, Solidity verifier,
  Ignition SRS).

Everything else that the verifier or the statement depends on should be
defined in Lean, so that ixcc (Lean → x86) eventually runs it with no trusted
Rust or Go stage. Witness generation, GPU kernels and prover scheduling are
not soundness-relevant: a wrong witness only fails verification.

**Classes.**
- **A**: move to Lean (Lean defines it; the exporter or ixcc runs it).
- **B**: part of the crypto layer. Each new B item is a TODO for the
  cryptography FV effort.
- **C**: delete (scaffolding, prototype, diagnostics).
- **D**: stays trusted.
- **P**: prover-only (completeness or performance). It does not affect
  soundness and can stay in Rust, CUDA or Go.

"New" means uncommitted or untracked in the worktree. "Pre" means on HEAD.

## 1. How a statement is made, and where trust enters

1. The Lean Aiur compiler (proved: `Aiur/Aiur/Audit.lean`) emits a `.ixa`
   artifact: bytecode, chips (constraints, sends, memory, enables) and
   groups.
2. Rust decodes the artifact. It lowers the chips and groups to multi-stark
   `CircuitInputs` (the receive, `(1−sel)·mult`, sends and ROM lookups:
   `Bridge.lower` in Lean terms), and builds table, ROM and template circuits.
3. Rust serializes those circuits, with their fixed commitments, into **key
   bytes**. These include the constraint graphs (`kzg_packed_advice::key_bytes`
   writes nodes, zeros and lookups). Policies pin the key digests, so the key
   bytes *are* the verified relation. Whatever Rust puts there is what the
   chain proves.
4. The Aiur verifier programs (`MultiStark/`, Lean source, proved compiler)
   parse the key, verify the predecessor, and fold the deferred pairings.
5. Rust (`plonk.rs`) exports the terminal execution to a JSON schema. Go
   (`tools/gnark`) lowers that schema to sparse PLONK gates, LogUp and the
   pairing gadget. gnark proves it, and Solidity verifies it.

Steps 2, 3 and 5 are the unverified non-crypto surface. Step 4 is in Lean,
but no theorem says the programs implement the verifiers: there is no
`theorem` anywhere under `MultiStark/`.

## 2. Inventory

### 2.1 Lowering, circuit construction and keys (Rust)

| Item | Path(s) | LoC | What it does | Soundness | New/Pre | Target |
|---|---|---:|---|---|---|---|
| Artifact decoder | `crates/aiur/src/artifact.rs`, `artifact/{pool,wide}.rs`, `ixon.rs` | 2,210 | Parses the Lean `.ixa` (chips, polys, groups, tables) | **Yes.** A parse bug changes the circuit | Pre | A, by removal: Lean emits final circuits and keys, so Rust stops parsing chips for the statement |
| FRI and wide lowering | `crates/aiur/src/trace/stark.rs` (build/assemble), `stark/{tables,rom,grouping}.rs`, parts of `planning.rs` | ~1,100 relevant of 2,250 | Chip and group → multi-stark circuits, fixed-table and ROM circuits, for the IxVM root, CompressWrap and CompressGL | **Yes.** This is the "Rust lowering to multi-stark" trusted item of `aiur-compression.md` §5 | Pre | A: Lean `Bridge.lower` plus a grouping lowering, exported as circuits |
| KZG lowering | `proof-compression/src/aiur_backend/kzg.rs` (`Compiler::inputs`), `kzg/circuits.rs` | 902 | The same lowering for BN254, with lookup-group and quotient choices | **Yes** | Pre, modified | A, same pass as the FRI lowering. Lookup grouping is a layout choice the Lean side must then check |
| Template v2 circuit build | `aiur_backend/template/v2.rs` (`narrow_circuit`, `stacked_circuit`, `inputs_with`, buses, offsets) | ~700 of 2,087 | Builds the shard, stacked-table and ROM circuits from the Lean layout. Lean plan §5f calls this "Rust circuit construction" | **Yes.** It is not checked against `Periodic.narrowCircuit` or `Stacked.circuit` | New | A: Lean emits the multi-stark circuits (expressions, lookups, shared slot list) directly |
| Template v2 lowering, numbering and validation | `template/v2.rs` (`lower`, `compress_bodies`, `id_offset`, `global_id`) | ~900 | Rust prototype of the v2 tiling. In production the layout comes from `tiling_export2` | Redundant. Lean is the source; `--lean-reference` is a cross-check | New | C for the layout path. Keep only witness placement (P) |
| Template v2 witness and admission | `template/v2.rs` (`witness*`, `admit`, `claims`, `cells_of`) | ~450 | Places the narrow witness and rejects executions over capacity | No (P) | New | P. Later ixcc-able, not required |
| Lean bridge input | `template/v2/lean.rs` | 499 | Writes `ix-tiling-v2-input-1` (graphs from Rust `compile_graph`) and reads the layout | **Yes.** The theorem covers the graphs Rust supplies; `Bridge.lower` agreement is trusted | New | A: `TilingExport2` reads the `.ixa` and applies `Bridge.lower` itself |
| Template v1 prototype | `template.rs`, `template/lower.rs`, `template/lean.rs` | 2,761 | v1 layout and its Lean-v1 path. Superseded by v2 | Not on the production path | New | C, once the differential tests move to v2 |
| Key writers | `kzg_advice.rs` (`IXAUKY01`, `IXAUKL01`, `IXAUCL01`, `IXAUPF01`), `kzg_packed_advice.rs` (`IXAUSK02`, tags 0/1/2, copies; `IXAUSP01`) | 798 | Serialize keys (pinned) and proofs (witness) | **Key bytes: yes.** Proof bytes: no | Pre and new | A for key bytes (Lean emits them, minus the commitments). P for proof bytes |
| Fixed-column commitments | `kzg/pcs.rs` (commit paths), `kzg/cuda/*`, multi-stark setup | — | Compute the key's fixed commitments | **Yes**, but deterministic and recomputable | Pre | D. Reproducible key generation; require an independent CPU recompute at release |

### 2.2 Statements, policies and admission

| Item | Path(s) | LoC | What it does | Soundness | New/Pre | Target |
|---|---|---:|---|---|---|---|
| CompressWrap statement | `stark-verifier/src/compress_wrap.rs` (`Statement`, `preimage`, `arguments`, `decode_claims`) | ~200 | Root key and claims → the 16-word public argument | **Yes.** Defines what the final two limbs mean | Pre | A: a Lean definition, plus a lemma that the Aiur program binds it |
| Wrap layout, normalization and admission | `compress_wrap.rs` (`Layout`, `plan_capacities`, `admit`, `validate_layout`, `check_normalized_shape`), `compress_wrap_cli.rs`, `compress-wrap/*.json` | ~420 | Pads the wrap to fixed capacities, and rejects roots that do not fit | No. "CompressGL itself accepts any shape"; the layout digest only selects a key | New | P. The layout digest bytes are A if any verifier pins them |
| `WrapPolicy` | `aiur_backend/compress_gl.rs` | ~120 | Root statement → CompressGL statement, artifact, key and layout pins | **Yes** (statement mapping) | New | A |
| Packed policies | `compress_bn/packed.rs` (`IXAUKP01`, `IXAUKG01`), `compress_bn.rs`, `pairing/final_program.rs` (`Configuration`, anchors, terminal coordinates) | ~1,000 | Build the pinned policy, anchors and claim chunk headers | **Yes.** They define the constants the terminal embeds. The in-circuit parsers are Lean | New and pre | A: the Lean exporter computes them. Rust only carries bytes |
| Chain formats | `aiur_backend/chain.rs` (`IXAUCH01`), `crates/ffi/src/aiur_chain.rs` (`IXAUCH02`) | 762+ | Host chain orchestration and saved artifacts | Mostly P. Any claim assembly in them is A | Pre | P, and audit the claim assembly |

### 2.3 Aiur verifier programs (Lean, compiled by the proved compiler, unproved)

| Item | Path(s) | LoC | Soundness | New/Pre | Target |
|---|---|---:|---|---|---|
| Per-column KZG verifier | `MultiStark/MultiStark/BN/Kzg{Algebra,Blake3,Deserialize,IO,Msm,Pcs,Shape,Transcript,Verifier}.lean` | ~4,000 (+800/−?, modified) | **Yes** | Pre, modified | A: program correctness, i.e. refinement to a Lean spec of the multi-stark verifier that the crypto FV models |
| Packed verifier | `BN/KzgPacked{Deserialize,Shape,Verifier,Program,Terminal}.lean`, `KzgPcsPacked.lean` | 1,265 | **Yes** | New | A (program) on top of B (protocol) |
| Recursion and fold | `CompressBN.lean`, `CompressBNPacked.lean`, `KzgAccumulator.lean` | ~600 | **Yes** | New and pre | A (program) on top of B (§4a argument) |
| Terminals | `CompressFinal.lean`, `CompressFinalPacked.lean`, `CompressFinalNarrow.lean` | ~500 | **Yes** | New | A |
| FRI verifier | `CompressGL.lean`, `Modules/*` | ~2,000 | **Yes** | Pre | A |
| Combined-coefficient overlay | `BN/KzgPcsCombined.lean`, `Examples/KzgCombined.lean`, `tests/aiur_kzg_combined.rs` | 848 | Opt-in, not adopted | New | **C** |
| Tiling pass and exporters | `Aiur/Aiur/Tiling/*` (41 files, about 13.3k lines, 415 theorems, no `sorry`); `Examples/TilingExport{,2}.lean` | 13,900 | Proved except for `enables` and the inputs listed in §5f | New | A, done. Remaining: the `enables` certificate, and reading the `.ixa` instead of Rust graphs |

### 2.4 Final circuit: Aiur → PLONK (Rust and Go)

| Item | Path(s) | LoC | What it does | Soundness | New/Pre | Target |
|---|---|---:|---|---|---|---|
| Schema exporter | `aiur_backend/plonk.rs`, `plonk/gnark.rs` | 720 | Trace plan → fixed-capacity schema (constraints, lookups, fixed tables, publics) | **Critical** | Pre, modified | A: Lean emits the schema from the artifact |
| Exact capacities | `plonk.rs` `capacity` check; `aiur_plonk.go` `validate` | ~20 | Allows non-power-of-two rows for dynamic circuits | **Critical.** It changes the next-row cycle (`(row+1)%rows`) and the first/last selectors away from the STARK semantics the theorems assume. Only the comment argues soundness | **New** | See §4. Restrict and prove, or revert |
| Unused-map removal | `plonk/unused_maps.rs`, `aiur_plonk_unused_maps_test.go` | 364 | Drops unrequested fixed-map pulls and adds weight = 0 | Yes. Sound by a monotonicity argument, but unproved. Opt-in | **New** | C now. A later, if wanted, as a Lean schema pass with its lemma |
| Gate lowering | `tools/gnark/aiur_plonk_lower.go` | 609 | Affine forms, sparse gates, product-atom fusion, coefficient scaling | **Critical.** This is the final circuit | **New** (replaces the direct `api.Add`/`Mul` walk) | A: Lean emits the gate list, with a proof that the gates hold iff the constraints hold. Go only loads it. Interim: keep a mode that compares it with the old per-node path |
| Circuit, LogUp and challenge | `aiur_plonk.go`, `aiur_plonk_lookup.go` (shared bases, grouping), `aiur_plonk_blake3.go` | 485 | Row constraints, signed LogUp, BLAKE3-derived β | **Critical** | Pre, modified | A: the LogUp-in-PLONK composition proved in Lean. The challenge derivation is B-like Fiat–Shamir and goes on the FV list |
| Pairing binding | `aiur_plonk_pairing.go` | 115 | Binds 18 private words to gnark `PairingCheck` with the fixed anchors | **Critical** | Pre | A for the binding. D for gnark's `PairingCheck` gadget |
| Counts, census and limits | `aiur_plonk_counts.go`, `*_census_test.go`, `*_limits_test.go` | ~300 | Measurement | No | Pre and new | C, or keep as tests |
| CUDA PLONK prover limits | `cuda/plonk/{plonk.cu,ix_plonk_bn254.h}`, `internal/cuda/accelerator.go` | ~10 changed | MSM `2^24→2^25`, quotient `m ≤ 2^27`, `N ≤ 2^25` | No (P). The prover is not the verifier | New | P. Not a crypto-FV item |

### 2.5 Crypto layer (B): new functionality in this branch

Each row is kept and recorded as a TODO for the cryptography FV effort.

| Item | Path(s) | LoC | Soundness note | Kept because |
|---|---|---:|---|---|
| Packed SHPLONK PCS (packing plus BDFG batch opening) | `kzg/shplonk.rs`, `kzg/packed_shplonk{.rs,/config.rs,/layout.rs}`; Lean `KzgPcsPacked.lean` | 1,488 Rust + 331 Lean | `aiur-packed-kzg-soundness.md` §1–§3 | User decision. Per-column KZG is out of range (66.2M constraints) |
| Shared fixed slots | fork `src/{system,prover,verifier}.rs` (+194/−68); key tag 2 in `IXAUSK02`; `KzgPackedShape`/`Deserialize` | ~300 | `aiur-template-backend.md` "Soundness of sharing" (one global ζ, equal heights, one opening) | A genuine improvement: 42 fixed packs and 84 openings fewer, about 5–8M terminal constraints. The fork is used through a CLI `[patch]`; Cargo pins upstream `bcf3fc8` |
| Transcript-derived fold weight | `CompressBNPacked::fold_weight`; native `kzg_advice::transcript_fold_challenge`, `packed_shplonk::capture_verification` | ~150 | `aiur-packed-kzg-soundness.md` §4a | A genuine improvement: it drops the BLAKE3 over the proof bytes. Stage one keeps the per-column fold, so two fold rules now exist |
| Deferred-pairing accumulation (`acc = cur + w·prev`) | `KzgAccumulator.lean`, `CompressBN*.lean` | — | `aiur-compression.md` §3.2 | Pre. Outside multi-stark, so it needs explicit FV scope |
| Packed copies (sharding) | `IXAUSK02` copy counts; `tests/aiur_kzg_sharding.rs` | — | `aiur-packed-kzg-soundness.md` §4 "Circuit copies". This is a lowering lemma, not crypto | A (Lean lemma). `PeriodicStacked` already covers the narrow shards |

The pre-existing per-column KZG PCS (`crates/proof-compression/src/kzg`,
about 12k lines with CUDA) is Ix code, not plonky3. Confirm that it is in the
FV scope.

## 3. Migration plan, by soundness impact

| # | Step | Removes | Effort |
|---:|---|---|---|
| 1 | **The final circuit in Lean.** Lean defines the PLONK constraint system from the `.ixa`: gate list, wiring, LogUp with the BLAKE3 β, the pairing-binding interface. Prove: gates satisfied ⇒ the Aiur constraint semantics (reuse `Tiling/Sound` gate-lowering lemmas; the form-level lowering is the same shape as `Lower.lean`). Go becomes a loader into gnark's builder | `plonk.rs`, `aiur_plonk*.go` from the trust base. This is the last circuit; nothing re-checks it | 6–10 weeks (Lean ~4–6k lines) |
| 2 | **Lean emits the circuits and key bytes** for every stage: `Bridge.lower` plus grouping for the wide stages, and `Periodic.narrowCircuit`/`Stacked.circuit` serialized as `IXAUSK02` (with slots and copies) for the narrow stage. Rust adds only the commitments | Rust lowering (`trace/stark.rs`, `kzg/circuits.rs`, `template/v2.rs` circuit build, `v2/lean.rs`), the artifact decoder on the statement path, the key writers | 4–6 weeks |
| 3 | **Statements and policies in Lean**: `CompressWrap` statement, `WrapPolicy`, `IXAUKP01`/`IXAUKG01`, anchors, claim headers. The exporter computes and embeds them, with lemmas that each Aiur entry binds them | Rust policy builders | 2–3 weeks |
| 4 | **The `enables` certificate**, the last assumption of `narrow_heap_sound_stacked` | Lean plan §4 | 1–2 weeks |
| 5 | **Program correctness of the verifier programs**: KZG/packed verifier, transcript, deserializers, fold and terminals refine a Lean verifier spec. The spec must be the interface the crypto FV proves sound | The largest Lean-but-unproved surface | 3–6 months. Start with the deserializers and the transcript, which are mechanical |
| 6 | **Reproducible key generation**: an independent CPU recomputation of the fixed commitments and key digests at release | GPU commit trust (D) | 1 week |
| 7 | **The ixcc switch**: exporters and witness generation run from Lean | Rust as production code | Depends on ixcc |

The crypto FV TODOs are separate from this plan and run in parallel: packed
SHPLONK, shared fixed slots, the transcript fold, deferred accumulation, the
BLAKE3 Fiat–Shamir challenges, and the scope of the per-column KZG.

## 4. Stop or revert now

1. **Non-power-of-two PLONK capacities** (`plonk.rs`, `aiur_plonk.go`
   `validate`). They change the row-cycle semantics of the final circuit, and
   only a comment argues soundness. Revert, or restrict to circuits with no
   next-row or selector reads (a checkable condition with a trivial argument).
   Power-of-two capacities still fit `2^25` (29.36M).
2. **Unused-map receiver removal** (`plonk/unused_maps.rs`). It is an
   opt-in optimization of the trusted final schema. Drop it until it exists
   as a proved Lean pass.
3. **New Go gate lowering** (`aiur_plonk_lower.go`). Do not grow it further.
   Make step 1 the place where gate optimizations live. Until then, gate it
   behind an equivalence check against the per-node path.
4. **The combined-coefficient KZG overlay** (`KzgPcsCombined.lean`,
   `kzg_combined_export`, `aiur_kzg_combined.rs`). Not adopted; delete.
5. **The Rust v1 template and the v2 layout prototype** (`template.rs`,
   `lower.rs`, `template/lean.rs`, the `v2.rs` lowering). Lean is the source
   now. Keep only witness placement.
6. **Key-format variants.** Keep one fixed-section form per key grammar
   (tag 2 when sharing), and one fold rule where possible. Each variant is a
   further in-circuit parser to prove.
7. **No further crypto-layer changes**, and keep the fork's slot change
   minimal. Do not build the conditional narrow Goldilocks FRI stage (target
   pipeline step 3) unless the decision gate forces it.
8. **The diagnostic examples** (`crates/proof-compression/examples/aiur_*`,
   `*_packed_*`; about 5k lines, untracked). Keep them out of the library.
   Delete them after the measurements are recorded.
