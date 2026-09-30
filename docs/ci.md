# CI builds and required coverage

**Status, 2026-09-29.** Compilatr.ix is rebuilding its compiler around Ixon v3
and a general x86 backend.
- Every check `nix flake check` ran was removed in one recorded coverage
  change.
- The checks for the kept foundations are back.
- Further gates return one at a time as the new pipeline needs them.

The removed surface, with its code and its last passing run, is preserved on
branch `jcb/ixby-archive` at `7599a43`. There, `nix flake check` passed all 44
checks in 15 min 38 s at `--max-jobs 2`, with no `--accept-flake-config`.
Hosted GitHub runs had already been disabled, and the workflow was removed
with the checks.

## Current surface

`nix flake check` runs the checks defined in `flake.nix` and
[`nix/checks.nix`](../nix/checks.nix). The builds they share:
- **`build`** is the production library.
- **`proofs`** builds every executable and the complete proof and fence
  collection (`CompilatrixTests.Proofs`) once, reusing the library's
  artifacts. Every other check runs those programs against the full tracked
  source tree.

| Check | Runs |
| --- | --- |
| `ixon-v3` | `tests-ixon-v3`; `check-ixon-v3` on the handoff fixture; `check-ixon-v3-catalog` on the fat and chunked catalogs |
| `aiur` | `tests-aiur`; `check-aiur` |
| `x86-encoder-decoder` | `check-x86-encoder` against GNU objdump |
| `x86-byte-execution` | `check-x86-bytes` |
| `x86-stream-objects` | `check-x86-streams` |
| `x86-elf-object` | `check-x86-object` with readelf and objdump; on x86-64 Linux, native link and run |
| `trusted-extern-ledger` | `check-trusted-externs` against the pinned Blake3 source and GMP version; `check-tools-tests` |
| `build-graph` | `check-build-graph`: the module manifest, production-import hygiene, and the proof, fence and runtime coverage inventory in [`nix/ci-coverage.json`](../nix/ci-coverage.json) |
| `census` | `census` on the K1 pack and on the five K1 benchmark closures in [`fixtures/ixon-v3/bench-k1`](../fixtures/ixon-v3/bench-k1/README.md); each report must equal its reviewed baseline (for example [`fixtures/ixon-v3/k1/census.json`](../fixtures/ixon-v3/k1/census.json)) |
| `x86-hardware` | x86-64 Linux only: `check-x86-hardware` enumerates `Op.rows` and runs 53,279 generated cases natively, compares them with `ByteEval`, and checks `llvm-mc` decodes each identically |

After changing imports or Lake roots, regenerate the manifest with
`lake exe check-build-graph --write`.

After a reviewed change to fences, proof modules or runtime assertions,
regenerate the coverage inventory:

```sh
lake exe check-build-graph --write-coverage "COMMIT: reason"
```

Review the diff before committing; the inventory exists to make coverage
changes visible.

## Coverage change record

| Date | Change | Checks |
| --- | --- | --- |
| 2026-09-29 | Removed the complete required surface | `build`, `proofs`, `build-graph`, `ci-workflow`, `trusted-extern-ledger`, `tests`, `catalog-contact`, `x86-encoder-decoder`, `x86-byte-execution`, `x86-stream-objects`, `x86-elf-object`, `source-coverage`, `source-recursion`, `source-call-reuse`, `source-space`, `source-modular`, `assembly-scaling`, `source-evidence`, `ixir2-identity`, `source-unique-reuse`, `source-borrow`, `source-borrow-runtime`, `source-native-{unique,runtime,allocating,upstream,scalar,physical-scalar,heap,captured-scalar}`, `native-sharing`, `native-graph`, `aiur`, `ixby`, `ixby-symbolic`, `ixby-stage2`, `ixby-lean`, and eight `ixby-stage2-binary-*` checks |
| 2026-09-29 | Restored the kept foundations | `build`, `proofs` (387 exact axiom assertions), `ixon-v3` (new; its suite was part of the former `tests`), `aiur`, `x86-encoder-decoder`, `x86-byte-execution`, `x86-stream-objects` and `x86-elf-object` (without their legacy reversal cases), `trusted-extern-ledger` (reset inventory), and `build-graph` (redefined coverage inventory) |
| 2026-09-29 | Added the admission census | `census` (new): per-constant first rejecting stage and v3 budget headroom for the K1 pack, exact match against its reviewed baseline |
| 2026-09-29 | Added the hardware-differential gate | `x86-hardware` (new): native execution and LLVM decoding of every generated case |
| 2026-09-29 | Drove x86 from one instruction table (C2) | `proofs`: 405 exact axiom assertions (from 387); 18 new x86 fences (table facts, `row_decode`, `row_execution`, `instruction_decode`, `instruction_execution`, `Compare.holds_eq`, `Decode.one_stable`, `Stream.run_pair`, `Stream.operation_pair`, three constructor well-formedness laws and two constructor semantics laws); no fence removed or renamed. `Checked.inV0` gains `Quot.sound` (well-formedness decides table membership); `Stream.run_permissions` loses `Classical.choice`. `instruction_decodeAt` and `encoded_instruction_execution` gain an `Instr.wellFormed` premise, discharged for every typed constructor and by `Program.wellFormed`; `compare_execution` states the `cmp` row in place of the retired compare operation. `x86-hardware` enumerates `Op.rows` (18,767 cases, from 11,067); `x86-byte-execution` runs 33,793 instruction cases (from 31,921); `x86-encoder-decoder` checks 30 forms and six addressing/REX edges (from 13 forms); `x86-stream-objects` runs 1,002 object corruptions/truncations (from 1,010, because the fixture objects are shorter) |
| 2026-09-29 | Extended the hardware gate (C3) | `x86-hardware`: disp32 extremes (±2³¹, with a compensating base) and input flags all clear, all set or random; 22,463 cases, 609 expected faults (from 18,767 and 87) |
| 2026-09-29 | Froze the K1 benchmark closures (Phase 1 M0.4) | `ixon-v3`: `tests-ixon-v3` also ingests, address-checks and types the five `bench-k1` closures (2,120 assertions, from 1,936); `census`: five more exact baselines |
| 2026-09-29 | Phase 1 table rows, branch producers, fused pairs and the failure exit (M1.B1) | `proofs`: 421 exact axiom assertions (from 405); 16 new x86 fences (`Op.safe_ok`, `Encode.compare_branch_bytes_execution`, `executeTerminator_compare`, `Terminator.compare_wellFormed`, `Encode.produced_flags`, `Encode.fused_execution`, `Encode.fused_decode`, `Stream.fused_progress`, `cutAt_suffix`, `Stream.FramesMapped.suffix`, `executeInstr_unwind`, `Stream.unwind_progress`, `unwind_inFrame`, `Straight.Segment.safe_unwind`, `ObjectEval.run_exit`, `StreamExamples.unwind_safe`); no fence removed or renamed and no axiom set changed. Restated: `terminator_decode` gains a `Terminator.wellFormed` premise; `instruction_decode` and `instruction_decodeAt` gain an `Instr.single` premise (a fused pair is two rows); `branch_bytes_execution`, `branch_patch` and `Stream.branch_at` take any producer row in place of a `Compare`, of which the former statements are the `Terminator.compare` instances (`compare_branch_bytes_execution` keeps the former byte law). `Form.InV0` now includes scalar division (`div`), shifts, `setcc` and `cmovcc`. `x86-hardware`: 53,279 cases, 1,382 expected memory faults and 256 `#DE`s (from 22,463 and 609), over every non-control row plus shift-count, `div`, fused-pair and producer-branch cases, with fault kinds compared by signal; `x86-byte-execution`: 55,940 instruction cases (from 33,793) and, new, 12,300 patched producer branches and 18,200 fused pairs; `x86-encoder-decoder`: 18 more forms (48); `x86-stream-objects`: new 155 producer-branch objects, 50 fused-pair objects and 9 failure-exit cases; `x86-elf-object`: a fourth fixture, `unwind`, run natively under a callee-saved sentinel harness |
| 2026-09-30 | Phase 1 IR and framework fences (M1.B2, M1.B3, M1.B5, M2.1) | `proofs`: 563 exact axiom assertions on `main` (from 421 after M1.B1): Lir operand metadata and frame lemmas (12), Xv selection lemmas including `test_self_flags`/`test_self_test` (11), stacking and layout lemmas (10: `FrameLayout.check_sound`, tunnelling chains, branch inversion), and the `Compilatrix.Sem` framework with its toy pipeline (109: clocked behaviours, `Sim.refines`/`backward`/`safe`/`comp`, `Refines`, certificate-taking `Transform.comp_correct`, `Reaches`, `Potential`, `Diagram.sim`, `Sim.ofStar`). No fence removed. The new executables (`tests-src`, `tests-src-slow`, `tests-relevance`, `check-lir`, `check-xv-select`, `check-regalloc`, `check-backend`) build in the programs derivation but are not yet run by a required check; they join in Phase 1 M3.1. |
| 2026-09-30 | Branch fall-through (M1.B5) | `proofs`: +3 exact axiom assertions (566 on `main` after the merge, from 563); new fences `Stream.branch_fall_at`, `executeTerminator_reach`, `Terminator.wellFormed_reach`; no fence removed, renamed or restated. `Terminator.branch` gains a `Reach` for its false edge (default `rel32`, so every existing statement keeps its text and now speaks of `rel32` branches); `safe_progress` keeps its one to three byte steps. `x86-stream-objects`: 100 branch objects and 310 producer-branch objects (from 50 and 155: each case also runs with its false edge falling through) and 19 stream corruptions (from 15: fall-through targets that are not the next block, and a `rel32` claim over fall-through bytes); `x86-byte-execution` also runs each patched producer branch without its `jmp` |
| 2026-09-30 | The front end's recheck path in the kernel (M1.K1) | Build-time only (the programs derivation builds `tests-lam`): `CompilatrixTests.Lam.KernelK1.Fib` evaluates `Src.Recheck.run` and erasure on the generated fib bench-k1 artifact with `decide +kernel` (11 globals, root `const 41`) and rejects nine mutations at the expected stage. Manual: `lake build CompilatrixTests.Lam.KernelK1` adds tak and gcd; `lake exe gen-src-artifacts --check` compares the committed artifacts with a fresh load. No fence changed. |
| 2026-09-30 | ELF symbols for every export (M1.B5) | `proofs`: +1 exact axiom assertion (567 on `main` after the merge); new fence `ELF.Valid.exported` (a further export resolves by name to its block's offset); no fence removed, renamed or restated (`ELF.Fields` gains an `exports` field; `ELF.Input` an `exports` list, default empty). `x86-elf-object`: a fifth fixture, `exports`, with two exported symbols checked by `readelf` and `objdump` and both called natively (`fixtures/x86/exports_harness.c`, pinned); `x86-stream-objects`: 9 further-export corruptions and mismatched export lists rejected |
| 2026-09-30 | Register-allocation validator soundness (M2.6a) | `proofs`: 982 exact axiom assertions on `main` after the merge (from 567): 415 fences in the new `CompilatrixTests.Fences.Validate`, one for each public theorem of `Compilatrix.Xv.Validate.Proof.*`, among them `Validate.sound`, `Validate.sound_final`, `Validate.program_eval_eq`, `Validate.program_sim`, `Validate.program_sound`, `Xv.eval_mono` and `Xl.eval_mono`, all with at most `propext`, `Classical.choice` and `Quot.sound`. No fence removed or renamed and no axiom set changed. The validator also rejects rows with stack traffic and narrow write-only register outputs outside a fused consumer (`Validate.rowShapeOk`), which Xl would run differently from Xv; `check-regalloc`, `check-xv-select` and `check-backend` still pass. |

| 2026-09-30 | Fir, the Phase 1 Own fragment and Cfg (M1.F5) | `proofs`: 1014 exact axiom assertions (from 982): 32 fences in the new `CompilatrixTests.Fences.Fir` (3) and `CompilatrixTests.Fences.Own` (29), one for each public theorem of `Compilatrix.Fir.*` and `Compilatrix.Own.*`, among them `Own.checkImmortal_iff` (the checker accepts exactly `Own.immortal (Own.erase q) = q`), `Own.erase_immortal`, `Own.immortal_erase` and `Own.checkImmortal_immortal`, all with at most `propext`, `Classical.choice` and `Quot.sound`. No fence removed, renamed or restated. Build-time only: `CompilatrixTests.Fir.KernelEval` (built with `tests-fir`) re-runs `Fir.lower`, `Own.immortal` and `Cfg.lower` by `decide +kernel` on the five bench-k1 entries and three small programs. `tests-fir` builds in the programs derivation and is not yet run by a required check (M3.1). |

The restored surface builds in about 2.5 minutes cold at `--max-jobs 2`,
measured with `--rebuild`: the library in 82 s, the shared program and
proof build in 44 s, and the checks in about 22 s. Blake3 and the
toolchain came from the binary cache.

Each returning gate adds a row: its date and the check it restores or
replaces.

## Rules for returning gates

- **One gate per named check** in `flake.nix`. Build shared artifacts once
  and reuse them across checks (AGENTS.md).
- **Budget:** required checks stay within 30 minutes cold on the configured
  machine. Record elapsed time and peak memory when a gate returns.
- **Exact axiom fences:** a gate that covers a public theorem also restores
  that theorem's fence, and the coverage inventory records it.
