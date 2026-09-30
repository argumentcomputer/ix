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
