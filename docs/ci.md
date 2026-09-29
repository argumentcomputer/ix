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
