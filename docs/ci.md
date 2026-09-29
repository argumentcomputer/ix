# CI builds and required coverage

**Status, 2026-09-29: the required check surface is empty.** Compilatr.ix
is rebuilding its compiler around Ixon v3 and a general x86 backend. Every
check that `nix flake check` ran was removed in one recorded coverage change.
Gates return one at a time as the new pipeline needs them.

The removed surface, with its code and its last passing run, is preserved on
branch `jcb/ixby-archive` at `7599a43`. There, `nix flake check` passed all 44
checks in 15 min 38 s at `--max-jobs 2`, with no `--accept-flake-config`.
Hosted GitHub runs had already been disabled, and the workflow was removed
with the checks.

## Current surface

- `nix flake check` evaluates the flake; `checks` is empty.
- `nix build` builds the production library, whose sources are selected
  through `nix/lean-modules.json`.
- After changing imports or Lake roots, regenerate that manifest with
  `lake exe check-build-graph --write`.

## Coverage change record

| Date | Change | Checks |
| --- | --- | --- |
| 2026-09-29 | Removed the complete required surface | `build`, `proofs`, `build-graph`, `ci-workflow`, `trusted-extern-ledger`, `tests`, `catalog-contact`, `x86-encoder-decoder`, `x86-byte-execution`, `x86-stream-objects`, `x86-elf-object`, `source-coverage`, `source-recursion`, `source-call-reuse`, `source-space`, `source-modular`, `assembly-scaling`, `source-evidence`, `ixir2-identity`, `source-unique-reuse`, `source-borrow`, `source-borrow-runtime`, `source-native-{unique,runtime,allocating,upstream,scalar,physical-scalar,heap,captured-scalar}`, `native-sharing`, `native-graph`, `aiur`, `ixby`, `ixby-symbolic`, `ixby-stage2`, `ixby-lean`, and eight `ixby-stage2-binary-*` checks |

Each returning gate adds a row: its date, its commit, and the check it
restores or replaces.

## Rules for returning gates

- **One gate per named check** in `flake.nix`. Build shared artifacts once
  and reuse them across checks (AGENTS.md).
- **Budget:** required checks stay within 30 minutes cold on the configured
  machine. Record elapsed time and peak memory when a gate returns.
- **Exact axiom fences:** a gate that covers a public theorem also restores
  that theorem's fence.
- **Trust audit and build-graph check:** both come back with a redefined
  inventory. Until then:
  - `check-trusted-externs` pins are not maintained;
  - `check-build-graph` check mode is dormant, because it reads the removed
    `nix/ci-coverage.json`.

**Planned first returns:**
- the Ixon v3 suite (`tests-ixon-v3`, `check-ixon-v3`,
  `check-ixon-v3-catalog`);
- the x86 E1/E2/ELF gates with their fences;
- the trust audit.
