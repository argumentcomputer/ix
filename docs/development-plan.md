# Development and validation

The [roadmap](roadmap.md) is the single source for priorities, state, and
acceptance criteria. This guide describes how to implement and verify those
packages. [Compiler design](compiler-design.md) records the enduring decisions;
focused specifications own executable contracts and detailed theorem evidence.
The [benchmark plan](benchmark-plan.md) defines native comparisons, compiler
cost measurements, reproducible result bundles, and performance regression
practice; its delivery gates live in the roadmap. The [first full reference](performance/native-reverse-2026-09-09/README.md)
records PERF1/C3 results, limitations, retained artifacts, and replay commands.

## Landing a work package

Begin with the package's observable exit and exact source/target domain.
Extend the existing checked entry point and public theorem interfaces where
possible. Record source origin, accepted fragment, selected artifact,
fallback behavior, and any remaining assumptions together.

For a new theorem-backed boundary:

1. Reuse local operation, heap, ownership, and continuation interfaces;
   compose them through the actual checked transformation and address rebuild.
2. Derive compiler invariants internally. State genuine source/environment
   premises explicitly; do not turn the missing simulation into a caller
   callback or substitute a theorem about a hand-built target.
3. Expose semantic preservation, resource/cost laws, and native byte/runtime
   guarantees at their respective boundaries. Add public results to
   [the axiom fence](../Compilatrix/Fence.lean) and preserve the existing axiom
   basis unless a deliberate trust change is part of the package.
4. Exercise a non-degenerate input at the claimed entry point, checked
   fallback, and the negative boundaries affected by the extension.
   Artifact checks should reject invalid evidence even when two fresh
   processes produce the same corrupted artifact.
5. Update the focused specification, restriction/trust ledger when affected,
   and the roadmap's scoped delivery record. Remove superseded planning
   narratives once their enduring constraint is captured.

Optional optimizer rejection retains the last checked artifact. Invalid
source remains an error. Keep analysis/check time, artifact/code growth, and
actual runtime or resource measurements attached to optimization claims.

Keep proof maintenance bounded to the extension that needs it. Extract
reusable heap algebra, compiler history, accepted-site composition, and
public wrappers behind narrow interfaces; preserve theorem names through
imports/aliases where practical. Measure elaboration cost before choosing
performance refactors. Do not add native reflection axioms to discharge
encoder or compiler correctness.

## Validation commands

Use the Lean version pinned in `lean-toolchain` and the repository's Nix
environment. The CI gate is:

```sh
nix flake check
```

Crane's Rust build helper downloads its locked crates directly from
`static.crates.io`. The flake overrides that helper's Nix Cargo fetcher because
the crates.io API download route can reject CI requests with HTTP 403. The
override preserves the upstream lockfile, crate checksums and TLS verification;
it leaves the helper and Blake3 library output paths unchanged. A cached local
check may conceal a failed source download. Use `nix build --rebuild` on the
named fetch derivation to exercise the download itself while still allowing
its build tools to come from the binary cache.

For the configured local development environment, the complete build and
compiled regression surface is:

```sh
lake build Compilatrix tests catalog-contact x86-object-fixture \
  source-coverage source-recursion source-call-reuse source-unique-reuse \
  source-native-unique source-native-runtime source-native-upstream source-borrow source-borrow-runtime \
  check-trusted-externs check-x86-encoder check-x86-bytes check-x86-streams \
  check-x86-object check-source-coverage check-source-recursion \
  check-source-call-reuse check-source-unique-reuse \
  check-source-native-unique check-source-native-runtime check-source-native-upstream check-source-borrow \
  check-source-borrow-runtime check-tools-tests benchmark
./.lake/build/bin/tests
./.lake/build/bin/check-trusted-externs --root .
./.lake/build/bin/check-tools-tests --root .
./.lake/build/bin/check-x86-encoder --objdump objdump
./.lake/build/bin/check-x86-bytes
./.lake/build/bin/check-x86-streams
./.lake/build/bin/check-x86-object \
  --fixture .lake/build/bin/x86-object-fixture \
  --readelf readelf --objdump objdump --cc cc \
  --harness fixtures/x86/native_harness.c
./.lake/build/bin/check-source-coverage \
  --fixture .lake/build/bin/source-coverage \
  --cc cc --harness fixtures/x86/native_harness.c
./.lake/build/bin/check-source-recursion --fixture .lake/build/bin/source-recursion
./.lake/build/bin/check-source-call-reuse --fixture .lake/build/bin/source-call-reuse
./.lake/build/bin/check-source-unique-reuse --fixture .lake/build/bin/source-unique-reuse
./.lake/build/bin/check-source-native-unique \
  --fixture .lake/build/bin/source-native-unique \
  --readelf readelf --objdump objdump --cc cc \
  --harness fixtures/source-native-unique/native_harness.c
./.lake/build/bin/check-source-native-runtime \
  --fixture .lake/build/bin/source-native-runtime \
  --readelf readelf --objdump objdump --cc cc \
  --harness fixtures/source-native-runtime/native_harness.c
./.lake/build/bin/check-source-borrow --fixture .lake/build/bin/source-borrow
./.lake/build/bin/check-source-native-upstream \
  --fixture .lake/build/bin/source-native-upstream \
  --cc gcc --harness fixtures/source-native-upstream/native_harness.c
./.lake/build/bin/benchmark analysis-self-check
./.lake/build/bin/check-source-borrow-runtime --fixture .lake/build/bin/source-borrow-runtime
```

Elaboration-time guards run in the build. The compiled gates cover native
boundaries, encoder/object oracles, complete fresh-process source artifacts,
independent corruption rejection, and the trust auditor's own regressions.
The [R6 credit fixtures](credit-refinement.md#regression-and-trust-boundary)
are imported by `Compilatrix.lean`; `lake build Compilatrix` checks their
whole-trace comparisons and the ten public credit-refinement axiom fences.
The [C2 coverage gate](source-coverage.md) includes three accepted upstream
closures, two upstream negative neighbors, and the reviewed Std transition.
The build checks the fresh-closure classifier's two axiom fences; the compiled
gate checks all 18 source cases and their complete artifacts in fresh processes.
The [C3 native gate](source-native-upstream.md) checks two unchanged computational
ELF objects, source/physical results and complete release, structural/overflow
negatives, independent reconstruction, and call-stack/ABI conditions. The six
new axiom fences retain the existing logical/hash basis. The [benchmark
protocol](../benchmarks/protocol.md) documents all six adapters, full correctness,
short smoke/schema rejection, reference measurement, and independent replay.
The first reference passed all 805 Lake jobs, 17 compiled validation commands,
and 19 Nix checks on x86_64 Linux before measurement. Its 30 paired blocks
cover every required baseline and both closed upstream native entries. A fresh
source/environment replay rebuilt identical artifacts and executables, reran
full correctness, and regenerated the analysis byte for byte; archive extraction
and relocated analysis also passed. These results and their logs are retained
in the linked reference. Ordinary CI keeps correctness and runner checks;
performance thresholds await history from a controlled host.
The [N2 runtime gate](source-native-runtime.md) compiles and emits once per
producer process, compares complete fresh artifact sets, and links one object
pair for eight runtime inputs and 203 malformed-input calls. Its source/native
interfaces and exact-Word adapter are checked by the axiom fence.
The [B1 borrowed-call gate](source-borrow.md) checks 18 accepted source chains,
complete source/compiler artifacts, independent caller/callee reconstruction
and heap replay, three checked source fallbacks, twelve boundary negatives,
and thirteen artifact corruptions. Ten axiom fences cover checked rewriting,
finite execution, source/result/resource agreement, and exact fallback.
The [B2 runtime-borrow gate](source-borrow-runtime.md) checks nine source
functions compiled before their arguments, 144 independent direct/PAP
comparisons, nine aliased lenders, four exact source fallbacks, eight
structural/lifetime guards, all twelve B1 negatives, and twenty artifact
corruptions. Fifteen new fences cover the universal source/function/continuation
proofs, input ownership, reclamation, RC/peak laws, and exact fallback.
Native execution checks apply on supported hosts; inspect the check output
before reporting platform coverage.

During implementation, run checks appropriate to the changed boundary, then
the required integration gate for delivery. Documentation and comment-only
changes need link/consistency checks; changing an integrity-pinned file also
requires a reviewed digest update and the trust check. Do not report a local
cached build as a clean build, a full Nix gate, or cross-platform validation.
