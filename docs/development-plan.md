# Development and validation

Use the [roadmap](roadmap.md) to choose a work package and the
[design reference](compiler-design.md) for its architectural constraints.
This guide covers implementation, validation, and documentation maintenance.
The [benchmark protocol](../benchmarks/protocol.md) owns measurement commands.

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

For the configured local development environment, the complete build and
compiled regression surface is:

```sh
lake build Compilatrix tests catalog-contact x86-object-fixture \
  source-coverage source-recursion source-call-reuse source-unique-reuse \
  source-native-unique source-native-runtime source-native-allocating source-native-upstream source-native-scalar \
  source-native-physical-scalar source-native-captured-scalar source-borrow source-borrow-runtime \
  check-trusted-externs check-x86-encoder check-x86-bytes check-x86-streams \
  check-x86-object check-source-coverage check-source-recursion \
  check-source-call-reuse check-source-unique-reuse \
  check-source-native-unique check-source-native-runtime check-source-native-allocating check-source-native-upstream check-source-native-scalar \
  check-source-native-physical-scalar check-source-native-captured-scalar check-source-borrow \
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
./.lake/build/bin/check-source-native-allocating \
  --fixture .lake/build/bin/source-native-allocating \
  --readelf readelf --objdump objdump --cc cc \
  --harness fixtures/source-native-allocating/native_harness.c
./.lake/build/bin/check-source-borrow --fixture .lake/build/bin/source-borrow
./.lake/build/bin/check-source-native-upstream \
  --fixture .lake/build/bin/source-native-upstream \
  --cc gcc --harness fixtures/source-native-upstream/native_harness.c
./.lake/build/bin/benchmark analysis-self-check
./.lake/build/bin/check-source-native-scalar \
  --fixture .lake/build/bin/source-native-scalar \
  --cc gcc --harness fixtures/source-native-scalar/native_harness.c
./.lake/build/bin/check-source-native-physical-scalar \
  --fixture .lake/build/bin/source-native-physical-scalar \
  --cc cc --harness fixtures/source-native-physical-scalar/native_harness.c
./.lake/build/bin/check-source-native-captured-scalar \
  --fixture .lake/build/bin/source-native-captured-scalar \
  --cc cc --harness fixtures/source-native-captured-scalar/native_harness.c
./.lake/build/bin/check-source-borrow-runtime --fixture .lake/build/bin/source-borrow-runtime
```

Elaboration-time guards run in the build. Compiled gates check native ABI and
object behavior, complete fresh-process artifacts, independent corruption
rejection, and the trust auditor. The focused contracts in the
[documentation guide](README.md) describe each gate's domain and theorem
fences. Inspect output before reporting native platform coverage.

Run checks appropriate to the changed boundary, followed by the required
integration gate. Documentation-only changes need link, anchor, and consistency
checks. An integrity-pinned input also needs its reviewed digest update and the
trust check. Report cached builds, clean builds, Nix validation, and platform
coverage accurately. Ordinary CI checks benchmark correctness and runner
behavior; timing thresholds require a controlled performance host.

## Documentation maintenance

- Keep the root README focused on purpose, current scope, setup, and navigation.
- Keep priorities and acceptance gates in the roadmap. On delivery, replace the
  plan with a compact scoped record linked to its contract or result.
- Put syntax, invariants, public APIs, and remaining restrictions in the focused
  specification. Replace superseded proof-progress paragraphs when the proof
  lands; keep implementation detail in source and theorem references.
- Keep commands in this guide, the relevant source-family gate, or the benchmark
  protocol. Link to them from overviews instead of repeating test inventories.
- Preserve dated reviews and retained performance evidence as historical
  records. New results get a new version; current status belongs in the roadmap.
- Update the documentation index and check relative links/anchors when adding,
  moving, or removing a page. Keep machine-readable identities and integrity
  pins separate from editorial changes.

## Build troubleshooting

Crane's Rust build helper downloads its locked crates directly from
`static.crates.io`. The flake overrides that helper's Nix Cargo fetcher because
the crates.io API download route can reject CI requests with HTTP 403. The
override preserves the upstream lockfile, crate checksums and TLS verification;
it leaves the helper and Blake3 library output paths unchanged. A cached local
check may conceal a failed source download. Use `nix build --rebuild` on the
named fetch derivation to exercise the download itself while still allowing
its build tools to come from the binary cache.
