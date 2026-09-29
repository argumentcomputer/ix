# Development and validation

Use the [roadmap](roadmap.md) to choose a work package and the
[design reference](compiler-design.md) for its architectural constraints.
This guide covers implementation, validation, and documentation maintenance.
The [benchmark design](benchmark-plan.md) owns comparison rules.

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
   [the axiom fences](../CompilatrixTests/Fences.lean) and preserve the existing axiom
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
environment. The required integration gate is:

```sh
nix flake check
```

The [CI guide](ci.md) lists its checks, the shared program build, the
coverage inventory and the coverage-change record. During development:

- Build the affected targets: `nix develop -c lake build <targets>`.
- Build every program and the proof collection:
  `nix develop -c lake build CompilatrixTests.Proofs <executables>`.
- Run the focused suites for the area: `lake exe tests-ixon-v3`,
  `lake exe check-ixon-v3 …`, `lake exe check-ixon-v3-catalog …`,
  `lake exe tests-aiur`, and the x86 checks `check-x86-encoder`,
  `check-x86-bytes`, `check-x86-streams` and `check-x86-object`.
- After changing imports or Lake roots, run
  `lake exe check-build-graph --write` and review the manifest. After a
  reviewed fence or assertion change, regenerate the coverage inventory
  with `--write-coverage` (see the CI guide).
- After changing an integrity-pinned file, review and update its pin in
  `docs/trusted-externs.json`, then run `check-trusted-externs` and
  `check-tools-tests`.

The former complete surface, including every family gate and its command,
is documented on branch `jcb/ixby-archive`.

Compiler-comparison and measurement runners live in an optional package outside
the root flake; they are being rebuilt for the new benchmark ladder. CakeML
and CompCert stay outside the CI check closure.

Elaboration-time guards run in the build. Compiled gates check native ABI and
object behavior, complete fresh-process artifacts, independent corruption
rejection, and the trust auditor. The focused contracts in the
[documentation guide](README.md) describe each gate's domain and theorem
fences. Inspect output before reporting native platform coverage.

Run checks appropriate to the changed boundary, followed by the required
integration gate. Documentation-only changes need link, anchor, and consistency
checks. An integrity-pinned input also needs its reviewed digest update and the
trust check. Report cached builds, clean builds, Nix validation, and platform
coverage accurately. Ordinary CI checks compiler correctness and artifacts.
Changes to the optional comparison package also require its explicit
correctness, smoke, analysis, and replay commands. Timing thresholds require a
controlled performance host.

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
