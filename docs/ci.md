# CI builds and required coverage

`nix flake check` runs the complete required surface. GitHub runs the same
checks in groups defined in [`nix/ci-groups.json`](../nix/ci-groups.json).
[`nix/groups.nix`](../nix/groups.nix) requires every check to appear exactly
once, accounting for the two native benchmark regressions that require
x86-64 Linux. Adding a check without assigning its job fails evaluation.

The final GitHub status remains **Nix flake checks**. It succeeds only when
the shared build and every matrix group succeed. Failed or skipped groups
cannot produce a successful final status, and one failing group does not
cancel the remaining diagnostic runs.

The build job first evaluates every required Linux check's derivation with
`nix eval`. Avoid `nix flake check --no-build` for this step: it enables a
read-only store, while the Lake helper reads manifests from filtered sources
that must first be copied into the store. That command can pass with a warm
store and fail on a fresh runner. The normal `nix flake check` command builds
checks and does not have this restriction.

## Build once, then execute

The shared build has three artifacts:

1. `nix build .#compilatrix` builds the production library, including its
   static/shared facets and reusable Lake artifacts.
2. `nix build .#ci-programs` reuses those artifacts and builds every registered
   CI executable together. It retains project `.olean` and native build
   artifacts for the proof build. Its `runtime` output contains the programs
   and the oleans needed by the dynamic frontend checks.
3. `nix build .#proofs` reuses the program build and explicitly builds
   `CompilatrixTests.Proofs`, which retains the complete original proof and
   elaboration-test collection and every axiom fence.

The runtime checks in [`nix/checks.nix`](../nix/checks.nix) execute these built
programs in fresh working directories. They do not invoke `lake build`.
Native harness compilation and independent GNU/Python oracles remain part of
the checks that need them.

CI executables use the pinned Lean shared libraries through Lake's
`ciLeanLibDir` configuration option. This avoids embedding another copy of
Lean in each executable. The Nix derivation supplies the exact toolchain
library directory and records its runtime search path. The default Lake
configuration continues to produce the usual static Lean executables.

GitHub transfers only the current run's project runtime output as a compressed
Nix export. Each worker fetches the separately pinned runtime dependencies
through the configured Nix binary caches. The producer verifies that those
dependencies cover every reference in the exported artifact. Workers select
the producer's artifact ID, reject transport digest mismatches, check the
archive SHA-256, import it, and verify the expected Nix output path. No cache
signing key or repository write permission is required. Artifact sharing
follows GitHub's [same-workflow artifact mechanism](https://docs.github.com/en/actions/tutorials/store-and-share-data).

The `.lake` build cache, dependency source trees, Rust build products, and
optional comparison toolchains are outside this transfer. Build and check
logs are retained for seven days; the compiled artifact is retained for one.
The workflow stages archives and diagnostics under
`$RUNNER_TEMP/compilatrix-ci`, outside the checkout. `plans/` is reserved for
local development records.

## Source and module boundaries

[`Compilatrix.lean`](../Compilatrix.lean) exposes the production compiler API.
The production import closure has 520 local modules with the Aiur AIR checkers, combined Ixon v3 source validator and catalog-v2 admission.
Direct Nat/Word32 conversion proofs preserve this inventory and all existing
nibble-helper proof and axiom-fence coverage.
The earlier CI refactor reduced that closure from 593 to 425 modules. It does
not import test modules, example suites, fixture corpora, or fence aggregators.

The five core runtime suites have independent entry points:

| Suite | Direct command |
| --- | --- |
| Addressing, codecs, and cross-IR checks | `lake exe tests-addressing` |
| Pipeline, ownership, reuse, and target integration | `lake exe tests-pipeline` |
| HPT caches, persistence, and optimizer checks | `lake exe tests-hpt` |
| Frozen Ixon v2 codecs, sharing, and catalogs | `lake exe tests-ixon` |
| Ix frontend / Ixon v3 contracts, typing, resource admission, handoff and catalogs | `lake exe tests-ixon-v3` |

The v3 suite runs 1,848 assertions, including frozen upstream resource,
primitive and catalog fixtures. Its 39 exact axiom fences retain all 2,373 earlier
assertions. State proofs and fixtures remain outside the production API.
The public validator combines erased typing, resource checks and canonical
literal pins over the same bytes; v3 backend lowering remains separate.
Catalog validator 1 checks the authenticated union's erased typing. Full
member witnesses authenticate overlapping chunked members; explicit resource
profiles remain separate. Both test executable targets depend on the catalog
CLI for their fresh-process checks, so the direct commands build it as needed.

The Aiur target has a separate required `aiur` gate, running `tests-aiur`
and `check-aiur --root .`. Its [contract](aiur-backend.md) records the
logical-trace, witness-memory, cycle, and pinned-source checks. The
[wire gate](aiur-wire.md) additionally runs the complete bytecode codec
regressions and fresh-process encoding/replay of four frozen fixtures,
including malformed-byte/root/component rejection. Its pure and addressed
proof cones are in the required fence aggregate. The
[execution suite](aiur-semantics.md) adds 276 assertions over all 34 opcodes,
four controls, witness memory, advice, and recursive trace examples. Its
39 exact axiom assertions use ordinary logic and remain in the same required
proof aggregate; large machine proofs and examples are separate from the
production API.

The [static assignment suite](aiur-static.md) adds 116 assertions and 39
exact axiom fences to those same targets. Counter normalization and order
proofs, concrete checker examples, and fences remain outside the production
import closure.

The [counter-analyzer proof](aiur-counter-analysis.md) adds 19 public kernel
regressions and 48 exact ordinary-logic fences. Its affine, replay, machine,
and search proofs remain outside the production closure and are
required through `CompilatrixTests.Proofs`. It preserves the runtime suites.

The [memory AIR suite](aiur-memory-air.md) adds 52 runtime assertions.
Its 16 public kernel regressions and 46 exact
ordinary-logic fences are required through the proof aggregate. The `aiur`
gate compares five frozen graphs produced by the actual pinned Rust memory
builder with a fresh-process Lean export and rejects eight graph mutations.
The optional Rust exporter remains outside production and required CI; its
source and the frozen graphs are included in the audited source inventory.

The [rank AIR suite](aiur-rank-air.md) adds 71 runtime assertions, bringing
the combined Aiur suite to 848. Its 22 kernel regressions and 63 ordinary-logic
fences are required in the proof aggregate. Five extraction proof modules
remain outside production. The `aiur` gate compares six complete Rust
function-circuit fixtures and all 65,536 u16 fixed-table row pairs, repeats
the Lean export in a fresh process, and rejects 14 graph/table mutations.
The optional Rust producer and its preparation script are audited sources;
required CI consumes the frozen artifacts without building that Rust crate.

`lake exe tests` remains the aggregate entry point. The required Nix `tests`
gate runs the individual entry points and their aggregate. New cases belong
in the corresponding `CompilatrixTests.<Area>` module.

The lowerer's differential corpus and pipeline integration fixtures are
separate test modules. The old well-moded/thesis corpus and fence module paths
remain compatibility imports. Their public declaration names are preserved.
Production algorithms and proof-carrying interfaces retain their names and
contracts.

[`nix/lean-modules.json`](../nix/lean-modules.json) records the exact local
module paths, imports, and Lake target roots. Nix computes separate transitive
source sets for the production library, CI programs, and complete proofs.
The production artifact also includes the complete Aiur reference library
required by its native facet; the public API keeps its narrower imports.
The trust auditor receives the full source/configuration inventory separately.
Editing a test body or its imports therefore does not change the production
source hash. Changing the shared Lake configuration or toolchain can still
invalidate all three artifacts.

After changing imports or Lake roots, run:

```sh
lake exe check-build-graph --write
lake exe check-build-graph
```

CI recomputes this manifest from the full audit tree and rejects stale data.
It also rejects test dependencies in the production closure.

## Preserved gates

The refactor keeps all 34 previous Linux gates required and adds explicit
proof, build-graph, and per-case Stage2 checks. The resulting Linux surface has
44 checks; the Aiur foundation adds a 45th required check. No correctness
gate moved to a manual or scheduled trigger.

| Previous gate | Required coverage after factoring |
| --- | --- |
| `build` | `build` compiles the production API; `proofs` compiles the complete previous proof/example collection and moved elaboration tests. |
| `tests` | Same 266 failure assertions, split across four compiled suites; both focused and aggregate entry points run. |
| `ixby-lean` | `ixby-lean` retains frontend differentials, binary-codec cases, independent decoding, two fresh Stage2 compilations, exact frozen-image equality, and inventory comparison. Eight `ixby-stage2-binary-*` checks execute every original serialized Stage2 case. |
| Other 31 gates | Their names, fixtures, expected outputs, rejection cases, and independent oracles are retained; compilation is shared. |

All eight serialized cases remain required: `wrong-claim-kind`,
`trailing-public`, `empty-proof`, `malformed-proof`, `truncated-proof`,
`trailing-proof`, `claim-mismatch`, and `valid`. Each runs with `LEAN_PATH`
unset against the frozen image whose byte equality is checked by the
frontend gate. The binary executor still executes the decoded program;
there is no source-evaluator fallback.

The 2,072 original axiom assertions are partitioned by subsystem under
[`CompilatrixTests/Fences`](../CompilatrixTests/Fences). Each theorem spelling
and complete expected axiom message is retained.
[`nix/ci-coverage.json`](../nix/ci-coverage.json) pins the sorted assertion
inventory, runtime failure inventory, original module collection, and moved
elaboration-test modules. The build-graph check verifies that every fence is
registered in the required proof aggregate. The trust ledger also pins the
test, checker, and CI configuration files. Changes to these inventories require
review alongside the actual assertions and gate mapping.

The checker regressions deliberately exercise stale manifests, a production
import of tests, removal of a moved proof module, deletion of an axiom
assertion, and removal of runtime failure assertions. The existing native,
Cargo, dependency, source-hygiene, and CI-action rejection tests still run.

## Runtime budgets and measurements

GitHub keeps a 60-minute ceiling for the shared build, with a target below
30 minutes including dependency downloads and artifact export. Runtime jobs
have 30-minute budgets, including dependency retrieval and artifact import.
The native allocating gate, source Stage2 verifier, and the four expensive
serialized Stage2 cases each have separate jobs. Cheap malformed cases share
one job. The full group assignment is the checked JSON inventory above.

Build and runtime steps use `/usr/bin/time -v` and retain their logs. Assess
hosted duration, peak memory, and transfer overhead before changing these
budgets. Step elapsed time includes Nix's work; its CPU/RSS statistics describe
the client process, so use runner or builder measurements for total resource
use. A successful local run does not establish the duration of a cold GitHub
runner.

The retained local baseline used an AMD Ryzen 9 7950X3D (16 cores, 32 threads),
x86-64 Linux, Lean 4.33.0, cached external toolchains, freshly built project
derivations, and Nix `--max-jobs 2`.
All 34 original checks passed within an observed 30 minutes 43 seconds.
Its longest combined check was the serialized Stage2/frontend gate at about
15 minutes 28 seconds; several other gates separately compiled the compiler.
Refactor measurements and validation logs are retained in
`plans/ci-factoring/`. Compare compilation, runtime, transfer, and incremental
cache behavior separately; the checks' new parallel assignment changes the
critical path.

The final local run passed all 44 required Linux checks in 19 minutes
57 seconds. It reused the production build and rebuilt the CI programs,
proof artifact, and runtime checks, so this is not a comparable cold-build
speedup measurement. A separate fresh production build took 4 minutes
45 seconds; the final program and proof build phases took 1 minute 22 seconds
and 58 seconds while reusing the preceding stages' Lake artifacts.

The shared project runtime contains 70 executables and occupies 928 MiB,
compressed to a 322 MiB artifact. Local export took 6.7 seconds; import and
output-path verification passed, with import taking 3.8 seconds into a store
that already contained the output. These measurements exclude hosted transfer
time and fresh-worker import cost. An isolated change adding an import to an
Ixon runtime test changed the program source path while leaving the production
and proof source paths identical. Hosted job duration remains to be measured.
