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
  `lake exe tests-aiur`, the x86 checks `check-x86-encoder`,
  `check-x86-bytes`, `check-x86-streams` and `check-x86-object`, and the
  pipeline suites `tests-src`, `tests-relevance`, `tests-lam`, `tests-anf`,
  `tests-fir`, `tests-rt --cc cc`, `tests-pipeline --cc cc`,
  `tests-recheck`, `tests-recheck-readback`, `check-lir`, `check-xv-select`, `check-regalloc`,
  `check-backend --cc cc`, `corpus check`, `tests-corpus --cc cc`,
  `tests-own --cc cc`, `tests-own-plain`, `tests-shrink` and
  `check-steps` (the required checks that run each are in the CI guide).
- After a reviewed change to emitted code, regenerate the step-count
  baseline with `lake exe check-steps --write` and review its diff; it is
  a performance-relevant change.
- After changing imports or Lake roots, run
  `lake exe check-build-graph --write` and review the manifest. After a
  reviewed fence or assertion change, regenerate the coverage inventory
  with `--write-coverage` (see the CI guide).
- After changing an integrity-pinned file, review and update its pin in
  `docs/trusted-externs.json`, then run `check-trusted-externs` and
  `check-tools-tests`.

The former complete surface, including every family gate and its command,
is documented on branch `jcb/ixby-archive`.

For equation/profile consumer changes, build the shared source and ownership
executables once, then run the affected checks:

```sh
lake build tests-src tests-own
lake exe tests-src
lake exe tests-own --only annotated-recursion
```

The `annotated-recursion` part also runs in default `tests-own`, including the
required Nix suite. It authenticates committed historical annotated/plain
fixtures, checks 36 complete observations, retains the annotated plain-RC
domain refusal and tests the local legacy empty-metadata adapter. It invokes
no producer and changes no production parser. Keep its historical provenance
distinct from final selected-producer acceptance and family refreeze.

For consumer case, wrapper and overapplication order, build `tests-lam` once
and run `.lake/build/bin/tests-lam --only evaluation-order`. Its 118 assertions
check sixteen synthetic cases through actual table/relevance rechecking,
lazification and erasure, with independent Src/Lam outcomes at two clocks.
The same part runs in default `tests-lam` and the required Nix `suites` check.
It does not establish arbitrary resource-profile compatibility or producer
admission. Run the complete `tests-lam` suite after changing this gate.

For the plain-RC foundation, build and run `tests-own-plain` and build
`CompilatrixTests.Own.Plain.Suite`, `CompilatrixTests.Fences.OwnPlain` and
`CompilatrixTests.Fences.OwnRc`. The pure suite is also required by
`CompilatrixTests.Proofs`.
The executable covers candidate rejection, complete values, shared aliases,
calls/joins, clocks and final release. These abstract-heap checks remain
required alongside the promoted runtime/certificate gates. Keep proof modules
out of the executable checker's import closure.

For the bounded plain-RC path, build the five focused executables and pure
Cfg controls once:

```sh
nix develop -c lake build CompilatrixTests.Cfg.Rc.Proofs tests-rt-rc tests-rc-certificate tests-driver-session tests-cfg-rc tests-pipeline-rc
```

Run the portable Lir and driver-model controls:

```sh
.lake/build/bin/tests-rt-rc controls
.lake/build/bin/tests-rt-rc deep
.lake/build/bin/tests-driver-session
.lake/build/bin/tests-cfg-rc
.lake/build/bin/tests-pipeline-rc levels plans/rc-validation/run-1/levels
.lake/build/bin/tests-pipeline-rc counters plans/rc-validation/run-1/counters
```

On x86-64 Linux, from the repository root with `cc`, `timeout` and `sha256sum`
available, run the native and fresh-process gates with a new log directory:

```sh
.lake/build/bin/tests-rt-rc native plans/rc-validation/run-1/runtime
.lake/build/bin/tests-rc-certificate fresh plans/rc-validation/run-1/certificate
.lake/build/bin/tests-pipeline-rc native plans/rc-validation/run-1/levels-native
.lake/build/bin/tests-pipeline-rc negative plans/rc-validation/run-1/negative
```

`fresh` starts four independent compiled processes: codec writer/reader and
complete RC replay writer/reader. It preserves the serialized certificates,
producer/replayed ELF bytes, refusal diagnostics, complete native observations
and memory dumps. The replayed objects also execute 168 calls/output drops in
three bounded arenas initialized once each. The independent C and Lean
oracles check full values and exact reclamation, including shared tails and
repeated elements. The runtime gates separately cover short heaps, count
and stack boundaries, a 64-cell release and 50 same-arena reuse cycles.
The Cfg pure aggregate retains 29 exact bounds, marker, map and scope examples.
Its executable checks four complete value/heap cases, bounded timeout
correspondence and 12 alias, stale-binding, ownership and count-limit controls.
The separate RC pipeline gate checks complete independent constructor trees
at Src, Lam, every certificate Anf stage, Fir, plain Own, RC Cfg, Lir, Xv,
Xl, typed x86 and emitted-byte execution. Its counter mode observes actual
`Cfg.Rc.step` transitions and compares entire results/heaps with `Cfg.Rc.run`.
It records attempts, allocations, increment multiplicities, decrements,
cascading frees and peak/final live cells separately, stopping before the
caller drops the owned result. These are bounded abstract-stage measurements;
the existing native call/drop gate checks physical recycling separately.
The native mode compares both C decoding and Lean dump readback. The negative
mode uses a fresh positive bundle, rejects object-only corruption both before
and after rehashing, and distinguishes real-root heap exhaustion from
initializer refusal, with successful full-value neighbors on the same code.
Do not rerun `fresh` over an existing bundle or replace it with an in-process
round trip. The fixture manifest under `fixtures/rc/real-source` pins the
input bytes and independent C harnesses; its current historical producer
identity does not establish final producer/refreeze acceptance.

The Nix registrations are `rc-runtime` on every configured system (including
RC pipeline `levels`/`counters`) and `rc-native` on x86-64 Linux (including
RC pipeline `native`/`negative`). They execute the shared programs artifact, with
600-second outer command limits, 120-second fresh-child limits and
30-second native-child limits. Build and run them explicitly during integration:

```sh
nix build .#checks.x86_64-linux.rc-runtime .#checks.x86_64-linux.rc-native
nix develop -c lake build CompilatrixTests.Proofs
```

Also run the complete build-graph, exact fence, trust/tool and required Nix
surface after registration. The separate `Recheck.RcReplay.run` theorem keeps
successful replay, `X86.Driver.Ok`, source `GoesWrong` and the documented
source/native model qualifications. Public drop/reentry proofs compose owned
operation boundaries; the native session test is not a new unconditional
arbitrary-session soundness theorem. See [compiler design](compiler-design.md#runtime)
and [CI coverage](ci.md) for their precise scope and recorded local results.

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

### Validating a certify-compile integration candidate

The [roadmap](roadmap.md#phase-15-priorities-after-the-certification-work)
defines the integration priorities. When adopting its certification interfaces,
use the following gates. Checker-only changes retain their existing validation
requirements without acquiring a dependency on this pilot.

1. Record the immutable upstream revision and actual checked-out source,
   binary/library/profile hashes and toolchain. In a Jujutsu workspace,
   `jj --ignore-working-copy log` and `jj --ignore-working-copy file show -r
   REV PATH` permit inspection without updating the working copy. A newer
   bookmark or remote run does not describe older checked-out files.
2. Keep a certification pilot in a separate validation target. Record its
   exact source cone, Ixon bytes, name map, support declarations, selected
   W/S route and route-specific theorem conclusion. At upstream `fc058f93`,
   changed-value S+a requires `--strong-changed`; direct/raw S and S+a have
   different conclusions and supported domains. Build and run the target;
   test a valid neighbor and independently corrupted evidence.
3. Run the consumer compatibility cases on that exact candidate: equation and
   `csimp` selection, annotation/profile transport, recursor-complete closure
   discovery and the previously failing proof closure. Keep unsupported,
   blocked, rejected and exhausted outcomes distinct. Preserve recorded
   resource-checker configurations and negative controls alongside certification.
   For the October 9 combined goal, run fresh paired acceptance at 500,000 steps
   per declaration/equation and depth 256; preserve historical 100,000-step results
   and explicit low-budget exhaustion controls. Optimization toward 100,000 is
   follow-up work, not evidence of current acceptance.
4. Treat compiler-output changes as a separate refreeze from checker-only
   changes. Follow [the corpus procedure](corpus.md#refreezing), retain
   independent source/oracle expectations, review every address/verdict delta,
   and run the focused native suites plus the full proof/fence, build-graph,
   trust and Nix surface before landing. Audit any expanded dependency closure;
   the existing production ix dependency is codec-only.

Library-wide upstream certification counts are evidence for those inputs;
they do not validate a consumer integration, a new theorem closure, resource
contracts, SrcEval adequacy, or IxVM proving. Keep the revision and the logs
supporting each claim together in `plans/<task>/`.

### Shrinking a generated failure

The generators (LamGen, FoGen, the Lir generator and the allocation
mutants) draw every choice through `RngM`, whose tape can record a run's
choice sequence or replay an edited one (`CompilatrixTests.Support.Rng`).
`lake exe tests-shrink` checks that recorded sequences regenerate their
seeded cases, and that a planted bug per generator is found, named at the
first level of its ladder that diverges from the generator's reference
level, shrunk, and written out (MT.5). For a real failure at some seed:

```sh
lake exe tests-shrink campaign GEN --from SEED --count 1 [--out DIR]
lake exe tests-shrink replay DIR/GEN-SEED.json
```

`GEN` is `lamgen`, `fogen`, `lirgen` or `regalloc-mutants`. The campaign
runs the generator's ladder (`lamgen`: Lam, Anf after each middle-end step,
Fir, Own, Cfg; `fogen`: Anf, Fir, Own, Cfg; `lirgen`: Lir, Lir with critical
edges split, Xv, Xl; `regalloc-mutants`: Lir, Xv, Xl, the validator-accepted
mutant) on each seed's case, shrinks every failing one by its choice
sequences until the same first level still diverges, and writes a
`compilatrix/repro/1` record: the sequences that regenerate the shrunk
case, its input, the level and both observations, the sizes before and
after, and the program as text. `replay` regenerates the case from the
sequences (not the seed, which stops reproducing once a generator changes)
and runs the ladder again; it exits 1 while the failure reproduces.

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
