# Repository guidelines

Use [compiler-design.md](docs/compiler-design.md) for architectural contracts,
[roadmap.md](docs/roadmap.md) for delivery scope, and
[development-plan.md](docs/development-plan.md) for validation commands.
The factoring rules below guide new work and incremental refactors; the current
tree still contains monolithic test and proof modules that need migration.

## Working preferences

1. Prefer Lean to Python, Perl, and shell scripts where practical, especially
   for repository tools, fixture generators, checkers, and structured data
   processing. Keep Nix/YAML build configuration declarative and shell glue
   small. Preserve independent test oracles when choosing an implementation.
2. Prefer the local, gitignored `plans/` directory to `/tmp` where practical.
   Use `plans/<task>/` for plans, scratch programs, logs, measurements, and
   review notes. Keep durable specifications in `docs/`. Temporary directories
   required by tests, tools, or Nix sandboxes can use their normal locations.
3. Prefer creating workspaces, worktrees, and reference checkouts under
   `~/projects` where practical. Reuse an appropriate existing checkout and
   give additional workspaces distinct names; preserve unrelated local work.

## IxCC in the ix repository

- IxCC is the `IxCC/` package of ix (`«ix-cc»`). Run Lake from `IxCC/` in
  ix's development shell (`nix develop` finds ix's flake from here). IxCC
  depends on `../IxCK` (its Ixon codec, the role vocabulary `IxCK.Kernel.Key`
  with which it reads role-bound environments, and the kernel's tiered
  admission entry and executed typing core, which the front end over the
  kernel uses; not the kernel's proof tree) and Blake3; its grounding
  library (`IxCCGrounding`, beside the production library) also imports the
  kernel's model, `IxCK.Kernel.Denotes` (the statement half), which nothing
  in the production library or the shared program build may import
  (`check-build-graph`);
  ix's root
  package does not depend on IxCC, and IxCC must not import the root
  package's `Ix.*` modules.
- ix's `flake.nix` builds IxCC from `nix/build.nix` and `nix/checks.nix`,
  with ix's toolchain, `lake2nix` and Blake3 build, and exposes its
  checks as `ixcc-*`. `nix/sources.nix` selects IxCC's sources from the
  workspace, so keep every input IxCC reads inside `IxCC/` or recorded in
  the trust ledger.
- `lean-toolchain` must equal ix's; the trust ledger checks this, as does
  CI Jobs' toolchain check.
- The [trust ledger](docs/trusted-extern-ledger.md) pins the following, so
  a change to any of them fails `ixcc-trusted-extern-ledger` until the ledger
  is updated and reviewed in the same change: every IxCC file its integrity
  rule covers (Lake files, `IxCC/`, `IxCCTests/`, `fixtures/`, `nix/`,
  `tools/` and a few named specifications; not the rest of `docs/`, the
  READMEs, this file or `benchmarks/`), the 82 files of the `IxCK` closure
  IxCC imports (the codec, the role vocabulary, the admission entry and the
  typing core, with the kernel's `implemented_by` rulings enumerated), the
  revisions of ix's `flake.lock`, the full text of
  `.github/workflows/ixcc.yml` and the remote actions it uses, and the set of
  required checks (`required_checks`, which must equal the attributes of
  `nix/checks.nix`). ix's `flake.nix` is not pinned; `ixcc.yml` instead
  fails unless the flake's `ixcc-*` checks are exactly `required_checks`.
  Not covered at all: ix's other workflows (including the jobs that call
  `ixcc.yml`) and IxCK outside that closure. For routine updates,
  `check-trusted-externs --record` prints the mechanical pins for review
  ("Routine updates" in the ledger document).
- Shared files at the repository root (`flake.nix`, `flake.lock`,
  `.github/`, `.gitattributes`) are ix's; change them with ix's
  conventions and keep ix's own checks passing.

## Modules, namespaces, and dependencies

- Keep production declarations under `IxCC.<Area>`, following the
  pipeline areas in docs/compiler-design.md (Ixon, Src, Lam, Anf, Fir, Own,
  Cfg, Lir, X86) and the Aiur target. Match
  module paths to their area and purpose; avoid unrelated global declarations.
- Put new test-only modules under `IxCCTests.<Area>`, with shared test
  utilities in `IxCCTests.Support`. Give them explicit Lake library and
  executable targets. Keep standalone entry points thin and their reusable
  logic in named modules.
- Separate definitions and executable algorithms from large simulation proofs,
  example corpora, fixture builders, and axiom fences. Proofs may retain their
  existing public `IxCC` declaration names when moved to narrower files.
  Small interface lemmas and proof-carrying compiler contracts belong with the
  interface that needs them.
- Production modules must not depend on test modules, fixtures, example suites,
  or axiom-fence aggregators. Extract any reusable definitions from those files
  into a lower-level production module before depending on them. Repository
  checkers and test support may depend on production interfaces.
- Import the smallest module that supplies the needed interface. Reserve broad
  umbrella imports for explicit aggregate targets. Keep `IxCC.lean`
  focused on the production API; expose complete proof and test collections
  through separate targets that CI builds explicitly.
- Namespaces alone do not isolate compilation. Align file boundaries, imports,
  Lake roots/globs, and Nix artifacts. Check the transitive dependency graph
  when introducing a library or executable; avoid globs that pull optional
  tools or tests into a production artifact.
- Split large files by coherent definitions, proof interfaces, and operations.
  Extract shared lemmas into narrow dependencies. Use elaboration timings and
  import dependencies to choose boundaries, and keep frequently edited code
  from invalidating unrelated expensive proofs.

## Test and proof factoring

- Organize suites by subsystem and behavior: codecs/addressing, IR passes,
  ownership/reuse, native execution, and repository tooling. Give each suite a
  direct build/run command and useful failure output. Extend the relevant
  focused suite instead of growing the root `Tests.lean` executable.
- Keep cheap pure assertions in focused test modules. Put large computations,
  corpus traversals, and FFI execution in compiled test executables. Building
  an executable is only the build check; its behavior check must run it.
- Keep production algorithms usable without elaborating regression fixtures.
  Share fixture data and test utilities through narrow test-support modules;
  preserve independent expected results, decoders, and execution oracles.
- Split axiom fences by subsystem and register every part in a required
  aggregate proof/fence check. Moving a test or theorem must preserve its
  assertions, premises, expected axiom set, and CI coverage. Maintain a mapping
  from old gates to new targets during a refactor so none silently disappear.
- Separate bounded correctness regressions from expensive reference execution,
  full corpora, stress tests, and performance measurements. Give slow gates
  explicit targets, runtime budgets, and CI jobs/triggers. Record any change
  from required to manual or scheduled coverage as a coverage change.
- Keep compiler comparisons and their toolchains in an optional package
  outside the root flake (see docs/benchmark-plan.md). Production CI must
  not acquire CakeML, CompCert, or measurement runners through an import,
  default target, or Nix dependency. Native compiler correctness checks remain
  part of the required validation surface.

## Lake, Nix, and CI efficiency

- Build shared artifacts once per source/toolchain/configuration and reuse
  them across checks with overlapping dependencies. Separate compilation from
  test execution so multiple runs can consume the same built programs.
  Avoid a fresh full compiler build for each fixture or checker.
- With the current Nix helper, `lakeDeps` supplies external dependencies;
  `lakeArtifacts` can supply previously built project artifacts. Verify actual
  reuse in Lake/Nix logs, including `.olean` and native artifacts as needed.
  Check that custom build hooks preserve artifact preparation. Do not force a
  small standalone check to depend on an unrelated full-library build.
- Group related checks when this shares expensive compilation; split groups
  when their independent runtime or dependency costs justify it. Balance CI
  jobs using measured duration and memory. Sharding must preserve artifact
  reuse and must not duplicate the full build in every job.
- Keep Nix source sets specific to each artifact. Plans, logs, reports, and
  unrelated documentation must not invalidate compiler builds. Give the trust
  audit the full source/configuration inventory it needs, independently of the
  narrower compiler artifact inputs.
- Measure cold builds and incremental builds, separately from test execution.
  Record the runner, toolchain, cache state, concurrency, elapsed time, and peak
  memory where available. A warm local success does not establish that a cold
  GitHub runner fits the job budget.
- Aim for required CI jobs to finish within 30 minutes on their configured
  runner (`.github/workflows/ixcc.yml`), including cold compilation.
  Investigate repeated compilation and oversized import closures before
  raising timeouts or concurrency. Budget long integration
  gates explicitly and retain visible failures and diagnostic logs.
- Use the pinned Lean toolchain consistently for Lean modules and native FFI
  headers. Keep Lake/Nix dependency pins and the trust ledger synchronized;
  changing a toolchain is a separate compatibility change from test factoring.

## Validating and landing changes

- Start with the affected module, focused executable, and corresponding Nix
  check. Run the executable when runtime behavior is affected. Documentation
  and ignore-rule edits need relevant static checks, not a full compiler run.
- For module, namespace, or build-graph refactors, validate affected targets,
  the complete proof/fence and trust-audit inventory, and the full required CI
  surface before declaring the refactor complete. Retain before/after build
  evidence in `plans/<task>/`; report which checks ran and any remaining gaps.
- Update Lake roots, Nix source sets, imports, docs, and the
  [trusted-extern ledger](docs/trusted-extern-ledger.md) when files move. Review
  integrity-pin changes against the actual diff. Preserve the trusted source
  inventory and the exact axiom fences; do not weaken checks to make a move pass.
- Keep behavior-preserving factoring separate from semantic or dependency
  changes. Preserve public theorem/API names where practical and update all
  affected consumers together. Claim a CI speedup only with comparable timing
  evidence; distinguish local checks from a completed hosted CI run.
