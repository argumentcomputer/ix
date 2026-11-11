# Fixture corpora

The compiler is tested on corpora of real Lean programs, frozen as Ixon v4
closures ([Ixon v4](ixon-v4.md)) with their `eq_def` sidecars. Each *family* is a
directory of closures described by one manifest in the format
`ixcc/corpus/1`. Required CI uses only the frozen files; it never runs
ix.

| Family | Manifest | Sources | Contents |
| --- | --- | --- | --- |
| `bench-k1` | [`fixtures/ixon-v4/bench-k1/corpus.json`](../fixtures/ixon-v4/bench-k1/corpus.json) | [`benchmarks/fixtures`](../benchmarks/fixtures/README.md) | the benchmark fixtures' pure `entry` closures: the five K1 programs, and four from the scalar corpus |
| `phase1-scalar` | [`fixtures/corpus/phase1-scalar/corpus.json`](../fixtures/corpus/phase1-scalar/corpus.json) | [`fixtures/corpus/phase1-scalar/src`](../fixtures/corpus/phase1-scalar/README.md) | the Phase 1 scalar corpus: 23 roots of first-order total programs, and five programs of Lean's `tests/compile` |
| `phase1-boundary` | [`fixtures/corpus/phase1-boundary/corpus.json`](../fixtures/corpus/phase1-boundary/corpus.json) | [`fixtures/corpus/phase1-boundary/src`](../fixtures/corpus/phase1-boundary/README.md) | every `Nat` primitive and operand shape at the `2⁶³` edge, literals of at least `2⁶³` in live and dead code, and the field-count and constructor-count limits |
| `phase1-resource` | [`fixtures/corpus/phase1-resource/corpus.json`](../fixtures/corpus/phase1-resource/corpus.json) | [`fixtures/corpus/phase1-resource/src`](../fixtures/corpus/phase1-resource/README.md) | heap, stack and trap failures (statuses 1, 2, 4) under per-case regions and stacks |
| `phase1-decline` | [`fixtures/corpus/phase1-decline/corpus.json`](../fixtures/corpus/phase1-decline/corpus.json) | [`fixtures/corpus/phase1-decline/src`](../fixtures/corpus/phase1-decline/README.md) | programs outside the Phase 1 fragment, each with its exact `stage: code`, and colliding export symbols |
| `phase1-abi` | [`fixtures/corpus/phase1-abi/corpus.json`](../fixtures/corpus/phase1-abi/corpus.json) | [`fixtures/corpus/phase1-abi/src`](../fixtures/corpus/phase1-abi/README.md) | the ABI and readback matrix, arities 0–6 by `Nat`, `Bool` and an enumeration |
| `phase1-bound` | [`fixtures/corpus/phase1-bound/corpus.json`](../fixtures/corpus/phase1-bound/corpus.json) | [`fixtures/corpus/phase1-scalar/src`](../fixtures/corpus/phase1-bound/README.md) | five `phase1-scalar` programs in the role-bound envelope `ix compile` writes by default (closure, role support, certificates and role binding), with the unbound twins' cases and declines |
| `ownership` | [`fixtures/ownership/corpus.json`](../fixtures/ownership/corpus.json) | [`fixtures/ownership/src`](../fixtures/ownership/README.md) | the ownership suite: annotated programs ix accepts, each beside its plain twin, and plain erasure and allocation fixtures; run by `tests-own` (with ix's verdicts on the annotated sources it rejects), not among `tests-corpus`'s registered families |
| `k1` | [`fixtures/ixon-v4/k1/corpus.json`](../fixtures/ixon-v4/k1/corpus.json) | [`fixtures/ixon-v4/k1`](../fixtures/ixon-v4/k1/README.md) | the K1 pack: the five K1 programs in one closure with their 40 unfolding equations and its census, without cases (the stage suites run its roots); not among `tests-corpus`'s registered families, so `corpus check` takes its manifest by path |

## The manifest

A manifest describes one family. Paths are relative to `IxCC/`
(`directory`, `source_root`) or to those directories.

| Field | Kind | Meaning |
| --- | --- | --- |
| `format` | fixed | `ixcc/corpus/1` |
| `family`, `description` | reviewed | the family's name and purpose |
| `tier` | reviewed | `required`, `campaign` or `manual` |
| `phase` | reviewed | the roadmap phase whose fragment the family tests |
| `directory` | reviewed | where the frozen files are |
| `source_root` | reviewed | where the Lean sources are; ix and Lean run here |
| `lean.version`, `lean.interpret` | reviewed, fixed | the Lean release, and the interpreter commands of both protocols |
| `producer` | reviewed | `ix_revision`, `ix_binary_sha256`, `ix_version`, `ix_build`, and the `anonymous`, `named` and `address` command templates |
| `fixtures[]` | | one closure each |

Per fixture:

| Field | Kind | Meaning |
| --- | --- | --- |
| `name` | reviewed | the fixture's name |
| `source` | reviewed, derived | `path`, `sha256` (derived), `license`, `variant` (`original`, `upstream`, `port`, …) and `origins` (upstream repository, commit, path, licence) |
| `consts` | reviewed | the `--consts` seeds: the closure's roots |
| `protocol` | reviewed | how the interpreter is run: `args` (one `lean --run SRC ARG…` per case, as the benchmark sources' `main`) or `stdin` (one run; a line `ROOT ARG…` per case; no run when no case is interpreted) |
| `allow_constructs` | reviewed | forbidden constructs (`partial`, `unsafe`, …) the source uses on purpose; only for fixtures whose roots are all declined (absent: none) |
| `closure` | derived | the anonymous closure: `path`, `sha256`, `bytes` |
| `equations` | derived | the sidecar (`ixcc/k1-equations/1`): `path`, `sha256`, and the `equations` and `failures` counts |
| `named_env_sha256` | derived | the named twin the addresses were resolved against (not retained) |
| `census` | derived | the admission census (`lake exe census`): `path`, `sha256` |
| `roots[]` | | one closure root each |

Per root:

| Field | Kind | Meaning |
| --- | --- | --- |
| `name`, `params`, `result` | reviewed | the root's Lean name (as the sidecar writes it, with `«»` where Lean needs them), its parameters (as the entry wrapper receives them: an erased type or proof parameter counts), and its result type: `nat`, `bool`, `enum` (a field-less inductive; the interpreter prints the constructor's index), or `other` (a declined root without cases) |
| `ctors` | reviewed | an `enum` result's constructor count (absent otherwise) |
| `together` | reviewed | further roots of the fixture compiled into the same object; the decline or the cases are that object's (absent: none) |
| `address` | derived | its content address, from the sidecar |
| `oracles` | reviewed | `lean-run` (Lean 4.34's interpreter), `constant` (an independent value), `upstream` (an upstream `.out.expected`) |
| `decline` | reviewed | `null`, or the `stage` and `code` the compiler must decline the root with (`ingress` included: `corpus check` then accepts that ingress decline) |
| `note` | reviewed | where the constants come from, and why a resource failure is allowed |
| `generate` | reviewed | a generator: `seed`, `count` and per parameter an inclusive range |
| `cases[]` | | the cases |

Per case:

| Field | Kind | Meaning |
| --- | --- | --- |
| `args` | reviewed | the arguments |
| `value` | derived | what the interpreter printed; `-` for a case with an argument of at least `2⁶³` (no word; the interpreter does not run it) and for a `trap` case; the `constant` for a `lean_fails` case |
| `constant` | reviewed | an independent value the interpreter's must equal |
| `machine` | reviewed | also run on the typed x86 machine and ByteEval |
| `allow` | reviewed | resource failures allowed at the word levels and natively: `natOverflow` when an intermediate value reaches `2⁶³`, `heap` when the run's immortal allocations outgrow the region, `stack` |
| `fail` | reviewed | the failure the word levels and native code must give: `natOverflow`, `heap`, `stack` or `trap` (statuses 3, 1, 2, 4) |
| `spurious` | reviewed | the `fail` or `allow`ed failure is a completeness gap: nothing the source program computes reaches the limit |
| `region` | reviewed | the region's bytes: the word levels' region (default 64 KiB) and the driver's `--region` (default 16 MiB) |
| `stack` | reviewed | the stack's bytes: the driver's `--stack` (default 256 MiB), and `stack − 4096` as the typed x86 machine's and ByteEval's stack budget, as the driver passes `cx_init` (default 896 KiB) |
| `note` | reviewed | why the case is there, and where its expectation comes from |
| `lean_fails` | reviewed | Lean's runtime fails on the case (its `Nat.pow` and `Nat.shiftLeft` refuse exponents of `2³²` or more), so neither the interpreter nor the source levels, which run on the same runtime, run it; the `constant` is its value |
| `generated` | derived | drawn from the root's generator |

Absent optional fields are not written, so manifests without them keep their
canonical form.

The expected behaviour of a compiled root on a case follows from these:
- the source levels (SrcEval, Lam, Anf, Fir, Own, Cfg; unbounded `Nat`) give
  `ok` and the interpreter's value (not run on `trap` and `lean_fails`
  cases);
- the word levels (Lir, Xv, Xl, typed x86, ByteEval) and native code give that
  value when the arguments and the result are below `2⁶³`, and status 3
  (`natOverflow`) when the result is not, or one of the case's `allow`ed
  failures;
- a case's `fail` replaces the value at every level that models it (`stack`:
  the typed x86 machine, ByteEval and native code; the others: Lir onwards);
  a level that does not model it gives the value (Lir, Xv and Xl have no
  stack);
- a region `cx_init` refuses (below 4 KiB) fails with `heap` before the root
  runs, at the word levels (`cx_init` at Lir), on the machines and natively
  (the driver's `init` line);
- with an argument of at least `2⁶³`, the entry wrapper returns status 3
  before the root runs.

Natively, Lean's `Rt.readback` of the returned word (and, for a result other
than `nat`, of the object area the driver dumps) must equal the driver's C
decoder.

## The builder: `lake exe corpus`

```sh
# offline: the frozen files against the manifests (all registered families)
lake exe corpus check [MANIFEST…] [--interpret] [--lean LEAN] [--work DIR]

# manual: rebuild a family with ix and Lean, then rewrite the derived fields
lake exe corpus rebuild MANIFEST --ix IX --ix-path DIR … [--lean LEAN] [--work DIR] [--only FIXTURE]
```

`check` verifies each source's hash and scans it for forbidden constructs
(`partial`, `unsafe`, `implemented_by`, `extrinsicFix`, `Task`); verifies the
closure's, sidecar's and census's hashes and sizes, the sidecar's roots,
addresses and counts, and reproduces the census byte for byte from the
closure; ingests every root; regenerates the generated arguments from their
seeds; checks every case's arity, value and constant; and checks that the
manifest is in the canonical form a rebuild writes. With `--interpret` it
also re-runs Lean's interpreter on every case.

`rebuild` refuses an ix binary whose SHA-256 is not the manifest's. Then, per
fixture, it runs the commands `build.sh` ran for the K1 pack: the anonymous
closure and the named twin (`ix compile --no-build --consts ROOTS --equations
[--anon]`, with `--unbound` when the manifest's commands carry it, as a
refreeze with the ix of this repository writes them; see
[Refreezing](#refreezing)), checks that their equation lists agree, resolves every root,
definition and equation name with `ix addr-of` against the twin, and writes
the sidecar and census. It draws the generated cases, runs every case through
`lean -Dlinter.all=false --run`, checks the constants, and rewrites the
derived fields. Files that do not change are not rewritten; the log says which
did. The pinned ix (`be45a159`, SHA-256 `396dffb7…`; see [Refreezing](#refreezing))
asks `lake env` for `LEAN_PATH`, so `--ix-path` names a directory with a
`lake` stand-in that answers it. It replaces an earlier shell build script.

## The suite: `lake exe tests-corpus`

```sh
lake exe tests-corpus [MANIFEST…] [--cc CC] [--work DIR] [--only FIXTURE]… [--root ROOT]…
                      [--no-machines] [--progress] [--survey [--dump] | --observe]
```

Without a manifest it runs every registered family. For each root, the
compiler either declines it with exactly the manifest's `stage: code`, or
compiles it, and then every case runs at every level `tests-pipeline` checks
(SrcEval, Lam, Anf after every middle-end step, Fir, Own, Cfg, Lir, Xv, Xl,
and, for `machine` cases, the typed x86 machine and ByteEval) and, with
`--cc`, natively under `fixtures/x86/runtime_driver.c`, with the expectations
above. A failure names the root, the case, the level and both observations.
`--survey` only compiles each root and prints `compiled` or its `stage: code`
against the manifest's (for reviewing a new family); `--dump` adds the Anf,
Lir and Xv of a root declined at allocation or later. `--observe` prints, as
tab-separated rows and without assertions, every case of every compiled root
at Cfg, Lir, Xv, Xl and (with `--cc`) natively, beside the manifest's `fail`
and `spurious` marks (for reviewing a new family's expectations and for
tabulating a boundary family). A native run is one driver process per
distinct region and stack of a root's cases.

## Adding a fixture

1. Write the source under the family's `source_root`, with an oracle driver
   `main` for its protocol, and record its licence and origins.
2. Add the fixture, its roots and their hand-picked cases (with independent
   constants where there are any) and generators to the manifest.
3. `lake exe corpus rebuild MANIFEST --ix … --only NAME`, then review the new
   closure's census and the interpreter's values.
4. `lake exe tests-corpus MANIFEST --survey`; record every decline as the
   root's expected `decline` (a decline is a completeness finding: list it).
   For a boundary or resource fixture, `--observe --cc cc` shows each case's
   outcome at every word level and natively: mark each status 3 the source
   explains as `fail` (or `allow`), and one it does not as `spurious` too.
5. `lake exe tests-corpus MANIFEST --cc cc`; a level disagreement or a wrong
   value is a compiler bug: keep the minimised program as a fixture.
6. Pin the new files in the trust ledger and regenerate
   `nix/lean-modules.json` if a Lake target changed.

## The kernel-recheck sample

`lake exe corpus kernel-artifacts` prints the recheck input of four small
corpus roots (`bench-k1/even-odd`, `phase1-scalar/tuple`, `natShiftr` and
`strictAndOr`'s `entryStrictAnd`) with the recheck artifact printer into
`IxCCTests/Corpus/Artifacts/`; with `--check` it compares them with a
fresh ingress, `produce` and native run. The manual target
`lake build IxCCTests.Corpus.KernelSample` states, for each, that
`Recheck.run` gives the object's bytes, by `decide +kernel` (20–24 s and
about 4 GB each on 2026-10-01). Like `IxCCTests.Recheck.KernelSlow`,
nothing in the default build or the programs derivation imports it.

## Optional certified-checker census

`certified-census` runs a separately built `kernel-check-ixe` and writes a
diagnostic JSON report plus the original per-declaration rows and process
logs. It does not import or build the kernel, change corpus expectations, or
gate compiler admission. A full source revision and the executable's verified
SHA-256 identify the checker; the source-to-binary attribution is supplied by
the caller and should come from a recorded build.

```sh
lake build certified-census
systemd-run --user --scope -p MemoryMax=16G -p MemorySwapMax=0 --quiet \
  taskset -c 4-23 nix develop -c lake exe certified-census \
  --checker /path/to/frozen/kernel-check-ixe \
  --revision <40-digit-revision> --sha256 <64-digit-sha256> \
  --out plans/certified-census/run-1 --timeout 60 --recursors as-frozen
```

With no inputs it checks the seven registered corpus families. Repeated
`--manifest PATH` selects other families; repeated `--input CLOSURE.ixe`
selects individual closures. Manifest inputs must match their frozen hash.
Use `--recursors explicitly-seeded` only when the supplied inputs were built
with explicit recursor seeds; use `unknown` when that provenance is absent.
The tool records this assertion and never recompiles or seeds inputs itself.

Every invocation is sequential and bounded by `--timeout` (1–3,600 seconds).
The output directory must be new. Completed records distinguish accepted,
rejected, declined and blocked declarations. Timeouts, crashes, malformed
rows, duplicate addresses, missing completion markers and partial output are
reported as incomplete runs and make the tool exit nonzero. Partial record
counts remain visible under `complete: false`; they are not whole-closure
acceptance. Completed rejections and declines are report data, so they do not
make the diagnostic command fail. This matters for known missing-recursor
declines and non-v4 input hangs in older external checker revisions.

`certified-census --self-test` checks the reporting protocol without an
external checker. CI runs that small test; actual certified census results
remain non-gating. Run all probes under the same machine-wide two-stream
limit as the compiler checks.

## Refreezing

Every frozen closure is a function of the producer (ix binary, its Lean
libraries, the toolchain). When the producer changes its output (a new Ixon
format, canonical order, repacked cliques), every family is refrozen at once
with the tools below, and nothing is written by hand: the closures,
sidecars, censuses, values, verdicts, pins and provenance all come from a
command. The last refreeze (2026-10-03, Ixon v3 → v4) changed every closure
and almost every address, and no source, root, case, value, equation list or
failure list. Check that for every manifest: with the fields a refreeze may
change removed, the old and new manifests are equal (a difference is a
stop-and-review):

```sh
norm='del(.producer.ix_revision, .producer.ix_binary_sha256, .producer.ix_version,
  .producer.ix_build, .lean.version) | .fixtures |= map(del(.source.sha256, .closure.sha256,
  .closure.bytes, .equations.sha256, .named_env_sha256, .census.sha256)
  | .roots |= map(del(.address)))'
diff <(git show HEAD:$m | jq -S "$norm") <(jq -S "$norm" $m)
```

What a refreeze needs:
- `IX`: the producer binary. The frozen files were produced by ix `be45a159`
  (`f829b760` plus the `--equations` export, built with Lake in ix's dev
  shell at that revision; SHA-256 `396dffb7…` from the 2026-11-07 rebuild, as
  the build is not reproducible), which is not in this repository's history:
  it is reachable only from ix's `jcb/compilatrix-donor-history-2026-10-11`
  and `jcb/compilatrix-resource-wip-2026-10-11` branches. The ix of this
  repository (`lake build ix` at the repository root) can be the producer
  instead: it has the same export (`ix compile --equations`), and
  `ix compile --unbound` writes the closure in the version-4 envelope the
  committed fixtures use; without the flag it writes a role-bound version-5
  envelope with the role support and certificates, which ingress also reads
  ([byte contract](byte-contract.md)), and from which IxCC takes its pinned
  identities.
  `refreeze-ixon producer` writes `--unbound` into every manifest's commands.
  Its `--consts` closure is ix's selected closure (recursors, whole logical
  units and checker support included), so refreezing with it changes every
  closure, census and most equation lists, but no source, root, case or
  value;
- `FAKE`: a directory holding a `lake` stand-in that answers
  `lake env printenv LEAN_PATH` with the producer workspace's built Lean
  libraries at the same revision (ix elaborates the sources against them; the
  ownership sources import `Ix.Compile.SourceContract.Elab`), and refuses
  everything else. For the ix of this repository that is the value
  `lake env printenv LEAN_PATH` prints at the repository root;
- `IXREPO`, `IXPIN`: a read-only ix checkout and the revision whose
  `Tests/Fixtures/ixon-v4/` and primitive table apply (`f829b760`, the wire
  revision, whose table is `Ix/Tc/Primitive.lean`; the codec pin `2dd96055`
  no longer has `Ix/Tc`). This repository keeps the table in
  `Ix/PrimAddrs.lean`, which has no `stringLegacyBack` field, so
  `refreeze-ixon tc-primitives` refuses it until the erased checker's table
  drops that field;
- the pinned toolchain's `lean` on `PATH` (`nix develop`).

The commands, in order, from `IxCC/`, with `lake build` of the
tools first:

```sh
REV=<the producer's 40-digit revision>
BUILD="Built with Lake (lake build ix) from the recorded revision, …; not a Nix build."
# 1. pin the producer and the interpreter's Lean in every manifest and in the verdicts
lake exe refreeze-ixon producer --ix $IX --revision $REV --build "$BUILD"
# 2. every corpus family: closures, sidecars, censuses, values (manifests rewritten)
for m in fixtures/ixon-v4/bench-k1/corpus.json fixtures/ixon-v4/k1/corpus.json \
         fixtures/corpus/*/corpus.json; do
  lake exe corpus rebuild $m --ix $IX --ix-path $FAKE
done
# the built tool itself: `lake exe` replaces LEAN_PATH for the interpreter runs
LEAN_PATH=$($FAKE/lake env printenv LEAN_PATH) \
  .lake/build/bin/corpus rebuild fixtures/ownership/corpus.json --ix $IX --ix-path $FAKE
# 3. ix's verdicts on the annotated ownership sources
lake exe tests-own verdicts --ix $IX --ix-path $FAKE
# 3b. the RC real-source input (fixtures/rc/real-source): the commands its
#     provenance.json records, then its manifest.sha256
# 4. the Src tables and the roots-only fixtures
#    (the real lake by its path: with FAKE first on PATH, `lake` is the stand-in)
LAKE=$(command -v lake)
PATH=$FAKE:$PATH $LAKE exe pin-src-tables --ix $IX --revision $REV
PATH=$FAKE:$PATH $LAKE exe pin-src-tables --ix $IX --revision $REV --diagnostics fixtures/ixon-v4/src-diag
PATH=$FAKE:$PATH $LAKE exe pin-src-tables --ix $IX --revision $REV --sortpoly fixtures/ixon-v4/src-sortpoly
# 5. ix's fixture package (vectors, handoff, primitives.tsv) and the erased
#    checker's primitive table, unchanged from ix
lake exe refreeze-ixon package --ix-repo $IXREPO --ix-revision $IXPIN
lake exe refreeze-ixon tc-primitives --ix-repo $IXREPO --ix-revision $IXPIN
# 6. Src.Pinned from the old and new primitives.tsv/src-tables.tsv
git show HEAD:fixtures/ixon-v4/primitives.tsv > old-primitives.tsv
git show HEAD:fixtures/ixon-v4/src-tables.tsv > old-src-tables.tsv
lake exe pin-src-tables --repin IxCC/Src/Pinned.lean \
  --old-primitives old-primitives.tsv --old-tables old-src-tables.tsv
lake exe pin-src-tables --repin IxCC/Src/Syntax.lean \
  --old-primitives old-primitives.tsv --old-tables old-src-tables.tsv
# 7. the typing bundles, then the catalogs over them (the ix of this repository
#    assembles only role-bound catalog members, so `catalog` refuses it)
PATH=$FAKE:$PATH $LAKE exe refreeze-ixon typing --ix $IX --revision $REV
lake exe refreeze-ixon catalog --ix $IX --revision $REV
# 8. the generated kernel artifacts (rebuild the generators first: Pinned changed)
lake build gen-src-artifacts gen-recheck-artifacts corpus tests-fir
lake exe gen-src-artifacts
lake exe gen-recheck-artifacts
lake exe corpus kernel-artifacts
lake exe tests-fir --render-artifacts > IxCCTests/Fir/Artifacts.lean
# 9. checks that must not change
lake exe check-steps          # the step baseline: a change is a stop-and-review
lake exe corpus check
lake exe corpus check fixtures/ixon-v4/k1/corpus.json fixtures/ownership/corpus.json
```

`corpus rebuild` refuses a closure that does not decode, so it cannot refreeze
phase1-boundary's `fields255` and `tags126`, whose expected decline is that
decode failure; that family keeps its closures and producer pin until a
refreeze admits them deliberately.

Then:
- the tests that name constants by number (`IxCCTests/Lam/KernelK1/*.lean`,
  which state facts about the Src artifacts by `decide +kernel`) are renumbered
  by their meaning (the entry root, the `prim`/`eqn`/`case` entries, the
  subsingleton recursor, the `lazy` constant, `Nat.zero`), each evaluated
  natively before the kernel build;
- the fixed identities in tests (the catalog roots in
  `IxCCTests/IxonV3/Catalog/Files.lean`) come from the catalog
  provenance;
- the trust ledger's integrity pins are re-recorded
  (`check-trusted-externs --record`; every new or changed fixture is
  covered by its rule), `nix/lean-modules.json` with
  `lake exe check-build-graph --write` if a module changed, and the fixture
  READMEs' producer lines follow the manifests;
- the suites run in full (`docs/ci.md`); their assertion counts can move
  where a test samples by constant number (`tests-relevance`'s annotation
  mutants are drawn over the renumbered constants).
