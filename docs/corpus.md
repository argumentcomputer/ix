# Fixture corpora

The compiler is tested on corpora of real Lean programs, frozen as Ixon v3
closures with their `eq_def` sidecars (phase 1 plan, MT). Each *family* is a
directory of closures described by one manifest in the format
`compilatrix/corpus/1`. Required CI uses only the frozen files; it never runs
ix.

| Family | Manifest | Sources | Contents |
| --- | --- | --- | --- |
| `bench-k1` | [`fixtures/ixon-v3/bench-k1/corpus.json`](../fixtures/ixon-v3/bench-k1/corpus.json) | [`benchmarks/fixtures`](../benchmarks/fixtures/README.md) | the benchmark fixtures' pure `entry` closures: the five K1 programs, and the four added by MT.2 |
| `phase1-scalar` | [`fixtures/corpus/phase1-scalar/corpus.json`](../fixtures/corpus/phase1-scalar/corpus.json) | [`fixtures/corpus/phase1-scalar/src`](../fixtures/corpus/phase1-scalar/README.md) | the Phase 1 scalar corpus: 23 roots of first-order total programs, and five programs of Lean's `tests/compile` |

## The manifest

A manifest describes one family. Paths are relative to the repository root
(`directory`, `source_root`) or to those directories.

| Field | Kind | Meaning |
| --- | --- | --- |
| `format` | fixed | `compilatrix/corpus/1` |
| `family`, `description` | reviewed | the family's name and purpose |
| `tier` | reviewed | `required`, `campaign` or `manual` (research §9.5) |
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
| `protocol` | reviewed | how the interpreter is run: `args` (one `lean --run SRC ARG…` per case, as the benchmark sources' `main`) or `stdin` (one run; a line `ROOT ARG…` per case) |
| `closure` | derived | the anonymous closure: `path`, `sha256`, `bytes` |
| `equations` | derived | the sidecar (`compilatrix/k1-equations/1`): `path`, `sha256`, and the `equations` and `failures` counts |
| `named_env_sha256` | derived | the named twin the addresses were resolved against (not retained) |
| `census` | derived | the admission census (`lake exe census`): `path`, `sha256` |
| `roots[]` | | one closure root each |

Per root:

| Field | Kind | Meaning |
| --- | --- | --- |
| `name`, `params`, `result` | reviewed | the root's Lean name, its `Nat` parameters, and its result type (`nat` or `bool`) |
| `address` | derived | its content address, from the sidecar |
| `oracles` | reviewed | `lean-run` (Lean 4.34's interpreter), `constant` (an independent value), `upstream` (an upstream `.out.expected`) |
| `decline` | reviewed | `null`, or the `stage` and `code` the compiler must decline the root with |
| `note` | reviewed | where the constants come from, and why a resource failure is allowed |
| `generate` | reviewed | a generator: `seed`, `count` and per parameter an inclusive range |
| `cases[]` | | the cases |

Per case: `args`; `value`, what the interpreter printed (derived; `-` for a
case with an argument of at least `2⁶³`, which has no word and which the
interpreter does not run); `constant`, an independent value it must equal
(reviewed); `machine`, also run on the typed x86 machine and ByteEval
(reviewed); `allow`, resource failures allowed at the word levels and natively
(reviewed: `natOverflow` when an intermediate value reaches `2⁶³`, `heap` when
the run's immortal allocations outgrow the word levels' 64 KiB region); and
`generated`, drawn from the root's generator (derived).

The expected behaviour of a compiled root on a case follows from these:
- the source levels (SrcEval, Lam, Anf, Fir, Own, Cfg; unbounded `Nat`) give
  `ok` and the interpreter's value;
- the word levels (Lir, Xv, Xl, typed x86, ByteEval) and native code give that
  value when the arguments and the result are below `2⁶³`, and status 3
  (`natOverflow`) when the result is not, or one of the case's `allow`ed
  failures;
- with an argument of at least `2⁶³`, the entry wrapper returns status 3
  before the root runs.

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
[--anon]`), checks that their equation lists agree, resolves every root,
definition and equation name with `ix addr-of` against the twin, and writes
the sidecar and census. It draws the generated cases, runs every case through
`lean -Dlinter.all=false --run`, checks the constants, and rewrites the
derived fields. Files that do not change are not rewritten; the log says which
did. The pinned ix (`9c4b9c65`, SHA-256 `d8ba031a…`) asks `lake env` for
`LEAN_PATH`, so `--ix-path` names a directory with a `lake` stand-in that
answers it (`plans/fixtures/ix-usage-ownership/fakebin`). On 2026-10-01,
`corpus rebuild` of `bench-k1` rewrote none of the five K1 closures, sidecars
and censuses, and reproduced every named-twin hash of their provenance: it
replaces `plans/x86-phase1/bench-k1/build.sh`.

## The suite: `lake exe tests-corpus`

```sh
lake exe tests-corpus [MANIFEST…] [--cc CC] [--work DIR] [--only FIXTURE]… [--root ROOT]…
                      [--no-machines] [--progress] [--survey [--dump]]
lake exe corpus kernel-artifacts [--check]
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
Lir and Xv of a root declined at allocation or later.

## Adding a fixture

1. Write the source under the family's `source_root`, with an oracle driver
   `main` for its protocol, and record its licence and origins.
2. Add the fixture, its roots and their hand-picked cases (with independent
   constants where there are any) and generators to the manifest.
3. `lake exe corpus rebuild MANIFEST --ix … --only NAME`, then review the new
   closure's census and the interpreter's values.
4. `lake exe tests-corpus MANIFEST --survey`; record every decline as the
   root's expected `decline` (a decline is a completeness finding: list it).
5. `lake exe tests-corpus MANIFEST --cc cc`; a level disagreement or a wrong
   value is a compiler bug: keep the minimised program as a fixture.
6. Pin the new files in the trust ledger and regenerate
   `nix/lean-modules.json` if a Lake target changed.

## The kernel-recheck sample

`lake exe corpus kernel-artifacts` prints the recheck input of four small
corpus roots (`bench-k1/even-odd`, `phase1-scalar/tuple`, `natShiftr` and
`strictAndOr`'s `entryStrictAnd`) with the recheck artifact printer into
`CompilatrixTests/Corpus/Artifacts/`; with `--check` it compares them with a
fresh ingress, `produce` and native run. The manual target
`lake build CompilatrixTests.Corpus.KernelSample` states, for each, that
`Recheck.run` gives the object's bytes, by `decide +kernel` (20–24 s and
about 4 GB each on 2026-10-01). Like `CompilatrixTests.Recheck.KernelSlow`,
nothing in the default build or the programs derivation imports it.
