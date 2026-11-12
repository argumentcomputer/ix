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
| `phase2-closures` | [`fixtures/corpus/phase2-closures/corpus.json`](../fixtures/corpus/phase2-closures/corpus.json) | [`fixtures/corpus/phase2-closures/src`](../fixtures/corpus/phase2-closures/README.md) | higher-order workloads compiled through the closures step (P8): a closure that grows each iteration, dictionary-passing polymorphic recursion, a `StateT`-over-`Except` loop (with the library's `StateT.bind`, whose tail call of eight arguments is a call and a return, a frame per iteration, with a case that ends with the stack-exhaustion status; with the stack's own `Monad` instance, proper tail calls), application through stored closures, a fuel-indexed record of closures; and (fixture `sparse`) matches with a catch-all, through Lean's sparse casesOn, with the unchosen arm's cost and outcome cases |
| `phase1-machines` | [`fixtures/corpus/phase1-machines/corpus.json`](../fixtures/corpus/phase1-machines/corpus.json) | [`fixtures/corpus/phase1-machines/src`](../fixtures/corpus/phase1-machines/README.md) | numeric state machines (standalone executables, X2): the `IxccExe` library (`lib/IxccExe.lean`, verbatim at the head of the source) with `fib` whose parsing and rendering are Lean, first order and through a closure, the identity, a request outside the interface, and the session machine `echo`; and, in the fixture `natural`, `fib` and the message step with the library written in the natural style (`if`, `==`, `if` chains), which the middle end makes first order |
| `grounding` | [`fixtures/corpus/grounding/corpus.json`](../fixtures/corpus/grounding/corpus.json) | [`fixtures/corpus/grounding/src`](../fixtures/corpus/grounding/README.md) | the grounding suite's subjects no other family holds: `decide (fib 10 = 55)`, role-bound |
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
| `producer` | derived | `ix` (always this repository's `ix`, in words), `ix_version` (`ix --version`), and the `anonymous`, `named` and `address` command templates |
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
| `region` | reviewed | the region's bytes: the word levels' region (default 64 KiB) and the native test executable's (default 16 MiB) |
| `stack` | reviewed | the stack's bytes: the native test executable's stack (default 256 MiB), and `stack − 4096` as the stack budget of the typed x86 machine, ByteEval and the executable, as the host passes it to `cx_init` (default 896 KiB) |
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
  (the test executable's `cx_init`);
- with an argument of at least `2⁶³`, the entry wrapper returns status 3
  before the root runs.

Natively, `Rt.readback` of the returned word (and, for a result other than
`nat`, of the object area the test executable returns) must equal the tests'
independent decoder (`IxCCTests.Rt.Decoder`).

## The builder: `lake exe corpus`

```sh
# offline: the frozen files against the manifests (all registered families)
lake exe corpus check [MANIFEST…] [--interpret] [--lean LEAN] [--work DIR]

# manual: rebuild a family with ix and Lean, then rewrite the derived fields
lake exe corpus rebuild MANIFEST --ix IX --ix-path DIR … [--lean LEAN] [--work DIR] [--only FIXTURE]
```

`check` verifies each source's hash and scans it for forbidden constructs
(`partial`, `unsafe`, `implemented_by`, `extrinsicFix`, `Task`); verifies the
closure's, sidecar's and census's hashes and sizes, that every closure is the
role-bound envelope (`0xE5`), the sidecar's roots, addresses and counts, and
reproduces the census byte for byte from the closure; ingests every root;
regenerates the generated arguments from their seeds; checks every case's
arity, value and constant; and checks that the manifest is in the canonical
form a rebuild writes. With `--interpret` it also re-runs Lean's interpreter
on every case.

`rebuild` runs, per fixture, the anonymous closure and the named twin
(`ix compile --no-build --consts ROOTS --equations [--anon]`: the role-bound
envelope, `ix compile`'s output), checks that their equation lists agree,
resolves every root, definition and equation name with `ix addr-of` against
the twin, and writes the sidecar and census. A closure whose envelope does not
decode is refused unless the manifest expects every root of the fixture
declined at `ingress: decode`. (A root that reaches a record over IxCC's
consumer budget, `phase1-boundary`'s `fields255` and `tags126`, is declined at
`ingress: decode` by ingress; its envelope decodes.) It draws the generated cases, runs every case through
`lean -Dlinter.all=false --run`, checks the constants, and rewrites the
derived fields, the producer record among them. Files that do not change are
not rewritten; the log says which did. ix asks `lake env` for `LEAN_PATH`, so
`--ix-path` names a directory with a `lake` stand-in that answers it.

The producer is always the ix of this repository (`lake build ix` at the
repository root). A manifest records it in words (`producer.ix`) and its
`ix --version`; no binary is named (the Lake build is not reproducible, and the
closures do not depend on the binary's bytes: two binaries of the same sources
write the same closures). `check` protects what it always did: the committed
bytes agree with the hashes the manifest records, the manifest is what a
rebuild writes, and every closure is role-bound. Whether this repository's ix
still writes the committed bytes is the regeneration check's question
(`tools/regenerate.sh --check`, [Refreezing](#refreezing)).

## The suite: `lake exe tests-corpus`

```sh
lake exe tests-corpus [MANIFEST…] [--native] [--work DIR] [--only FIXTURE]… [--root ROOT]…
                      [--no-machines] [--progress] [--survey [--dump] | --observe]
```

Without a manifest it runs every registered family. For each root, the
compiler either declines it with exactly the manifest's `stage: code`, or
compiles it, and then every case runs at every level `tests-pipeline` checks
(SrcEval, Lam, Anf after every middle-end step, Fir, Own, Cfg, Lir, Xv, Xl,
and, for `machine` cases, the typed x86 machine and ByteEval) and, with
`--native`, natively as test executables IxCC writes, with the expectations
above. A failure names the root, the case, the level and both observations.
`--survey` only compiles each root and prints `compiled` or its `stage: code`
against the manifest's (for reviewing a new family), and for a compiled root
what the closures step made of it: unchanged, or its entries, closure keys,
dispatchers and dispatch work against the budget P8 refuses past; `--dump`
adds the Anf (after the closures step), Lir and Xv of a root declined at
allocation or later. `--observe` prints, as
tab-separated rows and without assertions, every case of every compiled root
at Cfg, Lir, Xv, Xl and (with `--native`) natively, beside the manifest's `fail`
and `spurious` marks (for reviewing a new family's expectations and for
tabulating a boundary family). A native run is one test executable per
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
   For a boundary or resource fixture, `--observe --native` shows each case's
   outcome at every word level and natively: mark each status 3 the source
   explains as `fail` (or `allow`), and one it does not as `spurious` too.
5. `lake exe tests-corpus MANIFEST --native`; a level disagreement or a wrong
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

With no inputs it checks every registered corpus family. Repeated
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

Every committed closure is a function of the producer (this repository's
`ix`, its Lean libraries, the toolchain) and of the sources. When `ix`'s
output changes (the Ixon format, the closure it selects, the role table, the
canonical sharing), every family is regenerated at once, and nothing is
written by hand: closures, sidecars, censuses, values, manifests, tables and
generated modules all come from one command. A regeneration with an unchanged
producer changes nothing.

```sh
# in ix's dev shell, anywhere in the repository
IxCC/tools/regenerate.sh            # regenerate in place (a refreeze); then review the diff
IxCC/tools/regenerate.sh --check    # regenerate into a scratch export of HEAD and compare
```

It builds `ix` at the repository root with the root modules the fixtures' sources
import (`Ix.Compile.SourceContract.Elab`, which no default root target builds, so
that a cold checkout regenerates) and the IxCC tools, writes a `lake`
stand-in for `ix` (which asks `lake env printenv LEAN_PATH` where it
compiles; the stand-in answers with the root workspace's libraries), and
runs, in this order:

1. the tables, first, because the census and ingress read them: ix's fixture
   package (`refreeze-ixon package`: the root package's
   `Tests/Fixtures/ixon-v4/`, copied unchanged; its two handoff closures,
   `handoff/accepted.ixe` and `handoff/rejected-local-escape.ixe`, are the
   only unbound fixtures: ix's own generator writes them,
   `lake exe ixon-v4-tests --export-handoff` (`Tests/IxonV4Handoff.lean`, an
   environment without a role binding), and `ixon-v4-tests` checks the
   committed ones against it), the primitive table (`V3.PrimAddrs`,
   `IxCC/Ixon/V3/PrimAddrs.lean`; `refreeze-ixon tc-primitives`, from
   `Ix/PrimAddrs.lean`), the Src tables
   (`pin-src-tables`), then `Src.Pinned` and the fixed pins (`pin-src-tables
   --repin`); in place, the tools are rebuilt against them;
2. every family, in parallel: every `corpus.json` under `fixtures/` (the
   registered families of `IxCCTests.Corpus.families` and the unregistered
   `k1`, `ownership` and `phase2-arity`; a new family needs no change),
   `corpus rebuild` each; then ix's verdicts on the annotated ownership
   sources (`tests-own verdicts`), the RC real-source input (`refreeze-ixon
   rc-real-source`), and the roots-only fixtures (`pin-src-tables
   --diagnostics fixtures/ixon-v4/src-diag`, `--sortpoly
   fixtures/ixon-v4/src-sortpoly`);
3. the generated modules: `gen-src-artifacts` (with the K1 kernel tests'
   constants named by meaning, `Ids`), `gen-recheck-artifacts`, `corpus
   kernel-artifacts`, `tests-fir --render-artifacts`.

With `--check` it does this in a scratch export of `HEAD`, lists every file
that differs, and scans the committed tree for commits and absolute paths in
the fixtures, manifests, READMEs and generated modules (`tools/citations.sh
--fixtures`); it exits 0 only when nothing differs and nothing is cited. If
the tables differ it stops there (the tools built from the checkout would be
stale): regenerate in place. On a 64-core machine shared with other jobs it
takes about 13 minutes in place and 13 with `--check` (2026-11-12: 791 and 784
seconds, the families 516 and 488 of them). The slowest family is
`phase1-boundary` (seven fixtures in sequence, each compiled twice by `ix` and
interpreted once); its sources turn off what costs `ix` minutes at the field
limit (`genInjectivity`, `phase1-boundary/README.md`), without which the run
took 56 minutes.

Not regenerated, and why: the vendored Aiur snapshot and its reference
exports (not written by `ix`), and `fixtures/ixon-v4/bench-k1/steps.json` (a
measurement of the compiled code, checked by `check-steps`, rewritten by
`check-steps --write`).

**One family** (a new or changed family; others are left as they are):

```sh
LEAN_PATH=$($FAKE/lake env printenv LEAN_PATH) \
  IxCC/.lake/build/bin/corpus rebuild MANIFEST --ix $IX --ix-path $FAKE   # from IxCC/
lake exe corpus check MANIFEST
```

then its dependants only: `tests-own verdicts` after `ownership`;
`gen-src-artifacts` and `gen-recheck-artifacts` after `bench-k1`; `corpus
kernel-artifacts` after `bench-k1` or `phase1-scalar`; the K1 equation counts
(below) after `k1` or `bench-k1`; then the ledger pins.

**The manual steps, all reviews:**

1. **The manifests.** With the fields a regeneration may change removed, the
   old and new manifests are equal; a difference (a source, root, case, value,
   decline, failure list) is a stop-and-review:

   ```sh
   norm='del(.producer, .lean.version) | .fixtures |= map(del(.source.sha256, .closure.sha256,
     .closure.bytes, .equations.sha256, .equations.equations, .named_env_sha256, .census.sha256)
     | .roots |= map(del(.address)))'
   diff <(git show HEAD:IxCC/$m | jq -S "$norm") <(jq -S "$norm" $m)
   ```
2. **The censuses.** A root whose ingress verdict changed, or a constant now
   refused at typing, is a finding.
3. **The verdicts** (`fixtures/ownership/verdicts.json`): a changed verdict
   or code is reviewed and recorded in the family's README.
4. **The reviewed counts in tests**, which a regeneration moves:
   `IxCCTests/IxonV3/K1.lean` (each K1 pack's equation count) and
   `IxCCTests/Src/Table.lean` (the K1 and bench-k1 tables' `eqn`, `case`,
   `prim` and `lazy` counts; `tests-src` prints the observed values first).
5. **The step baseline**: `check-steps`; if the emitted code changed, `lake
   exe check-steps --write` and review the diff as a performance change.
6. **The ledger**: `nix/lean-modules.json` (`check-build-graph --write`) and
   the integrity pins ("Routine updates" in
   [trusted-extern-ledger.md](trusted-extern-ledger.md)), reviewed by class.

The tests that name constants of the generated artifacts do so by meaning
(`Ids` in each Src artifact; the recheck tests find the root, `Nat`,
`Nat.succ`, `Eq` and an `eqn` subject in the program), so no renumbering is
manual.
