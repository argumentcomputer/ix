# Benchmark fixtures, first wave (K1–K3)

These are the programs for the K1–K3 rungs of the benchmark ladder (roadmap
§9). Each fixture has a Lean program that Lean 4.34 compiles, plus a C or C++
twin that prints the same output. The data is in
[`manifest.json`](manifest.json), and [`Check.lean`](Check.lean) checks it.

| Fixture | Rung | Variant | Source | Twin | Test args | Bench args |
| --- | --- | --- | --- | --- | --- | --- |
| [`fib`](fib) | K1 | upstream | Compilatr.ix `fixtures/ixon-v3/k1/K1.lean` | `fib.c` (original) | `25` | `40` |
| [`sum-loop`](sum-loop) | K1 | upstream | same | `sum_loop.c` (original) | `1000000` | `100000000` |
| [`ackermann`](ackermann) | K1 | upstream | same | `ackermann.c` (original) | `3 6` | `3 10` |
| [`tak`](tak) | K1 | upstream | same | `tak.c` (original) | `18 18 12 6` | `24 24 16 8` |
| [`gcd`](gcd) | K1 | upstream | same | `gcd.c` (original) | `1071 462` | `F(91) F(90)` |
| [`nqueens`](nqueens) | K2 | port | Koka `test/bench/koka/nqueens.kk` | Koka `cpp/nqueens.cpp` (unchanged) | `8` | `13` |
| [`queue`](queue) | K2 | port | CakeML `cakeml_benchmarks/cakeml/queue.cml` | `queue.c` (original) | `1000` | `5000000` |
| [`reverse`](reverse) | K2 | port | CakeML `reverse.cml` | `reverse.c` (original) | `1000` | `50000` |
| [`foldl`](foldl) | K2 | port | CakeML `foldl.cml` | `foldl.c` (original) | `1000` | `40000` |
| [`list-qsort`](list-qsort) | K2 | port | CakeML `qsort.cml` | `list_qsort.c` (original) | `500` | `10000` |
| [`rbmap`](rbmap) | K3 | upstream | Lean `tests/compile_bench/rbmap.lean` | Koka `cpp/rbtree.cpp` (unchanged) | `100000` | `2000000` |
| [`rbmap_checkpoint`](rbmap_checkpoint) | K3 | upstream | Lean `rbmap_checkpoint.lean` | `rbmap_checkpoint.cpp` (persistent tree) | `100000 10` | `2000000 1` |
| [`const_fold`](const_fold) | K3 | upstream | Lean `const_fold.lean` | Koka `cpp/cfold.cpp` (adapted) | `15` | `23` |
| [`binarytrees`](binarytrees) | K3 | total | Lean `binarytrees.lean` | Koka `cpp/binarytrees.cpp` (adapted) | `14` | `21` |
| [`rbmap_fbip`](rbmap_fbip) | K3 | upstream | Lean `rbmap_fbip.lean` | the `rbmap` twin | `2000` | `2000000` |

The source commits are:

- Lean `v4.34.0`, `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`;
- Koka `8b803da69d3941ce1e03173578093aefc41ee548`;
- CakeML `530c7deec135ad421cce7ca768eed2f5801261b2`;
- Compilatr.ix `2e4740dea324ab0122e909613687d2b812eab4e0`.

The bench arguments for Lean fixtures come from the upstream `.init.sh`. For
the ports they are the constants in the upstream program. For K1 they were
chosen here, and the manifest records where each value comes from.

## Variants

- **upstream**: the upstream definitions, unchanged. Only `main` is replaced,
  by a pure `entry` and a `main` that prints `entry`'s result in the upstream
  format, so the upstream `.out.expected` still applies. `const_fold` is in
  this class: only its `unsafe def main` is replaced. The K1 definitions are
  verbatim from `fixtures/ixon-v3/k1/K1.lean` in this repository.
- **total**: a minimal, reviewed rewrite of an upstream program that uses
  `partial`, Tasks or computation in `IO`. The upstream file stays in
  `upstream/` as the recorded rejection, and `VARIANT.md` gives the diff and
  the rationale. In this wave, only `binarytrees` is total.
- **port**: a Lean translation of a program written in another language
  (Koka, CakeML). There is no upstream Lean program to diff against, so
  `VARIANT.md` maps upstream functions to Lean definitions and lists every
  deviation. Ports are reviewed like total variants. This class is not in the
  roadmap's list; it covers the K2 sources, which have no Lean original.
- **annotated**: an ix contract-syntax variant, for later comparison
  (`rbmap_fbip` is kept for this). None exist yet.
- **synthetic**: Lir or Ixon programs, for backend work only and never
  reported as real-program results. They are not part of this pack.

Every Lean program avoids `partial`, `unsafe`, `Task`, `implemented_by`,
`extrinsicFix` and the polymorphic range syntax `a...b`, and it does not
compute inside `IO`. Loops use `[0:n]`. The checker scans the code for these
words, ignoring comments and strings. `entry` is the closure root for
compilation, and the manifest records its type.

## Layout

```
manifest.json       one record per fixture (see below)
Check.lean          the checker
LICENSES/           upstream licence texts
<fixture>/
  upstream/         byte-identical upstream files (program, .init.sh, .out.expected, twins)
  <Name>.lean       the variant: definitions, `entry`, `main`
  <twin>.c / .cpp   the twin, when it is not an unchanged file in upstream/
  expected.txt      output at the test arguments
  VARIANT.md        diff or translation notes, and twin notes (all but K1)
```

A manifest record gives:

- `name`, `rung` and `variant`;
- `source` (repository, commit, path, licence);
- `vendored` (each file in `upstream/` with its upstream repository and path);
- `lean.path`, and `lean.verbatim`, the relation to upstream that the checker
  verifies;
- `entry` (name and type);
- `test_args`, `bench_args` and `bench_args_source`;
- `env`, the runtime environment (`const_fold` inherits
  `LEAN_STACK_SIZE_KB` from its `.init.sh`);
- `expected`, and `oracle` (the upstream `.out.expected`, or a computed
  constant with its derivation);
- `bench_expected`, the bench-size output on which the Lean program and its
  twin agree (a cross-check, not an upstream oracle);
- `twin` (path, language, origin, compile command, notes).

## Twins

Twins are natural C or C++ for the same computation. They are built with
`clang -O2` (C) or `clang++ -O2 -std=c++17` (C++), plus `-pthread` for
`binarytrees`.

- **Upstream twins** are used unchanged where possible: Koka `nqueens.cpp`
  and `rbtree.cpp`.
- **Adapted twins** read the size from `argv` and print in Lean's format:
  - `cfold.cpp`: upstream `const_folding` skips the recursive folding that
    Koka's `cfold.kk` and Lean both do; the twin restores it.
  - `binarytrees.cpp`: it runs one worker thread by default, to match the
    single-threaded Lean variant.
- **`rbmap_checkpoint.cpp`** is a persistent red-black tree. Both upstream
  twins copy a whole `std::map` per checkpoint (about 24 GB live at the test
  arguments) and print a different line. They are vendored for reference.
- **Lean's `rbmap_cpp_std.cpp`** needs Lean's in-tree C++ runtime headers and
  `libleanrt`. It is vendored for reference; the `rbmap` twin is Koka's
  equivalent `rbtree.cpp`.
- **The K1 and CakeML twins** were written for this pack. They mirror the
  Lean algorithm over `malloc`ed cells, updating cells in place where Lean's
  reference counting would reuse them. K1 twins use `uint64_t`, which is exact
  for the recorded arguments; each record states its domain.

## Running the checks

From the repository root, in the development shell, which provides Lean
4.34.0 and Clang 21 (as `cc` and `c++`; the `clang` first on its `PATH` is
Lean's bundled one):

```sh
nix develop -c bash -c 'lean --run benchmarks/fixtures/Check.lean \
  --cc "$(command -v cc)" --cxx "$(command -v c++)" --refs plans/refs --interpret'
```

or, with explicit paths:

```sh
LEAN=/nix/store/…-lean-4.34.0/bin/lean
CLANG=/nix/store/…-clang-wrapper-21.1.2/bin/clang
$LEAN --run benchmarks/fixtures/Check.lean --cc $CLANG --cxx $CLANG++ \
  [--refs plans/refs] [--interpret] [--bench] [--only rbmap,fib] [--work DIR]
```

The checker finds `lean` and `leanc` next to the Lean binary that runs it.
For each fixture it runs these checks:

1. **Forbidden constructs.** The Lean code uses none of the words listed
   above.
2. **Verbatim.** The K1 definitions occur verbatim in
   `fixtures/ixon-v3/k1/K1.lean`, and the text of an upstream-variant Lean
   file before `def main` occurs verbatim in the variant.
3. **Oracle.** `expected.txt` equals the upstream `.out.expected`.
4. **Vendored files** (`--refs`). Each file in `upstream/` matches the
   reference checkout byte for byte.
5. **Lean, compiled.** It is compiled as upstream `run_test.sh` does
   (`lean -c`, then `leanc -O3 -DNDEBUG`), run at the test arguments, and its
   output compared with `expected.txt`.
6. **Lean, interpreted** (`--interpret`). `lean --run` gets the same
   comparison.
7. **Twin.** It is built with its manifest command, run, and compared.

`--bench` uses the bench arguments and compares with `bench_expected` and the
Lean output. It raises the stack limit to the hard limit, as upstream
`set_stack_size_to_maximum` does. The checker exits with 0 only when every
check passes. Build products go to `--work` (default
`plans/c4-fixtures/build`, which is not tracked). These checks are
correctness checks, not measurements; timings come from the measurement
runner (roadmap §8).

## Licences

Vendored and derived files keep their upstream notices. Each modified file
starts with a notice saying that it was modified.

- **Lean 4**: Apache-2.0 ([`LICENSES/lean4-LICENSE`](LICENSES/lean4-LICENSE)).
  This covers `tests/compile_bench/*` and `tests/bench/*_cpp_std.cpp`, and
  the K3 variants derive from them.
- **Koka**: Apache-2.0, © Microsoft Research and Daan Leijen
  ([`LICENSES/koka-LICENSE`](LICENSES/koka-LICENSE)). This covers
  `nqueens.kk` and the `cpp/` twins. Koka's `binarytrees.cpp` is a Computer
  Language Benchmarks Game program, which that project distributes under the
  3-Clause BSD licence; its contributor notice is kept.
- **CakeML**: BSD-3-Clause
  ([`LICENSES/cakeml-LICENSE`](LICENSES/cakeml-LICENSE)). This covers the
  `.cml` programs, and the K2 ports derive from them.
- **Compilatr.ix**: the K1 definitions and the original twins are under the
  repository's licence (Apache-2.0 or MIT).

## Admission census (2026-09-29)

Each fixture's pure `entry` closure was compiled with `ix compile --consts entry
--equations --anon` (ix `9c4b9c65`, see [`fixtures/ixon-v3/k1`](../../fixtures/ixon-v3/k1/README.md))
and run through `lake exe census`. Every constant of every closure passes
strict decoding, erased typing and the D12 policy stage; the next stage is the
rebuilt pipeline's `src`.

| Fixture | Constants | Unfolding equations | Deepest expression |
| --- | ---: | ---: | ---: |
| fib | 55 | 2 | 28 |
| foldl | 71 | 3 | 42 |
| nqueens | 144 | 8 | 36 |
| tak | 149 | 5 | 42 |
| reverse | 227 | 11 | 44 |
| rbmap_fbip | 246 | 10 | 52 |
| gcd | 265 | 7 | 46 |
| rbmap | 416 | 12 | 50 |
| queue | 421 | 11 | 46 |
| const_fold | 441 | 16 | 46 |
| rbmap_checkpoint | 608 | 22 | 53 |
| ackermann | 1,405 | 34 | 66 |
| list-qsort | 1,491 | 37 | 58 |
| binarytrees | 1,502 | 37 | 58 |
| sum-loop | 1,540 | 34 | 58 |

The largest closures come from well-founded recursion and `for` loops: their
termination proofs pull in `Nat`/`omega` lemmas, which relevance analysis
will erase. All are within the v3 consumer budgets, the tightest being 4,096
typing declarations and depth 256.

## Measurement notes (first local session, 2026-09-29)

The first [runner](../runner/README.md) session (10 paired blocks, whole-process
wall time) showed three properties of these fixtures that any comparison must
account for:
- **`sum-loop`'s twin folds to a closed form.** Clang at `-O2` and `-O3`
  replaces `for (i < n) s += i` with arithmetic, so the twin's row (2–3 ms at
  `n = 10⁸`) measures process startup, not a loop. Compare Compilatrix with
  `lean-clang` on this fixture, or add a twin whose loop cannot be solved in
  closed form.
- **`tak` and `gcd` are startup-dominated.** At their bench arguments every
  row finishes in under 10 ms, so process and runtime initialisation dominate.
  Their ratios need the in-process entry profile with repetition counts
  ([benchmark design](../../docs/benchmark-plan.md), "Timing boundaries").
- **Two twins are slower than Lean.** `rbmap_checkpoint` (a persistent-tree
  twin) and `const_fold` (Koka's `cfold.cpp`) allocate through `malloc`/`new`
  and take 1.4× and 2.1× `lean-clang`'s time. These rows compare allocators
  as much as code generation.
