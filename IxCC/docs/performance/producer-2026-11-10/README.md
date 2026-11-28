# The producer's cost

**Question.** Where does `ixcc compile`'s producer spend its time, which of its
steps grow faster than linearly, and what did rewriting them change? The
producer is the untrusted half of produce-and-recheck: everything `ixcc compile`
does that `ixcc check-cert` does not (the unfolding table's build, admission,
the middle end's oracles and schedule `Anf.Pipeline.produce`, allocation with
its validated fallback, frame layouts, tunnelling and the block order), and the
relevance annotator, which `check-cert` re-runs as its Stage A. Its output is
checked, so it may be rewritten freely; the rewrites here keep its output
byte-identical on every committed program.

This is a current record (2026-11-10), listed among the current reports of the
[index](../README.md).

## Setup

- **Host.** The shared build box: an Intel Xeon 6975P-C, 64 logical CPUs (one
  socket, two threads per core), 495 GB of memory, Linux 7.0.0-1014-aws. Other
  sessions used it throughout: the load average was between 15 and 39. Up to
  four of these measurement processes ran at once, each single-threaded, and
  the validation build and suites overlapped the later scaling repetitions. No
  core pinning, frequency or SMT control. Times are therefore indicative; the
  allocation counts below are deterministic.
- **Toolchain.** Lean 4.34.1 (`lean-toolchain`); `ixcc` and `tests-recheck`
  built with `lake build` in the development shell from a warm Lake cache.
  Times are of the built executables, never of compilation.
- **Builds compared.** *Before*: IxCC as of 2026-11-10 with every certificate
  list capped, before these changes (and before the result-row and
  source-step-counter changes of the same day); the executables carry only the
  measurement code on top. *After*: the same tree with the producer changes
  described here. The timings below compare those two. The output identity
  was checked again after those later changes had been merged, between the
  merged tree and the tree without the producer changes (see "Committed
  programs").
- **Timers.** `/usr/bin/time` (wall time, peak resident memory) around
  `ixcc compile` and `ixcc check-cert`; `ixcc --stats` (milliseconds of
  reading, ingress, producing and the re-run); `tests-recheck --perf-stages`
  and `--perf-anf`, which time each stage with `IO.monoNanosNow` and count its
  allocations (the runtime's heartbeat count, `IO.getNumHeartbeats`: one per
  small object allocated, the same on every run of one build and input).
- **Inputs.** The committed programs: every closure under `fixtures/` with an
  `ixcc/k1-equations/1` sidecar (50 closures), compiled with all their roots and
  with each root alone, under `--rc off`, `on` and `auto`: 645 runs. Scaling
  closures written by `tests-recheck --perf-write DIR SHAPE N`
  ([`IxCCTests/Recheck/Perf.lean`](../../../IxCCTests/Recheck/Perf.lean)):
  `fns n` (n + 1 distinct non-recursive functions, each a 127-constructor
  tree over two calls of earlier functions; `fns6` the same with 63
  constructors), `many n` (n identity functions each calling the next, which
  the inliner collapses), `deep n`, `body d`, and the share DAGs `dag d`,
  `tree d` and `wide d` (an expansion of 2^(d+1) − 1 calls or constructors
  stored in d + 1 nodes). Anf-level shapes through the back end alone
  (`--perf-anf`): `loop0 k` (a self-recursive loop of k two-way branches in
  sequence), `case2 n` (two-way cases nested n deep) and the back-end budget
  shapes of `Deep.chainProgram`.

## Harness

The scripts are in this directory; run them from an `IxCC` directory in the
development shell, with the executables built.

- [`cli.sh`](cli.sh) `IXCC OUT.tsv PROGRAMS [MODES] [PERROOT]`: `ixcc compile`
  then `ixcc check-cert` on the emitted certificate, per closure, mode and
  (with `PERROOT=1`) root; wall time, peak memory, the `--stats` stage times,
  output sizes and the SHA-256 of the certificate and the object. `NOTC=1`
  passes `--no-typecheck` to both commands, which changes neither output.
- [`rep.sh`](rep.sh) `OUTDIR REPS LIST MODES TAG=IXCC...`: `cli.sh` repeated,
  interleaving the builds within each repetition.
- [`stages.sh`](stages.sh) and [`anf.sh`](anf.sh): `tests-recheck --perf-stages`
  and `--perf-anf` over a list, with wall time and peak memory
  (`PERF_DETAIL=1` adds the allocator's and `Backend.finish`'s parts).
- [`summarize.sh`](summarize.sh) `OUTDIR`: the identity comparison, the slowest
  compiles and the scaling medians (of `OUTDIR/notc-{base,final}.tsv`,
  `OUTDIR/typed-{base,final}.tsv` and `OUTDIR/scale/{base,final}.N.tsv`, the
  files the runs above wrote); [`scaletable.sh`](scaletable.sh) the scaling
  table below; [`compact.sh`](compact.sh) the raw tables here.

The raw tables are [`identity.tsv`](identity.tsv) (645 runs without and with the producer changes on the merged tree, with
`--no-typecheck`), [`typed.tsv`](typed.tsv) (every closure with typing, `--rc
off`, both builds) and [`scaling.tsv`](scaling.tsv) (three interleaved runs of
each build over the scaling closures).

To reproduce, with `B` and `A` the two builds' `ixcc` and the scaling closures
written to `in/` by `tests-recheck --perf-write in SHAPE N`:

```bash
NOTC=1 ./cli.sh B out/notc-base.tsv programs.txt "off on auto" 1
NOTC=1 ./cli.sh A out/notc-final.tsv programs.txt "off on auto" 1
./cli.sh B out/typed-base.tsv programs.txt off 0
./cli.sh A out/typed-final.tsv programs.txt off 0
./rep.sh out/scale 3 scale.txt off base=B final=A
./summarize.sh out
```

where `programs.txt` lists each committed closure and its sidecar (every
`fixtures/**/X.ixe` with an `X.equations.json`, and `fixtures/ixon-v4/k1/k1.ixe`
with `equations.json` and `fixtures/rc/real-source/anonymous.ixe` with
`consumer.equations.json`), and `scale.txt` the scaling closures likewise.

## Findings

### Committed programs

Every committed program compiles to the same certificate and object with and
without the producer changes, compared on the merged tree of 2026-11-10 (with
the result-row and source-step-counter changes; without them the comparison
gave the same counts):
642 of the 645 runs agree byte for byte (543 compiled, 99 refused with
the same message). The other three are one root, `SrcDiag.rootFloat` of
`fixtures/ixon-v4/src-diag` under each `--rc` mode, refused both times: before,
in the producer's middle end (`anf.produce: inline global 22: walk: copy
budget exhausted`); after, the producer does not take the inline round the
re-run would refuse, and the program is declined at the Anf → Fir boundary for
its closures (`fir.closures`), the construct it actually lacks.

The producer is not what makes them slow. Without erased typing every
committed program compiles (`ixcc compile`, the re-run included) in under 5 s
and checks (`ixcc check-cert`) in under 4.1 s; the slowest producer is
`tags125` (3.5 to 4.6 s), nearly all of it the relevance annotator
(`Src.Relevance.annotate`, 3.5 s), which `check-cert` also runs. With typing,
which `ixcc compile` and `ixcc check-cert` both run by default at ingress,
the 1 MB closures take 35 to 75 s each (with the box's load) and the 3.7 MB `strings` decline
fixture 240 to 310 s; typing is the same before and after.

One run per build, `ixcc compile` with every root and `--rc off`, then `ixcc check-cert` on its
certificate; erased typing on (the default). Both runs overlapped validation builds on the shared box,
which explains why ingress, the same code in both builds, varies between them by up to 1.6 times.

| Closure (all roots) | Before: compile s | ingress / produce ms | check-cert s | After: compile s | ingress / produce ms | check-cert s |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `strings` | 270.25 | refused |  | 253.98 | refused |  |
| `diag` | 71.44 | refused |  | 78.90 | refused |  |
| `prime-count` | 44.29 | 44124 / 110 | 49.37 | 73.45 | 73171 / 183 | 55.77 |
| `scalar` | 49.36 | 48898 / 270 | 49.95 | 56.09 | 55615 / 284 | 52.28 |
| `ackermann` | 36.02 | 35922 / 49 | 36.33 | 55.40 | 55296 / 49 | 45.84 |
| `k1` | 47.60 | 47427 / 109 | 49.89 | 54.77 | 54593 / 110 | 56.47 |
| `collatz` | 46.04 | 45875 / 103 | 40.42 | 46.79 | 46542 / 173 | 64.91 |
| `loops` | 46.71 | 46547 / 99 | 50.17 | 38.50 | 38331 / 98 | 38.07 |
| `resource` | 46.22 | 46043 / 112 | 45.30 | 40.46 | 40263 / 113 | 54.09 |
| `sum-loop` | 43.80 | 43646 / 91 | 40.99 | 45.21 | 45013 / 125 | 46.83 |
| `tags125` | 5.44 | 1753 / 3533 | 5.73 | 5.32 | 1731 / 3458 | 5.12 |

### Scaling

`ixcc compile` then `ixcc check-cert`, `--rc off`, erased typing on, the median of three runs of
each build interleaved (two for `fns 1000` before: one run was stopped by mistake). The produce and
re-run columns are `--stats`' milliseconds.

| Closure | Before: compile s (produce / re-run ms) | check-cert s | After: compile s (produce / re-run ms) | check-cert s |
| --- | ---: | ---: | ---: | ---: |
| `dag 12` | 0.09, refused |  | 0.09, refused |  |
| `dag 16` | 1.05, refused |  | 1.03, refused |  |
| `dag 20` | 1.37, refused |  | 1.36, refused |  |
| `tree 16` | 1.06, refused |  | 1.08, refused |  |
| `wide 16` | 0.93, refused |  | 0.95, refused |  |
| `deep 500` | 1.17 (717 / 238) | 0.44 | 1.53 (814 / 367) | 0.45 |
| `deep 1000` | 0.09, refused |  | 4.34 (2678 / 863) | 1.60 |
| `body 8` | 0.35 (178 / 107) | 0.17 | 0.31 (150 / 105) | 0.18 |
| `body 10` | 2.06 (1171 / 744) | 0.81 | 1.76 (935 / 686) | 0.77 |
| `many 500` | 0.34 (179 / 43) | 0.16 | 0.28 (142 / 36) | 0.15 |
| `many 1000` | 0.67 (367 / 82) | 0.32 | 0.58 (296 / 81) | 0.31 |
| `many 2000` | 1.76 (1074 / 191) | 0.74 | 1.31 (624 / 185) | 0.73 |
| `many 4000` | 5.19 (3277 / 465) | 1.99 | 3.29 (1342 / 481) | 1.99 |
| `fns 100` | 4.28 (2124 / 1818) | 2.09 | 3.97 (1851 / 1686) | 2.08 |
| `fns 200` | 9.46 (4651 / 4240) | 5.19 | 8.77 (3767 / 4182) | 4.96 |
| `fns 500` | 30.19 (11089 / 17407) | 19.38 | 27.81 (9447 / 16693) | 19.51 |
| `fns 1000` | 79.68 (21950 / 54085) | 56.89 | 79.72 (19731 / 56456) | 60.65 |
| `fns 2000` | 48.01, refused |  | 4.82, refused |  |
| `fns6 500` | 12.14 (5237 / 5817) | 7.02 | 12.13 (5352 / 5879) | 6.84 |
| `fns6 1000` | 29.53 (10821 / 16825) | 19.18 | 28.10 (9545 / 16659) | 19.61 |
| `fns6 2000` | 84.01 (24554 / 54964) | 60.68 | 81.15 (20311 / 56244) | 61.31 |
| `fns6 3000` | 159.26 (36919 / 114568) | 124.52 | 156.81 (31546 / 117176) | 123.67 |

From 100 to 1,000 functions (`fns`) the producer's time grows with exponent 1.03 after (1.0 before
but for the P3 oracle) and the re-run's with 1.52; from 500 to 3,000 (`fns6`) the producer's with
0.99 and the re-run's with 1.67. On `many` (500 to 4,000) the producer's exponent falls from 1.40
to 1.08. 3,001 functions of 63 constructors (`fns6 3000`) compile and are accepted in 157 s, 117 s
of it the re-run.

Per stage, from `tests-recheck --perf-stages` (one run each; milliseconds,
`--rc off`):

| Closure | Producer before | Producer after | Checker after | Allocator after | Block order before → after | P3 oracle before → after |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `fns 100` | 2,227 | 1,963 | 1,742 | 1,214 | 98 → 67 | 3.4 → 3.0 |
| `fns 200` | 4,397 | 3,698 | 4,296 | 2,218 | 155 → 141 | 10.2 → 8.3 |
| `fns 500` | 10,694 | 9,748 | 17,440 | 5,709 | 405 → 513 | 52 → 21 |
| `fns 1000` | 22,429 | 20,132 | 56,648 | 11,936 | 1,019 → 1,079 | 234 → 50 |
| `fns 2000` | 45,240, then refused by the re-run | 2,451, refused by its middle end | | | | 1,106 → |
| `fns6 2000` | | 18,901 | 55,648 | 11,212 | → 993 | → 57 |
| `many 1000` | 363 | 269 | 78 | | | 109 → 30 |
| `many 2000` | 1,042 | 575 | 179 | | | 455 → 71 |
| `many 4000` | | 1,300 | 463 | | | → 187 |
| `deep 500` | 680 | 545 | 234 | 489 | | |
| `deep 1000` | refused (shrink walk budget) | 2,534 | 829 | | | |
| `dag 16` | 1,021, refused (Lam nodes) | 988, refused (Lam nodes) | | | | |

On `fns`, the producer's allocations grow exactly linearly (76, 152, 380 and
761 million at 100, 200, 500 and 1,000 functions) and its time with them
(exponent 1.01 from 100 to 1,000); the checker's time grows with exponent 1.5,
its `Backend.finish` (E1 encoding with E2's stream check, and the ELF writer)
with 1.7 while finish's allocations stay linear (25.5, 51.0, 127.5 and 255.0
million), so the cost is in copying large byte arrays. The stages, ranked by
cost at `fns 1000` after: the allocator (`Alloc.runProducer`, 11.9 s: linear
scan about three quarters, its validation the rest), selection (1.3 s), stacking (2.3 s, the
checker's own pass), the block order (1.1 s), the relevance annotator (0.9 s),
`Rt.lower` (0.8 s, the checker's), shrink (0.7 s); all linear in allocations.
Under `--rc on` the plain-RC producer adds ownership code and RC lowering, both
linear (`fns 500`: 15.2 s, 10.7 s of it allocation; the plain-RC re-run 12.3 s).

The back end alone, from Anf (`--perf-anf`, the block order in ms):

| Shape | Before | After |
| --- | ---: | ---: |
| `loop0 12` | 0.4 | 0.0 |
| `loop0 16` | 3.8 | 0.0 |
| `loop0 20` | 49.8 | 0.0 |
| `loop0 24` | 870.7 | 0.1 |
| `loop0 400` | not run (the frontier doubles at each of 400 branches) | 1.3 |
| `case2 500` | 13.3 | 2.1 |
| `case2 1000` | 59.4 | 4.6 |
| `case2 2000` | 203.1 | 10.0 |

### What was super-linear, and the fixes

| Step | Was | Now | Output |
| --- | --- | --- | --- |
| `X86.Layout.Order.produce` (block order) | quadratic in a group's blocks: the depth-first search searched its path list at every edge, each chain start filtered every pending block and scanned every loop; exponential in the two-way branches of a loop body: the natural-loop search expanded a block once per path to it, doubling its frontier at each branch | near-linear: the path is a set, each header's loop is one breadth-first walk from all its latches that expands each block once, each block lists its loops smallest first, and the next chain's start comes from per-loop cursors that only move forward; still kernel-evaluable (`IxCCTests.Backend.KernelEval`) | identical |
| `Anf.Inline.produce` (P3 oracle) | quadratic in the globals: the recursive-global set took a reachability walk from every global; each reference re-measured its callee and searched the caller's sites as a list | linear: Tarjan's components with explicit stacks, inlinability decided once per global, sites a set | identical |
| `Anf.Specialize.produce` (P4 oracle) | masks an association list searched per call site, callees deduplicated by a quadratic search | maps | identical |
| `Anf.Shrink.produce` (P2 oracle) | its certificate searched the results once per global id | a map | identical |
| `Xv.Alloc.run` as the producer used it | validated every function twice (when choosing between linear scan and the fallback, then again for the whole program) | `Alloc.runProducer`: once; `Alloc.run`, which `Backend.alloc_validated` is stated of, is unchanged | identical |
| `Anf.Pipeline.produce` (schedule) | did not apply the re-run's budgets: a program past them was produced in full, back end included, and refused afterwards by the re-run (`fns 2000`: 45 s); a shrink round past a walk's budget failed the compile (`deep 1000`); the certificate's caps on steps, callees and decisions were not kept | the re-run's size, depth and work check after P1 and every shrink step, refused there with the re-run's message; inline rounds and specialisations taken through the re-run's own step; shrink rounds stop where the re-run would refuse the next; the caps kept | identical where the re-run accepts every step; elsewhere a refusal, sooner, or a certificate the re-run accepts |

A share DAG of depth 16 (a closure of under 1 KB whose root expands to 2^17
calls) was once seen to make `ixcc compile` run for more than 180 s; with the
middle end's Lam budget checked in the producer it was already refused
before these changes, and it still is, in about 1 s (`dag 16`, `tree 16`, `wide 16`).
At depth 10 these shapes are past the Anf depth budget and are now refused at
P1, in 15 ms.

### Regression test

`tests-recheck` (in the required `suites` check; alone with `tests-recheck
--producer`) compares each rewritten oracle with a verbatim copy of the code it
replaced (`IxCCTests.Recheck.ProducerRef`) on generated Lir programs, the
Anf-level loop and chain shapes, 250 generated Lam programs at every stage of
the pipeline, and the scaling closures; checks the budget behaviour above; and
counts the allocations of the block order, the middle end and the whole
producer on scaling inputs four times apart, which must stay within eight
times: near-linear growth passes (2.3 to 4.3 times today), a quadratic step
that allocates (16 times) or an exponential one fails, whatever the machine's
load. `tests-recheck --producer-reference` counts the same for the replaced
code: its block order allocates 133 and 215 times more on a loop of 16 branches
than on one of 4 (with empty and with working arms; at the test's 8 and 32 it
would not finish), its P3 oracle 14.8 times more on a
chain of 1,000 calls than of 250. Scans that allocate nothing escape the count:
the replaced block order's quadratic chain starts grow only 3.9 times in
allocations on nested two-way cases. The block order is therefore also timed
against the replaced code on 2,000 nested two-way cases, in the same process,
the least of three runs each, and must be at least four times faster (16 to
18 times in the runs here). Allocation counts do not see time spent copying large
arrays either, which is how the checker's `Backend.finish` grows; the
producer has no such step today.

## What remains

- **The checker's back end.** `Backend.finish` (`Stream.encodeK` and
  `ELF.writeCheckedK`) grows about quadratically in the object's text (`fns`:
  0.9, 2.6, 13.0 and 46.5 s at 100, 200, 500 and 1,000 functions), so compile
  time on large closures grows with exponent about 1.5 though the producer's
  is 1.0. It is the checker's code; making it linear is a change to the
  checked path.
- **Erased typing at ingress**: 35 to 75 s per 1 MB closure and 240 to 310 s
  on `strings` (3.7 MB), in both `compile` and `check-cert`.
- **The relevance annotator**, which Stage A re-runs: 3.5 s on `tags125`.
- **The checker's budgets bound closure size.** 2,001 functions of 127
  constructors are past `maxBackWork`; 2,001 of 63 compile and are accepted
  (about 80 s, 56 s of it the checker).
- **Linear scan** is linear but heavy (about 7 µs and 330 allocations per Xv
  instruction), and grows somewhat faster than linearly in the values live at
  once (`live 100`: 560 allocations per instruction, `live 200`: 970).
