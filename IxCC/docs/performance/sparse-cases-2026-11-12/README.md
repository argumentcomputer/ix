# Sparse casesOn as `lazy` rows: before and after

**Question.** Lean elaborates a `match` that names some constructors and ends
in a catch-all through a per-program definition, a sparse casesOn
(`T…._sparseCasesOn_N`), whose arms are ordinary arguments. IxCC read it as an
ordinary definition, so SrcEval and the compiled code evaluated every arm
before the match chose one. Since 2026-11-12 the unfolding table gives each
sparse casesOn a `lazy` row, recognised by its shape
(`Src.Table.checkSparseCases`; [compiler design](../../compiler-design.md),
"Unfolding-table entries"). What did that change in cost and in outcome, and
did any registered program get worse?

This is a current record (2026-11-12).

## Setup

- **Host.** The shared build box: an Intel Xeon 6975P-C, 64 logical CPUs, 495
  GB of memory. Other sessions used it throughout (load average 42–49); no core
  pinning. Times are wall times of one process each, so indicative; step counts
  and hashes are deterministic.
- **Builds compared.** *Before*: `ixcc` at `482f194e3` (branch
  `jcb/ixck-ixcc-merge`). *After*: the same tree with the change
  (`jcb/ixcc-sparse-cases`, production code as of `cb7ab1069`). Both built with
  `lake build` in the development shell.
- **Programs.** K2 `queue` (`benchmarks/fixtures/queue`) and the diagnosis's
  minimal program (`minD`, `minH`: an untaken `[]` arm that needs `n` frames of
  stack or allocates `n` cells; the same shapes as the fixture
  `phase2-closures/sparse`), frozen with this tree's `ix`; the registered corpus
  families.
- **Lean.** Lean 4.34.1's compiler (`lean -c`, `leanc -O3 -DNDEBUG`) on the
  same sources.

## K2 `queue`

`ixcc compile --exe` (stack 1 GiB, region 16 GiB), run natively; wall time and
peak resident memory of the process. *Plain RC* is the policy `--rc auto`
chose (both builds); *immortal* is `--rc off`.

| n | Before, plain RC | Before, immortal | After, plain RC | After, immortal | Lean |
| --- | --- | --- | --- | --- | --- |
| 1,000 | 0.03 s | 0.01 s, 23 MB | 0.00 s, 1.6 MB | 0.00 s, 1.6 MB | 0.00 s, 8.4 MB |
| 16,000 | 9.61 s | 11.94 s, 5.87 GB | | | |
| 100,000 | 597.5 s, 3.1 MB | (16 GiB region exhausted, heap plan) | 0.10 s, 3.1 MB | 0.03 s, 57 MB | 0.00 s, 10 MB |
| 5,000,000 | | | 4.65 s, 197 MB | 2.02 s, 2.93 GB | 0.22 s, 164 MB |

Every run printed `n / 2 − 1` (`499`, `7999`, `49999`, `2499999`), as Lean's
does. Before, each doubling of `n` multiplied the time by about four; after, by
about two. The object's text: plain RC 26,615 → 26,622 bytes, immortal 9,670 →
9,742 bytes. What remains (21× Lean at 5,000,000 under plain RC) is a constant
factor: the sparse casesOn is still compiled through `List.rec` with closures
for its minors and the closures step's dispatchers.

## Outcomes

`ixcc compile --exe` at the default executable layout (8 MiB stack, 64 MiB
region), the arm not taken (`b = 1`):

| Run | Before (immortal and plain RC alike) | After (both) | Lean |
| --- | --- | --- | --- |
| `minD 1 1000000` | `ixcc: stack exhausted`, exit 66 | `0` | `0` |
| `minD 1 10000000` | `ixcc: stack exhausted`, exit 66 | `0` | |
| `minH 1 10000000` | `ixcc: heap exhausted`, exit 65 | `0` | `0` |

## SrcEval steps

`src-steps` on the fixture `phase2-closures/sparse` (charged steps; the arm
counts `n` down): an untaken arm now costs nothing, a taken one two steps more
(its by-name slots are forced), the controls are unchanged, and every value is
the same.

| Root, (b, n) | Before | After |
| --- | --- | --- |
| `minS` (1, 10) / (1, 1000) / (1, 100000) | 408 / 34,068 / 3,400,068 | 50 / 50 / 50 |
| `minO` (1, 100000) | 3,400,066 | 48 |
| `minE` (1, 100000) | 3,400,138 | 120 |
| `minN` (1, 100000) (nested, as `queue`'s `checkf`) | 3,400,069 | 51 |
| `minD`, `minH` (1, 100000) | 3,100,067; 5,000,080 | 50; 50 |
| `minS` (0, 1000), taken | 34,050 | 34,052 |
| `sumS` (1, 100) / (1, 1000) | 177,924 / 17,079,024 | 7,824 / 78,024 |
| controls `minF`, `minM`, `sumF` | unchanged | unchanged |

On every case of every registered family (`src-steps --manifests`, 1,547
lines: cases, declined roots and skipped cases): the same results; the counts change only on `phase1-boundary`'s
`tags16`, `tags17` and `tags125`, whose untaken arms are literals: 139 → 133,
201 → 195, 224 → 210 and 210 → 196.

## Registered programs

Every root of every registered family and of `phase2-arity`, under `--rc off`,
`on` and `auto` (585 runs: 520 compiled, 65 declined), compiled by both builds:

- **Status, object and the declines' messages: identical in all 585 runs.**
  So the policy `--rc auto` chooses, the text size and the closures step's
  keys (`tests-corpus --survey`) are unchanged too (also compared directly).
- **Certificates** differ in 192 runs, whose closures contain a sparse casesOn
  (reached or not): in 183 only by the new `lazy` rows (the certificate's
  table lists every entry of the closure's table; three rows in the K1-style
  library closures: bench-k1 `ackermann`, `collatz`, `prime-count`,
  `sum-loop`, `phase1-scalar`, `phase1-resource`, `phase2-arity`,
  `phase1-decline`'s `loops`), and for the nine runs of `tags16`, `tags17` and
  `tags125` also in the middle end's trace (their Anf, 311 → 314 nodes, ends in
  the same object).

The new fixture's own roots: objects change where the match reaches a sparse
casesOn; text size falls or stays within 5 bytes (`minS` immortal 3,321 →
3,303; `minO` 1,227 → 1,098, and its `--rc auto` policy plain RC → zero RC;
`minH` immortal 3,417 → 3,422), closure keys unchanged.

## The benchmark programs that gain rows

K2 `list-qsort` (3 rows), K3 `rbmap` (2), `const_fold` (6) and `tokenise` (1),
frozen by the heap planner (`hpEntry`; the same closures for both builds),
compiled with stack 1 GiB and region 16 GiB, three runs each at the heap plan's
sizes (immortal only at the smaller size: the larger exhaust 16 GiB there);
*after* is the production code as of `d332ed96e`. Both builds compile every
program, and `--rc auto` chooses plain RC in every case.

| Program | Executables | Text, plain RC / immortal (bytes) | Plain RC: before → after | Immortal: before → after |
| --- | --- | --- | --- | --- |
| `list-qsort` | byte-identical | 4,002 / 2,243 | 10,000: 9.36, 9.68, 8.96 s → 8.25, 8.51, 8.90 s | 10,000: 2.79, 2.91, 3.05 s → 2.66, 3.00, 2.69 s |
| `rbmap` | differ | 539,823 → 539,542 / 162,331 → 162,177 | 100,000: 2.02, 2.04, 2.03 s → 1.95, 1.99, 1.98 s; 2,000,000: 53.6, 54.4, 56.7 s → 52.1, 52.4, 52.5 s | 100,000: 0.73, 0.70, 0.68 s, 1.28 GB → 0.61, 0.58, 0.58 s, 1.08 GB |
| `const_fold` | byte-identical | 203,522 / 70,892 | 20: 4.75, 5.11, 4.96 s → 4.77, 5.28, 5.32 s; 23: about 48–50 s both | 20: the same program |
| `tokenise` | byte-identical | 5,870 / 3,472 | 100,000: 0.19 s → 0.18–0.19 s | 100,000: 0.06–0.08 s both |

Where the executables are byte-identical the differences are the box's noise
(up to 5 %). SrcEval's charged steps (values identical):

| Program, n | Before | After |
| --- | --- | --- |
| `list-qsort` 10 / 100 | 16,601 / 1,092,821 | 16,601 / 1,092,821 |
| `rbmap` 10 / 100 | 5,660 / 122,553 | 5,702 / 121,970 |
| `tokenise` 10 / 100 | 41,697 / 416,367 | 41,827 / 417,667 |
| `const_fold` 5 / 10 | 11,419 / 430,515 | 11,886 / 451,566 (+4.9 %) |

So no compiled program is worse, but SrcEval's count rises where a sparse
casesOn's arguments are already values: `const_fold`'s helpers take λ arms
(each named constructor has fields) and a variable major, and passing them by
name costs one forced slot each in SrcEval; the middle end removes the
difference. Passing value-shaped arguments strictly at these positions (the
value-shaped exemption, in `Lazify` and erasure together) would remove it; it
is not done ([roadmap](../../roadmap.md), "Evaluation order of a match").

## Reproducing

From `IxCC/`, in the development shell, with each build's `ixcc`:
`ixcc compile CLOSURE --equations EQ --root ROOT --rc off|auto --stats --exe OUT
--stack 1073741824 --region 17179869184` (`queue`) or without the layout options
(the outcomes), then `OUT n`; `src-steps fixtures/corpus/phase2-closures/sparse.ixe
--equations fixtures/corpus/phase2-closures/sparse.equations.json --root ROOT b n`
and `src-steps --manifests`; for the registered programs, `ixcc compile` of
every root of every manifest under the three `--rc` modes with `-o` and
`--emit-cert`, comparing the SHA-256 of objects and certificates.
