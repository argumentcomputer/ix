# Mode-lane tests (kernel package only)

Tests of the resource-mode lane (`IxC/Resource/`): the checker `checkBodies`/`check` against the
reference run `runR`, on branch `jcb/ixcc-mode-repair`. Everything here needs only the kernel
package `IxC` (`lake -d IxC build IxC.Resource IxC.Kernel.Ixon.Prelude`), not the root package.
Their suite `Tests/Ix/ResourceModes.lean` holds the same finding cases in its own form, but it
needs the root package and its native libraries.

| File | What it is | How to run (from the repository root) |
|---|---|---|
| `Main.lean` | The driver (engineer MR): the suite's 41 fixture-free cases, the finding cases as added to the suite (Part 1b, a verbatim copy), and every finding and repair case with its control, each asserting the checker's verdict, `runR`'s outcome at every fuel tried, `InputsOk` (decided), fuel monotonicity, and "accepted with admissible inputs ⇒ no violating run". Exit 1 on any failure. | `lake -d IxC env lean --run ModeRepairTests/Main.lean` |
| `Findings.lean` | Engineer MT's encodings of the nineteen findings (MU added 19 and the `b4` group). It prints verdicts and outcomes, and asserts nothing. | `lake -d ModeRepairTests env lean --run ModeRepairTests/Findings.lean [all\|b4]` |
| `DiffTest/` | The differential tester (MT; recognisers, compare and the statement version by MU): a typed generator of run programs and inputs (`Gen.lean`), decision procedures for `InputsOk` and `ExternOk` (`Hyp.lean`), and the driver, with self-test, runs, tallies, shrinking and recognisers (`Main.lean`). `DESIGN.md` is MT's design note. | `lake -d ModeRepairTests build difftest`, then `ModeRepairTests/dt-seeds.sh OUT --n 100000 --shrink 300 --classify --stuck 4` |
| `lakefile.lean`, `lean-toolchain` | The package of the tester, requiring `../IxC`. | |

The tester works on `IxC.Resource.Syntax` programs (`Prog`), so its programs do not depend on the
record layout. Only its self-test reads Ixon records: it compares the generator's interfaces with
the reader's on a definition record per generated definition, and those records carry their
binder-data sections (Ixon v5). On the findings branch the statement version (`stmtV2`, repairs
I and K) was a per-tree shim written by `dt.sh sync`. Here it is fixed to this tree's statement
(`Hyp.lean`).

On the box (`~/runs/ixcc`), jobs go through `run.sh NAME on.sh fix-n . …`, under the shared
`heavy.lock`, capped at 8 GB per process.

## Results of record

All runs use seeds 1 to 8 × 100,000 programs (800,000). Case `i` of seed `s` is drawn from
`mix(s, i)` alone, so every tree sees the same programs and `--compare` joins two runs case by case.

**Counterexamples** (typed programs the checker accepts, with an input meeting `InputsOk` and a
fuel at which `runR` violates), per tree. Trees are named by the repairs they add; the commits are
the ones before the rebase onto f2b985847.

| Tree | Counterexamples | Job |
|---|---|---|
| landed, 6db9089a7 (accepts 197,817) | 4,464 | MT-dt-first2, MU-dt-L3 |
| + A B C (1b0704ea6) | 4,273 | MU-dt-R1c |
| + D N E (7e9d1c656) | 3,696 | MU-dt-R2c |
| + F (739ad6478) | 3,446 | MU-dt-F |
| + G Q R S T (3b4c5034e) | 3,439 | MU-dt-R3c |
| + O (f48376098) | 3,413 | MU-dt-O |
| + P U (6a5880069) | 3,388 (all F14) | MU-dt-r4 |
| + I J K L M M2 (800f47e4b; a61f89834 identical; accepts 188,860) | 0 (and 0 ill-typed-stream hits) | MU-dt-r6, MU-dt-r5 |
| the same, rebased onto f2b985847 (Ixon v5; tester at 52da1811d, kernel tree of 1804e2662) | 0 (and 0 ill-typed-stream hits) | MV-dt-head |

At the rebased head (MV-dt-head): accept 188,860, refuse 611,140, decline 0; admitted by K
163,205; stuck at the top fuel 6,859, all at an absurd cast; self-test 0 disagreements; 9.8 min
wall for the eight seeds in parallel, 5.8 s per thousand programs. Each of these totals equals
MU-dt-r6's.

From I on, the tester's statement has I and K, so F14's stale-capability extern is outside
`ExternOk`. No tree accepts a program its predecessor refused (`MU-dt-cmp2-*`, `MU-dt-cmp-O-R4`,
`MU-dt-cmp-R4-R6`).

**Completeness cost by repair**: programs the tree before accepts with no violating run at any fuel
tried, and the tree after refuses. Of the landed tree's 193,353 clean acceptances, about 7,900
(4.1 %) are refused at 800f47e4b. The counts are exact where a tree isolates the repair, and
assigned by witness otherwise.

| Repair | Refused clean programs |
|---|---|
| A (no-leaf refinement dropped) | 2,437 (exact; 1.26 % of the landed clean acceptances) |
| B | 0 |
| C | 9 |
| D | 4,095 |
| E | 120 |
| N | none expected |
| F | 700 (exact) |
| G + Q + R + S + T | 164 (once witnesses 150, G 14; Q has no reach in this grammar) |
| O | 88 (exact) |
| P | 266 |
| U | 3 |
| I, J, K, L, M, M2 | 0 (verdicts identical case by case, `MU-dt-cmp-R4-R6`) |

Stuck runs at the top fuel are 0.14 % (6,859 at 800f47e4b), every one at an absurd cast; no run
is claimed there. Not reachable by this grammar: findings 4 (two programs), 6 (records), and a
constructor with a function field (repair Q's route).
