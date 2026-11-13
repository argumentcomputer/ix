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

## Where this branch differs from note 12

The IxVM side's twelfth note (`IXCC-NOTE-12.md`, 2026-11-13, §2) agreed to our rulings and named
some repairs in its own terms. The places where this branch does something else, with the reason:

- **`.clo` is not admitted beside `.pap` in `ClosureAt`** (note 12 §2 item 7, A.8). An input at an
  arrow skeleton is still a partial application of a program constant, whose body the checker has
  analysed (`checkBodies` reads the whole closure since repair M). An input closure (`.clo`)
  carries a body and an environment that no check covers: `ModeSafe` would then quantify over run
  terms the checker never saw, and its conclusion would need a typing and mode invariant for them
  that nothing states. Admitting more inputs is a widening of the statement, for later (with the
  fresh-extern extension in `REPAIRS.md`, "Statement widenings, not built").
- **Wrapper taint is done by repair P, not by their `r7`** (note 12 §2 item 2). P keeps the
  container's regions at every `@shared` field, in a projection (`anProj`) and in a match
  (`caseField`), so nothing is assumed about what a `@shared` field holds, whether the "cell" is a
  real cell or a trivial wrapper that is the field itself. With repair J (an ill-typed field is a
  stuck run) and repair L (the oracle declines at its depth limit instead of answering `val`),
  that covers finding 4 and finding 15 without `r7`'s wrapper condition.
- **A.7(b) is unnecessary because of P** (note 12 §2 item 6: the `@shared` fields of a fresh cell
  an extern returns have empty taint). Since P the checker never takes a `@shared` field to be
  unconfined, and a call's result carries every argument's regions, so `ExternOk` needs no clause
  about `@shared` slots. Finding 5 (the extern `mkS`) has been refused since P.
- **L1, the owner's provisional ruling of 2026-11-13: a number is never confined** (commits W1 to
  W6). It changes `Eval.bindAt`: a borrowed binder no longer adds its region to a number. And it
  brings back, in a stronger form, the no-leaf refinement that note 12 §2 item 1 agreed to drop
  (`leafRegs := regs`): under L1 a call's result of class `leaf` carries no region at all (W3),
  and a class-`leaf` binding carries none (W2). Repair O, repair F and the leaf half of repair U go
  (W4 to W6). `Param.noLeaf` stays, unread. The cost: a borrow annotation on a number is not
  enforced on its own binder. `Statement.lean` does not change, since `ArgOk` and `ExternVal`
  already require a leaf's taint to be empty.
- **V1, the raw recursor check, is made at the recursors run bodies call** (note 12 §2 item 1
  locates it at `stuckAt`, that is, at every recursor of the closure). `readProg` checks each
  recursor a read run body names (at a spine's head or standing alone, an argument too), and,
  transitively, every recursor the rules of a checked recursor call (`Reading.rawRecursors`).
  Their rule's "mentioned nowhere else" refuses a recursor whose induction hypothesis passes an
  erased index; checked closure-wide that would refuse every subject that only matches on such a
  type, since `casesOn` brings the recursor into the closure without firing it raw.
- **`ModeSource.lean`** (in `IxC/Resource/`, which note 12 §1 freezes for this branch whole) was
  touched once, by V2 (note 12 §2 item 2 names it): `leadingBinders`' docstring only. The reading
  no longer uses `leadingBinders` (since V2 `ifaceErased` reads with `readForalls`); their suite's
  `eraseBinder` still does, to find a binder's node in a root block.

## The class oracle on recursive inductives (V7)

**The defect.** The class oracle (`oTypeClass`) classes a value of an inductive type by its
constructors: each field's type is asked whether it is `irr` (`keptFields` → `irrAt`) and, for a
trivial wrapper, the class of its one kept field. A recursive field's type is the type itself, so
on a recursive, mutual or nested inductive the oracle followed the field one level deeper each
time until its depth limit. As landed the depth limit answered `val`, which hid this (and was
unsound for deep type formers, finding 4); repair L made the depth limit a decline, which exposed
it: `check` declined at record level on every subject with a value of such a type (MX-oracle2, on
a real environment: a hand-made `L | nil | cons (h : E) (t : L)`, Lean's `List E`, a mutual
`A`/`B`, a nested `T | leaf | node (cs : List T)`, an indexed `V : Nat → Type`).

**The fix.** `oTypeClass` carries the path of the inductive instances whose constructors it is
analysing, each keyed by its head constant with its levels and its first `nParams` arguments; an
instance met again on its own path answers `val`. Each question of the classifier starts with an
empty path, and the oracle keeps no memo. The path is checked after the instance's own `irr`
tests (a sort, a type former, a proposition), so it skips only the constructor analysis, which
never answers `irr`. The argument is in the commit message; in short: where the oracle answered
before, it answers the same (a re-entered key repeats its analysis, so the oracle declined there),
and where it declined, the answer `val` at a re-entry is consumed as "not `irr`" (true by the
instance's own tests) or as a trivial wrapper's field, where a cycle of trivial wrappers has no
finite `ImmT`/`LeafT` derivation (least fixed points), so `val` is its class.

**The remaining limit.** An instance whose parameters grow without repeating (`N α | mk (x : N
(List α))`) never meets its key again and still declines at the depth limit. A constructor's type
carries the inductive's own level parameters, so the recursive field of a level-polymorphic type
at concrete levels (`List.{0} E`) has a different key (`List.{u} E`) and is caught one level
later.

The driver's cases (Part 3, `v7RecursiveTypes`) are hand-made records over the empty environment:
`L` matched by a case shape (a value), the mutual, nested and indexed types each matched by a raw
call of its recursor (stuck: `runR` is stuck at a recursor), the wrapper cycle in both orders, and
the non-uniform type at the depth limit.

Their suite has the same programs compiled by Lean on a real environment
(`Tests/Ix/ResourceModesRecFixture.lean`, the record cases `recTypeCases`): all five are accepted.

**The run's limit (not the oracle's).** `runR` enters a match only through a case shape, a
definition over a recursor with one motive (`caseShape`: `motives == 1`) whose minor premises
forward their fields. In that fixture Lean's matchers read as bodies, and the run reaches a value
through `L.casesOn` and `List.casesOn`. `A.casesOn` (a mutual block) and `T.casesOn` (a nested
type) are not case shapes, their recursors having a motive per type. `V.casesOn` (an indexed
family) is not read as one either: as compiled, its minor premise forwards `cons h n t` with the
prefix `cons h n` behind a sharing reference, and `caseShape`'s spine (`ixSpine`, also in
`forwarded`) does not read through a sharing reference in function position (job MY-probeV
printed the record). So the runs of the mutual, nested and indexed programs are stuck: no claim is
made of them, and nothing is unsound, but those programs are not run. Widening either is not part
of V7.

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
| + L1, the owner's provisional ruling (W1 to W6, driver 03530c2c8; accepts 212,909) | 0 (and 0 ill-typed-stream hits) | MV-dt-L1 |

At the rebased head (MV-dt-head): accept 188,860, refuse 611,140, decline 0; admitted by K
163,205; stuck at the top fuel 6,859, all at an absurd cast; self-test 0 disagreements; 9.8 min
wall for the eight seeds in parallel, 5.8 s per thousand programs. Each of these totals equals
MU-dt-r6's.

**L1** (the owner's provisional ruling of 2026-11-13: a number is never confined; commits W1 to
W6, each revertible). `runR` puts no region on a number at a borrowed binder (W1). The checker
gives a value of class `leaf` no region at a binding (W2) and as a call's result (W3, which
restores repair A's intent), and drops repair O (W4), repair F (W5) and U's leaf half (W6).
The cost: a borrow annotation on a number is not enforced on its own binder. A2 is moot. At
03530c2c8 (MV-dt-L1): accept 212,909 (+24,049 against MV-dt-head), refuse 587,091, 0
counterexamples, 0 ill-typed-stream hits, self-test 0 disagreements. Case by case against
MV-dt-head, joining the verdict files: 188,860 accepted at both, 24,049 refused before and
accepted now, 587,091 refused at both, none accepted before and refused now.

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
