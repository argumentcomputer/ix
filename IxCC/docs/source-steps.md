# Source steps: the unit of SrcEval work

Written 2026-11-10. This defines what a *step* of the source evaluator
(SrcEval, `IxCC/Src/Semantics.lean`) is, so that SrcEval's work on a program
can be counted, and another implementation of the same rules (for example a
consumer that runs the source evaluator elsewhere) can be measured in the
same unit. The counter is `IxCCTests/Src/Steps.lean`; the tool that reports it
is `src-steps`; recorded numbers are in
[performance/src-steps-2026-11-10](performance/src-steps-2026-11-10/README.md).

## SrcEval's clock is a depth bound

`Src.run p k root args` takes a clock `k`, but `k` is not a budget of steps.
SrcEval's rules (the E, A and F rules of `Semantics.lean`'s header) are of
two kinds:

- a **charged** rule checks `k`: at `0` the run times out; otherwise it runs
  the rest of its own computation at `k - 1`;
- every other rule runs its sub-computations at the same `k`, one after
  another.

So `k` bounds the *nesting depth* of charged rules along a path of the
evaluation, not their number: in an application both the function and the
argument are evaluated at `k` (`eval`'s `app` case). The **least clock** of a
run is the least `k` at which `Src.run` reaches its outcome; it is the largest
number of charged rules nested along one path. Runs are clock-monotone
(`Src.run_mono`): every clock at or above the least gives the same outcome.

## What a step is

A **step** is one application of a charged rule. The charged rules are
exactly those that consume the clock:

| Rule | Step |
| --- | --- |
| E8 δ | unfolding a constant through an `eqn` entry, a `csimp` entry, a safe definition's body, or an allowlisted opaque's value |
| A1 β | applying a λ closure to an argument |
| F2, F3, F4 ι | firing a recursor (ordinary, subsingleton or empty) |
| F5 `case` | firing a `case` entry (`T.casesOn`) |
| E1 forcing | evaluating a by-name slot when a variable bound to it is used |
| F8 `Quot.lift` | firing `Quot.lift` |

The **step count** of a run is the number of steps it makes. The other rule
applications are counted beside it, not in it:

| Rule | Counted as |
| --- | --- |
| F1 constructors (`Nat.zero`, `Nat.succ` give literals) | `ctor` |
| F6 primitive applications, and F6w fixed-width word operations (contract version 2) | `prim` |
| F7 `Quot.mk` | `quotMk` |
| E6 projections | `proj` |
| A2 an argument accumulated into a partial application | `pap` |
| every call of `eval` | `nodes` |

Conventions that follow from the rules:

- **Irrelevant positions cost nothing.** An argument, `let` or binder that is
  irrelevant at the run's levels is bound to `irr` without evaluation (E5,
  E7); types and sorts evaluate to `irr` (E2) in no step.
- **By-name slots are not memoised.** Passing an argument by name (a `lazy`
  entry's positions, recursor and `case` minors, induction hypotheses) costs
  nothing; each use of the slot costs one step (E1) plus the steps of
  evaluating its term, every time it is used.
- **A match with a catch-all runs only the chosen arm.** Lean elaborates it
  through a sparse casesOn, whose arms are arguments; since 2026-11-12 its
  `lazy` row passes them by name (each is used at most once), so an arm whose
  constructor is not chosen costs nothing, and the chosen one costs its steps
  plus the forced slots. This changed the counts of every program that applies
  one, and its evaluation order: an unchosen arm that would not return, or
  would run out of stack or heap, no longer runs (K2 `queue`, quadratic before,
  is linear; `phase1-boundary`'s `tags16` 139 → 133 on its first case; the
  [2026-11-10 tables](performance/src-steps-2026-11-10/README.md) are from before).
  An argument that is already a value, a λ arm or a variable major, still
  costs one forced slot when its helper has a `lazy` row, which it did not
  cost strictly: K3 `const_fold` (λ arms) counts 11,419 → 11,886 steps at
  `n = 5` and 430,515 → 451,566 (+4.9 %) at `n = 10`, `tokenise` +0.3 %,
  while its compiled code is byte-identical
  ([performance/sparse-cases-2026-11-12](performance/sparse-cases-2026-11-12/README.md)).
- **Primitives are one application each,** whatever the size of their `Nat`
  arguments (SrcEval's `Nat` is exact).
- **Literals peel for free.** A `Nat` literal used as a `Nat` recursor's or
  `case`'s major selects `Nat.zero` or `Nat.succ` within that ι or `case`
  step.
- **A run that times out has no step count.**

## The counter and its relation to `Src.run`

`IxCCTests.Src.Steps.run` is SrcEval transcribed rule for rule into a state
that counts each rule, and records the smallest clock left at any step. From
it, the least clock is `clock - m + 1`, with `m` that smallest value, since a
run at that clock leaves every step at least one unit.

Its agreement with SrcEval is **checked, not proved**: it is written with
`partial` functions, off every checked path. `Steps.measure` runs `Src.run`
at the same clock and requires the same outcome, then requires `Src.run` to
reach it at the counted least clock and to time out one below. A run that
fails either check is an error, never a reported count. `tests-src` pins
the step counts and least clocks of three small bench-k1 rows, so a change
to SrcEval's rules or to the front end that alters this unit fails a
required suite, and of nine rows of the sparse casesOn fixture
(`phase2-closures/sparse`), whose unchosen arm costs the same at `n = 1000`
and `n = 100000`.

## The tool

```text
src-steps CLOSURE.ixe --equations EQ.json --root NAME [--clock K] ARG...
src-steps --manifest CORPUS.json [--clock K]
src-steps --manifests [--clock K]
```

It runs `ixcc`'s front end (ingress with the certified kernel's acceptance,
the unfolding table, the relevance annotation, `Lazify` and admission), then
the root on the arguments, and prints one JSON object (`ixcc/src-steps/1`) per
run: the closure, root, arguments and clock; the outcome, with an `ok` value
read back as `Src.readback` reads it (a constructor by its index in its
inductive); `steps`, with `charged` and its parts and the uncharged counts;
and `leastClock`. A program the front end declines gives an object with the
front end's stage, code and message instead, and exit status 1. The manifest
forms run every case of every root of an `ixcc/corpus/1` manifest, or of every
registered family, that the corpus suite runs at the source level; a case it
skips there (an argument of at least `2⁶³`, no source value in the manifest, or
Lean's interpreter failing on it) gives an object with `skipped` and the
reason. Run it from the package root (`IxCC/`). SrcEval nests a
native frame per recursive call, so the tool re-runs itself once with a 16 GiB
Lean stack, as `tests-corpus` does; its default clock, 2,000,000, bounds the
depth a run may reach, and a deeper run (a boundary case that does not return
in practice) reports a timeout.
