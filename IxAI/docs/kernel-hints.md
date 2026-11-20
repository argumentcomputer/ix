# Learned kernel hints

A decision model that makes IxVM itself cheaper, with soundness independent of the model.

Status: measured on Mathlib (Measurements, below). Reducibility hints move the cost of a check
by about 1%, so the first decision proposed here is not worth a model; grouping claims so that
shared constants load once is worth up to about 20%.

## Why this fits

IxVM's definitional-equality check (`IxVM/IxVM/Source/KernelDefEq.lean` in ix) implements Lean's
lazy delta reduction in the circuit: when two terms do not match it unfolds one side, choosing by
each definition's reducibility hint (`delta_rank`), with a fixed fuel per loop (`lazy_delta_loop`,
16 or 8). Kernel admission already takes "an optional, untrusted reducibility hint per constant"
(`docs/kernel.md` in ix).

- **Every strategy is sound.** Any unfolding order, argument order or caching choice yields a
  correct verdict when the check succeeds; a poor choice only lengthens the trace or exhausts fuel.
- **The model stays outside the trusted base.** Heuristic choices are advice from the untrusted
  prover; the circuit verifies whichever path is taken. Certifying the model matters for
  reproducible proofs, not for soundness.
- **Labels are exact.** Cost is trace rows, which is proving time: run alternatives, measure,
  learn the cheapest.
- **The payoff goes to Ix itself.** Kernel reduction dominates the cost of proving environments
  such as Mathlib; fewer reduction steps mean smaller traces and faster, cheaper proofs for every
  Ix user.

## Decisions, by expected leverage

1. **Reducibility hints per constant**, through the existing untrusted channel. The default comes
   from definitional height; learned hints tuned on real workloads (instance diamonds, heavy
   unfolding) may unfold less. No circuit change.
2. **Lazy delta choices per check**: which side to unfold, or whether to reduce a projection
   first. Needs those choices to become prover advice in the circuit, which changes IxVM's keys.
3. **Argument order** in application congruence: compare the argument most likely to differ first,
   so mismatches fail fast. Same requirement as 2.
4. **Caching**: which reduction and definitional-equality results to keep.
5. **Fuel and partitioning**: per-check fuel; how `ix shard` groups constants so that shared
   reductions fall in one claim; record-size prediction for admission.

## Agent design

- **Input:** typed Ixon only: the constant (or the pair of terms under comparison), its type, its
  definition's shape and its dependency neighbourhood in the store.
- **Answer:** per constant, a reducibility hint from the hint type the kernel accepts; per check
  (later), which side to unfold or which argument to compare first.
- **Labels:** counterfactual measurement. Re-check a workload with an alternative hint and record
  the change in rows; the label is the hint that minimised rows, or the row delta itself for a
  regression head.
- **Training:** the certified, deterministic pipeline used for the other models, so a hint set is
  reproducible from its committed workload and spec.
- **Deployment:** the prover computes hints before a run and supplies them through the hint
  channel; nothing in the verifier changes. A hint set is an artifact with an Ixon address, and a
  proof records which one it used.
- **Safety:** none needed from the model; the kernel's verdict is unchanged by any hint, and a
  hint set that exhausts fuel only fails the run, which the prover retries with default hints.

## Plan

1. **Measure** (non-invasive): instrument a copy of IxVM's execution, not proving, on a Mathlib
   slice. Record every lazy-delta decision with its context and the rows spent in each kernel
   function, and find where definitional-equality cost concentrates.
2. **Headroom**: for the costliest constants, re-run execution with alternative hints and measure
   rows, giving an upper bound on what learned hints could save.
3. **Model**: if the headroom is material, train a hint predictor on features of constants and
   evaluate on held-out modules by proving cost with default against learned hints.
4. **Per-check advice** (2–3 above): only if hints alone leave a large gap, as a proposal to the
   Ix team, since it changes the circuit.

## Measurements (2026-11-19)

**Result: reducibility hints have about 1% of headroom on Mathlib, so decision 1 does not justify
a model.** The cost of an IxVM kernel check is substitution and loading constants, not the choice
of which definition to unfold.

Setup. A tracing build of ix (fork branch `kernel-hints`, `35e69a3ba`; `IX_KERNEL_HINTS_TRACE`)
records, for each executed claim, the rows of every function, every constant-against-constant
lazy-delta step and every hint loaded. A row is one memoized call. The sample is 80 claims of the
compiled Mathlib environment (783,115 constants): the 25 costliest by Lean-side check time and 55
drawn at random. Execution only, with the native IxVM executor. Scripts are in `ix/hints`; the
per-claim numbers are in `.truthmines/kernel-hints`.

Baseline, default hints: 1,086,365,372 rows in 380 s of execution.

| Where the rows go | Share |
|---|---|
| Substitution (`KernelSubst`) | 38.7% |
| Loading constants: deserializing, BLAKE3, conversion, byte handling | 25.6% |
| Lists | 10.0% |
| Weak-head reduction (`KernelWhnf`) | 5.4% |
| `KernelClaim` | 4.5% |
| Type inference (`KernelInfer`) | 3.5% |
| Definitional equality (`KernelDefEq`) | 3.5% |

Of 410,396 constant-against-constant lazy-delta steps, 72.7% have only one side that can unfold,
so the hint is not consulted. The rest split into unfolding the right side (10.9%), both (10.4%)
and the left side (6.0%).

Sensitivity. The same sample under five other hint sets, written into the environment's hint
section (`ixe_hints.py`), which the constants' Merkle root does not cover:

| Hint set | Rows against default | Claims over 1% better | Claims over 1% worse |
|---|---|---|---|
| `flat`: every regular height 0, so equal ranks unfold both sides | +1.00% | 0 | 46 |
| `invert`: unfold the lower definition first | +0.95% | 0 | 46 |
| `abbrev2reg`: abbreviations ranked as ordinary definitions | +0.45% | 0 | 27 |
| `noise`: every height moved by up to 3 | +0.05% | 0 | 0 |
| `swap`: half of the heights inverted | +0.05% | 0 | 0 |

The worst single claim under any set is 5.4% above its default. Taking the best of the six sets
separately for each claim gives 0.01% fewer rows than the default. The spread between the default
and the most adverse set is about 1%, and no set improved any claim by 1%: there is no sign of
headroom to learn.

What this rules out and what it leaves:

- **Decision 1 (hints per constant):** no headroom worth learning.
- **Decisions 2 and 3 (advice per check):** bounded by definitional equality and reduction, 8.9% of
  rows plus the substitution they cause, and the order of unfolding moved that by 1% at most.
- **Decision 5 (partitioning):** the 80 claims load definitions 41,929 times but only 6,283
  distinct ones. Loading each once would remove about 85% of the loading rows, 21.8% of all rows
  on this sample; random claims spend 33.4% of their rows loading. How claims are grouped into one
  execution is therefore worth far more than how they unfold.
- **Substitution** is the largest cost and is a property of the kernel algorithm and of the size
  of the proof term being checked, not of a choice a prover makes during the check.

Limits of the measurement: rows are not weighted by circuit width; the hint sets are global
perturbations, not a search per claim; the sample is 80 claims.
