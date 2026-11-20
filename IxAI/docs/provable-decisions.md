# Provable decisions over Ix

Strategy for the decision model, and a scoped first demo.

## Thesis

Typed decision models (TypeSafe's Jev, OpenAI's and Google's Decisions APIs) succeed because they
give software cheap, fast, typed answers it can act on directly. They take free text, cannot say
which model decided or how it was trained, and their accuracy is measured against human or LLM
labels.

The decision model here is a **System One for Ix**: the same interface, but its input is only
typed Lean/Ix syntax (Ixon constants, goals, terms, changes, environment slices) and its answer is
a Lean type. A learned model earns its place only where all three hold:

1. **No algorithm decides it.** The question is undecidable or too expensive in general: truth,
   equivalence, termination, which proof will work.
2. **The input is a rich Ixon structure.**
3. **The answer is eventually checkable.** The kernel confirms or refutes it (a proof or a
   counterexample), so labels are exact, accuracy and calibration are certified against the
   kernel, and a gate acts only on confirmed answers.

Where a plain algorithm decides the question, use the algorithm.

## What every answer carries

1. **Which model.** This exact model, by Ixon address, produced this answer on this input (an
   inference proof: milliseconds of proving for a model of this size).
2. **How it was trained.** Exactly `train spec config` on committed data (the certified,
   deterministic training already built here).
3. **What it can do.** A gate theorem for every weight setting: the model routes effort; only the
   kernel's confirmation changes the store, a merge or a published result. A wrong answer costs
   compute, never correctness.
4. **How well it is calibrated.** A certified calibration card on a committed evaluation set,
   against kernel-checked labels.

## Questions worth learning

| Question | Input | Answer type | Use |
|---|---|---|---|
| Are these two definitions equal? | two Ixon constants | `equal \| differ \| unknown` | semantic deduplication in the store; Lane/`ixvc` merges where equivalent definitions do not conflict; safe refactoring |
| Is this statement true? | an Ixon statement | `true \| false \| unknown` with a probability | which Truth Mines conjectures get proof effort; filtering RL samples before expensive checking |
| How should this goal be attacked? | goal and environment | tactic class, premise ranking | proof search; typed generation (`integration.md` §6) |
| Does this change preserve its spec? | an Ixon change and the theorems it touches | `preserved \| breaks \| unknown`, which dependents | reviewing agents' changes; ordering or skipping re-checks |
| Does this terminate within fuel N? | program and inputs | fuel class | scheduling; kernel route vs Aiur offload |

These are the programming and theorem-proving agent's judgments: the model sits inside the loop of
`integration.md`, deciding where effort goes while the kernel decides what is accepted.

## Larger models

- **Committed encoder, certified head.** A larger encoder over Ixon (100M–1B parameters) trained
  deterministically and committed by address; small typed heads on top get certified training,
  gate theorems and inference receipts. Guarantees are exact for the heads and conditional on the
  committed encoder. The same encoder serves every question above and premise selection.
- **Deterministic training at scale.** Integer tensor cores (int8 inputs, int32 accumulation) are
  exact and order-independent, so the fixed-point determinism used here extends to GPU-scale
  training.
- **Sampled certification.** Training commits to every intermediate model (a Merkle root of the
  trajectory); a verifier draws steps by Fiat–Shamir and requires proofs of only those, giving a
  probabilistic certificate of a large run at a tunable cost.
- **Typed generation.** The same model choosing well-typed moves that build programs and proofs,
  with the kernel's verdict as reward.

## First demo: definition equivalence

### Why this question

- Equivalence of definitions is undecidable in general, so learning is needed.
- Labels are checkable both ways: equal by a proof (`rfl`, `decide`, `simp`, `funext` plus
  induction), different by a counterexample found by evaluation.
- It pays off in this stack immediately: Lane already treats equal Ixon addresses as never
  conflicting; this extends it to equal meaning, and the store gains semantic deduplication.

### Data

- **Generated programs** in the typed language of the first synthesis experiment
  (`integration.md` §6: the M2b λ-calculus with `natRec`): pairs produced by semantics-preserving
  rewrites (equal) and by small mutations (usually different), each labelled by the kernel or by
  a counterexample; seeded, with held-out splits by program shape.
- **Mathlib pairs**, later: known-equal variants (definitions related by `rfl`/`simp` lemmas,
  alternative formulations proved equivalent in Mathlib) and near misses, labelled by the same
  checks.
- Committed with length-binding Merkle roots; splits proved disjoint.

### Model and gate

- **Input:** the pair as Ixon (structural features first: shapes, shared subterms, types,
  evaluation on a fixed probe set of inputs; an Ixon encoder later).
- **Answer:** `equal | differ | unknown`, with calibrated probabilities and a defer threshold.
- **Gate theorem:** a merge or deduplication happens only with a kernel-checked equality proof; a
  `differ` is published only with a counterexample. For every weight setting.
- **Routing:** `equal` with high confidence → attempt the cheap proof tactics first; `differ` →
  run the counterexample search first; `unknown` → defer or full search.

### Measured

- Accuracy, calibration and the certified card against kernel labels.
- **The learning milestone the review asked for:** checker-seconds and solved pairs per budget
  with the model routing, against solver-only (try every tactic and counterexample search in a
  fixed order) and heuristic baselines with the same tools.
- Opus 5.5 on the same pairs (typed input rendered as Lean), with the same tools and scored by
  the same checker.

### Phases

1. **Generator and labeller:** rewrites and mutations over the λ-calculus, equality proofs and
   counterexample search, with a theorem that every label is correct (as `XInst.check_sound` does
   for `prop-xhard`).
2. **Model, training, card:** structural features, certified training, calibration and defer.
3. **Routing benchmark:** the throughput comparison above.
4. **Receipts:** an inference circuit for the model's forward pass with its refinement theorem
   (from the existing forward-pass spec), per-answer STARK receipts, batched PLONK.
5. **Integration:** a Lane merge mode that consults the model and merges equivalent declarations
   once the proof is found.

### Risks

- **Too easy or too hard.** Generated pairs may be separable by evaluation on a few inputs; the
  generator must include pairs that agree on small inputs and differ on large ones, and equal
  pairs that need induction.
- **Shape-specific circuits.** The current refinement specs are tied to the model's sizes;
  receipts for a new model need them adapted or made generic.
- **Transfer to Mathlib.** Structural features from a small λ-calculus may not carry over; the
  Ixon encoder is the fix.
