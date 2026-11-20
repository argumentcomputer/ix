# Certified computation offload

A proposal for the Ix team: kernel-level statements, such as `train spec config = W` about
Ixon-addressed Lean constants, proved at the speed of a purpose-built Aiur circuit, with the
bridge between the two being a kernel-checked theorem rather than an assumption.

- Specs and safety theorems live in the kernel.
- Heavy numerics run in purpose-built circuits.
- The bridge between them is itself a checked theorem.

## The gap it closes

This project certifies training two ways (`README.md`, `plan.md`):

| | Kernel route (IxVM) | Aiur route |
|---|---|---|
| Proves | Ix's kernel reduces the Lean constant `IxAICore.train spec config` to `W` | runs of a hand-written Aiur program (`Fixed::step`, chained) map committed weights to weights |
| Statement is about | Ixon constants: the spec itself | a program key and BLAKE3 commitments |
| Meaning from | kernel reduction | Lean refinement theorems (`step_spec` … `train_sound_eq`) plus evaluation-checked parity |
| Cost | ~659 s per 20 SGD steps; the full run projected at ~6 h | ~46 ms per step; the full 600-step run, aggregated and compressed to one 584-byte PLONK certificate, in ~45 min |

The kernel route has the right statement and the wrong cost; the Aiur route the reverse. Today
the two are joined only informally: a CheckEnv certificate over the spec and refinement theorems,
an `aiurExec` certificate over the executions, and a reader who knows that the second instantiates
the first.

## Mechanism

The ingredients exist; what is new is letting Ix use them together.

1. **The program and its semantics as Ix constants.** The Aiur source (`IxAIStep.Fixed.source`),
   its formal semantics (`Aiur.Generic.SourceSemantics.ObsFn`) and the backend soundness theorem
   (`Optimized.Physical.Prepared.depth_grouped_activated_native_heap_sound_goldilocks_observed`)
   are Lean, so they compile to Ixon and can be checked by IxC.
2. **A refinement theorem in the environment.** For a program `P`, entry `e` and Lean function
   `f`, a theorem `R : Accepted P e (enc x) (enc y) → f x = y`, where `Accepted` is the Lean-level
   statement "the memo checker accepts rows of a compilation of `P` with this root claim".
   `train_sound_eq` is this theorem for `Fixed::train` and `IxAICore.train`; `train_of_deployed_steps`
   is its chained form for `Fixed::step`.
3. **A claim kind that discharges `Accepted` with a proof.** Ix accepts the statement `f x = y`
   (as Ixon constants) given:
   - a CheckEnv (or catalog) certificate for an environment containing `R`, `P` and `f`;
   - an Aiur proof (or an `aiurExec` aggregate) under the key that compiles from `P`, whose claim
     encodes `x` and `y`;
   - inside the aggregate circuit: a check that the program key and `R`'s Ixon address are the
     ones named, and that the claim's encoding matches `enc`.

   The output is an Ix claim about `f x = y` on Ixon addresses, as if IxVM had reduced it.
4. **Composition.** In the IxVM aggregate, the Aiur proof is a child (`ChildKind.aiur`, the
   prototype in `~/repos/forks/ix-aiurexec`), and the refinement theorem is an environment
   constant like any other, so one certificate covers spec, safety theorems and training.

## Soundness and trusted base

The one step that is not a Lean proof is the same one Ix already relies on for its own kernel
circuit: an accepting STARK implies its rows satisfy the Lean-modelled checker (Ix's Audit trust
boundary). Everything else is checked:

| Step | Today in this project | With offload |
|---|---|---|
| `f x = y` from accepted rows | `train_sound_eq` (Lean kernel) | the same theorem, IxC-checked in the environment |
| circuits are a compilation of `P` | `#eval` parity check (`IxAIRefine/Check.lean`), `StepOnlyParity` as a hypothesis | the key is compiled from `P` inside Ix, or parity proved |
| aggregation verifies and chains children | `aiurExec` prototype, not proved | aggregator soundness proved, as for Ix's own aggregator |
| claim encodes `x`, `y` | checker code (`aiur_exec_check`) | `enc` as a Lean definition the claim names |
| statement names the spec | separate CheckEnv certificate, joined by the reader | one claim on Ixon addresses |

So the trusted base shrinks to Ix's existing assumptions plus soundness of the aggregation
circuit, which Ix needs for its own aggregator anyway.

In effect this is a sound `native_decide`: fast evaluation justified by a checked theorem, not by
trusting a compiler.

## Why it matters for verifiably safe AI

- **Specs stay readable and general.** A model, loss, reward or safety property is a Lean
  definition; its certificate names that definition's Ixon address.
- **Cost stays practical.** Only the hot numeric loop needs a circuit and a refinement proof;
  everything cheap (eval cards, gate decisions, rewards, labels) uses the kernel route directly.
- **Nothing is taken on trust between them.** A circuit that drifts from its spec breaks the
  refinement theorem, not a reader's assumption.
- **The store stays uniform.** Truth Mines entries remain Ixon constants with claims about them;
  `trainedOutput`'s address, not the BLAKE3 of an ad hoc encoding, is what gets certified.

## What exists

- Refinement theorems for `Fixed::step` and `Fixed::train` (`ix.ixai-aiur/Aiur/IxAIRefine`),
  standard axioms only.
- Kernel-route certificates for the tiny and small models and the deployed model's card,
  decisions and safety theorems.
- The `aiurExec` prototype: 600 step proofs aggregated on the GPU and compressed by the standard
  pipeline to one 584-byte PLONK certificate, checked independently
  (`docs/aiur-composition.md` in the fork).

## The concrete ask: Aiur children in `ix_aggr`

Ix already builds one certificate for an environment by recursion: the `ix_aggr` circuit verifies
the STARK proofs of child claims and joins them. The ask is to let that verifier accept a second
child kind.

- **`ChildKind.aiur`.** A child that is a proof of an Aiur program entry under a key supplied as
  data, bound by BLAKE3 in the claim (as the `aiurExec` prototype's 80-byte identity blob does).
  The child contributes its claim (program key, entry, input and output commitments) to the
  join.
- **Join rule.** An Aiur child is admitted only together with an environment child whose subject
  root contains a binding constant `B` naming the child's program key and a refinement theorem
  `T` about that program (Merkle paths, as for discharged assumptions today). The joined claim
  states: the environment checks, it contains `T` and `B`, and the named program produced these
  committed outputs on these committed inputs.
- **Result.** One native Ix claim and one certificate for "`f x = y`, computed by an Aiur
  program and justified by a checked refinement theorem", for any Aiur program, not only
  training. This replaces both the prototype combine circuit and the claim-level join.
- **Cost.** Changing `ix_aggr` changes every IxVM aggregate key, so existing aggregate
  certificates would need re-proving under the new keys. Typechecking semantics do not change.
- **Prototype, run end to end (2026-11-20).** Implemented in a fork of Ix (branch `cert` of
  `~/repos/forks/ix-cert`: the join shapes, two kernel fixes, and the verifying-key pins of the
  changed circuits). The training run and the environment holding `T` and `B` were proved as
  children of one aggregate and compressed to one 584-byte PLONK certificate; `plan.md` (Done)
  has the identifiers, the timings and what was checked independently.

## What it needs

1. An Ix decision on adding a claim kind (or `ChildKind.aiur`) that binds a refinement theorem's
   Ixon address and a program key. This is a protocol change and needs sign-off.
2. A soundness proof for the aggregation circuit.
3. A Lean definition of the claim encoding `enc`, and a proof that the decoded claim is `enc x`.
4. Either compiling the program key inside Ix or a proof of the parity now checked by `#eval`.

## Open questions

- Should the wrap layout be shared between the IxVM and Aiur paths? Sharing the final stages gives
  one PLONK key; each path can reach a canonical shape through its own normalising stage first, so
  the IxVM keys never change and the Aiur path's admission margin (99% of `G_cold0` for 20-step
  block roots) is fixed in its own stage. With `ChildKind.aiur`, Aiur proofs enter the IxVM
  aggregate as children and only its root is wrapped, so they need to fit the aggregator's child
  verification rather than the wrap.
- One claim kind per (program, refinement) pair, or a generic "evaluate via" claim that looks up
  the refinement theorem by type?
- Should refinement be stated per entry (`step`) with chaining in Lean, or per run (`train`), and
  which composes better with streaming aggregation?
- Can the kernel route and the offload route share cache entries, so a constant reduced once by
  either is not re-proved?
- How far does this extend: tactic outcomes, decision procedures, RL rewards over check records?
