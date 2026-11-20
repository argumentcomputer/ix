# Verifiable reinforcement learning

`IxAICore/Reinforce.lean` (generic) and `IxAICore/TriagePolicy.lean` (the triage routing policy).

## What current practice gets wrong, and what Ix changes

| Problem in RL with verifiable rewards (RLVR) today | Here |
|---|---|
| The reward is a programmatic verifier, but policies exploit what it fails to check ("LLMs gaming verifiers", arXiv 2604.15149). | The reward is a Lean function in the spec, with a content address. Safety is not delegated to the reward: `outcome_publish_sound` holds for every model, so a gap in the reward can cost efficiency but never safety. |
| A certificate or report of "trained with reward R" is trust-me. | `rlTrain spec bandit config m0 = W` is an Ix claim. A different reward (`hackedBandit`) gives a different claim, so a verifier sees exactly which reward produced which policy. |
| Bitwise reproducibility needs batch-invariant kernels, fixed seeds and deterministic training modes, and still excludes multi-turn rollouts and reward-model serving (verl, vime, TBIK). | Fixed-point arithmetic with exact sums: the run is a pure function, identical on any machine and in IxVM. |
| Group-relative baselines (GRPO) and importance weights trade bias for variance; group-relative REINFORCE is effectively off-policy (arXiv 2509.24203). | The reward is cheap over a finite typed action set, so the update uses the *exact* expected advantage over all actions: no sampling variance, no importance weights, no clipping. |

## The algorithm

Contextual bandit. Each round draws contexts from the environment's specified RNG (independent of
the policy, so the whole schedule is fixed by the config). For each context:

1. the policy `π` is read from the model's policy answer group (clamp-and-normalize, as for every
   decision question);
2. the improved policy is `t_a = clamp01(π_a + α (r_a − Σ_b π_b r_b))`;
3. the model is regressed onto `t` by one `Model.step`, with every other output's target equal to
   its current value.

Step 3 is advantage-weighted regression in shape. It reuses the supervised step unchanged, so the
regression is certified by the same Aiur circuit and refinement proof as a training step, and a
run by the same chain lemma (`rlTrain_eq_of_chain`). Steps 1–2 (forward pass, probabilities,
`improve`) produce the step's targets and need a small circuit of their own, with its own
refinement proof; the forward pass is already part of the step circuit's `delta`.

## Triage routing

The policy chooses `attempt` (run the decision procedure) or `defer`. Rewards (units of 1/256):
attempt +256 if valid, −192 if not; defer −64 if valid, 0 if not. The optimum attempts when
`P(valid) > 3/8`, a threshold that comes from the economics, not from any label.

`hackedReward` pays +256 for every attempt. The policy it produces attempts everything, wastes the
procedure on invalid formulas, and still publishes no false formula (`outcome_publish_sound`); its
certificate names the gamed reward.

## Status

Elaborated and run: `IxAICore/Reinforce.lean` and `TriagePolicy.lean` build, and the results of
`ixai rl` on the small and full configurations are in `plan.md` (Results, Policy / RL). To rebuild
and rerun, gated:

```
ix/heavy.sh timeout 1800 env PATH=$PWD/.toolchain/bin:$PATH lake build IxAICore.TriagePolicy ixai
.lake/build/bin/ixai rl tiny
.lake/build/bin/ixai rl small
```

Next: a Python mirror for cross-implementation bit-identity (as `shell/triage.py` does for
training), RL claims and chunked certificates (the supervised generators apply with `rlStep` in
place of `stepFn`), and a sampled-action variant for action spaces too large to enumerate.

## Related work

- Zhang, *Towards Formalizing Reinforcement Learning Theory* (arXiv 2511.03618): Lean 4 and
  Mathlib proofs of almost-sure convergence of Q-learning and linear TD on finite MDPs
  (github.com/ShangtongZhang/rl-theory-in-lean). Convergence theory for the algorithms, not
  certification of a particular run; the two are complementary.
- MDPLib (reservoir.lean-lang.org/@formalproofs/mdplib): Lean algorithms and proofs for tabular,
  robust and risk-averse MDPs.
- Gupta et al., *Optimal Baseline Corrections for Off-Policy Contextual Bandits* (arXiv 2405.05736).
- verl determinism docs and Thinking Machines' batch-invariant kernels: the state of bitwise
  reproducibility in GPU RL.
