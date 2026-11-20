import IxAICore.Decision
import IxAICore.Chain

/-!
# Reinforcement learning against a specified reward

A `Bandit` is a one-step decision problem: a context `st : σ` drawn by the spec, a typed action
`a : α` chosen from a finite set, and a reward `reward st a`. The reward is an ordinary Lean
function. It is part of the spec, so it has a content address, and a certificate for a policy
names the exact reward it was trained against. There is no learned reward model to exploit.

## The update

Each round draws a batch of contexts with the specified RNG. For every context the current policy
`π = probabilities (policy outputs)` is improved toward

  `t_a = clamp01 (π_a + α · (r_a − Σ_b π_b r_b))`,

the policy moved along the *exact* expected advantage. The reward is a cheap function over a
finite action set, so it is evaluated for every action rather than estimated from sampled
rollouts: the update has no sampling variance, and no importance weights. The group-relative
baseline of GRPO becomes the exact policy-weighted mean.

The policy is then regressed onto `t` by one ordinary supervised step (`Model.step`) whose
targets for every other output are the model's current outputs, so only the policy head gets a
gradient. This is the advantage-weighted-regression shape of policy improvement. It reuses the
training step unchanged, and with it the step's Aiur circuit and refinement proof: an RL run is
certified exactly like a supervised one.

## Determinism and certification

Contexts are drawn from the environment's RNG and do not depend on the policy, so the whole
context schedule is fixed by the config (`RLConfig.contexts`). `rlTrain` is a fold of `rlStep`
over that schedule, and `rlTrain_eq_of_chain` lets a run be certified as a chain of per-round
links, as `train_eq_of_chain` does for supervised training.
-/

namespace IxAICore

/-- A one-step decision problem: contexts of type `σ`, actions of type `α`, and the reward of
each action in each context, in units of `1/256`. -/
structure Bandit (σ α : Type) [Finite α] where
  name : String
  reward : σ → α → Int

/-- The reward of every action in a context, in `Finite.all` order. -/
def Bandit.rewards {σ α : Type} [Finite α] (b : Bandit σ α) (st : σ) : List Int :=
  (Finite.all : List α).map (b.reward st)

/-- The position of answer group `n` in the flat output vector. -/
def slotOffset {σ : Type} : List (Slot σ) → Nat → Nat
  | [], _ => 0
  | _, 0 => 0
  | q :: qs, n + 1 => q.arity + slotOffset qs n

/-- The policy's action probabilities in context `st`, read from answer group `pos`. -/
def Model.policy {σ : Type} (m : Model) (s : Spec σ) (pos : Nat) (st : σ) : List Fx :=
  probabilities (getD (splitByArity s.slots (m.outputs (s.inputs st))) pos [])

/-- `Σ π_a r_a`, in units of `1/256²`. -/
def expectedRaw : List Fx → List Int → Int
  | p :: ps, r :: rs => p.raw * r + expectedRaw ps rs
  | _, _ => 0

/-- The improved policy: each probability moved by `α` times its exact advantage, clamped to
`[0, 1]`. `alphaRaw` is in units of `1/256`. -/
def improve (alphaRaw : Int) (probs : List Fx) (rewards : List Int) : List Fx :=
  let base := expectedRaw probs rewards >>> (8 : Nat)
  List.zipWith (fun p r => Fx.clamp01 ⟨p.raw + (alphaRaw * (r - base)) >>> (8 : Nat)⟩) probs rewards

/-- `xs` with the entries from `off` on replaced by `seg`. -/
def replaceSegment (xs : List Fx) (off : Nat) (seg : List Fx) : List Fx :=
  xs.take off ++ seg ++ xs.drop (off + seg.length)

/-- The regression target for one context: the current outputs, with the policy group replaced by
the improved policy. Every other output's error is zero, so the step changes only what the
policy needs. -/
def Model.rlTarget {σ α : Type} [Finite α] (m : Model) (s : Spec σ) (b : Bandit σ α) (pos : Nat)
    (alphaRaw : Int) (st : σ) : List Fx :=
  let os := m.outputs (s.inputs st)
  let probs := probabilities (getD (splitByArity s.slots os) pos [])
  replaceSegment os (slotOffset s.slots pos) (improve alphaRaw probs (b.rewards st))

structure RLConfig where
  seed : Nat
  rounds : Nat
  /-- Contexts per round. -/
  batch : Nat
  /-- Policy-improvement step size, in units of `1/256`. -/
  alphaRaw : Int
  /-- Regression learning rate, in units of `1/256`. -/
  lrRaw : Int
  /-- The answer group holding the policy. -/
  pos : Nat
  deriving Repr

def RLConfig.contextsFrom {σ : Type} (s : Spec σ) (batch : Nat) : Nat → Rng → List (List σ)
  | 0, _ => []
  | n + 1, r =>
    let (xs, r) := s.sampleN batch r
    xs :: RLConfig.contextsFrom s batch n r

/-- Every round's contexts, fixed by the config: the environment does not depend on the policy. -/
def RLConfig.contexts {σ : Type} (rc : RLConfig) (s : Spec σ) : List (List σ) :=
  RLConfig.contextsFrom s rc.batch rc.rounds (Rng.seeded (rc.seed + 11))

/-- One round: regress the policy onto its improvement on this round's contexts. -/
def rlStep {σ α : Type} [Finite α] (s : Spec σ) (b : Bandit σ α) (rc : RLConfig) (m : Model)
    (ctx : List σ) : Model :=
  m.step ⟨rc.lrRaw⟩ (ctx.map fun st => (s.inputs st, m.rlTarget s b rc.pos rc.alphaRaw st))

/-- The specified result of reinforcement learning from `m0`: a pure function of the spec, the
reward and the config. -/
def rlTrain {σ α : Type} [Finite α] (s : Spec σ) (b : Bandit σ α) (rc : RLConfig) (m0 : Model) :
    Model :=
  (rc.contexts s).foldl (rlStep s b rc) m0

/-- A chain of per-round links over the specified contexts ends at `rlTrain`'s result. -/
theorem rlTrain_eq_of_chain {σ α : Type} [Finite α] (s : Spec σ) (b : Bandit σ α) (rc : RLConfig)
    (m0 : Model) (ls : List (Link Model (List σ))) (h : ChainOK (rlStep s b rc) m0 ls)
    (hin : ls.map (·.input) = rc.contexts s) :
    chainEnd m0 ls = rlTrain s b rc m0 := by
  rw [chain_eq_fold (rlStep s b rc) m0 ls h, hin]
  rfl

theorem Fx.clamp01_raw (a : Fx) : 0 ≤ (Fx.clamp01 a).raw ∧ (Fx.clamp01 a).raw ≤ 256 := by
  unfold Fx.clamp01
  split
  · exact ⟨by decide, by decide⟩
  · split
    · exact ⟨by decide, by decide⟩
    · exact ⟨by omega, by omega⟩

theorem mem_zipWith_of_all {α β γ : Type} (f : α → β → γ) (P : γ → Prop) (hf : ∀ a b, P (f a b)) :
    ∀ (l1 : List α) (l2 : List β), ∀ t ∈ List.zipWith f l1 l2, P t
  | [], _, t, ht => by simp at ht
  | _ :: _, [], t, ht => by simp at ht
  | a :: l1, b :: l2, t, ht => by
    rw [List.zipWith_cons_cons, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact hf a b
    · exact mem_zipWith_of_all f P hf l1 l2 t ht

/-- The improvement target is a vector of probabilities in `[0, 1]`, whatever the rewards. -/
theorem improve_bounds (alphaRaw : Int) (ps : List Fx) (rs : List Int) :
    ∀ t ∈ improve alphaRaw ps rs, 0 ≤ t.raw ∧ t.raw ≤ 256 := by
  intro t ht
  unfold improve at ht
  exact mem_zipWith_of_all _ (fun t : Fx => 0 ≤ t.raw ∧ t.raw ≤ 256)
    (fun _ _ => Fx.clamp01_raw _) ps rs t ht

end IxAICore
