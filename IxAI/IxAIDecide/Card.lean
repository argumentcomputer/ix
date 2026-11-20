import IxAIDecide.Decide

/-!
# A decision's evaluation card

`decisionCard` evaluates weights and a gate on held-out labelled examples, beside a baseline
rule written as ordinary code. It is a pure function of its arguments, so like `IxAICore.card` it
can be stated as an `Eval` claim and certified for the deployed weights.

Counts are over the examples' **specified labels**, which may include noise: an accuracy below
100% can be the label noise rather than the model.
-/

namespace IxAIDecide

open IxAICore

/-- Results on held-out examples. Probabilities and the Brier sum are in units of `1/256`. -/
structure DecisionCard where
  total : Nat
  /-- The model's most probable option equals the label. -/
  modelCorrect : Nat
  /-- The baseline rule's option equals the label. -/
  baselineCorrect : Nat
  /-- `Σ` over examples of `Σ_k (p_k − t_k)²`. -/
  brierRaw : Int
  /-- Examples where the gate returned an option. -/
  decided : Nat
  /-- Of those, the option equals the label. -/
  decidedCorrect : Nat
  /-- Examples where the gate returned the guarded option. -/
  guardedChosen : Nat
  /-- Of those, the label is a different option: the costly mistakes. -/
  guardedWrong : Nat
  deriving Repr, DecidableEq

/-- The squared distance of a probability vector from the one-hot target at `tgt`. -/
def brierOf (ps : List Fx) (tgt : Nat) : Int :=
  ((withIndex ps 0).map fun (p, k) =>
    let d := p.raw - (if k == tgt then 256 else 0)
    (d * d) >>> 8).foldl (· + ·) 0

/-- Evaluate weights `m` behind gate `g` and the rule `baseline` on `test`. `guarded` is the
option whose mistakes are costly (the irreversible one). -/
def decisionCard {ι ω : Type} [Encode ι] [Finite ω] [Inhabited ω] [DecidableEq ω]
    (m : Model) (g : Gate ω) (baseline : ι → ω) (guarded : ω) (test : List (Labelled ι ω)) :
    DecisionCard :=
  test.foldl (fun c e =>
    let j : Judgment ω := judge m e.input
    let v := g.apply j
    let b2n := fun (b : Bool) => if b then 1 else 0
    { total := c.total + 1
      modelCorrect := c.modelCorrect + b2n (j.option == e.label)
      baselineCorrect := c.baselineCorrect + b2n (baseline e.input == e.label)
      brierRaw := c.brierRaw + brierOf j.probs (Finite.index e.label)
      decided := c.decided + b2n (v != .defer)
      decidedCorrect := c.decidedCorrect + b2n (v == .choose e.label)
      guardedChosen := c.guardedChosen + b2n (v == .choose guarded)
      guardedWrong := c.guardedWrong + b2n (v == .choose guarded && e.label != guarded) })
    ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- How often a rule agrees with the labels. -/
def ruleCorrect {ι ω : Type} [DecidableEq ω] (rule : ι → ω) (test : List (Labelled ι ω)) : Nat :=
  (test.filter fun e => rule e.input == e.label).length

end IxAIDecide
