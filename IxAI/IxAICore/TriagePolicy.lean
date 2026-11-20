import IxAICore.Reinforce
import IxAICore.Triage

/-!
# Triage routing learned by reinforcement

A routing policy for formulas, trained against a specified cost model rather than labels. For
each formula the policy chooses to `attempt` the decision procedure or to `defer` to a slower
process. The reward prices the outcome:

| choice  | formula valid | formula invalid |
|---------|---------------|-----------------|
| attempt | +256 (published) | −192 (procedure run for nothing, confidently wrong) |
| defer   | −64 (missed)     | 0 |

Under this reward the best policy attempts exactly when `P(valid) > 192 / 512 = 3/8`, a
threshold no label states: the policy has to learn the economics, not only the classification.

Safety does not depend on the reward. `outcome_publish_sound` holds for every model, so no reward,
however misspecified or gamed, and no training run can make the system publish a false formula.
The reward decides how much work the policy saves; the types decide what it may do.
-/

namespace IxAICore.Triage

inductive Choice where
  | attempt
  | defer
  deriving DecidableEq, Repr, Inhabited

instance : Finite Choice := ⟨[.attempt, .defer], fun
  | .attempt => 0 | .defer => 1⟩

/-- The routing problem's spec: the triage features, and one answer group, the choice. -/
def policySpec : Spec Formula :=
  { spec with name := "triage-routing", slots := [⟨"choice", 2, fun _ => 0⟩] }

/-- The specified cost model, in units of `1/256`. -/
def reward (f : Formula) : Choice → Int
  | .attempt => if f.valid then 256 else -192
  | .defer => if f.valid then -64 else 0

def bandit : Bandit Formula Choice := ⟨"triage-routing", reward⟩

/-- The deployed policy's choice: its most probable action. -/
def route (m : Model) (f : Formula) : Choice := (m.ask policySpec 0 f).value

/-- What happens to a formula: attempted formulas go through the decision procedure. -/
def outcome (m : Model) (f : Formula) : Action :=
  match route m f with
  | .attempt => if f.valid then .publish else .refuted
  | .defer => .defer

/-- Whatever the weights, and so whatever reward they were trained on, a published formula is
valid. -/
theorem outcome_publish_sound (m : Model) (f : Formula) (h : outcome m f = .publish) :
    f.valid = true := by
  unfold outcome at h
  split at h
  · split at h
    · assumption
    · cases h
  · cases h

/-- A gamed cost model that pays for every attempt, as a careless or adversarial reward author
might write it. A policy trained on it attempts everything; `outcome_publish_sound` still holds
for that policy, and its certificate names this reward's address rather than `bandit`'s. -/
def hackedReward (_ : Formula) : Choice → Int
  | .attempt => 256
  | .defer => 0

def hackedBandit : Bandit Formula Choice := ⟨"triage-routing-hacked", hackedReward⟩

/-- The best achievable reward for a formula. -/
def oracleReward (f : Formula) : Int := max (reward f .attempt) (reward f .defer)

/-- A routing policy's results on held-out formulas. -/
structure PolicyCard where
  total : Nat
  attempts : Nat
  /-- Attempts the procedure refuted. -/
  refuted : Nat
  /-- Valid formulas deferred. -/
  missed : Nat
  rewardRaw : Int
  oracleRaw : Int
  deriving DecidableEq, Repr

def policyCard (m : Model) (fs : List Formula) : PolicyCard :=
  fs.foldl (fun c f =>
    let ch := route m f
    { total := c.total + 1
      attempts := c.attempts + (if ch = .attempt then 1 else 0)
      refuted := c.refuted + (if ch = .attempt ∧ f.valid = false then 1 else 0)
      missed := c.missed + (if ch = .defer ∧ f.valid = true then 1 else 0)
      rewardRaw := c.rewardRaw + reward f ch
      oracleRaw := c.oracleRaw + oracleReward f }) ⟨0, 0, 0, 0, 0, 0⟩

end IxAICore.Triage
