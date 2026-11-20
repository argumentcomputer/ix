import IxAICore
import IxAICommon.Hash

/-!
# `ixai rl`: reinforcement runs of the routing policy
-/

namespace IxAICli

open IxAI

/- Closed subterms such as a reference training run would otherwise become module initializers,
run at every start of `ixai` whatever the command. -/
set_option compiler.extract_closed false

/-- Reinforcement runs of the routing policy: a base config for initial weights and held-out
formulas, and the RL schedule. -/
def rlConfigs : List (String × IxAICore.Config × IxAICore.RLConfig) :=
  [("tiny", ({ seed := 42, hidden := 4, lrRaw := 2, epochs := 0, batch := 8, trainSize := 0, testSize := 32 },
             { seed := 7, rounds := 4, batch := 8, alphaRaw := 128, lrRaw := 4, pos := 0 })),
   ("small", ({ seed := 42, hidden := 8, lrRaw := 2, epochs := 0, batch := 20, trainSize := 0, testSize := 200 },
              { seed := 7, rounds := 60, batch := 20, alphaRaw := 128, lrRaw := 4, pos := 0 })),
   ("full", ({ seed := 42, hidden := 16, lrRaw := 2, epochs := 0, batch := 20, trainSize := 0, testSize := 200 },
             { seed := 7, rounds := 600, batch := 20, alphaRaw := 128, lrRaw := 2, pos := 0 }))]

def showPolicyCard (label : String) (pc : IxAICore.Triage.PolicyCard) : IO Unit :=
  IO.println s!"{label}: reward {pc.rewardRaw} of oracle {pc.oracleRaw} over {pc.total}; attempts {pc.attempts}, refuted {pc.refuted}, missed {pc.missed}"

/-- Train the routing policy by reinforcement against the specified cost model and against the
gamed one, and compare both with fixed policies on held-out formulas. -/
def rlRun (size : String) : IO UInt32 := do
  let some (c, rc) := (rlConfigs.find? (·.1 == size)).map (·.2)
    | IO.println s!"unknown size {size}"; return 2
  let s := IxAICore.Triage.policySpec
  let test := c.test s
  let m0 := c.init s
  let card := fun m => IxAICore.Triage.policyCard m test
  let fixed := fun (ch : IxAICore.Triage.Choice) =>
    test.foldl (fun acc f => acc + IxAICore.Triage.reward f ch) (0 : Int)
  IO.println s!"always attempt: reward {fixed .attempt}"
  IO.println s!"always defer: reward {fixed .defer}"
  showPolicyCard "initial" (card m0)
  let honest := IxAICore.rlTrain s IxAICore.Triage.bandit rc m0
  showPolicyCard "rl (specified reward)" (card honest)
  let hacked := IxAICore.rlTrain s IxAICore.Triage.hackedBandit rc m0
  showPolicyCard "rl (gamed reward)" (card hacked)
  let falsePublished := test.filter fun f => IxAICore.Triage.outcome hacked f == .publish && !f.valid
  IO.println s!"gamed policy: false publications {falsePublished.length} (outcome_publish_sound: always 0)"
  IO.println s!"policy weights BLAKE3 {IxAI.digestOf "weights" ((honest.w1.flatten ++ honest.b1 ++ honest.w2.flatten ++ honest.b2).map (·.raw))}"
  return 0

end IxAICli
