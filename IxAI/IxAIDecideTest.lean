import IxAIDecide

/-!
Build-time tests for the decision library: every `#guard` runs when this library builds.
-/

namespace IxAIDecideTest

open IxAICore IxAIDecide IxAIDecide.Invoice

/-! ### Options and encodings -/

#guard Finite.Lawful Disposition && Finite.Lawful Tenure && Finite.Lawful Channel
#guard (Finite.all : List Disposition).map Finite.index == [0, 1, 2]
#guard Encode.width Profile == 18
#guard Encode.encode (true, (3 : Fin 4)) == [1, 1, 1, 1]
#guard Encode.encode ((1 : Fin 4), Channel.email) == [1, 0, 0, 0, 0, 1]
#guard Encode.encode (some false) == [1, 0] && Encode.encode (none : Option Bool) == [0, 0]
#guard Encode.encode routine ==
  [0, 0, 1,  1, 0, 0,  1, 1, 0, 0, 0, 0, 0,  1,  0,  0, 0, 0]
#guard Encode.widthOK ((config.test task.spec).map (·.input))
#guard task.spec.outputs == 3 && task.spec.numFeatures == 18

/-! ### The generated data -/

-- Same seed, same data.
#guard config.data task.spec == config.data task.spec
#guard (config.data task.spec).length == 512 && (config.test task.spec).length == 1024
-- Label frequencies in the training set: pay, hold, reject.
#guard
  let d := config.data task.spec
  let n := fun (o : Disposition) => (d.filter (·.label == o)).length
  (n .pay, n .hold, n .reject) == (327, 140, 45)
-- The written policy and the best rule on the visible fields, on the held-out set.
#guard ruleCorrect writtenPolicy (config.test task.spec) == 893
#guard ruleCorrect bayesRule (config.test task.spec) == 918
-- Where the two rules disagree (new vendor, changed bank details, not by email, or the reverse),
-- the written policy is right 13 times in 52 and the model's answer 38 times; the gate defers 28
-- of the 52.
#guard
  let g := (config.test task.spec).filter fun e => writtenPolicy e.input != bayesRule e.input
  (g.length, (g.filter fun e => writtenPolicy e.input == e.label).length,
    (g.filter fun e => (decision.judge e.input).option == e.label).length,
    (g.filter fun e => decision.run e.input == .defer).length) == (52, 13, 38, 28)

/-! ### Training is deterministic and gives the deployed weights -/

-- `trainingClaim`, checked by running training in the interpreter.
#guard train task.spec config == deployed
-- The untrained weights decide nothing on the held-out set; the trained ones decide most.
#guard
  let c := decisionCard (config.init task.spec) gate writtenPolicy .pay (config.test task.spec)
  c.decided == 0
#guard deployedCard.decided == 737

-- A two-step run, small enough for the kernel to replay: the same statement as
-- `trainingClaim`, proved by kernel evaluation.
def tiny : Config := { config with hidden := 4, epochs := 1, trainSize := 32, testSize := 8 }

private def fx (xs : List Int) : List Fx := xs.map Fx.mk

def tinyWeights : Model :=
  { w1 := [fx [4, 7, 6, 8, -4, 13, 4, 0, 0, -12, -4, -14, 10, 5, -13, -4, 14, -10],
      fx [8, -11, 4, 10, 16, -9, 11, -8, 0, -14, 8, -3, 13, 17, -13, 4, -6, 17],
      fx [14, 3, 16, -11, -8, -1, -3, -5, 15, 3, 12, 3, 14, 15, -9, -1, -13, -8],
      fx [-2, -1, -14, -14, -8, -4, 0, 6, 5, 5, 8, 9, 7, -4, 10, 6, 15, -13]]
    b1 := fx [1, 16, -8, 1]
    w2 := [fx [17, 9, 8, -1], fx [5, 16, -7, -2], fx [-9, -8, -11, 8]]
    b2 := fx [111, 69, 12] }

theorem tiny_trained : train task.spec tiny = tinyWeights := by decide +kernel

/-! ### The gate holds for weights nobody trained -/

-- A model that always says `pay` with full confidence: the gate pays, and `handle` still holds an
-- invoice over its purchase order and rejects an unapproved vendor.
def alwaysPay : Model :=
  { tinyWeights with
    w2 := [fx [0, 0, 0, 0], fx [0, 0, 0, 0], fx [0, 0, 0, 0]], b2 := fx [256, 0, 0] }

def invoice : Invoice :=
  { vendorApproved := true, tenure := .established, channel := .portal, total := 120000
    poTotal := some 150000, bankChanged := false, disputes := 0 }

#guard handle ⟨alwaysPay, gate⟩ invoice == .paid
#guard handle ⟨alwaysPay, gate⟩ { invoice with total := 160000 } == .held .overPurchaseOrder
#guard handle ⟨alwaysPay, gate⟩ { invoice with vendorApproved := false } ==
  .rejected .vendorNotApproved
-- A model with every output zero is uniform at 85/256, below the floor: everything is escalated.
#guard handle ⟨{ alwaysPay with b2 := fx [0, 0, 0] }, gate⟩ invoice == .escalated .pay 85

-- On the held-out set, for the trained, the untrained and the constant model, `pay` is only ever
-- returned at confidence 230 or more, and nothing is returned below 128.
#guard [deployed, config.init task.spec, alwaysPay].all fun m =>
  (config.test task.spec).all fun e =>
    let j : Judgment Disposition := judge m e.input
    match gate.apply j with
    | .choose .pay => decide (230 ≤ j.confidence)
    | .choose _ => decide (128 ≤ j.confidence)
    | .defer => true

-- A stricter gate turns decisions into deferrals and changes none.
def strict : Gate Disposition := { gate with floor := 200 }
#guard (config.test task.spec).all fun e =>
  let j : Judgment Disposition := judge deployed e.input
  strict.apply j == .defer || strict.apply j == gate.apply j

-- A cascade: the written policy's `hold` answers stand; everything else goes to the model.
def policyHoldsFirst (p : Profile) : Verdict Disposition :=
  if needsHold p then .choose .hold else .defer
#guard cascade policyHoldsFirst decision.run largeWithoutPO == .choose .hold
#guard cascade policyHoldsFirst decision.run routine == .choose .pay

/-! ### The service on concrete invoices -/

#guard service invoice == .paid
#guard service { invoice with tenure := .new, channel := .email, bankChanged := true } ==
  .escalated .reject 158
#guard service { invoice with poTotal := none, total := 6000000 } == .held .model
#guard amountBand 120000 == 2 && amountBand 6000000 == 5 && amountBand 0 == 0

end IxAIDecideTest
