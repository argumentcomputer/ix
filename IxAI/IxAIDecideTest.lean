import IxAIDecide

/-!
Build-time tests for the decision library: every `#guard` runs when this library builds.
-/

namespace IxAIDecideTest

open IxAICore IxAIDecide IxAIDecide.Invoice

/-- Seed 2026's training and held-out sets, and seed 101's held-out and validation sets, each
generated once. -/
private def trainSet := config.data task.spec
private def testSet := config.test task.spec
private def test101 := recipe.config.test task.spec
private def val101 := validationSet recipe.config task.spec

/-! ### Options and encodings -/

#guard Finite.Lawful Disposition && Finite.Lawful Tenure && Finite.Lawful Channel
#guard (Finite.all : List Disposition).map Finite.index == [0, 1, 2]
#guard Encode.width Profile == 18
#guard Encode.encode (true, (3 : Fin 4)) == [1, 1, 1, 1]
#guard Encode.encode ((1 : Fin 4), Channel.email) == [1, 0, 0, 0, 0, 1]
#guard Encode.encode (some false) == [1, 0] && Encode.encode (none : Option Bool) == [0, 0]
#guard Encode.encode routine ==
  [0, 0, 1,  1, 0, 0,  1, 1, 0, 0, 0, 0, 0,  1,  0,  0, 0, 0]
#guard Encode.widthOK (testSet.map (·.input))
#guard task.spec.outputs == 3 && task.spec.numFeatures == 18

/-! ### The generated data -/

-- Same seed, same data: a second generation equals the first.
#guard config.data task.spec == trainSet
#guard trainSet.length == 512 && testSet.length == 1024 && val101.length == 1024
-- Label frequencies in the training set: pay, hold, reject.
#guard
  let d := trainSet
  let n := fun (o : Disposition) => (d.filter (·.label == o)).length
  (n .pay, n .hold, n .reject) == (327, 140, 45)
-- The written policy and the best rule on the visible fields, on the held-out set.
#guard ruleCorrect writtenPolicy testSet == 893
#guard ruleCorrect bayesRule testSet == 918
-- Seed 101, the deployed model's: policy and ceiling on its held-out set.
#guard ruleCorrect writtenPolicy test101 == 888
#guard ruleCorrect bayesRule test101 == 918

/-! ### Training is deterministic and gives the deployed weights -/

def tinyConfig : Config := { config with hidden := 4, trainSize := 32, testSize := 8 }

-- `trainingClaim`, checked by running training in the interpreter.
#guard recipe.train task.spec == deployed
-- A shorter schedule is a prefix of a longer one, so checkpoints are the shorter recipes.
#guard
  let r : Recipe := ⟨{ tinyConfig with epochs := 2 }, 627⟩
  (r.checkpoints task.spec 1).map (·.2) ==
    [Recipe.train ⟨{ tinyConfig with epochs := 1 }, 627⟩ task.spec, r.train task.spec]

-- The gate's thresholds are those `thresholdFor` gives on validation for the stated targets.
#guard
  let js := judgments deployed val101
  ([Disposition.pay, .hold, .reject].map fun o => thresholdFor js o (targetPercent o) 100 20) ==
    [gate.need .pay, gate.need .hold, gate.need .reject]

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
-- The same statement evaluated in the interpreter, which runs `trainArr` through `@[csimp]`.
#guard train task.spec tiny == tinyWeights

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

-- On the held-out set, for the trained, the untrained and the constant model, nothing is returned
-- below 128 and `reject` is never returned.
#guard [deployed, config.init task.spec, alwaysPay].all fun m =>
  test101.all fun e =>
    let j : Judgment Disposition := judge m e.input
    match gate.apply j with
    | .choose .reject => false
    | .choose _ => decide (128 ≤ j.confidence)
    | .defer => true

-- A stricter gate turns decisions into deferrals and changes none.
def strict : Gate Disposition := { gate with floor := 200 }
#guard test101.all fun e =>
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
  .escalated .reject 151
#guard service { invoice with poTotal := none, total := 6000000 } == .held .model
#guard amountBand 120000 == 2 && amountBand 6000000 == 5 && amountBand 0 == 0

end IxAIDecideTest
