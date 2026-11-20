import IxAIDecide

/-!
Build-time tests for the decision library: every `#guard` runs when this library builds.
-/

namespace IxAIDecideTest

open IxAICore IxAIDecide IxAIDecide.Invoice

/-- Seed 2026's training and held-out sets, and the deployed seed's held-out and validation sets,
each generated once. -/
private def trainSet := config.data task.spec
private def testSet := config.test task.spec
private def testDeployed := recipe.config.test task.spec
private def valDeployed := validationSetN recipe.config task.spec 4096

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

/-! ### The binomial test -/

-- Upper-tail numerators against exact values computed independently (Python's `math.comb`):
-- `Σ_{k=r}^{n} C(n,k) aᵏ bⁿ⁻ᵏ`.
#guard binomTailNum 20 15 1 1 == 21700
#guard binomTailNum 30 28 4 1 == 41144886195656851456
#guard binomTailNum 50 48 9 1 == 11172875634634714781481799307017666109443219859676
-- The whole tail is `(a + b)ⁿ`; past `n` it is empty; `b = 0` is a certain success.
#guard binomTailNum 5 0 2 3 == 5 ^ 5 && binomTailNum 5 6 1 1 == 0 && binomTailNum 5 3 1 0 == 1
-- A fair coin: 15 heads of 20 has tail 21700/2²⁰ ≈ 0.021 ≤ 0.05, 14 of 20 has ≈ 0.058.
#guard binomTest 20 15 1 1 && !binomTest 20 14 1 1
example : binomTailNum 20 15 1 1 = 21700 := by decide +kernel

/-! ### The generated data -/

-- Same seed, same data: a second generation equals the first.
#guard config.data task.spec == trainSet
#guard trainSet.length == 512 && testSet.length == 1024 && valDeployed.length == 4096
-- Label frequencies in the training set: pay, hold, reject.
#guard
  let d := trainSet
  let n := fun (o : Disposition) => (d.filter (·.label == o)).length
  (n .pay, n .hold, n .reject) == (327, 140, 45)
-- The written policy and the best rule on the visible fields, on the held-out set.
#guard ruleCorrect writtenPolicy testSet == 893
#guard ruleCorrect bayesRule testSet == 918
-- Seed 301, the deployed model's: policy and ceiling on its held-out set.
#guard ruleCorrect writtenPolicy testDeployed == 881
#guard ruleCorrect bayesRule testDeployed == 913
-- The first 1,024 of the 4,096 validation examples are the 1,024-example validation set.
#guard valDeployed.take 1024 == validationSet recipe.config task.spec

/-! ### Training is deterministic and gives the deployed weights -/

def tinyConfig : Config := { config with hidden := 4, trainSize := 32, testSize := 8 }

-- `trainingClaim`, checked by running training in the interpreter.
#guard recipe.train task.spec == deployed
-- A shorter schedule is a prefix of a longer one, so checkpoints are the shorter recipes.
#guard
  let r : Recipe := ⟨{ tinyConfig with epochs := 2 }, 627⟩
  (r.checkpoints task.spec 1).map (·.2) ==
    [Recipe.train ⟨{ tinyConfig with epochs := 1 }, 627⟩ task.spec, r.train task.spec]

-- The gate's thresholds are protocol v3's (`gateCumulative`) on the deployed seed's 4,096
-- validation examples.
#guard
  let g := gateCumulative deployed valDeployed
  [Disposition.pay, .hold, .reject].all fun o => g.need o == gate.need o

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

-- A model that always says `pay` with full confidence, behind a gate that allows `pay` from 128:
-- the gate pays, and `handle` still holds an invoice over its purchase order and rejects an
-- unapproved vendor. Behind the deployed gate it pays nothing.
def alwaysPay : Model :=
  { tinyWeights with
    w2 := [fx [0, 0, 0, 0], fx [0, 0, 0, 0], fx [0, 0, 0, 0]], b2 := fx [256, 0, 0] }

def invoice : Invoice :=
  { vendorApproved := true, tenure := .established, channel := .portal, total := 120000
    poTotal := some 150000, bankChanged := false, disputes := 0 }

def openGate : Gate Disposition := { floor := 128, need := fun _ => 128 }

#guard handle ⟨alwaysPay, openGate⟩ invoice == .paid
#guard handle ⟨alwaysPay, openGate⟩ { invoice with total := 160000 } == .held .overPurchaseOrder
#guard handle ⟨alwaysPay, openGate⟩ { invoice with vendorApproved := false } ==
  .rejected .vendorNotApproved
#guard handle ⟨alwaysPay, gate⟩ invoice == .escalated .pay 256
-- A model with every output zero is uniform at 85/256, below the floor: everything is escalated.
#guard handle ⟨{ alwaysPay with b2 := fx [0, 0, 0] }, gate⟩ invoice == .escalated .pay 85

-- On the held-out set, for the trained, the untrained and the constant model, nothing is returned
-- below 128 and neither `pay` nor `reject` is returned.
#guard [deployed, config.init task.spec, alwaysPay].all fun m =>
  testDeployed.all fun e =>
    let j : Judgment Disposition := judge m e.input
    match gate.apply j with
    | .choose .reject | .choose .pay => false
    | .choose _ => decide (128 ≤ j.confidence)
    | .defer => true

-- A stricter gate turns decisions into deferrals and changes none.
def strict : Gate Disposition := { gate with floor := 200 }
#guard testDeployed.all fun e =>
  let j : Judgment Disposition := judge deployed e.input
  strict.apply j == .defer || strict.apply j == gate.apply j

-- A cascade: the written policy's `hold` answers stand; everything else goes to the model.
def policyHoldsFirst (p : Profile) : Verdict Disposition :=
  if needsHold p then .choose .hold else .defer
#guard cascade policyHoldsFirst decision.run largeWithoutPO == .choose .hold
#guard cascade policyHoldsFirst decision.run routine == .defer

/-! ### The service on concrete invoices -/

#guard service invoice == .escalated .pay 246
#guard service { invoice with tenure := .new, channel := .email, bankChanged := true } ==
  .escalated .pay 216
#guard service { invoice with poTotal := none, total := 6000000 } == .held .model
#guard service { invoice with tenure := .new, bankChanged := true } == .escalated .pay 247
#guard amountBand 120000 == 2 && amountBand 6000000 == 5 && amountBand 0 == 0

end IxAIDecideTest
