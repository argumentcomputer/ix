import IxAIDecide.Invoice

/-!
# The deployed invoice decision

`deployed` is `recipe.train task.spec`, the model protocol v2 selected for seed 201
(`docs/decision-library.md`, "Protocol v2"), written out as literals so that every later
statement about it (its card, its decisions) is a small evaluation. That it is the training
function's output is the claim `trainingClaim`. At build time `IxAIDecideTest` checks it by
running training in Lean's interpreter; certifying it is the same job as for the triage model: an
Ix `Eval` claim, or a chain of per-step claims. Proving it with `decide +kernel` here would make
the kernel replay 3,200 SGD steps, which the triage model's 600-step run shows is too slow for a
build (21.7 minutes in `README.md`).

Everything else in this file is proved by kernel evaluation over the literal weights, or holds
for every weight setting.
-/

namespace IxAIDecide.Invoice

open IxAICore

private def fx (xs : List Int) : List Fx := xs.map Fx.mk

/-- The trained weights: 18 inputs, 8 hidden units, 3 outputs, 179 parameters. -/
def deployed : Model :=
  { w1 := [fx [456, 454, 471, 489, 482, 487, -78, 53, -36, -16, -296, 31, 2, 300, -4, -9, 611, 25],
      fx [-158, -67, 16, 83, -150, 47, -102, 55, -166, -9, 20, -10, 19, 28, 80, -56, -76, -67],
      fx [-166, -39, 31, 83, 22, -113, -109, -207, -133, -103, -73, -252, 53, -197, 72, -200, 65, 71],
      fx [96, 74, 81, -149, -117, 42, -172, -154, 97, -108, 76, -21, 7, 8, -131, 0, -80, -83],
      fx [510, 179, 282, 371, 423, 624, -109, -131, 248, 29, -54, -192, 180, 132, 459, -28, -10, 183],
      fx [-7, -56, -138, -51, -41, -170, -40, 4, -5, -130, -165, -76, -122, 43, 62, 10, -17, -82],
      fx [-80, 33, 13, -74, -42, 65, -37, 26, -10, -22, -61, 16, 96, -76, -70, -111, -63, -129],
      fx [516, 575, 540, 602, 554, 581, -88, 11, -128, 141, 554, 5, 40, -628, 7, -33, 310, 19]]
    b1 := fx [-1173, -142, -197, -106, -998, -103, -111, -1016]
    w2 := [fx [-88, 346, 262, 509, -53, 141, 505, -76],
      fx [107, 79, 220, 107, 8, 140, -75, 54],
      fx [-14, 119, 168, 25, 50, 182, 357, 27]]
    b2 := fx [250, -2, 7] }

/-- The weights are the specified training result. Checked at build time by evaluation; the
statement Ix would certify. -/
def trainingClaim : Prop := recipe.train task.spec = deployed

def decision : Decision Profile Disposition := ⟨deployed, gate⟩

/-- The card of `deployed` behind `gate`, against `writtenPolicy`, on seed 201's 1,024 held-out
examples. -/
def deployedCard : DecisionCard :=
  { total := 1024, modelCorrect := 877, baselineCorrect := 857, brierRaw := 68104
    decided := 718, decidedCorrect := 636, guardedChosen := 438, guardedWrong := 34 }

/-- The card is the specified evaluation of the deployed weights. -/
def cardClaim : Prop :=
  decisionCard deployed gate writtenPolicy .pay (recipe.config.test task.spec) = deployedCard

/-- Proved by kernel evaluation, which regenerates the 1,024 held-out examples from the seed and
runs the model, the gate and the baseline on each. -/
theorem card_certified : cardClaim := by unfold cardClaim; decide +kernel

/-! ## Gate properties, for every weight setting -/

/-- Whatever the weights: `pay` only at confidence at least 224/256. -/
theorem pay_needs_confidence (m : Model) (x : Profile)
    (h : (⟨m, gate⟩ : Decision _ _).run x = .choose .pay) :
    224 ≤ (judge m x : Judgment Disposition).confidence :=
  run_choose_need ⟨m, gate⟩ x h

/-- Whatever the weights: the gate never rejects; a likely fraud goes to a person. -/
theorem never_rejects (m : Model) (x : Profile) :
    (⟨m, gate⟩ : Decision _ _).run x ≠ .choose .reject :=
  run_never ⟨m, gate⟩ x .reject (show (256 : Int) < 257 by decide)

/-- Whatever the weights: below 128/256 the case goes to a person. -/
theorem low_confidence_defers (m : Model) (x : Profile)
    (h : (judge m x : Judgment Disposition).confidence < 128) :
    (⟨m, gate⟩ : Decision _ _).run x = .defer :=
  run_defer_of_lt_floor ⟨m, gate⟩ x h

/-! ## Decisions of the deployed model, proved by kernel evaluation -/

/-- An established vendor, invoicing through the portal, a small amount with a purchase order,
no bank change and no disputes. -/
def routine : Profile :=
  { tenure := .established, channel := .portal, amount := 2, hasPO := true, bankChanged := false
    disputes := 0 }

/-- No purchase order and a large amount (level 6). -/
def largeWithoutPO : Profile := { routine with hasPO := false, amount := 6 }

/-- A new vendor, invoicing by email, with changed bank details: the hidden high-risk pattern. -/
def newVendorEmailBankChange : Profile :=
  { routine with tenure := .new, channel := .email, bankChanged := true }

/-- A new vendor with changed bank details, invoicing through the portal. The written policy
rejects it; under the label rule it is fraudulent one time in four. -/
def newVendorPortalBankChange : Profile :=
  { routine with tenure := .new, bankChanged := true }

/-- Paid: `pay` at 229/256, above the 224 that `pay` needs. -/
theorem routine_pays : decision.run routine = .choose .pay := by decide +kernel

/-- The model's answer is `hold`, at 123/256, below the floor: a person decides. -/
theorem largeWithoutPO_escalates :
    (decision.judge largeWithoutPO).option = .hold ∧
      (decision.judge largeWithoutPO).confidence = 123 ∧
      decision.run largeWithoutPO = .defer := by decide +kernel

/-- The riskiest visible profile: the model's answer is `pay` at only 130/256, and the gate sends
it to a person. -/
theorem newVendorEmailBankChange_escalates :
    (decision.judge newVendorEmailBankChange).option = .pay ∧
      (decision.judge newVendorEmailBankChange).confidence = 130 ∧
      decision.run newVendorEmailBankChange = .defer := by decide +kernel

/-- The written policy rejects; the model answers `pay` at 183/256, below the 224 that `pay`
needs, so the gate sends it to a person rather than paying. Under the generator this profile is
fraudulent one time in four. -/
theorem newVendorPortalBankChange_escalates :
    writtenPolicy newVendorPortalBankChange = .reject ∧
      (decision.judge newVendorPortalBankChange).option = .pay ∧
      (decision.judge newVendorPortalBankChange).confidence = 183 ∧
      decision.run newVendorPortalBankChange = .defer := by decide +kernel

end IxAIDecide.Invoice
