import IxAIDecide.Invoice

/-!
# The deployed invoice decision

`deployed` is `recipe.train task.spec`, the model the training protocol selected for seed 101
(`docs/decision-library.md`, "Training protocol"), written out as literals so that every later
statement about it (its card, its decisions) is a small evaluation. That it is the training
function's output is the claim `trainingClaim`. At build time `IxAIDecideTest` checks it by
running training in Lean's interpreter; certifying it is the same job as for the triage model: an
Ix `Eval` claim, or a chain of per-step claims. Proving it with `decide +kernel` here would make
the kernel replay 1,920 SGD steps, which the triage model's 600-step run shows is too slow for a
build (21.7 minutes in `README.md`).

Everything else in this file is proved by kernel evaluation over the literal weights, or holds
for every weight setting.
-/

namespace IxAIDecide.Invoice

open IxAICore

private def fx (xs : List Int) : List Fx := xs.map Fx.mk

/-- The trained weights: 18 inputs, 16 hidden units, 3 outputs, 355 parameters. -/
def deployed : Model :=
  { w1 := [fx [313, 372, 488, 301, 435, 402, -399, -117, -123, 159, 37, 186, 154, -152, 272, -65, 128, 325],
      fx [-153, -221, 4, -3, -28, -68, -140, -234, -173, -185, -83, -213, 87, -66, 5, -85, -53, -70],
      fx [514, 427, 452, 324, 258, 319, -263, -231, 20, 36, 29, 167, 352, -214, 239, 3, 248, 113],
      fx [329, 337, 205, 268, 279, 307, -192, -207, -38, 125, -3, 266, 88, -131, 152, 48, 87, 243],
      fx [-120, 67, -41, 35, -105, 4, -106, -99, -100, -40, 27, 14, -56, 30, -51, -78, 0, 17],
      fx [290, 368, 333, 267, 293, 240, -95, 70, -23, -34, 184, -30, 69, -138, 8, 4, 367, 35],
      fx [-98, -5, -111, -106, -90, -1, -148, -116, -92, -94, 5, 32, -156, -106, 35, -53, -7, -113],
      fx [334, -9, 163, 103, 84, 374, -12, -132, -87, 49, 48, 80, 43, 12, 528, 23, 141, 60],
      fx [-74, -54, -36, -7, 49, -27, -123, 79, -75, -2, 53, 16, 91, -40, -11, 69, 23, -7],
      fx [277, 205, 290, 218, 229, 282, -138, -152, 102, 96, 368, 54, 4, -421, 116, 7, -285, -64],
      fx [327, 295, 282, 250, 220, 269, -128, -15, 35, 0, -231, -27, 100, 153, 81, -10, 531, 113],
      fx [-147, -71, -95, -60, 39, -23, -113, -62, -152, 32, 2, 62, -14, -51, 21, -94, 114, 72],
      fx [-95, 17, -115, -120, -34, 47, -33, -127, -62, 55, -94, -51, 46, -100, 26, -46, -44, -74],
      fx [-124, -94, -17, -134, -43, -142, -119, -119, 11, -22, 84, -98, -1, 18, -33, -1, 27, -99],
      fx [-139, -137, -138, -111, -37, -10, 27, -54, -92, 47, -8, 149, -75, -71, 9, -109, 48, -14],
      fx [341, 417, 325, 293, 390, 156, -146, -72, -57, 109, 345, -4, 225, -355, -33, -56, 447, 51]]
    b1 := fx [-543, -251, -594, -385, -71, -535, -228, -718, -76, -399, -594, -69, -54, 0, 0, -520]
    w2 := [fx [41, -95, 40, 5, 163, -40, -54, -69, 225, -100, -85, -182, 100, 82, -61, -64],
      fx [-27, -102, -14, -28, 257, 64, 113, -31, 133, 102, 81, 30, 100, 35, 76, 59],
      fx [-10, -566, -22, 19, 186, 5, -55, 110, 225, 7, -2, 33, 125, 79, -83, -4]]
    b2 := fx [249, 6, 0] }

/-- The weights are the specified training result. Checked at build time by evaluation; the
statement Ix would certify. -/
def trainingClaim : Prop := recipe.train task.spec = deployed

def decision : Decision Profile Disposition := ⟨deployed, gate⟩

/-- The card of `deployed` behind `gate`, against `writtenPolicy`, on seed 101's 1,024 held-out
examples. -/
def deployedCard : DecisionCard :=
  { total := 1024, modelCorrect := 914, baselineCorrect := 888, brierRaw := 51012
    decided := 991, decidedCorrect := 894, guardedChosen := 653, guardedWrong := 60 }

/-- The card is the specified evaluation of the deployed weights. -/
def cardClaim : Prop :=
  decisionCard deployed gate writtenPolicy .pay (recipe.config.test task.spec) = deployedCard

/-- Proved by kernel evaluation, which regenerates the 1,024 held-out examples from the seed and
runs the model, the gate and the baseline on each. -/
theorem card_certified : cardClaim := by unfold cardClaim; decide +kernel

/-! ## Gate properties, for every weight setting -/

/-- Whatever the weights: `pay` only at confidence at least 128/256. -/
theorem pay_needs_confidence (m : Model) (x : Profile)
    (h : (⟨m, gate⟩ : Decision _ _).run x = .choose .pay) :
    128 ≤ (judge m x : Judgment Disposition).confidence :=
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

/-- Paid: `pay` at 249/256. -/
theorem routine_pays : decision.run routine = .choose .pay := by decide +kernel

/-- Held: `hold` at 244/256. -/
theorem largeWithoutPO_holds : decision.run largeWithoutPO = .choose .hold := by decide +kernel

/-- The model's answer is `reject`, at 151/256; the gate never rejects, so the case goes to a
person. -/
theorem newVendorEmailBankChange_escalates :
    (decision.judge newVendorEmailBankChange).option = .reject ∧
      (decision.judge newVendorEmailBankChange).confidence = 151 ∧
      decision.run newVendorEmailBankChange = .defer := by decide +kernel

/-- The written policy rejects; the model answers `pay` at 193/256 and the gate pays, although
under the generator this profile is fraudulent one time in four. The `pay` threshold comes from
aggregate validation precision, which this profile hardly moves. -/
theorem newVendorPortalBankChange_pays :
    writtenPolicy newVendorPortalBankChange = .reject ∧
      (decision.judge newVendorPortalBankChange).confidence = 193 ∧
      decision.run newVendorPortalBankChange = .choose .pay := by decide +kernel
end IxAIDecide.Invoice
