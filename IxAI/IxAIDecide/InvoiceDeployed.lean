import IxAIDecide.Invoice

/-!
# The deployed invoice decision

`deployed` is the output of `train task.spec config`, written out as literals so that every
later statement about it (its card, its decisions) is a small evaluation. That it is the
training function's output is the claim `trainingClaim`. At build time `IxAIDecideTest` checks it
by running `train` in Lean's interpreter (about ten seconds); certifying it is the same job as for
the triage model: an Ix `Eval` claim, or a chain of per-step claims (`IxAICore.train_eq_of_chain`).
Proving it with `decide +kernel` here would make the kernel replay 2,560 SGD steps, which the
triage model's 600-step run shows is too slow for a build (21.7 minutes in `README.md`).

Everything else in this file is proved by kernel evaluation over the literal weights, or holds
for every weight setting.
-/

namespace IxAIDecide.Invoice

open IxAICore

private def fx (xs : List Int) : List Fx := xs.map Fx.mk

/-- The trained weights: 18 inputs, 8 hidden units, 3 outputs, 179 parameters. -/
def deployed : Model :=
  { w1 := [fx [166, 193, 199, 195, 154, 187, -116, -73, -19, -24, 34, 48, 59, -85, 59, -62, 33, 54],
      fx [315, 411, 384, 378, 365, 397, -201, -104, -29, 3, 40, 117, 176, -48, 133, -26, 86, 175],
      fx [327, 517, 445, 382, 381, 429, -480, -219, -58, -20, 94, 267, 417, -163, 295, -41, 167, 434],
      fx [400, 418, 376, 338, 371, 449, -313, -152, -106, -7, 133, 154, 347, -181, 327, 1, 208, 216],
      fx [423, 456, 415, 434, 470, 411, -187, -46, 14, -7, -164, -20, 10, 260, -48, 13, 516, 84],
      fx [553, 586, 588, 565, 565, 567, -317, 4, 41, -1, -129, 61, 147, 113, -47, 43, -296, 48],
      fx [412, 241, 187, 127, 209, 474, -64, 64, -312, 93, 86, 29, 137, -60, 431, 21, 25, 9],
      fx [424, 483, 461, 442, 410, 454, -149, -87, -88, 97, 435, 19, 189, -519, 85, 31, 168, 28]]
    b1 := fx [-436, -763, -733, -716, -912, -748, -729, -661]
    w2 := [fx [235, 191, -33, 41, -95, 58, -55, -95],
      fx [91, 130, -94, 10, 95, -49, -19, 85],
      fx [152, 181, -51, -38, 11, 8, 95, 21]]
    b2 := fx [215, 23, 9] }

/-- The weights are the specified training result. Checked at build time by evaluation; the
statement Ix would certify. -/
def trainingClaim : Prop := train task.spec config = deployed

def decision : Decision Profile Disposition := ⟨deployed, gate⟩

/-- The card of `deployed` behind `gate`, against `writtenPolicy`, on the 1,024 held-out
examples. -/
def deployedCard : DecisionCard :=
  { total := 1024, modelCorrect := 912, baselineCorrect := 893, brierRaw := 54299
    decided := 737, decidedCorrect := 679, guardedChosen := 441, guardedWrong := 36 }

/-- The card is the specified evaluation of the deployed weights. -/
def cardClaim : Prop :=
  decisionCard deployed gate writtenPolicy .pay (config.test task.spec) = deployedCard

/-- Proved by kernel evaluation, which regenerates the 1,024 held-out examples from the seed and
runs the model, the gate and the baseline on each (about 30 seconds). -/
theorem card_certified : cardClaim := by unfold cardClaim; decide +kernel

/-! ## Gate properties, for every weight setting -/

/-- Whatever the weights: the model's answer is `pay` only at confidence at least 230/256. -/
theorem pay_needs_confidence (m : Model) (x : Profile)
    (h : (⟨m, gate⟩ : Decision _ _).run x = .choose .pay) :
    230 ≤ (judge m x : Judgment Disposition).confidence :=
  run_choose_need ⟨m, gate⟩ x h

/-- Whatever the weights: `reject` only at confidence at least 192/256. -/
theorem reject_needs_confidence (m : Model) (x : Profile)
    (h : (⟨m, gate⟩ : Decision _ _).run x = .choose .reject) :
    192 ≤ (judge m x : Judgment Disposition).confidence :=
  run_choose_need ⟨m, gate⟩ x h

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

/-- Paid: the model gives `pay` 242/256, above the 230 that `pay` needs. -/
theorem routine_pays : decision.run routine = .choose .pay := by decide +kernel

/-- Held: `hold` at 157/256, above the floor. -/
theorem largeWithoutPO_holds : decision.run largeWithoutPO = .choose .hold := by decide +kernel

/-- The model's answer is `reject`, at 158/256, short of the 192 that `reject` needs, so the case
goes to a person. -/
theorem newVendorEmailBankChange_escalates :
    (decision.judge newVendorEmailBankChange).option = .reject ∧
      (decision.judge newVendorEmailBankChange).confidence = 158 ∧
      decision.run newVendorEmailBankChange = .defer := by decide +kernel

/-- The model leans to `pay` (183/256) where the written policy rejects; the gate sends it to a
person. -/
theorem newVendorPortalBankChange_escalates :
    (decision.judge newVendorPortalBankChange).option = .pay ∧
      writtenPolicy newVendorPortalBankChange = .reject ∧
      decision.run newVendorPortalBankChange = .defer := by decide +kernel

end IxAIDecide.Invoice
