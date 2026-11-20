import IxAIDecide.Invoice

/-!
# The deployed invoice decision

`deployed` is `recipe.train task.spec`, the model protocol v3 selected for seed 301
(`docs/decision-library.md`, "Protocol v3"), written out as literals so that every later
statement about it (its card, its decisions) is a small evaluation. That it is the training
function's output is the claim `trainingClaim`. At build time `IxAIDecideTest` checks it by
running training in Lean's interpreter; certifying it is the same job as for the triage model: an
Ix `Eval` claim, or a chain of per-step claims. Proving it with `decide +kernel` here would make
the kernel replay 2,560 SGD steps, which the triage model's 600-step run shows is too slow for a
build (21.7 minutes in `README.md`).

Everything else in this file is proved by kernel evaluation over the literal weights, or holds
for every weight setting.
-/

namespace IxAIDecide.Invoice

open IxAICore

private def fx (xs : List Int) : List Fx := xs.map Fx.mk

/-- The trained weights: 18 inputs, 8 hidden units, 3 outputs, 179 parameters. -/
def deployed : Model :=
  { w1 := [fx [80, -50, 21, -107, 82, -147, -43, -46, -147, -30, -142, -97, 65, -98, 34, -89, -82, 77],
      fx [-125, -54, -49, -114, 14, -108, 113, -74, -86, 52, -27, -10, 28, -125, -136, 86, -43, -78],
      fx [-30, -31, 0, -107, 84, 41, -195, 21, -57, 80, -83, -71, 53, 37, -139, -85, -26, -133],
      fx [490, 530, 510, 476, 508, 465, -71, -38, -61, 60, 288, -1, 2, 522, -35, 14, -562, -71],
      fx [29, -5, 13, -129, 88, -44, -115, -49, -157, 32, -124, 56, 10, -198, 53, 110, -162, -134],
      fx [508, 310, 364, 408, 331, 591, -62, -144, 35, -98, 68, 49, 284, -99, 497, 144, -77, 70],
      fx [608, 569, 589, 540, 488, 500, -27, 102, 46, -103, -531, -58, -144, -284, 0, 41, -551, -108],
      fx [6, 5, 131, 29, 3, -92, -235, -53, -60, -97, -166, 48, -33, 0, 46, 39, 134, -137]]
    b1 := fx [-187, -36, -89, -1091, -152, -851, -581, -174]
    w2 := [fx [111, 304, 147, 95, -35, -10, 102, 167],
      fx [-31, 62, 343, -85, 61, -28, -83, 408],
      fx [82, 136, 304, -8, -19, 43, -18, 18]]
    b2 := fx [31, 224, -1] }

/-- The weights are the specified training result. Checked at build time by evaluation; the
statement Ix would certify. -/
def trainingClaim : Prop := recipe.train task.spec = deployed

def decision : Decision Profile Disposition := ⟨deployed, gate⟩

/-- The card of `deployed` behind `gate`, against `writtenPolicy`, on seed 301's 1,024 held-out
examples. -/
def deployedCard : DecisionCard :=
  { total := 1024, modelCorrect := 901, baselineCorrect := 881, brierRaw := 57559
    decided := 337, decidedCorrect := 302, guardedChosen := 0, guardedWrong := 0 }

/-- The card is the specified evaluation of the deployed weights. -/
def cardClaim : Prop :=
  decisionCard deployed gate writtenPolicy .pay (recipe.config.test task.spec) = deployedCard

/-- Proved by kernel evaluation, which regenerates the 1,024 held-out examples from the seed and
runs the model, the gate and the baseline on each. -/
theorem card_certified : cardClaim := by unfold cardClaim; decide +kernel

/-! ## Gate properties, for every weight setting -/

/-- Whatever the weights: `pay` only at confidence at least `gate.need .pay`. -/
theorem pay_needs_confidence (m : Model) (x : Profile)
    (h : (⟨m, gate⟩ : Decision _ _).run x = .choose .pay) :
    gate.need .pay ≤ (judge m x : Judgment Disposition).confidence :=
  run_choose_need ⟨m, gate⟩ x h

/-- Whatever the weights: the gate never pays; every invoice the model would pay goes to a
person. -/
theorem never_pays (m : Model) (x : Profile) :
    (⟨m, gate⟩ : Decision _ _).run x ≠ .choose .pay :=
  run_never ⟨m, gate⟩ x .pay (show (256 : Int) < 257 by decide)

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

/-- The model answers `pay` at 246/256; the gate never pays, so a person decides. -/
theorem routine_escalates :
    (decision.judge routine).option = .pay ∧ (decision.judge routine).confidence = 246 ∧
      decision.run routine = .defer := by decide +kernel

/-- Held: `hold` at 199/256. -/
theorem largeWithoutPO_holds : decision.run largeWithoutPO = .choose .hold := by decide +kernel

/-- The riskiest visible profile: the model answers `pay` at 216/256, which a gate that paid
would act on; this gate sends it to a person. -/
theorem newVendorEmailBankChange_escalates :
    (decision.judge newVendorEmailBankChange).option = .pay ∧
      (decision.judge newVendorEmailBankChange).confidence = 216 ∧
      decision.run newVendorEmailBankChange = .defer := by decide +kernel

/-- The written policy rejects; the model answers `pay` at 247/256; the gate sends it to a
person. Under the generator this profile is fraudulent one time in four. -/
theorem newVendorPortalBankChange_escalates :
    writtenPolicy newVendorPortalBankChange = .reject ∧
      (decision.judge newVendorPortalBankChange).option = .pay ∧
      (decision.judge newVendorPortalBankChange).confidence = 247 ∧
      decision.run newVendorPortalBankChange = .defer := by decide +kernel

end IxAIDecide.Invoice
