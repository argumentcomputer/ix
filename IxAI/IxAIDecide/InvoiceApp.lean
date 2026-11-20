import IxAIDecide.InvoiceDeployed

/-!
# An application that pays invoices through the certified decision

`handle` is what an accounts-payable service would call for each incoming invoice. It does the
checks code can do exactly first, then asks the model only for the judgment that code cannot make,
and acts on the gate's verdict:

1. Exact checks, in ordinary code: the vendor must be on the approved list, and a total above
   its purchase order is held whatever the model says.
2. The judgment: `decision.run` on the invoice's profile.
3. The action: pay, hold, reject, or send to a person.

`handle_paid` is the property the business cares about, proved for every model: an invoice is
paid only if its vendor is approved, it is within its purchase order, and the model's confidence
in `pay` reached the gate's `pay` threshold (`gate.need .pay`, set on validation).
-/

namespace IxAIDecide.Invoice

open IxAICore

/-- An incoming invoice, as the application stores it. Amounts are in cents. -/
structure Invoice where
  vendorApproved : Bool
  tenure : Tenure
  channel : Channel
  total : Nat
  poTotal : Option Nat
  bankChanged : Bool
  disputes : Nat
  deriving Repr, DecidableEq

/-- Amount bands in cents: below 100, 1k, 5k, 10k, 50k, 100k, 500k dollars, then above. -/
def amountBand (cents : Nat) : Fin 8 :=
  let bounds := [10000, 100000, 500000, 1000000, 5000000, 10000000, 50000000]
  Fin.ofNat 8 (bounds.filter (· ≤ cents)).length

/-- The fields the model sees, derived from the stored invoice. -/
def Invoice.profile (inv : Invoice) : Profile :=
  { tenure := inv.tenure, channel := inv.channel, amount := amountBand inv.total
    hasPO := inv.poTotal.isSome, bankChanged := inv.bankChanged
    disputes := Fin.ofNat 4 (min inv.disputes 3) }

inductive Reason where
  | vendorNotApproved
  | overPurchaseOrder
  | model
  deriving Repr, DecidableEq

inductive Outcome where
  | paid
  | held (why : Reason)
  | rejected (why : Reason)
  /-- Sent to a person, with the model's leaning and confidence for context. -/
  | escalated (leaning : Disposition) (confidence : Int)
  deriving Repr, DecidableEq

/-- The total exceeds the purchase order it cites. -/
def Invoice.overPO (inv : Invoice) : Bool :=
  match inv.poTotal with
  | some po => decide (po < inv.total)
  | none => false

/-- Handle one invoice with the deployed decision `d`. -/
def handle (d : Decision Profile Disposition) (inv : Invoice) : Outcome :=
  if !inv.vendorApproved then .rejected .vendorNotApproved
  else if inv.overPO then .held .overPurchaseOrder
  else
    match d.run inv.profile with
    | .choose .pay => .paid
    | .choose .hold => .held .model
    | .choose .reject => .rejected .model
    | .defer =>
      let j := d.judge inv.profile
      .escalated j.option j.confidence

/-- For every model behind `gate`: a paid invoice has an approved vendor, is within its purchase
order, and was judged `pay` with confidence at least `gate.need .pay`. -/
theorem handle_paid (m : Model) (inv : Invoice) (h : handle ⟨m, gate⟩ inv = .paid) :
    inv.vendorApproved = true ∧ inv.overPO = false ∧
      gate.need .pay ≤ (judge m inv.profile : Judgment Disposition).confidence := by
  unfold handle at h
  by_cases ha : inv.vendorApproved = true
  · by_cases ho : inv.overPO = true
    · simp [ha, ho] at h
    · simp only [ha, ho, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      refine ⟨ha, by simpa using ho, ?_⟩
      split at h
      · rename_i hr
        exact pay_needs_confidence m inv.profile hr
      all_goals cases h
  · simp [ha] at h

/-- With the deployed gate, whose `pay` threshold is 257, no invoice is paid, for any weights. -/
theorem handle_never_pays (m : Model) (inv : Invoice) : handle ⟨m, gate⟩ inv ≠ .paid := by
  intro h
  have := (handle_paid m inv h).2.2
  have := judge_confidence_le (ω := Disposition) m inv.profile
  have hp : gate.need .pay = 257 := rfl
  omega

/-- The deployed service. -/
def service (inv : Invoice) : Outcome := handle decision inv

end IxAIDecide.Invoice
