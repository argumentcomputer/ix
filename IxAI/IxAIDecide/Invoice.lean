import IxAIDecide.Card
import IxAIDecide.Protocol
import IxAICore.Rng

/-!
# Use case: pay, hold or reject an invoice

The action is paying a supplier invoice, which cannot be undone. The judgment it depends on is
whether this invoice should be paid now, held for information, or rejected as likely fraudulent,
asked of a typed profile of the invoice.

## The generated data

There is no real dataset, so examples come from a seeded specification (`sampleInvoice`), as
the formula dataset does. Each draw, in order:

| Field | Distribution |
|---|---|
| `tenure` | `new`, `recent`, `established`, uniform |
| `channel` | `portal`, `edi`, `email`, uniform |
| `amount` | level 0–7, uniform (levels are amount bands; the application maps a total to one) |
| `hasPO` | true with probability 3/4 |
| `bankChanged` | true with probability 1/4 |
| `disputes` | 0 with probability 5/8, otherwise 1, 2 or 3, each 1/8 |

A hidden variable, `fraud`, is then drawn and never shown to the model. Its probability depends
on an interaction of three fields:

| Condition | P(fraud) |
|---|---|
| bank details changed, new vendor, invoice by email | 24/32 |
| bank details changed, and new vendor or email (not both) | 8/32 |
| bank details changed otherwise | 2/32 |
| bank details unchanged | 1/32 |

The label is the stated rule `ruleLabel`: `reject` if fraudulent; otherwise `hold` if there is no
purchase order and the amount level is 5 or more, or if there are two or more prior disputes;
otherwise `pay`. Finally, with probability 1/16 the label is replaced by a uniformly drawn option
(which may be the same one), standing for clerical error.

The **baseline** (`writtenPolicy`) is the rule a finance team would write from the fraud
guidance "reject when a new vendor changes bank details": it uses the visible fields and the
same hold conditions, and does not know about the email interaction. `bayesRule` is the best
any predictor of the visible fields can do in expectation; it is not available in practice,
and is given only as a ceiling.
-/

namespace IxAIDecide.Invoice

open IxAICore

inductive Tenure where
  | new | recent | established
  deriving Repr, DecidableEq, Inhabited

instance : Finite Tenure := finiteOf [.new, .recent, .established]

inductive Channel where
  | portal | edi | email
  deriving Repr, DecidableEq, Inhabited

instance : Finite Channel := finiteOf [.portal, .edi, .email]

/-- The options. `pay` cannot be undone; `hold` and `reject` can be revisited. -/
inductive Disposition where
  | pay | hold | reject
  deriving Repr, DecidableEq, Inhabited

instance : Finite Disposition := finiteOf [.pay, .hold, .reject]

/-- What the model sees about an invoice. -/
structure Profile where
  tenure : Tenure
  channel : Channel
  /-- Amount band, 0 (smallest) to 7. -/
  amount : Fin 8
  hasPO : Bool
  bankChanged : Bool
  /-- Prior disputes with this vendor, capped at 3. -/
  disputes : Fin 4
  deriving Repr, DecidableEq, Inhabited

/-- Every field is visible to the model: 3 + 3 + 7 + 1 + 1 + 3 = 18 features. -/
instance : Encode Profile :=
  Encode.via fun p => (p.tenure, p.channel, p.amount, p.hasPO, p.bankChanged, p.disputes)

/-- Probability of fraud, in 32nds. -/
def fraudRisk (p : Profile) : Nat :=
  if !p.bankChanged then 1
  else
    let isNew := p.tenure == .new
    let byEmail := p.channel == .email
    if isNew && byEmail then 24 else if isNew || byEmail then 8 else 2

/-- The hold conditions, shared by the label rule and the baseline. -/
def needsHold (p : Profile) : Bool :=
  (!p.hasPO && decide (5 ≤ p.amount.val)) || decide (2 ≤ p.disputes.val)

def ruleLabel (p : Profile) (fraud : Bool) : Disposition :=
  if fraud then .reject else if needsHold p then .hold else .pay

def tenureOf (k : Nat) : Tenure := if k == 0 then .new else if k == 1 then .recent else .established
def channelOf (k : Nat) : Channel := if k == 0 then .portal else if k == 1 then .edi else .email
def dispositionOf (k : Nat) : Disposition :=
  if k == 0 then .pay else if k == 1 then .hold else .reject

def sampleInvoice (r : Rng) : Labelled Profile Disposition × Rng :=
  let (t, r) := r.below 3
  let (c, r) := r.below 3
  let (a, r) := r.below 8
  let (po, r) := r.below 4
  let (bank, r) := r.below 4
  let (d, r) := r.below 8
  let p : Profile :=
    { tenure := tenureOf t, channel := channelOf c, amount := Fin.ofNat 8 a, hasPO := po != 0
      bankChanged := bank == 0, disputes := Fin.ofNat 4 (d - 4) }
  let (f, r) := r.below 32
  let (noise, r) := r.below 16
  let (flip, r) := r.below 3
  let label := if noise == 0 then dispositionOf flip else ruleLabel p (decide (f < fraudRisk p))
  (⟨p, label⟩, r)

def task : Task Profile Disposition := ⟨"invoice-disposition", sampleInvoice⟩

/-- The rule a finance team would write without knowing the email interaction. -/
def writtenPolicy (p : Profile) : Disposition :=
  if p.bankChanged && p.tenure == .new then .reject else if needsHold p then .hold else .pay

/-- The most probable label given the visible fields: reject only when fraud is more likely than
not (risk 24/32), otherwise the rule's answer without fraud. -/
def bayesRule (p : Profile) : Disposition :=
  if fraudRisk p > 16 then .reject else if needsHold p then .hold else .pay

/-! ## Training configuration and gate -/

/-- The base configuration: 512 training examples, batches of 16, 1,024 held-out and 1,024
validation examples. The protocol (`IxAIDecide.grid`) sets the seed, hidden units, learning rate
and epochs; the seed here is the first model's, kept for `writtenPolicy` comparisons in tests. -/
def config : Config :=
  { seed := 2026, hidden := 8, lrRaw := 8, epochs := 80, batch := 16, trainSize := 512,
    testSize := 1024 }

/-- The recipe the protocol selected for seed 101 on validation: fan-in initialization with gain
627/256, learning rate 8/256, 16 hidden units, 60 epochs (1,920 SGD steps). -/
def recipe : Recipe :=
  ⟨{ config with seed := 101, hidden := 16, lrRaw := 8, epochs := 60 }, 627⟩

/-- Validation targets: `pay` right 90% of the time, `hold` 80%, `reject` 90%, each over at
least 20 validation answers. -/
def targetPercent : Disposition → Nat
  | .pay => 90
  | .hold => 80
  | .reject => 90

/-- The thresholds `thresholdFor` gives on `recipe`'s validation judgments for those targets
(checked in `IxAIDecideTest`): `pay` and `hold` qualify at the floor, 128/256; `reject` at no
threshold, so it is 257 and the gate never rejects (`run_never`). Below the floor every case goes
to a person. -/
def gate : Gate Disposition :=
  { floor := 128
    need := fun
      | .pay => 128
      | .hold => 128
      | .reject => 257 }

end IxAIDecide.Invoice
