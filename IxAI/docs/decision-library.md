# A library for certified decisions

`IxAIDecide` lets a Lean program declare a narrow decision, train a small model for it with
`IxAICore`'s deterministic training, and call it through a gate whose safety is proved for every
weight setting. It generalizes the triage model (one hard-wired task: formulas, 8 features,
three answer groups, one gate) into a facility for any task over structured records. This is a
first version, written 2026-11-20; what does not work yet is listed at the end.

The pattern comes from Jev's use-case map (`docs.typesafe.ai/concepts/use-case-map`): start from
an action, list the judgments it depends on, ask each as a narrow question with a typed answer
and a probability, and keep the rules that combine the answers in ordinary code, with stricter
thresholds for actions that are hard to undo and uncertain cases sent to a person. What this
library adds:

- **Options are a Lean type.** A decision is a function from a typed input to a `Verdict`: one
  value of a finite option type, or `defer`.
- **The gate is proved.** Its theorems hold for every model output, so for weights before
  training, after training, and weights nobody trained.
- **The model is its specification.** The weights are `IxAICore.train t.spec config`, a pure
  function of a seeded data generator and a configuration, and the card is a pure function of the
  weights.
- **Each decision can carry a proof.** `decision.run x = .choose o` for concrete `x` is a theorem
  the Lean kernel checks by evaluation, and Ix can certify it in the same way as the triage
  model's decision receipts.

**Domain.** The models are fixed-point MLPs over integer features. They decide over structured
records: enumerations, flags, ordered levels, bucketed numbers. They cannot read free text, which
most of Jev's examples need. The section "Text" sketches what would and would not be certified
if an untrusted encoder supplied the features.

## The interface

Library: `IxAIDecide/Encode.lean`, `Decide.lean`, `Card.lean`. Use case:
`IxAIDecide/Invoice.lean`, `InvoiceDeployed.lean`, `InvoiceApp.lean`. Tests: `IxAIDecideTest.lean`.

A complete decision, from type declarations to a call site. This compiles against the library
as built (checked with `lake env lean`):

```lean
import IxAIDecide
open IxAICore IxAIDecide

-- 1. The options: a finite type. `finiteOf` fixes their order, which fixes the model's outputs.
inductive Queue where
  | close | tier1 | incident
  deriving Repr, DecidableEq, Inhabited
instance : Finite Queue := finiteOf [.close, .tier1, .incident]

inductive Severity where
  | low | medium | high
  deriving Repr, DecidableEq, Inhabited
instance : Finite Severity := finiteOf [.low, .medium, .high]

-- 2. The input: a record. The encoding is derived from the types of the fields the model may
--    see; `hostId` is left out, so the model never sees it.
structure Alert where
  severity : Severity
  assetCritical : Bool
  seenBefore : Bool
  failedLogins : Fin 4
  hostId : Nat
  deriving Repr, DecidableEq, Inhabited

instance : Encode Alert :=
  Encode.via fun a => (a.severity, a.assetCritical, a.seenBefore, a.failedLogins)
-- width 3 (one-hot) + 1 + 1 + 3 (thermometer) = 8 features

-- 3. The task: a seeded generator of labelled examples.
def label (a : Alert) : Queue :=
  if a.assetCritical && a.severity == .high then .incident
  else if a.seenBefore then .close else .tier1

def sample (r : Rng) : Labelled Alert Queue × Rng :=
  let (s, r) := r.below 3
  let (c, r) := r.below 2
  let (b, r) := r.below 2
  let (f, r) := r.below 4
  let a : Alert := { severity := if s == 0 then .low else if s == 1 then .medium else .high
                     assetCritical := c == 1, seenBefore := b == 1
                     failedLogins := Fin.ofNat 4 f, hostId := 0 }
  (⟨a, label a⟩, r)

def task : Task Alert Queue := ⟨"alert-queue", sample⟩

-- 4. Training is the core's `train`; the configuration names the seed and every size.
def config : Config :=
  { seed := 1, hidden := 4, lrRaw := 8, epochs := 20, batch := 16, trainSize := 128,
    testSize := 128 }

-- 5. The gate: closing an alert is hard to undo, so it needs 0.9; the rest need the 0.5 floor.
def gate : Gate Queue :=
  { floor := 128, need := fun | .close => 230 | .incident => 128 | .tier1 => 128 }

def decision : Decision Alert Queue := ⟨train task.spec config, gate⟩

-- 6. The call site: ordinary code acting on a verdict.
def route (a : Alert) : String :=
  match decision.run a with
  | .choose .close => "closed"
  | .choose .tier1 => "tier 1"
  | .choose .incident => "incident"
  | .defer => "analyst"

-- 7. A theorem for free, for every weight setting.
example (m : Model) (a : Alert) (h : (⟨m, gate⟩ : Decision Alert Queue).run a = .choose .close) :
    230 ≤ (judge m a : Judgment Queue).confidence :=
  run_choose_need ⟨m, gate⟩ a h
```

In this example the label is a noiseless rule over visible fields, and the trained model matches
it on all 128 held-out alerts. That is the case where no model is needed: use the rule. The
library earns its place when the label depends on interactions the rule-writer does not know,
or on noise the model must quantify, as in the invoice use case below.

### The pieces

| Name | What it is |
|---|---|
| `Encode α` | `width` and `encode : α → List Int`, the features. |
| `finiteOf l` | A `Finite α` (the core's option class) from a list of values. `Finite.Lawful α` is a decidable check that the order and the index agree. |
| `Labelled ι ω` | An input with its specified option. |
| `Task ι ω` | A name and `sample : Rng → Labelled ι ω × Rng`. |
| `Task.spec` | The task as an `IxAICore.Spec` with one answer group, so `train`, `Config.data`, `Config.test`, `Config.schedule`, `Config.init` and `train_eq_of_chain` apply unchanged. |
| `judge m x` | The model's most probable option, its probability and all probabilities, in units of 1/256. |
| `Gate ω` | `floor : Int` and `need : ω → Int`. `Gate.apply` returns the model's option if its confidence reaches both, else `defer`. |
| `Decision ι ω` | Weights and a gate. `Decision.run x : Verdict ω`. |
| `cascade first second` | Ask `first`; on `defer`, ask `second`. |
| `decisionCard m g baseline guarded test` | Accuracy, Brier score, how many cases the gate decided and how many of those were right, how often the guarded option was returned and how often wrongly, and the baseline rule's accuracy. |

### Theorems every decision gets

All in `IxAIDecide/Decide.lean`, quantified over every judgment, hence every model and input:

| Theorem | Statement |
|---|---|
| `apply_choose_need`, `run_choose_need` | If the verdict is `choose o`, then `need o ≤ confidence`. |
| `apply_choose_floor` | If the verdict is `choose o`, then `floor ≤ confidence`. |
| `apply_defer_of_lt_floor`, `run_defer_of_lt_floor` | If `confidence < floor`, the verdict is `defer`. |
| `apply_choose_eq`, `run_choose_eq` | If the verdict is `choose o`, then `o` is the judgment's `option`, the option at the model's largest output (first one on a tie). The gate never substitutes another option. |
| `apply_defer_iff` | The verdict is `defer` if and only if `confidence < floor` or `confidence < need option`. |
| `apply_stricter` | If `g'` has a floor and every need at least `g`'s (`Gate.Stricter`), then whenever `g'` returns `choose o`, `g` returns `choose o` too. |
| `cascade_choose` | If `cascade first second x = choose o`, then `first x = choose o`, or `first x = defer` and `second x = choose o`. |
| `judge_confidence_le` | For any weights and input, `confidence ≤ 256`. |
| `run_never` | If `need o > 256`, then `d.run x ≠ choose o` for every input: a threshold of 257 rules an option out, whatever the weights. |

`confidence` is the judgment's probability for its own option, from `probabilitiesNonneg`; the
theorems say nothing about whether that number is calibrated (see "What the gate does not say").

An application composes these with its own exact checks, as `handle_paid` does below.

## Inputs from Lean types

Features are derived from the type's structure by instance resolution:

| Type | Encoding | Width |
|---|---|---|
| `Bool` | `0` or `1` | 1 |
| an enumeration with `Finite` | one-hot | number of values |
| `Fin (n + 1)`, an ordered level | thermometer: `k` ones, then zeros | `n` |
| `α × β` | concatenation | sum of widths |
| `Option α` | presence flag, then `α` or zeros | `1 +` width of `α` |
| a record | `Encode.via` a projection to a product of its visible fields | that product's |

The projection is the one line an author writes per record, and it doubles as the statement of
what the model may see. There is no `deriving Encode` handler yet; it would generate exactly this
projection from the structure's fields.

Numbers must be bucketed into a small ordered level by code (`amountBand` in the use case). The
core reads features with `Fx.ofInt`, so every feature is an integer, and inputs of large magnitude
destabilize fixed-point SGD; thermometer levels keep every feature at 0 or 1.

## How Jev's decision shapes map

| Shape | Fits? | How |
|---|---|---|
| Classification: one category from a known list | yes | `ω` is the list. The invoice and alert examples. |
| Detection: probability a property is present | yes | `ω := Bool` (`Finite Bool` is in the core). The gate's `need .true` is the detection threshold; `need .false` can be set high to defer rather than clear. |
| Scoring: a point on an ordered scale | partly | `ω` is the scale as an enumeration. The model treats levels as unordered categories (one-hot targets, Brier loss), so it does not know that 3 is closer to 4 than to 0. An ordinal loss would need a new spec in the core. |
| Routing: a category picks the next code path | yes | `match decision.run x with …` is the router; `defer` is one more path. |
| Verification: check an output for specific error kinds | yes, over structured outputs | `ι` is the structured output (a record of a computed result's fields), `ω` the error kinds plus `ok`. Errors code can detect exactly stay in code, as `overPO` does. Verifying free text is out of reach. |
| Cascade: cheap model first, escalate when unsure | yes | `cascade d₁.run d₂.run`, with `cascade_choose` carrying each stage's guarantee to the result. The test file cascades the written policy's hold rule before the model. |
| Free-text judgments (claims notes, alert descriptions, emails, LLM outputs) | no | No text encoder. See "Text". |
| Choosing a function-call argument from a fixed list | yes, if the context is structured | `ω` is the list of values. |

## Use case: pay, hold or reject an invoice

Paying a supplier invoice cannot be undone. The judgment: pay now, hold for information, or
reject as likely fraud. `Profile` (`IxAIDecide/Invoice.lean`) is the model's view: vendor tenure
(`new | recent | established`), channel (`portal | edi | email`), amount band (`Fin 8`), purchase
order present, bank details changed, prior disputes (`Fin 4`). 18 features.

**Data.** Seeded generator `sampleInvoice`, fields drawn as tabulated in `Invoice.lean`. A hidden
variable `fraud` is drawn and not shown to the model; its probability is 24/32 when bank details
changed, the vendor is new and the invoice came by email, 8/32 when bank details changed and
exactly one of the other two holds, 2/32 when only bank details changed, 1/32 otherwise. The
label is `reject` if fraudulent, else `hold` without a purchase order at amount level 5 or more or
with two or more disputes, else `pay`; then with probability 1/16 a uniformly drawn option replaces
it. Training set: 512 examples from seed 2026 (327 pay, 140 hold, 45 reject); held-out set: 1,024
examples from seed 2026 + 1000003.

**Baselines.** `writtenPolicy` is the rule a finance team would write from "reject when a new
vendor changes bank details", with the same hold conditions. `bayesRule` is the most probable label
given the visible fields, which needs knowledge of the generator and is shown only as a ceiling.

**First model (superseded).** The first model (seed 2026, 8 hidden units, `IxAICore`'s
initialization, 2,560 steps) had its learning rate and length chosen by looking at its own
held-out score. On that seed it scored 912 of 1,024 against the written policy's 893 and the
ceiling's 918, but with the same settings on seeds 1, 2 and 3 it scored 906, 842 and 852 against
the policy's 890, 878 and 903: a mean of 878 against the policy's 891. Its gate thresholds were
set by hand (`pay` 230, `reject` 192) and `reject` was never reached. The protocol below replaces
it; the deployed model is now the protocol's model for seed 101.

## Training protocol for the invoice model

The first model's settings were chosen by looking at its own held-out score, and across seeds it
did not beat the written policy. This protocol replaces that. It was written down before any of
its runs.

**Data per seed `s`.** Training: 512 examples from `Rng.seeded s` (`Config.data`). Validation:
1,024 examples from `Rng.seeded (s + 2000003)` (`validationSet`). Held-out: 1,024 examples from
`Rng.seeded (s + 1000003)` (`Config.test`). The three sets come from distinct generator streams.
They are not disjoint as sets of profiles: there are only 1,152 distinct profiles, so the same
profile recurs across sets with independently drawn labels.

**What varies** (8 runs per seed, each scored at 6 checkpoints, so 48 candidates):

| Setting | Values |
|---|---|
| Initialization | fan-in scaled (`Recipe.init`): each layer's weights uniform in `±gain/√fanIn`, biases zero; gain 1.0 or 2.45 (≈ √6), raw 256 or 627 |
| Learning rate (`lrRaw`, per summed batch gradient) | 4 or 8 |
| Hidden units | 8 or 16 |
| Training length | checkpoints after 20, 40, 60, 80, 100 and 120 epochs of 32 batches of 16 |

Training with fewer epochs is a prefix of training with more (`Config.schedule` draws epochs in
sequence from one generator), so a checkpoint at `e` epochs is exactly the recipe with
`epochs := e`.

**Selection rule, validation only.** The candidate with the most validation examples whose most
probable option equals the label; ties broken by lower validation Brier sum, then fewer epochs,
fewer hidden units, lower learning rate, lower gain. `selectRecipe` implements this.

**Thresholds, validation only.** On the selected model's validation judgments, for each option
`o` and each candidate threshold `t` in 128, 136, …, 256: take the validation examples whose
most probable option is `o` with confidence at least `t`. `need o` is the smallest `t` at which
there are at least 20 such examples and at least the target fraction of them have label `o`.
Targets: `pay` 90%, `hold` 80%, `reject` 90%. If no `t` qualifies, `need o` is 257, above every
probability the model can output, so the gate never returns `o`. The floor stays 128.
`thresholdsFrom` implements this.

What the targets mean against the generator: with 1/16 label noise and a 1/32 fraud rate even
for the safest profile, a perfect predictor's `pay` answers are right about 93% of the time,
so 90% is near the best reachable. A `reject` answer is right at most about 72% of the time (the
riskiest profile is fraudulent with probability 3/4, and noise lowers it), so at 90% `reject`
is expected to stay a person's decision. That is the intended reading: under this generator the
fields cannot establish fraud with the confidence rejecting a real vendor would require.

**Seeds reported:** 101 to 108, fixed in advance. Seed 2026 is not among them because its
settings were tuned on its held-out set before this protocol existed.

**Held-out set:** scored once per seed, for the selected recipe and thresholds only. Reported per
seed: the model's correct count, the written policy's, the ceiling rule's; behind the gate: how
many decided, how many of those right, how many `pay`s and how many of those wrong; and
calibration by confidence bin.

**Criterion for "reliably matches or beats the policy"**, also fixed in advance: the model's
held-out correct count is at least the policy's on at least 7 of the 8 seeds, and its mean over
the 8 seeds is at least the policy's mean.

**The deployed model** is seed 101's selected recipe, with its validation thresholds.

## Protocol results

All numbers below are from the protocol as written above, run once per seed (each seed about
116 s in Lean's interpreter, in three `ix/light.sh` jobs; the script is not part of the library,
but `candidates`, `selectRecipe`, `thresholdFor` and `calibration` in `IxAIDecide/Protocol.lean`
are the whole computation). Held-out sets have 1,024 examples.

| Seed | Selected: gain, lr, hidden, epochs | `need pay` | Model | Policy | Ceiling | Decided | Right among decided | Model's `pay`s / wrong | Policy's `pay`s / wrong |
|---|---|---|---|---|---|---|---|---|---|
| 101 | 627, 8, 16, 60 | 128 | 914 | 888 | 918 | 991 | 894 | 653 / 60 | 617 / 48 |
| 102 | 627, 4, 16, 80 | 160 | 904 | 886 | 916 | 936 | 836 | 597 / 62 | 626 / 58 |
| 103 | 256, 8, 16, 60 | 128 | 913 | 899 | 920 | 1,008 | 900 | 701 / 69 | 655 / 54 |
| 104 | 256, 8, 16, 100 | 128 | 899 | 900 | 916 | 999 | 887 | 683 / 72 | 637 / 49 |
| 105 | 256, 8, 16, 60 | 144 | 890 | 883 | 910 | 957 | 852 | 614 / 61 | 610 / 58 |
| 106 | 256, 8, 8, 100 | 160 | 892 | 884 | 911 | 980 | 866 | 678 / 78 | 662 / 71 |
| 107 | 256, 8, 8, 60 | 152 | 903 | 876 | 915 | 992 | 886 | 663 / 75 | 626 / 63 |
| 108 | 256, 8, 16, 80 | 136 | 903 | 897 | 907 | 984 | 878 | 671 / 68 | 637 / 52 |
| Mean | | | 902.3 | 889.1 | 914.1 | 980.9 | 874.9 | 657.5 / 68.1 | 633.8 / 56.6 |

`need hold` was 128 and `need reject` 257 on every seed: `reject` never qualified, as predicted.

**Accuracy: the criterion is met.** The model's most probable option is at least as accurate as
the written policy on 7 of 8 seeds (seed 104 is 1 short), and its mean is 13.1 higher (902.3
against 889.1), closing a little over half of the 25-case gap between the policy and the
ceiling. No setting was chosen on held-out data. What changed from the first model: fan-in
initialization, and choosing the training length on validation, which matters because
validation accuracy is not monotone in training length (seed 101, gain 1.0, rate 4, 8 hidden:
813 after 40 epochs, 735 after 60, 829 after 80).

**Wrong payments: the gate is worse than the policy.** Behind the validation-set thresholds the
model pays 24 more invoices per seed than the written policy, and 11.5 more of its payments have
another label (10.4% wrong against the policy's 8.9%). The reason is the threshold rule: it asks
for 90% precision over all validation `pay` answers, and because most `pay` answers are routine
invoices, the rule is satisfied at the floor even though some profiles it pays are risky. The
deployed model pays a new vendor that changed bank details through the portal at confidence
193/256 (`newVendorPortalBankChange_pays`), a profile that is fraudulent one time in four; the
written policy rejects it. A precision target over the whole option is the wrong rule for the
irreversible option. What would fix it, not tried: require the target in every confidence bin
at and above the threshold, or set the `pay` target above the written policy's own precision
(91%) so the gate is never looser than the rule it replaces.

**Calibration** (all 8 seeds pooled, 8,192 held-out answers):

| Confidence bin (of 256) | Answers | Mean confidence | Right | Decided | Right among decided |
|---|---|---|---|---|---|
| below 128 | 52 | 45.3% | 44.2% | 0 | — |
| 128–159 | 430 | 56.2% | 65.3% | 192 | 64.1% |
| 160–191 | 728 | 69.6% | 81.3% | 697 | 82.1% |
| 192–223 | 2,322 | 82.4% | 89.0% | 2,298 | 89.1% |
| 224–256 | 4,660 | 93.9% | 91.3% | 4,660 | 91.3% |

Confidence means something: accuracy rises with it in every bin. It is not calibrated: in the
middle bins the model is right 7–12 points more often than it says, and in the top bin 2.6
points less often. The top bin cannot do much better than about 93% under 1/16 label noise. A
gate threshold read as a probability is therefore conservative in the middle and optimistic at
the top; `thresholdFor` uses observed precision on validation, not the stated confidence, for
this reason.

**Reject stays a person's decision.** No `reject` threshold reaches 90% on validation, which
matches the generator: the riskiest visible profile is fraudulent with probability 3/4, so a
`reject` answer is right at most about 72% of the time. The visible fields cannot establish fraud
with the confidence that rejecting a real vendor should need. `never_rejects` proves that the
deployed gate never rejects, for every weight setting.

**Why the model still trails the ceiling by 12.** Evidence, not proof: (1) In the deployed model, 4
of the 16 hidden units have a pre-activation of at most 0 on every one of the 1,152 valid
profiles, so they never contribute (checked by enumerating the profiles against the weights). (2) Brier loss
with one-hot targets on 1/16-noised labels pulls outputs toward the noise floor, which flattens
the margin for the rare `reject` class (45 of 512 training examples). (3) 512 training examples
cover at most 512 of the 1,152 profiles. Next: a larger training set, a smaller learning rate
late in training, and initial biases set positive so units start active.

### The v1 deployed model (seed 101, superseded)

Seed 101's selected recipe (gain 627, learning rate 8, 16 hidden units, 60 epochs) behind v1's
thresholds (`pay` 128, `hold` 128, `reject` 257): card 914 correct against the policy's 888, 991
decided with 894 right, 653 `pay`s of which 60 wrong. It paid the new-vendor, portal,
bank-change profile at 193/256. Replaced by the protocol v2 model below.

## Protocol v2: thresholds that hold in every bin

Under v1 the gate paid more wrong invoices than the written policy (10.4% against 8.9%), because a
precision target averaged over all `pay` answers was met at the floor. v2 changes **only the
threshold rule**. Data streams, the grid, training and `selectRecipe` are exactly as in v1, so
each seed's selected model is the one v1 would select, and any difference in the gated numbers is
the rule's. Written before any v2 run.

**Bins.** `gateBins`: confidence `[128, 160)`, `[160, 192)`, `[192, 224)`, `[224, 257)` (in
256ths). Candidate thresholds are the four lower edges.

**Rule** (`thresholdPerBin`). For option `o`, on the selected model's validation judgments: `need o`
is the lowest edge `e` such that **every** bin with lower edge at least `e` holds at least 20
validation answers whose most probable option is `o`, and those answers meet `o`'s target. A bin
with fewer than 20 such answers fails: too little evidence counts against deciding, not for it.
If no edge qualifies, `need o` is 257 and the gate never returns `o` (`run_never`). The floor stays
128.

**Targets.**
- `pay`: the written policy's own `pay` precision on the same validation set plus one percentage
  point. With `R` of the policy's `P` validation `pay`s right, a bin with `n` answers of which `r`
  are right meets it when `100·P·r ≥ (100·R + P)·n` (`policyPayTarget`).
- `hold`: 80% in every bin. `reject`: 90% in every bin (as in v1, now per bin).

**Seeds:** 201 to 208, fixed in advance and never run before. The held-out set is scored once per
seed. v1's thresholds on the same models are reported beside v2's, for attribution only.

**Success criteria, fixed in advance.**
- **Safety:** the fraction of the gated model's `pay`s whose label is another option is at most
  the written policy's fraction on at least 7 of the 8 seeds, and lower when pooled over the 8
  seeds. A seed where the gate pays nothing counts as 0 wrong.
- **Usefulness:** the gate decides (returns an option, not `defer`) at least 512 of 1,024
  held-out invoices on average, and pays at least half as many invoices as the written policy on
  average. **Below 50% coverage the gate is pointless**: a person would see most invoices anyway,
  and the written policy decides all of them.
- Both must hold for the rule to count as working. If safety holds only by deferring almost
  everything, that is the finding.

**Deployed:** seed 201's selected model with its v2 thresholds.

## Protocol v2 results

Run once on seeds 201–208 (about 80 s per seed in the interpreter with the `@[csimp]` fast
schedule, in three `ix/light.sh` jobs). The models are the ones v1's selection picks; only the
thresholds differ. `need` is `pay / hold`; `reject` was 257 on every seed. Before the full run, a
one-candidate smoke test of the sweep script was run on seed 201 (20 epochs, one recipe) to check
the script; it did not feed any choice.

| Seed | Selected: gain, lr, hidden, epochs | `need` | Model | Policy | Ceiling | Decided | Right among decided | Deferred | Model's `pay`s / wrong | Policy's `pay`s / wrong | v1 thresholds' `pay`s / wrong |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 201 | 627, 8, 8, 100 | 224 / 128 | 877 | 857 | 885 | 718 | 636 | 306 | 438 / 34 (7.8%) | 612 / 66 (10.8%) | 648 / 77 (11.9%) |
| 202 | 627, 8, 16, 60 | 192 / 192 | 910 | 883 | 921 | 818 | 746 | 206 | 552 / 51 (9.24%) | 628 / 58 (9.24%) | 642 / 65 (10.1%) |
| 203 | 256, 8, 16, 100 | 257 / 192 | 903 | 895 | 918 | 290 | 259 | 734 | 0 / 0 | 654 / 55 (8.4%) | 713 / 77 (10.8%) |
| 204 | 627, 4, 16, 80 | 257 / 192 | 900 | 882 | 911 | 196 | 172 | 828 | 0 / 0 | 653 / 63 (9.6%) | 681 / 82 (12.0%) |
| 205 | 256, 8, 16, 60 | 224 / 160 | 921 | 885 | 927 | 522 | 482 | 502 | 232 / 14 (6.0%) | 639 / 50 (7.8%) | 663 / 53 (8.0%) |
| 206 | 256, 8, 16, 20 | 224 / 160 | 909 | 885 | 911 | 521 | 476 | 503 | 220 / 17 (7.7%) | 642 / 62 (9.7%) | 639 / 61 (9.5%) |
| 207 | 256, 8, 16, 40 | 257 / 160 | 918 | 905 | 937 | 275 | 253 | 749 | 0 / 0 | 643 / 50 (7.8%) | 564 / 46 (8.2%) |
| 208 | 256, 8, 16, 80 | 224 / 192 | 903 | 892 | 918 | 662 | 608 | 362 | 355 / 19 (5.4%) | 651 / 63 (9.7%) | 668 / 68 (10.2%) |
| Mean | | | 905.1 | 885.5 | 916.0 | 500.3 | 454.0 | 523.8 | 224.6 / 16.9 | 640.3 / 58.4 | 652.3 / 66.1 |

**Safety: met, partly vacuously.** The gated model's wrong-payment fraction is at most the
policy's on 7 of 8 seeds (seed 202 is above it by 0.003 points: 51/552 against 58/628), and
pooled over the 8 seeds it is 7.5% (135 of 1,797) against the policy's 9.1% (467 of 5,122). But 3
of those 7 seeds (203, 204, 207) pay nothing at all, which the rule fixed in advance counts as 0
wrong. On the 5 seeds where the gate pays, it is safer than the policy on 4.

**Usefulness: not met.** The gate decides 500.3 of 1,024 invoices on average, just under the 512
fixed in advance as the point below which it is pointless, and on 3 seeds it decides fewer than
300. It pays 224.6 invoices per seed against the policy's 640.3, far under the half (320) required.
**The rule fails as a whole: safety is bought mostly by deferring.**

**Accuracy** of the most probable option, unchanged by the rule: 905.1 against the policy's 885.5
and the ceiling's 916.0, at least the policy's on all 8 seeds. v1's thresholds on the same models
paid wrongly 10.1% of the time (529 of 5,218), so the v1 result reproduces on fresh seeds.

**Why it fails.** The `pay` target, the policy's validation precision plus one point (90.9% to
93.6% across the seeds), sits at the noise ceiling: with 1/16 of labels replaced at random, even
a perfect `pay` is right about 93% of the time. And requiring it in **every** bin, each judged on
20 to 550 validation answers, makes the outcome depend on sampling noise of several points in
the smallest bin. Seed 203's top `pay` bin held 48 answers with 44 right (91.7% against a target
of 93.6%); seed 204's held 38 with 35 right (92.1% against 92.5%); one short bin and `pay`
becomes 257.

**What I would change, not tried on these seeds** (a v3 must be fixed in advance and run on fresh
seeds):
- Judge a threshold `t` on the **cumulative** answers at or above every edge from `t` up, not on
  each bin alone: this still forbids a low-confidence region from hiding behind a good top bin,
  but each test uses at least as many answers as the top bin.
- Make the margin statistical rather than fixed: require the policy's precision to be below a
  lower confidence bound of the gate's (for example, a one-sided binomial bound computed in
  integers), so a thin bin fails for lack of evidence and a large bin can pass at the policy's
  own level.
- Use a larger validation set (4,096 examples) so the top bins hold hundreds of answers.
- Compare against the policy on the same invoices: the policy's precision among the invoices
  the gate would pay, rather than over all its own payments.

### The v2 deployed model (seed 201, superseded)

Seed 201's selected recipe (gain 627, learning rate 8, 8 hidden units, 100 epochs) behind v2's
thresholds (`pay` 224, `hold` 128, `reject` 257): card 877 correct against the policy's 857, 718
decided with 636 right, 438 `pay`s of which 34 wrong. It escalated the new-vendor, portal,
bank-change profile (`pay` at 183, below 224). Replaced by the protocol v3 model below.

## Protocol v3: a binomial test on cumulative answers

The last round. v2 was safe but not useful, because a fixed margin judged on thin bins turned
sampling noise into deferral. v3 changes **only the threshold rule and the validation set size**.
Training streams, the grid, training and the selection rule are as in v1 and v2. Written before
any v3 run.

**Validation set:** 4,096 examples from `Rng.seeded (s + 2000003)` (`validationSetN`), used both
for selection and for thresholds. Its first 1,024 examples are v1's validation set, because the
generator draws examples in sequence.

**The test.** For a set of `n` answers of which `r` are right and a comparison precision
`p₀ = a/(a + b)`, the test passes when the exact binomial upper tail
`P(X ≥ r | n, p₀) = Σ_{k=r}^{n} C(n,k)·aᵏ·bⁿ⁻ᵏ / (a + b)ⁿ` is at most 1/20, computed in integers as
`20 · binomTailNum n r a b ≤ (a + b)ⁿ` (`binomTest`). This is a one-sided test at the 95% level
of "precision is at most `p₀`". It passes exactly when the one-sided 95% Clopper–Pearson lower
bound on the precision is at least `p₀`, because the tail grows with `p₀`.

**The rule** (`thresholdCumulative`). Edges: 128, 160, 192, 224. For option `o` and edge `e`, let
`S(e)` be the validation answers whose most probable option is `o` with confidence at least `e`
(cumulative, not a bin). An edge is **tested** when `S(e)` holds at least 50 answers; a tested
edge **passes** when `binomTest` passes on `S(e)`. `need o` is the lowest tested edge that passes
and above which every tested edge also passes. Answers above an untested edge are still counted
in every lower edge's `S`. If no edge qualifies, `need o` is 257 and the gate never returns `o`
(`run_never`). The floor stays 128.

**Comparison precisions.**
- `pay`: `p₀` is the written policy's own `pay` precision on the same 4,096 validation examples,
  `R/P` with `a = R`, `b = P − R`. This is the quantity the safety criterion compares against
  (the policy's wrong payments over its own payments). The policy's precision on only the
  invoices the gate would pay is a different quantity and is not used, because the criterion
  does not measure it.
- `hold`: `p₀ = 80%` (`a = 4, b = 1`). `reject`: `p₀ = 90%` (`a = 9, b = 1`).

**Checking the bound.** `binomTailNum` is checked by `#guard` against exact values computed
independently (Python's `math.comb`, for example `binomTailNum 20 15 1 1 = 21700`, the count
behind `P(X ≥ 15) = 21700/2²⁰` for a fair coin), and one value is proved by `decide +kernel`.

**Seeds:** 301 to 308, fixed in advance and never run before. Held-out set (1,024 examples)
scored once per seed. v1's and v2's thresholds on the same models are reported beside v3's for
attribution.

**Success criteria, fixed in advance** (v2's, plus non-vacuity):
- **Safety:** the gated model's wrong-payment fraction is at most the policy's on at least 7 of
  8 seeds, and lower pooled over the 8 seeds.
- **Usefulness:** at least 512 of 1,024 decided on average, and at least half as many payments
  as the policy on average.
- **Non-vacuity:** the gate pays at least one invoice on at least 7 of 8 seeds.
- All three must hold.

**Deployed:** seed 301's selected model with its v3 thresholds. Whatever the result, this is the
last round.

## Protocol v3 results

Run once on seeds 301–308 (about 90 s per seed in the interpreter, in three `ix/light.sh`
jobs). Before the full run, the sweep script was smoke-tested on seed 999 (one recipe, 20
epochs), which is not a reported seed. `need` is `pay / hold`; `reject` was 257 on every seed.

| Seed | Selected: gain, lr, hidden, epochs | `need` | Model | Policy | Ceiling | Decided | Right among decided | Deferred | Model's `pay`s / wrong | Policy's `pay`s / wrong |
|---|---|---|---|---|---|---|---|---|---|---|
| 301 | 627, 8, 8, 80 | 257 / 128 | 901 | 881 | 913 | 337 | 302 | 687 | 0 / 0 | 629 / 63 (10.0%) |
| 302 | 256, 8, 8, 60 | 257 / 128 | 886 | 884 | 911 | 346 | 301 | 678 | 0 / 0 | 603 / 51 (8.5%) |
| 303 | 627, 8, 8, 100 | 257 / 128 | 907 | 911 | 920 | 313 | 279 | 711 | 0 / 0 | 646 / 51 (7.9%) |
| 304 | 627, 8, 16, 120 | 257 / 128 | 903 | 901 | 925 | 324 | 288 | 700 | 0 / 0 | 614 / 45 (7.3%) |
| 305 | 627, 8, 16, 40 | 257 / 128 | 896 | 880 | 910 | 292 | 255 | 732 | 0 / 0 | 666 / 62 (9.3%) |
| 306 | 627, 8, 16, 120 | 224 / 128 | 918 | 895 | 925 | 788 | 725 | 236 | 445 / 34 (7.6%) | 609 / 58 (9.5%) |
| 307 | 256, 8, 16, 100 | 257 / 128 | 922 | 893 | 930 | 337 | 307 | 687 | 0 / 0 | 630 / 50 (7.9%) |
| 308 | 256, 8, 16, 20 | 224 / 128 | 896 | 880 | 904 | 623 | 552 | 401 | 290 / 34 (11.7%) | 634 / 72 (11.4%) |
| Mean | | | 903.6 | 890.6 | 917.3 | 420.0 | 376.1 | 604.0 | 91.9 / 8.5 | 628.9 / 56.5 |

On the same models, v2's thresholds paid on 4 of 8 seeds and v1's on all 8 (v1: 5,100 payments,
515 wrong, 10.1%).

**Criteria.**
- **Safety: not met.** Per seed, the model's wrong-payment fraction is at most the policy's on 7
  of 8, but 6 of those pay nothing. Seed 308 passed the validation test at 224 and then paid
  wrongly 11.7% of the time on held-out data, against the policy's 11.4%. Pooled, the model's
  payments are 9.3% wrong (68 of 735) against the policy's 9.0% (452 of 5,031): not lower.
- **Usefulness: not met.** 420 decided on average (512 required); 91.9 payments against the 314
  required.
- **Non-vacuity: not met.** The gate pays on 2 of 8 seeds (7 required).

**v3 fails on all three criteria, and this was the last round.** Accuracy of the most probable
option, which the rule does not touch, is 903.6 against the policy's 890.6 and the ceiling's
917.3, at least the policy's on 7 of 8 seeds.

**Where the limit is: the model, inside the narrow room the label noise leaves.** Under this
generator the safest set of invoices a rule on the visible fields can pay, those without changed
bank details and without a hold condition, has a `pay` label about 92.9% of the time (fraud 1/32,
then 1/16 noise), against about 91% for the written policy's payments: 1.5 to 2 points of
headroom, and no profile is safer. That headroom is enough for the rule. An oracle gate that pays
exactly that set passes v3's validation test on 7 of 8 seeds (all but 301), and on the held-out
sets it pays 514 invoices per seed with 7.6% wrong (314 of 4,112) against the policy's 9.0%, safer
on all 8 seeds: it would meet every criterion. The trained models do not find that set. Their
most confident `pay` answers were no more precise than the policy's on validation (seed 301: 91.3%
at confidence 224 or more against the policy's 91.6%), and the deployed model is more confident
about paying a new vendor that changed bank details through the portal (247/256, fraudulent one
time in four) than about a routine invoice (246/256). The models learn the majority rule (pay
unless a hold condition) and do not rank the 1/32, 2/32 and 8/32 fraud risks among payable
invoices, which is the distinction safe paying needs. The rule is not the binding limit and the
label noise does not make the goal unreachable; the model, as trained here (squared error on
one-hot labels, at most 16 hidden units, 512 examples, no cost on wrong payments), is.


### The deployed model (seed 301)

`recipe` (gain 627, learning rate 8, 8 hidden units, 80 epochs: 2,560 SGD steps, 179
parameters) behind v3's thresholds. `#guard recipe.train task.spec == deployed` re-runs training
at every build of the test library and checks it bit for bit.

**Gate** (`gate` in `Invoice.lean`; a `#guard` checks it equals `gateCumulative deployed` on seed
301's 4,096 validation examples): floor 128; `pay` 257; `hold` 128; `reject` 257. On validation,
the model's `pay` answers at confidence 224 or more were right 1,721 times in 1,886 (91.3%), below
the written policy's 2,340 of 2,554 (91.6%), so no edge passes. Proved for every weight setting:

- `never_pays` and `never_rejects` (`run_never`, as 257 > 256);
- `pay_needs_confidence`, `low_confidence_defers`;
- `handle_never_pays`: the service pays no invoice.

**Card** (`card_certified`, `decide +kernel`): model 901, policy 881, Brier sum 57,559/256, 337
decided (all `hold`) with 302 right, no payments.

**Decisions**, each `by decide +kernel`:

- `routine_escalates`: the model answers `pay` at 246; the verdict is `defer`.
- `largeWithoutPO_holds`: `hold` at 199.
- `newVendorEmailBankChange_escalates`: the riskiest visible profile; the model answers `pay` at
  216; the verdict is `defer`.
- `newVendorPortalBankChange_escalates`: the written policy rejects; the model answers `pay` at
  **247**, more confidently than for the routine invoice (246), although under the generator this
  profile is fraudulent one time in four; the verdict is `defer`.

**Application** (`InvoiceApp.lean`). `handle` rejects an unapproved vendor and holds a total above
its purchase order in ordinary code, then calls `decision.run` on the invoice's profile and acts:

```lean
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

theorem handle_paid (m : Model) (inv : Invoice) (h : handle ⟨m, gate⟩ inv = .paid) :
    inv.vendorApproved = true ∧ inv.overPO = false ∧
      gate.need .pay ≤ (judge m inv.profile : Judgment Disposition).confidence
```

With the deployed gate `handle_never_pays` follows: no invoice is paid, whatever the weights.
The test file exercises `handle` with a model that says `pay` at full confidence for everything,
behind a gate that allows `pay` from 128: it pays an in-order invoice and still holds one over
its purchase order and rejects an unapproved vendor.

**What the gate does not say.** Confidence is the model's own number. An untrained model can be
fully confident: under `probabilitiesNonneg`, one positive output and the rest negative give
256/256 (on seed 2's initial weights the first model's gate paid every held-out invoice). The
theorems bound what a confident model can do; whether its confidence means anything is the
card's and the calibration table's question, and those are certified for the deployed weights
only.

## What is certified, and how

| Statement | Mechanism in this project | State here |
|---|---|---|
| Gate theorems, every weight setting | ordinary Lean proofs; an Ix `Check` claim each, as `deployedPublishSound` (5.2–5.6 s each in `README.md`) | proved in Lean |
| `handle_paid`, `handle_never_pays`, `never_pays`, `never_rejects`, every weight setting | same | proved in Lean |
| `trainingClaim : recipe.train task.spec = deployed` | an Ix `Eval` claim, or a chain of per-step claims joined by `train_eq_of_chain` (`IxAICore/Chain.lean`) | checked by `#guard` at build; not certified |
| `card_certified` | an Ix `Eval` claim, as the triage card | proved by `decide +kernel` |
| Decisions on concrete inputs | an Ix `Eval` or `Check` claim each, as the triage decision receipts | proved by `decide +kernel` |
| A two-step training run (`tiny_trained` in the tests) | as above | proved by `decide +kernel`, showing `train` over `Task.spec` reduces in the kernel |

Everything in `IxAIDecide` imports only `IxAICore` and `Init`, uses structural recursion over
`List` and `Nat`, and has no opaque functions or hashes, so it is in the form IxVM evaluates.

Certification steps, following `README.md`'s route for the triage model:

1. Copy `IxAIDecide` into `ix/bundle` beside `IxAICore` (Ix's toolchain is Lean 4.34.1) and
   `ix compile` it to Ixon.
2. Generate a `Certified_invoice.lean` with the training claim in chunks and the card, decision and
   gate theorems; `ixai certified` is hard-wired to `Triage.spec` and needs a generic variant.
3. Prove the training. The Aiur circuit and its refinement proofs (`train_refines`,
   `step_sound_deployed`) are specific to the triage full configuration's shapes (8 inputs, 16
   hidden, 11 outputs, batches of 20), so this model would go through IxVM chunks. Scaling the
   triage figure (659 s per 20-step chunk at 331 parameters and batches of 20) by parameters times
   batch size gives about 565 s per chunk here (355 parameters, batches of 16) and about 15 hours
   for 96 chunks: a projection, not a measurement. A smaller run is cheaper, or the Aiur circuit is generalized over shapes.
4. Prove the card, decisions and theorems as `Eval`/`Check` claims, aggregate, and compress to one
   PLONK certificate as for the tiny model.

## Where `IxAICore` was general enough, and where not

**Used unchanged:** `Fx`, `Rng`, the `Finite` class, `Spec`, `Model` and its forward pass, `train`,
`Config` (data, test, schedule, step), `probabilitiesNonneg`, `Chain`. `Spec` is general over
the example type, and labelling through `Labelled ι ω` lets the label depend on hidden variables
and noise while the model sees only the encoded input.

**Not general enough, and what this library does instead:**

- `Model.ask` and `card` use `probabilities`, which clamps at 1.0 and turns a confident margin into
  a tie (as `DecisionNext.lean` notes). `judge` and `decisionCard` use `probabilitiesNonneg`.
- `card` has no gate, no baseline and no count of costly mistakes. `DecisionCard` adds them.
- `Triage.Gate` and `Triage.act` are tied to formulas, one threshold and a decision procedure.
  `Gate ω` has a floor and a per-option need.
- `Spec.features` is `List Int` read by `Fx.ofInt`: integer features only. Encodings stay within
  0/1.
- `Config.init` draws uniform weights in ±16/256 regardless of fan-in, and training has no
  validation split or early stopping. `Recipe` (`Protocol.lean`) keeps the core's `Config`,
  schedule and step and replaces only the initialization (fan-in scaled, zero biases);
  `validationSet`, `Recipe.checkpoints` and `selectRecipe` add validation and early stopping.
- `Config.schedule` shuffles a list with `setAt`, quadratic in the training-set size: 2.3 s of
  every 10 s training run of seed 101's recipe in the interpreter. `IxAIDecide/Fast.lean`
  proves an array shuffle and an array schedule equal to the core's (`schedule_eq_scheduleArr`,
  `train_eq_trainArr`) and registers them with `@[csimp]`, so code compiled after it runs the fast
  versions while every statement names the core's. The shuffle and its proof are repeated from
  `IxAIData/Scorer.lean` rather than imported. Measured on seed 101's recipe: the schedule from
  2,263 ms to 63 ms, `recipe.train` from 7,958 ms to 5,782 ms, the test library from 10.9 s to
  8.5 s (this last figure also includes generating each data set once in the tests). The kernel still reduces the core's list shuffle.
- `IxAICore.Finite` carries no lawfulness proof; `Finite.Lawful` is a decidable check, and
  completeness of the listing is not checked.
- The Aiur circuit, the refinement proofs and the `ixai` code generators are tied to
  `Triage.spec`.

## Text

For text, an untrusted encoder (a language model's embedding, or an LLM's structured extraction
into a record) produces the features. The certified part would be a head and gate over them:

- The features are committed by hash, `h = BLAKE3(features)`, and the head's input is the
  committed vector. The receipt states: these weights, which are `train spec config` on a
  committed dataset of feature vectors and labels, given the vector with hash `h`, through this
  gate, returned this verdict; and the gate theorems hold for any vector.
- **Covered:** the head's training on the committed vectors, its card on committed held-out
  vectors, the gate's guarantees for every vector, and each decision given its vector.
- **Not covered:** that the vector is the encoder's output on this text, that the encoder is any
  particular model, that the training vectors came from real texts with honest labels, and
  whether the head's card transfers to new texts. The card measures the head against labels on
  vectors; its meaning for text rests entirely on the encoder and the labelling.
- The gate's guarantees survive an adversarial encoder: a crafted vector can make the model
  confident, but every verdict still respects the thresholds and the exact checks in code. That
  is the same guarantee as for an untrained model.
- Not built: BLAKE3 in kernel-evaluable form, real-valued features in the core, and a dataset of
  vectors.

## Decisions inside an agent harness: Lane

Lane is the Lean proving harness this project plans around (`docs/lane.md`). This section is
checked against the code of the fork at `~/repos/forks/lane`, branch `ix-addresses`, tip
`a97befb`; `file:line` references are to that commit unless a branch is named. Markers:
- no marker: what Lane's code does today;
- *(proposed)*: a rule, feature or record this design adds; Lane does not do it today;
- *(built)*: proposed here and implemented in this project (`IxAIDecide/LaneGate.lean`, checked);
- *(drafted)*: implemented on the fork's local branch `outcome-records` (`docs/lane.md`, change
  11) but not yet built or tested.

### What Lane records today

**Roles.** The server tells the main agent from a worker by the token on each request: the admin
token runs anything, a session token only the verbs in `workerRequestAllowed`
(`Lane/Server/Runtime.lean:434`), and what a worker's request stores is tagged `origin = worker`
(`Runtime.lean:474`). `MERGEBATCH`, `SUBMIT`, `DISCARD` and `CHANGE` are admin-only; `FINISH`,
`WRITE`, `VERIFYREC`, `ADDOB`/`RESOLVEOB` (obligations), `ACTIVITY` and `RESOLVE` are worker verbs.
There is still no OS isolation (change 9 not started), so a worker that reads `.lane/admin-token`
is the main agent.

**The change record at `finish`.** `finishLane` (`Lane/Server/Changes.lean:216-308`) runs in the
server and writes a `lane-change-v1` record as canonical JSON into the blob store: its address is
the BLAKE3 of its content, `.lane/blobs/<address>`, and `.lane/lanes/<n>/change` holds the address
(`Changes.lean:293-294`); the response also returns it as `change`. Lane IDs, timings and counts
of open obligations are in the response only. Fields, and who computes each:

| Field | Content | Computed by |
|---|---|---|
| `base`, `result` | Merkle roots of the tree the change applies to and of the finish checkpoint | server (`Changes.lean:262-269`) |
| `files[]` | `path`, `status` (`created`/`modified`/`deleted`), `before`/`after` blob addresses, `validation`, `unchecked` | server, from the lane's overlay (`Changes.lean:222-238`); but `validation` is the tag the writer sent with its last `WRITE`/`CREATE` (`Lane/Server/Storage.lean:379-391`), so `unchecked: true` means the writer said so (a worker needs `delegate --allow-unchecked` to say it), and `false` proves nothing |
| `declarations` | `null` if the finishing client sent no classification; else `reported_by` (`admin` or `worker`, the token's origin), `edits[]` (`path`, `declaration`, `kind`, `class`, `before`/`after` command-text addresses, and with `finish --admit` `ixon`, `ix_outcome`, `ix_check` or `ix_error`), `outside_declarations[]` (paths whose text outside declarations changed), `unclassified[]` (modules that did not parse) | **the finishing client** (`Lane/Prove/Validate.lean:266-288`, with `laneChangeContents`/`laneEdits`/`classifyEdit` in `Lane/Prove/Change.lean:12-102`). The server checks only that the claimed path→address map equals the lane's files (`Changes.lean:242-250`), that each class is a known one (`:179`), and drops edits on untouched paths (`:175`). It does not check that the edits describe the files. |
| `notes[]` | `target`, `message` of the lane's own notes | server, copying worker-written notes |
| `obligations[]` | `path`, `declaration`, `state` of proofs displaced by `theorem-to-sorry` | server, copying state that `ADDOB`/`RESOLVEOB` (worker verbs) maintain (`Lane/Server/Lanes.lean:89-108`) |
| `conflicts[]` | `conflict` address, `resolution` | server; every entry is resolved, because `finish` refuses a lane with an open conflict (`Changes.lean:219-220`) |
| `verify` | `worker[]`, `admin[]`: addresses of verify records stored against the `result` root | server (`Changes.lean:283-284`), listing records each origin stored |

The edit classes are `added`, `removed`, `proof_only` (a theorem's value), `body_only` (any other
declaration's value), `statement` (kind or header), `modifiers`, `layout` (whitespace only).
There is no count of sorries, no heartbeat use and no outcome in the record.

**`finish` does not check for sorries.** `finishLane` checks only the lane's state and the claim's
consistency. Sorries are seen by `lane sorries` (textual `sorry`/`admit` per declaration,
`Lane/Prove/Extraction.lean:379-402`), by `verify --no-sorry` (`has_placeholder`), and by
`submit --require no-sorry` (`sorryAx` among the collected axioms, `Validate.lean:82`).

**What `submit --require …` records.** `submitValidated` (`Lane/Prove/Analysis.lean:76-167`) runs
in the main agent's process. It recomputes the lane's edits there, against the recorded canonical
bases (`:107-109`), rebuilds the affected project (`:119`), and for every non-removed edit stores
a `lane-verify-v1` record with `checker: submit` (`Validate.lean:92-109`: `state` = the lane tree's
root, `path`, `source`, `declaration`, `policy` with the checks and the heartbeat **budget**,
`result` with `success`/`found`/`failed`, `toolchain`, `axioms`, `new_axioms`, `ix`) under
`.lane/lanes/<n>/verify-admin/<address>` (`Changes.lean:124-138`). What is not recorded:
- the outcome. A refused submission stores its failing per-declaration records (`Analysis.lean:142`
  runs before the refusal at `:153`), but the refusal and its code exist only in the command's
  stdout. A broken affected rebuild (`AFFECTED_PROJECT_INVALID`, `:125-131`) stores nothing. A
  successful one leaves the `submitted` marker and an activity `lane.submitted` whose detail is
  the comma-joined paths (`Lane/Server/Transactions.lean:84-86`);
- the edit class, which is in the stdout entry (`Analysis.lean:146`) but not in the stored record;
- any link to a change: records are keyed by the submitting lane's tree root, and the main agent
  usually submits its own lane, which has no change record, after merging workers' changes into it.
  The merge leaves activity `lane.merged` (detail: the target lane's ID) on the source and
  `lane.absorbed-source` on the target (`Transactions.lean:316-319`), not the change's address.

Without `--require` and without an `ix` binary, `submit` stores no record at all.

**Activity records.** `addActivity` (`Storage.lean:455-462`) writes
`.lane/lanes/<n>/activity/<k>/{kind,detail}`: a per-lane counter, a kind and a free-text detail,
with no time, no origin and no address. Kinds: `lane.created`, `lane.forked`, `lane.checkpointed`,
`lane.finished` (snapshot ID), `change.recorded` (change address), `lane.merged`,
`lane.absorbed-source`, `lane.absorbed`, `absorb.<kind>`, `lane.submitted`, `lane.discarded`,
`lane.garbage-collected`, `source.written`/`source.created`/`source.deleted` (path), `claim.created`/
`claim.released`, `note.created`, `verify.recorded` (`origin:address`), `conflict.recorded`,
`conflict.resolved`, `repository.relocated`. No `prove`, `probe` or other elaborating command
leaves activity, and `ACTIVITY` returns every lane of the repository to any caller, workers
included (`Lanes.lean:235-247`).

**`fuel.heartbeats`.** A per-process counter (`Lane/Prove/Elab.lean:23-24`) summed over every
command elaborated synchronously under `--max-heartbeats N`, plus what a `_validate` child reports
(`Validate.lean:211-213`). It is printed in the command's stdout as `fuel` (`Elab.lean:31-47`) and
reset only by `_validate` and per `prove-session` candidate (`Analysis.lean:691`). It is recorded
against nothing: not in verify records (which hold only the budget, `policy.max_heartbeats`), not
in change records, not in activity. A heartbeat count is attributable to one CLI invocation, by
whoever kept its stdout.

### What a model may decide

**For proofs the kernel is already the verifier.** A model cannot make a proof more correct, and
no decision below may accept one. A model adds value only around the kernel: which worker or
budget a goal gets, when to escalate, which finished lanes the main agent reviews first, and what
to show a worker. Every gate below has the shape of `handle`: exact rules in code first, then a
model that only routes.

| Jev's item | Decision point | Typed input | Options | Label | Exact rule, in code | Model's judgment | Gate property to prove |
|---|---|---|---|---|---|---|---|
| Guardrails on inputs and outputs | Main agent receiving a finished lane | `ChangeSummary`: counts from the change record (files by status, unchecked files, edits per class, added axioms, outside-declaration and unclassified modules, IxC rejections, notes, open obligations, resolved conflicts, verify records per origin) plus two counts the main agent measures (`merge --check-only` conflicts, `lane sorries`) and who classified the edits *(built)* | `mergeNow`, `review`, `discard`; the model's own options are only `clean`, `needsReview` *(built)* | whether the change, once merged, passed `submit --require …` with its declarations unedited; needs outcome records keyed by change address *(drafted on the fork branch `outcome-records`, not built or tested)* | edits not classified by the main agent, a statement, removed, modifier or body edit, an added axiom, outside-declaration text, an unclassified module, an unchecked file, any conflict, an open obligation, a sorry, or an IxC rejection rules out `mergeNow`; an empty change is discarded *(built)* | how likely the rest is to submit cleanly | proved in `LaneGate.lean` for every model and gate (below) |
| Checking an answer against the given material | A worker reports a proof accepted | — | — | — | the main agent's `submit --require …` rechecks it in its own process; a worker's `validation` tag and its verify records are self-reported | none: exact | — |
| Reviewing finished agent runs | Order of the main agent's review queue | change record, plus counts of activity kinds above (activity holds edits, claims, notes, verifies and conflicts, not elaboration attempts) | review priority `low`, `medium`, `high` *(proposed)* | whether review changed or discarded the change: merge records with the target's tree after the merge, then the submit outcome and the submitted tree, compared per declaration *(drafted on the fork branch, not built or tested)* | a `statement` edit is `high` *(proposed)* | priority among the rest | a `statement` edit is never ranked below `high` |
| Cascade | Who attempts a goal first | the goal as typed syntax *(proposed; goals as terms need change 10, not started)* | `cheapWorker`, `strongWorker` *(proposed)* | whether a cheap attempt ended with a proof accepted by `submit --require` within its heartbeat budget. Not recorded: attempts leave no activity, heartbeats are stdout only, and a submission's outcome is not stored on `a97befb` | the budget cap | whether the cheap attempt will succeed | `cascade_choose`: the strong worker runs only after the cheap stage deferred or failed; acceptance stays with the kernel |
| Model router | Which worker type, or none | as above | `cheapWorker`, `strongWorker`, `skip` *(proposed)* | as above | a goal whose statement address already has an accepted proof is not routed; needs the outcome cache of "Integration path" 5, future work | the route | `skip` is never returned for a goal the main agent marked required *(proposed)* |
| Suggesting a skill from a large fixed list | What a worker's prompt suggests | goal features | a fixed list of tactic families or Lane verbs *(proposed)* | the family the accepted proof used; `premises` gives an accepted proof's used constants, and the proof text is the edit's `after` blob | none | the suggestion | none needed: a suggestion cannot change acceptance |
| Choosing an assistant's next action | A worker's next verb | lane state: `sorries` count, last diagnostic class, heartbeats used | `prove`, `probe`, `extract-sorry`, `fork`, `finish` (all Lane verbs) | traces of finished lanes, which Lane does not keep (no activity for elaborating verbs); a reinforcement problem (`docs/rl.md`) | `finish` is withheld while `lane sorries` reports any. Lane's `finish` does not check this; a harness must *(proposed)* | the next verb | `finish` is never chosen while the lane has sorries |
| Function calling: each argument from a fixed list | Arguments of `prove` and `claim` | goal features | a heartbeat budget from a fixed ladder (`Fin k`) *(proposed)*; a claim target kind, one of `decl:`, `file:`, `module:`, `goal:`, `task:` | the smallest rung at which the proof was accepted; needs `fuel.heartbeats` stored with the attempt's outcome *(proposed)* | the ladder's top is the configured cap *(proposed)* | the rung | the budget never exceeds the cap (true by the option type) |
| Tool-call and data-leak checks | A worker reading the admin token or canonical sources | — | — | — | access control: change 9 or the caller's sandbox | none: a model must not be the guard; at most it flags activity for review | — |
| Simple memory | Reusing past results | goal address | — | — | an outcome cache keyed by `(env, goal, tactic, fuel)` addresses ("Integration path" 5, future) is exact | which past notes to show a worker *(proposed)* | none needed |

### The guardrail gate (`IxAIDecide/LaneGate.lean`)

The module is a prototype kept in the working directory: the library does not import it and it
is not part of the committed tree. It is checked on its own with `lake env lean`.

`ChangeSummary` has one field per count above. `Leaning` (`clean | needsReview`) is the model's
question; `gate` needs 230/256 for `clean` and has a floor of 128, set by hand because there is no
calibration data. `reasons s` lists every exact rule `s` trips, in a fixed order, and

```lean
def handle (d : Decision ChangeSummary Leaning) (s : ChangeSummary) : Outcome :=
  if s.changedFiles = 0 then .discard
  else
    match reasons s with
    | r :: _ => .review r
    | [] =>
      match d.run s with
      | .choose .clean => .mergeNow
      | .choose .needsReview | .defer =>
        let j := d.judge s
        .review (.model j.option j.confidence)
```

Proved for every `d` (every model and every gate) unless a gate is named:

| Theorem | Statement |
|---|---|
| `handle_mergeNow` | `handle d s = .mergeNow → s.changedFiles ≠ 0 ∧ reasons s = [] ∧ d.run s = .choose .clean` |
| `reasons_eq_nil` | `reasons s = []` gives every blocking count `= 0` and `s.classifiedBy = .main` |
| `mergeNow_no_statement`, `_no_added_axiom`, `_no_unchecked_file` | `0 < s.edits.statement` (resp. `addedAxioms`, `unchecked`) `→ handle d s ≠ .mergeNow` |
| `mergeNow_no_conflict` | `0 < s.resolvedConflicts ∨ 0 < s.mergeConflicts → handle d s ≠ .mergeNow` |
| `mergeNow_no_sorry` | `0 < s.sorries ∨ 0 < s.openObligations → handle d s ≠ .mergeNow` |
| `mergeNow_classified_by_main` | `handle d s = .mergeNow → s.classifiedBy = .main` |
| `handle_discard_iff` | `handle d s = .discard ↔ s.changedFiles = 0`: the model never causes a discard |
| `handle_exact` | if `s.changedFiles = 0 ∨ reasons s ≠ []`, then `handle d s = handle d' s` for any `d'`: the model is not consulted |
| `handle_mergeNow_confident` | behind `gate`, `mergeNow` implies `230 ≤ (judge m s).confidence` |

**Why the model never discards.** A wrong `discard` loses a worker's possibly correct proof and
the main agent may never look at it again; a wrong `review` costs only the main agent's time. So
the model chooses only between `mergeNow` and `review`, and discarding is the exact rule "the
change changes no file". A dataset could still teach the model which changes reviewers discard,
as a `needsReview` leaning with a reason; the action stays with the main agent.

**The trust point.** A delegated worker's change record has `reported_by: worker`, and those counts
are not evidence; `reasons` sends every summary not classified by the main agent to review
(`mergeNow_classified_by_main`). The main agent's process can re-derive the classification with
code the fork already has: `laneChangeContents lane` then `laneEdits` (`Change.lean:75-102`), the
same calls `finish` makes and that `submit --require` already makes in the main agent's process
(`Analysis.lean:108-109`, there against the recorded canonical bases instead of the fork base).
The admin token may read a finished lane's files and change bases (`READOPT`, `READCHANGEBASE`).
What is missing is a command that runs them for a finished lane and compares the result with the
record's `edits`; until it exists, `classifiedBy = .main` is honest only for lanes the main agent
finished itself (`reported_by: admin`). Equally, `sorries` and `mergeConflicts` must come from the
main agent's own `lane sorries` and `lane merge <main> <change> --check-only` (`Source.lean:888`),
and `unchecked = 0` is a worker's claim (above).

**Not done.** No model is trained and no data exists: labels need outcome records over real
lanes (`docs/lane.md`, "Outcome records"). The encoding (`Encode ChangeSummary`, 69 features:
the classifier one-hot and every count as a level 0, 1, 2, 3+) is fixed so that such a dataset can
be built. Tests: `IxAIDecide/LaneGateTest.lean`, constant models only.

## What does not work yet

- **No threshold rule yet makes the gate both safer than the written policy and useful.** v1's
  rule (90% precision averaged over all `pay` answers) paid wrongly 10.4% and 10.1% of the time
  on two sets of seeds, against the policy's 8.9% and 9.1%. v2's (policy precision plus one point
  in every bin) is safer (7.5%) but decides only 500 of 1,024 invoices on average and pays none on
  3 of 8 seeds. v3's (an exact one-sided binomial test on cumulative answers against the
  policy's precision, 4,096 validation examples) fails safety, usefulness and non-vacuity: the
  gate pays on 2 of 8 seeds, and those payments are not safer pooled. An oracle paying exactly
  the safest visible profiles meets every criterion, so the limit is the model's ranking of
  payable invoices by risk (see "Protocol v3 results").
- **The model trails the ceiling by about 12 of 1,024** on average; dead hidden units, the noisy
  Brier targets and 512 training examples are the likely causes (see "Protocol results").
- **Confidence is monotone but not calibrated**: underconfident by 7–12 points in the middle,
  overconfident by 2.6 points at the top. A recalibration step (a monotone map fitted on
  validation) would make thresholds readable as probabilities.
- **`reject` is never decided by the model.** Under this generator that is correct, not a defect.
- **The protocol's sweep is not part of the build**: it costs about 116 s per seed in the
  interpreter (8 seeds, 48 candidates each). Its definitions are in `Protocol.lean`; certifying
  "the deployed recipe is the one `selectRecipe` picks" would mean certifying all 48 runs.
- **Ordinal answers** are trained as unordered categories.
- **No `deriving Encode`**, no encoding of `Nat` beyond code-written buckets, and no text.
- **Training is not certified**, only checked at build. Generalizing `ixai certified` to any
  `Task.spec`, and the Aiur circuit to any shape, are the two routes.
- **Completeness of an option listing** is not checked; a missing option is never scored.

## What a second use case would need

Taking other examples from Jev's map, what this library lacks for each:

- **Claims or alert triage from descriptions**: text. Out of scope (see "Text").
- **Choosing a function-call argument from a fixed list**: the list is often per call (the open
  accounts of this customer), while `ω` is one fixed type. Needs an option mask per input: a gate
  that may only return options in a code-supplied set, with a theorem that it never returns one
  outside it.
- **Several judgments behind one action** (pay needs "not fraud" and "goods received"): the core
  `Spec` supports several answer groups, but `Task.spec` exposes one. Needs a task with several
  typed questions and a gate over their joint verdicts.
- **A real, committed dataset** instead of a generator: `Task` only has `sample`, and `Config.data`
  draws from it. Needs a task built from a committed list of examples (with the list's address in
  the claim) and a split proved disjoint, as `IxAIData` does for premise selection.
- **Human labels**: nothing here models label provenance; the card would be against those labels,
  with no kernel to confirm them.
- **Scoring on an ordered scale** (severity 1–5): an ordinal loss.
- **Costs that differ by mistake**: training is unweighted Brier; a mistaken `pay` costs the same
  as a mistaken `hold` during training, and only the gate makes it expensive.
- **Larger numbers of features or options**: training time in the interpreter grows with both;
  above a few hundred parameters the `#guard` check of training becomes slow and the IxVM route
  costly (see "What is certified").
- **Per-bin threshold rules and recalibration**, so a threshold on an irreversible option is a
  statement about every case it lets through, not an average.

## Build and tests

`ix/light.sh .toolchain/bin/lake build IxAIDecide IxAIDecideTest` (2026-11-20, after protocol
v3): all 18 jobs succeeded (the Lane gate prototype is not imported and is checked on its own). `InvoiceDeployed` took 32 s (the kernel-checked card),
`IxAIDecideTest` 8.5 s (it re-runs the deployed recipe's 2,560-step training), every other
module under 0.6 s. The tests cover: encodings and widths; `binomTailNum` against independently
computed exact tails, and one tail proved by `decide +kernel`; the dataset's label counts; the
two baselines on seeds 2026 and 301; the 4,096-example validation set extending the 1,024-example
one; `recipe.train task.spec == deployed`; checkpoints equal to the shorter recipes; the gate
equal to `gateCumulative` on validation; the kernel-checked two-step core training and the same
run through the `@[csimp]` fast path; `handle` with a constant `pay` model behind an open gate
and behind the deployed one; every held-out example for three weight settings (nothing below
128, never `pay`, never `reject`); a stricter gate changing no decision; a cascade; and the
service on concrete invoices, including the new-vendor, portal, bank-change invoice escalated at
247.
