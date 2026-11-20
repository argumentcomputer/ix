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

**Model.** 8 hidden units, 179 parameters, learning rate 8/256 per summed batch gradient, batches
of 16, 80 epochs (2,560 SGD steps). The weights are written out in `InvoiceDeployed.lean` as
`deployed`; `#guard train task.spec config == deployed` re-runs training at every build of the
test library and checks the result bit for bit (about 10 s in the interpreter). Same seed, same
weights.

**Card** (`card_certified`, proved by kernel evaluation in about 30 s; held-out set, 1,024
examples):

| | Correct | |
|---|---|---|
| Model's most probable option | 912 (89.1%) | Brier sum 54,299/256, 0.21 per example |
| Written policy | 893 (87.2%) | |
| Best rule on visible fields (ceiling) | 918 (89.6%) | |

The model's most probable option agrees with the ceiling rule on 1,010 of 1,024. Where the
written policy and the ceiling disagree (52 cases: a new vendor changing bank details outside
email), the policy is right 13 times and the model 38; the gate defers 28 of the 52.

| Behind the gate | |
|---|---|
| Decided | 737 (72%); 679 right (92.1%). The written policy is right on 659 of the same 737. |
| Deferred to a person | 287; the model's leaning was right on 233 |
| `pay` returned | 441, of which 36 (8.2%) had another label. The written policy pays 659, of which 63 (9.6%) had another label. |
| `reject` returned | 0. The model's largest reject confidence on the held-out set stays below the 192 that `reject` needs, so every likely fraud goes to a person. |

**Against the two baselines, in one table** (deployed model, seed 2026, 1,024 held-out
examples):

| | Model | Written policy | Ceiling rule |
|---|---|---|---|
| Correct overall | 912 | 893 | 918 |
| Correct where the two rules disagree (52) | 38 | 13 | 38 |
| Correct on the 737 cases the gate decided | 679 (model behind the gate) | 659 | — |
| `pay` answers / of which another label | 441 / 36 (gated) | 659 / 63 | 693 / 76 |
| Can defer | yes, 287 cases | no | no |

Across seeds (same configuration; the ceiling and the policy do not depend on training):

| Seed | Model | Written policy | Ceiling |
|---|---|---|---|
| 2026 (deployed) | 912 | 893 | 918 |
| 1 | 906 | 890 | 913 |
| 2 | 842 | 878 | 909 |
| 3 | 852 | 903 | 918 |
| Mean | 878 | 891 | 914.5 |

Reading: on the deployed seed the model beats the written policy by 19 cases of 1,024 and comes
within 6 of the ceiling, and all of its advantage is in the 52 cases where the policy's fraud rule
is wrong. Averaged over four seeds it is 13 cases **worse** than the written policy. So the rule
matches or beats the model on this task as trained here; the model's gain is not robust.

**This result depends on the seed.** With the same configuration and seeds 1, 2 and 3, the model
was correct on 906, 842 and 852 against the written policy's 890, 878 and 903: it beat the policy
on two seeds of four and lost clearly on two. The learning rate and epoch count were chosen by
looking at seed 2026's held-out score, so that seed's margin is optimistic. Plain SGD on this
fixed-point MLP is unstable at these sizes (one configuration with 16 hidden units reached only
644). The honest summary: on this task a written rule is about as accurate as the model; the
model's contribution is a confidence the gate can act on, which a rule does not have.

**Gate.** `pay` needs 230/256, `reject` 192/256, `hold` 128/256, and below 128 every case goes to
a person. Proved for every weight setting (`InvoiceDeployed.lean`):

- `pay_needs_confidence`: `pay` is returned only at confidence at least 230.
- `reject_needs_confidence`: `reject` only at at least 192.
- `low_confidence_defers`: below 128 the verdict is `defer`.

**Decisions**, each `by decide +kernel` over the deployed weights:

- `routine_pays`: an established vendor, portal, amount level 2, with a purchase order: `pay` at
  242/256.
- `largeWithoutPO_holds`: the same at amount level 6 without a purchase order: `hold` at 157.
- `newVendorEmailBankChange_escalates`: the model's answer is `reject` at 158, short of 192, so the
  verdict is `defer`.
- `newVendorPortalBankChange_escalates`: the written policy rejects; the model leans to `pay` at
  183; the verdict is `defer`.

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
      230 ≤ (judge m inv.profile : Judgment Disposition).confidence
```

The test file exercises it with a model that says `pay` at full confidence for everything: it
pays an in-order invoice and still holds one over its purchase order and rejects an unapproved
vendor.

**What the gate does not say.** Confidence is the model's own number. An untrained model can be
fully confident: under `probabilitiesNonneg`, one positive output and the rest negative give
256/256. On seed 2's initial weights the gate paid every held-out invoice. The theorems bound
what a confident model can do; whether its confidence means anything is the card's question, and
the card is certified for the deployed weights only.

## What is certified, and how

| Statement | Mechanism in this project | State here |
|---|---|---|
| Gate theorems, every weight setting | ordinary Lean proofs; an Ix `Check` claim each, as `deployedPublishSound` (5.2–5.6 s each in `README.md`) | proved in Lean |
| `handle_paid`, every weight setting | same | proved in Lean |
| `trainingClaim : train task.spec config = deployed` | an Ix `Eval` claim, or a chain of per-step claims joined by `train_eq_of_chain` (`IxAICore/Chain.lean`) | checked by `#guard` at build; not certified |
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
   batch size gives about 280 s per chunk here and about 10 hours for 128 chunks: a projection,
   not a measurement. A smaller run is cheaper, or the Aiur circuit is generalized over shapes.
4. Prove the card, decisions and theorems as `Eval`/`Check` claims, aggregate, and compress to one
   PLONK certificate as for the tiny model.

## Where `IxAICore` was general enough, and where not

**Used unchanged:** `Fx`, `Rng`, the `Finite` class, `Spec`, `Model` and its forward pass, `train`,
`Config` (data, test, schedule, init), `probabilitiesNonneg`, `Chain`. `Spec` is general over
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
  validation split, early stopping or learning-rate schedule. The seed sensitivity above is
  likely partly this.
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

Lane is the Lean proving harness this project plans around. This section rests only on
`docs/lane.md` and `docs/provable-decisions.md`; Lane's code was not read. Markers:
- no marker: the behaviour is described in `docs/lane.md` (section named in brackets);
- *(proposed)*: a rule, feature or record this design would add; Lane does not do it today;
- *(inferred)*: an assumption about Lane that `docs/lane.md` does not state.

What Lane does, per `docs/lane.md`:
- A server owns lanes; the main agent holds the admin token and can `new`, `fork`, `delegate`,
  `revoke`, `merge`, `submit`; workers are restricted to observe, edit, claim, note and finish
  verbs on their own lane, and `finish` freezes the lane ("Roles and capabilities").
- In this project's fork, `finish` stores a change record with per-declaration edits classified
  as added, removed, proof_only, body_only, statement, modifiers or layout, plus notes,
  obligations, verify-record addresses, files marked unchecked, and conflicts. The edits are
  classified **by the finishing client** and labelled `reported_by` ("Implemented in fork", 2 and
  6). A gate must therefore not trust a worker-reported classification; its exact rules must
  re-derive the classification in the main agent's process *(proposed)*.
- `submit --require no-sorry,no-new-axioms,no-unsafe,no-native,standard-axioms` rechecks every
  changed declaration in the main agent's process, and `--require ix-checked` refuses unless
  IxC accepts each ("Implemented in fork", 3 and 4).
- `--max-heartbeats N` reports `fuel.heartbeats` deterministically (8). Wall-clock times must not
  feed a label ("Proposed changes", 8).
- No OS isolation: a worker can read the admin token and canonical sources; containment (change
  9) is not started ("What Lane does not do"; "Implemented in fork").

**For proofs the kernel is already the verifier.** A model cannot make a proof more correct, and
no decision below may accept one. A model adds value only around the kernel: which worker or
budget a goal gets, when to escalate, which finished lanes the main agent reviews first, and what
to show a worker. Every gate below has the shape of `handle`: exact rules in code first, then a
model that only routes.

| Jev's item | Decision point | Typed input | Options | Label | Exact rule, in code | Model's judgment | Gate property to prove |
|---|---|---|---|---|---|---|---|
| Guardrails on inputs and outputs | Main agent receiving a finished lane | the change record: counts of edits per class, unchecked files, conflicts, which verify records exist | `mergeNow`, `review`, `discard` *(proposed)* | whether `submit --require …` later succeeded on that change without further edits *(inferred: needs submit outcomes recorded against change addresses)* | a `statement` edit, an added axiom, an unchecked file, an open conflict or a failed policy record rules out `mergeNow`, with the classification recomputed by the main agent *(proposed)* | how likely the rest is to submit cleanly | `mergeNow` is never returned for a change that alters a statement, adds an axiom or contains an unchecked file, whatever the model outputs |
| Checking an answer against the given material | A worker reports a proof accepted | — | — | — | the main agent's `submit --require …` rechecks it; a worker's "validated" is self-reported and does not count ("What Lane does not do") | none: exact | — |
| Reviewing finished agent runs | Order of the main agent's review queue | change record, plus counts from the lane's append-only activity records *(inferred: which kinds of activity are recorded is not listed)* and `fuel.heartbeats` | review priority `low`, `medium`, `high` *(proposed)* | whether the main agent's review changed or discarded the lane *(inferred: not recorded today)* | a `statement` edit is `high` *(proposed)* | priority among the rest | a `statement` edit is never ranked below `high` |
| Cascade | Who attempts a goal first | the goal as typed syntax: head symbol, size, binders, modules touched *(proposed; goals as terms need change 10, not started)* | `cheapWorker`, `strongWorker` *(proposed)* | whether a cheap attempt ended with a proof accepted by `submit --require` within its heartbeat budget *(inferred: per-attempt outcomes are not described as recorded)* | the budget cap | whether the cheap attempt will succeed | `cascade_choose`: the strong worker runs only after the cheap stage deferred or failed; acceptance stays with the kernel |
| Model router | Which worker type, or none | as above | `cheapWorker`, `strongWorker`, `skip` *(proposed)* | as above | a goal whose statement address already has an accepted proof is not routed; this needs the outcome cache of "Integration path" 5, which is future work | the route | `skip` is never returned for a goal the main agent marked required *(proposed)* |
| Suggesting a skill from a large fixed list | What a worker's prompt suggests | goal features | a fixed list of tactic families or Lane verbs *(proposed)* | the family the accepted proof used; `premises` gives an accepted proof's used constants, and the proof text is in the lane's files | none | the suggestion | none needed: a suggestion cannot change acceptance. `docs/decision-models.md` ranks tactic choice second among its candidates and leaves its value open |
| Choosing an assistant's next action | A worker's next verb | lane state: `sorries` count, last diagnostic class, heartbeats used | `prove`, `probe`, `extract-sorry`, `fork`, `finish` (all Lane verbs) | traces of finished lanes; credit assignment makes it a reinforcement problem (`docs/rl.md`) | `finish` is withheld while `sorries` reports any *(proposed: `docs/lane.md` does not say `finish` checks this)* | the next verb | `finish` is never chosen while the lane has sorries |
| Function calling: each argument from a fixed list | Arguments of `prove` and `claim` | goal features | a heartbeat budget from a fixed ladder (`Fin k`) *(proposed)*; a claim target kind, one of `decl:`, `file:`, `module:`, `goal:`, `task:` | the smallest rung at which the proof was accepted, from `fuel.heartbeats` | the ladder's top is the configured cap *(proposed)* | the rung | the budget never exceeds the cap (true by the option type) |
| Tool-call and data-leak checks | A worker reading the admin token or canonical sources | — | — | — | access control: change 9 or the caller's sandbox | none: a model must not be the guard; at most it flags activity for review | — |
| Simple memory | Reusing past results | goal address | — | — | an outcome cache keyed by `(env, goal, tactic, fuel)` addresses ("Integration path" 5, future) is exact | which past notes to show a worker, a scoring decision *(proposed)* | none needed |

Labels here come from Lane's records and the kernel, so they are exact in the sense of
`docs/provable-decisions.md`, provided the outcomes marked *(inferred)* are actually recorded.

What the library lacks for this: inputs from Lean syntax (a goal or declaration as typed
features, which needs change 10 or Ix's elaborator), a dataset of finished lanes with their change
records and outcomes, and gates whose exact rules read a change record. The first property worth
building is the guardrail row, proved the same way as `handle_paid`.

## What does not work yet

- **Training is unstable across seeds**, and the model does not reliably beat a written rule on
  the use case. Next: fan-in-scaled initialization and a validation split chosen before looking at
  the test set, both as new `Config`-like definitions beside the core rather than edits to it.
- **The gate never rejects** on the held-out set: the model's reject confidence tops out below
  192. Either the threshold or the model's calibration is wrong for that option; the card shows
  it, and the threshold should be set from a certified calibration table rather than by hand.
- **No calibration measure** in `DecisionCard` yet; the core's `calibrationRaw` uses the clamping
  probabilities. Add one over `probabilitiesNonneg`.
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
- **Calibration on the card**, to set thresholds from evidence rather than by hand.

## Build and tests

`ix/light.sh .toolchain/bin/lake build IxAIDecide IxAIDecideTest` (2026-11-20): all 15 jobs
succeeded, no warnings. `InvoiceDeployed` took 29 s (the kernel-checked card), `IxAIDecideTest`
9.7 s (re-running the 2,560-step training), every other module under 0.4 s. The tests cover: encodings and
widths, the dataset's label counts, the two baselines, `train task.spec config == deployed`, the
initial weights deciding nothing, the kernel-checked two-step training, the gate on a constant
`pay` model, the gate's thresholds on every held-out example for three different weight settings,
a stricter gate changing no decision, a cascade, and the service on concrete invoices.
