import IxAICore.Decision
import IxAICore.Formula

/-!
# Formula triage: a specified decision model behind a certified gate

The model answers three typed questions about a formula:

* `valid : Bool`: is it true under every assignment?
* `head : Head`: which atom, if any, is its conclusion?
* `coverage : Coverage`: how many of the 8 assignments satisfy it?

Each is decided by a procedure in this file, so training labels are computed.

The deployed system acts through `Triage.act`. The model only *routes*: a formula the model is
confident about is sent to the decision procedure, and is published only if the procedure
confirms it. `act_publish_sound` and `act_publish_confident` hold for every model, trained or not,
so no choice of weights can make the system publish a false formula, and nothing is published
without the model's stated confidence. Training can change how much work the system saves; it
cannot change what the system is allowed to do.
-/

namespace IxAICore

inductive Head where
  | p0 | p1 | p2 | top | none
  deriving DecidableEq, Repr, Inhabited

instance : Finite Head := ⟨[.p0, .p1, .p2, .top, .none], fun
  | .p0 => 0 | .p1 => 1 | .p2 => 2 | .top => 3 | .none => 4⟩

inductive Coverage where
  /-- No satisfying assignment. -/
  | never
  /-- One to three of eight. -/
  | rarely
  /-- Four to seven of eight. -/
  | mostly
  /-- All eight. -/
  | always
  deriving DecidableEq, Repr, Inhabited

instance : Finite Coverage := ⟨[.never, .rarely, .mostly, .always], fun
  | .never => 0 | .rarely => 1 | .mostly => 2 | .always => 3⟩

namespace Triage

def headOf (f : Formula) : Head :=
  match f.head with
  | .atom 0 => .p0
  | .atom 1 => .p1
  | .atom 2 => .p2
  | .top => .top
  | _ => .none

def coverageOf (f : Formula) : Coverage :=
  let m := f.models
  if m == 0 then .never else if m < 4 then .rarely else if m < 8 then .mostly else .always

def validQ : Question Formula Bool := ⟨"valid", Formula.valid⟩
def headQ : Question Formula Head := ⟨"head", headOf⟩
def coverageQ : Question Formula Coverage := ⟨"coverage", coverageOf⟩

def spec : Spec Formula :=
  { name := "formula-triage"
    features := Formula.features
    numFeatures := 8
    slots := [validQ.slot, headQ.slot, coverageQ.slot]
    sample := Formula.gen 3 }

def askValid (m : Model) (f : Formula) : Answer Bool := m.ask spec 0 f
def askHead (m : Model) (f : Formula) : Answer Head := m.ask spec 1 f
def askCoverage (m : Model) (f : Formula) : Answer Coverage := m.ask spec 2 f

inductive Action where
  /-- Publish as a valid formula. Only after the decision procedure confirms it. -/
  | publish
  /-- Confident the formula is valid, but the procedure refuted it: the model was wrong. -/
  | refuted
  /-- Not confident enough: leave it for a slower process. -/
  | defer
  deriving DecidableEq, Repr

structure Gate where
  /-- Minimum probability of `valid = true`, in units of `1/256`, before the procedure runs. -/
  threshold : Int
  deriving DecidableEq, Repr

/-- The probability the model assigns to `valid = true`. -/
def confidence (m : Model) (f : Formula) : Int := (getD (askValid m f).probs 1 Fx.zero).raw

def act (g : Gate) (m : Model) (f : Formula) : Action :=
  if confidence m f ≥ g.threshold then
    if f.valid then .publish else .refuted
  else .defer

/-- Whatever the weights, a published formula is valid. -/
theorem act_publish_sound (g : Gate) (m : Model) (f : Formula) (h : act g m f = .publish) :
    f.valid = true := by
  unfold act at h
  split at h
  · split at h
    · assumption
    · cases h
  · cases h

/-- Whatever the weights, nothing is published without the model's stated confidence. -/
theorem act_publish_confident (g : Gate) (m : Model) (f : Formula) (h : act g m f = .publish) :
    confidence m f ≥ g.threshold := by
  unfold act at h
  split at h
  · assumption
  · cases h

/-- The procedure runs only on formulas the model is confident about, so a deferred formula
costs nothing. -/
theorem act_defer_iff (g : Gate) (m : Model) (f : Formula) :
    act g m f = .defer ↔ confidence m f < g.threshold := by
  unfold act
  constructor
  · intro h
    split at h
    · split at h <;> cases h
    · exact Int.lt_of_not_ge (by assumption)
  · intro h
    rw [if_neg (Int.not_le.mpr h)]

/-- Outcomes of running the gate over a set of formulas. -/
structure Report where
  published : Nat
  refuted : Nat
  deferred : Nat
  /-- Valid formulas left unpublished: the work the model failed to save. -/
  missed : Nat
  deriving DecidableEq, Repr

def report (g : Gate) (m : Model) (fs : List Formula) : Report :=
  let acts := fs.map fun f => (act g m f, f.valid)
  { published := (acts.filter (·.1 == .publish)).length
    refuted := (acts.filter (·.1 == .refuted)).length
    deferred := (acts.filter (·.1 == .defer)).length
    missed := (acts.filter fun (a, v) => v && a != .publish).length }

end Triage

end IxAICore
