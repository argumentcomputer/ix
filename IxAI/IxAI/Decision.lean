import IxAICommon.Hash

/-!
# Typed decisions and certified gates

Decision APIs (Jev, OpenAI and Gemini Decisions) return a distribution over a closed set of
answers instead of text. Here distributions are in parts per thousand, as an integer-exact model
readout would give them. A gate maps an answer to an action, and its safety property is proved
for every possible model output, so model errors are bounded by construction rather than by the
model being right.
-/

namespace IxAI

structure Question where
  instructions : String
  options : List String
  deriving Repr

instance : Enc Question := ⟨fun b q => Enc.enc (Enc.enc b q.instructions) q.options⟩

/-- Questions are content-addressed so shared definitions (a standard compliance question, say)
have one identity across organizations. -/
def Question.addr (q : Question) : Digest := digestOf "question" q

structure ChoiceAnswer where
  /-- Per-option probability in parts per thousand. -/
  permille : List Nat
  deriving Repr

def ChoiceAnswer.prob (a : ChoiceAnswer) (i : Nat) : Nat := a.permille.getD i 0

def ChoiceAnswer.top (a : ChoiceAnswer) : Nat := a.permille.foldl max 0

/-- Concentration, as TypeSafe defines confidence for a choice: 0 for uniform, 1000 for certain. -/
def ChoiceAnswer.concentration (a : ChoiceAnswer) : Nat :=
  let n := a.permille.length
  if n ≤ 1 then 1000
  else
    let base := 1000 / n
    (a.top - base) * 1000 / (1000 - base)

inductive Action where
  | approve
  | escalate
  | reject
  deriving Repr, DecidableEq

structure Gate where
  approveOption : Nat
  approveAt : Nat
  rejectBelow : Nat

def Gate.decide (g : Gate) (a : ChoiceAnswer) : Action :=
  if g.approveAt ≤ a.prob g.approveOption then .approve
  else if a.prob g.approveOption < g.rejectBelow then .reject
  else .escalate

/-- Whatever the model outputs, approval only happens at or above the threshold. -/
theorem Gate.approve_sound (g : Gate) (a : ChoiceAnswer) (h : g.decide a = .approve) :
    g.approveAt ≤ a.prob g.approveOption := by
  unfold Gate.decide at h
  split at h
  · assumption
  · split at h <;> cases h

/-- Raising the approval threshold never turns an escalation or rejection into an approval. -/
theorem Gate.approve_monotone (g : Gate) (a : ChoiceAnswer) (t : Nat) (ht : g.approveAt ≤ t)
    (h : ({ g with approveAt := t } : Gate).decide a = .approve) : g.decide a = .approve := by
  have := Gate.approve_sound _ _ h
  unfold Gate.decide
  simp only at this
  simp [Nat.le_trans ht this]

end IxAI
