import IxAICore.Decision
import IxAICore.DecisionNext
import IxAIDecide.Encode

/-!
# Certified decisions: task, model, gate

A **task** names an input type `ι`, an option type `ω` and a seeded generator of labelled
examples. `Task.spec` turns it into an `IxAICore.Spec` with one answer group, so the core's
`Config`, `train`, `Config.data` and `Config.test` apply unchanged: training a decision model is
`IxAICore.train t.spec config`, a pure function of the task and the configuration.

The example type is `Labelled ι ω`, an input together with its specified option. The generator
draws both, so a label may depend on things the input does not show (a hidden variable, or
noise), while `Task.spec` lets the model see only `Encode.encode input`.

A **judgment** is what the model says about one input: its most probable option and that
option's probability. A **gate** turns a judgment into a `Verdict`: an option, or `defer`. A gate
has a floor below which it always defers, and a separate minimum confidence for each option, so
an option that is hard to undo can demand more confidence than one that is easy to undo.

The theorems in this file quantify over every judgment, hence over every model and every input:
they hold before training, after training, and for weights nobody trained. Training changes how
often the gate decides, never what it may decide.
-/

namespace IxAIDecide

open IxAICore

/-- An input with the option the task's specification assigns to it. -/
structure Labelled (ι ω : Type) where
  input : ι
  label : ω
  deriving Repr, DecidableEq, Inhabited

/-- A decision task: what is asked, over which inputs, with which options, and how labelled
examples are generated from a seed. -/
structure Task (ι ω : Type) where
  name : String
  sample : Rng → Labelled ι ω × Rng

/-- The task as a core specification: the model sees the encoded input and answers one question,
the option. -/
def Task.spec {ι ω : Type} [Encode ι] [Finite ω] (t : Task ι ω) : Spec (Labelled ι ω) :=
  { name := t.name
    features := fun e => Encode.encode e.input
    numFeatures := Encode.width ι
    slots := [⟨"option", arity ω, fun e => Finite.index e.label⟩]
    sample := t.sample }

/-- The model's output for each option, in the options' order. -/
def scores {ι : Type} [Encode ι] (m : Model) (x : ι) : List Fx :=
  m.outputs ((Encode.encode x).map Fx.ofInt)

/-- What the model says about one input. -/
structure Judgment (ω : Type) where
  /-- The most probable option. -/
  option : ω
  /-- Its probability, in units of `1/256`. -/
  confidence : Int
  /-- Every option's probability, in the options' order, in units of `1/256`. -/
  probs : List Fx
  deriving Repr

/-- Ask the model. Probabilities are `IxAICore.probabilitiesNonneg` of the outputs, so a margin
above `1.0` is kept rather than clamped away. -/
def judge {ι ω : Type} [Encode ι] [Finite ω] [Inhabited ω] (m : Model) (x : ι) : Judgment ω :=
  let os := scores m x
  let i := argmax os
  let ps := probabilitiesNonneg os
  ⟨getD (Finite.all : List ω) i default, (getD ps i Fx.zero).raw, ps⟩

/-- A gate's answer: an option, or send the case to someone else. -/
inductive Verdict (ω : Type) where
  | choose (o : ω)
  | defer
  deriving Repr, DecidableEq, Inhabited

/-- Confidence thresholds, in units of `1/256`. -/
structure Gate (ω : Type) where
  /-- Below this confidence every case is deferred, whatever the option. -/
  floor : Int
  /-- The confidence each option needs before the gate may return it. -/
  need : ω → Int

def Gate.apply {ω : Type} (g : Gate ω) (j : Judgment ω) : Verdict ω :=
  if g.floor ≤ j.confidence ∧ g.need j.option ≤ j.confidence then .choose j.option else .defer

/-! ## Gate theorems, for every judgment -/

section
variable {ω : Type} (g : Gate ω) (j : Judgment ω)

/-- An option is returned only at the confidence that option demands. -/
theorem apply_choose_need {o : ω} (h : g.apply j = .choose o) : g.need o ≤ j.confidence := by
  unfold Gate.apply at h
  split at h
  · cases h; rename_i hc; exact hc.2
  · cases h

/-- Nothing is returned below the floor. -/
theorem apply_choose_floor {o : ω} (h : g.apply j = .choose o) : g.floor ≤ j.confidence := by
  unfold Gate.apply at h
  split at h
  · rename_i hc; exact hc.1
  · cases h

/-- Below the floor the answer is `defer`. -/
theorem apply_defer_of_lt_floor (h : j.confidence < g.floor) : g.apply j = .defer := by
  unfold Gate.apply
  rw [ite_eq_right (fun hc => absurd hc.1 (Int.not_le.mpr h))]

/-- The gate never substitutes an option: it returns the model's own answer or defers. -/
theorem apply_choose_eq {o : ω} (h : g.apply j = .choose o) : o = j.option := by
  unfold Gate.apply at h
  split at h
  · cases h; rfl
  · cases h

/-- Exactly when the gate defers. -/
theorem apply_defer_iff :
    g.apply j = .defer ↔ j.confidence < g.floor ∨ j.confidence < g.need j.option := by
  unfold Gate.apply
  constructor
  · intro h
    split at h
    · cases h
    · rename_i hc
      by_cases hf : g.floor ≤ j.confidence
      · exact Or.inr (Int.not_le.mp fun hn => hc ⟨hf, hn⟩)
      · exact Or.inl (Int.not_le.mp hf)
  · intro h
    rw [ite_eq_right]
    intro ⟨hf, hn⟩
    cases h with
    | inl h => exact absurd hf (Int.not_le.mpr h)
    | inr h => exact absurd hn (Int.not_le.mpr h)

end

/-- `g'` is at least as strict as `g` everywhere. -/
def Gate.Stricter {ω : Type} (g' g : Gate ω) : Prop :=
  g.floor ≤ g'.floor ∧ ∀ o, g.need o ≤ g'.need o

/-- Raising thresholds can only turn decisions into deferrals, never change a decision. -/
theorem apply_stricter {ω : Type} {g g' : Gate ω} (hs : g'.Stricter g) (j : Judgment ω) {o : ω}
    (h : g'.apply j = .choose o) : g.apply j = .choose o := by
  have ho := apply_choose_eq g' j h
  have hf := apply_choose_floor g' j h
  have hn := apply_choose_need g' j h
  subst ho
  unfold Gate.apply
  rw [ite_eq_left ⟨Int.le_trans hs.1 hf, Int.le_trans (hs.2 _) hn⟩]

/-! ## Deployed decisions -/

/-- A deployed decision: weights and the gate they act through. -/
structure Decision (ι ω : Type) where
  model : Model
  gate : Gate ω

def Decision.judge {ι ω : Type} [Encode ι] [Finite ω] [Inhabited ω] (d : Decision ι ω) (x : ι) :
    Judgment ω :=
  IxAIDecide.judge d.model x

def Decision.run {ι ω : Type} [Encode ι] [Finite ω] [Inhabited ω] (d : Decision ι ω) (x : ι) :
    Verdict ω :=
  d.gate.apply (d.judge x)

section
variable {ι ω : Type} [Encode ι] [Finite ω] [Inhabited ω] (d : Decision ι ω) (x : ι)

/-- For any weights: an option is returned only at the confidence it demands. -/
theorem run_choose_need {o : ω} (h : d.run x = .choose o) :
    d.gate.need o ≤ (d.judge x).confidence :=
  apply_choose_need _ _ h

/-- For any weights: below the floor the answer is `defer`. -/
theorem run_defer_of_lt_floor (h : (d.judge x).confidence < d.gate.floor) : d.run x = .defer :=
  apply_defer_of_lt_floor _ _ h

/-- For any weights: a returned option is the model's most probable one. -/
theorem run_choose_eq {o : ω} (h : d.run x = .choose o) : o = (d.judge x).option :=
  apply_choose_eq _ _ h

end

/-! ## Confidence is at most one -/

theorem relu_nonneg (a : Fx) : 0 ≤ (Fx.relu a).raw := by
  unfold Fx.relu
  split
  · omega
  · simp [Fx.zero]

theorem sumRaw_nonneg (l : List Fx) (hl : ∀ y ∈ l, 0 ≤ y.raw) : 0 ≤ Fx.sumRaw l := by
  induction l with
  | nil => simp [Fx.sumRaw]
  | cons b bs ih =>
    simp only [Fx.sumRaw]
    have := hl b (by simp)
    have := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    omega

theorem le_sumRaw (l : List Fx) (hl : ∀ y ∈ l, 0 ≤ y.raw) : ∀ x ∈ l, x.raw ≤ Fx.sumRaw l := by
  induction l with
  | nil => intro x hx; cases hx
  | cons a as ih =>
    intro x hx
    have hs : 0 ≤ Fx.sumRaw as := sumRaw_nonneg as (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    simp only [Fx.sumRaw]
    rcases List.mem_cons.mp hx with h | h
    · subst h; omega
    · have := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) x h
      have := hl a (by simp)
      omega

/-- Every probability `probabilitiesNonneg` outputs is at most `256/256`. -/
theorem probabilitiesNonneg_le (os : List Fx) : ∀ p ∈ probabilitiesNonneg os, p.raw ≤ 256 := by
  intro p hp
  unfold probabilitiesNonneg at hp
  simp only at hp
  split at hp
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hp
    exact Int.ediv_le_self _ (by decide)
  · rename_i ht
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    have hnn : ∀ y ∈ os.map Fx.relu, 0 ≤ y.raw := by
      intro y hy
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hy
      exact relu_nonneg a
    have hle := le_sumRaw _ hnn c hc
    have hpos : 0 < Fx.sumRaw (os.map Fx.relu) := by omega
    show c.raw * 256 / Fx.sumRaw (os.map Fx.relu) ≤ 256
    exact Int.ediv_le_of_le_mul hpos (by
      calc c.raw * 256 ≤ Fx.sumRaw (os.map Fx.relu) * 256 :=
            Int.mul_le_mul_of_nonneg_right hle (by decide)
        _ = 256 * Fx.sumRaw (os.map Fx.relu) := Int.mul_comm _ _)

theorem getD_le {l : List Fx} (h : ∀ p ∈ l, p.raw ≤ 256) (i : Nat) (d : Fx)
    (hd : d.raw ≤ 256) :
    (getD l i d).raw ≤ 256 := by
  induction l generalizing i with
  | nil => simpa [getD] using hd
  | cons a as ih =>
    cases i with
    | zero => exact h a (by simp)
    | succ i => exact ih (fun p hp => h p (List.mem_cons_of_mem _ hp)) i

/-- Whatever the weights and input, a judgment's confidence is at most `256`. A threshold above
256 therefore rules its option out. -/
theorem judge_confidence_le {ι ω : Type} [Encode ι] [Finite ω] [Inhabited ω] (m : Model)
    (x : ι) :
    (judge m x : Judgment ω).confidence ≤ 256 :=
  getD_le (probabilitiesNonneg_le _) _ _ (by decide)

/-- An option whose threshold exceeds 256 is never returned, for any weights. -/
theorem run_never {ι ω : Type} [Encode ι] [Finite ω] [Inhabited ω] (d : Decision ι ω) (x : ι)
    (o : ω) (ho : 256 < d.gate.need o) : d.run x ≠ .choose o := by
  intro h
  have := run_choose_need d x h
  have := judge_confidence_le (ω := ω) d.model x
  simp only [Decision.judge] at *
  omega
/-! ## Cascades -/

/-- Ask `first`; if it defers, ask `second`. The usual shape is a cheap model first and a costlier
one (or a person) second. -/
def cascade {ι ω : Type} (first second : ι → Verdict ω) (x : ι) : Verdict ω :=
  match first x with
  | .choose o => .choose o
  | .defer => second x

/-- A cascade's answer is the first stage's, or the second's after the first deferred. So any
property both stages guarantee for a returned option, the cascade guarantees too. -/
theorem cascade_choose {ι ω : Type} (first second : ι → Verdict ω) (x : ι) {o : ω}
    (h : cascade first second x = .choose o) :
    first x = .choose o ∨ (first x = .defer ∧ second x = .choose o) := by
  unfold cascade at h
  split at h
  · rename_i hf; cases h; exact Or.inl hf
  · rename_i hf; exact Or.inr ⟨hf, h⟩

end IxAIDecide
