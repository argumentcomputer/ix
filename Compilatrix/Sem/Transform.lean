import Compilatrix.Sem.Simulation

/-!
# Languages, refinement and certificate-taking passes

The pass interface of design note `plans/x86-v2/00-conventions.md` (MetaCoq's
`Transform.t`, with a certificate):

- `Lang I S`: programs `S` run on inputs `I` under a monotone clocked
  semantics, with values observed as first-order `Obs`. `I` is an out
  parameter: a program type fixes its input type, and M2.7 chooses one input
  type shared by every level. (The class is `Lang`, not `Sem`, because
  `Sem.Sem` would clash with the namespace.)
- `Refines s t`: on every input, the behaviour of `t` refines that of `s` up
  to equal observations; the target may add resource failures, and a stuck
  source imposes nothing. `Refines.backward` and `Refines.safe` have the
  shapes of `compile_sound` and `compile_safe` (roadmap §1.1).
- `Transform I S T`: a pass that reads an untrusted certificate and is
  correct for every certificate; `Transform.comp` composes passes and
  `Transform.comp_correct` their correctness. `Transform.compile` runs a pass
  on the certificate of an arbitrary producer (the produce/recheck split,
  D17): correctness never depends on the producer.

A pass proves `Refines` per input through a clocked simulation
(`Refines.of_sim`); no clock map reaches this level.
-/

namespace Compilatrix.Sem

/-- A language: programs `S` run on inputs `I` with a monotone clocked
semantics whose values are observed as `Obs`. -/
class Lang (I : outParam Type) (S : Type) where
  /-- The values a run returns. -/
  Val : Type
  /-- The clocked semantics of a program on an input. -/
  run : S → I → Nat → Result Val
  /-- Clock monotonicity of every run. -/
  mono : ∀ s i, ClockMono (run s i)
  /-- First-order observation of a value, if it has one. -/
  obs : Val → Option Obs

namespace Lang

variable {I S T : Type} [Lang I S] [Lang I T]

/-- Two values, of possibly different languages, observe the same. -/
def ObsEq (v : Val S) (w : Val T) : Prop := obs v = obs w

/-- The behaviour of a program on an input. -/
noncomputable def behaviour (s : S) (i : I) : Behaviour (Val S) := Sem.behaviour (run s i)

end Lang

open Lang

variable {I S T U : Type} [Lang I S] [Lang I T] [Lang I U]

/-- `t` refines `s`: on every input, every behaviour of `s` is matched by
`t` up to equal observations, with extra target resource failures allowed. -/
def Refines (s : S) (t : T) : Prop :=
  ∀ i, Behaviour.Refines ObsEq (Lang.behaviour s i) (Lang.behaviour t i)

namespace Refines

theorem refl (s : S) : Refines s s := fun _ => .refl fun _ => rfl

theorem trans {s : S} {t : T} {u : U} (h₁ : Refines s t) (h₂ : Refines t u) :
    Refines s u := fun i =>
  ((h₁ i).trans (h₂ i)).mono fun _ _ ⟨_, h, h'⟩ => h.trans h'

/-- A clocked simulation on every input, for a value relation that keeps
observations, gives refinement. -/
theorem of_sim {s : S} {t : T} {R : Val S → Val T → Prop}
    (hR : ∀ v w, R v w → ObsEq v w)
    (hsim : ∀ i, ∃ f, Sim R f (Lang.run s i) (Lang.run t i)) : Refines s t := fun i => by
  obtain ⟨f, hs⟩ := hsim i
  exact (hs.refines (Lang.mono s i) (Lang.mono t i)).mono hR

/-- The shape of `compile_sound`: a target value comes from a source value
with the same observation, or the source is stuck. -/
theorem backward {s : S} {t : T} (h : Refines s t) {i : I} {k : Nat} {w : Val T}
    (ht : Lang.run t i k = .ok w) :
    (∃ k' v, Lang.run s i k' = .ok v ∧ ObsEq v w) ∨ ∃ k', Lang.run s i k' = .stuck := by
  have hb : Lang.behaviour t i = .terminates w :=
    (behaviour_eq_terminates_iff (Lang.mono t i)).2 ⟨k, ht⟩
  have href := h i
  rw [hb] at href
  rcases href.of_terminates with ⟨v, hv, hvw⟩ | hv
  · obtain ⟨k', hk'⟩ := (behaviour_eq_terminates_iff (Lang.mono s i)).1 hv
    exact .inl ⟨k', v, hk', hvw⟩
  · exact .inr ((behaviour_eq_stuck_iff (Lang.mono s i)).1 hv)

/-- The shape of `compile_safe`: if the source goes wrong at no clock, the
target goes wrong at no clock; it returns, times out or runs out of a
resource. -/
theorem safe {s : S} {t : T} (h : Refines s t) {i : I}
    (hs : ∀ k, ¬ (Lang.run s i k).GoesWrong) (k : Nat) : ¬ (Lang.run t i k).GoesWrong := by
  intro ht
  have hk : Lang.run t i k ≠ .timeout := fun h' => by simp [h'] at ht
  have hb : (Lang.behaviour t i).GoesWrong := by
    unfold Lang.behaviour
    rw [behaviour_of_ne_timeout (Lang.mono t i) hk]
    exact Behaviour.goesWrong_toBehaviour.2 ht
  have hsb := (h i).goesWrong hb
  unfold Lang.behaviour at hsb
  by_cases hex : ∃ k', Lang.run s i k' ≠ .timeout
  · obtain ⟨k', hk'⟩ := hex
    rw [behaviour_of_ne_timeout (Lang.mono s i) hk'] at hsb
    exact hs k' (Behaviour.goesWrong_toBehaviour.1 hsb)
  · rw [behaviour_of_forall_timeout fun k' =>
      Classical.byContradiction fun hk' => hex ⟨k', hk'⟩] at hsb
    exact hsb

end Refines

/-- A pass from `S` to `T` that reads a certificate (`Unit` if it has none)
and is correct for every certificate. `run` is the kernel-evaluable pass
(style P re-runs it, style V checks the certificate and applies it). -/
structure Transform (I S T : Type) [Lang I S] [Lang I T] where
  name : String
  /-- Untrusted certificate data the pass reads. -/
  Cert : Type := Unit
  /-- The well-formedness the pass needs. -/
  pre : S → Prop
  run : S → Cert → Except String T
  /-- The well-formedness the pass establishes. -/
  post : T → Prop
  correct : ∀ s c t, pre s → run s c = .ok t → post t ∧ Refines s t

namespace Transform

/-- Sequential composition: the certificate is a pair, and the first pass's
postcondition must give the second's precondition. -/
def comp (t₁ : Transform I S T) (t₂ : Transform I T U) (h : ∀ t, t₁.post t → t₂.pre t) :
    Transform I S U where
  name := t₁.name ++ " ; " ++ t₂.name
  Cert := t₁.Cert × t₂.Cert
  pre := t₁.pre
  run s c := (t₁.run s c.1).bind fun t => t₂.run t c.2
  post := t₂.post
  correct s c u hs hu := by
    cases h₁ : t₁.run s c.1 with
    | error e => simp [h₁, Except.bind] at hu
    | ok t =>
      simp only [h₁, Except.bind] at hu
      obtain ⟨hpost, hst⟩ := t₁.correct s c.1 t hs h₁
      obtain ⟨hpost', htu⟩ := t₂.correct t c.2 u (h t hpost) hu
      exact ⟨hpost', hst.trans htu⟩

theorem comp_run (t₁ : Transform I S T) (t₂ : Transform I T U) (h : ∀ t, t₁.post t → t₂.pre t)
    (s : S) (c₁ : t₁.Cert) (c₂ : t₂.Cert) :
    (t₁.comp t₂ h).run s (c₁, c₂) = (t₁.run s c₁).bind fun t => t₂.run t c₂ := rfl

/-- Correctness of a composed pass, for every pair of certificates. -/
theorem comp_correct (t₁ : Transform I S T) (t₂ : Transform I T U)
    (h : ∀ t, t₁.post t → t₂.pre t) {s : S} {c₁ : t₁.Cert} {c₂ : t₂.Cert} {u : U}
    (hs : t₁.pre s) (hu : (t₁.comp t₂ h).run s (c₁, c₂) = .ok u) :
    t₂.post u ∧ Refines s u :=
  (t₁.comp t₂ h).correct s (c₁, c₂) u hs hu

/-- Run a pass on the certificate an untrusted producer proposes. -/
def compile (t : Transform I S T) (produce : S → t.Cert) (s : S) : Except String T :=
  t.run s (produce s)

/-- Whatever the producer, a successful run is correct. -/
theorem compile_correct (t : Transform I S T) (produce : S → t.Cert) {s : S} {u : T}
    (hs : t.pre s) (hu : t.compile produce s = .ok u) : t.post u ∧ Refines s u :=
  t.correct s (produce s) u hs hu

end Transform

end Compilatrix.Sem
