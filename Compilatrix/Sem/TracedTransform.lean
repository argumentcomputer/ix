import Compilatrix.Sem.TracedSim
import Compilatrix.Sem.Transform

/-!
# Traced languages, refinement and passes

The traced counterparts of `Lang`, `Refines` and `Transform` (decision D-1):

- `TLang Env E I S`: programs `S` run on inputs `I` under an environment
  `Env`, performing events `E`, with a trace monotone semantics
  `run : S → I → Env → Nat → Traced E Val`. `Env`, `E` and `I` are out
  parameters: a program type fixes them, and two languages refine each
  other only at the same environment and event types. `Env` is the
  environment the IO design note chooses (an oracle, answering from the
  events so far or from its own state; how it refuses is its choice).
- `Lang.lift`: every pure language is a traced one, ignoring the
  environment and performing no event. Phase 1 levels use it at
  `Env := Unit`, `E := Empty` (a low-priority instance), so their passes
  are stated in the traced shape without new proofs (`Refines.ofPure`,
  `Transform.lift`).
- `TRefines s t`: on every input and environment, the traced behaviour of
  `t` refines that of `s` up to equal observations. `TRefines.backward`
  (a returned value with its trace), `trace_prefix` (every target trace is
  a source trace), `live` (every source trace is a target trace), `safe`
  and `diverges` are the shapes of `compile_sound_io`, `compile_live_io`
  and `compile_safe` (effects note §4.5.1), each with its stuck-source
  and resource-failure escapes.
- `TTransform S T`: a certificate-taking pass correct for every
  certificate, with `comp`, `comp_correct` and `compile_correct` as for
  `Transform`.
-/

namespace Compilatrix.Sem

/-- A traced language: programs `S` run on inputs `I` under an environment
`Env`, performing events `E`, with values observed as `Obs`. -/
class TLang (Env E I : outParam Type) (S : Type) where
  /-- The values a run returns. -/
  Val : Type
  /-- The clocked, traced semantics of a program on an input under an
  environment. -/
  run : S → I → Env → Nat → Traced E Val
  /-- Trace monotonicity of every run. -/
  mono : ∀ s i o, TraceMono (run s i o)
  /-- First-order observation of a value, if it has one. -/
  obs : Val → Option Obs

namespace TLang

variable {Env E I S T : Type} [TLang Env E I S] [TLang Env E I T]

/-- Two values, of possibly different languages, observe the same. -/
def ObsEq (v : Val S) (w : Val T) : Prop := obs v = obs w

/-- The traced behaviour of a program on an input under an environment. -/
noncomputable def tbehaviour (s : S) (i : I) (o : Env) : TBehaviour E (Val S) :=
  Sem.tbehaviour (run s i o)

end TLang

/-- A pure language as a traced one, at any environment and event types:
the run ignores the environment and performs no event. -/
@[reducible] def Lang.lift (Env E : Type) (I S : Type) [Lang I S] : TLang Env E I S where
  Val := Lang.Val S
  run s i _ k := Traced.lift (Lang.run s i k)
  mono s i _ := TraceMono.ofPure (Lang.mono s i)
  obs := Lang.obs

/-- Phase 1 levels are traced languages with `Env := Unit` and
`E := Empty`. -/
instance (priority := low) Lang.instTLang {I S : Type} [Lang I S] : TLang Unit Empty I S :=
  Lang.lift Unit Empty I S

section

variable {Env E I S T U : Type} [TLang Env E I S] [TLang Env E I T] [TLang Env E I U]

/-- `t` refines `s`: on every input and environment, every traced
behaviour of `s` is matched by `t` up to equal observations; the target may
fail for a resource after a trace the source performs, and a stuck source
imposes nothing. -/
def TRefines (s : S) (t : T) : Prop :=
  ∀ i o, TBehaviour.Refines TLang.ObsEq (TLang.tbehaviour s i o) (TLang.tbehaviour t i o)

namespace TRefines

theorem refl (s : S) : TRefines s s := fun _ _ => .refl (R := TLang.ObsEq) (fun _ => rfl) _

theorem trans {s : S} {t : T} {u : U} (h₁ : TRefines s t) (h₂ : TRefines t u) :
    TRefines s u := fun i o =>
  ((h₁ i o).trans (h₂ i o)).mono fun _ _ ⟨_, h, h'⟩ => h.trans h'

/-- A traced simulation on every input, for a value relation that keeps
observations, gives refinement. -/
theorem of_sim {s : S} {t : T} {R : TLang.Val S → TLang.Val T → Prop}
    (hR : ∀ v w, R v w → TLang.ObsEq v w)
    (hsim : ∀ i, ∃ f, TSim R f (TLang.run s i) (TLang.run t i)) : TRefines s t := fun i o => by
  obtain ⟨f, hs⟩ := hsim i
  exact (hs.refines (TLang.mono s i) (TLang.mono t i) o).mono hR

/-- The shape of `compile_sound_io`: a value the target returns comes, with
the same trace, from a source value with the same observation, or the
source is stuck. -/
theorem backward {s : S} {t : T} (h : TRefines s t) {i : I} {o : Env} {k : Nat}
    {w : TLang.Val T} {tr : List E} (ht : TLang.run t i o k = ⟨.ok w, tr⟩) :
    (∃ k' v, TLang.run s i o k' = ⟨.ok v, tr⟩ ∧ TLang.ObsEq v w) ∨
      ∃ k', (TLang.run s i o k').result = .stuck := by
  have hb : TLang.tbehaviour t i o = .ends ⟨.ok w, tr⟩ :=
    (tbehaviour_eq_ends_iff (TLang.mono t i o)).2 ⟨nofun, k, ht⟩
  have href := h i o
  rw [hb] at href
  generalize hsb : TLang.tbehaviour s i o = b at href
  cases href with
  | ends h' =>
    rcases h'.of_ok rfl with ⟨v, hv, hvw, htr⟩ | hst
    · obtain ⟨_, k', hk'⟩ := (tbehaviour_eq_ends_iff (TLang.mono s i o)).1 hsb
      refine .inl ⟨k', v, ?_, hvw⟩
      rw [hk']
      exact Traced.ext hv htr
    · obtain ⟨_, k', hk'⟩ := (tbehaviour_eq_ends_iff (TLang.mono s i o)).1 hsb
      exact .inr ⟨k', by rw [hk']; exact hst⟩
  | stuck hst =>
    obtain ⟨_, k', hk'⟩ := (tbehaviour_eq_ends_iff (TLang.mono s i o)).1 hsb
    exact .inr ⟨k', by rw [hk']; exact hst⟩
  | resource _ hf _ => cases hf

/-- Trace safety: every trace the target performs is performed by the
source, unless the source is stuck. -/
theorem trace_prefix {s : S} {t : T} (h : TRefines s t) (i : I) (o : Env) (k : Nat) :
    (∃ k', (TLang.run t i o k).trace <+: (TLang.run s i o k').trace) ∨
      ∃ k', (TLang.run s i o k').result = .stuck := by
  have ht : (TLang.tbehaviour t i o).Performs (TLang.run t i o k).trace :=
    (performs_tbehaviour (TLang.mono t i o)).2 ⟨k, List.prefix_refl _⟩
  rcases (h i o).performs ht with hp | hst
  · exact .inl ((performs_tbehaviour (TLang.mono s i o)).1 hp)
  · exact .inr ((stuck_tbehaviour (TLang.mono s i o)).1 hst)

/-- The shape of `compile_live_io`: every trace the source performs is
performed by the target, unless the target fails for a resource or the
source is stuck. A source that keeps performing events keeps its target
doing so. -/
theorem live {s : S} {t : T} (h : TRefines s t) (i : I) (o : Env) (k : Nat) :
    (∃ k', (TLang.run s i o k).trace <+: (TLang.run t i o k').trace) ∨
      (∃ k' failure, (TLang.run t i o k').result = .resource failure) ∨
      ∃ k', (TLang.run s i o k').result = .stuck := by
  have hs : (TLang.tbehaviour s i o).Performs (TLang.run s i o k).trace :=
    (performs_tbehaviour (TLang.mono s i o)).2 ⟨k, List.prefix_refl _⟩
  rcases (h i o).live hs with hp | ⟨u, failure, hu, hf⟩ | hst
  · exact .inl ((performs_tbehaviour (TLang.mono t i o)).1 hp)
  · obtain ⟨_, k', hk'⟩ := (tbehaviour_eq_ends_iff (TLang.mono t i o)).1 hu
    exact .inr (.inl ⟨k', failure, by rw [hk']; exact hf⟩)
  · exact .inr (.inr ((stuck_tbehaviour (TLang.mono s i o)).1 hst))

/-- The shape of `compile_safe`: if the source goes wrong at no clock, the
target goes wrong at no clock. -/
theorem safe {s : S} {t : T} (h : TRefines s t) {i : I} {o : Env}
    (hs : ∀ k, ¬ (TLang.run s i o k).result.GoesWrong) (k : Nat) :
    ¬ (TLang.run t i o k).result.GoesWrong := by
  intro ht
  have hb : (TLang.tbehaviour t i o).GoesWrong :=
    (goesWrong_tbehaviour (TLang.mono t i o)).2 ⟨k, ht⟩
  obtain ⟨k', hk'⟩ := (goesWrong_tbehaviour (TLang.mono s i o)).1 ((h i o).goesWrong hb)
  exact hs k' hk'

/-- Divergence is preserved: a source that times out at every clock has a
target that times out at every clock or fails for a resource. -/
theorem diverges {s : S} {t : T} (h : TRefines s t) {i : I} {o : Env}
    (hs : ∀ k, (TLang.run s i o k).result = .timeout) :
    (∀ k, (TLang.run t i o k).result = .timeout) ∨
      ∃ k failure, (TLang.run t i o k).result = .resource failure := by
  have href := h i o
  unfold TLang.tbehaviour at href
  rw [tbehaviour_of_forall_timeout hs] at href
  by_cases hex : ∃ k, (TLang.run t i o k).result ≠ .timeout
  · obtain ⟨k, hk⟩ := hex
    rw [tbehaviour_of_ne_timeout (TLang.mono t i o) hk] at href
    cases href with
    | resource failure hf _ => exact .inr ⟨k, failure, hf⟩
  · exact .inl fun k => Classical.byContradiction fun hk => hex ⟨k, hk⟩

end TRefines

end

/-- Pure refinement is traced refinement of the lifted languages
(`Env := Unit`, `E := Empty`). -/
theorem Refines.ofPure {I S T : Type} [Lang I S] [Lang I T] {s : S} {t : T}
    (h : Refines s t) : TRefines s t := fun i _ =>
  TBehaviour.Refines.ofPure (Lang.mono s i) (Lang.mono t i) (h i)

/-- A pass from `S` to `T` over traced languages that reads a certificate
(`Unit` if it has none) and is correct for every certificate. -/
structure TTransform {Env E I : Type} (S T : Type) [TLang Env E I S] [TLang Env E I T] where
  name : String
  /-- Untrusted certificate data the pass reads. -/
  Cert : Type := Unit
  /-- The well-formedness the pass needs. -/
  pre : S → Prop
  run : S → Cert → Except String T
  /-- The well-formedness the pass establishes. -/
  post : T → Prop
  correct : ∀ s c t, pre s → run s c = .ok t → post t ∧ TRefines s t

namespace TTransform

variable {Env E I S T U : Type} [TLang Env E I S] [TLang Env E I T] [TLang Env E I U]

/-- Sequential composition: the certificate is a pair, and the first pass's
postcondition must give the second's precondition. -/
def comp (t₁ : TTransform S T) (t₂ : TTransform T U) (h : ∀ t, t₁.post t → t₂.pre t) :
    TTransform S U where
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

theorem comp_run (t₁ : TTransform S T) (t₂ : TTransform T U) (h : ∀ t, t₁.post t → t₂.pre t)
    (s : S) (c₁ : t₁.Cert) (c₂ : t₂.Cert) :
    (t₁.comp t₂ h).run s (c₁, c₂) = (t₁.run s c₁).bind fun t => t₂.run t c₂ := rfl

/-- Correctness of a composed pass, for every pair of certificates. -/
theorem comp_correct (t₁ : TTransform S T) (t₂ : TTransform T U)
    (h : ∀ t, t₁.post t → t₂.pre t) {s : S} {c₁ : t₁.Cert} {c₂ : t₂.Cert} {u : U}
    (hs : t₁.pre s) (hu : (t₁.comp t₂ h).run s (c₁, c₂) = .ok u) :
    t₂.post u ∧ TRefines s u :=
  (t₁.comp t₂ h).correct s (c₁, c₂) u hs hu

/-- Run a pass on the certificate an untrusted producer proposes. -/
def compile (t : TTransform S T) (produce : S → t.Cert) (s : S) : Except String T :=
  t.run s (produce s)

/-- Whatever the producer, a successful run is correct. -/
theorem compile_correct (t : TTransform S T) (produce : S → t.Cert) {s : S} {u : T}
    (hs : t.pre s) (hu : t.compile produce s = .ok u) : t.post u ∧ TRefines s u :=
  t.correct s (produce s) u hs hu

end TTransform

/-- A pure pass as a pass over the lifted languages (`Env := Unit`,
`E := Empty`), with the same run and certificate. -/
def Transform.lift {I S T : Type} [Lang I S] [Lang I T] (t : Transform S T) : TTransform S T where
  name := t.name
  Cert := t.Cert
  pre := t.pre
  run := t.run
  post := t.post
  correct s c u hs hu := (t.correct s c u hs hu).imp_right Refines.ofPure

theorem Transform.lift_run {I S T : Type} [Lang I S] [Lang I T] (t : Transform S T) :
    t.lift.run = t.run := rfl

end Compilatrix.Sem
