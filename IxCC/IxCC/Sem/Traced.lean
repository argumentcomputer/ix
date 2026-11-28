import IxCC.Sem.Simulation

/-!
# Traced outcomes and their behaviours

The statement shapes that let IO arrive without restating any simulation
theorem (decision D-1). A traced semantics reads an environment and returns, at every clock,
a `Traced E α`: the clocked `Result` together with the events performed so
far, on timeout too.

The environment and the event type `E` stay abstract. Phase 1 levels lift
their pure evaluators (`Traced.lift`, `TraceMono.ofPure`): the environment
is `Unit`, `E` is `Empty` and every trace is `[]`. A later IO design
chooses the concrete events (for example an operation with first-order
arguments and response), the oracle, and how an oracle refusal ends a run.
None of them needs a new `Result` constructor: a refusal can be a response
the program sees (a total oracle), or a final event after which the run
performs nothing more; both leave `Traced.Refines` and `TSim` as stated.

- `TraceMono c`: an outcome other than `timeout` is, with its trace, the
  outcome at every larger clock, and the trace at a clock is a prefix of the
  trace at every larger clock.
- `Traced.Refines R s t`: per-clock refinement. The source is stuck (no
  claim); or the traces are equal and the results are related by
  `Result.Refines`; or the target fails for a resource after a prefix of
  the source's trace.
- `tbehaviour c`: the run ends with an outcome and its whole trace, or every
  clock times out and the run performs the prefixes of its traces. A
  divergence with an infinite trace is the least upper bound of that chain
  (CakeML's `build_lprefix_lub`), so no infinite object is needed.
- `TBehaviour.Refines R b₁ b₂`: behaviour refinement up to resource
  failure: ended runs refine as `Traced.Refines`, diverging runs perform the
  same finite traces, a stuck source imposes nothing, and the target may
  fail for a resource after a trace the source performs.

Behaviours are Prop-level (`tbehaviour` decides an unbounded quantifier),
never evaluated.
-/

namespace IxCC.Sem

/-- A clocked outcome with the events performed so far, on timeout too. -/
@[ext] structure Traced (E α : Type) where
  result : Result α
  trace : List E
  deriving DecidableEq, Repr

namespace Traced

variable {E α β γ : Type}

/-- A pure outcome as a traced one: no event. -/
def lift (r : Result α) : Traced E α := ⟨r, []⟩

@[simp] theorem lift_result (r : Result α) : (lift r : Traced E α).result = r := rfl
@[simp] theorem lift_trace (r : Result α) : (lift r : Traced E α).trace = [] := rfl

/-- Per-clock refinement of traced outcomes: `t` matches `s` up to `R` on
values. -/
inductive Refines (R : α → β → Prop) : Traced E α → Traced E β → Prop
  /-- A stuck source imposes nothing. -/
  | stuck {s : Traced E α} {t : Traced E β} : s.result = .stuck → Refines R s t
  /-- The same trace, with results related as `Result.Refines` relates them. -/
  | result {s : Traced E α} {t : Traced E β} : s.trace = t.trace →
      Result.Refines R s.result t.result → Refines R s t
  /-- A target resource failure after a prefix of the source's trace. -/
  | resource {s : Traced E α} {t : Traced E β} (failure : Resource) :
      t.result = .resource failure → t.trace <+: s.trace → Refines R s t

namespace Refines

variable {R : α → β → Prop}

theorem refl {R : α → α → Prop} (h : ∀ v, R v v) (s : Traced E α) : Refines R s s :=
  .result rfl (.refl h)

theorem mono {R' : α → β → Prop} (hR : ∀ v w, R v w → R' v w) {s : Traced E α}
    {t : Traced E β} (h : Refines R s t) : Refines R' s t := by
  cases h with
  | stuck hs => exact .stuck hs
  | result htr hr => exact .result htr (hr.mono hR)
  | resource failure ht hp => exact .resource failure ht hp

/-- Pure per-clock refinement lifts, for every event type. -/
theorem lift {r : Result α} {r' : Result β} (h : Result.Refines R r r') :
    Refines R (Traced.lift r : Traced E α) (Traced.lift r') :=
  .result rfl h

/-- Refinement of lifted outcomes is pure refinement. -/
theorem toPure {r : Result α} {r' : Result β}
    (h : Refines R (Traced.lift r : Traced E α) (Traced.lift r')) : Result.Refines R r r' := by
  cases h with
  | stuck hs => simp only [lift_result] at hs; rw [hs]; exact .stuck
  | result _ hr => exact hr
  | resource failure ht _ => simp only [lift_result] at ht; rw [ht]; exact .resource failure

/-- A target timeout matches only a source timeout or a stuck source. -/
theorem of_timeout {s : Traced E α} {t : Traced E β} (h : Refines R s t)
    (ht : t.result = .timeout) : s.result = .timeout ∨ s.result = .stuck := by
  cases h with
  | stuck hs => exact .inr hs
  | result _ hr => rw [ht] at hr; exact hr.of_timeout
  | resource failure ht' _ => rw [ht] at ht'; cases ht'

/-- A source resource failure is matched only by a target resource failure
after a prefix of its trace. -/
theorem of_resource {s : Traced E α} {t : Traced E β} {failure : Resource} (h : Refines R s t)
    (hs : s.result = .resource failure) :
    ∃ failure', t.result = .resource failure' ∧ t.trace <+: s.trace := by
  cases h with
  | stuck hs' => rw [hs] at hs'; cases hs'
  | result htr hr =>
    rw [hs] at hr
    obtain ⟨failure', h'⟩ := hr.of_resource
    exact ⟨failure', h', htr ▸ List.prefix_refl _⟩
  | resource failure' ht hp => exact ⟨failure', ht, hp⟩

/-- A target value matches only a related source value with the same trace,
or a stuck source. -/
theorem of_ok {s : Traced E α} {t : Traced E β} {w : β} (h : Refines R s t)
    (ht : t.result = .ok w) :
    (∃ v, s.result = .ok v ∧ R v w ∧ s.trace = t.trace) ∨ s.result = .stuck := by
  cases h with
  | stuck hs => exact .inr hs
  | result htr hr =>
    rw [ht] at hr
    rcases hr.of_ok with ⟨v, hv, hvw⟩ | hv
    · exact .inl ⟨v, hv, hvw, htr⟩
    · exact .inr hv
  | resource failure ht' _ => rw [ht] at ht'; cases ht'

/-- A stuck target matches only a stuck source. -/
theorem of_stuck {s : Traced E α} {t : Traced E β} (h : Refines R s t)
    (ht : t.result = .stuck) : s.result = .stuck := by
  cases h with
  | stuck hs => exact hs
  | result _ hr => rw [ht] at hr; exact hr.of_stuck
  | resource failure ht' _ => rw [ht] at ht'; cases ht'

/-- A target that goes wrong matches only a source that goes wrong. -/
theorem goesWrong {s : Traced E α} {t : Traced E β} (h : Refines R s t)
    (ht : t.result.GoesWrong) : s.result.GoesWrong := by
  cases h with
  | stuck hs => rw [hs]; exact trivial
  | result _ hr => exact hr.goesWrong ht
  | resource failure ht' _ => rw [ht'] at ht; exact absurd ht (Result.not_goesWrong_resource _)

/-- The target's trace is a prefix of the source's, unless the source is
stuck. -/
theorem trace_prefix {s : Traced E α} {t : Traced E β} (h : Refines R s t) :
    t.trace <+: s.trace ∨ s.result = .stuck := by
  cases h with
  | stuck hs => exact .inr hs
  | result htr _ => exact .inl (htr ▸ List.prefix_refl _)
  | resource _ _ hp => exact .inl hp

/-- The source's trace is a prefix of the target's, unless the target fails
for a resource or the source is stuck. -/
theorem trace_live {s : Traced E α} {t : Traced E β} (h : Refines R s t) :
    s.trace <+: t.trace ∨ (∃ failure, t.result = .resource failure) ∨ s.result = .stuck := by
  cases h with
  | stuck hs => exact .inr (.inr hs)
  | result htr _ => exact .inl (htr ▸ List.prefix_refl _)
  | resource failure ht _ => exact .inr (.inl ⟨failure, ht⟩)

theorem trans {S : β → γ → Prop} {s : Traced E α} {t : Traced E β} {u : Traced E γ}
    (h₁ : Refines R s t) (h₂ : Refines S t u) : Refines (RelComp R S) s u := by
  cases h₁ with
  | stuck hs => exact .stuck hs
  | result htr hr =>
    cases h₂ with
    | stuck ht => rw [ht] at hr; exact .stuck hr.of_stuck
    | result htr' hr' => exact .result (htr.trans htr') (hr.trans hr')
    | resource failure hu hp => exact .resource failure hu (htr ▸ hp)
  | resource failure ht hp =>
    obtain ⟨failure', hu, hp'⟩ := h₂.of_resource ht
    exact .resource failure' hu (hp'.trans hp)

end Refines

end Traced

/-! ## Clock monotonicity -/

/-- Clock monotonicity of a traced clocked semantics: an outcome other than
`timeout` is, with its trace, the outcome at every larger clock (`final`),
and the trace at a clock is a prefix of the trace at every larger clock
(`grows`). `final` is stronger than `ClockMono` of the results: a run that
has ended performs no further event, so its behaviour is well defined. -/
structure TraceMono {E α : Type} (c : Nat → Traced E α) : Prop where
  final : ∀ ⦃k k' : Nat⦄, k ≤ k' → (c k).result ≠ .timeout → c k' = c k
  grows : ∀ ⦃k k' : Nat⦄, k ≤ k' → (c k).trace <+: (c k').trace

namespace TraceMono

variable {E α : Type} {c : Nat → Traced E α}

/-- The results are clock monotone. -/
theorem result (h : TraceMono c) : ClockMono fun k => (c k).result :=
  fun _ _ hle hk => congrArg Traced.result (h.final hle hk)

/-- Two clocks that do not time out give the same traced outcome. -/
theorem eq_of_ne_timeout (h : TraceMono c) {k k' : Nat} (hk : (c k).result ≠ .timeout)
    (hk' : (c k').result ≠ .timeout) : c k = c k' := by
  rcases Nat.le_total k k' with hle | hle
  · exact (h.final hle hk).symm
  · exact h.final hle hk'

/-- A timeout at some clock is a timeout at every smaller clock. -/
theorem timeout_of_le (h : TraceMono c) {k k' : Nat} (hle : k ≤ k')
    (hk' : (c k').result = .timeout) : (c k).result = .timeout :=
  h.result.timeout_of_le hle hk'

/-- Every trace is a prefix of the trace of a clock that does not time
out. -/
theorem trace_prefix_final (h : TraceMono c) (k : Nat) {k' : Nat}
    (hk' : (c k').result ≠ .timeout) : (c k).trace <+: (c k').trace := by
  rcases Nat.le_total k k' with hle | hle
  · exact h.grows hle
  · rw [h.final hle hk']
    exact List.prefix_refl _

/-- A clock monotone pure semantics, lifted, is trace monotone. -/
theorem ofPure {c : Nat → Result α} (h : ClockMono c) :
    TraceMono fun k => (Traced.lift (c k) : Traced E α) where
  final _ _ hle hk := by
    simp only [Traced.lift_result] at hk
    simp only [Traced.lift, h hle hk]
  grows _ _ _ := List.prefix_refl _

/-- A constant function of the clock is trace monotone. -/
theorem const (t : Traced E α) : TraceMono fun _ => t where
  final _ _ _ _ := rfl
  grows _ _ _ := List.prefix_refl _

end TraceMono

/-! ## Behaviours -/

/-- The observable behaviour of a traced clocked semantics, without
infinite objects. -/
inductive TBehaviour (E α : Type) where
  /-- The run ends: its outcome, never `timeout`, with every event it
  performed. -/
  | ends (outcome : Traced E α)
  /-- Every clock times out; `trace k` is the trace at clock `k`. The run
  performs exactly their prefixes, and its possibly infinite trace is their
  least upper bound. -/
  | diverges (trace : Nat → List E)

namespace TBehaviour

variable {E α β γ : Type}

/-- The finite traces a behaviour performs: a prefix-closed set. -/
def Performs : TBehaviour E α → List E → Prop
  | ends t, tr => tr <+: t.trace
  | diverges trace, tr => ∃ k, tr <+: trace k

/-- The set of performed traces is prefix closed. -/
theorem Performs.of_prefix {b : TBehaviour E α} {tr tr' : List E} (h : b.Performs tr)
    (h' : tr' <+: tr) : b.Performs tr' := by
  cases b with
  | ends t => exact h'.trans h
  | diverges trace =>
    obtain ⟨k, hk⟩ := h
    exact ⟨k, h'.trans hk⟩

/-- A behaviour that goes wrong: it ends stuck or with a trap. -/
def GoesWrong : TBehaviour E α → Prop
  | ends t => t.result.GoesWrong
  | diverges _ => False

/-- A behaviour that ends stuck. -/
def Stuck : TBehaviour E α → Prop
  | ends t => t.result = .stuck
  | diverges _ => False

/-- Behaviour refinement up to resource failure. -/
inductive Refines (R : α → β → Prop) : TBehaviour E α → TBehaviour E β → Prop
  /-- Both runs end, with outcomes related by `Traced.Refines`. -/
  | ends {s : Traced E α} {t : Traced E β} : Traced.Refines R s t → Refines R (.ends s) (.ends t)
  /-- Both runs diverge, performing the same finite traces: the same
  possibly infinite trace. -/
  | diverges {a b : Nat → List E} :
      (∀ tr, (∃ k, tr <+: a k) ↔ ∃ k, tr <+: b k) → Refines R (.diverges a) (.diverges b)
  /-- A stuck source imposes nothing. -/
  | stuck {s : Traced E α} {b : TBehaviour E β} : s.result = .stuck → Refines R (.ends s) b
  /-- A target resource failure after a trace the source performs. -/
  | resource {b : TBehaviour E α} {t : Traced E β} (failure : Resource) :
      t.result = .resource failure → b.Performs t.trace → Refines R b (.ends t)

namespace Refines

variable {R : α → β → Prop}

theorem refl {R : α → α → Prop} (h : ∀ v, R v v) (b : TBehaviour E α) : Refines R b b := by
  cases b with
  | ends t => exact .ends (.refl h t)
  | diverges trace => exact .diverges fun _ => Iff.rfl

theorem mono {R' : α → β → Prop} (hR : ∀ v w, R v w → R' v w) {b₁ : TBehaviour E α}
    {b₂ : TBehaviour E β} (h : Refines R b₁ b₂) : Refines R' b₁ b₂ := by
  cases h with
  | ends h => exact .ends (h.mono hR)
  | diverges h => exact .diverges h
  | stuck hs => exact .stuck hs
  | resource failure ht hp => exact .resource failure ht hp

/-- Every finite trace the target performs is performed by the source,
unless the source is stuck. -/
theorem performs {b₁ : TBehaviour E α} {b₂ : TBehaviour E β} (h : Refines R b₁ b₂)
    {tr : List E} (ht : b₂.Performs tr) : b₁.Performs tr ∨ b₁.Stuck := by
  cases h with
  | ends h =>
    rcases h.trace_prefix with hp | hs
    · exact .inl (List.IsPrefix.trans ht hp)
    · exact .inr hs
  | diverges h => exact .inl ((h tr).2 ht)
  | stuck hs => exact .inr hs
  | resource _ _ hp => exact .inl (hp.of_prefix ht)

/-- Every finite trace the source performs is performed by the target,
unless the target ends with a resource failure or the source is stuck. -/
theorem live {b₁ : TBehaviour E α} {b₂ : TBehaviour E β} (h : Refines R b₁ b₂)
    {tr : List E} (hs : b₁.Performs tr) :
    b₂.Performs tr ∨ (∃ t failure, b₂ = .ends t ∧ t.result = .resource failure) ∨ b₁.Stuck := by
  cases h with
  | ends h =>
    rcases h.trace_live with hp | ⟨failure, hf⟩ | hst
    · exact .inl (List.IsPrefix.trans hs hp)
    · exact .inr (.inl ⟨_, failure, rfl, hf⟩)
    · exact .inr (.inr hst)
  | diverges h => exact .inl ((h tr).1 hs)
  | stuck hst => exact .inr (.inr hst)
  | resource failure hf _ => exact .inr (.inl ⟨_, failure, rfl, hf⟩)

/-- A target that goes wrong matches only a source that goes wrong. -/
theorem goesWrong {b₁ : TBehaviour E α} {b₂ : TBehaviour E β} (h : Refines R b₁ b₂)
    (hb : b₂.GoesWrong) : b₁.GoesWrong := by
  cases h with
  | ends h => exact h.goesWrong hb
  | diverges _ => exact hb
  | stuck hs => show Result.GoesWrong _; rw [hs]; exact trivial
  | resource failure ht _ =>
    exact absurd (show Result.GoesWrong _ from hb) (by rw [ht]; exact Result.not_goesWrong_resource _)

theorem trans {S : β → γ → Prop} {b₁ : TBehaviour E α} {b₂ : TBehaviour E β}
    {b₃ : TBehaviour E γ} (h₁ : Refines R b₁ b₂) (h₂ : Refines S b₂ b₃) :
    Refines (RelComp R S) b₁ b₃ := by
  cases h₂ with
  | resource failure ht hp =>
    rcases h₁.performs hp with hp' | hs
    · exact .resource failure ht hp'
    · cases b₁ with
      | ends s => exact .stuck hs
      | diverges _ => exact absurd hs id
  | ends h₂₃ =>
    cases h₁ with
    | ends h₁₂ => exact .ends (h₁₂.trans h₂₃)
    | stuck hs => exact .stuck hs
    | resource failure ht hp =>
      obtain ⟨failure', hu, hp'⟩ := h₂₃.of_resource ht
      exact .resource failure' hu (hp.of_prefix hp')
  | diverges h₂₃ =>
    cases h₁ with
    | diverges h₁₂ => exact .diverges fun tr => (h₁₂ tr).trans (h₂₃ tr)
    | stuck hs => exact .stuck hs
  | stuck ht =>
    cases h₁ with
    | ends h₁₂ => exact .stuck (h₁₂.of_stuck ht)
    | stuck hs => exact .stuck hs
    | resource failure ht' _ => rw [ht] at ht'; cases ht'

end Refines

end TBehaviour

/-- A behaviour refinement of single pure outcomes is their refinement. -/
theorem Result.Refines.ofBehaviour {α β : Type} {R : α → β → Prop} {r : Result α}
    {r' : Result β} (h : Behaviour.Refines R r.toBehaviour r'.toBehaviour) :
    Result.Refines R r r' := by
  cases r <;> cases r' <;> simp only [Result.toBehaviour] at h <;> cases h <;>
    first
    | exact .ok ‹_›
    | exact .timeout
    | exact .trap
    | exact .stuck
    | exact .resource _

open Classical in
/-- The traced behaviour of a clocked semantics under one environment: the
traced outcome at any clock that does not time out, or divergence with the
trace at every clock. -/
noncomputable def tbehaviour {E α : Type} (c : Nat → Traced E α) : TBehaviour E α :=
  if h : ∃ k, (c k).result ≠ .timeout then .ends (c (Classical.choose h))
  else .diverges fun k => (c k).trace

section tbehaviour

variable {E α β : Type} {c : Nat → Traced E α}

/-- Under monotonicity, any clock that does not time out gives the
behaviour. -/
theorem tbehaviour_of_ne_timeout (h : TraceMono c) {k : Nat} (hk : (c k).result ≠ .timeout) :
    tbehaviour c = .ends (c k) := by
  unfold tbehaviour
  split
  · next hex => rw [h.eq_of_ne_timeout (Classical.choose_spec hex) hk]
  · next hex => exact absurd ⟨k, hk⟩ hex

theorem tbehaviour_of_forall_timeout (hc : ∀ k, (c k).result = .timeout) :
    tbehaviour c = .diverges fun k => (c k).trace := by
  unfold tbehaviour
  split
  · next hex => exact absurd (hc _) (Classical.choose_spec hex)
  · rfl

/-- A run ends with `t` exactly when `t` is its outcome at a clock that does
not time out. -/
theorem tbehaviour_eq_ends_iff (h : TraceMono c) {t : Traced E α} :
    tbehaviour c = .ends t ↔ t.result ≠ .timeout ∧ ∃ k, c k = t := by
  constructor
  · intro hb
    by_cases hex : ∃ k, (c k).result ≠ .timeout
    · obtain ⟨k, hk⟩ := hex
      rw [tbehaviour_of_ne_timeout h hk] at hb
      cases hb
      exact ⟨hk, k, rfl⟩
    · rw [tbehaviour_of_forall_timeout fun k =>
        Classical.byContradiction fun hk => hex ⟨k, hk⟩] at hb
      cases hb
  · rintro ⟨ht, k, rfl⟩
    exact tbehaviour_of_ne_timeout h ht

/-- A run diverges exactly when every clock times out. -/
theorem tbehaviour_diverges_iff (h : TraceMono c) :
    (∃ trace, tbehaviour c = .diverges trace) ↔ ∀ k, (c k).result = .timeout := by
  constructor
  · rintro ⟨trace, hb⟩ k
    refine Classical.byContradiction fun hk => ?_
    rw [tbehaviour_of_ne_timeout h hk] at hb
    cases hb
  · intro hc
    exact ⟨_, tbehaviour_of_forall_timeout hc⟩

/-- The finite traces of a run's behaviour are the prefixes of its traces. -/
theorem performs_tbehaviour (h : TraceMono c) {tr : List E} :
    (tbehaviour c).Performs tr ↔ ∃ k, tr <+: (c k).trace := by
  by_cases hex : ∃ k, (c k).result ≠ .timeout
  · obtain ⟨k, hk⟩ := hex
    rw [tbehaviour_of_ne_timeout h hk]
    exact ⟨fun hp => ⟨k, hp⟩, fun ⟨k', hp⟩ => hp.trans (h.trace_prefix_final k' hk)⟩
  · rw [tbehaviour_of_forall_timeout fun k => Classical.byContradiction fun hk => hex ⟨k, hk⟩]
    exact Iff.rfl

/-- A run's behaviour is stuck exactly when some clock is stuck. -/
theorem stuck_tbehaviour (h : TraceMono c) :
    (tbehaviour c).Stuck ↔ ∃ k, (c k).result = .stuck := by
  by_cases hex : ∃ k, (c k).result ≠ .timeout
  · obtain ⟨k, hk⟩ := hex
    rw [tbehaviour_of_ne_timeout h hk]
    refine ⟨fun hs => ⟨k, hs⟩, fun ⟨k', hk'⟩ => ?_⟩
    show (c k).result = .stuck
    rw [h.eq_of_ne_timeout hk (k' := k') (by simp [hk']), hk']
  · have hc : ∀ k, (c k).result = .timeout := fun k =>
      Classical.byContradiction fun hk => hex ⟨k, hk⟩
    rw [tbehaviour_of_forall_timeout hc]
    exact ⟨False.elim, fun ⟨k, hk⟩ => by rw [hc k] at hk; cases hk⟩

/-- A run's behaviour goes wrong exactly when some clock goes wrong. -/
theorem goesWrong_tbehaviour (h : TraceMono c) :
    (tbehaviour c).GoesWrong ↔ ∃ k, (c k).result.GoesWrong := by
  by_cases hex : ∃ k, (c k).result ≠ .timeout
  · obtain ⟨k, hk⟩ := hex
    rw [tbehaviour_of_ne_timeout h hk]
    refine ⟨fun hs => ⟨k, hs⟩, fun ⟨k', hk'⟩ => ?_⟩
    show (c k).result.GoesWrong
    have : (c k').result ≠ .timeout := fun e => by rw [e] at hk'; exact hk'
    rwa [h.eq_of_ne_timeout hk this]
  · have hc : ∀ k, (c k).result = .timeout := fun k =>
      Classical.byContradiction fun hk => hex ⟨k, hk⟩
    rw [tbehaviour_of_forall_timeout hc]
    exact ⟨False.elim, fun ⟨k, hk⟩ => by rw [hc k] at hk; exact hk⟩

/-- Pure behaviour refinement of clock monotone semantics is traced
behaviour refinement of their lifts, for every event type. -/
theorem TBehaviour.Refines.ofPure {R : α → β → Prop} {c₁ : Nat → Result α}
    {c₂ : Nat → Result β} (h₁ : ClockMono c₁) (h₂ : ClockMono c₂)
    (h : Behaviour.Refines R (behaviour c₁) (behaviour c₂)) :
    TBehaviour.Refines R (tbehaviour fun k => (Traced.lift (c₁ k) : Traced E α))
      (tbehaviour fun k => (Traced.lift (c₂ k) : Traced E β)) := by
  have m₁ := TraceMono.ofPure (E := E) h₁
  have m₂ := TraceMono.ofPure (E := E) h₂
  by_cases hex₁ : ∃ k, c₁ k ≠ .timeout
  · obtain ⟨k, hk⟩ := hex₁
    rw [tbehaviour_of_ne_timeout m₁ (k := k) hk]
    rw [behaviour_of_ne_timeout h₁ hk] at h
    by_cases hex₂ : ∃ k, c₂ k ≠ .timeout
    · obtain ⟨k', hk'⟩ := hex₂
      rw [tbehaviour_of_ne_timeout m₂ (k := k') hk']
      rw [behaviour_of_ne_timeout h₂ hk'] at h
      exact .ends (.lift (Result.Refines.ofBehaviour h))
    · have hc₂ : ∀ k, c₂ k = .timeout := fun k =>
        Classical.byContradiction fun hk => hex₂ ⟨k, hk⟩
      rw [behaviour_of_forall_timeout hc₂] at h
      revert h hk
      generalize c₁ k = r
      intro h hk
      cases r <;> simp only [Result.toBehaviour] at h <;> cases h
      · exact absurd rfl hk
      · exact .stuck rfl
  · have hc₁ : ∀ k, c₁ k = .timeout := fun k =>
      Classical.byContradiction fun hk => hex₁ ⟨k, hk⟩
    rw [tbehaviour_of_forall_timeout (c := fun k => (Traced.lift (c₁ k) : Traced E α))
      fun k => by simp [hc₁ k]]
    rw [behaviour_of_forall_timeout hc₁] at h
    by_cases hex₂ : ∃ k, c₂ k ≠ .timeout
    · obtain ⟨k', hk'⟩ := hex₂
      rw [tbehaviour_of_ne_timeout m₂ (k := k') hk']
      rw [behaviour_of_ne_timeout h₂ hk'] at h
      revert h hk'
      generalize c₂ k' = r
      intro h hk'
      cases r <;> simp only [Result.toBehaviour] at h <;> cases h
      · exact absurd rfl hk'
      · exact .resource _ rfl ⟨0, List.nil_prefix⟩
    · have hc₂ : ∀ k, c₂ k = .timeout := fun k =>
        Classical.byContradiction fun hk => hex₂ ⟨k, hk⟩
      rw [tbehaviour_of_forall_timeout (c := fun k => (Traced.lift (c₂ k) : Traced E β))
        fun k => by simp [hc₂ k]]
      exact .diverges fun _ => Iff.rfl

end tbehaviour

end IxCC.Sem

