import IxCC.Sem.Traced

/-!
# Traced clocked simulation

`TSim R f c₁ c₂` is the clocked simulation of `Sem.Sim` for traced
semantics that read an environment `o : Env` (decision D-1; the shape of
`plans/systems/research/effects-concurrency.md` §4.2). For every
environment:

- **forward:** an outcome of the source at clock `k` other than `timeout`
  is matched by the target at *some* clock `k'` (`Traced.Refines`: the same
  trace with a related value or the same trap, a target resource failure
  after a prefix of the source's trace, or anything if the source is
  stuck);
- **timeout:** a source timeout at clock `f k` is a target timeout or
  resource failure at `k`, whose trace is a prefix of the source's at
  `f k` (the target has not performed more than the source);
- **progress:** the source's trace at any clock is a prefix of the target's
  at some clock, unless the target fails for a resource (the target keeps
  up with a source that keeps performing events, including one that
  diverges).

The environment and `f` are shared across the clauses; theorems quantify
over every environment (a demonic oracle). Progress holds at every source
clock, a stuck one included: a pass may not drop events the source performs
before it gets stuck (CompCert's `behavior_improves` at the proof level),
while `TBehaviour.Refines` still asks nothing of a stuck source.

Phase 1 levels lift their pure simulations: `TSim.ofPure` turns a `Sim`
into a `TSim` of the lifted semantics for every `Env` and `E` (the trace
clauses hold with `[]`), and `TSim.toPure` goes back.

`TSim.refines` is the divergence lemma (CakeML's `IMP_semantics_eq` with
`lprefix_lub`): under trace monotonicity a simulation refines the traced
behaviours, a diverging source's finite traces included. `backward`,
`trace_prefix` and `safe` are the per-clock shapes of `compile_sound`,
trace safety and `compile_safe`; `comp` composes simulations.
-/

namespace IxCC.Sem

/-- A traced clocked simulation from `c₁` to `c₂` with value relation `R`
and clock map `f` (see the module comment). -/
structure TSim {Env E α β : Type} (R : α → β → Prop) (f : Nat → Nat)
    (c₁ : Env → Nat → Traced E α) (c₂ : Env → Nat → Traced E β) : Prop where
  /-- Every source outcome other than `timeout` is matched at some clock. -/
  forward : ∀ o k, (c₁ o k).result ≠ .timeout → ∃ k', Traced.Refines R (c₁ o k) (c₂ o k')
  /-- A source timeout at `f k` is a target timeout or resource failure at
  `k`, after a prefix of the source's trace. -/
  timeout : ∀ o k, (c₁ o (f k)).result = .timeout →
    ((c₂ o k).result = .timeout ∨ ∃ failure, (c₂ o k).result = .resource failure) ∧
      (c₂ o k).trace <+: (c₁ o (f k)).trace
  /-- Every source trace is a prefix of a target trace, unless the target
  fails for a resource. -/
  progress : ∀ o k, ∃ k', (c₁ o k).trace <+: (c₂ o k').trace ∨
    ∃ failure, (c₂ o k').result = .resource failure

namespace TSim

variable {Env E α β γ : Type} {R : α → β → Prop} {f : Nat → Nat}
  {c₁ : Env → Nat → Traced E α} {c₂ : Env → Nat → Traced E β}

/-- A pure simulation is a traced simulation of the lifted semantics, for
every environment and event type. -/
theorem ofPure {c₁ : Nat → Result α} {c₂ : Nat → Result β} (hs : Sim R f c₁ c₂) :
    TSim (Env := Env) (E := E) R f (fun _ k => Traced.lift (c₁ k))
      (fun _ k => Traced.lift (c₂ k)) where
  forward _ k hk := (hs.forward k hk).imp fun _ h => .lift h
  timeout _ k hk := ⟨hs.timeout k hk, List.prefix_refl _⟩
  progress _ k := ⟨k, .inl (List.prefix_refl _)⟩

/-- A traced simulation of lifted semantics is a pure simulation. -/
theorem toPure {c₁ : Nat → Result α} {c₂ : Nat → Result β} (o : Env)
    (hs : TSim (E := E) R f (fun (_ : Env) k => Traced.lift (c₁ k))
      (fun _ k => Traced.lift (c₂ k))) : Sim R f c₁ c₂ where
  forward k hk := (hs.forward o k hk).imp fun _ h => h.toPure
  timeout k hk := (hs.timeout o k hk).1

/-- The identity simulation. -/
theorem refl {R : α → α → Prop} (hR : ∀ v, R v v) (c : Env → Nat → Traced E α) :
    TSim R id c c where
  forward _ k _ := ⟨k, .refl hR _⟩
  timeout _ _ h := ⟨.inl h, List.prefix_refl _⟩
  progress _ k := ⟨k, .inl (List.prefix_refl _)⟩

/-- A simulation for a stronger value relation is one for a weaker one. -/
theorem mono {R' : α → β → Prop} (hR : ∀ v w, R v w → R' v w) (hs : TSim R f c₁ c₂) :
    TSim R' f c₁ c₂ where
  forward o k hk := (hs.forward o k hk).imp fun _ h => h.mono hR
  timeout := hs.timeout
  progress := hs.progress

/-- The divergence lemma (CakeML's `IMP_semantics_eq` with `lprefix_lub`):
under every environment, a traced simulation between trace monotone
semantics refines their traced behaviours. -/
theorem refines (h₁ : ∀ o, TraceMono (c₁ o)) (h₂ : ∀ o, TraceMono (c₂ o))
    (hs : TSim R f c₁ c₂) (o : Env) :
    TBehaviour.Refines R (tbehaviour (c₁ o)) (tbehaviour (c₂ o)) := by
  by_cases hex : ∃ k, (c₁ o k).result ≠ .timeout
  · obtain ⟨k, hk⟩ := hex
    obtain ⟨k', hr⟩ := hs.forward o k hk
    rw [tbehaviour_of_ne_timeout (h₁ o) hk]
    by_cases hk' : (c₂ o k').result = .timeout
    · rcases hr.of_timeout hk' with h | h
      · exact absurd h hk
      · exact .stuck h
    · rw [tbehaviour_of_ne_timeout (h₂ o) hk']
      exact .ends hr
  · have hdiv : ∀ k, (c₁ o k).result = .timeout := fun k =>
      Classical.byContradiction fun hk => hex ⟨k, hk⟩
    rw [tbehaviour_of_forall_timeout hdiv]
    by_cases hend : ∃ k, (c₂ o k).result ≠ .timeout
    · obtain ⟨k, hk⟩ := hend
      rw [tbehaviour_of_ne_timeout (h₂ o) hk]
      obtain ⟨h | ⟨failure, h⟩, hp⟩ := hs.timeout o k (hdiv _)
      · exact absurd h hk
      · exact .resource failure h ⟨f k, hp⟩
    · have hdiv₂ : ∀ k, (c₂ o k).result = .timeout := fun k =>
        Classical.byContradiction fun hk => hend ⟨k, hk⟩
      rw [tbehaviour_of_forall_timeout hdiv₂]
      refine .diverges fun tr => ⟨fun ⟨k, hk⟩ => ?_, fun ⟨k, hk⟩ => ⟨f k, ?_⟩⟩
      · obtain ⟨k', hp | ⟨failure, hf⟩⟩ := hs.progress o k
        · exact ⟨k', hk.trans hp⟩
        · rw [hdiv₂ k'] at hf
          cases hf
      · exact hk.trans (hs.timeout o k (hdiv _)).2

/-- Backward reading at one clock: a target outcome other than `timeout`
matches the source's outcome at clock `f k`. In particular a target value
comes, with the same trace, from a related source value or a stuck source
(`Traced.Refines.of_ok`). -/
theorem backward (h₂ : ∀ o, TraceMono (c₂ o)) (hs : TSim R f c₁ c₂) {o : Env} {k : Nat}
    (hk : (c₂ o k).result ≠ .timeout) : Traced.Refines R (c₁ o (f k)) (c₂ o k) := by
  by_cases hsrc : (c₁ o (f k)).result = .timeout
  · obtain ⟨h | ⟨failure, h⟩, hp⟩ := hs.timeout o k hsrc
    · exact absurd h hk
    · exact .resource failure h hp
  · obtain ⟨k', hr⟩ := hs.forward o _ hsrc
    by_cases hk' : (c₂ o k').result = .timeout
    · rcases hr.of_timeout hk' with h | h
      · exact absurd h hsrc
      · exact .stuck h
    · rwa [(h₂ o).eq_of_ne_timeout hk' hk] at hr

/-- Trace safety at one clock: the target's trace at `k` is a prefix of the
source's at `f k`, unless the source is stuck there. -/
theorem trace_prefix (h₂ : ∀ o, TraceMono (c₂ o)) (hs : TSim R f c₁ c₂) (o : Env) (k : Nat) :
    (c₂ o k).trace <+: (c₁ o (f k)).trace ∨ (c₁ o (f k)).result = .stuck := by
  by_cases hsrc : (c₁ o (f k)).result = .timeout
  · exact .inl (hs.timeout o k hsrc).2
  · obtain ⟨k', hr⟩ := hs.forward o _ hsrc
    by_cases hk' : (c₂ o k').result = .timeout
    · rcases hr.of_timeout hk' with h | h
      · exact absurd h hsrc
      · exact .inr h
    · rcases hr.trace_prefix with hp | h
      · exact .inl (((h₂ o).trace_prefix_final k hk').trans hp)
      · exact .inr h

/-- Safety at one clock: if the source does not go wrong at clock `f k`,
the target does not go wrong at `k`. -/
theorem safe (h₂ : ∀ o, TraceMono (c₂ o)) (hs : TSim R f c₁ c₂) {o : Env} {k : Nat}
    (hsrc : ¬ (c₁ o (f k)).result.GoesWrong) : ¬ (c₂ o k).result.GoesWrong := by
  intro ht
  have hk : (c₂ o k).result ≠ .timeout := fun h => by rw [h] at ht; exact ht
  exact hsrc ((hs.backward h₂ hk).goesWrong ht)

/-- Traced simulations compose; the clock maps compose in reverse. -/
theorem comp {S : β → γ → Prop} {g : Nat → Nat} {c₃ : Env → Nat → Traced E γ}
    (h₃ : ∀ o, TraceMono (c₃ o)) (hs : TSim R f c₁ c₂) (ht : TSim S g c₂ c₃) :
    TSim (RelComp R S) (fun k => f (g k)) c₁ c₃ where
  forward o k hk := by
    obtain ⟨k', h₁₂⟩ := hs.forward o k hk
    by_cases hk' : (c₂ o k').result = .timeout
    · rcases h₁₂.of_timeout hk' with h | h
      · exact absurd h hk
      · exact ⟨0, .stuck h⟩
    · obtain ⟨k'', h₂₃⟩ := ht.forward o k' hk'
      exact ⟨k'', h₁₂.trans h₂₃⟩
  timeout o k hk := by
    obtain ⟨h₂ | ⟨failure, h₂⟩, hp₁₂⟩ := hs.timeout o (g k) hk
    · obtain ⟨h₃', hp₂₃⟩ := ht.timeout o k h₂
      exact ⟨h₃', hp₂₃.trans hp₁₂⟩
    · obtain ⟨k', h₂₃⟩ := ht.forward o (g k) (by rw [h₂]; exact nofun)
      obtain ⟨failure', hf', hp'⟩ := h₂₃.of_resource h₂
      have hp : (c₃ o k).trace <+: (c₃ o k').trace :=
        (h₃ o).trace_prefix_final k (by rw [hf']; exact nofun)
      refine ⟨?_, hp.trans (hp'.trans hp₁₂)⟩
      by_cases hk3 : (c₃ o k).result = .timeout
      · exact .inl hk3
      · refine .inr ⟨failure', ?_⟩
        rw [(h₃ o).eq_of_ne_timeout hk3 (k' := k') (by rw [hf']; exact nofun), hf']
  progress o k := by
    obtain ⟨k', hp | ⟨failure, hf⟩⟩ := hs.progress o k
    · obtain ⟨k'', hp' | hf'⟩ := ht.progress o k'
      · exact ⟨k'', .inl (hp.trans hp')⟩
      · exact ⟨k'', .inr hf'⟩
    · obtain ⟨k'', h₂₃⟩ := ht.forward o k' (by rw [hf]; exact nofun)
      obtain ⟨failure', hf', _⟩ := h₂₃.of_resource hf
      exact ⟨k'', .inr ⟨failure', hf'⟩⟩

/-- If the source does not go wrong at any clock, the target never goes
wrong. -/
theorem safe_all (h₂ : ∀ o, TraceMono (c₂ o)) (hs : TSim R f c₁ c₂) {o : Env}
    (hsrc : ∀ k, ¬ (c₁ o k).result.GoesWrong) (k : Nat) : ¬ (c₂ o k).result.GoesWrong :=
  hs.safe h₂ (hsrc _)

end TSim

end IxCC.Sem
