import IxCC.Anf.Walk

/-! # The walk's monad, inverted

The rewriting walk (`Anf.Walk`) runs in `StateT Fires (Except String)`; the
state only counts rule firings and the nodes they copy. These lemmas invert a
successful run of a bind, `pure`, `throw` and `fire` (M2.3). -/

set_option autoImplicit false

namespace IxCC.Anf.Walk

theorem run_bind_ok {α β : Type} {x : M α} {f : α → M β} {s s'' : Fires} {b : β}
    (h : (x >>= f).run s = .ok (b, s'')) : ∃ a s', x.run s = .ok (a, s') ∧ (f a).run s' = .ok (b, s'') := by
  simp only [StateT.run_bind] at h
  cases hx : x.run s with
  | error e => rw [hx] at h; cases h
  | ok p =>
    obtain ⟨a, s'⟩ := p
    rw [hx] at h
    exact ⟨a, s', rfl, h⟩

theorem run_pure_ok {α : Type} {a b : α} {s s' : Fires} (h : (pure a : M α).run s = .ok (b, s')) :
    a = b ∧ s = s' := by
  simp only [StateT.run_pure] at h
  cases h
  exact ⟨rfl, rfl⟩

theorem run_throw_ok {α : Type} {e : String} {s : Fires} {r : α × Fires}
    (h : (throw e : M α).run s = .ok r) : False := by
  cases h

theorem run_fire_ok {f : Fires → Fires} {s : Fires} {r : Unit × Fires} (h : (fire f).run s = .ok r) :
    r = ((), f s) := by
  change (if (f s).total > maxFires then
    (.error "walk: rule firing budget exhausted" : Except String (Unit × Fires))
    else if (f s).copied > maxCopy then .error "walk: copy budget exhausted"
    else .ok ((), f s)) = .ok r at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      rfl

/-- A walk step's work charge changes only the state (its work counter). -/
theorem run_charge_then {α : Type} {cost : Nat → Nat} {x : M α} {s s' : Fires} {a : α}
    (h : (charge cost >>= fun _ => x).run s = .ok (a, s')) : ∃ s0, x.run s0 = .ok (a, s') := by
  obtain ⟨u, s0, _, h2⟩ := run_bind_ok h
  exact ⟨s0, h2⟩

/-- A walk step's depth check changes only the state (its deepest step). -/
theorem run_descend_then {α : Type} {lvl : Nat} {x : M α} {s s' : Fires} {a : α}
    (h : (descend lvl >>= fun _ => x).run s = .ok (a, s')) : ∃ s0, x.run s0 = .ok (a, s') := by
  obtain ⟨u, s0, _, h2⟩ := run_bind_ok h
  exact ⟨s0, h2⟩

theorem run_map_ok {α β : Type} {g : α → β} {x : M α} {s s' : Fires} {b : β}
    (h : (g <$> x).run s = .ok (b, s')) : ∃ a, x.run s = .ok (a, s') ∧ g a = b := by
  simp only [StateT.run_map] at h
  cases hx : x.run s with
  | error e => rw [hx] at h; cases h
  | ok p =>
    obtain ⟨a, s1⟩ := p
    rw [hx] at h
    cases h
    exact ⟨a, rfl, rfl⟩

end IxCC.Anf.Walk
