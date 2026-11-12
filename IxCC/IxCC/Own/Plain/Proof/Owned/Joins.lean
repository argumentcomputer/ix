import IxCC.Own.Plain.Proof.Owned.Rhs

/-! # Join declarations and jumps

A declaration saves its body with the context it was checked from (`OwnedEntry`): nothing moves,
the captured list is recorded against the join in `Δ`. A jump hands over the arguments' tokens
and one token of each captured variable that is not an immediate of the declaration; the body
starts from exactly those (`Ctx.enter`), so the counts are the jump's with the vacuous tokens of
immediates added or dropped. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)
open IxCC.Fir (Var Arg)

theorem nodupFrom_spec : ∀ {seen : Src.NatSet} {xs : List Var}, nodupFrom seen xs = true →
    xs.Nodup ∧ ∀ y, y ∈ xs → seen.contains y = false
  | _, [], _ => ⟨List.nodup_nil, fun _ h => by simp at h⟩
  | seen, x :: xs, h => by
    simp only [nodupFrom, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hx, hrest⟩ := h
    obtain ⟨hn, hs⟩ := nodupFrom_spec hrest
    refine ⟨List.nodup_cons.mpr ⟨fun hm => ?_, hn⟩, fun y hy => ?_⟩
    · have := hs x hm
      simp [Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert] at this
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · have := hs y hy
        simp only [Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert] at this ⊢
        split at this
        · simp at this
        · exact this

theorem nodupVars_nodup {xs : List Var} (h : nodupVars xs = true) : xs.Nodup :=
  (nodupFrom_spec h).1

theorem fresh_mono : ∀ {big small ps : List Var}, fresh big ps = true →
    (∀ x, x ∈ small → x ∈ big) → fresh small ps = true
  | _, _, [], _, _ => rfl
  | big, small, p :: ps, h, hs => by
    simp only [fresh, Bool.and_eq_true] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, fresh_mono h2 (fun x hx => ?_)⟩
    · have hp : p ∉ big := by simpa using h1
      have : p ∉ small := fun hm => hp (hs p hm)
      simpa using this
    · rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ (hs x hx)
      · exact List.mem_append_right _ hx

theorem Fir.lookupJ_id {j : Fir.JoinId} : ∀ {J : List Fir.JEntry} {e : Fir.JEntry}
    {rest : List Fir.JEntry}, Fir.lookupJ j J = some (e, rest) → e.id = j
  | [], _, _, h => by simp [Fir.lookupJ] at h
  | e₀ :: J, e, rest, h => by
    simp only [Fir.lookupJ] at h
    split at h
    · next he => simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h; exact he
    · exact Fir.lookupJ_id h

theorem Fir.lookupJ_of_arity {j : Fir.JoinId} {n : Nat} : ∀ {J : List Fir.JEntry},
    (stackArities J).lookup j = some n → ∃ e rest, Fir.lookupJ j J = some (e, rest) ∧
      e.params.length = n
  | [], h => by simp [stackArities, List.lookup] at h
  | e₀ :: J, h => by
    by_cases he : e₀.id = j
    · have hb : (j == e₀.id) = true := by simp [he]
      simp only [stackArities, List.map_cons, List.lookup, hb, Option.some.injEq] at h
      exact ⟨e₀, J, by simp [Fir.lookupJ, he], h⟩
    · have hb : (j == e₀.id) = false := by simpa [eq_comm] using he
      have h' : (stackArities J).lookup j = some n := by
        simpa [stackArities, List.lookup, hb] using h
      obtain ⟨e, rest, hl, hn⟩ := Fir.lookupJ_of_arity h'
      exact ⟨e, rest, by simp [Fir.lookupJ, he, hl], hn⟩

/-- Keep the tokens a predicate selects; those dropped hold immediates. -/
theorem EnvRoots.filter {ρ : Own.Env} (p : Var → Bool) :
    ∀ {xs : List Var} {vs : List RVal}, EnvRoots ρ xs vs →
      (∀ x, x ∈ xs → p x = false → ∃ v, ρ.get? x = some v ∧ ImmVal v) →
      ∃ vs', EnvRoots ρ (xs.filter p) vs' ∧ SameRefs vs vs'
  | [], vs, h, _ => ⟨[], rfl, by cases h; exact SameRefs.refl _⟩
  | y :: ys, vs, h, hp => by
    obtain ⟨u, us, hy, hus, rfl⟩ := EnvRoots.cons_iff.mp h
    obtain ⟨vs', hr, hs⟩ := EnvRoots.filter p hus (fun x hx => hp x (List.mem_cons_of_mem _ hx))
    cases hpy : p y with
    | true =>
      refine ⟨u :: vs', ?_, SameRefs.cons u hs⟩
      rw [List.filter_cons_of_pos hpy]
      exact EnvRoots.cons hy hr
    | false =>
      obtain ⟨u', hu', himm⟩ := hp y List.mem_cons_self hpy
      have : u' = u := Option.some.inj (hu'.symm.trans hy)
      subst this
      refine ⟨vs', ?_, (SameRefs.imm_cons himm us).trans hs⟩
      rw [List.filter_cons_of_neg (by simp [hpy])]
      exact hr

end IxCC.Own.Plain
