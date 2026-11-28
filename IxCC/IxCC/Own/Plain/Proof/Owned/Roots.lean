import IxCC.Own.Plain.Proof.Owned.Context
import IxCC.Own.Plain.Proof.CaptureRoots
import IxCC.Own.Plain.Proof.Bindings

/-! # Token lists and their values

A path's tokens are a list of variables (`Ctx.Tokens`); their values (`EnvRoots`) are what
`Balance` counts. Only the number of references to each location matters (`SameRefs`), so a token
may be taken from any position, and a token whose value is an immediate counts for nothing. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Fir (Var Arg)

/-- The same number of references to every location. -/
def SameRefs (a b : List RVal) : Prop := ∀ l, refsIn l a = refsIn l b

namespace SameRefs

theorem refl (a : List RVal) : SameRefs a a := fun _ => rfl
theorem symm {a b : List RVal} (h : SameRefs a b) : SameRefs b a := fun l => (h l).symm
theorem trans {a b c : List RVal} (h₁ : SameRefs a b) (h₂ : SameRefs b c) : SameRefs a c :=
  fun l => (h₁ l).trans (h₂ l)

theorem append {a b c d : List RVal} (h₁ : SameRefs a b) (h₂ : SameRefs c d) :
    SameRefs (a ++ c) (b ++ d) := fun l => by simp only [refsIn_append, h₁ l, h₂ l]

theorem comm (a b : List RVal) : SameRefs (a ++ b) (b ++ a) := fun l => by
  simp only [refsIn_append]; omega

theorem cons {a b : List RVal} (v : RVal) (h : SameRefs a b) : SameRefs (v :: a) (v :: b) :=
  fun l => by simp only [refsIn, h l]

theorem balance {H : Heap} {external : Nat → Nat} {a b : List RVal}
    (h : SameRefs a b) (hb : Balance H external a) : Balance H external b := fun l => by
  rw [hb l, h l]

/-- An immediate value counts for nothing. -/
theorem imm_cons {v : RVal} (hv : ImmVal v) (a : List RVal) : SameRefs (v :: a) a := fun l => by
  simp only [refsIn]
  have : v ≠ .loc l := hv l
  simp [this]

end SameRefs

/-- Every value in the list is an immediate. -/
def AllImm (vs : List RVal) : Prop := ∀ v, v ∈ vs → ImmVal v

theorem SameRefs.allImm {vs : List RVal} (h : AllImm vs) (a : List RVal) : SameRefs (vs ++ a) a := by
  induction vs with
  | nil => exact SameRefs.refl _
  | cons v vs ih =>
    exact (SameRefs.imm_cons (h v List.mem_cons_self) _).trans
      (ih (fun u hu => h u (List.mem_cons_of_mem _ hu)))

theorem EnvRoots.nil (ρ : Own.Env) : EnvRoots ρ [] [] := rfl

theorem EnvRoots.cons_iff {ρ : Own.Env} {x : Var} {xs : List Var} {vs : List RVal} :
    EnvRoots ρ (x :: xs) vs ↔ ∃ v vs', ρ.get? x = some v ∧ EnvRoots ρ xs vs' ∧ vs = v :: vs' := by
  unfold EnvRoots
  simp only [List.map_cons, Own.evalArgs, Own.evalArg]
  constructor
  · intro h
    cases hx : ρ.get? x with
    | none => rw [hx] at h; cases h
    | some v =>
      cases hs : Own.evalArgs ρ (xs.map Fir.Arg.var) with
      | none => rw [hx, hs] at h; cases h
      | some vs' =>
        rw [hx, hs] at h
        exact ⟨v, vs', rfl, rfl, (Option.some.inj h).symm⟩
  · rintro ⟨v, vs', hx, hs, rfl⟩
    rw [hx, hs]

theorem EnvRoots.cons {ρ : Own.Env} {x : Var} {xs : List Var} {v : RVal} {vs : List RVal}
    (hx : ρ.get? x = some v) (h : EnvRoots ρ xs vs) : EnvRoots ρ (x :: xs) (v :: vs) :=
  EnvRoots.cons_iff.mpr ⟨v, vs, hx, h, rfl⟩

/-- Taking a token from any position. -/
theorem EnvRoots.erase {ρ : Own.Env} {x : Var} {v : RVal} (hx : ρ.get? x = some v) :
    ∀ {xs : List Var} {vs : List RVal}, EnvRoots ρ xs vs → x ∈ xs →
      ∃ vs', EnvRoots ρ (xs.erase x) vs' ∧ SameRefs vs (v :: vs')
  | [], _, _, hm => by cases hm
  | y :: ys, vs, h, hm => by
    obtain ⟨u, us, hy, hus, rfl⟩ := EnvRoots.cons_iff.mp h
    by_cases he : y = x
    · subst he
      have : u = v := Option.some.inj (hy.symm.trans hx)
      subst this
      exact ⟨us, by simpa [List.erase_cons_head] using hus, SameRefs.refl _⟩
    · have hm' : x ∈ ys := by
        rcases List.mem_cons.mp hm with h' | h'
        · exact absurd h'.symm he
        · exact h'
      obtain ⟨vs', hr, hs⟩ := EnvRoots.erase hx hus hm'
      have hne : (y == x) = false := by simpa using he
      refine ⟨u :: vs', ?_, ?_⟩
      · rw [List.erase_cons, hne]
        exact EnvRoots.cons hy hr
      · intro l
        have := hs l
        simp only [refsIn] at this ⊢
        omega

/-- Dropping the tokens of a variable whose value is an immediate. -/
theorem EnvRoots.filter_imm {ρ : Own.Env} {x : Var} {v : RVal} (hx : ρ.get? x = some v)
    (hv : ImmVal v) :
    ∀ {xs : List Var} {vs : List RVal}, EnvRoots ρ xs vs →
      ∃ vs', EnvRoots ρ (xs.filter (fun y => y != x)) vs' ∧ SameRefs vs vs'
  | [], vs, h => ⟨[], rfl, by cases h; exact SameRefs.refl _⟩
  | y :: ys, vs, h => by
    obtain ⟨u, us, hy, hus, rfl⟩ := EnvRoots.cons_iff.mp h
    obtain ⟨vs', hr, hs⟩ := EnvRoots.filter_imm hx hv hus
    by_cases he : y = x
    · subst he
      have : u = v := Option.some.inj (hy.symm.trans hx)
      subst this
      refine ⟨vs', by simpa [List.filter_cons] using hr, ?_⟩
      exact (SameRefs.imm_cons hv us).trans hs
    · refine ⟨u :: vs', ?_, SameRefs.cons u hs⟩
      have hf : (y :: ys).filter (fun z => z != x) = y :: ys.filter (fun z => z != x) := by
        simp [List.filter_cons, he]
      rw [hf]
      exact EnvRoots.cons hy hr

/-- Lookups of variables other than a fresh one are unchanged. -/
theorem EnvRoots.insert_fresh {ρ : Own.Env} {xs : List Var} {vs : List RVal}
    (h : EnvRoots ρ xs vs) (x : Var) (v : RVal) (hx : x ∉ xs) : EnvRoots (ρ.insert x v) xs vs := by
  unfold EnvRoots at h ⊢
  rw [evalVars_congr (ρ.insert x v) ρ xs (fun y hy =>
    Src.NatMap.get?_insert_ne _ _ (by intro he; subst y; exact hx hy))]
  exact h

theorem EnvRoots.congr {ρ ρ' : Own.Env} {xs : List Var} {vs : List RVal}
    (h : EnvRoots ρ xs vs) (he : ∀ y, y ∈ xs → ρ'.get? y = ρ.get? y) : EnvRoots ρ' xs vs := by
  unfold EnvRoots at h ⊢
  rw [evalVars_congr ρ' ρ xs he]
  exact h

end IxCC.Own.Plain
