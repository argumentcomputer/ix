import Compilatrix.Own.Plain.Proof.Bounds

/-! Successful checked heap operations preserve shape even when no Balance
premise is supplied. This lets the independent evaluator shape induction
cover the actual target execution, including source-stuck cases. -/

set_option autoImplicit false
namespace Compilatrix.Own.Rc

theorem changeCount_heapOk {H H' : Heap} {v : RVal} {f : Nat → Option Nat}
    (hh : HeapOk H) (hop : changeCount f H v = some H') : HeapOk H' := by
  cases v with
  | loc l =>
    simp only [changeCount] at hop
    split at hop
    · next rc b hc =>
      split at hop
      · cases hop
      · cases hf : f rc with
        | none => simp [hf] at hop
        | some rc' =>
          simp only [hf, bind, Option.bind] at hop
          split at hop
          · cases hop
          · next hp =>
            cases hop
            exact heapOk_set_count hh hc (by simp only [beq_iff_eq] at hp; omega)
    · cases hop; exact hh
    · cases hop
  | lit _ | ctor0 _ | erased => cases hop; exact hh

theorem releaseOne_size {H H' : Heap} {v : RVal} {pending pending' : List RVal}
    (hop : releaseOne H v pending = some (H', pending')) : H'.size = H.size := by
  cases v with
  | loc l =>
    simp only [releaseOne] at hop
    split at hop <;> simp_all
    all_goals rw [← hop.1]; exact setCell_size ..
  | lit _ | ctor0 _ | erased =>
    simp only [releaseOne, Option.some.injEq, Prod.mk.injEq] at hop
    rcases hop with ⟨rfl, rfl⟩
    rfl

theorem dropAll_shape (H : Heap) (pending : List RVal) {H' : Heap}
    (hh : HeapOk H) (hop : dropAll H pending = some H') : HeapOk H' ∧ H'.size = H.size := by
  match hPending : pending with
  | [] =>
    simp only [dropAll] at hop
    cases hop
    exact ⟨hh, rfl⟩
  | v :: ps =>
    rw [dropAll] at hop
    cases hstep : releaseOne H v ps with
    | none => rw [hstep] at hop; cases hop
    | some pair =>
      obtain ⟨H₁, ps'⟩ := pair
      rw [hstep] at hop
      have hdrop : dropAll H₁ ps' = some H' := hop
      obtain ⟨shape, size⟩ := dropAll_shape H₁ ps' (releaseOne_heapOk hh hstep) hdrop
      exact ⟨shape, size.trans (releaseOne_size hstep)⟩
termination_by (mass H, pending.length)
decreasing_by
  have hd := Prod.lex_def.mp (releaseOne_decreases hstep)
  apply Prod.lex_def.mpr
  rcases hd with hd | ⟨he, hd⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨he, by omega⟩

end Compilatrix.Own.Rc

namespace Compilatrix.Own.Plain
open Rc
open Compilatrix.Sem (Result)

theorem action_shape {H H' : Heap} {ρ : Own.Env} {a : Action}
    (hh : HeapOk H) (hop : evalAction ρ H a = .ok H') : HeapOk H' ∧ H'.size = H.size := by
  cases a with
  | inc x n =>
    cases hx : ρ.get? x with
    | none => simp [evalAction, hx] at hop
    | some v =>
      cases hi : inc H v n with
      | none => simp [evalAction, hx, hi, Result.ofOption] at hop
      | some H₁ =>
        simp only [evalAction, hx, hi, Result.ofOption, Result.ok.injEq] at hop
        subst H'
        exact ⟨changeCount_heapOk hh hi, (changeCount_sameBodies hi).1.symm⟩
  | dec x =>
    cases hx : ρ.get? x with
    | none => simp [evalAction, hx] at hop
    | some v =>
      cases hd : dropAll H [v] with
      | none => simp [evalAction, hx, hd, Result.ofOption] at hop
      | some H₁ =>
        simp only [evalAction, hx, hd, Result.ofOption, Result.ok.injEq] at hop
        subst H'
        exact dropAll_shape H [v] hh hd

end Compilatrix.Own.Plain
