import IxCC.Own.Plain.Proof.Bounds

/-! Successful checked heap operations preserve shape even when no Balance
premise is supplied. This lets the independent evaluator shape induction
cover the actual target execution, including source-stuck cases. -/

set_option autoImplicit false
namespace IxCC.Own.Rc

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

end IxCC.Own.Rc

namespace IxCC.Own.Plain
open Rc
open IxCC.Sem (Result)

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

theorem incList_shape : ∀ {H H' : Heap} {vs : List RVal},
    HeapOk H → incList H vs = some H' → HeapOk H' ∧ H'.size = H.size
  | H, H', [], hh, hop => by cases hop; exact ⟨hh, rfl⟩
  | H, H', v :: vs, hh, hop => by
    simp only [incList, bind, Option.bind] at hop
    cases hi : inc H v 1 with
    | none => rw [hi] at hop; cases hop
    | some H₁ =>
      rw [hi] at hop
      obtain ⟨hh', hsz⟩ := incList_shape (changeCount_heapOk hh hi) hop
      exact ⟨hh', hsz.trans (changeCount_sameBodies hi).1.symm⟩

theorem reuseCell_shape {H H' : Heap} {l : Nat} {b' : Body} {v : RVal}
    (hh : HeapOk H) (hb : BodyOk H.size b') (hr : reuseCell H l b' = some (v, H')) :
    HeapOk H' ∧ H.size ≤ H'.size ∧ Bounded H'.size v := by
  simp only [reuseCell] at hr
  cases hc : H.cell? l with
  | none => simp [hc] at hr
  | some c =>
    cases c with
    | dead => simp [hc] at hr
    | live rc m old =>
      cases rc with
      | zero => simp [hc] at hr
      | succ r =>
        cases r with
        | succ _ => simp [hc] at hr
        | zero =>
          cases m with
          | static => simp [hc] at hr
          | dyn =>
            simp only [hc, Option.some.injEq] at hr
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
            have hl : l < H.size := Proof.cell?_some hc
            have hfree := heapOk_free hh hl
            have hb' : BodyOk (setCell H l .dead).size b' := by rwa [setCell_size]
            have hok' := heapOk_alloc hfree hb'
            have hsz := setCell_size H l .dead
            exact ⟨hok', by simp only [Heap.size, Array.size_push] at hsz ⊢; omega, by simp [Heap.size, Bounded]⟩

private theorem resetMask_shared_shape {H H' : Heap} {l : Nat} {liveFields : List RVal} {uniq : Bool} {sv : RVal}
    (hh : HeapOk H)
    (hop : (if uniq then .stuck else
      match incList H liveFields with
      | some H₁ => Result.ofOption ((Rc.dropAll H₁ [.loc l]).map (.erased, ·))
      | none => .stuck) = Result.ok (sv, H')) :
    HeapOk H' ∧ H.size ≤ H'.size ∧ Bounded H'.size sv := by
  cases uniq with
  | true => simp at hop
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hop
    cases hi : incList H liveFields with
    | none => simp [hi] at hop
    | some H₁ =>
      simp only [hi] at hop
      cases hd : dropAll H₁ [.loc l] with
      | none => simp [hd, Result.ofOption] at hop
      | some H₂ =>
        simp only [hd, Option.map_some, Result.ofOption, Result.ok.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        obtain ⟨hh₁, hsz₁⟩ := incList_shape hh hi
        obtain ⟨hh₂, hsz₂⟩ := dropAll_shape H₁ [.loc l] hh₁ hd
        exact ⟨hh₂, by omega, trivial⟩

theorem resetMask_shape {H H' : Heap} {ρ : Own.Env} {x : Fir.Var} {ctor : Fir.CtorInfo}
    {mask : Nat} {uniq : Bool} {sv : RVal}
    (hh : HeapOk H) (hop : evalResetMask ρ H x ctor mask uniq = .ok (sv, H')) :
    HeapOk H' ∧ H.size ≤ H'.size ∧ Bounded H'.size sv := by
  unfold evalResetMask at hop
  by_cases hfl : ctor.fieldless = true
  · simp [hfl] at hop
  · have hpos : 0 < ctor.arity := by
      simp only [Fir.CtorInfo.fieldless, beq_iff_eq] at hfl; omega
    simp only [hfl, Bool.false_eq_true, ↓reduceIte] at hop
    cases hx : ρ.get? x with
    | none => simp [hx] at hop
    | some v =>
      simp only [hx] at hop
      cases v with
      | lit _ | ctor0 _ | erased =>
        dsimp only at hop
        split at hop
        · cases hop
        · simp only [Result.ok.injEq, Prod.mk.injEq] at hop
          obtain ⟨rfl, rfl⟩ := hop
          exact ⟨hh, Nat.le_refl _, trivial⟩
      | loc l =>
        cases hc : H.cell? l with
        | none => simp [hc] at hop
        | some cell =>
          simp only [hc] at hop
          cases cell with
          | dead => cases hop
          | live rc m b =>
            cases rc with
            | zero => exact resetMask_shared_shape hh hop
            | succ r =>
              cases r with
              | zero =>
                cases m with
                | dyn =>
                  cases hr : reuseCell H l (resetShell ctor) with
                  | none => simp [hr] at hop
                  | some p =>
                    simp only [hr] at hop
                    cases hd : dropAll p.2 ((b.fields.zipIdx).filterMap fun x =>
                        if (!mask.testBit x.2) = true then some x.1 else none) with
                    | none => simp only [hd, Option.map_none, Result.ofOption] at hop; cases hop
                    | some H₂ =>
                      simp only [hd, Option.map_some, Result.ofOption, Result.ok.injEq, Prod.mk.injEq] at hop
                      obtain ⟨rfl, rfl⟩ := hop
                      have hb : BodyOk H.size (resetShell ctor) :=
                        ⟨by simp [resetShell], hpos, fun k hk => by simp [resetShell] at hk⟩
                      obtain ⟨hh₁, hsz₁, hbd₁⟩ := reuseCell_shape hh hb hr
                      obtain ⟨hh₂, hsz₂⟩ := dropAll_shape p.2 _ hh₁ hd
                      exact ⟨hh₂, by omega, by rwa [hsz₂]⟩
                | static => exact resetMask_shared_shape hh hop
              | succ _ => exact resetMask_shared_shape hh hop

theorem reuseVal_shape {H H' : Heap} {ρ : Own.Env} {sv v : RVal} {ctor : Fir.CtorInfo}
    {args : List Fir.Arg} {uniq : Bool}
    (hh : HeapOk H) (henv : EnvBounded H.size ρ)
    (hop : evalReuseVal ρ H sv ctor args uniq = .ok (v, H')) :
    HeapOk H' ∧ H.size ≤ H'.size ∧ Bounded H'.size v := by
  unfold evalReuseVal at hop
  cases ha : Own.evalArgs ρ args with
  | none => simp [ha] at hop
  | some vs =>
    simp only [ha] at hop
    split at hop
    · next hcond =>
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcond
      obtain ⟨hfl, hlen⟩ := hcond
      have hpos : 0 < ctor.arity := by
        simp only [Fir.CtorInfo.fieldless, beq_eq_false_iff_ne] at hfl; omega
      have hbody : BodyOk H.size { ctor, fields := vs } :=
        ⟨hlen, hpos, fun k hk => henv.args args ha (.loc k) hk⟩
      cases sv with
      | loc l =>
        cases hr : reuseCell H l { ctor, fields := vs } with
        | none => simp [hr, Result.ofOption] at hop
        | some p =>
          simp only [hr, Result.ofOption, Result.ok.injEq] at hop
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hop
          exact reuseCell_shape hh hbody hr
      | erased =>
        cases uniq with
        | true => simp at hop
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at hop
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hop
          exact ⟨heapOk_alloc hh hbody, by simp [Heap.size], by simp [Heap.size, Bounded]⟩
      | lit _ | ctor0 _ => cases hop
    · cases hop

theorem dropVal_shape {H H' : Heap} {sv : RVal}
    (hh : HeapOk H) (hop : evalDropVal H sv = .ok H') : HeapOk H' ∧ H'.size = H.size := by
  unfold evalDropVal at hop
  cases hd : dropAll H [sv] with
  | none => simp [hd, Result.ofOption] at hop
  | some H₁ =>
    simp only [hd, Result.ofOption, Result.ok.injEq] at hop
    subst H'
    exact dropAll_shape H [sv] hh hd

end IxCC.Own.Plain
