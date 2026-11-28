import IxCC.Cfg.Rc.Run
import IxCC.Cfg.Rc.Proof.Ordered

set_option autoImplicit false
namespace IxCC.Cfg.Rc


theorem step_next_cases {P : Program} {s s' : State} {charge : Bool}
    (h : step P s = .next s' charge) :
    Cfg.step .rc P.base s = .next s' charge ∨
      ∃ fr stk H H' env' i rest, s = .run fr stk H ∧ fr.rest = i :: rest ∧
        s' = .run {fr with rest, env := env'} stk H' ∧ charge = false := by
  cases s with
  | call f args stk H => exact Or.inl h
  | ret v stk H => exact Or.inl h
  | run fr stk H =>
    cases cursor : fr.rest with
    | nil => exact Or.inl (by simpa only [step, cursor] using h)
    | cons i rest =>
      cases reservedHead : reserved P.base.size i with
      | false =>
        cases reuseHead : isReuseOp P.base.size i with
        | false =>
          exact Or.inl (by simpa only [step, cursor, reservedHead, reuseHead, Bool.false_eq_true, ↓reduceIte] using h)
        | true =>
          simp only [step, cursor, reservedHead, reuseHead, Bool.false_eq_true, ↓reduceIte] at h
          cases h1 : decodeReset P.base.size i with
          | none =>
            cases h2 : decodeReuse P.base.size i with
            | none => simp [h1, h2] at h
            | some p2 =>
              obtain ⟨dst, slotReg, ci, uniq, args⟩ := p2
              simp only [h1, h2] at h
              cases hc : heapCtorAt P.base.ctors ci with
              | none => simp [hc] at h
              | some ctor =>
                cases hsv : fr.env.get? slotReg with
                | none => simp [hc, hsv] at h
                | some sv =>
                  simp only [hc, hsv] at h
                  cases he : Own.Plain.evalReuseVal fr.env H sv ctor args uniq with
                  | ok res =>
                    simp only [he, Sem.Step.next.injEq] at h
                    exact Or.inr ⟨fr, stk, H, res.2, fr.env.insert dst res.1, i, rest, rfl, cursor, h.1.symm, h.2.symm⟩
                  | timeout | resource _ | trap | stuck => simp [he] at h
          | some p1 =>
            obtain ⟨slotReg, x, ci, mask, uniq⟩ := p1
            cases h2 : decodeReuse P.base.size i with
            | some _ => simp [h1, h2] at h
            | none =>
              simp only [h1, h2] at h
              cases hc : heapCtorAt P.base.ctors ci with
              | none => simp [hc] at h
              | some ctor =>
                simp only [hc] at h
                cases he : Own.Plain.evalResetMask fr.env H x ctor mask uniq with
                | ok res =>
                  simp only [he, Sem.Step.next.injEq] at h
                  exact Or.inr ⟨fr, stk, H, res.2, fr.env.insert slotReg res.1, i, rest, rfl, cursor, h.1.symm, h.2.symm⟩
                | timeout | resource _ | trap | stuck => simp [he] at h
      | true =>
        simp only [step, cursor, reservedHead, ↓reduceIte] at h
        cases decoded : decode P.base.size i with
        | none => simp [decoded] at h
        | some pair =>
          obtain ⟨slot, action⟩ := pair
          cases lookup : P.actions.get? fr.fn with
          | none => simp [decoded, lookup] at h
          | some table =>
            cases stored : table.get? slot with
            | none => simp [decoded, lookup, stored] at h
            | some a =>
              simp only [decoded, lookup, stored] at h
              split at h
              · cases effect : Own.Plain.evalAction fr.env H action with
                | ok H' =>
                  simp only [actionStep, effect, Sem.Step.next.injEq] at h
                  exact Or.inr ⟨fr, stk, H, H', fr.env, i, rest, rfl, cursor, h.1.symm, h.2.symm⟩
                | timeout | resource _ | trap | stuck => simp [actionStep, effect] at h
              · cases h

theorem potential_next {P : Program} (ordered : Cfg.Ordered P.base)
    {s s' : State} {charge : Bool} (h : step P s = .next s' charge) :
    (charge = false → Cfg.potential P.base s' < Cfg.potential P.base s) ∧
      Cfg.potential P.base s' ≤ Cfg.potential P.base s + (1 + P.base.instrs) := by
  rcases step_next_cases h with ordinary | ⟨fr, stk, H, H', env', i, rest, rfl, cursor, rfl, rfl⟩
  · exact Cfg.potential_next
      (fun hf _ _ _ hb he hback => ordered.forward hf hb he hback)
      (fun hf => Cfg.size_le_instrs ordered hf) ordinary
  · simp only [Cfg.potential, Cfg.framePot, cursor, List.length_cons]
    constructor
    · intro h; omega
    · omega

theorem potential_step {P : Program} (ordered : Cfg.Ordered P.base) :
    Sem.Potential (step P) (fun _ => True) (Cfg.potential P.base) (1 + P.base.instrs) where
  free _ h := ⟨trivial, (potential_next ordered h).1 rfl⟩
  charge _ h := ⟨trivial, (potential_next ordered h).2⟩

theorem runs_run {P : Program} (ordered : Cfg.Ordered P.base) (f : Nat)
    (args : List Own.RVal) (H : Own.Heap) :
    Sem.Runs (step P) (.call f args [] H) (fun clock => run P clock f args H) := fun clock =>
  (potential_step ordered).runClocked (s := .call f args [] H) trivial
    (by simpa [Cfg.potential, Cfg.stackPot] using Cfg.fuel_enough P.base clock)

end IxCC.Cfg.Rc
