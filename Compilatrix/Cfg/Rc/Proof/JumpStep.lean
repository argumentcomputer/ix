import Compilatrix.Cfg.Rc.Proof.State

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc
open Cfg.Proof (Impl spine)

/-- Restore a saved lexical environment through the actual lowered edge. Its
first entry is free; a recursive re-entry preserves the source charge flag. -/
theorem At.jump {F : Fir.Program} {P : Program} {fr : Frame} {ρ : Own.Env}
    {saved rest : List Own.Plain.JEntry} {j : Fir.JoinId} {args : List Fir.Arg}
    (stateRel : At F P fr ρ saved (.jmp j args)) {e : Own.Plain.JEntry}
    (found : Own.Plain.lookupJ j saved = some (e, rest)) {vs : List Own.RVal}
    (values : Own.evalArgs ρ args = some vs) (arity : vs.length = e.params.length)
    (stk : List (Frame × Fir.Var)) (H : Own.Heap) :
    ∃ after, step P (.run fr stk H) = .next (.run after stk H) e.charged ∧
      At F P after (Own.bindAll e.env e.params vs) (e.after rest) e.body := by
  obtain ⟨fd, scope, params, acc, next, first, lo, lookup, range, layout, cursor,
    env, below, scopedNames, joins⟩ := stateRel
  obtain ⟨bj, scope', ps, loEntry, loBody, bodyFirst, label, idEq, previous, lower,
    paramsEq, chargeRec, bodyLayout, savedSub, savedBelow, psLower, bound, psUpper, bodyNames⟩ := joins.lookup found
  simp only [skeleton, Impl] at layout
  simp only [skeleton, spine] at cursor
  obtain ⟨term, targetBlock⟩ := Cfg.Proof.impl_head bodyLayout
  have length : vs.length = ps.length := by rw [arity, paramsEq]; simp
  let after : Frame := { fr with
    blk := bj
    rest := spine (skeleton P.base.size bodyFirst e.body)
    env := Own.bindAll fr.env (ps.map (·.1)) vs }
  refine ⟨after, ?_, ?_⟩
  · simp only [step, cursor]
    rw [Cfg.Proof.step_run_term cursor lookup layout]
    simp only [Cfg.Proof.termStep, Cfg.Proof.jumpTerm, label]
    rw [Cfg.Proof.takeEdge_eq targetBlock (Cfg.Proof.evalArgs_sub env values) length]
    simp [after]
  · refine ⟨fd, _, ps, [], bj + 1, bodyFirst, loBody, lookup, range, bodyLayout, rfl, ?_, ?_, bodyNames, ?_⟩
    · rw [paramsEq]
      exact Cfg.Proof.Sub.bindAll savedSub _ _
    · apply Cfg.Proof.below_bindAll (fun y v hy => Nat.lt_of_lt_of_le (savedBelow y v hy) bound) ?_ vs
      intro y hy
      rw [paramsEq] at hy
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
      exact psUpper p hp
    · have agree : ∀ y, y < loEntry → (Own.bindAll fr.env (ps.map (·.1)) vs).get? y = fr.env.get? y := by
        intro y hy
        apply Cfg.Proof.bindAll_get_notin
        intro mem
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp mem
        exact (Nat.not_lt_of_ge (psLower p hp)) hy
      have tail := (previous.agree agree).mono bound
      unfold Own.Plain.JEntry.after
      cases recCase : e.isRec with
      | false => simpa [recCase] using tail
      | true =>
        simp only [↓reduceIte]
        have self := Joins.cons (e := { e with charged := true }) (ps := ps) (bj := bj)
          (previous.agree agree) bound paramsEq (fun _ => recCase)
          (by simpa [recCase] using bodyLayout)
          (fun y v hy => by rw [agree y (savedBelow y v hy)]; exact savedSub y v hy)
          savedBelow psLower bound psUpper bodyNames
        simpa [recCase] using self


end Compilatrix.Cfg.Rc
