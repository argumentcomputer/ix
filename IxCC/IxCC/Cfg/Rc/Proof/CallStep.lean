import IxCC.Cfg.Rc.Proof.State

set_option autoImplicit false
namespace IxCC.Cfg.Rc
open Cfg.Proof (Impl spine)

/-- A suspended real binding can accept any returned owned value. The result
write preserves all saved lexical environments by the admitted naming bound. -/
theorem At.bind_continuation {F : Fir.Program} {P : Program} {fr : Frame} {ρ : Own.Env}
    {saved : List Own.Plain.JEntry} {x : Fir.Var} {rhs : Fir.Rhs} {k : Own.Plain.Code}
    {slots : Src.NatMap Own.RVal}
    (stateRel : At F P fr ρ saved (.bind x rhs k) slots) :
    ∃ rest, fr.rest = .bind x (Own.immRhs rhs) :: rest ∧
      ∀ v, At F P { fr with rest, env := fr.env.insert x v } (ρ.insert x v) saved k slots := by
  obtain ⟨fd, scope, params, acc, next, first, lo, slotBase, lookup, range, layout, cursor,
    env, below, loSlot, slotSub, scopedNames, vb, rc, joins⟩ := stateRel
  simp only [names, Bool.and_eq_true, decide_eq_true_eq] at scopedNames
  simp only [varsBelow, Bool.and_eq_true, decide_eq_true_eq] at vb
  change Impl fd.block? fr.fn scope fr.blk params (.bind x (Own.immRhs rhs) :: acc) next
    (skeleton P.base.size first k F.ctors slotBase) at layout
  change fr.rest = .bind x (Own.immRhs rhs) :: spine (skeleton P.base.size first k F.ctors slotBase) at cursor
  refine ⟨_, cursor, fun v => ?_⟩
  refine ⟨fd, scope, params, .bind x (Own.immRhs rhs) :: acc, next, first, x + 1, slotBase,
    lookup, range, layout, rfl, Cfg.Proof.Sub.insert env x v, ?_, vb.1,
    slotSub.insert_var vb.1 v, scopedNames.2, vb.2, rc, ?_⟩
  · intro y value hy
    by_cases eq : y = x
    · subst y; exact Nat.lt_succ_self x
    · rw [Src.NatMap.get?_insert_ne _ _ eq] at hy
      exact Nat.lt_of_lt_of_le (below y value hy) (by omega)
  · apply (joins.agree ?_).mono (show lo ≤ x + 1 by omega)
    intro y hy
    exact Src.NatMap.get?_insert_ne _ _ (by omega : y ≠ x)

theorem At.call_step {F : Fir.Program} {P : Program} {fr : Frame} {ρ : Own.Env}
    {saved : List Own.Plain.JEntry} {x f : Nat} {args : List Fir.Arg} {k : Own.Plain.Code}
    {slots : Src.NatMap Own.RVal}
    (stateRel : At F P fr ρ saved (.bind x (.call f args) k) slots)
    (range : f < P.base.size) {vs : List Own.RVal} (values : Own.evalArgs ρ args = some vs)
    (stk : List (Frame × Fir.Var)) (H : Own.Heap) :
    ∃ continuation, step P (.run fr stk H) =
      .next (.call f vs ((continuation, x) :: stk) H) false ∧
      ∀ v, At F P { continuation with env := continuation.env.insert x v } (ρ.insert x v) saved k slots := by
  obtain ⟨rest, cursor, resume⟩ := stateRel.bind_continuation
  obtain ⟨fd, scope, params, acc, next, first, lo, slotBase, lookup, sourceRange, layout, sourceCursor,
    env, below, loSlot, slotSub, scopedNames, vb, rc, joins⟩ := stateRel
  have ordinary : reserved P.base.size (.bind x (Own.immRhs (.call f args))) = false := by
    simp [Own.immRhs, reserved, show f ≠ P.base.size by omega,
      show f ≠ P.base.size + 1 by omega]
  have nonReuse : isReuseOp P.base.size (.bind x (Own.immRhs (.call f args))) = false := by
    simp [Own.immRhs, isReuseOp, show f ≠ P.base.size + 2 by omega,
      show f ≠ P.base.size + 3 by omega]
  refine ⟨{ fr with rest }, ?_, resume⟩
  rw [step_ordinary cursor ordinary nonReuse]
  exact Cfg.Proof.step_run_call cursor (Cfg.Proof.evalArgs_sub env values)



end IxCC.Cfg.Rc
