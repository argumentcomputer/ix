import Compilatrix.Cfg.Rc.Proof.State

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc
open Compilatrix.Sem (Result)
open Cfg.Proof (Below Impl spine)

theorem generate_tables {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (h : generate F bodies = some P) :
    P.base.tables = ({ ctors := F.ctors, known := F.known } : Own.Tables) := by
  unfold generate at h
  cases he : entries F bodies (List.range F.size) with
  | none => simp [he] at h
  | some es =>
    simp only [he, bind, Option.bind, Option.some.injEq] at h
    subst P
    rfl

/-- All non-call computations reuse the existing counted Cfg RHS operation.
Only real variable x is inserted, preserving saved join environments below the
checked real-name bound. Allocation and borrowed projection are not erased. -/
theorem At.bind {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true) {fr : Frame} {ρ : Own.Env}
    {saved : List Own.Plain.JEntry} {x : Fir.Var} {rhs : Fir.Rhs} {k : Own.Plain.Code}
    (stateRel : At F P fr ρ saved (.bind x rhs k))
    (noCall : ∀ f args, rhs ≠ .call f args)
    {stk : List (Frame × Fir.Var)} {H H' : Own.Heap} {v : Own.RVal}
    (effect : Own.Plain.evalRhs { ctors := F.ctors, known := F.known } ρ H rhs = .ok (v, H')) :
    ∃ after, step P (.run fr stk H) = .next (.run after stk H') false ∧
      At F P after (ρ.insert x v) saved k := by
  obtain ⟨fd, scope, params, acc, next, first, lo, lookup, range, layout, cursor,
    env, below, scopedNames, joins⟩ := stateRel
  simp only [names, Bool.and_eq_true, decide_eq_true_eq] at scopedNames
  change Impl fd.block? fr.fn scope fr.blk params (.bind x (Own.immRhs rhs) :: acc) next
    (skeleton P.base.size first k) at layout
  change fr.rest = .bind x (Own.immRhs rhs) :: spine (skeleton P.base.size first k) at cursor
  have ordinary : ∀ f args, Own.immRhs rhs ≠ .fir (.call f args) := by
    cases rhs <;> simp_all [Own.immRhs]
  have unreserved : reserved P.base.size (.bind x (Own.immRhs rhs)) = false := by
    cases rhs <;> simp_all [Own.immRhs, reserved]
  have effectOwn : Own.evalRhs .rc { ctors := F.ctors, known := F.known } ρ H (Own.immRhs rhs) = .ok (v, H') := by
    cases rhs <;> simpa only [Own.Plain.evalRhs, Own.immRhs] using effect
  have tables := generate_tables (checkProgram_parts (checkScopedProgram_parts checked).1).2
  have targetEffect : Own.evalRhs .rc P.base.tables fr.env H (Own.immRhs rhs) = .ok (v, H') := by
    rw [tables]
    exact Cfg.Proof.evalRhs_sub_ok env effectOwn
  let after : Frame := {
    fr with
    rest := spine (skeleton P.base.size first k)
    env := fr.env.insert x v }
  refine ⟨after, ?_, ?_⟩
  · rw [step_ordinary cursor unreserved, Cfg.Proof.step_run_bind cursor ordinary, targetEffect]
  · refine ⟨fd, scope, params, .bind x (Own.immRhs rhs) :: acc, next, first, x + 1,
      lookup, range, layout, rfl, Cfg.Proof.Sub.insert env x v, ?_, scopedNames.2, ?_⟩
    · intro y value hy
      by_cases eq : y = x
      · subst y; exact Nat.lt_succ_self x
      · rw [Src.NatMap.get?_insert_ne _ _ eq] at hy
        exact Nat.lt_of_lt_of_le (below y value hy) (by omega)
    · apply (joins.agree ?_).mono (show lo ≤ x + 1 by omega)
      intro y hy
      exact Src.NatMap.get?_insert_ne _ _ (by omega : y ≠ x)


end Compilatrix.Cfg.Rc
