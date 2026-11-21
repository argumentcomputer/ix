import Aiur.Generic.ControlBranchFacts
import Aiur.Generic.ControlNoExit
import Aiur.Generic.PreparationPatternFacts

namespace Aiur.Generic.ControlLower
open SourceSemantics OpenSource
variable {F : Type} [Field F] [DecidableEq F]
variable {world : SourceSemantics.World F} {calls : CallRelation F}

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

mutual
/-- Concrete continuations preserve normal and abrupt source execution,
including the exact heap and every call premise. -/
theorem expression_correct {env : Renaming} {expr code : Expr F}
    {next : Continuation F} {handlers : Handlers F}
    (built : expression fuel env expr next handlers = .ok code) :
    Correct world calls env expr code next handlers := by
  intro source target before result after scope
  cases fuel with
  | zero => simp [expression] at built
  | succ fuel =>
    cases expr with
    | literal value =>
        simp only [expression, except_pure_ok] at built
        subst code
        rw [eval_apply_exec, exec_literal, exec_literal]
    | var name =>
        cases found : env.lookup name with
        | none => simp [expression, found] at built
        | some renamed =>
            simp only [expression, found, except_pure_ok] at built
            subst code
            rw [eval_apply_exec, exec_var, exec_var]
            simp only [find_lookup_some, scope name renamed found]
    | global name type => simp [expression] at built
    | control kind body =>
        cases kind with
        | block label =>
            rw [expression] at built
            rw [expression_correct built _ _ _ _ _ scope, exec_block]
            apply Exec.congr (fun _ _ => Iff.rfl)
            intro t v h
            by_cases same : t = .block label
            · subst t; simp [Handlers.run]
            · simp [Handlers.run, List.lookup_cons, beq_eq_false_iff_ne.mpr same, same]
        | exit t =>
            cases found : handlers.lookup t with
            | none => simp [expression, found] at built
            | some handler =>
                simp only [expression, found] at built
                rw [expression_correct built _ _ _ _ _ scope, exec_exit]
                apply Exec.congr ?_ (fun _ _ _ => Iff.rfl)
                intro v h
                simp [Handlers.run, found]
    | tuple xs =>
        rw [expression] at built
        rw [arguments_correct built _ _ _ _ _ scope, exec_tuple]
    | array xs =>
        rw [expression] at built
        rw [arguments_correct built _ _ _ _ _ scope, exec_array]
    | «repeat» x n =>
        simp only [expression, except_bind_ok] at built
        obtain ⟨input, freshInput, child⟩ := built
        have fresh := fresh_reserved (fresh_ok freshInput)
        rw [expression_correct child _ _ _ _ _ scope, exec_repeat]
        apply Exec.congr ?_ (fun _ _ _ => Iff.rfl)
        intro v h
        exact run_repeat fresh.next
    | index x i =>
        simp only [expression, except_bind_ok] at built
        obtain ⟨input, freshInput, child⟩ := built
        have fresh := fresh_reserved (fresh_ok freshInput)
        rw [expression_correct child _ _ _ _ _ scope, exec_index]
        apply Exec.congr ?_ (fun _ _ _ => Iff.rfl)
        intro v h
        exact run_index fresh.next
    | slice x start stop =>
        simp only [expression, except_bind_ok] at built
        obtain ⟨input, freshInput, child⟩ := built
        have fresh := fresh_reserved (fresh_ok freshInput)
        rw [expression_correct child _ _ _ _ _ scope, exec_slice]
        apply Exec.congr ?_ (fun _ _ _ => Iff.rfl)
        intro v h
        exact run_slice fresh.next
    | project x i =>
        simp only [expression, except_bind_ok] at built
        obtain ⟨input, freshInput, child⟩ := built
        have fresh := fresh_reserved (fresh_ok freshInput)
        rw [expression_correct child _ _ _ _ _ scope, exec_project]
        apply Exec.congr ?_ (fun _ _ _ => Iff.rfl)
        intro v h
        exact run_project fresh.next
    | member x field =>
        simp only [expression, except_bind_ok] at built
        obtain ⟨input, freshInput, child⟩ := built
        have fresh := fresh_reserved (fresh_ok freshInput)
        rw [expression_correct child _ _ _ _ _ scope, exec_member]
        apply Exec.congr ?_ (fun _ _ _ => Iff.rfl)
        intro v h
        exact run_member fresh.next
    | store x =>
        simp only [expression, except_bind_ok] at built
        obtain ⟨input, freshInput, child⟩ := built
        have fresh := fresh_reserved (fresh_ok freshInput)
        rw [expression_correct child _ _ _ _ _ scope, exec_store]
        apply Exec.congr ?_ (fun _ _ _ => Iff.rfl)
        intro v h
        exact run_store fresh.next
    | load x =>
        simp only [expression, except_bind_ok] at built
        obtain ⟨input, freshInput, child⟩ := built
        have fresh := fresh_reserved (fresh_ok freshInput)
        rw [expression_correct child _ _ _ _ _ scope, exec_load]
        apply Exec.congr ?_ (fun _ _ _ => Iff.rfl)
        intro v h
        exact run_load fresh.next
    | hint type x channel =>
        simp only [expression, except_bind_ok] at built
        obtain ⟨input, freshInput, child⟩ := built
        have fresh := fresh_reserved (fresh_ok freshInput)
        rw [expression_correct child _ _ _ _ _ scope, exec_hint]
        apply Exec.congr ?_ (fun _ _ _ => Iff.rfl)
        intro v h
        simpa only [Ty.subst_nil] using (run_hint (world := world) (calls := calls) (locals := target) (type := type) (value := v) (before := h) (result := result) (after := after) fresh.next)
    | neg x =>
        simp only [expression, except_bind_ok] at built
        obtain ⟨input, freshInput, child⟩ := built
        have fresh := fresh_reserved (fresh_ok freshInput)
        rw [expression_correct child _ _ _ _ _ scope, exec_neg]
        apply Exec.congr ?_ (fun _ _ _ => Iff.rfl)
        intro v h
        exact run_neg fresh.next
    | construct name types ctor xs =>
        simp only [expression, except_bind_ok] at built
        obtain ⟨input, freshInput, child⟩ := built
        have fresh := fresh_reserved (fresh_ok freshInput)
        rw [arguments_correct child _ _ _ _ _ scope, exec_construct]
        apply ExecArgs.congr_length ?_ (fun _ _ _ => Iff.rfl)
        intro vs h length
        rw [← length]
        exact run_construct fresh.next
    | constructAs params type ctor xs =>
        simp only [expression, except_bind_ok] at built
        obtain ⟨input, freshInput, child⟩ := built
        have fresh := fresh_reserved (fresh_ok freshInput)
        rw [arguments_correct child _ _ _ _ _ scope, exec_constructAs]
        apply ExecArgs.congr_length ?_ (fun _ _ _ => Iff.rfl)
        intro vs h length
        rw [← length]
        exact run_constructAs fresh.next
    | builtin paths xs =>
        simp only [expression, except_bind_ok] at built
        obtain ⟨input, freshInput, child⟩ := built
        have fresh := fresh_reserved (fresh_ok freshInput)
        rw [arguments_correct child _ _ _ _ _ scope, exec_builtin]
        apply ExecArgs.congr_length ?_ (fun _ _ _ => Iff.rfl)
        intro vs h length
        rw [← length]
        exact run_builtin fresh.next
    | update paths xs =>
        simp only [expression, except_bind_ok] at built
        obtain ⟨input, freshInput, child⟩ := built
        have fresh := fresh_reserved (fresh_ok freshInput)
        rw [arguments_correct child _ _ _ _ _ scope, exec_update]
        apply ExecArgs.congr_length ?_ (fun _ _ _ => Iff.rfl)
        intro vs h length
        rw [← length]
        exact run_update fresh.next
    | record head xs =>
        simp only [expression, except_bind_ok] at built
        obtain ⟨input, freshInput, child⟩ := built
        have fresh := fresh_reserved (fresh_ok freshInput)
        rw [arguments_correct child _ _ _ _ _ scope, exec_record]
        apply ExecArgs.congr_length ?_ (fun _ _ _ => Iff.rfl)
        intro vs h length
        rw [← length]
        exact run_record fresh.next
    | call name types xs =>
        simp only [expression, except_bind_ok] at built
        obtain ⟨input, freshInput, child⟩ := built
        have fresh := fresh_reserved (fresh_ok freshInput)
        rw [arguments_correct child _ _ _ _ _ scope, exec_call]
        apply ExecArgs.congr_length ?_ (fun _ _ _ => Iff.rfl)
        intro vs h length
        rw [← length]
        exact run_call fresh.next
    | binary op x y =>
        simp only [expression, except_bind_ok] at built
        obtain ⟨left, freshLeft, right, freshRight, rest, rightBuilt, leftBuilt⟩ := built
        have fl := fresh_reserved (fresh_ok freshLeft)
        have fr := fresh_reserved (show right ∉ reserved env next handlers from
          fun h => fresh_ok freshRight (by simp [h]))
        have different : left ≠ right := by intro h; subst right; exact fresh_ok freshRight (by simp)
        rw [expression_correct leftBuilt _ _ _ _ _ scope, exec_binary]
        apply Exec.congr ?_ (fun _ _ _ => Iff.rfl)
        intro v h
        change OpenSource.EvalExpr _ _ _ _ rest _ _ _ ↔ _
        rw [expression_correct rightBuilt _ _ _ _ _ (scope.add fl.scope v)]
        apply Exec.congr ?_ ?_
        · intro w a; exact run_binary fl.next fr.next different
        · intro t w a; exact Handlers.run_add fl.handlers
    | letValue pat x body =>
        simp only [expression, except_bind_ok] at built
        obtain ⟨bound, boundBuilt, input, freshInput, rest, bodyBuilt, xBuilt⟩ := built
        have fresh := fresh_reserved (show input ∉ reserved env next handlers from
          fun h => fresh_ok freshInput (by simp [h]))
        rw [expression_correct xBuilt _ _ _ _ _ scope, exec_let]
        apply Exec.congr ?_ (fun _ _ _ => Iff.rfl)
        intro v h
        change OpenSource.EvalExpr _ _ _ _ (.letValue _ (.var input) rest) _ _ _ ↔ _
        rw [eval_let_var]
        exact branch_iff boundBuilt (expression_correct bodyBuilt) fresh scope
    | matchValue x arms =>
        simp only [expression, except_bind_ok] at built
        obtain ⟨input, freshInput, compiledArms, armsBuilt, xBuilt⟩ := built
        have fresh := fresh_reserved (fresh_ok freshInput)
        rw [expression_correct xBuilt _ _ _ _ _ scope, exec_match]
        apply Exec.congr ?_ (fun _ _ _ => Iff.rfl)
        intro v h
        change OpenSource.EvalExpr _ _ _ _ (.matchValue (.var input) compiledArms) _ _ _ ↔ _
        rw [eval_match_var]
        change Selected _ _ _ _ _ ↔ Selected _ _ _ _ _
        apply Iff.symm
        apply selected_congr
        apply (Preparation.mapM_relation armsBuilt).imp
        intro a b built
        rcases a with ⟨pat, body⟩
        simp only [except_bind_ok, except_pure_ok] at built
        obtain ⟨bound, boundBuilt, rest, bodyBuilt, rfl⟩ := built
        exact ⟨(branch_iff boundBuilt (expression_correct bodyBuilt) fresh scope).symm,
          (renamed_none (bindings_ok boundBuilt).1).symm⟩
termination_by fuel

theorem arguments_correct {env : Renaming} {exprs : List (Expr F)} {code : Expr F}
    {next : Continuation F} {handlers : Handlers F}
    (built : arguments fuel env exprs next handlers = .ok code) :
    ArgsCorrect world calls env exprs code next handlers := by
  intro source target before result after scope
  cases fuel with
  | zero => simp [arguments] at built
  | succ fuel =>
    cases exprs with
    | nil =>
        simp only [arguments, except_pure_ok] at built
        subst code
        rw [eval_apply_exec, exec_tuple, execArgs_nil, execArgs_nil]
    | cons first rest =>
        simp only [arguments, except_bind_ok] at built
        obtain ⟨head, freshHead, tail, freshTail, remaining, tailBuilt, headBuilt⟩ := built
        have fh := fresh_reserved (fresh_ok freshHead)
        have ft := fresh_reserved (show tail ∉ reserved env next handlers from
          fun h => fresh_ok freshTail (by simp [h]))
        have different : head ≠ tail := by intro h; subst tail; exact fresh_ok freshTail (by simp)
        rw [expression_correct headBuilt _ _ _ _ _ scope, execArgs_cons]
        apply Exec.congr ?_ (fun _ _ _ => Iff.rfl)
        intro v h
        change OpenSource.EvalExpr _ _ _ _ remaining _ _ _ ↔ _
        rw [arguments_correct tailBuilt _ _ _ _ _ (scope.add fh.scope v)]
        apply ExecArgs.congr_length ?_ ?_
        · intro vs a length
          rw [← length]
          exact run_arguments fh.next ft.next different
        · intro t w a; exact Handlers.run_add fh.handlers
termination_by fuel
end

/-- The final continuation simply returns its argument. -/
theorem run_identity :
    (Continuation.mk name (.var name)).run world calls locals value before result after ↔
      value = result ∧ before = after := by
  constructor
  · intro h; cases h with
    | var found => exact ⟨by simpa using found, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .var (by simp)

/-- A compiled function catches exactly its own return. Named exits are
resolved lexically inside the function, never across a call boundary. -/
theorem function_correct (built : function expr parameters = .ok code) :
    OpenSource.EvalExpr world calls [] locals code before result after ↔
      OpenSource.EvalExpr world calls [] locals expr before result after ∨
      OpenSource.EvalExit world calls [] locals expr before .function result after := by
  unfold function at built
  split at built
  · rename_i absent
    have absent : hasControl expr = false := by simpa using absent
    obtain rfl := except_pure_ok.mp built
    constructor
    · exact Or.inl
    · rintro (normal | abrupt)
      · exact normal
      · exact (abrupt.hasControl absent).elim
  · simp only [except_bind_ok, except_pure_ok, exists_eq_left'] at built
    obtain ⟨_, _, name, fresh, compiled⟩ := built
    rw [expression_correct compiled _ _ _ _ _ (ScopeRel.identity parameters locals)]
    simp only [Exec, run_identity, Handlers.run, List.lookup_cons, List.lookup_nil]
    constructor
    · rintro (⟨v, h, ev, rfl, rfl⟩ | ⟨t, v, h, ev, k, found, post⟩)
      · exact .inl ev
      · cases t with
        | block label => cases found
        | function =>
            have same : k = ⟨name, .var name⟩ := by simpa using found.symm
            subst k
            obtain ⟨rfl, rfl⟩ := run_identity.mp post
            exact .inr ev
    · rintro (normal | abrupt)
      · exact .inl ⟨_, _, normal, rfl, rfl⟩
      · exact .inr ⟨.function, _, _, abrupt, ⟨name, .var name⟩, by simp,
          run_identity.mpr ⟨rfl, rfl⟩⟩

end Aiur.Generic.ControlLower
