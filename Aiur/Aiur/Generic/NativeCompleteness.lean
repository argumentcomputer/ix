import Aiur.Generic.LoweringCompleteness
import Aiur.Generic.PreparationFunctionFacts
import Aiur.Generic.SourceCallInduction
import Aiur.Generic.Correctness

namespace Aiur.Generic

theorem constantExpr_lower (value : Constant F) : (constantExpr value).lower [] = value.toExpr := by
  cases value with
  | field => simp only [constantExpr, Expr.lower, Constant.toExpr]
  | ptr _ address => exact Empty.elim address
  | tuple values | construct name ctor values =>
      simp only [constantExpr, Expr.lower, Constant.toExpr, Option.getD_some, List.map_nil,
        Instance.symbol, List.isEmpty_nil, ↓reduceIte, List.map_map]
      congr 1
      apply List.map_congr_left
      intro value hv
      exact constantExpr_lower value
termination_by sizeOf value

theorem constantExpr_safe (value : Constant F) : (constantExpr value).lowerSafe [] := by
  cases value with
  | field => simp only [constantExpr, Expr.lowerSafe]
  | ptr _ address => exact Empty.elim address
  | tuple values | construct name ctor values =>
      simp only [constantExpr, Expr.lowerSafe, List.forall_mem_map]
      intro value hv
      exact constantExpr_safe value
termination_by sizeOf value

theorem constantExpr_closed (value : Constant F) : Consts.Closed (constantExpr value) := by
  cases value with
  | field => simpa only [constantExpr] using (Consts.Closed.literal (F := F) (x := _))
  | ptr _ address => exact Empty.elim address
  | tuple values | construct name ctor values =>
      simp only [constantExpr]
      constructor
      intro expr member
      obtain ⟨value, hv, rfl⟩ := List.mem_map.mp member
      exact constantExpr_closed value
termination_by sizeOf value

theorem Specialized.prepare_complete [Field F] [DecidableEq F] {s : Source F}
    (q : Specialized s entries) (reachable : name ∈ callableNames q.program)
    (prepared : s.world.prepare name args = .ok (types, locals, expr))
    (evaluated : OpenSource.EvalExpr s.world (Engine.EvalFn s.coreWorld)
      types locals expr before result after ∨
      OpenSource.EvalExit s.world (Engine.EvalFn s.coreWorld) types locals expr before .function result after) :
    Engine.EvalFn s.coreWorld name args before result after := by
  cases compiled : s.compilerFunction? name with
  | none =>
      have sourceAbsent : s.program.sourceFunction? name = none := by
        have ready := q.loweringReady name reachable
        cases found : s.program.sourceFunction? name with
        | none => rfl
        | some _ => simp [found, compiled] at ready
      simp only [Source.world, sourceWorld, sourceAbsent, except_bind_ok, except_pure_ok,
        Prod.mk.injEq] at prepared
      obtain ⟨value, found, rfl, rfl, rfl⟩ := prepared
      have evaluated : OpenSource.EvalExpr s.world (Engine.EvalFn s.coreWorld) [] []
          (constantExpr value) before result after := by
        rcases evaluated with normal | abrupt
        · exact normal
        · exact (abrupt.hasControl (constantExpr_closed value).noControl).elim
      have lowered := lowering_complete (core := s.coreWorld) rfl evaluated (constantExpr_safe value)
      rw [constantExpr_lower] at lowered
      exact .intro (by simp [Source.coreWorld, compiled, found, bind, Except.bind, pure, Except.pure]) lowered.close
  | some core =>
      obtain ⟨source, preparedBody, body, found, expanded, control, safe, params, bodyEq⟩ := Source.compilerFunction_spec compiled
      have prepared : source.prepare s.program.enum? args = .ok (types, locals, expr) := by
        simpa only [Source.world, sourceWorld, found] using prepared
      obtain ⟨argTypes, formed, rfl, rfl, rfl⟩ := SourceFunction.prepare_iff.mp prepared
      have expandedEval : OpenSource.EvalExpr s.world (Engine.EvalFn s.coreWorld) []
          ((source.params.map Prod.fst).zip args) preparedBody before result after ∨
          OpenSource.EvalExit s.world (Engine.EvalFn s.coreWorld) []
          ((source.params.map Prod.fst).zip args) preparedBody before .function result after := by
        rcases evaluated with normal | abrupt
        · exact .inl ((SourceSemantics.expression_preparation_open_iff s.program s.world
            (fun _ _ => rfl) rfl _ _ _ expanded _ _ _ _).mp normal)
        · exact .inr ((SourceSemantics.exit_preparation_open_iff s.program s.world
            (fun _ _ => rfl) rfl _ _ _ expanded _ _ _ _ _).mp abrupt)
      have controlEval := (ControlLower.function_correct control).mpr expandedEval
      have lowered := lowering_complete (core := s.coreWorld) rfl controlEval safe
      rw [← bodyEq] at lowered
      refine .intro (locals := (source.params.map Prod.fst).zip args) (expr := core.body) ?_ lowered.close
      simp only [Source.coreWorld, compiled, prepareFunction, params]
      rw [if_pos ⟨argTypes, formed⟩]

/-- Every finite evaluation of the original generic source has an evaluation
of the compiled instance with the identical value and allocation heap. Consts,
native arrays, pointer patterns and nondeterministic hints are all included. -/
theorem Specialized.native_complete [Field F] [DecidableEq F] {s : Source F}
    (q : Specialized s entries) (reachable : name ∈ callableNames q.program)
    (evaluated : SourceSemantics.EvalFn s.world name args before result after) :
    Engine.EvalFn s.coreWorld name args before result after := by
  apply evaluated.openCalls q.sourceAgreement.closed
    (fun n hn args ts ls e b v a prep ev => q.prepare_complete hn prep ev) reachable

theorem Specialized.native_core_complete [Field F] [DecidableEq F] {s : Source F}
    (q : Specialized s entries) (reachable : name ∈ callableNames q.program)
    (evaluated : SourceSemantics.EvalFn s.world name args before result after) :
    Aiur.EvalFn q.program name args before result after :=
  (q.coreEvalFn_iff reachable).mp (q.native_complete reachable evaluated)

end Aiur.Generic
