import Aiur.Generic.BuiltinFacts
import Aiur.Generic.UpdateFacts
import Aiur.Generic.LoweringCompleteness
import Aiur.Generic.LoweringTypeFacts

namespace Aiur.Generic
open SourceSemantics PatternLowering

/-- Typed reflection for expressions. The hypotheses about calls are discharged
by induction on the enclosing core evaluation, rather than by a totality
assumption. The source predicate still interprets the original source forms. -/
theorem lowering_sound [Field F] [DecidableEq F]
    {program : Aiur.Program F} {source : SourceSemantics.World F}
    {calls sourceCalls : CallRelation F}
    (checkedProgram : typecheck program = .ok ())
    (closed : ∀ n args b v a, calls n args b v a → Aiur.EvalFn program n args b v a)
    (reflect : ∀ n args b v a, calls n args b v a → b.Good program.enums →
      (∀ arg ∈ args, arg.Good program.enums) → sourceCalls n args b v a)
    (hints : ∀ t, knownType program.enums t = true → ∀ v,
      (Engine.World.ofProgram program).typed t v = true → source.typed t v = true)
    (expr : Expr F) (types : Types) (locals : Environment F Nat)
    (before : Heap F) (result : SourceValue F) (after : Heap F)
    (safe : expr.lowerSafe types)
    {type : Aiur.Ty} (checked : expr.checkLowerTypes program types (environmentTypes locals) = some type)
    (evaluated : OpenCore.EvalExpr (.ofProgram program) calls locals (expr.lower types) before result after)
    (heapGood : before.Good program.enums) (localsGood : locals.Good program.enums) :
    OpenSource.EvalExpr source sourceCalls types locals expr before result after := by
  have sub (child : Expr F) (smaller : sizeOf child < sizeOf expr)
      (ls : Environment F Nat) (b : Heap F) (v : SourceValue F) (a : Heap F)
      (safe : child.lowerSafe types) {t : Aiur.Ty}
      (checked : child.checkLowerTypes program types (environmentTypes ls) = some t)
      (ev : OpenCore.EvalExpr (.ofProgram program) calls ls (child.lower types) b v a)
      (hg : b.Good program.enums) (lg : ls.Good program.enums) :
      OpenSource.EvalExpr source sourceCalls types ls child b v a :=
    lowering_sound checkedProgram closed reflect hints child types ls b v a safe checked ev hg lg
  have children (es : List (Expr F))
      (smaller : ∀ e ∈ es, sizeOf e < sizeOf expr)
      (safe : ∀ e ∈ es, e.lowerSafe types)
      (typed : ∀ e ∈ es, ∃ t, e.checkLowerTypes program types (environmentTypes locals) = some t)
      {b : Heap F} {values : List (SourceValue F)} {a : Heap F}
      (ev : OpenCore.EvalArgs (.ofProgram program) calls locals (es.map (Expr.lower types)) b values a)
      (hg : b.Good program.enums) :
      OpenSource.EvalArgs source sourceCalls types locals es b values a ∧
        (∀ v ∈ values, v.Good program.enums) ∧ a.Good program.enums := by
    induction es generalizing b values with
    | nil => cases ev; exact ⟨.nil, by simp, hg⟩
    | cons e es ih =>
        cases ev with
        | cons head tail =>
            obtain ⟨t, ht⟩ := typed e (by simp)
            have info := head.lowerTyped checkedProgram closed hg localsGood ht
            obtain ⟨rest, good, last⟩ := ih (fun x hx => smaller x (by simp [hx]))
              (fun x hx => safe x (by simp [hx])) (fun x hx => typed x (by simp [hx])) tail info.2.2
            exact ⟨.cons (sub e (smaller e (by simp)) locals _ _ _ (safe e (by simp)) ht head hg localsGood) rest,
              by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro info.2.1 good, last⟩
  have inferred := Expr.checkLowerTypes_infer checked
  have scope := Expr.checkLowerTypes_scope checked
  rw [Expr.checkLowerTypes.eq_def] at checked
  simp only [inferred, Except.toOption, Bind.bind, Option.bind] at checked
  rw [if_neg (by simp [scope])] at checked
  obtain ⟨unit, checks, _⟩ := Option.map_eq_some_iff.mp checked
  cases unit
  cases expr with
  | control => simp [Expr.lowerSafe] at safe
  | literal x => rw [Expr.lower] at evaluated; cases evaluated; exact .literal
  | var name => rw [Expr.lower] at evaluated; cases evaluated with | var found => exact .var found
  | global => simp [Expr.lowerSafe] at safe
  | tuple es | array es =>
      rw [Expr.lower] at evaluated
      cases evaluated with
      | tuple items =>
          obtain ⟨_, mapped, _⟩ := Option.bind_eq_some_iff.mp checks
          have args := (children es (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
            (by simpa only [Expr.lowerSafe] using safe) (option_mapM_hasResult mapped) items heapGood).1
          first | exact .tuple args | exact .array args
  | builtin paths es =>
      rw [Expr.lower] at evaluated
      obtain ⟨values, items, builtind⟩ := BuiltinLowering.expression_iff.mp evaluated
      obtain ⟨_, mapped, _⟩ := Option.bind_eq_some_iff.mp checks
      exact .builtin ((children es (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
        (by simpa only [Expr.lowerSafe] using safe) (option_mapM_hasResult mapped) items heapGood).1) builtind
  | update paths es =>
      rw [Expr.lower] at evaluated
      obtain ⟨values, items, updated⟩ := UpdateLowering.expression_iff.mp evaluated
      obtain ⟨_, mapped, _⟩ := Option.bind_eq_some_iff.mp checks
      exact .update ((children es (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
        (by simpa only [Expr.lowerSafe] using safe) (option_mapM_hasResult mapped) items heapGood).1) updated
  | record head es =>
      rw [Expr.lower] at evaluated
      obtain ⟨values, items, rfl⟩ := StructLowering.record_iff.mp evaluated
      obtain ⟨_, mapped, _⟩ := Option.bind_eq_some_iff.mp checks
      exact .record ((children es (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
        (by simpa only [Expr.lowerSafe] using safe) (option_mapM_hasResult mapped) items heapGood).1)
  | member child field =>
      rw [Expr.lowerSafe] at safe
      rw [Expr.lower] at evaluated
      obtain ⟨value, ev, projected⟩ := (StructLowering.member_iff safe.2).mp evaluated
      obtain ⟨_, typed, _⟩ := Option.bind_eq_some_iff.mp checks
      exact .member (sub child (by simp_wf; omega) locals _ _ _ safe.1 typed ev heapGood localsGood) projected
  | construct name args ctor es | constructAs params t ctor es =>
      rw [Expr.lower] at evaluated
      cases evaluated with
      | construct items =>
          obtain ⟨_, mapped, _⟩ := Option.bind_eq_some_iff.mp checks
          have args := (children es (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
            (by simpa only [Expr.lowerSafe] using safe) (option_mapM_hasResult mapped) items heapGood).1
          first | exact .construct args | exact .constructAs args
  | «repeat» child n =>
      rw [Expr.lower] at evaluated
      obtain ⟨value, ev, rfl⟩ := ArrayLowering.repeatValue_iff.mp evaluated
      obtain ⟨_, typed, _⟩ := Option.bind_eq_some_iff.mp checks
      exact .repeat (sub child (by simp_wf <;> omega) locals _ _ _
        (by simpa only [Expr.lowerSafe] using safe) typed ev heapGood localsGood)
  | index child i | project child i =>
      rw [Expr.lower] at evaluated
      cases evaluated with
      | project ev projected =>
          obtain ⟨_, typed, _⟩ := Option.bind_eq_some_iff.mp checks
          have childEval := sub child (by simp_wf <;> omega) locals _ _ _
            (by simpa only [Expr.lowerSafe] using safe) typed ev heapGood localsGood
          first | exact .index childEval projected | exact .project childEval projected
  | store child =>
      rw [Expr.lower] at evaluated
      cases evaluated with
      | store ev =>
          obtain ⟨_, typed, _⟩ := Option.bind_eq_some_iff.mp checks
          exact .store (sub child (by simp_wf <;> omega) locals _ _ _
            (by simpa only [Expr.lowerSafe] using safe) typed ev heapGood localsGood)
  | load child =>
      rw [Expr.lower] at evaluated
      cases evaluated with
      | load ev loaded =>
          obtain ⟨_, typed, _⟩ := Option.bind_eq_some_iff.mp checks
          exact .load (sub child (by simp_wf <;> omega) locals _ _ _
            (by simpa only [Expr.lowerSafe] using safe) typed ev heapGood localsGood) loaded
  | hint t child channel =>
      simp only [Expr.lower, Engine.inScope, Bool.and_eq_true] at scope
      rw [Expr.lower] at evaluated
      cases evaluated with
      | hint ev formed =>
          obtain ⟨_, typed, _⟩ := Option.bind_eq_some_iff.mp checks
          exact .hint (sub child (by simp_wf <;> omega) locals _ _ _
            (by simpa only [Expr.lowerSafe] using safe) typed ev heapGood localsGood)
            (hints _ scope.1 _ formed)
  | neg child =>
      rw [Expr.lower] at evaluated
      cases evaluated with
      | neg ev operation =>
          obtain ⟨_, typed, _⟩ := Option.bind_eq_some_iff.mp checks
          exact .neg (sub child (by simp_wf <;> omega) locals _ _ _
            (by simpa only [Expr.lowerSafe] using safe) typed ev heapGood localsGood) operation
  | binary op left right =>
      rw [Expr.lowerSafe] at safe
      rw [Expr.lower] at evaluated
      cases evaluated with
      | binary first second operation =>
          obtain ⟨_, leftType, rest⟩ := Option.bind_eq_some_iff.mp checks
          obtain ⟨_, rightType, _⟩ := Option.bind_eq_some_iff.mp rest
          have middleGood := (first.lowerTyped checkedProgram closed heapGood localsGood leftType).2.2
          exact .binary (sub left (by simp_wf <;> omega) locals _ _ _ safe.1 leftType first heapGood localsGood)
            (sub right (by simp_wf <;> omega) locals _ _ _ safe.2 rightType second middleGood localsGood) operation
  | call name args es =>
      rw [Expr.lower] at evaluated
      cases evaluated with
      | call argEval callee =>
          obtain ⟨_, mapped, _⟩ := Option.bind_eq_some_iff.mp checks
          obtain ⟨argsEval, argsGood, middleGood⟩ := children es
            (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
            (by simpa only [Expr.lowerSafe] using safe) (option_mapM_hasResult mapped) argEval heapGood
          exact .call argsEval (reflect _ _ _ _ _ callee middleGood argsGood)
  | slice child start stop =>
      cases stop with
      | none => simp [Expr.lowerSafe] at safe
      | some stop =>
          rw [Expr.lowerSafe] at safe
          obtain ⟨inputType, childType, rest⟩ := Option.bind_eq_some_iff.mp checks
          cases inputType <;> try cases rest
          rename_i fields
          dsimp only at rest
          split at rest
          · rename_i bounds
            rw [Expr.lower] at evaluated
            obtain ⟨input, values, childEval, projected, rfl⟩ := ArrayLowering.sliceValue_iff.mp evaluated
            have shape := (childEval.lowerTyped checkedProgram closed heapGood localsGood childType).1
            cases input <;> simp only [Value.type] at shape
            all_goals first | contradiction | skip
            rename_i inputs
            have bound : stop ≤ inputs.length := by
              have length := congrArg List.length (Aiur.Ty.tuple.inj shape)
              simp only [List.length_map] at length
              omega
            exact .slice (sub child (by simp_wf <;> omega) locals _ _ _ safe.2 childType childEval heapGood localsGood)
              (ArrayLowering.source_slice_of_projects bounds.1 bound projected)
          · cases rest
  | letValue pat value body =>
      rw [Expr.lowerSafe] at safe
      obtain ⟨inputType, valueType, rest⟩ := Option.bind_eq_some_iff.mp checks
      obtain ⟨bindingTypes, patternType, rest⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨_, bodyType, _⟩ := Option.bind_eq_some_iff.mp rest
      rw [Expr.lower] at evaluated
      obtain ⟨input, middle, bindings, valueEval, matched, bodyEval⟩ :=
        (lowerLet_open_iff types pat _ _ safe.2.2 source.constant source.constDepth _ _ _ _).mp evaluated
      obtain ⟨shape, inputGood, middleGood⟩ := valueEval.lowerTyped checkedProgram closed heapGood localsGood valueType
      obtain ⟨bindingShape, bindingsGood⟩ := Pattern.lowerBindingTypes_sound middleGood inputGood matched
        (by rw [shape]; exact patternType)
      exact .letValue (sub value (by simp_wf <;> omega) locals _ _ _ safe.1 valueType valueEval heapGood localsGood) matched
        (sub body (by simp_wf <;> omega) (bindings ++ locals) _ _ _ safe.2.1
          (by simpa only [environmentTypes_append, bindingShape] using bodyType) bodyEval middleGood
          (Environment.good_append.mpr ⟨bindingsGood, localsGood⟩))
  | matchValue value arms =>
      rw [Expr.lowerSafe] at safe
      obtain ⟨inputType, valueType, rest⟩ := Option.bind_eq_some_iff.mp checks
      obtain ⟨_, armsTyped, _⟩ := Option.bind_eq_some_iff.mp rest
      rw [Expr.lower] at evaluated
      obtain ⟨input, middle, bindings, body, valueEval, selected, bodyEval⟩ :=
        (lowerMatch_open_iff types _ _ safe.2.2 source.constant source.constDepth _ _ _ _).mp evaluated
      rw [choose_map] at selected
      cases chosen : choose source.constant source.constDepth types middle input arms with
      | error e => simp [chosen, Except.map] at selected
      | ok selection => cases selection with
        | none => simp [chosen, Except.map] at selected
        | some selection =>
            rcases selection with ⟨bs, branch⟩
            have same : bs = bindings ∧ branch.lower types = body := by
              simpa [chosen, Except.map] using selected
            obtain ⟨rfl, rfl⟩ := same
            obtain ⟨pat, member, matched⟩ := choose_matched chosen
            obtain ⟨_, branchTypes⟩ := option_mapM_hasResult armsTyped (pat, branch) member
            obtain ⟨bindingTypes, patType, branchType⟩ := Option.bind_eq_some_iff.mp branchTypes
            obtain ⟨shape, inputGood, middleGood⟩ := valueEval.lowerTyped checkedProgram closed heapGood localsGood valueType
            obtain ⟨bindingShape, bindingsGood⟩ := Pattern.lowerBindingTypes_sound middleGood inputGood matched
              (by rw [shape]; exact patType)
            apply OpenSource.EvalExpr.matchValue
              (sub value (by simp_wf <;> omega) locals _ _ _ safe.1 valueType valueEval heapGood localsGood)
              (by rw [← choose_source]; exact chosen)
            exact sub branch (by simp_wf; have h := List.sizeOf_lt_of_mem member; simp only [Prod.mk.sizeOf_spec] at h; omega)
              (bs ++ locals) _ _ _ (safe.2.1 _ member)
              (by simpa only [environmentTypes_append, bindingShape] using branchType) bodyEval middleGood
              (Environment.good_append.mpr ⟨bindingsGood, localsGood⟩)
termination_by sizeOf expr
decreasing_by exact smaller

end Aiur.Generic
