import Aiur.Inlining.Completeness

namespace Aiur.Inlining
open Generic

/-- Reflect expansion using the static argument types. Calls are discharged by
induction on the finite target evaluation, so recursive functions need not be total. -/
theorem soundExpr [Field F] [DecidableEq F]
    {p q : Aiur.Program F} {names : List String} {calls : Generic.CallRelation F}
    (sameEnums : p.enums = q.enums) (checkedProgram : typecheck q = .ok ())
    (closed : ∀ n args b v a, calls n args b v a → Aiur.EvalFn q n args b v a)
    (reflect : ∀ n args b v a, calls n args b v a → b.Good q.enums →
      (∀ arg ∈ args, arg.Good q.enums) → Aiur.EvalFn p n args b v a)
    (tree : Tree F) (locals : Environment F Nat)
    (before : Heap F) (result : SourceValue F) (after : Heap F)
    (safe : tree.Safe p names) {type : Aiur.Ty}
    (checked : tree.checkTypes q (environmentTypes locals) = some type)
    (evaluated : OpenCore.EvalExpr (.ofProgram q) calls locals tree.target before result after)
    (heapGood : before.Good q.enums) (localsGood : locals.Good q.enums) :
    OpenCore.EvalExpr (.ofProgram p) (Engine.EvalFn (.ofProgram p)) locals tree.source before result after := by
  have sub (child : Tree F) (smaller : sizeOf child < sizeOf tree)
      (ls : Environment F Nat) (b : Heap F) (v : SourceValue F) (a : Heap F)
      (safe : child.Safe p names) {t : Aiur.Ty}
      (checked : child.checkTypes q (environmentTypes ls) = some t)
      (ev : OpenCore.EvalExpr (.ofProgram q) calls ls child.target b v a)
      (hg : b.Good q.enums) (lg : ls.Good q.enums) :
      OpenCore.EvalExpr (.ofProgram p) (Engine.EvalFn (.ofProgram p)) ls child.source b v a :=
    soundExpr sameEnums checkedProgram closed reflect child ls b v a safe checked ev hg lg
  have children (es : List (Tree F)) (smaller : ∀ e ∈ es, sizeOf e < sizeOf tree)
      (safe : ∀ e ∈ es, e.Safe p names) {types : List Aiur.Ty}
      (typed : es.mapM (Tree.checkTypes q (environmentTypes locals)) = some types)
      {b : Heap F} {values : List (SourceValue F)} {a : Heap F}
      (ev : OpenCore.EvalArgs (.ofProgram q) calls locals (es.map Tree.target) b values a)
      (hg : b.Good q.enums) :
      OpenCore.EvalArgs (.ofProgram p) (Engine.EvalFn (.ofProgram p)) locals (es.map Tree.source) b values a ∧
        values.map Value.type = types ∧ (∀ v ∈ values, v.Good q.enums) ∧ a.Good q.enums := by
    induction es generalizing b values types with
    | nil =>
        cases ev
        have same : ([] : List Aiur.Ty) = types := Option.some.inj typed
        subst types
        exact ⟨.nil,rfl,by simp,hg⟩
    | cons e es ih =>
        cases ev with
        | cons head tail =>
            simp only [List.mapM_cons, bind, Option.bind] at typed
            obtain ⟨t, ht, rest⟩ := Option.bind_eq_some_iff.mp typed
            obtain ⟨ts, hts, last⟩ := Option.bind_eq_some_iff.mp rest
            cases Option.some.inj last
            have info := Tree.typed checkedProgram closed head hg localsGood ht
            obtain ⟨rest, shape, good, last⟩ := ih (fun x hx => smaller x (by simp [hx]))
              (fun x hx => safe x (by simp [hx])) hts tail info.2.2
            exact ⟨.cons (sub e (smaller e (by simp)) locals _ _ _ (safe e (by simp)) ht head hg localsGood) rest,
              by simp only [List.map_cons,info.1,shape],
              by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro info.2.1 good,last⟩
  have inferred := Tree.checkTypes_infer checked
  rw [Tree.checkTypes.eq_def] at checked
  simp only [inferred, Except.toOption, Bind.bind, Option.bind] at checked
  obtain ⟨checkedUnit, checks, _⟩ := Option.map_eq_some_iff.mp checked
  cases checkedUnit
  cases tree with
  | literal x =>
      simp only [Tree.Safe] at safe
      simp only [Tree.source]
      rw [Tree.target] at evaluated; cases evaluated; exact .literal
  | var n =>
      simp only [Tree.Safe] at safe
      simp only [Tree.source]
      rw [Tree.target] at evaluated; cases evaluated with | var found => exact .var found
  | tuple es =>
      simp only [Tree.Safe] at safe
      simp only [Tree.source]
      rw [Tree.target] at evaluated
      cases evaluated with
      | tuple items =>
          obtain ⟨_,mapped,_⟩ := Option.map_eq_some_iff.mp checks
          exact .tuple ((children es (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
            safe mapped items heapGood).1)
  | construct _ _ es =>
      simp only [Tree.Safe] at safe
      simp only [Tree.source]
      rw [Tree.target] at evaluated
      cases evaluated with
      | construct items =>
          obtain ⟨_,mapped,_⟩ := Option.map_eq_some_iff.mp checks
          exact .construct ((children es (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
            safe mapped items heapGood).1)
  | project child i =>
      simp only [Tree.Safe] at safe
      simp only [Tree.source]
      rw [Tree.target] at evaluated
      obtain ⟨_,typed,_⟩ := Option.map_eq_some_iff.mp checks
      cases evaluated with
      | project ev operation =>
          exact .project (sub child (by simp_wf; try omega) locals _ _ _ safe typed ev heapGood localsGood) operation
  | store child =>
      simp only [Tree.Safe] at safe
      simp only [Tree.source]
      rw [Tree.target] at evaluated
      obtain ⟨_,typed,_⟩ := Option.map_eq_some_iff.mp checks
      cases evaluated with
      | store ev =>
          exact .store (sub child (by simp_wf; try omega) locals _ _ _ safe typed ev heapGood localsGood)
  | load child =>
      simp only [Tree.Safe] at safe
      simp only [Tree.source]
      rw [Tree.target] at evaluated
      obtain ⟨_,typed,_⟩ := Option.map_eq_some_iff.mp checks
      cases evaluated with
      | load ev operation =>
          exact .load (sub child (by simp_wf; try omega) locals _ _ _ safe typed ev heapGood localsGood) operation
  | hint _ child channel =>
      simp only [Tree.Safe] at safe
      simp only [Tree.source]
      rw [Tree.target] at evaluated
      obtain ⟨_,typed,_⟩ := Option.map_eq_some_iff.mp checks
      cases evaluated with
      | hint ev formed =>
          exact .hint (sub child (by simp_wf; try omega) locals _ _ _ safe typed ev heapGood localsGood)
            (by simpa only [Engine.World.ofProgram,sameEnums] using formed)
  | neg child =>
      simp only [Tree.Safe] at safe
      simp only [Tree.source]
      rw [Tree.target] at evaluated
      obtain ⟨_,typed,_⟩ := Option.map_eq_some_iff.mp checks
      cases evaluated with
      | neg ev operation =>
          exact .neg (sub child (by simp_wf; try omega) locals _ _ _ safe typed ev heapGood localsGood) operation
  | binary op left right =>
      simp only [Tree.Safe] at safe
      simp only [Tree.source]
      rw [Tree.target] at evaluated
      cases evaluated with
      | binary first second operation =>
          obtain ⟨_,leftType,rest⟩ := Option.bind_eq_some_iff.mp checks
          obtain ⟨_,rightType,_⟩ := Option.bind_eq_some_iff.mp rest
          have middleGood := (Tree.typed checkedProgram closed first heapGood localsGood leftType).2.2
          exact .binary (sub left (by simp_wf; omega) locals _ _ _ safe.1 leftType first heapGood localsGood)
            (sub right (by simp_wf; omega) locals _ _ _ safe.2 rightType second middleGood localsGood) operation
  | assertEq op left right =>
      simp only [Tree.Safe] at safe
      simp only [Tree.source]
      rw [Tree.target] at evaluated
      cases evaluated with
      | assertEq first second operation =>
          obtain ⟨_,leftType,rest⟩ := Option.bind_eq_some_iff.mp checks
          obtain ⟨_,rightType,_⟩ := Option.bind_eq_some_iff.mp rest
          have middleGood := (Tree.typed checkedProgram closed first heapGood localsGood leftType).2.2
          exact .assertEq (sub left (by simp_wf; omega) locals _ _ _ safe.1 leftType first heapGood localsGood)
            (sub right (by simp_wf; omega) locals _ _ _ safe.2 rightType second middleGood localsGood) operation
  | call name es =>
      simp only [Tree.Safe] at safe
      simp only [Tree.source]
      rw [Tree.target] at evaluated
      cases evaluated with
      | call argEval callee =>
          obtain ⟨_, mapped, _⟩ := Option.map_eq_some_iff.mp checks
          obtain ⟨argsEval,_,argsGood,middleGood⟩ := children es
            (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) safe.2 mapped argEval heapGood
          exact .call argsEval (Engine.core_iff.mpr (reflect _ _ _ _ _ callee middleGood argsGood))
  | letValue pat value body =>
      simp only [Tree.Safe] at safe
      simp only [Tree.source]
      obtain ⟨inputType,valueType,rest⟩ := Option.bind_eq_some_iff.mp checks
      obtain ⟨bindingTypes,patternType,rest⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨_,bodyType,_⟩ := Option.bind_eq_some_iff.mp rest
      rw [Tree.target] at evaluated
      cases evaluated with
      | letValue valueEval matched bodyEval =>
          obtain ⟨shape,inputGood,middleGood⟩ := Tree.typed checkedProgram closed valueEval heapGood localsGood valueType
          have bindingShape := patternTypes_bindings (caller := "$inline")
            (by rw [shape]; exact checkPattern_types (except_toOption_some_iff.mp patternType)) inputGood.1 matched
          exact .letValue (sub value (by simp_wf; omega) locals _ _ _ safe.1 valueType valueEval heapGood localsGood) matched
            (sub body (by simp_wf; omega) _ _ _ _ safe.2
              (by simpa only [environmentTypes_append,bindingShape] using bodyType) bodyEval middleGood
              (Environment.good_append.mpr ⟨Pattern.bindings_good inputGood matched,localsGood⟩))
  | matchValue value arms =>
      simp only [Tree.Safe] at safe
      simp only [Tree.source]
      obtain ⟨inputType,valueType,rest⟩ := Option.bind_eq_some_iff.mp checks
      obtain ⟨_,armsTyped,_⟩ := Option.bind_eq_some_iff.mp rest
      rw [Tree.target] at evaluated
      cases evaluated with
      | matchValue valueEval selected bodyEval =>
          rw [select_map] at selected
          obtain ⟨⟨bs,branch⟩,chosen,same⟩ := Option.map_eq_some_iff.mp selected
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
          obtain ⟨pat,member,matched⟩ := choose_member chosen
          obtain ⟨_,branchTypes⟩ := option_mapM_hasResult armsTyped (pat,branch) member
          obtain ⟨bindingTypes,patType,branchType⟩ := Option.bind_eq_some_iff.mp branchTypes
          obtain ⟨shape,inputGood,middleGood⟩ := Tree.typed checkedProgram closed valueEval heapGood localsGood valueType
          have bindingShape := patternTypes_bindings (caller := "$inline")
            (by rw [shape]; exact checkPattern_types (except_toOption_some_iff.mp patType)) inputGood.1 matched
          exact .matchValue (sub value (by simp_wf; omega) locals _ _ _ safe.1 valueType valueEval heapGood localsGood)
            (by rw [select_map,chosen]; rfl)
            (sub branch (by simp_wf; have h := List.sizeOf_lt_of_mem member; simp only [Prod.mk.sizeOf_spec] at h; omega)
              _ _ _ _ (safe.2 _ member) (by simpa only [environmentTypes_append,bindingShape] using branchType)
              bodyEval middleGood (Environment.good_append.mpr ⟨Pattern.bindings_good inputGood matched,localsGood⟩))
  | expand f es body =>
      simp only [Tree.Safe] at safe
      simp only [Tree.source]
      obtain ⟨types,argsTyped,rest⟩ := Option.bind_eq_some_iff.mp checks
      split at rest
      · cases rest
      · rename_i sameTypes
        have sameTypes : types = f.params.map Prod.snd := by simpa using sameTypes
        obtain ⟨_,bodyTyped,_⟩ := Option.bind_eq_some_iff.mp rest
        rw [Tree.target] at evaluated
        cases evaluated with
        | letValue argEval matched bodyEval =>
            cases argEval with
            | tuple items =>
                rename_i values
                obtain ⟨argsEval,shape,argsGood,middleGood⟩ := children es
                  (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) safe.2.2.2.2.2 argsTyped items heapGood
                have typesEq := shape.trans sameTypes
                have length : (f.params.map Prod.fst).length = values.length := by
                  simpa using (congrArg List.length typesEq).symm
                have matched' := PatternLowering.bindingsList_binders _ _ length
                simp only [List.map_map,Function.comp_def] at matched'
                simp only [Aiur.Pattern.bindings] at matched
                rw [matched'] at matched
                cases Option.some.inj matched
                have params := parameterTypes f.params _ typesEq.symm
                have scope : hasScope (((f.params.map Prod.fst).zip values).map Prod.fst) body.target = true := by
                  rw [List.map_fst_zip (by omega)]; exact safe.2.2.2.1
                have isolated := (isolated_iff scope).mpr bodyEval
                have localGood : Environment.Good q.enums ((f.params.map Prod.fst).zip values) :=
                  fun binding member => argsGood binding.2 (List.of_mem_zip member).2
                have sourceBody := sub body (by simp_wf; omega) _ _ _ _ safe.2.2.2.2.1
                  (by simpa only [params] using bodyTyped) isolated middleGood localGood
                exact .call argsEval (.intro
                  (by
                    rw [safe.2.2.1]
                    exact prepareCall_of_types safe.1 typesEq.symm
                      (fun arg ha => by simpa only [sameEnums] using (argsGood arg ha).1)) sourceBody.close)
termination_by sizeOf tree
decreasing_by exact smaller

end Aiur.Inlining
