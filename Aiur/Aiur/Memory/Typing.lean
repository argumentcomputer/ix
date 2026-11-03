import Aiur.Memory.ValueNames
import Aiur.TypecheckFacts

namespace Aiur

theorem parameterTypes (params : List (String × Ty)) (args : List (Value F A))
    (types : params.map Prod.snd = args.map Value.type) :
    environmentTypes ((params.map Prod.fst).zip args) = params := by
  induction params generalizing args with
  | nil => cases args <;> simp_all [environmentTypes]
  | cons param params ih =>
      cases args with
      | nil => simp at types
      | cons arg args =>
          simp only [List.map_cons, List.cons.injEq] at types
          simp only [List.map_cons, List.zip_cons_cons, environmentTypes, List.map_cons]
          rw [← types.1]
          exact congrArg (param :: ·) (ih args types.2)

/-- Checked source execution preserves constructor payloads, pointer annotations, and every stored cell. -/
theorem EvalExpr.wellTyped [Field F] [DecidableEq F] {program : Program F}
    (checkedProgram : typecheck program = .ok ())
    {locals : Environment F Nat} {expr : Expr F} {result : SourceValue F} {before after : Heap F}
    (evaluated : EvalExpr program locals expr before result after) :
    before.Good program.enums → locals.Good program.enums → ∀ caller type,
      inferType program caller (environmentTypes locals) expr = .ok type →
        result.type = type ∧ result.Good program.enums ∧ after.Good program.enums := by
  induction evaluated using EvalExpr.rec
    (motive_2 := fun locals exprs before values after _ => before.Good program.enums →
      locals.Good program.enums → ∀ caller types,
      inferTypes program caller (environmentTypes locals) exprs = .ok types →
        values.map Value.type = types ∧ (∀ value ∈ values, value.Good program.enums) ∧ after.Good program.enums)
    (motive_3 := fun name args before value after _ => before.Good program.enums →
      (∀ arg ∈ args, arg.PointerNames program.enums) → ∀ fn, program.findSignature? name = some fn →
        value.type = fn.result ∧ value.Good program.enums ∧ after.Good program.enums) with
  | literal =>
      intro memory formed caller type checked
      exact ⟨by simpa [inferType, Value.type, pure, Except.pure] using checked, by simp, memory⟩
  | var lookup =>
      intro memory formed caller type checked
      refine ⟨?_, formed _ (List.mem_of_find?_eq_some lookup), memory⟩
      simpa [inferType, environmentTypes, List.find?_map, Function.comp_def, lookup,
        pure, Except.pure] using checked
  | hint _ typed ih =>
      intro memory formed caller type checked
      simp only [inferType] at checked
      obtain ⟨keyType, keyRun, checked⟩ := except_bind_ok.mp checked
      have heapGood := (ih memory formed caller keyType keyRun).2.2
      obtain ⟨_, _, checked⟩ := except_bind_ok.mp checked
      obtain ⟨rfl, _⟩ := checkHintType_ok checked
      have typed := (by simpa [Value.WellTyped, Value.hasType] using typed)
      exact ⟨by simpa using typed.1,
        ⟨by simpa using typed.2, Value.pointerNames_of_free (Constant.toValue_pointerFree _)⟩, heapGood⟩
  | tuple _ ih =>
      intro memory formed caller type checked
      simp only [inferType] at checked
      obtain ⟨types, itemsRun, finished⟩ := except_bind_ok.mp checked
      obtain rfl := except_pure_ok.mp finished
      obtain ⟨shape, valuesGood, heapGood⟩ := ih memory formed caller types itemsRun
      exact ⟨by simp [Value.type, shape], (Value.good_tuple _ _).mpr valuesGood, heapGood⟩
  | @construct locals exprs before values after name ctor _ ih =>
      intro memory formed caller type checked
      cases found : program.enums.findConstructor? name ctor with
      | none => simp [inferType, found] at checked
      | some definition =>
          simp only [inferType, found] at checked
          split at checked
          · cases checked
          · rename_i arity
            simp only [pure_bind] at checked
            obtain ⟨types, argsRun, rest⟩ := except_bind_ok.mp checked
            obtain ⟨finished, typesRun, rest⟩ := except_bind_ok.mp rest
            cases finished
            obtain rfl := except_pure_ok.mp rest
            obtain ⟨shape, valuesGood, heapGood⟩ := ih memory formed caller types argsRun
            have length : definition.fields.length = types.length := by
              have len := inferTypes_length argsRun
              have arity : exprs.length = definition.fields.length := by simpa using arity
              omega
            have combined := congrArg (fun r : Except CheckError PUnit => r >>= fun _ =>
              (pure () : Except CheckError Unit)) typesRun
            have typesEq := requireTypes_ok (caller := caller) length
              (by simpa only [bind, Except.bind, pure, Except.pure] using combined)
            refine ⟨by simp [Value.type], ⟨?_, ?_⟩, heapGood⟩
            · exact (Value.wellFormed_construct _ _ _ _).mpr
                ⟨definition, found, shape.trans typesEq.symm, fun v h => (valuesGood v h).1⟩
            · exact (Value.pointerNames_construct _ _ _ _).mpr (fun v h => (valuesGood v h).2)
  | @project locals expr before input after index result _ projected ih =>
      intro memory formed caller type checked
      simp only [inferType] at checked
      obtain ⟨inputType, inputRun, rest⟩ := except_bind_ok.mp checked
      obtain ⟨inputShape, inputGood, heapGood⟩ := ih memory formed caller inputType inputRun
      cases input with
      | field | ptr | construct => cases projected
      | tuple values =>
          simp only [Value.type] at inputShape
          subst inputType
          cases found : (values.map Value.type)[index]? with
          | none => simp [found] at rest
          | some itemType =>
              simp only [found, except_pure_ok] at rest
              subst type
              cases source : values[index]? with
              | none => simp [projectValue, source] at projected
              | some value =>
                  simp [projectValue, source, pure, Except.pure] at projected
                  subst result
                  refine ⟨?_, (Value.good_tuple _ _).mp inputGood _ (List.mem_of_getElem? source), heapGood⟩
                  simpa [List.getElem?_map, source] using found
  | letValue _ matched _ valueIH bodyIH =>
      intro memory formed caller type checked
      simp only [inferType] at checked
      obtain ⟨valueType, valueRun, rest⟩ := except_bind_ok.mp checked
      obtain ⟨bindingTypes, patternRun, rest⟩ := except_bind_ok.mp rest
      obtain ⟨shape, inputGood, heapGood⟩ := valueIH memory formed caller valueType valueRun
      have bindings := patternTypes_bindings (caller := caller)
        (by rw [shape]; exact checkPattern_types patternRun) inputGood.1 matched
      exact bodyIH heapGood (Environment.good_append.mpr
        ⟨Pattern.bindings_good inputGood matched, formed⟩) caller type
        (by simpa only [environmentTypes_append, bindings] using rest)
  | store _ ih =>
      intro memory formed caller type checked
      simp only [inferType] at checked
      obtain ⟨inputType, inputRun, rest⟩ := except_bind_ok.mp checked
      obtain rfl := except_pure_ok.mp rest
      obtain ⟨shape, inputGood, heapGood⟩ := ih memory formed caller inputType inputRun
      refine ⟨by simp [Value.type, shape], ⟨by simp, ?_⟩, ?_⟩
      · simpa only [Value.PointerNames] using Value.type_names inputGood.1 inputGood.2
      · simpa only [Heap.Good, List.mem_append, List.mem_singleton, or_imp, forall_and,
          forall_eq] using And.intro heapGood inputGood
  | @load locals expr before input after result _ loaded ih =>
      intro memory formed caller type checked
      simp only [inferType] at checked
      obtain ⟨inputType, inputRun, rest⟩ := except_bind_ok.mp checked
      obtain ⟨pointerShape, _, heapGood⟩ := ih memory formed caller inputType inputRun
      cases input with
      | field | tuple | construct => cases loaded
      | ptr target address =>
          simp only [Value.type] at pointerShape
          subst inputType
          obtain rfl := except_pure_ok.mp rest
          cases found : after[address]? with
          | none => simp [loadValue, found] at loaded
          | some stored =>
              by_cases typed : stored.type = target
              · simp [loadValue, found, typed, bind, Except.bind, pure, Except.pure] at loaded
                subst result
                exact ⟨typed, heapGood _ (List.mem_of_getElem? found), heapGood⟩
              · simp [loadValue, found, typed] at loaded
  | @neg locals expr before input after result _ operation ih =>
      intro memory formed caller type checked
      simp only [inferType] at checked
      obtain ⟨inputType, inputRun, rest⟩ := except_bind_ok.mp checked
      obtain ⟨finished, _, rest⟩ := except_bind_ok.mp rest
      obtain rfl := except_pure_ok.mp rest
      have heapGood := (ih memory formed caller inputType inputRun).2.2
      cases input with
      | field x => cases operation; exact ⟨by simp [Value.type], by simp, heapGood⟩
      | tuple | ptr | construct => cases operation
  | @assertEq locals lhs before x middle rhs y after op result _ _ operation leftIH rightIH =>
      intro memory formed caller type checked
      simp only [inferType] at checked
      obtain ⟨leftType, leftRun, rest⟩ := except_bind_ok.mp checked
      obtain ⟨rightType, rightRun, rest⟩ := except_bind_ok.mp rest
      obtain ⟨finished, _, rest⟩ := except_bind_ok.mp rest
      have resultUnit := (evalAssertEq_ok.mp operation).2.2
      subst result
      split at rest
      · simp [bind, Except.bind] at rest
      · have same : type = .tuple [] := by simpa [bind, Except.bind, pure, Except.pure] using rest.symm
        subst type
        have heapGood := (rightIH (leftIH memory formed caller leftType leftRun).2.2 formed caller rightType rightRun).2.2
        exact ⟨by simp [Value.type], by simp, heapGood⟩
  | @binary locals lhs before x middle rhs y after op result _ _ operation leftIH rightIH =>
      intro memory formed caller type checked
      simp only [inferType] at checked
      obtain ⟨leftType, leftRun, rest⟩ := except_bind_ok.mp checked
      obtain ⟨finished, _, rest⟩ := except_bind_ok.mp rest
      obtain ⟨rightType, rightRun, rest⟩ := except_bind_ok.mp rest
      obtain ⟨finished, _, rest⟩ := except_bind_ok.mp rest
      obtain rfl := except_pure_ok.mp rest
      have heapGood := (rightIH (leftIH memory formed caller leftType leftRun).2.2 formed caller rightType rightRun).2.2
      cases x with
      | tuple | ptr | construct => cases operation
      | field x =>
          cases y with
          | tuple | ptr | construct => cases operation
          | field y =>
              cases op <;> simp only [evalBinOp] at operation
              all_goals first
                | (split at operation <;> cases operation; exact ⟨by simp [Value.type], by simp, heapGood⟩)
                | (cases operation; exact ⟨by simp [Value.type], by simp, heapGood⟩)
  | @call locals args before values middle name result after _ _ argsIH callIH =>
      intro memory formed caller type checked
      cases found : program.findSignature? name with
      | none => simp [inferType, found] at checked
      | some fn =>
          simp only [inferType, found] at checked
          split at checked
          · cases checked
          · simp only [pure_bind] at checked
            obtain ⟨types, argsRun, rest⟩ := except_bind_ok.mp checked
            obtain ⟨finished, _, rest⟩ := except_bind_ok.mp rest
            obtain rfl := except_pure_ok.mp rest
            obtain ⟨_, valuesGood, heapGood⟩ := argsIH memory formed caller types argsRun
            exact callIH heapGood (fun v h => (valuesGood v h).2) fn found
  | @matchValue locals expr before input middle arms bindings body result after _ selected _ valueIH bodyIH =>
      intro memory formed caller type checked
      simp only [inferType] at checked
      obtain ⟨inputType, inputRun, rest⟩ := except_bind_ok.mp checked
      obtain ⟨shape, inputGood, heapGood⟩ := valueIH memory formed caller inputType inputRun
      cases arms with
      | nil => simp [selectArm] at selected
      | cons arm arms =>
          rcases arm with ⟨pattern, branch⟩
          obtain ⟨bindingTypes, patternRun, rest⟩ := except_bind_ok.mp rest
          obtain ⟨branchType, branchRun, rest⟩ := except_bind_ok.mp rest
          obtain ⟨finished, armsRun, rest⟩ := except_bind_ok.mp rest
          cases finished
          obtain rfl := except_pure_ok.mp rest
          have allChecked : checkArms program caller (environmentTypes locals) input.type branchType
              ((pattern, branch) :: arms) = .ok () := by
            rw [shape]
            simp [checkArms, patternRun, branchRun, requireType, armsRun, bind, Except.bind]
          exact bodyIH heapGood (Environment.good_append.mpr
            ⟨selectArm_good inputGood selected, formed⟩) caller branchType (by
            simpa only [environmentTypes_append] using checkArms_selected allChecked inputGood.1 selected)
  | nil =>
      rename_i memory formed caller types checked
      simp only [inferTypes, except_pure_ok] at checked
      subst types
      exact ⟨rfl, by simp, memory⟩
  | cons _ _ headIH tailIH =>
      rename_i memory formed caller types checked
      simp only [inferTypes] at checked
      obtain ⟨headType, headRun, rest⟩ := except_bind_ok.mp checked
      obtain ⟨tailTypes, tailRun, rest⟩ := except_bind_ok.mp rest
      obtain rfl := except_pure_ok.mp rest
      obtain ⟨headType, headGood, middleGood⟩ := headIH memory formed caller headType headRun
      obtain ⟨tailTypes, tailGood, heapGood⟩ := tailIH middleGood formed caller tailTypes tailRun
      exact ⟨by simp [headType, tailTypes], by simpa [headGood] using tailGood, heapGood⟩
  | intro prepared evaluated bodyIH =>
      rename_i memory names signature found
      rcases prepareCall_spec prepared with function | table
      · obtain ⟨fn, sourceFound, types, formed, rfl, rfl⟩ := function
        have same := Option.some.inj (found.symm.trans (Program.signature_of_function sourceFound))
        subst signature
        refine bodyIH memory ?_ fn.name fn.result ?_
        · intro binding member
          have argMember := (List.of_mem_zip member).2
          exact ⟨formed _ argMember, names _ argMember⟩
        · rw [parameterTypes _ _ types]
          exact typecheck_function checkedProgram (List.mem_of_find?_eq_some sourceFound)
      · obtain ⟨constant, absent, looked, rfl, rfl⟩ := table
        obtain ⟨map, key, mapFound, _, _, _, _, typed⟩ := lookupMap_spec looked
        have same := Option.some.inj (found.symm.trans (Program.signature_of_map absent mapFound))
        subst signature
        obtain ⟨rfl, rfl⟩ := EvalExpr.constant_result constant evaluated
        have typed : constant.type = map.result ∧ constant.wellFormed program.enums = true := by
          simpa [Value.hasType] using typed
        exact ⟨by simpa using typed.1, ⟨by simpa using typed.2,
          Value.pointerNames_of_free (Constant.toValue_pointerFree constant)⟩, memory⟩

theorem EvalFn.heap_good [Field F] [DecidableEq F] {program : Program F}
    (checked : typecheck program = .ok ()) {name : String} {args : List (SourceValue F)}
    {before after : Heap F} {result : SourceValue F}
    (evaluated : EvalFn program name args before result after) (memory : before.Good program.enums)
    (names : ∀ arg ∈ args, arg.PointerNames program.enums) :
    result.Good program.enums ∧ after.Good program.enums := by
  cases evaluated with
  | intro prepared body =>
      rcases prepareCall_spec prepared with function | table
      · obtain ⟨fn, found, types, formed, rfl, rfl⟩ := function
        have localsGood : Environment.Good program.enums ((fn.params.map Prod.fst).zip args) := by
          intro binding member
          have argMember := (List.of_mem_zip member).2
          exact ⟨formed _ argMember, names _ argMember⟩
        exact (body.wellTyped checked memory localsGood fn.name fn.result (by
          rw [parameterTypes _ _ types]
          exact typecheck_function checked (List.mem_of_find?_eq_some found))).2
      · obtain ⟨constant, _, looked, rfl, rfl⟩ := table
        obtain ⟨rfl, rfl⟩ := EvalExpr.constant_result constant body
        obtain ⟨_, _, _, _, _, _, _, typed⟩ := lookupMap_spec looked
        have formed : constant.wellFormed program.enums = true := by
          simp only [Value.hasType, Bool.and_eq_true] at typed
          exact typed.2
        exact ⟨⟨by simpa using formed,
          Value.pointerNames_of_free (Constant.toValue_pointerFree constant)⟩, memory⟩

end Aiur
