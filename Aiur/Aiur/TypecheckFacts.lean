import Aiur.PatternTyping
import Aiur.Semantics.WithCalls
import Aiur.ValueFacts
import Aiur.ExceptFacts
import Mathlib.Data.List.Forall2

namespace Aiur

theorem checkHintType_ok {decls : Declarations} {caller : String} {type result : Ty}
    (checked : checkHintType decls caller type = .ok result) :
    result = type ∧ type.pointerFree decls = true := by
  cases names : type.checkNames decls with
  | error error => simp [checkHintType, names, Except.mapError, bind, Except.bind] at checked
  | ok done =>
      cases done
      cases free : type.pointerFree decls <;>
        simp_all [checkHintType, names, requirePointerFree, Except.mapError, bind, Except.bind,
          pure, Except.pure]

variable {F : Type} {rom : ROM F}

/-- A call premise has the result shape of the function or map it names. -/
def CallsTyped (program : Program F) (calls : CallRelation F) : Prop :=
  ∀ name args result, calls name args result →
    ∀ fn, program.findSignature? name = some fn → result.type = fn.result ∧ result.wellFormed program.enums = true

theorem typecheck_declarations [DecidableEq F] {program : Program F} (checked : typecheck program = .ok ()) :
    checkDeclarations program.enums = .ok () := by
  unfold typecheck at checked
  obtain ⟨done, declarations, _⟩ := except_bind_ok.mp checked
  cases run : checkDeclarations program.enums with
  | error error => simp [run, Except.mapError] at declarations
  | ok unit => cases unit; rfl

theorem typecheck_function [DecidableEq F] {program : Program F} (checked : typecheck program = .ok ())
    {fn : Function F} (member : fn ∈ program.functions) :
    inferType program fn.name fn.params fn.body = .ok fn.result := by
  unfold typecheck at checked
  obtain ⟨done, _, rest⟩ := except_bind_ok.mp checked
  split at rest
  · cases rest
  · simp only [pure_bind] at rest
    obtain ⟨_, _, rest⟩ := except_bind_ok.mp rest
    have body := forIn_ok rest fn member
    unfold checkFunction at body
    obtain ⟨_, _, body⟩ := except_bind_ok.mp body
    obtain ⟨_, _, body⟩ := except_bind_ok.mp body
    split at body
    · cases body
    · simp only [pure_bind] at body
      obtain ⟨type, inferred, same⟩ := except_bind_ok.mp body
      rw [← requireType_ok same] at inferred
      exact inferred

theorem inferTypes_length {program : Program F} {caller : String} {locals : List (String × Ty)}
    {exprs : List (Expr F)} {types : List Ty}
    (checked : inferTypes program caller locals exprs = .ok types) : types.length = exprs.length := by
  induction exprs generalizing types with
  | nil => simp only [inferTypes, except_pure_ok] at checked; subst types; rfl
  | cons expr exprs ih =>
      simp only [inferTypes] at checked
      obtain ⟨type, _, rest⟩ := except_bind_ok.mp checked
      obtain ⟨types, tail, finished⟩ := except_bind_ok.mp rest
      obtain rfl := except_pure_ok.mp finished
      simp [ih tail]

theorem requireTypes_ok {caller : String} {expected actual : List Ty}
    (length : expected.length = actual.length)
    (checked : (do for (e, a) in expected.zip actual do requireType caller e a : Except CheckError Unit) = .ok ()) :
    expected = actual := by
  have all := forIn_ok checked
  have related : List.Forall₂ Eq expected actual := List.forall₂_iff_zip.mpr
    ⟨length, fun h => requireType_ok (all _ h)⟩
  simpa only [List.forall₂_eq_eq_eq] using related

/-- Typed ROM cells supply well-formed constructor data to loads. -/
def ROM.WellFormed (decls : Declarations) (rom : ROM F) : Prop :=
  ∀ entry ∈ rom.entries, entry.2.wellFormed decls = true

/-- Evaluation preserves declared types and constructor payload invariants. -/
theorem ROMEvalExprWith.wellTyped [Field F] [DecidableEq F] {program : Program F} {calls : CallRelation F}
    (typed : CallsTyped program calls) (memory : rom.WellFormed program.enums)
    {locals : Environment F} {expr : Expr F} {result : Value F}
    (evaluated : ROMEvalExprWith program.enums rom calls locals expr result) :
    locals.WellFormed program.enums → ∀ caller type,
      inferType program caller (environmentTypes locals) expr = .ok type →
        result.type = type ∧ result.wellFormed program.enums = true := by
  induction evaluated using ROMEvalExprWith.rec
    (motive_2 := fun locals exprs values _ => locals.WellFormed program.enums → ∀ caller types,
      inferTypes program caller (environmentTypes locals) exprs = .ok types →
        values.map Value.type = types ∧ ∀ value ∈ values, value.wellFormed program.enums = true) with
  | literal =>
      intro formed caller type checked
      refine ⟨?_, by simp⟩
      simpa [inferType, Value.type, pure, Except.pure] using checked
  | var lookup =>
      intro formed caller type checked
      refine ⟨?_, formed _ (List.mem_of_find?_eq_some lookup)⟩
      simpa [inferType, environmentTypes, List.find?_map, Function.comp_def, lookup,
        pure, Except.pure] using checked
  | hint _ typed _ =>
      intro formed caller type checked
      simp only [inferType] at checked
      obtain ⟨_, _, checked⟩ := except_bind_ok.mp checked
      obtain ⟨_, _, checked⟩ := except_bind_ok.mp checked
      obtain ⟨rfl, _⟩ := checkHintType_ok checked
      simpa [Value.WellTyped, Value.hasType, Constant.toValue] using typed
  | tuple _ ih =>
      intro formed caller type checked
      simp only [inferType] at checked
      obtain ⟨types, itemsRun, finished⟩ := except_bind_ok.mp checked
      obtain rfl := except_pure_ok.mp finished
      obtain ⟨shape, valuesFormed⟩ := ih formed caller types itemsRun
      exact ⟨by simp [Value.type, shape], (Value.wellFormed_tuple _ _).mpr valuesFormed⟩
  | @construct locals exprs values name ctor _ ih =>
      intro formed caller type checked
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
            obtain ⟨shape, valuesFormed⟩ := ih formed caller types argsRun
            have length : definition.fields.length = types.length := by
              have len := inferTypes_length argsRun
              have arity : exprs.length = definition.fields.length := by simpa using arity
              omega
            have combined := congrArg (fun r : Except CheckError PUnit => r >>= fun _ =>
              (pure () : Except CheckError Unit)) typesRun
            have typesEq := requireTypes_ok (caller := caller) length
              (by simpa only [bind, Except.bind, pure, Except.pure] using combined)
            refine ⟨by simp [Value.type], (Value.wellFormed_construct _ _ _ _).mpr ?_⟩
            exact ⟨definition, found, shape.trans typesEq.symm, valuesFormed⟩
  | @project locals expr input index result _ projected ih =>
      intro formed caller type checked
      simp only [inferType] at checked
      obtain ⟨inputType, inputRun, rest⟩ := except_bind_ok.mp checked
      obtain ⟨inputShape, inputFormed⟩ := ih formed caller inputType inputRun
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
                  refine ⟨?_, (Value.wellFormed_tuple _ _).mp inputFormed _ (List.mem_of_getElem? source)⟩
                  simpa [List.getElem?_map, source] using found
  | letValue _ matched _ valueIH bodyIH =>
      intro formed caller type checked
      simp only [inferType] at checked
      obtain ⟨valueType, valueRun, rest⟩ := except_bind_ok.mp checked
      obtain ⟨bindingTypes, patternRun, rest⟩ := except_bind_ok.mp rest
      obtain ⟨shape, inputFormed⟩ := valueIH formed caller valueType valueRun
      have bindings := patternTypes_bindings (caller := caller)
        (by rw [shape]; exact checkPattern_types patternRun) inputFormed matched
      exact bodyIH (Environment.wellFormed_append.mpr
        ⟨Pattern.bindings_wellFormed inputFormed matched, formed⟩) caller type
        (by simpa only [environmentTypes_append, bindings] using rest)
  | store _ _ ih =>
      intro formed caller type checked
      simp only [inferType] at checked
      obtain ⟨inputType, inputRun, rest⟩ := except_bind_ok.mp checked
      obtain rfl := except_pure_ok.mp rest
      exact ⟨by simp [Value.type, (ih formed caller inputType inputRun).1], by simp⟩
  | @load locals expr target address result _ cell shape ih =>
      intro formed caller type checked
      simp only [inferType] at checked
      obtain ⟨inputType, inputRun, rest⟩ := except_bind_ok.mp checked
      have pointerShape := (ih formed caller inputType inputRun).1
      simp only [Value.type] at pointerShape
      subst inputType
      obtain rfl := except_pure_ok.mp rest
      exact ⟨shape, memory _ cell⟩
  | @neg locals expr input result _ operation ih =>
      intro formed caller type checked
      simp only [inferType] at checked
      obtain ⟨inputType, _, rest⟩ := except_bind_ok.mp checked
      obtain ⟨finished, _, rest⟩ := except_bind_ok.mp rest
      obtain rfl := except_pure_ok.mp rest
      cases input with
      | field x => cases operation; simp [Value.type]
      | tuple | ptr | construct => cases operation
  | @assertEq locals lhs x rhs y op result _ _ operation leftIH rightIH =>
      intro formed caller type checked
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
        simp [Value.type]
  | @binary locals lhs x rhs y op result _ _ operation leftIH rightIH =>
      intro formed caller type checked
      simp only [inferType] at checked
      obtain ⟨leftType, _, rest⟩ := except_bind_ok.mp checked
      obtain ⟨finished, _, rest⟩ := except_bind_ok.mp rest
      obtain ⟨rightType, _, rest⟩ := except_bind_ok.mp rest
      obtain ⟨finished, _, rest⟩ := except_bind_ok.mp rest
      obtain rfl := except_pure_ok.mp rest
      cases x with
      | tuple | ptr | construct => cases operation
      | field x =>
          cases y with
          | tuple | ptr | construct => cases operation
          | field y =>
              cases op <;> simp only [evalBinOp] at operation
              all_goals first
                | (split at operation <;> cases operation; simp [Value.type])
                | (cases operation; simp [Value.type])
  | @call locals args values name result _ callee ih =>
      intro formed caller type checked
      cases found : program.findSignature? name with
      | none => simp [inferType, found] at checked
      | some fn =>
          simp only [inferType, found] at checked
          split at checked
          · cases checked
          · simp only [pure_bind] at checked
            obtain ⟨types, _, rest⟩ := except_bind_ok.mp checked
            obtain ⟨finished, _, rest⟩ := except_bind_ok.mp rest
            obtain rfl := except_pure_ok.mp rest
            exact typed name values result callee fn found
  | @matchValue locals expr input arms bindings body result _ selected _ valueIH bodyIH =>
      intro formed caller type checked
      simp only [inferType] at checked
      obtain ⟨inputType, inputRun, rest⟩ := except_bind_ok.mp checked
      obtain ⟨shape, inputFormed⟩ := valueIH formed caller inputType inputRun
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
          exact bodyIH (Environment.wellFormed_append.mpr
            ⟨selectArm_wellFormed inputFormed selected, formed⟩) caller branchType (by
            simpa only [environmentTypes_append] using checkArms_selected allChecked inputFormed selected)
  | nil =>
      rename_i formed caller types checked
      simp only [inferTypes, except_pure_ok] at checked
      subst types
      exact ⟨rfl, by simp⟩
  | cons _ _ headIH tailIH =>
      rename_i formed caller types checked
      simp only [inferTypes] at checked
      obtain ⟨headType, headRun, rest⟩ := except_bind_ok.mp checked
      obtain ⟨tailTypes, tailRun, rest⟩ := except_bind_ok.mp rest
      obtain rfl := except_pure_ok.mp rest
      obtain ⟨headType, headFormed⟩ := headIH formed caller headType headRun
      obtain ⟨tailTypes, tailFormed⟩ := tailIH formed caller tailTypes tailRun
      exact ⟨by simp [headType, tailTypes], by simpa [headFormed] using tailFormed⟩

theorem ROMEvalExprWith.type [Field F] [DecidableEq F] {program : Program F} {calls : CallRelation F}
    (typed : CallsTyped program calls) (memory : rom.WellFormed program.enums)
    {locals : Environment F} {expr : Expr F} {result : Value F}
    (evaluated : ROMEvalExprWith program.enums rom calls locals expr result)
    (formed : locals.WellFormed program.enums) (caller : String) (type : Ty)
    (checked : inferType program caller (environmentTypes locals) expr = .ok type) : result.type = type :=
  (evaluated.wellTyped typed memory formed caller type checked).1

end Aiur
