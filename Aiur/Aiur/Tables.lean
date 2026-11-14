import Aiur.TypecheckFacts
import Aiur.Semantics.CallTypes
import Aiur.Semantics
import Aiur.EvalCorrectness

namespace Aiur

set_option linter.unusedSimpArgs false

variable {F : Type}

theorem Program.signature_of_function {program : Program F} {name : String} {fn : Function F}
    (found : program.findFunction? name = some fn) :
    program.findSignature? name = some ⟨fn.params, fn.result⟩ := by
  simp [Program.findSignature?, found]

theorem Program.signature_of_map {program : Program F} {name : String} {map : MapDecl}
    (absent : program.findFunction? name = none) (found : program.findMap? name = some map) :
    program.findSignature? name = some ⟨map.params, map.result⟩ := by
  simp [Program.findSignature?, absent, found]

/-- Expose the typed, aligned static row selected by a successful lookup. -/
theorem lookupMap_spec [DecidableEq F] {program : Program F} {name : String}
    {args : List (Value F A)} {value : Constant F}
    (looked : lookupMap program name args = .ok value) :
    ∃ map key, program.findMap? name = some map ∧
      map.params.map Prod.snd = args.map Value.type ∧
      (∀ arg ∈ args, arg.wellFormed program.enums = true) ∧
      (Value.tuple args).toConstant? = some key ∧
      (key, value) ∈ program.mapRows map ∧ value.hasType program.enums map.result = true := by
  cases found : program.findMap? name with
  | none => simp [lookupMap, found] at looked
  | some map =>
      by_cases arity : map.params.length = args.length
      · simp only [lookupMap, found, arity, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          pure_bind] at looked
        obtain ⟨done, arguments, rest⟩ := except_bind_ok.mp looked
        cases done
        have checked := checked_arguments_types program.enums name map.params args arity (by
          simpa [bind, Except.bind, pure, Except.pure] using arguments)
        cases extracted : (Value.tuple args).toConstant? with
        | none => simp [extracted] at rest
        | some key =>
            simp only [extracted] at rest
            cases row : (program.mapRows map).find? (fun row => decide (row.1 = key)) with
            | none => simp [row] at rest
            | some pair =>
                obtain ⟨input, output⟩ := pair
                have same : input = key := by simpa using List.find?_some row
                subst input
                simp only [row] at rest
                split at rest
                · cases rest
                · rename_i valid
                  have valid : output.hasType program.enums map.result = true := by simpa using valid
                  obtain rfl := except_pure_ok.mp rest
                  exact ⟨map, key, rfl, checked.1, checked.2, rfl,
                    List.mem_of_find?_eq_some row, valid⟩
      · simp [lookupMap, found, arity, bind, Except.bind] at looked

theorem prepareCall_map [DecidableEq F] {program : Program F} {name : String}
    {args : List (Value F A)} {value : Constant F}
    (absent : program.findFunction? name = none)
    (looked : lookupMap program name args = .ok value) :
    prepareCall program name args = .ok ([], value.toExpr) := by
  simp [prepareCall, absent, looked, bind, Except.bind, pure, Except.pure]

theorem lookupMap_mapAddress [DecidableEq F] (program : Program F) (name : String)
    (args : List (Value F A)) (encode : A → B) :
    lookupMap program name (args.map (Value.mapAddress encode)) = lookupMap program name args := by
  have same : (Value.tuple (args.map (Value.mapAddress encode))).toConstant? =
      (Value.tuple args).toConstant? := by
    simpa only [Value.mapAddress] using Value.toConstant_mapAddress (.tuple args) encode
  unfold lookupMap
  cases program.findMap? name with
  | none => rfl
  | some map =>
      simp only [List.length_map, List.zip_map_right, List.forIn_map, Prod.map_fst,
        Prod.map_snd, id_eq, Value.type_mapAddress, Value.wellFormed_mapAddress, same]

theorem ROMEvalArgsWith.map_iff [Field F] [DecidableEq F] {decls : Declarations}
    {rom : ROM F} {calls : CallRelation F} {locals : Environment F}
    (items : List α) (expression : α → Expr F) (value : α → Value F)
    (each : ∀ item ∈ items, ∀ result,
      ROMEvalExprWith decls rom calls locals (expression item) result ↔ result = value item)
    {results : List (Value F)} :
    ROMEvalArgsWith decls rom calls locals (items.map expression) results ↔ results = items.map value := by
  induction items generalizing results with
  | nil =>
      constructor
      · intro evaluated; cases evaluated; rfl
      · rintro rfl; exact .nil
  | cons item items ih =>
      simp only [List.map_cons]
      constructor
      · intro evaluated
        cases evaluated with
        | cons head tail =>
            have h := (each item (by simp) _).mp head
            have t := (ih (fun v mem => each v (by simp [mem]))).mp tail
            simp [h, t]
      · rintro rfl
        exact .cons ((each item (by simp) _).mpr rfl)
          ((ih (fun v mem => each v (by simp [mem]))).mpr rfl)

/-- Returning a constant is independent of the ROM and every call relation. -/
theorem ROMEvalExprWith.constant_iff [Field F] [DecidableEq F] {decls : Declarations}
    {rom : ROM F} {calls : CallRelation F} {locals : Environment F}
    (constant : Constant F) {result : Value F} :
    ROMEvalExprWith decls rom calls locals constant.toExpr result ↔ result = constant.toValue := by
  cases constant with
  | field x =>
      simp only [Constant.toExpr, Constant.toValue, Value.mapAddress]
      constructor
      · intro evaluated; cases evaluated; rfl
      · rintro rfl; exact .literal
  | ptr _ address => exact Empty.elim address
  | tuple items =>
      have arguments (results : List (Value F)) := ROMEvalArgsWith.map_iff
        (decls := decls) (rom := rom) (calls := calls) (locals := locals) (results := results)
        items Constant.toExpr Constant.toValue
        (fun item _ _ => ROMEvalExprWith.constant_iff (decls := decls) item)
      simp only [Constant.toExpr, Constant.toValue, Value.mapAddress]
      constructor
      · intro evaluated
        cases evaluated with
        | tuple evaluated => rw [arguments _] at evaluated; subst evaluated; rfl
      · rintro rfl
        exact .tuple ((arguments _).mpr rfl)
  | construct name ctor items =>
      have arguments (results : List (Value F)) := ROMEvalArgsWith.map_iff
        (decls := decls) (rom := rom) (calls := calls) (locals := locals) (results := results)
        items Constant.toExpr Constant.toValue
        (fun item _ _ => ROMEvalExprWith.constant_iff (decls := decls) item)
      simp only [Constant.toExpr, Constant.toValue, Value.mapAddress]
      constructor
      · intro evaluated
        cases evaluated with
        | construct evaluated => rw [arguments _] at evaluated; subst evaluated; rfl
      · rintro rfl
        exact .construct ((arguments _).mpr rfl)
termination_by sizeOf constant

theorem EvalArgs.constants [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F Nat} {heap : Heap F}
    (items : List α) (expression : α → Expr F) (value : α → SourceValue F)
    (each : ∀ item ∈ items, EvalExpr program locals (expression item) heap (value item) heap) :
    EvalArgs program locals (items.map expression) heap (items.map value) heap := by
  induction items with
  | nil => exact .nil
  | cons item items ih => exact .cons (each item (by simp)) (ih (fun v h => each v (by simp [h])))

/-- Static results do not allocate or inspect memory. -/
theorem Constant.evaluates [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F Nat} {heap : Heap F} (constant : Constant F) :
    EvalExpr program locals constant.toExpr heap constant.toValue heap := by
  cases constant with
  | field => simpa [Constant.toExpr, Constant.toValue, Value.mapAddress] using
      (@EvalExpr.literal F _ _ program locals _ heap)
  | ptr _ address => exact Empty.elim address
  | tuple items =>
      simp only [Constant.toExpr, Constant.toValue, Value.mapAddress]
      exact .tuple (EvalArgs.constants items Constant.toExpr Constant.toValue
        (fun item _ => Constant.evaluates item))
  | construct name ctor items =>
      simp only [Constant.toExpr, Constant.toValue, Value.mapAddress]
      exact .construct (EvalArgs.constants items Constant.toExpr Constant.toValue
        (fun item _ => Constant.evaluates item))
termination_by sizeOf constant

theorem EvalArgs.constants_result [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F Nat} (items : List α) (expression : α → Expr F)
    (value : α → SourceValue F)
    (each : ∀ item ∈ items, ∀ before result after,
      EvalExpr program locals (expression item) before result after → result = value item ∧ after = before)
    {before after : Heap F} {results : List (SourceValue F)}
    (evaluated : EvalArgs program locals (items.map expression) before results after) :
    results = items.map value ∧ after = before := by
  induction items generalizing before results with
  | nil => cases evaluated; exact ⟨rfl, rfl⟩
  | cons item items ih =>
      cases evaluated with
      | cons head tail =>
          obtain ⟨rfl, rfl⟩ := each item (by simp) _ _ _ head
          obtain ⟨rfl, rfl⟩ := ih (fun x h => each x (by simp [h])) tail
          exact ⟨rfl, rfl⟩

/-- Constant results remain unique even when other functions contain hints. -/
theorem EvalExpr.constant_result [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F Nat} (constant : Constant F) {before after : Heap F}
    {result : SourceValue F} (evaluated : EvalExpr program locals constant.toExpr before result after) :
    result = constant.toValue ∧ after = before := by
  cases constant with
  | field x =>
      simp only [Constant.toExpr] at evaluated
      cases evaluated
      simp [Constant.toValue, Value.mapAddress]
  | ptr _ address => exact Empty.elim address
  | tuple items =>
      simp only [Constant.toExpr] at evaluated
      cases evaluated with
      | tuple arguments =>
          obtain ⟨rfl, rfl⟩ := EvalArgs.constants_result items Constant.toExpr Constant.toValue
            (fun item _ _ _ _ h => EvalExpr.constant_result item h) arguments
          simp [Constant.toValue, Value.mapAddress]
  | construct name ctor items =>
      simp only [Constant.toExpr] at evaluated
      cases evaluated with
      | construct arguments =>
          obtain ⟨rfl, rfl⟩ := EvalArgs.constants_result items Constant.toExpr Constant.toValue
            (fun item _ _ _ _ h => EvalExpr.constant_result item h) arguments
          simp [Constant.toValue, Value.mapAddress]
termination_by sizeOf constant

end Aiur
