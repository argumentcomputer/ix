import Aiur.Generic.RecordFacts
import Aiur.Generic.OpenCore
import Aiur.Generic.ArrayFacts

namespace Aiur.Generic.StructLowering
open SourceSemantics
variable [Field F] [DecidableEq F] {world : Engine.World F} {calls : CallRelation F}

private theorem pureArgs {es : List (Aiur.Expr F)} {vs : List (SourceValue F)}
    (rel : List.Forall₂ (fun e v => ∀ b w a,
      OpenCore.EvalExpr world calls locals e b w a ↔ w = v ∧ a = b) es vs) :
    OpenCore.EvalArgs world calls locals es before values after ↔ values = vs ∧ after = before := by
  induction rel generalizing before values with
  | nil => constructor <;> intro h
           · cases h; exact ⟨rfl, rfl⟩
           · obtain ⟨rfl, rfl⟩ := h; exact .nil
  | cons head _ ih =>
      constructor
      · intro h; cases h with
        | cons hv rest =>
            obtain ⟨rfl, rfl⟩ := (head _ _ _).mp hv
            obtain ⟨rfl, rfl⟩ := ih.mp rest
            exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩
        exact .cons ((head _ _ _).mpr ⟨rfl, rfl⟩) (ih.mpr ⟨rfl, rfl⟩)

private theorem recordProjects (head : RecordHead) (vs : List (SourceValue F)) :
    OpenCore.EvalArgs world calls (("$record", .tuple vs) :: locals)
      (head.order ((List.range vs.length).map fun i => .project (.var "$record") i) (.tuple []))
      before values after ↔ values = head.order vs (.tuple []) ∧ after = before := by
  apply pureArgs
  apply head.order_rel
  · apply List.forall₂_of_length_eq_of_get (by simp)
    intro i hi hj
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
    intro b w a
    constructor
    · intro ev; cases ev with
      | project ev op =>
          cases ev with
          | var found =>
              simp only [List.find?_cons, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq, true_and] at found
              cases found
              simpa [projectValue, List.getElem?_eq_getElem hj, pure, Except.pure] using op.symm
    · rintro ⟨rfl, rfl⟩
      exact .project (input := .tuple vs) (.var (by simp)) (by simp [projectValue, List.getElem?_eq_getElem hj])
  · intro b w a
    constructor
    · intro ev; cases ev with
      | tuple es => cases es; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact .tuple .nil

/-- Construction runs the written initializer sequence exactly once, then only rearranges values. -/
theorem record_iff {items : List (Aiur.Expr F)} :
    OpenCore.EvalExpr world calls locals (record types head items) before result after ↔
      ∃ values, OpenCore.EvalArgs world calls locals items before values after ∧
        result = .construct (constructorName types head.type) structConstructor (head.order values (.tuple [])) := by
  have lengths {es : List (Aiur.Expr F)} {vs b a}
      (ev : OpenCore.EvalArgs world calls locals es b vs a) : es.length = vs.length := by
    induction es generalizing vs b with
    | nil => cases ev; rfl
    | cons e es ih => cases ev with
      | cons _ rest => simp only [List.length_cons, ih rest]
  constructor
  · intro ev
    cases ev with
    | letValue operand matched body =>
        cases operand with
        | tuple args =>
            simp only [Aiur.Pattern.bindings, Option.some.injEq] at matched
            subst_vars
            cases body with
            | construct fields =>
                rw [lengths args] at fields
                obtain ⟨rfl, rfl⟩ := (recordProjects head _).mp fields
                exact ⟨_, args, rfl⟩
  · rintro ⟨values, args, rfl⟩
    apply OpenCore.EvalExpr.letValue (bindings := [("$record", .tuple values)]) (.tuple args)
      (by simp [Aiur.Pattern.bindings])
    apply OpenCore.EvalExpr.construct
    rw [lengths args]
    exact (recordProjects head values).mpr ⟨rfl, rfl⟩

private theorem wildcard_bindings (n : Nat) (values : List (SourceValue F)) :
    Aiur.Pattern.bindingsList (List.replicate n (.wildcard : Aiur.Pattern F)) values =
      if values.length = n then some [] else none := by
  induction n generalizing values with
  | zero => cases values <;> simp [Aiur.Pattern.bindingsList]
  | succ n ih =>
      cases values with
      | nil => simp [Aiur.Pattern.bindingsList]
      | cons v vs =>
          by_cases h : vs.length = n <;>
            simp [List.replicate_succ, Aiur.Pattern.bindingsList, Aiur.Pattern.bindings, ih, h]

private theorem fieldPatterns_bindings (count index : Nat) (bound : index < count)
    (values : List (SourceValue F)) :
    Aiur.Pattern.bindingsList (fieldPatterns count index) values =
      if values.length = count then values[index]?.map (fun v => [("$member", v)]) else none := by
  induction count generalizing index values with
  | zero => omega
  | succ n ih =>
      cases index with
      | zero =>
          cases values with
          | nil => simp [fieldPatterns, Aiur.Pattern.bindingsList]
          | cons v vs =>
              simp only [fieldPatterns, Aiur.Pattern.bindingsList, Aiur.Pattern.bindings, wildcard_bindings]
              by_cases h : vs.length = n <;> simp [h]
      | succ i =>
          cases values with
          | nil => simp [fieldPatterns, Aiur.Pattern.bindingsList]
          | cons v vs =>
              simp only [fieldPatterns, Aiur.Pattern.bindingsList, Aiur.Pattern.bindings, ih i (by omega)]
              by_cases h : vs.length = n <;> simp [h]

private theorem field_bindings (field : FieldRef) (bound : field.index < field.arity)
    (types : Types) (value : SourceValue F) (bindings : Environment F Nat) :
    (fieldPattern (field.subst types)).bindings value = some bindings ↔
      ∃ result, memberValue types field value = .ok result ∧ bindings = [("$member", result)] := by
  have name : nominalName [] ((field.owner.map (Ty.subst types)).getD (.named "$invalid" [])) =
      constructorName types (field.owner.getD (.named "$invalid" [])) := by
    cases field.owner <;> simp [nominalName, constructorName, Ty.subst_nil, Ty.subst] <;> rfl
  cases value <;> simp only [fieldPattern, FieldRef.subst, Aiur.Pattern.bindings,
    memberValue, name, fieldPatterns_bindings _ _ bound]
  all_goals try simp [bind, Except.bind]
  rename_i n c vs
  by_cases hn : n = constructorName types (field.owner.getD (.named "$invalid" []))
  · subst n
    by_cases hc : c = structConstructor
    · subst c
      by_cases hl : vs.length = field.arity
      · have hi : field.index < vs.length := by omega
        simp [hl, List.getElem?_eq_getElem hi, pure, Except.pure, eq_comm]
      · simp [hl, pure, Except.pure, bind, Except.bind]
    · simp [hc, Ne.symm hc, pure, Except.pure, bind, Except.bind]
  · simp [hn, Ne.symm hn, pure, Except.pure, bind, Except.bind]

/-- A named projection is exactly one operand evaluation followed by a nominal field read. -/
theorem member_iff (bound : field.index < field.arity) :
    OpenCore.EvalExpr world calls locals (member types operand field) before result after ↔
      ∃ value, OpenCore.EvalExpr world calls locals operand before value after ∧
        memberValue types field value = .ok result := by
  constructor
  · intro ev
    cases ev with
    | letValue operand matched body =>
        obtain ⟨value, op, rfl⟩ := (field_bindings field bound _ _ _).mp matched
        cases body with
        | var found =>
            simp only [List.cons_append, List.nil_append, List.find?_cons, beq_self_eq_true,
              Option.some.injEq, Prod.mk.injEq, true_and] at found
            cases found
            exact ⟨_, operand, op⟩
  · rintro ⟨value, operand, op⟩
    exact .letValue (bindings := [("$member", result)]) operand
      ((field_bindings field bound _ _ _).mpr ⟨result, op, rfl⟩) (.var (by simp))

end Aiur.Generic.StructLowering
