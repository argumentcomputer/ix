import Aiur.Semantics
import Aiur.Semantics.CallFacts
import Aiur.Semantics.CallTypes
import Aiur.Tables
import Aiur.Generic.SourceSemantics
import Aiur.Modules.Correctness

/-!
# Composable Step & Inversion Lemmas for Aiur Source Semantics

This module provides `iff` inversion and introduction lemmas for concrete
`Aiur.EvalExpr` / `Aiur.EvalArgs` / `Aiur.EvalFn`, generic
`Aiur.Generic.SourceSemantics.EvalExpr` / `EvalArgs` / `EvalFn`, and
`Aiur.Modules.Prepared.EvalFn`, together with the Hint-Invariance
(non-deterministic witness soundness) Hoare combinator.
-/

namespace Aiur

variable {F : Type} [Field F] [DecidableEq F]

/-! ## Concrete `Aiur.EvalExpr`, `Aiur.EvalArgs`, and `Aiur.EvalFn` Step Lemmas -/

theorem evalExpr_literal_iff {program : Program F} {locals : Environment F Nat}
    {value : F} {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr program locals (.literal value) before result after ↔
      result = .field value ∧ after = before := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .literal

theorem evalExpr_var_iff {program : Program F} {locals : Environment F Nat}
    {name : String} {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr program locals (.var name) before result after ↔
      locals.find? (·.1 == name) = some (name, result) ∧ after = before := by
  constructor
  · intro h; cases h with | var lookup => exact ⟨lookup, rfl⟩
  · rintro ⟨lookup, rfl⟩; exact .var lookup

theorem evalExpr_tuple_iff {program : Program F} {locals : Environment F Nat}
    {exprs : List (Expr F)} {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr program locals (.tuple exprs) before result after ↔
      ∃ values, EvalArgs program locals exprs before values after ∧ result = .tuple values := by
  constructor
  · intro h; cases h with | tuple items => exact ⟨_, items, rfl⟩
  · rintro ⟨values, items, rfl⟩; exact .tuple items

theorem evalExpr_construct_iff {program : Program F} {locals : Environment F Nat}
    {name : String} {ctor : String} {exprs : List (Expr F)}
    {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr program locals (.construct name ctor exprs) before result after ↔
      ∃ values, EvalArgs program locals exprs before values after ∧
        result = .construct name ctor values := by
  constructor
  · intro h; cases h with | construct items => exact ⟨_, items, rfl⟩
  · rintro ⟨values, items, rfl⟩; exact .construct items

theorem evalExpr_project_iff {program : Program F} {locals : Environment F Nat}
    {expr : Expr F} {index : Nat} {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr program locals (.project expr index) before result after ↔
      ∃ input, EvalExpr program locals expr before input after ∧
        projectValue input index = .ok result := by
  constructor
  · intro h; cases h with | project value projected => exact ⟨_, value, projected⟩
  · rintro ⟨input, value, projected⟩; exact .project value projected

theorem evalExpr_letValue_iff {program : Program F} {locals : Environment F Nat}
    {pattern : Pattern F} {expr rest : Expr F}
    {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr program locals (.letValue pattern expr rest) before result after ↔
      ∃ input middle bindings,
        EvalExpr program locals expr before input middle ∧
        pattern.bindings input = some bindings ∧
        EvalExpr program (bindings ++ locals) rest middle result after := by
  constructor
  · intro h; cases h with | letValue value matched body => exact ⟨_, _, _, value, matched, body⟩
  · rintro ⟨input, middle, bindings, value, matched, body⟩
    exact .letValue value matched body

theorem evalExpr_store_iff {program : Program F} {locals : Environment F Nat}
    {expr : Expr F} {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr program locals (.store expr) before result after ↔
      ∃ input middle,
        EvalExpr program locals expr before input middle ∧
        result = .ptr input.type middle.length ∧
        after = middle ++ [input] := by
  constructor
  · intro h; cases h with | store value => exact ⟨_, _, value, rfl, rfl⟩
  · rintro ⟨input, middle, value, rfl, rfl⟩; exact .store value

theorem evalExpr_load_iff {program : Program F} {locals : Environment F Nat}
    {expr : Expr F} {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr program locals (.load expr) before result after ↔
      ∃ input, EvalExpr program locals expr before input after ∧
        loadValue after input = .ok result := by
  constructor
  · intro h; cases h with | load pointer loaded => exact ⟨_, pointer, loaded⟩
  · rintro ⟨input, pointer, loaded⟩; exact .load pointer loaded

theorem evalExpr_hint_iff {program : Program F} {locals : Environment F Nat}
    {type : Ty} {expr : Expr F} {channel : String}
    {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr program locals (.hint type expr channel) before result after ↔
      ∃ (input : SourceValue F) (value : Constant F),
        EvalExpr program locals expr before input after ∧
        value.WellTyped program.enums type ∧
        result = value.toValue := by
  constructor
  · intro h
    cases h
    rename_i input value typed key
    exact ⟨input, value, key, typed, rfl⟩
  · rintro ⟨input, value, key, typed, rfl⟩
    exact .hint key typed

theorem evalExpr_neg_iff {program : Program F} {locals : Environment F Nat}
    {expr : Expr F} {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr program locals (.neg expr) before result after ↔
      ∃ input, EvalExpr program locals expr before input after ∧
        evalNeg input = .ok result := by
  constructor
  · intro h; cases h with | neg value operation => exact ⟨_, value, operation⟩
  · rintro ⟨input, value, operation⟩; exact .neg value operation

theorem evalExpr_assertEq_iff {program : Program F} {locals : Environment F Nat}
    {op : Assertion} {lhs rhs : Expr F}
    {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr program locals (.assertEq op lhs rhs) before result after ↔
      ∃ x middle y,
        EvalExpr program locals lhs before x middle ∧
        EvalExpr program locals rhs middle y after ∧
        evalAssertEq op x y = .ok result := by
  constructor
  · intro h; cases h with | assertEq left right operation => exact ⟨_, _, _, left, right, operation⟩
  · rintro ⟨x, middle, y, left, right, operation⟩; exact .assertEq left right operation

theorem evalExpr_binary_iff {program : Program F} {locals : Environment F Nat}
    {op : BinOp} {lhs rhs : Expr F}
    {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr program locals (.binary op lhs rhs) before result after ↔
      ∃ x middle y,
        EvalExpr program locals lhs before x middle ∧
        EvalExpr program locals rhs middle y after ∧
        evalBinOp op x y = .ok result := by
  constructor
  · intro h; cases h with | binary left right operation => exact ⟨_, _, _, left, right, operation⟩
  · rintro ⟨x, middle, y, left, right, operation⟩; exact .binary left right operation

theorem evalExpr_call_iff {program : Program F} {locals : Environment F Nat}
    {name : String} {args : List (Expr F)}
    {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr program locals (.call name args) before result after ↔
      ∃ values middle,
        EvalArgs program locals args before values middle ∧
        EvalFn program name values middle result after := by
  constructor
  · intro h; cases h with | call arguments callee => exact ⟨_, _, arguments, callee⟩
  · rintro ⟨values, middle, arguments, callee⟩; exact .call arguments callee

theorem evalFn_iff {program : Program F} {name : String} {args : List (SourceValue F)}
    {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalFn program name args before result after ↔
      ∃ locals expr,
        prepareCall program name args = .ok (locals, expr) ∧
        EvalExpr program locals expr before result after := by
  constructor
  · intro h; cases h with | intro prepared body => exact ⟨_, _, prepared, body⟩
  · rintro ⟨locals, expr, prepared, body⟩; exact .intro prepared body

theorem evalExpr_call_function_iff {program : Program F} {locals : Environment F Nat}
    {name : String} {fn : Function F} {args : List (Expr F)}
    {before : Heap F} {result : SourceValue F} {after : Heap F}
    (found : program.findFunction? name = some fn) :
    EvalExpr program locals (.call name args) before result after ↔
      ∃ values middle,
        EvalArgs program locals args before values middle ∧
        fn.params.map Prod.snd = values.map Value.type ∧
        (∀ arg ∈ values, arg.wellFormed program.enums = true) ∧
        EvalExpr program ((fn.params.map Prod.fst).zip values) fn.body middle result after := by
  rw [evalExpr_call_iff]
  constructor
  · rintro ⟨values, middle, arguments, callee⟩
    rw [evalFn_iff] at callee
    obtain ⟨callLocals, expr, prepared, body⟩ := callee
    rcases prepareCall_spec prepared with ⟨fn', found', types, formed, rfl, rfl⟩ | ⟨_, absent, _⟩
    · rw [found] at found'
      cases found'
      exact ⟨values, middle, arguments, types, formed, body⟩
    · rw [found] at absent
      contradiction
  · rintro ⟨values, middle, arguments, types, formed, body⟩
    exact ⟨values, middle, arguments, .intro (prepareCall_of_types found types formed) body⟩

theorem evalExpr_call_table_iff {program : Program F} {locals : Environment F Nat}
    {name : String} {args : List (Expr F)}
    {before : Heap F} {result : SourceValue F} {after : Heap F}
    (absent : program.findFunction? name = none) :
    EvalExpr program locals (.call name args) before result after ↔
      ∃ (values : List (SourceValue F)) (value : Constant F),
        EvalArgs program locals args before values after ∧
        lookupMap program name values = .ok value ∧
        result = value.toValue := by
  rw [evalExpr_call_iff]
  constructor
  · rintro ⟨values, middle, arguments, callee⟩
    rw [evalFn_iff] at callee
    obtain ⟨callLocals, expr, prepared, body⟩ := callee
    rcases prepareCall_spec prepared with ⟨fn', found', _⟩ | ⟨value, _, looked, rfl, rfl⟩
    · rw [absent] at found'
      contradiction
    · obtain ⟨rfl, rfl⟩ := EvalExpr.constant_result value body
      exact ⟨values, value, arguments, looked, rfl⟩
  · rintro ⟨values, value, arguments, looked, rfl⟩
    exact ⟨values, after, arguments, .intro (prepareCall_map absent looked) (Constant.evaluates value)⟩

theorem evalExpr_matchValue_iff {program : Program F} {locals : Environment F Nat}
    {expr : Expr F} {arms : List (Pattern F × Expr F)}
    {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr program locals (.matchValue expr arms) before result after ↔
      ∃ input middle bindings body,
        EvalExpr program locals expr before input middle ∧
        selectArm input arms = some (bindings, body) ∧
        EvalExpr program (bindings ++ locals) body middle result after := by
  constructor
  · intro h; cases h with | matchValue value selected branch => exact ⟨_, _, _, _, value, selected, branch⟩
  · rintro ⟨input, middle, bindings, body, value, selected, branch⟩
    exact .matchValue value selected branch

theorem evalArgs_nil_iff {program : Program F} {locals : Environment F Nat}
    {before : Heap F} {values : List (SourceValue F)} {after : Heap F} :
    EvalArgs program locals [] before values after ↔
      values = [] ∧ after = before := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .nil

theorem evalArgs_cons_iff {program : Program F} {locals : Environment F Nat}
    {expr : Expr F} {exprs : List (Expr F)}
    {before : Heap F} {results : List (SourceValue F)} {after : Heap F} :
    EvalArgs program locals (expr :: exprs) before results after ↔
      ∃ value middle values,
        EvalExpr program locals expr before value middle ∧
        EvalArgs program locals exprs middle values after ∧
        results = value :: values := by
  constructor
  · intro h; cases h with | cons head tail => exact ⟨_, _, _, head, tail, rfl⟩
  · rintro ⟨value, middle, values, head, tail, rfl⟩; exact .cons head tail

/-! ## Concrete Hint-Invariance (Non-Deterministic Soundness) Combinators -/

/-- If a `let pattern = hint ...; rest` expression evaluates and every well-typed
hint witness `c` that matches `pattern` and satisfies the continuation `rest`
establishes `P c result after`, then some well-typed witness `c` satisfies `P`. -/
theorem evalExpr_let_hint_invariance {program : Program F} {locals : Environment F Nat}
    {pattern : Pattern F} {type : Ty} {keyExpr : Expr F} {channel : String} {rest : Expr F}
    {before : Heap F} {result : SourceValue F} {after : Heap F}
    {P : Constant F → SourceValue F → Heap F → Prop}
    (eval : EvalExpr program locals (.letValue pattern (.hint type keyExpr channel) rest) before result after)
    (hPost : ∀ (c : Constant F) (middle : Heap F) (bindings : Environment F Nat),
      c.WellTyped program.enums type →
      pattern.bindings c.toValue = some bindings →
      EvalExpr program (bindings ++ locals) rest middle result after →
      P c result after) :
    ∃ c : Constant F, c.WellTyped program.enums type ∧ P c result after := by
  rw [evalExpr_letValue_iff] at eval
  obtain ⟨input, middle, bindings, hHint, matched, body⟩ := eval
  rw [evalExpr_hint_iff] at hHint
  obtain ⟨_, c, _, typed, rfl⟩ := hHint
  exact ⟨c, typed, hPost c middle bindings typed matched body⟩

/-- Function-level Hint-Invariance combinator for concrete `EvalFn`. -/
theorem evalFn_hint_invariance {program : Program F} {name : String} {fn : Function F}
    {args : List (SourceValue F)} {before : Heap F} {result : SourceValue F} {after : Heap F}
    {pattern : Pattern F} {type : Ty} {keyExpr : Expr F} {channel : String} {rest : Expr F}
    {P : Constant F → SourceValue F → Heap F → Prop}
    (found : program.findFunction? name = some fn)
    (hBody : fn.body = .letValue pattern (.hint type keyExpr channel) rest)
    (eval : EvalFn program name args before result after)
    (hPost : ∀ (c : Constant F) (middle : Heap F) (bindings : Environment F Nat),
      c.WellTyped program.enums type →
      pattern.bindings c.toValue = some bindings →
      EvalExpr program (bindings ++ (fn.params.map Prod.fst).zip args) rest middle result after →
      P c result after) :
    ∃ c : Constant F, c.WellTyped program.enums type ∧ P c result after := by
  rw [evalFn_iff] at eval
  obtain ⟨locals, expr, prepared, body⟩ := eval
  rcases prepareCall_spec prepared with ⟨fn', found', _, _, rfl, rfl⟩ | ⟨_, absent, _⟩
  · rw [found] at found'
    cases found'
    rw [hBody] at body
    exact evalExpr_let_hint_invariance body hPost
  · rw [found] at absent
    contradiction

namespace Generic.SourceSemantics

/-! ## Generic `SourceSemantics` Step Lemmas -/

theorem evalExpr_literal_iff {world : World F} {types : Types} {locals : Environment F Nat}
    {value : F} {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr world types locals (.literal value) before result after ↔
      result = .field value ∧ after = before := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .literal

theorem evalExpr_var_iff {world : World F} {types : Types} {locals : Environment F Nat}
    {name : String} {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr world types locals (.var name) before result after ↔
      locals.find? (·.1 == name) = some (name, result) ∧ after = before := by
  constructor
  · intro h; cases h with | var lookup => exact ⟨lookup, rfl⟩
  · rintro ⟨lookup, rfl⟩; exact .var lookup

theorem evalExpr_tuple_iff {world : World F} {types : Types} {locals : Environment F Nat}
    {exprs : List (Expr F)} {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr world types locals (.tuple exprs) before result after ↔
      ∃ values, EvalArgs world types locals exprs before values after ∧ result = .tuple values := by
  constructor
  · intro h; cases h with | tuple items => exact ⟨_, items, rfl⟩
  · rintro ⟨values, items, rfl⟩; exact .tuple items

theorem evalExpr_array_iff {world : World F} {types : Types} {locals : Environment F Nat}
    {exprs : List (Expr F)} {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr world types locals (.array exprs) before result after ↔
      ∃ values, EvalArgs world types locals exprs before values after ∧ result = .tuple values := by
  constructor
  · intro h; cases h with | array items => exact ⟨_, items, rfl⟩
  · rintro ⟨values, items, rfl⟩; exact .array items

theorem evalExpr_let_iff {world : World F} {types : Types} {locals : Environment F Nat}
    {pattern : Pattern F} {expr rest : Expr F}
    {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr world types locals (.letValue pattern expr rest) before result after ↔
      ∃ input middle bindings,
        EvalExpr world types locals expr before input middle ∧
        world.matchPattern types middle pattern input = .ok (some bindings) ∧
        EvalExpr world types (bindings ++ locals) rest middle result after := by
  constructor
  · intro h; cases h with | letValue value matched body => exact ⟨_, _, _, value, matched, body⟩
  · rintro ⟨input, middle, bindings, value, matched, body⟩
    exact .letValue value matched body

theorem evalExpr_store_iff {world : World F} {types : Types} {locals : Environment F Nat}
    {expr : Expr F} {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr world types locals (.store expr) before result after ↔
      ∃ input middle,
        EvalExpr world types locals expr before input middle ∧
        result = .ptr input.type middle.length ∧
        after = middle ++ [input] := by
  constructor
  · intro h; cases h with | store value => exact ⟨_, _, value, rfl, rfl⟩
  · rintro ⟨input, middle, value, rfl, rfl⟩; exact .store value

theorem evalExpr_load_iff {world : World F} {types : Types} {locals : Environment F Nat}
    {expr : Expr F} {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr world types locals (.load expr) before result after ↔
      ∃ input, EvalExpr world types locals expr before input after ∧
        loadValue after input = .ok result := by
  constructor
  · intro h; cases h with | load pointer loaded => exact ⟨_, pointer, loaded⟩
  · rintro ⟨input, pointer, loaded⟩; exact .load pointer loaded

theorem evalExpr_hint_iff {world : World F} {types : Types} {locals : Environment F Nat}
    {t : Ty} {expr : Expr F} {channel : String}
    {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr world types locals (.hint t expr channel) before result after ↔
      ∃ (input : SourceValue F) (value : Constant F),
        EvalExpr world types locals expr before input after ∧
        world.typed (t.subst types).toCore value = true ∧
        result = value.toValue := by
  constructor
  · intro h
    cases h
    rename_i input value typed key
    exact ⟨input, value, key, typed, rfl⟩
  · rintro ⟨input, value, key, typed, rfl⟩
    exact .hint key typed

theorem evalExpr_builtin_iff {world : World F} {types : Types} {locals : Environment F Nat}
    {operation : Builtin} {exprs : List (Expr F)}
    {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr world types locals (.builtin operation exprs) before result after ↔
      ∃ values,
        EvalArgs world types locals exprs before values after ∧
        operation.apply values = .ok result := by
  constructor
  · intro h; cases h with | builtin items applied => exact ⟨_, items, applied⟩
  · rintro ⟨values, items, applied⟩; exact .builtin items applied

theorem evalArgs_nil_iff {world : World F} {types : Types} {locals : Environment F Nat}
    {before : Heap F} {values : List (SourceValue F)} {after : Heap F} :
    EvalArgs world types locals [] before values after ↔
      values = [] ∧ after = before := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .nil

theorem evalArgs_cons_iff {world : World F} {types : Types} {locals : Environment F Nat}
    {expr : Expr F} {exprs : List (Expr F)}
    {before : Heap F} {results : List (SourceValue F)} {after : Heap F} :
    EvalArgs world types locals (expr :: exprs) before results after ↔
      ∃ value middle values,
        EvalExpr world types locals expr before value middle ∧
        EvalArgs world types locals exprs middle values after ∧
        results = value :: values := by
  constructor
  · intro h; cases h with | cons head tail => exact ⟨_, _, _, head, tail, rfl⟩
  · rintro ⟨value, middle, values, head, tail, rfl⟩; exact .cons head tail

theorem evalExpr_assertEq_iff {world : World F} {types : Types} {locals : Environment F Nat}
    {assertion : Assertion} {lhs rhs : Expr F}
    {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr world types locals (.builtin (.assertEq assertion) [lhs, rhs]) before result after ↔
      ∃ x middle y,
        EvalExpr world types locals lhs before x middle ∧
        EvalExpr world types locals rhs middle y after ∧
        evalAssertEq assertion x y = .ok result := by
  rw [evalExpr_builtin_iff]
  constructor
  · rintro ⟨values, items, applied⟩
    rw [evalArgs_cons_iff] at items
    obtain ⟨x, middle, rest1, hLhs, items1, rfl⟩ := items
    rw [evalArgs_cons_iff] at items1
    obtain ⟨y, middle2, rest2, hRhs, items2, rfl⟩ := items1
    rw [evalArgs_nil_iff] at items2
    obtain ⟨rfl, rfl⟩ := items2
    exact ⟨x, middle, y, hLhs, hRhs, applied⟩
  · rintro ⟨x, middle, y, hLhs, hRhs, applied⟩
    exact ⟨[x, y], .cons hLhs (.cons hRhs .nil), applied⟩

theorem evalExpr_binary_iff {world : World F} {types : Types} {locals : Environment F Nat}
    {op : BinOp} {lhs rhs : Expr F}
    {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr world types locals (.binary op lhs rhs) before result after ↔
      ∃ x middle y,
        EvalExpr world types locals lhs before x middle ∧
        EvalExpr world types locals rhs middle y after ∧
        evalBinOp op x y = .ok result := by
  constructor
  · intro h; cases h with | binary left right operation => exact ⟨_, _, _, left, right, operation⟩
  · rintro ⟨x, middle, y, left, right, operation⟩; exact .binary left right operation

theorem evalExpr_neg_iff {world : World F} {types : Types} {locals : Environment F Nat}
    {expr : Expr F} {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr world types locals (.neg expr) before result after ↔
      ∃ input, EvalExpr world types locals expr before input after ∧
        evalNeg input = .ok result := by
  constructor
  · intro h; cases h with | neg value operation => exact ⟨_, value, operation⟩
  · rintro ⟨input, value, operation⟩; exact .neg value operation

theorem evalExpr_block_iff {world : World F} {types : Types} {locals : Environment F Nat}
    {label : String} {expr : Expr F}
    {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr world types locals (.control (.block label) expr) before result after ↔
      EvalExpr world types locals expr before result after ∨
      EvalExit world types locals expr before (.block label) result after := by
  constructor
  · intro h
    cases h with
    | block body => exact Or.inl body
    | blockExit body => exact Or.inr body
  · rintro (body | body)
    · exact .block body
    · exact .blockExit body

theorem evalExpr_call_iff {world : World F} {types : Types} {locals : Environment F Nat}
    {name : String} {typeArgs : Option (List Ty)} {args : List (Expr F)}
    {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr world types locals (.call name typeArgs args) before result after ↔
      ∃ values middle,
        EvalArgs world types locals args before values middle ∧
        EvalFn world (instanceName types name typeArgs) values middle result after := by
  constructor
  · intro h; cases h with | call arguments callee => exact ⟨_, _, arguments, callee⟩
  · rintro ⟨values, middle, arguments, callee⟩; exact .call arguments callee

theorem evalExpr_matchValue_iff {world : World F} {types : Types} {locals : Environment F Nat}
    {expr : Expr F} {arms : List (Pattern F × Expr F)}
    {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalExpr world types locals (.matchValue expr arms) before result after ↔
      ∃ input middle bindings body,
        EvalExpr world types locals expr before input middle ∧
        selectArm world types middle input arms = .ok (some (bindings, body)) ∧
        EvalExpr world types (bindings ++ locals) body middle result after := by
  constructor
  · intro h; cases h with | matchValue value selected branch => exact ⟨_, _, _, _, value, selected, branch⟩
  · rintro ⟨input, middle, bindings, body, value, selected, branch⟩
    exact .matchValue value selected branch

theorem evalFn_step_iff {world : World F} {name : String} {args : List (SourceValue F)}
    {before : Heap F} {result : SourceValue F} {after : Heap F} :
    EvalFn world name args before result after ↔
      ∃ types locals expr,
        world.prepare name args = .ok (types, locals, expr) ∧
        (EvalExpr world types locals expr before result after ∨
         EvalExit world types locals expr before .function result after) := by
  constructor
  · intro h
    cases h with
    | intro prepared body => exact ⟨_, _, _, prepared, Or.inl body⟩
    | returned prepared body => exact ⟨_, _, _, prepared, Or.inr body⟩
  · rintro ⟨types, locals, expr, prepared, body | body⟩
    · exact .intro prepared body
    · exact .returned prepared body

/-- Generic `SourceSemantics` Hint-Invariance combinator. -/
theorem evalExpr_let_hint_invariance {world : World F} {types : Types} {locals : Environment F Nat}
    {pattern : Pattern F} {t : Ty} {keyExpr : Expr F} {channel : String} {rest : Expr F}
    {before : Heap F} {result : SourceValue F} {after : Heap F}
    {P : Constant F → SourceValue F → Heap F → Prop}
    (eval : EvalExpr world types locals (.letValue pattern (.hint t keyExpr channel) rest) before result after)
    (hPost : ∀ (c : Constant F) (middle : Heap F) (bindings : Environment F Nat),
      world.typed (t.subst types).toCore c = true →
      world.matchPattern types middle pattern c.toValue = .ok (some bindings) →
      EvalExpr world types (bindings ++ locals) rest middle result after →
      P c result after) :
    ∃ c : Constant F, world.typed (t.subst types).toCore c = true ∧ P c result after := by
  rw [evalExpr_let_iff] at eval
  obtain ⟨input, middle, bindings, hHint, matched, body⟩ := eval
  rw [evalExpr_hint_iff] at hHint
  obtain ⟨_, c, _, typed, rfl⟩ := hHint
  exact ⟨c, typed, hPost c middle bindings typed matched body⟩

end Generic.SourceSemantics

namespace Modules

theorem Prepared.evalFn_iff {program : Program F} {p : Prepared program}
    {name : String} {args : List (SourceValue F)} {value : SourceValue F} {heap : Heap F} :
    p.EvalFn name args value heap ↔
      ∃ entry, p.find? name = some entry ∧
        Generic.SourceSemantics.EvalFn p.environment.source.world entry.resolved.name args [] value heap :=
  Iff.rfl

end Modules

end Aiur
