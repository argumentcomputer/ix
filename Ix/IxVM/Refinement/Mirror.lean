import Ix.IxVM.Refinement.Exec
import Aiur.Generic.LookupFacts
import Aiur.Generic.NativeCompleteness

/-! # Mirror lemmas: reading a source derivation off a concrete body

Track B, Phase 3 (`plans/ixvm-certification-gap.md`). A mirror lemma says
what every derivation of one function computes. Its proof walks the
function's body: each step inverts the derivation at the body's head
(`EvalExpr.*_inv`, one lemma per expression form), evaluates the side
conditions on the values found so far (pattern matches, arm selection,
binary operations), and uses the callees' mirror lemmas at calls. This
module is the helper library those proofs use:

* inversion: `EvalExpr.literal_inv`, `var_inv`, `load_inv`, `letValue_inv`,
  `matchValue_inv`, `call_inv`, `tuple_inv`, `array_inv`, `binary_inv`,
  `global_inv`, `EvalArgs.nil_inv`, `cons_inv`;
* constants: `constant_inv` (a constant expression evaluates to its value,
  and to nothing else);
* calls in a checked source's world: `EvalFn.function_inv` (a function with
  no control syntax runs its body with its parameters bound) and
  `EvalFn.map_inv` (a map call returns the map's row and leaves the heap);
* patterns: `matchPattern_bind`, `matchPattern_wildcard`, and the `simp` set
  `matchPattern_simps` for tuple, array and constructor patterns. -/

namespace Aiur.Generic.SourceSemantics

variable {F : Type} [Field F] [DecidableEq F] {world : World F} {types : Types}
  {locals : Environment F Nat} {before after : Heap F} {result : SourceValue F}

/-! ## Inversion at the body's head -/

theorem EvalExpr.literal_inv {x : F}
    (h : EvalExpr world types locals (.literal x) before result after) :
    result = .field x ∧ after = before := by
  cases h; exact ⟨rfl, rfl⟩

theorem EvalExpr.var_inv {name : String}
    (h : EvalExpr world types locals (.var name) before result after) :
    locals.find? (·.1 == name) = some (name, result) ∧ after = before := by
  cases h with | var lookup => exact ⟨lookup, rfl⟩

theorem EvalExpr.load_inv {e : Expr F}
    (h : EvalExpr world types locals (.load e) before result after) :
    ∃ input, EvalExpr world types locals e before input after ∧ loadValue after input = .ok result := by
  cases h with | load pointer loaded => exact ⟨_, pointer, loaded⟩

theorem EvalExpr.letValue_inv {pat : Pattern F} {e rest : Expr F}
    (h : EvalExpr world types locals (.letValue pat e rest) before result after) :
    ∃ input middle bindings, EvalExpr world types locals e before input middle ∧
      world.matchPattern types middle pat input = .ok (some bindings) ∧
      EvalExpr world types (bindings ++ locals) rest middle result after := by
  cases h with | letValue value matched body => exact ⟨_, _, _, value, matched, body⟩

theorem EvalExpr.matchValue_inv {e : Expr F} {arms : List (Pattern F × Expr F)}
    (h : EvalExpr world types locals (.matchValue e arms) before result after) :
    ∃ input middle bindings body, EvalExpr world types locals e before input middle ∧
      selectArm world types middle input arms = .ok (some (bindings, body)) ∧
      EvalExpr world types (bindings ++ locals) body middle result after := by
  cases h with | matchValue value selected branch => exact ⟨_, _, _, _, value, selected, branch⟩

theorem EvalExpr.call_inv {name : String} {typeArgs : Option (List Ty)} {args : List (Expr F)}
    (h : EvalExpr world types locals (.call name typeArgs args) before result after) :
    ∃ values middle, EvalArgs world types locals args before values middle ∧
      EvalFn world (instanceName types name typeArgs) values middle result after := by
  cases h with | call arguments callee => exact ⟨_, _, arguments, callee⟩

theorem EvalExpr.tuple_inv {es : List (Expr F)}
    (h : EvalExpr world types locals (.tuple es) before result after) :
    ∃ values, EvalArgs world types locals es before values after ∧ result = .tuple values := by
  cases h with | tuple items => exact ⟨_, items, rfl⟩

theorem EvalExpr.array_inv {es : List (Expr F)}
    (h : EvalExpr world types locals (.array es) before result after) :
    ∃ values, EvalArgs world types locals es before values after ∧ result = .tuple values := by
  cases h with | array items => exact ⟨_, items, rfl⟩

theorem EvalExpr.binary_inv {op : BinOp} {lhs rhs : Expr F}
    (h : EvalExpr world types locals (.binary op lhs rhs) before result after) :
    ∃ x y middle, EvalExpr world types locals lhs before x middle ∧
      EvalExpr world types locals rhs middle y after ∧ evalBinOp op x y = .ok result := by
  cases h with | binary left right operation => exact ⟨_, _, _, left, right, operation⟩

theorem EvalExpr.global_inv {name : String} {type : Ty}
    (h : EvalExpr world types locals (.global name (some type)) before result after) :
    ∃ pattern body, world.constant name (type.subst types) = .ok pattern ∧
      Consts.toExpr pattern = .ok body ∧ EvalExpr world [] [] body before result after := by
  cases h with | global lookup interpreted value => exact ⟨_, _, lookup, interpreted, value⟩

theorem EvalArgs.nil_inv {values : List (SourceValue F)}
    (h : EvalArgs world types locals [] before values after) : values = [] ∧ after = before := by
  cases h; exact ⟨rfl, rfl⟩

theorem EvalArgs.cons_inv {e : Expr F} {es : List (Expr F)} {values : List (SourceValue F)}
    (h : EvalArgs world types locals (e :: es) before values after) :
    ∃ v vs middle, values = v :: vs ∧ EvalExpr world types locals e before v middle ∧
      EvalArgs world types locals es middle vs after := by
  cases h with | cons head tail => exact ⟨_, _, _, rfl, head, tail⟩

/-! ## Constants -/

/-- **A constant expression evaluates to its value**, and the heap is
unchanged. -/
theorem constant_inv (world : World F) (value : Constant F) {types : Types}
    {locals : Environment F Nat} {before after : Heap F} {result : SourceValue F}
    (h : EvalExpr world types locals (constantExpr value) before result after) :
    result = value.toValue ∧ after = before := by
  have children (values : List (Constant F))
      (smaller : ∀ v ∈ values, sizeOf v < sizeOf value) :
      ∀ {results : List (SourceValue F)} {before after : Heap F},
        EvalArgs world types locals (values.map constantExpr) before results after →
          results = values.map (Value.mapAddress Empty.elim) ∧ after = before := by
    induction values with
    | nil => intro results before after h; cases h; exact ⟨rfl, rfl⟩
    | cons v vs ih =>
        intro results before after h
        rw [List.map_cons] at h
        obtain ⟨r, rs, middle, rfl, head, tail⟩ := h.cons_inv
        obtain ⟨rfl, rfl⟩ := constant_inv world v head
        obtain ⟨rfl, rfl⟩ := ih (fun x hx => smaller x (by simp [hx])) tail
        exact ⟨rfl, rfl⟩
  cases value with
  | field x =>
      simp only [constantExpr] at h
      obtain ⟨rfl, rfl⟩ := h.literal_inv
      exact ⟨by simp [Constant.toValue, Value.mapAddress], rfl⟩
  | ptr _ address => exact Empty.elim address
  | tuple values =>
      simp only [constantExpr] at h
      obtain ⟨results, items, rfl⟩ := h.tuple_inv
      obtain ⟨rfl, rfl⟩ := children values
        (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) items
      exact ⟨by simp [Constant.toValue, Value.mapAddress], rfl⟩
  | construct name ctor values =>
      simp only [constantExpr] at h
      cases h with
      | construct items =>
        obtain ⟨rfl, rfl⟩ := children values
          (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) items
        exact ⟨by simp [Constant.toValue, Value.mapAddress, instanceName, Instance.symbol], rfl⟩
termination_by sizeOf value
decreasing_by exact smaller _ (by simp)

/-- **A constant lookup that returned the literal `x`**, as a Boolean the kernel
evaluates. -/
def isLiteral (e : Except EvalError (Pattern F)) (x : F) : Bool :=
  match e with
  | .ok (.literal y) => decide (y = x)
  | _ => false

omit [Field F] in
theorem eq_of_isLiteral {e : Except EvalError (Pattern F)} {x : F} (h : isLiteral e x = true) :
    e = .ok (.literal x) := by
  unfold isLiteral at h
  split at h
  · simp only [decide_eq_true_eq] at h
    subst h
    rfl
  · cases h

/-! ## Calls in a checked source's world -/

/-- **A function call runs the body**, with its parameters bound to the
arguments, when the body has no control syntax. -/
theorem EvalFn.function_inv {s : Source F} {name : String} {fn : SourceFunction F}
    (hfn : s.program.sourceFunction? name = some fn) (free : ControlLower.hasControl fn.body = false)
    {args : List (SourceValue F)} (h : EvalFn s.world name args before result after) :
    EvalExpr s.world fn.types ((fn.params.map Prod.fst).zip args) fn.body before result after := by
  cases h with
  | intro prepared body =>
    obtain ⟨rfl, rfl, rfl⟩ := Source.world_prepare_of_sourceFunction hfn prepared
    exact body
  | returned prepared body =>
    obtain ⟨-, -, rfl⟩ := Source.world_prepare_of_sourceFunction hfn prepared
    exact (OpenSource.EvalExit.hasControl (OpenSource.exit_of_closed body) free).elim

/-- **A map call returns the map's row** for its arguments, and leaves the
heap. -/
theorem EvalFn.map_inv {s : Source F} {name : String} (hfn : s.program.sourceFunction? name = none)
    {args : List (SourceValue F)} {row : Constant F} (looked : lookupMap s.tables name args = .ok row)
    (h : EvalFn s.world name args before result after) : result = row.toValue ∧ after = before := by
  have prepared : ∀ {types locals expr}, s.world.prepare name args = .ok (types, locals, expr) →
      types = [] ∧ locals = [] ∧ expr = constantExpr row := by
    intro types locals expr prepared
    simp only [Source.world, sourceWorld, hfn, looked, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at prepared
    exact ⟨prepared.1.symm, prepared.2.1.symm, prepared.2.2.symm⟩
  cases h with
  | intro p body =>
    obtain ⟨rfl, rfl, rfl⟩ := prepared p
    exact constant_inv _ row body
  | returned p body =>
    obtain ⟨rfl, rfl, rfl⟩ := prepared p
    exact (OpenSource.EvalExit.hasControl (OpenSource.exit_of_closed body)
      (constantExpr_closed row).noControl).elim

/-! ## Patterns -/

omit [Field F] in
theorem matchPattern_bind (name : String) (value : SourceValue F) (heap : Heap F) :
    world.matchPattern types heap (.bind name) value = .ok (some [(name, value)]) := by
  simp [World.matchPattern, matchPatternWith, pure, Except.pure]

omit [Field F] in
theorem matchPattern_wildcard (value : SourceValue F) (heap : Heap F) :
    world.matchPattern types heap .wildcard value = .ok (some []) := by
  simp [World.matchPattern, matchPatternWith, pure, Except.pure]

omit [Field F] in
theorem matchPattern_literal (x y : F) (heap : Heap F) :
    world.matchPattern types heap (.literal x) (.field y) = .ok (if x = y then some [] else none) := by
  simp [World.matchPattern, matchPatternWith, Aiur.Pattern.bindings, pure, Except.pure]

omit [Field F] [DecidableEq F] in
theorem matchListWith_map {A B : Type}
    (g : A → SourceValue F → Except EvalError (Option (Environment F Nat))) (π : B → A) :
    ∀ (l : List B) (vs : List (SourceValue F)),
      matchListWith (fun b v => g (π b) v) l vs = matchListWith g (l.map π) vs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | b :: l, v :: vs => by simp only [matchListWith, List.map_cons, matchListWith_map g π l vs]

omit [Field F] in
theorem matchPattern_tuple (ps : List (Pattern F)) (vs : List (SourceValue F)) (heap : Heap F) :
    world.matchPattern types heap (.tuple ps) (.tuple vs) =
      if ps.length != vs.length then .ok none
      else matchListWith (world.matchPattern types heap) ps vs := by
  unfold World.matchPattern
  rw [matchPatternWith]
  simp only [bind, Except.bind, pure, Except.pure]
  split <;> rename_i h
  · rfl
  · rw [matchListWith_map (matchPatternWith world.constant world.constDepth types heap) Subtype.val,
      List.attach_map_subtype_val]

omit [Field F] in
theorem matchPattern_array (ps : List (Pattern F)) (vs : List (SourceValue F)) (heap : Heap F) :
    world.matchPattern types heap (.array ps) (.tuple vs) =
      if ps.length != vs.length then .ok none
      else matchListWith (world.matchPattern types heap) ps vs := by
  unfold World.matchPattern
  rw [matchPatternWith]
  simp only [bind, Except.bind, pure, Except.pure]
  split <;> rename_i h
  · rfl
  · rw [matchListWith_map (matchPatternWith world.constant world.constDepth types heap) Subtype.val,
      List.attach_map_subtype_val]

omit [Field F] in
theorem matchPattern_construct (t : Ty) (c : String) (ps : List (Pattern F)) (name ctor : String)
    (vs : List (SourceValue F)) (heap : Heap F) :
    world.matchPattern types heap (.construct t c ps) (.construct name ctor vs) =
      if (name != constructorName types t || ctor != c || ps.length != vs.length) = true then .ok none
      else matchListWith (world.matchPattern types heap) ps vs := by
  unfold World.matchPattern
  rw [matchPatternWith]
  simp only [bind, Except.bind, pure, Except.pure]
  split <;> rename_i h
  · rfl
  · rw [matchListWith_map (matchPatternWith world.constant world.constDepth types heap) Subtype.val,
      List.attach_map_subtype_val]

end Aiur.Generic.SourceSemantics
