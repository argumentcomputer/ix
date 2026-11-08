import Ix.IxVM.Refinement.Exec
import Aiur.Generic.LookupFacts
import Aiur.Generic.NativeCompleteness
import Aiur.Generic.Observe

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

theorem EvalExpr.store_inv {e : Expr F}
    (h : EvalExpr world types locals (.store e) before result after) :
    ∃ input middle, EvalExpr world types locals e before input middle ∧
      result = .ptr input.type middle.length ∧ after = middle ++ [input] := by
  cases h with | store value => exact ⟨_, _, value, rfl, rfl⟩

theorem EvalExpr.construct_inv {name : String} {args : Option (List Ty)} {ctor : String}
    {es : List (Expr F)}
    (h : EvalExpr world types locals (.construct name args ctor es) before result after) :
    ∃ values, EvalArgs world types locals es before values after ∧
      result = .construct (instanceName types name args) ctor values := by
  cases h with | construct items => exact ⟨_, items, rfl⟩

theorem ObsExpr.call_inv {name : String} {typeArgs : Option (List Ty)} {args : List (Expr F)}
    {calls : List (Call F)}
    (h : ObsExpr world types locals (.call name typeArgs args) before result after calls) :
    ∃ values middle calls₁ calls₂,
      ObsArgs world types locals args before values middle calls₁ ∧
      ObsFn world (instanceName types name typeArgs) values middle result after calls₂ ∧
      calls = calls₁ ++ ⟨instanceName types name typeArgs, values, middle⟩ :: calls₂ := by
  cases h with | call arguments callee => exact ⟨_, _, _, _, arguments, callee, rfl⟩

theorem ObsFn.function_inv {s : Source F} {name : String} {fn : SourceFunction F}
    (hfn : s.program.sourceFunction? name = some fn) (free : ControlLower.hasControl fn.body = false)
    {args : List (SourceValue F)} {calls : List (Call F)}
    (h : ObsFn s.world name args before result after calls) :
    ObsExpr s.world fn.types ((fn.params.map Prod.fst).zip args) fn.body before result after calls := by
  cases h with
  | intro prepared body =>
    obtain ⟨rfl, rfl, rfl⟩ := Source.world_prepare_of_sourceFunction hfn prepared
    exact body
  | returned prepared body =>
    obtain ⟨-, -, rfl⟩ := Source.world_prepare_of_sourceFunction hfn prepared
    exact (OpenSource.EvalExit.hasControl (OpenSource.exit_of_closed body.erase) free).elim

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

omit [Field F] [DecidableEq F] in
@[simp] theorem instanceName_plain_some (name : String) : instanceName [] name (some []) = name := by
  simp [instanceName, Instance.symbol]

omit [Field F] [DecidableEq F] in
@[simp] theorem instanceName_plain_none (name : String) : instanceName [] name none = name := by
  simp [instanceName, Instance.symbol]

/-! ## For generated mirrors

A generated mirror (`IxVM.Refinement.Mirrors`) is a Lean function with fuel
that runs one function's body on values and a heap. Its lemma `of_eval`
inverts a derivation node by node with the lemmas below and evaluates the
mirror on what it found. -/

theorem EvalExpr.index_inv {e : Expr F} {i : Nat}
    (h : EvalExpr world types locals (.index e i) before result after) :
    ∃ input, EvalExpr world types locals e before input after ∧ projectValue input i = .ok result := by
  cases h with | index value projected => exact ⟨_, value, projected⟩

theorem EvalExpr.builtin_inv {op : Builtin} {es : List (Expr F)}
    (h : EvalExpr world types locals (.builtin op es) before result after) :
    ∃ values, EvalArgs world types locals es before values after ∧ op.apply values = .ok result := by
  cases h with | builtin items applied => exact ⟨_, items, applied⟩

theorem EvalExpr.repeat_inv {e : Expr F} {n : Nat}
    (h : EvalExpr world types locals (.repeat e n) before result after) :
    ∃ input, EvalExpr world types locals e before input after ∧ result = .tuple (List.replicate n input) := by
  cases h with | «repeat» value => exact ⟨_, value, rfl⟩

theorem EvalExpr.global_literal_inv {name : String} {t : Ty} {x : F}
    (hc : world.constant name (t.subst types) = .ok (.literal x))
    (h : EvalExpr world types locals (.global name (some t)) before result after) :
    result = .field x ∧ after = before := by
  obtain ⟨pattern, body, lookup, interpreted, value⟩ := h.global_inv
  rw [hc] at lookup
  cases lookup
  simp only [Consts.toExpr, pure, Except.pure, Except.ok.injEq] at interpreted
  subst interpreted
  exact value.literal_inv

/-- **A map call, as a mirror reads it**: the map's row for the arguments. -/
def mapCall (tables : Aiur.Program F) (name : String) (args : List (SourceValue F))
    (heap : Heap F) : Option (SourceValue F × Heap F) :=
  match lookupMap tables name args with
  | .ok row => some (row.toValue, heap)
  | .error _ => none

/-- **A map call returns some row** of the map for its arguments. -/
theorem EvalFn.map_row {s : Source F} {name : String} (hfn : s.program.sourceFunction? name = none)
    {args : List (SourceValue F)} (h : EvalFn s.world name args before result after) :
    mapCall s.tables name args before = some (result, after) := by
  cases looked : lookupMap s.tables name args with
  | error e =>
    cases h with
    | intro p _ => simp [Source.world, sourceWorld, hfn, looked, bind, Except.bind] at p
    | returned p _ => simp [Source.world, sourceWorld, hfn, looked, bind, Except.bind] at p
  | ok row =>
    obtain ⟨rfl, rfl⟩ := EvalFn.map_inv hfn looked h
    simp [mapCall, looked]

omit [Field F] in
theorem matchPattern_literal_any (c : F) (v : SourceValue F) (heap : Heap F) :
    world.matchPattern types heap (.literal c) v = .ok (if v = .field c then some [] else none) := by
  cases v <;> simp [World.matchPattern, matchPatternWith, Aiur.Pattern.bindings, pure, Except.pure,
    eq_comm]

omit [Field F] in
theorem selectArm_literal_inv {c : F} {b body : Expr F} {arms : List (Pattern F × Expr F)}
    {v : SourceValue F} {heap : Heap F} {bs : Environment F Nat}
    (h : selectArm world types heap v ((.literal c, b) :: arms) = .ok (some (bs, body))) :
    (v = .field c ∧ bs = [] ∧ body = b) ∨
      (v ≠ .field c ∧ selectArm world types heap v arms = .ok (some (bs, body))) := by
  rw [selectArm, matchPattern_literal_any] at h
  by_cases hv : v = .field c
  · simp only [hv, ite_true, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
      Option.some.injEq, Prod.mk.injEq] at h
    exact .inl ⟨hv, h.1.symm, h.2.symm⟩
  · simp only [hv, ite_false, bind, Except.bind] at h
    exact .inr ⟨hv, h⟩

omit [Field F] in
theorem selectArm_wildcard_inv {b body : Expr F} {arms : List (Pattern F × Expr F)}
    {v : SourceValue F} {heap : Heap F} {bs : Environment F Nat}
    (h : selectArm world types heap v ((.wildcard, b) :: arms) = .ok (some (bs, body))) :
    bs = [] ∧ body = b := by
  simp only [selectArm, matchPattern_wildcard, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

omit [Field F] in
theorem matchPattern_tuple_inv {ps : List (Pattern F)} {v : SourceValue F} {heap : Heap F}
    {bs : Environment F Nat} (h : world.matchPattern types heap (.tuple ps) v = .ok (some bs)) :
    ∃ vs, v = .tuple vs ∧ ps.length = vs.length ∧
      matchListWith (world.matchPattern types heap) ps vs = .ok (some bs) := by
  cases v with
  | tuple vs =>
    rw [matchPattern_tuple] at h
    split at h
    · cases h
    · rename_i hl
      exact ⟨vs, rfl, by simpa using hl, h⟩
  | _ => simp [World.matchPattern, matchPatternWith, pure, Except.pure] at h

omit [Field F] in
theorem matchPattern_array_inv {ps : List (Pattern F)} {v : SourceValue F} {heap : Heap F}
    {bs : Environment F Nat} (h : world.matchPattern types heap (.array ps) v = .ok (some bs)) :
    ∃ vs, v = .tuple vs ∧ ps.length = vs.length ∧
      matchListWith (world.matchPattern types heap) ps vs = .ok (some bs) := by
  cases v with
  | tuple vs =>
    rw [matchPattern_array] at h
    split at h
    · cases h
    · rename_i hl
      exact ⟨vs, rfl, by simpa using hl, h⟩
  | _ => simp [World.matchPattern, matchPatternWith, pure, Except.pure] at h

omit [Field F] in
theorem matchPattern_construct_inv {t : Ty} {c : String} {ps : List (Pattern F)}
    {v : SourceValue F} {heap : Heap F} {bs : Environment F Nat}
    (h : world.matchPattern types heap (.construct t c ps) v = .ok (some bs)) :
    ∃ vs, v = .construct (constructorName types t) c vs ∧ ps.length = vs.length ∧
      matchListWith (world.matchPattern types heap) ps vs = .ok (some bs) := by
  cases v with
  | construct name ctor vs =>
    rw [matchPattern_construct] at h
    split at h
    · cases h
    · rename_i hl
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hl
      obtain ⟨⟨rfl, rfl⟩, hlen⟩ := hl
      exact ⟨vs, rfl, by simpa using hlen, h⟩
  | _ => simp [World.matchPattern, matchPatternWith, pure, Except.pure] at h

end Aiur.Generic.SourceSemantics
