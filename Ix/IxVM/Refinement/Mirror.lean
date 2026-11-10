import Ix.IxVM.Refinement.Exec
import Aiur.Generic.LookupFacts
import Aiur.Generic.NativeCompleteness
import Aiur.Generic.Observe
import Aiur.Generic.TypeFacts

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

theorem ObsExit.hasControl {target : ExitTarget} {calls : List (Call F)} {expr : Expr F}
    (ev : ObsExit world types locals expr before target result after calls) :
    ControlLower.hasControl expr = false → False := by
  induction ev using ObsExit.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ es _ _ _ _ _ _ =>
      (∀ e ∈ es, ControlLower.hasControl e = false) → False) with
  | exit | exitPayload | fromBlock => simp [ControlLower.hasControl]
  | fromGlobal _ interpreted _ ih =>
      intro _
      exact ih (Consts.toExpr_closed _ interpreted).noControl
  | fromBuiltin _ ih | fromUpdate _ ih | fromRecord _ ih | fromTuple _ ih | fromArray _ ih
    | fromConstruct _ ih | fromConstructAs _ ih | fromCall _ ih =>
      intro h
      apply ih
      simpa [ControlLower.hasControl, List.any_eq_false] using h
  | fromMember _ ih | fromRepeat _ ih | fromIndex _ ih | fromSlice _ ih | fromProject _ ih
    | fromStore _ ih | fromLoad _ ih | fromHint _ ih | fromNeg _ ih =>
      simpa only [ControlLower.hasControl] using ih
  | fromLetValue _ ih | binaryLeft _ ih | fromMatchValue _ ih =>
      intro h
      simp only [ControlLower.hasControl, Bool.or_eq_false_iff] at h
      exact ih h.1
  | letBody _ _ _ _ ih | binaryRight _ _ _ ih =>
      intro h
      simp only [ControlLower.hasControl, Bool.or_eq_false_iff] at h
      exact ih h.2
  | matchBody _ selected _ _ ih =>
      intro h
      obtain ⟨pat, member⟩ := selected_member selected
      simp only [ControlLower.hasControl, Bool.or_eq_false_iff,
        List.any_map, List.any_eq_false, Function.comp_def, id_eq] at h
      exact ih (by simpa using h.2 _ member)
  | head _ ih => rename_i h; exact ih (h _ (by simp))
  | tail _ _ _ ih => rename_i h; exact ih (fun e he => h e (by simp [he]))
  | _ => trivial

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
    exact (body.hasControl free).elim

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
@[simp] theorem instanceName_plain_some (types : Types) (name : String) :
    instanceName types name (some []) = name := by
  simp [instanceName, Instance.symbol]

omit [Field F] [DecidableEq F] in
@[simp] theorem instanceName_plain_none (types : Types) (name : String) :
    instanceName types name none = name := by
  simp [instanceName, Instance.symbol]

omit [Field F] [DecidableEq F] in
theorem instanceName_some_one (types : Types) (name : String) (t : Ty) :
    instanceName types name (some [t]) = (Instance.mk name [t.subst types]).symbol := rfl

omit [Field F] [DecidableEq F] in
@[simp] theorem subst_param_singleton (tp : String) (t : Ty) :
    (Ty.param tp).subst [(tp, t)] = t := by
  simp [Ty.subst, List.lookup]

omit [Field F] [DecidableEq F] in
theorem Program.sourceFunction?_of_mem_one {p : Program F} (hd : (p.functions.map (·.name)).Nodup)
    {f : Function F} (hf : f ∈ p.functions) {tp : String} (htypes : f.typeParams = [tp]) (t : Ty) :
    p.sourceFunction? (Instance.mk f.name [t]).symbol =
      some { types := [(tp, t)],
             params := f.params.map fun (n, pt) => (n, (pt.subst [(tp, t)]).toCore),
             body := f.body } := by
  have hsym : Instance.ofSymbol (Instance.mk f.name [t]).symbol = .ok ⟨f.name, [t]⟩ :=
    Instance.ofSymbol_symbol_of_ne_nil ⟨f.name, [t]⟩ (by simp)
  simp [Program.sourceFunction?, hsym, Except.toOption, Program.findFunction?_of_mem hd hf, htypes,
    arguments, pure, Except.pure, bind, Except.bind]

/-! ## For generated mirrors

A generated mirror (`IxVM.Refinement.Mirrors`) is a Lean function with fuel
that runs one function's body on values and a heap. Its lemma `of_eval`
inverts a derivation node by node with the lemmas below and evaluates the
mirror on what it found. -/

theorem EvalExpr.index_inv {e : Expr F} {i : Nat}
    (h : EvalExpr world types locals (.index e i) before result after) :
    ∃ input, EvalExpr world types locals e before input after ∧ projectValue input i = .ok result := by
  cases h with | index value projected => exact ⟨_, value, projected⟩

theorem EvalExpr.project_inv {e : Expr F} {i : Nat}
    (h : EvalExpr world types locals (.project e i) before result after) :
    ∃ input, EvalExpr world types locals e before input after ∧ projectValue input i = .ok result := by
  cases h with | project value projected => exact ⟨_, value, projected⟩

theorem EvalExpr.slice_inv {e : Expr F} {a : Nat} {b : Option Nat}
    (h : EvalExpr world types locals (.slice e a b) before result after) :
    ∃ input, EvalExpr world types locals e before input after ∧ sliceValue input a b = .ok result := by
  cases h with | slice value sliced => exact ⟨_, value, sliced⟩

theorem EvalExpr.member_inv {e : Expr F} {field : FieldRef}
    (h : EvalExpr world types locals (.member e field) before result after) :
    ∃ input, EvalExpr world types locals e before input after ∧
      memberValue types field input = .ok result := by
  cases h with | member value projected => exact ⟨_, value, projected⟩

theorem EvalExpr.neg_inv {e : Expr F}
    (h : EvalExpr world types locals (.neg e) before result after) :
    ∃ input, EvalExpr world types locals e before input after ∧ evalNeg input = .ok result := by
  cases h with | neg value negated => exact ⟨_, value, negated⟩

theorem EvalExpr.constructAs_inv {ps : List String} {t : Ty} {ctor : String} {es : List (Expr F)}
    (h : EvalExpr world types locals (.constructAs ps t ctor es) before result after) :
    ∃ values, EvalArgs world types locals es before values after ∧
      result = .construct (constructorName types t) ctor values := by
  cases h with | constructAs items => exact ⟨_, items, rfl⟩

theorem EvalExpr.record_inv {head : RecordHead} {es : List (Expr F)}
    (h : EvalExpr world types locals (.record head es) before result after) :
    ∃ values, EvalArgs world types locals es before values after ∧
      result = .construct (constructorName types head.type) structConstructor
        (head.order values (.tuple [])) := by
  cases h with | record items => exact ⟨_, items, rfl⟩

theorem EvalExpr.update_inv {paths : List UpdatePath} {es : List (Expr F)}
    (h : EvalExpr world types locals (.update paths es) before result after) :
    ∃ values, EvalArgs world types locals es before values after ∧
      Update.value types paths values = .ok result := by
  cases h with | update items updated => exact ⟨_, items, updated⟩

theorem EvalExpr.hint_inv {t : Ty} {key : Expr F} {channel : String}
    (h : EvalExpr world types locals (.hint t key channel) before result after) :
    ∃ input value, EvalExpr world types locals key before input after ∧
      world.typed (t.subst types).toCore value = true ∧ result = value.toValue := by
  cases h with | hint evaluated typed => exact ⟨_, _, evaluated, typed, rfl⟩

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

/-- **A pattern that denotes a constant value `u` with no bindings.** -/
def MatchesConst (world : World F) (types : Types) (p : Pattern F) (u : SourceValue F) : Prop :=
  ∀ (heap : Heap F) (v : SourceValue F),
    world.matchPattern types heap p v = .ok (if v = u then some [] else none)

/-- **A list of constant patterns denoting `us` elementwise.** -/
inductive MatchesConstList (world : World F) (types : Types) :
    List (Pattern F) → List (SourceValue F) → Prop where
  | nil : MatchesConstList world types [] []
  | cons {p : Pattern F} {u : SourceValue F} {ps : List (Pattern F)} {us : List (SourceValue F)} :
      MatchesConst world types p u → MatchesConstList world types ps us →
      MatchesConstList world types (p :: ps) (u :: us)

omit [Field F] in
theorem MatchesConst.literal (c : F) :
    MatchesConst world types (.literal c) (.field c) :=
  fun heap v => matchPattern_literal_any c v heap

omit [Field F] in
theorem MatchesConst.global {s : Source F} {name : String} {t : Ty} {c : F}
    (hc : s.world.constant name (t.subst types) = .ok (.literal c)) :
    MatchesConst s.world types (.global name (some t)) (.field c) := by
  intro heap v
  unfold World.matchPattern
  change matchPatternWith s.world.constant (s.program.consts.length + 1) types heap
    (.global name (some t)) v = _
  rw [matchPatternWith]
  simp only [hc, bind, Except.bind]
  rw [matchPatternWith]
  cases v <;> simp [Aiur.Pattern.bindings, pure, Except.pure, eq_comm]

omit [Field F] in
theorem MatchesConstList.length {ps : List (Pattern F)} {us : List (SourceValue F)}
    (h : MatchesConstList world types ps us) : ps.length = us.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

omit [Field F] in
theorem MatchesConstList.matchListWith {ps : List (Pattern F)} {us : List (SourceValue F)}
    (h : MatchesConstList world types ps us) (heap : Heap F) :
    ∀ vs : List (SourceValue F),
      SourceSemantics.matchListWith (world.matchPattern types heap) ps vs =
        .ok (if vs = us then some [] else none) := by
  induction h with
  | nil =>
    intro vs
    cases vs <;> rfl
  | @cons p u ps us hp _ ih =>
    intro vs
    cases vs with
    | nil => rfl
    | cons v vs =>
      simp only [SourceSemantics.matchListWith, hp heap v, ih vs,
        bind, Except.bind, pure, Except.pure, List.cons.injEq]
      by_cases hv : v = u
      · by_cases hvs : vs = us <;> simp [hv, hvs]
      · simp [hv]

omit [Field F] in
theorem MatchesConst.tuple {ps : List (Pattern F)} {us : List (SourceValue F)}
    (h : MatchesConstList world types ps us) :
    MatchesConst world types (.tuple ps) (.tuple us) := by
  intro heap v
  cases v with
  | tuple vs =>
    rw [matchPattern_tuple, h.matchListWith heap vs]
    by_cases hlen : (ps.length != vs.length) = true
    · have hne : vs ≠ us := by
        intro heq; subst heq; exact absurd h.length (by simpa using hlen)
      simp [hlen, hne]
    · simp [hlen]
  | _ => simp [World.matchPattern, matchPatternWith, pure, Except.pure]

omit [Field F] in
theorem MatchesConst.array {ps : List (Pattern F)} {us : List (SourceValue F)}
    (h : MatchesConstList world types ps us) :
    MatchesConst world types (.array ps) (.tuple us) := by
  intro heap v
  cases v with
  | tuple vs =>
    rw [matchPattern_array, h.matchListWith heap vs]
    by_cases hlen : (ps.length != vs.length) = true
    · have hne : vs ≠ us := by
        intro heq; subst heq; exact absurd h.length (by simpa using hlen)
      simp [hlen, hne]
    · simp [hlen]
  | _ => simp [World.matchPattern, matchPatternWith, pure, Except.pure]

omit [Field F] in
theorem selectArm_const_inv {p : Pattern F} {u : SourceValue F} {b body : Expr F}
    {arms : List (Pattern F × Expr F)} {v : SourceValue F} {heap : Heap F}
    {bs : Environment F Nat}
    (h : selectArm world types heap v ((p, b) :: arms) = .ok (some (bs, body)))
    (hp : MatchesConst world types p u) :
    (v = u ∧ bs = [] ∧ body = b) ∨
      (v ≠ u ∧ selectArm world types heap v arms = .ok (some (bs, body))) := by
  rw [selectArm, hp heap v] at h
  by_cases hv : v = u
  · simp only [hv, ite_true, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
      Option.some.injEq, Prod.mk.injEq] at h
    exact .inl ⟨hv, h.1.symm, h.2.symm⟩
  · simp only [hv, ite_false, bind, Except.bind] at h
    exact .inr ⟨hv, h⟩

/-- **A flat pattern** (`.bind` or `.wildcard`) always succeeds on every value. -/
def IsFlatPattern : Pattern F → Prop
  | .bind _ => True
  | .wildcard => True
  | _ => False

/-- **A list of flat patterns.** -/
def IsFlatPatternList : List (Pattern F) → Prop
  | [] => True
  | p :: ps => IsFlatPattern p ∧ IsFlatPatternList ps

omit [Field F] in
theorem IsFlatPattern.matchPattern {p : Pattern F} (hp : IsFlatPattern p)
    (v : SourceValue F) (heap : Heap F) :
    ∃ bs, world.matchPattern types heap p v = .ok (some bs) := by
  cases p <;> try contradiction
  · exact ⟨_, matchPattern_wildcard v heap⟩
  · exact ⟨_, matchPattern_bind _ v heap⟩

omit [Field F] in
theorem IsFlatPatternList.matchListWith :
    ∀ {ps : List (Pattern F)} {vs : List (SourceValue F)},
      IsFlatPatternList ps → ps.length = vs.length →
      ∀ (heap : Heap F), ∃ bs,
        SourceSemantics.matchListWith (world.matchPattern types heap) ps vs = .ok (some bs)
  | [], [], _, _, _ => ⟨[], rfl⟩
  | _ :: _, v :: _, ⟨hp, hps⟩, hlen, heap => by
      obtain ⟨bs1, h1⟩ := hp.matchPattern (world := world) (types := types) v heap
      obtain ⟨bs2, h2⟩ := hps.matchListWith (Nat.succ.inj hlen) heap
      refine ⟨bs1 ++ bs2, ?_⟩
      simp [SourceSemantics.matchListWith, h1, h2, bind, Except.bind, pure, Except.pure]

/-- **Branch on a constructor with `n` fields** (`matchValue` on `.construct`). -/
def matchConstruct {α : Type} (name ctor : String) :
    Nat → SourceValue F → (List (SourceValue F) → α) → α → α
  | n, .construct name' ctor' vs, onMatch, onMiss =>
      if name' = name ∧ ctor' = ctor ∧ vs.length = n then onMatch vs else onMiss
  | _, _, _, onMiss => onMiss

omit [Field F] [DecidableEq F] in
@[simp] theorem matchConstruct_construct {α : Type} (name ctor : String) (n : Nat)
    (name' ctor' : String) (vs : List (SourceValue F))
    (onMatch : List (SourceValue F) → α) (onMiss : α) :
    matchConstruct name ctor n (.construct name' ctor' vs) onMatch onMiss =
      if name' = name ∧ ctor' = ctor ∧ vs.length = n then onMatch vs else onMiss := rfl

omit [Field F] in
theorem selectArm_construct_inv {t : Ty} {c : String} {ps : List (Pattern F)}
    {b body : Expr F} {arms : List (Pattern F × Expr F)}
    {v : SourceValue F} {heap : Heap F} {bs : Environment F Nat}
    (hflat : IsFlatPatternList ps)
    (h : selectArm world types heap v ((.construct t c ps, b) :: arms) = .ok (some (bs, body))) :
    (∃ vs, v = .construct (constructorName types t) c vs ∧ ps.length = vs.length ∧
      matchListWith (world.matchPattern types heap) ps vs = .ok (some bs) ∧ body = b) ∨
    ((∀ {α : Type} (onMatch : List (SourceValue F) → α) (onMiss : α),
        matchConstruct (constructorName types t) c ps.length v onMatch onMiss = onMiss) ∧
      selectArm world types heap v arms = .ok (some (bs, body))) := by
  rw [selectArm] at h
  cases hm : world.matchPattern types heap (.construct t c ps) v with
  | error e => simp [hm, bind, Except.bind] at h
  | ok opt =>
    cases opt with
    | some bindings =>
      simp only [hm, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨vs, hv, hlen, hml⟩ := matchPattern_construct_inv hm
      exact .inl ⟨vs, hv, hlen, hml, rfl⟩
    | none =>
      simp only [hm, bind, Except.bind] at h
      refine .inr ⟨fun {α} onMatch onMiss => ?_, h⟩
      cases v with
      | construct name' ctor' vs =>
        unfold matchConstruct
        by_cases hc : name' = constructorName types t ∧ ctor' = c ∧ vs.length = ps.length
        · obtain ⟨hname, hctor, hlen⟩ := hc
          rw [matchPattern_construct] at hm
          simp only [hname, hctor, hlen, bne_self_eq_false, Bool.false_or] at hm
          obtain ⟨bs', hbs'⟩ := hflat.matchListWith (world := world) (types := types) hlen.symm heap
          rw [hbs'] at hm
          cases hm
        · simp [hc]
      | _ => rfl

omit [Field F] in
theorem selectArm_bind_inv {n : String} {b body : Expr F} {arms : List (Pattern F × Expr F)}
    {v : SourceValue F} {heap : Heap F} {bs : Environment F Nat}
    (h : selectArm world types heap v ((.bind n, b) :: arms) = .ok (some (bs, body))) :
    bs = [(n, v)] ∧ body = b := by
  simp only [selectArm, matchPattern_bind, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- **Branch on a tuple with `n` fields** (`matchValue` on `.tuple`). -/
def matchTuple {α : Type} :
    Nat → SourceValue F → (List (SourceValue F) → α) → α → α
  | n, .tuple vs, onMatch, onMiss =>
      if vs.length = n then onMatch vs else onMiss
  | _, _, _, onMiss => onMiss

omit [Field F] [DecidableEq F] in
@[simp] theorem matchTuple_tuple {α : Type} (n : Nat) (vs : List (SourceValue F))
    (onMatch : List (SourceValue F) → α) (onMiss : α) :
    matchTuple n (.tuple vs) onMatch onMiss =
      if vs.length = n then onMatch vs else onMiss := rfl

omit [Field F] in
theorem selectArm_tuple_inv {ps : List (Pattern F)}
    {b body : Expr F} {arms : List (Pattern F × Expr F)}
    {v : SourceValue F} {heap : Heap F} {bs : Environment F Nat}
    (hflat : IsFlatPatternList ps)
    (h : selectArm world types heap v ((.tuple ps, b) :: arms) = .ok (some (bs, body))) :
    (∃ vs, v = .tuple vs ∧ ps.length = vs.length ∧
      matchListWith (world.matchPattern types heap) ps vs = .ok (some bs) ∧ body = b) ∨
    ((∀ {α : Type} (onMatch : List (SourceValue F) → α) (onMiss : α),
        matchTuple ps.length v onMatch onMiss = onMiss) ∧
      selectArm world types heap v arms = .ok (some (bs, body))) := by
  rw [selectArm] at h
  cases hm : world.matchPattern types heap (.tuple ps) v with
  | error e => simp [hm, bind, Except.bind] at h
  | ok opt =>
    cases opt with
    | some bindings =>
      simp only [hm, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨vs, hv, hlen, hml⟩ := matchPattern_tuple_inv hm
      exact .inl ⟨vs, hv, hlen, hml, rfl⟩
    | none =>
      simp only [hm, bind, Except.bind] at h
      refine .inr ⟨fun {α} onMatch onMiss => ?_, h⟩
      cases v with
      | tuple vs =>
        unfold matchTuple
        by_cases hc : vs.length = ps.length
        · rw [matchPattern_tuple] at hm
          simp only [hc, bne_self_eq_false] at hm
          obtain ⟨bs', hbs'⟩ := hflat.matchListWith (world := world) (types := types) hc.symm heap
          rw [hbs'] at hm
          cases hm
        · simp [hc]
      | _ => rfl

/-- **Branch on a literal-headed tuple** `.tuple (.literal c :: ps)` (`matchValue`). -/
def matchLitTuple {α : Type} (c : F) :
    Nat → SourceValue F → (List (SourceValue F) → α) → α → α
  | n, .tuple (v0 :: vs), onMatch, onMiss =>
      if v0 = .field c ∧ vs.length = n then onMatch vs else onMiss
  | _, _, _, onMiss => onMiss

omit [Field F] in
@[simp] theorem matchLitTuple_tuple_field {α : Type} (c : F) (n : Nat)
    (vs : List (SourceValue F)) (onMatch : List (SourceValue F) → α) (onMiss : α) :
    matchLitTuple c n (.tuple (.field c :: vs)) onMatch onMiss =
      if vs.length = n then onMatch vs else onMiss := by
  simp [matchLitTuple]

omit [Field F] [DecidableEq F] in
@[congr] theorem matchConstruct_congr {α : Type} (name ctor : String) (n : Nat)
    {v v' : SourceValue F} (onMatch : List (SourceValue F) → α) (onMiss : α)
    (hv : v = v') :
    matchConstruct name ctor n v onMatch onMiss =
      matchConstruct name ctor n v' onMatch onMiss := by
  rw [hv]

omit [Field F] [DecidableEq F] in
@[congr] theorem matchTuple_congr {α : Type} (n : Nat)
    {v v' : SourceValue F} (onMatch : List (SourceValue F) → α) (onMiss : α)
    (hv : v = v') :
    matchTuple n v onMatch onMiss = matchTuple n v' onMatch onMiss := by
  rw [hv]

omit [Field F] in
@[congr] theorem matchLitTuple_congr {α : Type} (c : F) (n : Nat)
    {v v' : SourceValue F} (onMatch : List (SourceValue F) → α) (onMiss : α)
    (hv : v = v') :
    matchLitTuple c n v onMatch onMiss = matchLitTuple c n v' onMatch onMiss := by
  rw [hv]

/-- **Bind an `Except` result into `Option`**, with short-circuiting `@[congr]`. -/
def bindOk {ε α : Type} (x : Except ε (SourceValue F)) (f : SourceValue F → Option α) : Option α :=
  match x with
  | .ok v => f v
  | .error _ => none

omit [Field F] [DecidableEq F] in
@[simp] theorem bindOk_ok {ε α : Type} (v : SourceValue F) (f : SourceValue F → Option α) :
    bindOk (.ok v : Except ε (SourceValue F)) f = f v := rfl

omit [Field F] [DecidableEq F] in
@[simp] theorem bindOk_error {ε α : Type} (e : ε) (f : SourceValue F → Option α) :
    bindOk (.error e : Except ε (SourceValue F)) f = none := rfl

omit [Field F] [DecidableEq F] in
@[congr] theorem bindOk_congr {ε α : Type} {x x' : Except ε (SourceValue F)}
    (f : SourceValue F → Option α) (hx : x = x') :
    bindOk x f = bindOk x' f := by
  rw [hx]

/-- **Unpack a `cons` cell in `onMatch`**, with short-circuiting `@[congr]`. -/
def bindCons {α : Type} (vs : List (SourceValue F))
    (f : SourceValue F → List (SourceValue F) → Option α) : Option α :=
  match vs with
  | v :: vs' => f v vs'
  | [] => none

omit [Field F] [DecidableEq F] in
@[simp] theorem bindCons_cons {α : Type} (v : SourceValue F) (vs : List (SourceValue F))
    (f : SourceValue F → List (SourceValue F) → Option α) :
    bindCons (v :: vs) f = f v vs := rfl

omit [Field F] [DecidableEq F] in
@[simp] theorem bindCons_nil {α : Type} (f : SourceValue F → List (SourceValue F) → Option α) :
    bindCons ([] : List (SourceValue F)) f = none := rfl

omit [Field F] [DecidableEq F] in
@[congr] theorem bindCons_congr {α : Type} {vs vs' : List (SourceValue F)}
    (f : SourceValue F → List (SourceValue F) → Option α) (hvs : vs = vs') :
    bindCons vs f = bindCons vs' f := by
  rw [hvs]

/-- **Read `n` elements from a heap-allocated `Lists::Node<field>` list.** -/
def readStreamBytes : Nat → Heap F → SourceValue F → Option (List (SourceValue F) × SourceValue F)
  | 0, _, s => some ([], s)
  | n + 1, h, s =>
    bindOk (loadValue h s) fun v =>
      matchConstruct (constructorName [] (.named "Lists::Node" [.field])) "Cons" 2 v
        (fun vs => bindCons vs fun b vs => bindCons vs fun s' _ =>
          (readStreamBytes n h s').map fun p => (b :: p.1, p.2))
        none

omit [Field F] [DecidableEq F] in
@[simp] theorem readStreamBytes_zero (h : Heap F) (s : SourceValue F) :
    readStreamBytes 0 h s = some ([], s) := rfl

omit [Field F] [DecidableEq F] in
@[simp] theorem readStreamBytes_succ (n : Nat) (h : Heap F) (s : SourceValue F) :
    readStreamBytes (n + 1) h s =
      bindOk (loadValue h s) fun v =>
        matchConstruct (constructorName [] (.named "Lists::Node" [.field])) "Cons" 2 v
          (fun vs => bindCons vs fun b vs => bindCons vs fun s' _ =>
            (readStreamBytes n h s').map fun p => (b :: p.1, p.2))
          none := rfl

omit [Field F] in
theorem selectArm_litTuple_inv {c : F} {ps : List (Pattern F)}
    {b body : Expr F} {arms : List (Pattern F × Expr F)}
    {v : SourceValue F} {heap : Heap F} {bs : Environment F Nat}
    (hflat : IsFlatPatternList ps)
    (h : selectArm world types heap v ((.tuple (.literal c :: ps), b) :: arms) = .ok (some (bs, body))) :
    (∃ vs, v = .tuple (.field c :: vs) ∧ ps.length = vs.length ∧
      matchListWith (world.matchPattern types heap) ps vs = .ok (some bs) ∧ body = b) ∨
    ((∀ {α : Type} (onMatch : List (SourceValue F) → α) (onMiss : α),
        matchLitTuple c ps.length v onMatch onMiss = onMiss) ∧
      selectArm world types heap v arms = .ok (some (bs, body))) := by
  rw [selectArm] at h
  cases hm : world.matchPattern types heap (.tuple (.literal c :: ps)) v with
  | error e => simp [hm, bind, Except.bind] at h
  | ok opt =>
    cases opt with
    | some bindings =>
      simp only [hm, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨vs0, rfl, hlen0, hml0⟩ := matchPattern_tuple_inv hm
      cases vs0 with
      | nil => simp at hlen0
      | cons v0 vs =>
        simp only [List.length_cons, Nat.succ.injEq] at hlen0
        simp only [matchListWith, matchPattern_literal_any, bind, Except.bind] at hml0
        by_cases hv0 : v0 = .field c
        · subst hv0
          simp only [↓reduceIte] at hml0
          cases hml : matchListWith (world.matchPattern types heap) ps vs with
          | error e => simp [hml] at hml0
          | ok opt' =>
            cases opt' with
            | none => simp [hml] at hml0
            | some bs' =>
              simp only [hml, pure, Except.pure, List.nil_append, Except.ok.injEq,
                Option.some.injEq] at hml0
              subst hml0
              exact .inl ⟨vs, rfl, hlen0, hml, rfl⟩
        · simp [hv0, pure, Except.pure] at hml0
    | none =>
      simp only [hm, bind, Except.bind] at h
      refine .inr ⟨fun {α} onMatch onMiss => ?_, h⟩
      cases v with
      | tuple vs0 =>
        cases vs0 with
        | nil => rfl
        | cons v0 vs =>
          unfold matchLitTuple
          by_cases hc : v0 = .field c ∧ vs.length = ps.length
          · obtain ⟨rfl, hlen⟩ := hc
            rw [matchPattern_tuple] at hm
            simp only [List.length_cons, hlen, bne_self_eq_false,
              matchListWith, matchPattern_literal_any, bind, Except.bind] at hm
            obtain ⟨bs', hbs'⟩ := hflat.matchListWith (world := world) (types := types) hlen.symm heap
            rw [hbs'] at hm
            simp [pure, Except.pure] at hm
          · simp [hc]
      | _ => rfl

end Aiur.Generic.SourceSemantics
