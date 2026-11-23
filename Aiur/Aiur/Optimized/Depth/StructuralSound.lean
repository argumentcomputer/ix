import Aiur.Optimized.Depth.Structural
import Aiur.Semantics.WithCalls
import Aiur.Semantics.Guard
import Mathlib.Logic.Relation

/-!
# The static relations hold of every call an evaluation makes

`Structural.scan` relates the arguments of each call of a function body to the function's
parameters. `scan_sound` shows the relations hold in every evaluation of the body, whatever the
relation `calls` that answers its calls: the evaluation is also an evaluation over `calls`
restricted to the calls `scan` lists, with arguments that satisfy their relations
(`Restrict`). No finiteness of the call graph is used; the body evaluation is finite.

This is the source half of the soundness argument for exempt SCCs. `guard` packages it as the
`CallGuard` the compiler's soundness proof consults; circuits and memo graphs enter in
`Optimized.StructuralModel` and `Depth.StructuralEndToEnd`.
-/

namespace Aiur.Optimized.Depth.Structural

variable {F : Type} [Field F] [DecidableEq F] {rom : ROM F} {params : List (Value F)}

/-! ## Parts of values -/

/-- `Component rom part whole`: `part` is an item of the tuple or constructor `whole`, or what
the pointer `whole` holds in `rom`. -/
inductive Component (rom : ROM F) : Value F → Value F → Prop where
  | tuple {value : Value F} {values : List (Value F)} (member : value ∈ values) :
      Component rom value (.tuple values)
  | construct {value : Value F} {values : List (Value F)} {name ctor : String}
      (member : value ∈ values) : Component rom value (.construct name ctor values)
  | load {value : Value F} {target : Ty} {address : F} (cell : (address, value) ∈ rom.entries)
      (typed : value.type = target) : Component rom value (.ptr target address)

/-- A proper part: reached by at least one `Component` step. -/
def Part (rom : ROM F) : Value F → Value F → Prop := _root_.Relation.TransGen (Component rom)

/-- What a static relation says of a value. -/
def Holds (rom : ROM F) (params : List (Value F)) (value : Value F) (fact : Nat × Relation) : Prop :=
  match fact.2 with
  | .same => params[fact.1]? = some value
  | .part => ∃ param, params[fact.1]? = some param ∧ Part rom value param
  | .down => ∃ (x : F) (n : Nat), 0 < n ∧ n ≤ maxStep ∧ value = .field x ∧
      params[fact.1]? = some (.field (x + (n : F)))
  | .up => ∃ (x : F) (n : Nat), 0 < n ∧ n ≤ maxStep ∧ value = .field (x + (n : F)) ∧
      params[fact.1]? = some (.field x)

/-- Every static relation of `parts` holds of `value`. -/
def Sound (rom : ROM F) (params : List (Value F)) (parts : Parts) (value : Value F) : Prop :=
  ∀ fact ∈ parts, Holds rom params value fact

theorem Sound.nil {value : Value F} : Sound rom params [] value := by
  intro fact member; cases member

theorem Sound.proper {parts : Parts} {value component : Value F}
    (sound : Sound rom params parts value) (step : Component rom component value) :
    Sound rom params parts.proper component := by
  intro fact member
  simp only [Parts.proper, List.mem_filterMap] at member
  obtain ⟨⟨i, relation⟩, inside, kept⟩ := member
  have holds := sound _ inside
  cases relation with
  | same =>
      simp only [true_or, if_true, Option.some.injEq] at kept
      subst kept
      exact ⟨value, holds, .single step⟩
  | part =>
      simp only [or_true, if_true, Option.some.injEq] at kept
      subst kept
      obtain ⟨param, found, inner⟩ := holds
      exact ⟨param, found, .head step inner⟩
  | down | up => simp at kept

theorem isStep_spec {constant : F} (step : isStep constant = true) :
    ∃ n : Nat, 0 < n ∧ n ≤ maxStep ∧ constant = (n : F) := by
  simp only [isStep, List.any_eq_true, List.mem_range, beq_iff_eq] at step
  obtain ⟨n, bound, same⟩ := step
  exact ⟨n + 1, by omega, by omega, same⟩

theorem Sound.down {parts : Parts} {left result : Value F} {constant : F}
    (sound : Sound rom params parts left)
    (operation : evalBinOp .sub left (.field constant) = .ok result) :
    Sound rom params (parts.step .down constant) result := by
  intro fact member
  unfold Parts.step at member
  split at member
  · rename_i step
    obtain ⟨n, positive, small, rfl⟩ := isStep_spec step
    simp only [List.mem_filterMap] at member
    obtain ⟨⟨i, relation⟩, inside, kept⟩ := member
    have holds := sound _ inside
    cases relation with
    | same =>
        simp only [if_true, Option.some.injEq] at kept
        subst kept
        cases left with
        | field x =>
            simp only [evalBinOp, Except.ok.injEq] at operation
            subst operation
            refine ⟨x - (n : F), n, positive, small, rfl, ?_⟩
            have : x - (n : F) + (n : F) = x := by ring
            rw [this]
            exact holds
        | tuple | ptr | construct => simp [evalBinOp] at operation
    | part | down | up => simp at kept
  · cases member

theorem Sound.up {parts : Parts} {left result : Value F} {constant : F}
    (sound : Sound rom params parts left)
    (operation : evalBinOp .add left (.field constant) = .ok result) :
    Sound rom params (parts.step .up constant) result := by
  intro fact member
  unfold Parts.step at member
  split at member
  · rename_i step
    obtain ⟨n, positive, small, rfl⟩ := isStep_spec step
    simp only [List.mem_filterMap] at member
    obtain ⟨⟨i, relation⟩, inside, kept⟩ := member
    have holds := sound _ inside
    cases relation with
    | same =>
        simp only [if_true, Option.some.injEq] at kept
        subst kept
        cases left with
        | field x =>
            simp only [evalBinOp, Except.ok.injEq] at operation
            subst operation
            exact ⟨x, n, positive, small, rfl, holds⟩
        | tuple | ptr | construct => simp [evalBinOp] at operation
    | part | down | up => simp at kept
  · cases member

theorem mem_meet {fact : Nat × Relation} :
    ∀ {lists : List Parts}, fact ∈ meet lists → ∀ parts ∈ lists, fact ∈ parts := by
  have fold : ∀ (rest : List Parts) (first : Parts),
      fact ∈ rest.foldl (fun common parts => common.filter parts.contains) first →
      fact ∈ first ∧ ∀ parts ∈ rest, fact ∈ parts := by
    intro rest
    induction rest with
    | nil => intro first member; exact ⟨member, by simp⟩
    | cons head tail ih =>
        intro first member
        obtain ⟨inside, others⟩ := ih _ member
        simp only [List.mem_filter, List.contains_iff_mem] at inside
        refine ⟨inside.1, ?_⟩
        intro parts present
        rcases List.mem_cons.mp present with rfl | present
        · exact inside.2
        · exact others parts present
  intro lists member parts present
  cases lists with
  | nil => cases present
  | cons first rest =>
      obtain ⟨inside, others⟩ := fold rest first member
      rcases List.mem_cons.mp present with rfl | present
      · exact inside
      · exact others parts present

/-! ## Patterns -/

/-- Static and dynamic bindings of one pattern: the same names in the same order, with
relations that hold. -/
def Aligned (rom : ROM F) (params : List (Value F)) :
    List (String × Parts) → Environment F → Prop :=
  List.Forall₂ fun static binding => static.1 = binding.1 ∧ Sound rom params static.2 binding.2

mutual
  theorem bind_aligned : ∀ (pattern : Pattern F) (parts : Parts) (value : Value F)
      (bindings : Environment F), Sound rom params parts value →
      pattern.bindings value = some bindings → Aligned rom params (bind pattern parts) bindings
    | .literal x, parts, value, bindings, _, matched => by
        cases value <;> simp [Pattern.bindings] at matched
        obtain ⟨_, rfl⟩ := matched
        simp [bind, Aligned]
    | .wildcard, parts, value, bindings, _, matched => by
        simp only [Pattern.bindings, Option.some.injEq] at matched
        subst matched
        simp [bind, Aligned]
    | .bind name, parts, value, bindings, sound, matched => by
        simp only [Pattern.bindings, Option.some.injEq] at matched
        subst matched
        simp only [bind, Aligned]
        exact .cons ⟨rfl, sound⟩ .nil
    | .tuple items, parts, value, bindings, sound, matched => by
        cases value with
        | tuple values =>
            simp only [Pattern.bindings] at matched
            simp only [bind]
            exact bindList_aligned items parts.proper values bindings
              (fun item member => sound.proper (.tuple member)) matched
        | field | ptr | construct => simp [Pattern.bindings] at matched
    | .construct name ctor items, parts, value, bindings, sound, matched => by
        cases value with
        | construct other ctor' values =>
            simp only [Pattern.bindings] at matched
            split at matched
            · simp only [bind]
              exact bindList_aligned items parts.proper values bindings
                (fun item member => sound.proper (.construct member)) matched
            · cases matched
        | field | ptr | tuple => simp [Pattern.bindings] at matched

  theorem bindList_aligned : ∀ (patterns : List (Pattern F)) (parts : Parts)
      (values : List (Value F)) (bindings : Environment F),
      (∀ value ∈ values, Sound rom params parts value) →
      Pattern.bindingsList patterns values = some bindings →
      Aligned rom params (patterns.map fun item => bind item parts).flatten bindings
    | [], parts, values, bindings, _, matched => by
        cases values <;> simp [Pattern.bindingsList] at matched
        subst matched
        simp [Aligned]
    | pattern :: patterns, parts, values, bindings, sound, matched => by
        cases values with
        | nil => simp [Pattern.bindingsList] at matched
        | cons value values =>
            simp only [Pattern.bindingsList, bind, Option.bind_eq_bind, Option.pure_def,
              Option.bind_eq_some_iff, Option.some.injEq] at matched
            obtain ⟨first, firstMatched, rest, restMatched, rfl⟩ := matched
            simp only [List.map_cons, List.flatten_cons]
            exact List.rel_append
              (bind_aligned pattern parts value first (sound value List.mem_cons_self) firstMatched)
              (bindList_aligned patterns parts values rest
                (fun item member => sound item (List.mem_cons_of_mem _ member)) restMatched)
end

/-- The static environment describes the dynamic one: a variable's relations hold of the
value it is bound to. -/
def EnvOK (rom : ROM F) (params : List (Value F)) (env : List (String × Parts))
    (locals : Environment F) : Prop :=
  ∀ name value, locals.find? (·.1 == name) = some (name, value) →
    Sound rom params ((env.lookup name).getD []) value

theorem EnvOK.append {static env : List (String × Parts)} {bindings locals : Environment F}
    (aligned : Aligned rom params static bindings) (ok : EnvOK rom params env locals) :
    EnvOK rom params (static ++ env) (bindings ++ locals) := by
  induction aligned with
  | nil => exact ok
  | @cons first binding static bindings head _ ih =>
      intro name value found
      obtain ⟨key, parts⟩ := first
      obtain ⟨boundName, bound⟩ := binding
      obtain ⟨sameName, sound⟩ := head
      simp only at sameName sound
      subst sameName
      simp only [List.cons_append, List.find?_cons] at found
      by_cases here : key = name
      · subst here
        simp only [beq_self_eq_true, Option.some.injEq, Prod.mk.injEq, true_and] at found
        subst found
        simpa [List.lookup] using sound
      · have differs : (key == name) = false := by simpa using here
        simp only [differs] at found
        have other : (name == key) = false := by simpa using fun same => here same.symm
        simpa [List.lookup, other] using ih name value found

theorem selectArm_some {input : Value F} :
    ∀ {arms : List (Pattern F × Expr F)} {bindings : Environment F} {body : Expr F},
      selectArm input arms = some (bindings, body) →
      ∃ arm ∈ arms, arm.1.bindings input = some bindings ∧ arm.2 = body
  | [], _, _, selected => by simp [selectArm] at selected
  | (pattern, expr) :: rest, bindings, body, selected => by
      unfold selectArm at selected
      split at selected
      · rename_i found matched
        simp only [Option.some.injEq, Prod.mk.injEq] at selected
        obtain ⟨rfl, rfl⟩ := selected
        exact ⟨(pattern, expr), List.mem_cons_self, matched, rfl⟩
      · obtain ⟨arm, member, matched⟩ := selectArm_some selected
        exact ⟨arm, List.mem_cons_of_mem _ member, matched⟩

/-! ## Evaluation -/

/-- `calls`, restricted to the listed call sites with arguments that satisfy their static
relations. -/
def Restrict (rom : ROM F) (params : List (Value F)) (sites : List Call) (calls : CallRelation F) :
    CallRelation F :=
  fun name args result => calls name args result ∧
    ∃ site ∈ sites, site.callee = name ∧ List.Forall₂ (Sound rom params) site.args args

/-- The static relations of `scan` hold in every evaluation: of the result, and of the
arguments of every call made. -/
theorem scan_sound {decls : Declarations} {calls : CallRelation F} {locals : Environment F}
    {expr : Expr F} {result : Value F}
    (evaluated : ROMEvalExprWith decls rom calls locals expr result) :
    ∀ env, EnvOK rom params env locals →
      Sound rom params (scan env expr).1 result ∧
      ∀ sites, (∀ site ∈ (scan env expr).2, site ∈ sites) →
        ROMEvalExprWith decls rom (Restrict rom params sites calls) locals expr result := by
  induction evaluated using ROMEvalExprWith.rec
    (motive_2 := fun locals exprs values _ => ∀ env, EnvOK rom params env locals →
      List.Forall₂ (Sound rom params) ((exprs.map (scan env)).map (·.1)) values ∧
      ∀ sites, (∀ site ∈ ((exprs.map (scan env)).map (·.2)).flatten, site ∈ sites) →
        ROMEvalArgsWith decls rom (Restrict rom params sites calls) locals exprs values) with
  | literal =>
      intro env _
      exact ⟨by simp only [scan]; exact .nil, fun _ _ => .literal⟩
  | var lookup =>
      intro env ok
      exact ⟨by simpa only [scan] using ok _ _ lookup, fun _ _ => .var lookup⟩
  | tuple _ ih =>
      intro env ok
      obtain ⟨_, run⟩ := ih env ok
      exact ⟨by simp only [scan]; exact .nil,
        fun sites inside => .tuple (run sites (by simpa only [scan] using inside))⟩
  | construct _ ih =>
      intro env ok
      obtain ⟨_, run⟩ := ih env ok
      exact ⟨by simp only [scan]; exact .nil,
        fun sites inside => .construct (run sites (by simpa only [scan] using inside))⟩
  | @project _ _ input index _ _ projected ih =>
      intro env ok
      obtain ⟨sound, run⟩ := ih env ok
      refine ⟨?_, fun sites inside => .project (run sites (by simpa only [scan] using inside)) projected⟩
      simp only [scan]
      apply sound.proper
      cases input with
      | tuple items =>
          simp only [projectValue] at projected
          cases found : items[index]? with
          | none => simp [found] at projected
          | some item =>
              simp only [found] at projected
              cases projected
              exact .tuple (List.mem_of_getElem? found)
      | field | ptr | construct => simp [projectValue] at projected
  | letValue _ matched _ valueIH bodyIH =>
      intro env ok
      obtain ⟨sound, run⟩ := valueIH env ok
      obtain ⟨bodySound, bodyRun⟩ := bodyIH _ (EnvOK.append (bind_aligned _ _ _ _ sound matched) ok)
      refine ⟨by simpa only [scan] using bodySound, fun sites inside => ?_⟩
      simp only [scan, List.mem_append] at inside
      exact .letValue (run sites fun site member => inside site (.inl member)) matched
        (bodyRun sites fun site member => inside site (.inr member))
  | store _ cell ih =>
      intro env ok
      obtain ⟨_, run⟩ := ih env ok
      exact ⟨by simp only [scan]; exact .nil,
        fun sites inside => .store (run sites (by simpa only [scan] using inside)) cell⟩
  | load _ cell typed ih =>
      intro env ok
      obtain ⟨sound, run⟩ := ih env ok
      exact ⟨by simp only [scan]; exact sound.proper (.load cell typed),
        fun sites inside => .load (run sites (by simpa only [scan] using inside)) cell typed⟩
  | hint _ typed ih =>
      intro env ok
      obtain ⟨_, run⟩ := ih env ok
      exact ⟨by simp only [scan]; exact .nil,
        fun sites inside => .hint (run sites (by simpa only [scan] using inside)) typed⟩
  | neg _ operation ih =>
      intro env ok
      obtain ⟨_, run⟩ := ih env ok
      exact ⟨by simp only [scan]; exact .nil,
        fun sites inside => .neg (run sites (by simpa only [scan] using inside)) operation⟩
  | assertEq _ _ operation leftIH rightIH =>
      intro env ok
      obtain ⟨_, leftRun⟩ := leftIH env ok
      obtain ⟨_, rightRun⟩ := rightIH env ok
      refine ⟨by simp only [scan]; exact .nil, fun sites inside => ?_⟩
      simp only [scan, List.mem_append] at inside
      exact .assertEq (leftRun sites fun site member => inside site (.inl member))
        (rightRun sites fun site member => inside site (.inr member)) operation
  | ptrEq _ _ leftIH rightIH =>
      intro env ok
      obtain ⟨_, leftRun⟩ := leftIH env ok
      obtain ⟨_, rightRun⟩ := rightIH env ok
      refine ⟨by simp only [scan]; exact .nil, fun sites inside => ?_⟩
      simp only [scan, List.mem_append] at inside
      exact .ptrEq (leftRun sites fun site member => inside site (.inl member))
        (rightRun sites fun site member => inside site (.inr member))
  | @binary _ lhs _ rhs _ op _ left right operation leftIH rightIH =>
      intro env ok
      obtain ⟨sound, leftRun⟩ := leftIH env ok
      obtain ⟨_, rightRun⟩ := rightIH env ok
      refine ⟨?_, fun sites inside => ?_⟩
      · simp only [scan]
        unfold moved
        split
        · cases right
          exact sound.down operation
        · cases right
          exact sound.up operation
        · exact .nil
      · simp only [scan, List.mem_append] at inside
        exact .binary (leftRun sites fun site member => inside site (.inl member))
          (rightRun sites fun site member => inside site (.inr member)) operation
  | call _ callee ih =>
      intro env ok
      obtain ⟨sound, run⟩ := ih env ok
      refine ⟨by simp only [scan]; exact .nil, fun sites inside => ?_⟩
      simp only [scan, List.mem_append, List.mem_singleton] at inside
      exact .call (run sites fun site member => inside site (.inl member))
        ⟨callee, _, inside _ (.inr rfl), rfl, sound⟩
  | matchValue _ selected _ valueIH branchIH =>
      intro env ok
      obtain ⟨sound, run⟩ := valueIH env ok
      obtain ⟨arm, member, matched, rfl⟩ := selectArm_some selected
      obtain ⟨branchSound, branchRun⟩ :=
        branchIH _ (EnvOK.append (bind_aligned _ _ _ _ sound matched) ok)
      refine ⟨?_, fun sites inside => ?_⟩
      · simp only [scan]
        intro fact present
        exact branchSound fact (mem_meet present _
          (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨arm, member, rfl⟩, rfl⟩))
      · simp only [scan, List.mem_append, List.mem_flatten, List.mem_map] at inside
        exact .matchValue (run sites fun site present => inside site (.inl present)) selected
          (branchRun sites fun site present =>
            inside site (.inr ⟨_, ⟨_, ⟨arm, member, rfl⟩, rfl⟩, present⟩))
  | nil => exact ⟨.nil, fun _ _ => .nil⟩
  | cons _ _ headIH tailIH =>
      rename_i env ok
      obtain ⟨headSound, headRun⟩ := headIH env ok
      obtain ⟨tailSound, tailRun⟩ := tailIH env ok
      refine ⟨.cons headSound tailSound, fun sites inside => ?_⟩
      simp only [List.map_cons, List.flatten_cons, List.mem_append] at inside
      exact .cons (headRun sites fun site member => inside site (.inl member))
        (tailRun sites fun site member => inside site (.inr member))

theorem scanArgs_sound {decls : Declarations} {calls : CallRelation F} {locals : Environment F}
    {exprs : List (Expr F)} {values : List (Value F)}
    (evaluated : ROMEvalArgsWith decls rom calls locals exprs values)
    {env : List (String × Parts)} (ok : EnvOK rom params env locals) :
    List.Forall₂ (Sound rom params) ((exprs.map (scan env)).map (·.1)) values := by
  induction evaluated using ROMEvalArgsWith.rec
    (motive_1 := fun _ _ _ _ => True) with
  | nil => exact .nil
  | cons head _ _ tailIH => exact .cons (scan_sound head _ ok).1 (tailIH ok)
  | _ => trivial

/-! ## The guard of the static analysis -/

/-- A call to `name` with arguments `values` is one of `sites`, and its arguments satisfy that
site's static relations to `params`. -/
def Allowed (rom : ROM F) (params : List (Value F)) (sites : List Call) (name : String)
    (values : List (Value F)) : Prop :=
  ∃ site ∈ sites, site.callee = name ∧ List.Forall₂ (Sound rom params) site.args values

/-- The guard that holds of an expression in an environment the static analysis describes,
when every call the analysis lists for it is one of `sites`. It allows the calls of `sites`
whose arguments satisfy their static relations to `params`. -/
def guard (decls : Declarations) (rom : ROM F) (calls : CallRelation F) (params : List (Value F))
    (sites : List Call) : CallGuard decls rom calls where
  holds env expr := ∃ static, EnvOK rom params static env ∧ ∀ site ∈ (scan static expr).2, site ∈ sites
  allowed := Allowed rom params sites
  sub := by
    rintro env env' expr expr' ⟨static, ok, inside⟩ reach
    have item : ∀ {items : List (Expr F)} {item : Expr F} {site : Call}, item ∈ items →
        site ∈ (scan static item).2 → site ∈ ((items.map (scan static)).map (·.2)).flatten :=
      fun member present => List.mem_flatten.mpr
        ⟨_, List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨_, member, rfl⟩, rfl⟩, present⟩
    cases reach with
    | tuple member | construct member =>
        exact ⟨static, ok, fun site present => inside site (by
          simp only [scan]; exact item member present)⟩
    | project | store | load | hint | neg =>
        exact ⟨static, ok, fun site present => inside site (by simpa only [scan] using present)⟩
    | letValue | binaryLeft | assertEqLeft | ptrEqLeft | matchScrutinee =>
        exact ⟨static, ok, fun site present => inside site (by
          simp only [scan, List.mem_append]; exact .inl present)⟩
    | binaryRight | assertEqRight | ptrEqRight =>
        exact ⟨static, ok, fun site present => inside site (by
          simp only [scan, List.mem_append]; exact .inr present)⟩
    | letBody evaluated matched =>
        exact ⟨_, EnvOK.append (bind_aligned _ _ _ _ (scan_sound evaluated static ok).1 matched) ok,
          fun site present => inside site (by
            simp only [scan, List.mem_append]; exact .inr present)⟩
    | callArg member =>
        exact ⟨static, ok, fun site present => inside site (by
          simp only [scan, List.mem_append]; exact .inl (item member present))⟩
    | matchArm evaluated member matched =>
        exact ⟨_, EnvOK.append (bind_aligned _ _ _ _ (scan_sound evaluated static ok).1 matched) ok,
          fun site present => inside site (by
            simp only [scan, List.mem_append]
            exact .inr (List.mem_flatten.mpr
              ⟨_, List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨_, member, rfl⟩, rfl⟩, present⟩))⟩
  call := by
    rintro env name args values ⟨static, ok, inside⟩ evaluated
    exact ⟨⟨name, (args.map (scan static)).map (·.1)⟩,
      inside _ (by simp [scan]), rfl,
      scanArgs_sound evaluated ok⟩

/-- A function's parameters, bound to its arguments, are what the static analysis starts
from. -/
theorem EnvOK.parameters : ∀ (declared : List (String × Ty)) (args : List (Value F)) (k : Nat),
    (∀ j value, args[j]? = some value → params[k + j]? = some value) →
    EnvOK rom params ((declared.zipIdx k).map fun (param, i) => (param.1, [(i, Relation.same)]))
      ((declared.map Prod.fst).zip args)
  | [], _, _, _ => by intro name value found; simp at found
  | param :: declared, [], _, _ => by intro name value found; simp at found
  | param :: declared, arg :: args, k, indexed => by
      intro name value found
      simp only [List.map_cons, List.zip_cons_cons, List.find?_cons] at found
      by_cases here : param.1 = name
      · subst here
        simp only [beq_self_eq_true, Option.some.injEq, Prod.mk.injEq, true_and] at found
        subst found
        intro fact member
        simp only [List.zipIdx_cons, List.map_cons, List.lookup, beq_self_eq_true,
          Option.getD_some, List.mem_singleton] at member
        subst member
        simpa [Holds] using indexed 0 arg rfl
      · have differs : (param.1 == name) = false := by simpa using here
        have other : (name == param.1) = false := by simpa using fun same => here same.symm
        simp only [differs] at found
        have rest := EnvOK.parameters declared args (k + 1) (fun j value at_ => by
          have := indexed (j + 1) value (by simpa using at_)
          simpa [Nat.add_assoc, Nat.add_comm 1 j] using this) name value found
        simpa [List.zipIdx_cons, List.lookup, other] using rest

/-- The guard holds of a function's body in the environment of its call. -/
theorem guard_body {decls : Declarations} {calls : CallRelation F} (function : Function F)
    (args : List (Value F)) :
    (guard decls rom calls args (Structural.calls function)).holds
      ((function.params.map Prod.fst).zip args) function.body :=
  ⟨_, EnvOK.parameters function.params args 0 (by simp), fun _ member => member⟩

end Aiur.Optimized.Depth.Structural
