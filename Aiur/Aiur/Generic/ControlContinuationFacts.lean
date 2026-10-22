import Aiur.Generic.ControlScopeFacts
import Aiur.Generic.ControlRules

namespace Aiur.Generic.ControlLower
open SourceSemantics OpenSource Engine
variable {F : Type} [Field F] [DecidableEq F]
variable {world : SourceSemantics.World F} {calls : CallRelation F}
variable {locals : Environment F Nat} {next : Continuation F} {handlers : Handlers F}

/-- Interpret a compiler continuation in its captured lexical environment. -/
def Continuation.run (next : Continuation F) (world : SourceSemantics.World F) (calls : CallRelation F)
    (locals : Environment F Nat) (value : SourceValue F) (before : Heap F) (result : SourceValue F) (after : Heap F) : Prop :=
  OpenSource.EvalExpr world calls [] ((next.arg, value) :: locals) next.body before result after

def Handlers.run (handlers : Handlers F) (world : SourceSemantics.World F) (calls : CallRelation F)
    (locals : Environment F Nat) (target : ExitTarget) (value : SourceValue F)
    (before : Heap F) (result : SourceValue F) (after : Heap F) : Prop :=
  ∃ next, handlers.lookup target = some next ∧ next.run world calls locals value before result after

structure Fresh (name : String) (env : Renaming) (next : Continuation F) (handlers : Handlers F) : Prop where
  scope : name ∉ env.map Prod.snd
  next : name ∉ next.names
  handlers : ∀ target next, handlers.lookup target = some next → name ∉ next.names

theorem fresh_reserved (fresh : name ∉ reserved env next handlers) : Fresh name env next handlers := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; exact fresh (by simp [reserved, h])
  · intro h; exact fresh (by simp [reserved, h])
  · intro target k hk h
    have member : (target, k) ∈ handlers := by
      obtain ⟨left, right, rfl, _⟩ := List.lookup_eq_some_iff.mp hk
      simp
    exact fresh (by simp only [reserved, List.mem_append, List.mem_flatMap]; exact .inr ⟨_, member, h⟩)

theorem env_prepend {names : List String} (extra : Environment F Nat)
    (fresh : ∀ n ∈ names, n ∉ extra.map Prod.fst) : EnvAgrees names (extra ++ locals) locals := by
  intro n hn
  rw [List.find?_append, find_lookup, lookup_none (fresh n hn)]
  rfl

theorem Continuation.run_prepend (extra : Environment F Nat)
    (fresh : ∀ n ∈ next.names, n ∉ extra.map Prod.fst) :
    next.run world calls (extra ++ locals) value before result after ↔
      next.run world calls locals value before result after := by
  apply OpenSource.evalExpr_env_iff
  exact (env_prepend extra (fun n hn => fresh n (by simp [Continuation.names, hn]))).prepend [(next.arg, value)]

theorem Continuation.run_add (fresh : name ∉ next.names) :
    next.run world calls ((name, extra) :: locals) value before result after ↔
      next.run world calls locals value before result after := by
  apply Continuation.run_prepend [(name, extra)]
  intro n hn
  simpa using (show n ≠ name from fun same => fresh (same ▸ hn))

theorem Handlers.run_add
    (fresh : ∀ target next, handlers.lookup target = some next → name ∉ next.names) :
    handlers.run world calls ((name, extra) :: locals) target value before result after ↔
      handlers.run world calls locals target value before result after := by
  constructor <;> rintro ⟨next, found, ev⟩
  · exact ⟨next, found, (next.run_add (fresh _ _ found)).mp ev⟩
  · exact ⟨next, found, (next.run_add (fresh _ _ found)).mpr ev⟩

theorem Handlers.run_prepend (extra : Environment F Nat)
    (fresh : ∀ target next, handlers.lookup target = some next →
      ∀ n ∈ next.names, n ∉ extra.map Prod.fst) :
    handlers.run world calls (extra ++ locals) target value before result after ↔
      handlers.run world calls locals target value before result after := by
  constructor <;> rintro ⟨next, found, ev⟩
  · exact ⟨next, found, (next.run_prepend extra (fresh _ _ found)).mp ev⟩
  · exact ⟨next, found, (next.run_prepend extra (fresh _ _ found)).mpr ev⟩

theorem eval_apply :
    OpenSource.EvalExpr world calls [] locals (next.apply expr) before result after ↔
      ∃ value middle, OpenSource.EvalExpr world calls [] locals expr before value middle ∧
        next.run world calls locals value middle result after := by
  constructor
  · intro h; cases h with
    | letValue value matched body =>
        simp only [World.matchPattern, matchPatternWith, except_pure_ok, Option.some.injEq] at matched
        subst matched
        exact ⟨_, _, value, body⟩
  · rintro ⟨value, middle, ev, body⟩
    exact .letValue (bindings := [(next.arg, value)]) ev (by simp [World.matchPattern, matchPatternWith]) body

theorem eval_apply_exec :
    OpenSource.EvalExpr world calls [] locals (next.apply expr) before result after ↔
      Exec world calls [] locals expr
        (fun value middle => next.run world calls locals value middle result after) (fun _ _ _ => False) before := by
  rw [eval_apply]
  simp only [Exec, and_false, exists_false, or_false]

theorem exec_var_found (found : locals.find? (·.1 == name) = some (name, value)) :
    Exec world calls [] locals (.var name) normal abrupt heap ↔ normal value heap := by
  rw [exec_var, found]
  simp only [Option.some.injEq, Prod.mk.injEq, true_and, exists_eq_left']

theorem exec_var_head :
    Exec world calls [] ((name, value) :: locals) (.var name) normal abrupt heap ↔ normal value heap :=
  exec_var_found (by simp)

theorem execArgs_pure {es : List (Expr F)} {vs : List (SourceValue F)}
    (related : List.Forall₂ (fun e v => ∀ normal abrupt heap,
      Exec world calls [] locals e normal abrupt heap ↔ normal v heap) es vs) :
    ExecArgs world calls [] locals es normal abrupt heap ↔ normal vs heap := by
  induction related generalizing normal with
  | nil => exact execArgs_nil
  | cons h _ ih => rw [execArgs_cons, h, ih]

theorem exec_projects (found : locals.find? (·.1 == name) = some (name, .tuple values)) :
    ExecArgs world calls [] locals (projects name values.length) normal abrupt heap ↔ normal values heap := by
  apply execArgs_pure (vs := values)
  apply List.forall₂_of_length_eq_of_get
  · simp [projects]
  · intro i hi hv normal abrupt heap
    simp only [projects, List.get_eq_getElem, List.getElem_map, List.getElem_range]
    rw [exec_project, exec_var_found found]
    simp [projectValue, List.getElem?_eq_getElem hv, bind, Except.bind, pure, Except.pure]

theorem run_repeat (fresh : input ∉ next.names) :
    (Continuation.mk input (next.apply (.repeat (.var input) n))).run world calls locals value before result after ↔
      next.run world calls locals (.tuple (List.replicate n value)) before result after := by
  change OpenSource.EvalExpr _ _ _ _ (next.apply _) _ _ _ ↔ _
  rw [eval_apply_exec, exec_repeat, exec_var_head]
  simp only [Continuation.run_add fresh, Ty.subst_nil]

theorem run_store (fresh : input ∉ next.names) :
    (Continuation.mk input (next.apply (.store (.var input)))).run world calls locals value before result after ↔
      next.run world calls locals (.ptr value.type before.length) (before ++ [value]) result after := by
  change OpenSource.EvalExpr _ _ _ _ (next.apply _) _ _ _ ↔ _
  rw [eval_apply_exec, exec_store, exec_var_head]
  simp only [Continuation.run_add fresh, Ty.subst_nil]

theorem run_index (fresh : input ∉ next.names) :
    (Continuation.mk input (next.apply (.index (.var input) i))).run world calls locals value before result after ↔
      ∃ output, projectValue value i = .ok output ∧ next.run world calls locals output before result after := by
  change OpenSource.EvalExpr _ _ _ _ (next.apply _) _ _ _ ↔ _
  rw [eval_apply_exec, exec_index, exec_var_head]
  simp only [Continuation.run_add fresh, Ty.subst_nil]

theorem run_project (fresh : input ∉ next.names) :
    (Continuation.mk input (next.apply (.project (.var input) i))).run world calls locals value before result after ↔
      ∃ output, projectValue value i = .ok output ∧ next.run world calls locals output before result after := by
  change OpenSource.EvalExpr _ _ _ _ (next.apply _) _ _ _ ↔ _
  rw [eval_apply_exec, exec_project, exec_var_head]
  simp only [Continuation.run_add fresh, Ty.subst_nil]

theorem run_member (fresh : input ∉ next.names) :
    (Continuation.mk input (next.apply (.member (.var input) field))).run world calls locals value before result after ↔
      ∃ output, memberValue [] field value = .ok output ∧ next.run world calls locals output before result after := by
  change OpenSource.EvalExpr _ _ _ _ (next.apply _) _ _ _ ↔ _
  rw [eval_apply_exec, exec_member, exec_var_head]
  simp only [Continuation.run_add fresh, Ty.subst_nil]

theorem run_slice (fresh : input ∉ next.names) :
    (Continuation.mk input (next.apply (.slice (.var input) start stop))).run world calls locals value before result after ↔
      ∃ output, sliceValue value start stop = .ok output ∧ next.run world calls locals output before result after := by
  change OpenSource.EvalExpr _ _ _ _ (next.apply _) _ _ _ ↔ _
  rw [eval_apply_exec, exec_slice, exec_var_head]
  simp only [Continuation.run_add fresh, Ty.subst_nil]

theorem run_load (fresh : input ∉ next.names) :
    (Continuation.mk input (next.apply (.load (.var input)))).run world calls locals value before result after ↔
      ∃ output, loadValue before value = .ok output ∧ next.run world calls locals output before result after := by
  change OpenSource.EvalExpr _ _ _ _ (next.apply _) _ _ _ ↔ _
  rw [eval_apply_exec, exec_load, exec_var_head]
  simp only [Continuation.run_add fresh, Ty.subst_nil]

theorem run_neg (fresh : input ∉ next.names) :
    (Continuation.mk input (next.apply (.neg (.var input)))).run world calls locals value before result after ↔
      ∃ output, evalNeg value = .ok output ∧ next.run world calls locals output before result after := by
  change OpenSource.EvalExpr _ _ _ _ (next.apply _) _ _ _ ↔ _
  rw [eval_apply_exec, exec_neg, exec_var_head]
  simp only [Continuation.run_add fresh, Ty.subst_nil]

theorem run_hint (fresh : input ∉ next.names) :
    (Continuation.mk input (next.apply (.hint type (.var input) channel))).run world calls locals value before result after ↔
      ∃ output : Constant F, world.typed type.toCore output = true ∧ next.run world calls locals output.toValue before result after := by
  change OpenSource.EvalExpr _ _ _ _ (next.apply _) _ _ _ ↔ _
  rw [eval_apply_exec, exec_hint, exec_var_head]
  simp only [Continuation.run_add fresh, Ty.subst_nil]

theorem run_construct (fresh : input ∉ next.names) :
    (Continuation.mk input (next.apply (.construct name typeArgs ctor (projects input values.length)))).run world calls locals (.tuple values) before result after ↔
      next.run world calls locals (.construct (instanceName [] name typeArgs) ctor values) before result after := by
  change OpenSource.EvalExpr _ _ _ _ (next.apply _) _ _ _ ↔ _
  rw [eval_apply_exec, exec_construct, exec_projects (by simp)]
  simp only [Continuation.run_add fresh]

theorem run_constructAs (fresh : input ∉ next.names) :
    (Continuation.mk input (next.apply (.constructAs params type ctor (projects input values.length)))).run world calls locals (.tuple values) before result after ↔
      next.run world calls locals (.construct (constructorName [] type) ctor values) before result after := by
  change OpenSource.EvalExpr _ _ _ _ (next.apply _) _ _ _ ↔ _
  rw [eval_apply_exec, exec_constructAs, exec_projects (by simp)]
  simp only [Continuation.run_add fresh]

theorem run_builtin (fresh : input ∉ next.names) :
    (Continuation.mk input (next.apply (.builtin paths (projects input values.length)))).run
      world calls locals (.tuple values) before result after ↔
      ∃ output, paths.apply values = .ok output ∧
        next.run world calls locals output before result after := by
  change OpenSource.EvalExpr _ _ _ _ (next.apply _) _ _ _ ↔ _
  rw [eval_apply_exec, exec_builtin, exec_projects (by simp)]
  simp only [Continuation.run_add fresh]

theorem run_update (fresh : input ∉ next.names) :
    (Continuation.mk input (next.apply (.update paths (projects input values.length)))).run
      world calls locals (.tuple values) before result after ↔
      ∃ output, Update.value [] paths values = .ok output ∧
        next.run world calls locals output before result after := by
  change OpenSource.EvalExpr _ _ _ _ (next.apply _) _ _ _ ↔ _
  rw [eval_apply_exec, exec_update, exec_projects (by simp)]
  simp only [Continuation.run_add fresh]

theorem run_record (fresh : input ∉ next.names) :
    (Continuation.mk input (next.apply (.record head (projects input values.length)))).run world calls locals (.tuple values) before result after ↔
      next.run world calls locals (.construct (constructorName [] head.type) structConstructor (head.order values (.tuple []))) before result after := by
  change OpenSource.EvalExpr _ _ _ _ (next.apply _) _ _ _ ↔ _
  rw [eval_apply_exec, exec_record, exec_projects (by simp)]
  simp only [Continuation.run_add fresh]

theorem run_call (fresh : input ∉ next.names) :
    (Continuation.mk input (next.apply (.call name typeArgs (projects input values.length)))).run world calls locals (.tuple values) before result after ↔
      ∃ v a, calls (instanceName [] name typeArgs) values before v a ∧ next.run world calls locals v a result after := by
  change OpenSource.EvalExpr _ _ _ _ (next.apply _) _ _ _ ↔ _
  rw [eval_apply_exec, exec_call, exec_projects (by simp)]
  simp only [Continuation.run_add fresh]

theorem run_binary (freshLeft : left ∉ next.names) (freshRight : right ∉ next.names)
    (different : left ≠ right) :
    (Continuation.mk right (next.apply (.binary op (.var left) (.var right)))).run
      world calls ((left, x) :: locals) y before result after ↔
      ∃ output, evalBinOp op x y = .ok output ∧ next.run world calls locals output before result after := by
  change OpenSource.EvalExpr _ _ _ _ (next.apply _) _ _ _ ↔ _
  rw [eval_apply_exec, exec_binary, exec_var_found (value := x) (by simp [different, Ne.symm different]), exec_var_head]
  simp only [Continuation.run_add freshRight, Continuation.run_add freshLeft]

theorem run_arguments (freshHead : head ∉ next.names) (freshTail : tail ∉ next.names)
    (different : head ≠ tail) :
    (Continuation.mk tail (next.apply (.tuple (.var head :: projects tail values.length)))).run
      world calls ((head, value) :: locals) (.tuple values) before result after ↔
      next.run world calls locals (.tuple (value :: values)) before result after := by
  change OpenSource.EvalExpr _ _ _ _ (next.apply _) _ _ _ ↔ _
  rw [eval_apply_exec, exec_tuple, execArgs_cons,
    exec_var_found (value := value) (by simp [different, Ne.symm different]), exec_projects (by simp)]
  simp only [Continuation.run_add freshTail, Continuation.run_add freshHead]

end Aiur.Generic.ControlLower
