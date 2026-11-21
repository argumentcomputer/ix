import Aiur.Inlining.Soundness
import Aiur.Generic.CoreCallInduction
import Aiur.Generic.Specialize
import Aiur.InputTypes
import Aiur.TableChecking

namespace Aiur.Inlining
open Generic

abbrev Bodies (F : Type) := List (String × Tree F)
def Bodies.body (bodies : Bodies F) (name : String) : Tree F :=
  ((bodies.find? (·.1 == name)).map Prod.snd).getD (.tuple [])
def Bodies.function (bodies : Bodies F) (f : Aiur.Function F) : Aiur.Function F :=
  { f with body := (bodies.body f.name).target }
def Bodies.program (bodies : Bodies F) (p : Aiur.Program F) (names : List String) : Aiur.Program F :=
  { p with functions := (p.functions.filter (fun f => !names.contains f.name)).map bodies.function }

/-- The certificate contains only decidable checks of finite syntax. -/
def Bodies.Valid [DecidableEq F] (b : Bodies F) (p : Aiur.Program F) (names entries : List String) : Prop :=
  let q := b.program p names
  typecheck q = .ok () ∧
  (∀ f ∈ p.functions,
    (b.body f.name).source = f.body ∧ (b.body f.name).Safe p names ∧
    (b.body f.name).checkTypes q f.params = some f.result ∧
    Engine.inScope (callableNames q) (knownType q.enums) (b.body f.name).target = true) ∧
  (∀ n ∈ entries, n ∉ names ∧ Aiur.checkEntry q n = .ok ())

instance [DecidableEq F] (b : Bodies F) (p : Aiur.Program F) (names entries : List String) :
    Decidable (b.Valid p names entries) := by unfold Bodies.Valid; infer_instance

structure Prepared [DecidableEq F] (p : Aiur.Program F) (names entries : List String) where
  bodies : Bodies F
  checked : typecheck p = .ok ()
  valid : bodies.Valid p names entries

def Prepared.program [DecidableEq F] {p : Aiur.Program F} {names entries : List String}
    (q : Prepared p names entries) : Aiur.Program F := q.bodies.program p names

def prepare [DecidableEq F] (p : Aiur.Program F) (names entries : List String) :
    Except String (Prepared p names entries) := do
  if checked : typecheck p = .ok () then
    for n in entries do
      if names.contains n then throw s!"inline function '{n}' cannot be an entrypoint"
    let bodies : Bodies F ← p.functions.mapM fun f => do
      let tree ← expand p names (p.functions.length + 1) f.body
      return (f.name,tree)
    let q := bodies.program p names
    (typecheck q).mapError toString
    if valid : bodies.Valid p names entries then return ⟨bodies,checked,valid⟩
    else throw "inlining failed its structural certificate check"
  else throw "inlining requires a typechecked program"

@[simp] theorem Prepared.enums [DecidableEq F] {p : Aiur.Program F} (q : Prepared p names entries) : q.program.enums = p.enums := rfl

theorem Bodies.findFunction (b : Bodies F) (p : Aiur.Program F) (names : List String) (n : String) :
    (b.program p names).findFunction? n =
      if n ∈ names then none else (p.findFunction? n).map b.function := by
  simp only [Bodies.program,Aiur.Program.findFunction?,List.find?_map,List.find?_filter,
    Function.comp_def,Bodies.function]
  by_cases member : n ∈ names
  · rw [if_pos member]
    have absent : p.functions.find? (fun f => decide ((!names.contains f.name) = true ∧ (f.name == n) = true)) = none := by
      apply List.find?_eq_none.mpr
      intro f _
      by_cases named : f.name = n <;> simp [named,member]
    rw [absent]
    rfl
  · rw [if_neg member]
    have predicate : (fun f : Aiur.Function F => decide ((!names.contains f.name) = true ∧ (f.name == n) = true)) =
        (fun f => f.name == n) := by
      funext f
      by_cases named : f.name = n <;> simp [named,member]
    rw [predicate]

theorem function_name {p : Aiur.Program F} (found : p.findFunction? n = some f) : f.name = n := by
  simpa [Aiur.Program.findFunction?] using List.find?_some found

def constantTree : Constant F → Tree F
  | .field x => .literal x
  | .ptr _ a => nomatch a
  | .tuple xs => .tuple (xs.map constantTree)
  | .construct n c xs => .construct n c (xs.map constantTree)
termination_by v => sizeOf v

theorem constantTree_source (v : Constant F) : (constantTree v).source = v.toExpr := by
  cases v with
  | field => simp [constantTree,Tree.source,Constant.toExpr]
  | ptr _ a => exact Empty.elim a
  | tuple xs | construct n c xs =>
      simp only [constantTree,Tree.source,Constant.toExpr,List.map_map]
      congr 1
      exact List.map_congr_left fun x hx => constantTree_source x
termination_by sizeOf v

theorem constantTree_target (v : Constant F) : (constantTree v).target = v.toExpr := by
  cases v with
  | field => simp [constantTree,Tree.target,Constant.toExpr]
  | ptr _ a => exact Empty.elim a
  | tuple xs | construct n c xs =>
      simp only [constantTree,Tree.target,Constant.toExpr,List.map_map]
      congr 1
      exact List.map_congr_left fun x hx => constantTree_target x
termination_by sizeOf v

theorem constantTree_safe (v : Constant F) : (constantTree v).Safe p names := by
  cases v with
  | field => simp [constantTree,Tree.Safe]
  | ptr _ a => exact Empty.elim a
  | tuple xs | construct n c xs =>
      simp only [constantTree,Tree.Safe,List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂]
      intro x hx
      exact constantTree_safe x
termination_by sizeOf v

theorem constant_scope (v : Constant F) : Engine.inScope names hintType v.toExpr = true := by
  cases v with
  | field => simp [Constant.toExpr,Engine.inScope]
  | ptr _ a => exact Empty.elim a
  | tuple xs | construct n c xs =>
      simp only [Constant.toExpr,Engine.inScope,List.all_map,List.all_eq_true,Function.comp_def,id_eq]
      intro x hx
      exact constant_scope x
termination_by sizeOf v

variable [Field F] [DecidableEq F] {p : Aiur.Program F} {names entries : List String}

omit [Field F] in
@[simp] theorem Prepared.lookupMap (q : Prepared p names entries) (n : String) (args : List (SourceValue F)) :
    lookupMap q.program n args = lookupMap p n args := rfl

omit [Field F] in
theorem Prepared.forward (q : Prepared p names entries) : ForwardCalls p q.program names := by
  intro n retained args ls body prepared
  rcases prepareCall_spec prepared with ⟨f,found,types,formed,rfl,rfl⟩ | ⟨v,absent,looked,rfl,rfl⟩
  · have named := function_name found
    have cert := q.valid.2.1 f (List.mem_of_find?_eq_some found)
    refine ⟨q.bodies.body f.name,cert.1,cert.2.1,?_⟩
    have found' : q.program.findFunction? n = some (q.bodies.function f) := by
      simp only [Prepared.program,Bodies.findFunction,if_neg retained,found,Option.map_some]
    exact prepareCall_of_types found' types formed
  · refine ⟨constantTree v,constantTree_source v,constantTree_safe v,?_⟩
    rw [constantTree_target]
    exact prepareCall_map (by simp [Prepared.program,Bodies.findFunction,absent]) (by simpa using looked)

theorem Prepared.complete (q : Prepared p names entries) (retained : name ∉ names)
    (evaluated : Aiur.EvalFn p name args before result after) :
    Aiur.EvalFn q.program name args before result after := by
  cases Engine.core_iff.mpr evaluated with
  | intro prepared body =>
      obtain ⟨tree,source,safe,prepared'⟩ := q.forward name retained _ _ _ prepared
      exact .intro prepared' ((completeExpr (p := p) (q := q.program) rfl q.forward body tree source safe).toCore)

omit [Field F] in
/-- Retained target functions have the original calling convention and the
certified expanded body. Static maps are unchanged. -/
theorem Prepared.backward (q : Prepared p names entries) {args : List (SourceValue F)}
    (prepared : prepareCall q.program n args = .ok (ls,expr)) :
    (∃ f, p.findFunction? n = some f ∧
      f.params.map Prod.snd = args.map Value.type ∧
      (∀ arg ∈ args, arg.wellFormed p.enums = true) ∧
      ls = (f.params.map Prod.fst).zip args ∧ expr = (q.bodies.body f.name).target) ∨
    (∃ v : Constant F, prepareCall p n args = .ok ([],v.toExpr) ∧ ls = [] ∧ expr = v.toExpr) := by
  rcases prepareCall_spec prepared with ⟨g,found,types,formed,rfl,rfl⟩ | ⟨v,absent,looked,rfl,rfl⟩
  · left
    rw [Prepared.program,Bodies.findFunction] at found
    split at found
    · cases found
    · obtain ⟨f,original,rfl⟩ := Option.map_eq_some_iff.mp found
      exact ⟨f,original,types,formed,rfl,rfl⟩
  · right
    have original : p.findFunction? n = none := by
      obtain ⟨m,key,found,_⟩ := lookupMap_spec looked
      have named : m.name = n := by simpa [Aiur.Program.findMap?] using List.find?_some found
      rw [← named]
      exact map_function_absent q.checked (List.mem_of_find?_eq_some found)
    exact ⟨v,prepareCall_map original (by simpa using looked),rfl,rfl⟩

omit [Field F] in
theorem Prepared.closed (q : Prepared p names entries) :
    ∀ n ∈ callableNames q.program, ∀ args ls e,
      (Engine.World.ofProgram q.program).prepare n args = .ok (ls,e) →
      Engine.inScope (callableNames q.program) (knownType q.program.enums) e = true := by
  intro n _ args ls e prepared
  rcases q.backward prepared with ⟨f,found,_,_,_,rfl⟩ | ⟨v,_,_,rfl⟩
  · exact (q.valid.2.1 f (List.mem_of_find?_eq_some found)).2.2.2
  · exact constant_scope v

theorem Prepared.prepare_sound (q : Prepared p names entries) {calls : Generic.CallRelation F}
    (closed : ∀ n args b v a, calls n args b v a → Aiur.EvalFn q.program n args b v a)
    (reflect : ∀ n args b v a, calls n args b v a → b.Good q.program.enums →
      (∀ arg ∈ args, arg.Good q.program.enums) → Aiur.EvalFn p n args b v a)
    (prepared : prepareCall q.program name args = .ok (locals,expr))
    (evaluated : OpenCore.EvalExpr (.ofProgram q.program) calls locals expr before result after)
    (heapGood : before.Good q.program.enums) (argsGood : ∀ arg ∈ args, arg.Good q.program.enums) :
    Aiur.EvalFn p name args before result after := by
  rcases q.backward prepared with ⟨f,found,types,formed,rfl,rfl⟩ | ⟨v,prep,rfl,rfl⟩
  · have cert := q.valid.2.1 f (List.mem_of_find?_eq_some found)
    have localsGood : Environment.Good q.program.enums ((f.params.map Prod.fst).zip args) :=
      fun binding member => argsGood binding.2 (List.of_mem_zip member).2
    have body := soundExpr (p := p) (q := q.program) rfl q.valid.1 closed reflect (q.bodies.body f.name) _ _ _ _ cert.2.1
      (by rw [parameterTypes f.params args types]; exact cert.2.2.1) evaluated heapGood localsGood
    rw [cert.1] at body
    exact .intro (prepareCall_of_types found types formed) body.close.toCore
  · obtain ⟨rfl,rfl⟩ := Aiur.EvalExpr.constant_result v (evaluated.toProgram closed)
    exact .intro prep v.evaluates

theorem Prepared.sound (q : Prepared p names entries)
    (reachable : name ∈ callableNames q.program)
    (evaluated : Aiur.EvalFn q.program name args before result after)
    (heapGood : before.Good q.program.enums) (argsGood : ∀ arg ∈ args, arg.Good q.program.enums) :
    Aiur.EvalFn p name args before result after := by
  let calls : Generic.CallRelation F := fun n args b v a =>
    Aiur.EvalFn q.program n args b v a ∧
      (b.Good q.program.enums → (∀ arg ∈ args, arg.Good q.program.enums) → Aiur.EvalFn p n args b v a)
  have lifted := Engine.core_iff.mpr evaluated
  have conclusion : calls name args before result after := lifted.openCalls q.closed
    (fun n _ args ls e b v a prepared body ev =>
      ⟨.intro prepared body.toCore, fun hg ag => q.prepare_sound
        (fun _ _ _ _ _ h => h.1) (fun _ _ _ _ _ h => h.2) prepared ev hg ag⟩) reachable
  exact conclusion.2 heapGood argsGood

theorem Prepared.entry_sound (q : Prepared p names entries) (selected : name ∈ entries)
    (evaluated : Aiur.EvalFn q.program name args [] result heap) :
    Aiur.EvalFn p name args [] result heap := by
  have entry := (q.valid.2.2 name selected).2
  have reachable : name ∈ callableNames q.program := by
    obtain ⟨signature,found,_⟩ := (checkEntry_ok q.program name).mp entry
    unfold Aiur.Program.findSignature? at found
    cases fn : q.program.findFunction? name with
    | some f => exact List.mem_append_left _ (List.mem_map.mpr
        ⟨f,List.mem_of_find?_eq_some fn,function_name fn⟩)
    | none =>
        simp only [fn] at found
        obtain ⟨m,fm,_⟩ := Option.map_eq_some_iff.mp found
        have named : m.name = name := by simpa [Aiur.Program.findMap?] using List.find?_some fm
        exact List.mem_append_right _ (List.mem_map.mpr ⟨m,List.mem_of_find?_eq_some fm,named⟩)
  exact q.sound reachable evaluated (by simp [Heap.Good]) (fun arg member =>
    ⟨(evaluated.publicArguments entry arg member).2,
      Value.pointerNames_of_free (evaluated.public_pointerFree entry arg member)⟩)

/-- Mandatory expansion preserves exactly the selected entry evaluations,
including allocations and nondeterministic choices. -/
theorem Prepared.entry_iff (q : Prepared p names entries) (selected : name ∈ entries) :
    Aiur.EvalFn p name args [] result heap ↔ Aiur.EvalFn q.program name args [] result heap :=
  ⟨q.complete (q.valid.2.2 name selected).1,q.entry_sound selected⟩

end Aiur.Inlining
