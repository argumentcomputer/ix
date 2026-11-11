import Aiur.Generic.Specialize
import Aiur.Generic.CoreRuntime
import Aiur.TableChecking

namespace Aiur.Generic

private theorem lookupMap_transfer [DecidableEq F] {p q : Aiur.Program F}
    {n : String} {args : List (SourceValue F)} {value : Constant F}
    (checked : typecheck q = .ok ()) (tables : p.tables = q.tables) (maps : p.maps = q.maps)
    (looked : lookupMap p n args = .ok value) : lookupMap q n args = .ok value := by
  obtain ⟨m, key, found, _, _, extracted, row, _⟩ := lookupMap_spec looked
  have name : m.name = n := by simpa [Program.findMap?] using List.find?_some found
  have member : m ∈ q.maps := by rw [← maps]; exact List.mem_of_find?_eq_some found
  have same := Value.toConstant_spec extracted
  cases key with
  | field | construct => simp [show (Constant.toValue : Constant F → Value F _) = Value.mapAddress Empty.elim from rfl, Constant.toValue, Value.mapAddress] at same
  | ptr _ address => exact Empty.elim address
  | tuple constants =>
      have argsEq : constants.map Constant.toValue = args := by simpa [show (Constant.toValue : Constant F → Value F _) = Value.mapAddress Empty.elim from rfl, Constant.toValue, Value.mapAddress] using same
      have rowQ : (.tuple constants, value) ∈ q.mapRows m := by
        simpa only [Program.mapRows, Program.findTable?, tables] using row
      have h := lookupMap_of_entry (A := Nat) (entry := ⟨constants, value⟩) checked member (mapEntry_mem_iff.mpr rowQ)
      simpa only [name, argsEq] using h

private theorem prepared_function_iff [DecidableEq F] {p : Aiur.Program F}
    (found : p.findFunction? n = some fn) :
    prepareCall p n args = .ok (locals, body) ↔
      fn.params.map Prod.snd = args.map Value.type ∧
      (∀ v ∈ args, v.wellFormed p.enums = true) ∧
      locals = (fn.params.map Prod.fst).zip args ∧ body = fn.body := by
  constructor
  · intro h
    rcases prepareCall_spec h with ⟨f, hf, ht, hv, hl, hb⟩ | ⟨v, hf, _⟩
    · have : f = fn := Option.some.inj (hf.symm.trans found)
      subst f
      exact ⟨ht, hv, hl, hb⟩
    · simp [found] at hf
  · rintro ⟨ht, hv, rfl, rfl⟩
    exact prepareCall_of_types found ht hv

private theorem prepareFunction_iff :
    prepareFunction enums fn args = .ok (locals, body) ↔
      fn.params.map Prod.snd = args.map Value.type ∧
      (∀ v ∈ args, wellFormed enums v = true) ∧
      locals = (fn.params.map Prod.fst).zip args ∧ body = fn.body := by
  unfold prepareFunction
  split
  · rename_i h
    simp only [List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
    constructor
    · intro same
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same)
      exact ⟨h.1, h.2, rfl, rfl⟩
    · rintro ⟨_, _, rfl, rfl⟩
      rfl
  · rename_i h
    simp only [List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
    simp only [reduceCtorEq, false_iff]
    rintro ⟨ht, hv, _⟩
    exact h ⟨ht, hv⟩

private theorem constant_scope (v : Constant F) : Engine.inScope names hintType v.toExpr = true := by
  cases v with
  | field => simp [Constant.toExpr, Engine.inScope]
  | ptr _ a => exact Empty.elim a
  | tuple xs | construct n c xs =>
      simp only [Constant.toExpr, Engine.inScope, List.all_map, List.all_eq_true, Function.comp_def, id_eq]
      intro x hx
      exact constant_scope x
termination_by sizeOf v

/-- Checked instance lookup and closed declarations imply the runtime
agreement needed by the general simulation theorem. -/
theorem Specialized.coreAgreement [DecidableEq F] {s : Source F} {entries : List String}
    (q : Specialized s entries) :
    Engine.Agreement s.coreWorld (.ofProgram q.program)
      (callableNames q.program) (knownType q.program.enums) := by
  rcases q.valid with ⟨checked, tables, maps, functions, enums, closed, bodies, roots⟩
  have enumAgreement : ∀ n d, q.program.enums.findEnum? n = some d → s.program.enum? n = some d := by
    intro n d found
    have hn : d.name = n := by simpa [Declarations.findEnum?] using List.find?_some found
    simpa [hn] using enums d (List.mem_of_find?_eq_some found)
  have prep : ∀ n ∈ callableNames q.program, ∀ args locals body,
      s.coreWorld.prepare n args = .ok (locals, body) ↔ prepareCall q.program n args = .ok (locals, body) := by
    intro n hn args locals body
    have fnAgreement := functions n hn
    cases found : q.program.findFunction? n with
    | none =>
        have absent : s.compilerFunction? n = none := fnAgreement.trans found
        simp only [Source.coreWorld, absent, prepareCall, found]
        simp only [except_bind_ok, except_pure_ok, Prod.mk.injEq]
        constructor
        · rintro ⟨v, hv, hl, hb⟩
          exact ⟨v, lookupMap_transfer checked tables.symm maps.symm hv, hl, hb⟩
        · rintro ⟨v, hv, hl, hb⟩
          exact ⟨v, lookupMap_transfer s.tablesChecked tables maps hv, hl, hb⟩
    | some fn =>
        have resolved : s.compilerFunction? n = some fn := fnAgreement.trans found
        simp only [Source.coreWorld, resolved, prepareFunction_iff, prepared_function_iff found]
        by_cases ht : fn.params.map Prod.snd = args.map Value.type
        · have known := (bodies fn (List.mem_of_find?_eq_some found)).1
          have values : ∀ v ∈ args, wellFormed s.program.enum? v = v.wellFormed q.program.enums := by
            intro v hv
            apply formed_agrees enumAgreement closed
            have mem : v.type ∈ fn.params.map Prod.snd := ht ▸ List.mem_map.mpr ⟨v, hv, rfl⟩
            obtain ⟨param, hp, same⟩ := List.mem_map.mp mem
            simpa [same] using known param hp
          simp only [ht, true_and]
          apply and_congr _ Iff.rfl
          constructor
          · intro all v hv; rw [← values v hv]; exact all v hv
          · intro all v hv; rw [values v hv]; exact all v hv
        · simp [ht]
  refine ⟨prep, ?_, ?_⟩
  · intro t ht v
    exact congrArg (· = true) (hasType_agrees enumAgreement closed t ht v) |>.to_iff
  · intro n hn args locals body prepared
    have target := (prep n hn args locals body).mp prepared
    rcases prepareCall_spec target with ⟨fn, found, _, _, _, rfl⟩ | ⟨v, _, _, _, rfl⟩
    · exact (bodies fn (List.mem_of_find?_eq_some found)).2
    · exact constant_scope v

/-- The lowered reference interpreter and the concrete compiler program agree.
This core-level result is separate from source-level specialization. -/
theorem Specialized.coreEvalFn_iff [Field F] [DecidableEq F] {s : Source F} {entries : List String}
    (q : Specialized s entries) (reachable : name ∈ callableNames q.program) :
    Engine.EvalFn s.coreWorld name args before result after ↔
      Aiur.EvalFn q.program name args before result after :=
  (Engine.evalFn_iff q.coreAgreement reachable).trans Engine.core_iff

/-- Core-level equivalence at selected entries. -/
theorem Specialized.coreEvalCall_iff [Field F] [DecidableEq F] {s : Source F} {entries : List String}
    (q : Specialized s entries) (selected : name ∈ entries) :
    s.CoreEvalCall name args result ↔ Aiur.EvalCall q.program name args result := by
  have root := q.valid.2.2.2.2.2.2.2 name selected
  simp only [Source.CoreEvalCall, Aiur.EvalCall, root.2.1, root.2.2, true_and]
  exact exists_congr fun heap => q.coreEvalFn_iff root.1

private theorem cached_lookup {A : Type} (lookup : String → Option A)
    {names : List String} {name : String} (member : name ∈ names) :
    (((names.map fun n => (n, lookup n)).find? (·.1 == name)).bind Prod.snd) = lookup name := by
  induction names with
  | nil => simp at member
  | cons n names ih =>
      by_cases same : n = name
      · subst n; simp
      · have hn := (List.mem_cons.mp member).resolve_left (Ne.symm same)
        simpa [List.find?, same] using ih hn

private theorem source_constant_scope (v : Constant F) :
    SourceSemantics.inScope names (fun _ => true) types (constantExpr v) = true := by
  cases v with
  | field => simp [constantExpr, SourceSemantics.inScope]
  | ptr _ a => exact Empty.elim a
  | tuple xs | construct n c xs =>
      simp only [constantExpr, SourceSemantics.inScope, List.all_map, List.all_eq_true, Function.comp_def, id_eq]
      intro x hx
      exact source_constant_scope x
termination_by sizeOf v

/-- Finite specialization preserves source bodies and concrete type bindings.
This agreement is independent of the later translation into core expressions. -/
theorem Specialized.sourceAgreement [DecidableEq F] {s : Source F} {entries : List String}
    (q : Specialized s entries) :
    SourceSemantics.Agreement s.world q.world (callableNames q.program) (fun _ => true) := by
  have prep : ∀ n ∈ callableNames q.program, ∀ args,
      s.world.prepare n args = q.world.prepare n args := by
    intro n hn args
    simp only [Source.world, Specialized.world, Specialized.instances, sourceWorld,
      cached_lookup s.program.sourceFunction? hn]
  refine ⟨rfl, rfl, fun n hn args _ _ _ => (congrArg (· = _) (prep n hn args)).to_iff,
    fun _ _ _ => Iff.rfl, ?_⟩
  intro n hn args types locals body prepared
  cases found : s.program.sourceFunction? n with
  | none =>
      simp only [Source.world, sourceWorld, found, except_bind_ok, except_pure_ok,
        Prod.mk.injEq] at prepared
      obtain ⟨v, _, rfl, rfl, rfl⟩ := prepared
      exact source_constant_scope v
  | some fn =>
      have closed := q.sourceClosed n hn
      simp only [found, Option.all_some] at closed
      simp only [Source.world, sourceWorld, found, SourceFunction.prepare] at prepared
      split at prepared
      · obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj prepared) |>.imp_right Prod.mk.inj
        exact closed
      · simp at prepared

/-- Source-level specialization preserves and reflects every finite evaluation,
including native array operations, pointer patterns, hints, and the exact heap. -/
theorem Specialized.evalFn_iff [Field F] [DecidableEq F] {s : Source F} {entries : List String}
    (q : Specialized s entries) (reachable : name ∈ callableNames q.program) :
    SourceSemantics.EvalFn s.world name args before result after ↔
      SourceSemantics.EvalFn q.world name args before result after :=
  SourceSemantics.evalFn_iff q.sourceAgreement reachable

theorem Specialized.evalCall_iff [Field F] [DecidableEq F] {s : Source F} {entries : List String}
    (q : Specialized s entries) (selected : name ∈ entries) :
    s.EvalCall name args result ↔ q.EvalCall name args result := by
  have root := q.valid.2.2.2.2.2.2.2 name selected
  have entry := q.checkEntry_iff.mpr selected
  simp only [Source.EvalCall, Specialized.EvalCall, root.2.1, entry, true_and]
  exact exists_congr fun heap => q.evalFn_iff root.1

theorem Specialized.run_spec [Field F] [DecidableEq F] {s : Source F} {entries : List String}
    {q : Specialized s entries} {hints : s.HintProvider} {name args fuel result heap}
    (run : q.run name args fuel hints = .ok (result, heap)) :
    q.checkEntry name = .ok () ∧ SourceSemantics.EvalFn q.world name args [] result heap := by
  cases entry : q.checkEntry name with
  | error e => simp [Specialized.run, entry, bind, Except.bind] at run
  | ok u =>
      cases u
      cases prepared : q.world.prepare name args with
      | error e => simp [Specialized.run, entry, prepared, Except.mapError, bind, Except.bind] at run
      | ok triple =>
          rcases triple with ⟨types, locals, body⟩
          have executed : SourceSemantics.evalFunctionWith q.world hints types locals fuel body [] = .ok (result, heap) := by
            cases h : SourceSemantics.evalFunctionWith q.world hints types locals fuel body [] <;>
              simpa [Specialized.run, entry, prepared, h, Except.mapError, bind, Except.bind] using run
          exact ⟨rfl, SourceSemantics.evalFunction_spec prepared executed⟩

theorem Specialized.evalCall_of_run [Field F] [DecidableEq F] {s : Source F} {entries : List String}
    {q : Specialized s entries} {hints : s.HintProvider} {name args fuel result heap}
    (run : q.run name args fuel hints = .ok (result, heap)) : q.EvalCall name args result := by
  obtain ⟨entry, evaluated⟩ := Specialized.run_spec run
  exact ⟨entry, heap, evaluated⟩

end Aiur.Generic
