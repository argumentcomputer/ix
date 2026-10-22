import Aiur.Generic.LoweringSoundness
import Aiur.Generic.NativeCompleteness
import Aiur.Generic.NativeConstantFacts
import Aiur.Generic.CoreCallInduction
import Aiur.InputTypes

namespace Aiur.Generic

theorem Specialized.prepare_sound [Field F] [DecidableEq F] {s : Source F}
    (q : Specialized s entries) {calls : CallRelation F}
    (closed : ∀ n args b v a, calls n args b v a → Aiur.EvalFn q.program n args b v a)
    (reflect : ∀ n args b v a, calls n args b v a → b.Good q.program.enums →
      (∀ arg ∈ args, arg.Good q.program.enums) → SourceSemantics.EvalFn s.world n args b v a)
    (reachable : name ∈ callableNames q.program)
    (prepared : (Engine.World.ofProgram q.program).prepare name args = .ok (locals, expr))
    (evaluated : OpenCore.EvalExpr (.ofProgram q.program) calls locals expr before result after)
    (heapGood : before.Good q.program.enums)
    (argsGood : ∀ arg ∈ args, arg.Good q.program.enums) :
    SourceSemantics.EvalFn s.world name args before result after := by
  have prepared := (q.coreAgreement.prepare name reachable args locals expr).mpr prepared
  cases compiled : s.compilerFunction? name with
  | none =>
      have sourceAbsent : s.program.sourceFunction? name = none := by
        have ready := q.loweringReady name reachable
        cases found : s.program.sourceFunction? name with
        | none => rfl
        | some _ => simp [found, compiled] at ready
      simp only [Source.coreWorld, compiled, except_bind_ok, except_pure_ok, Prod.mk.injEq] at prepared
      obtain ⟨value, found, rfl, rfl⟩ := prepared
      obtain ⟨rfl, rfl⟩ := Aiur.EvalExpr.constant_result value (evaluated.toProgram closed)
      exact .intro (types := []) (locals := []) (expr := constantExpr value)
        (by simp [Source.world, sourceWorld, sourceAbsent, found, bind, Except.bind, pure, Except.pure])
        (SourceSemantics.constant_evaluates s.world value [] [] after)
  | some core =>
      obtain ⟨source, preparedBody, body, found, expanded, control, safe, params, bodyEq⟩ := Source.compilerFunction_spec compiled
      have check := q.typedLowering name reachable
      simp only [found, Option.all_some, expanded, control] at check
      cases bodyChecked : body.checkLowerTypes q.program [] source.params with
      | none => simp [bodyChecked] at check
      | some type =>
          simp only [Source.coreWorld, compiled, prepareFunction, params] at prepared
          split at prepared
          · rename_i valid
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj prepared)
            rw [bodyEq] at evaluated
            have localsGood : Environment.Good q.program.enums ((source.params.map Prod.fst).zip args) :=
              fun binding member => argsGood binding.2 (List.of_mem_zip member).2
            have native := lowering_sound (source := s.world) q.valid.1 closed reflect
              (fun t ht v hv => (q.coreAgreement.hint t ht v).mpr hv)
              body [] _ _ _ _ safe
              (by rw [parameterTypes source.params args valid.1]; exact bodyChecked)
              evaluated heapGood localsGood
            rcases (ControlLower.function_correct control).mp native with normal | abrupt
            · have original := (SourceSemantics.expression_preparation_open_iff s.program s.world
                (fun _ _ => rfl) rfl _ _ _ expanded _ _ _ _).mpr normal
              exact .intro (by simp only [Source.world, sourceWorld, found, SourceFunction.prepare, if_pos valid])
                original.close
            · have original := (SourceSemantics.exit_preparation_open_iff s.program s.world
                (fun _ _ => rfl) rfl _ _ _ expanded _ _ _ _ _).mpr abrupt
              exact .returned (by simp only [Source.world, sourceWorld, found, SourceFunction.prepare, if_pos valid])
                original.close
          · cases prepared

/-- Reflection at any reachable instance, with the ordinary well-formed heap
and argument invariants. The proof inducts on the finite core evaluation;
recursive source functions need not be total. -/
theorem Specialized.native_sound [Field F] [DecidableEq F] {s : Source F}
    (q : Specialized s entries) (reachable : name ∈ callableNames q.program)
    (evaluated : Aiur.EvalFn q.program name args before result after)
    (heapGood : before.Good q.program.enums) (argsGood : ∀ arg ∈ args, arg.Good q.program.enums) :
    SourceSemantics.EvalFn s.world name args before result after := by
  let calls : CallRelation F := fun n args b v a =>
    Aiur.EvalFn q.program n args b v a ∧
      (b.Good q.program.enums → (∀ arg ∈ args, arg.Good q.program.enums) →
        SourceSemantics.EvalFn s.world n args b v a)
  have closed : ∀ n args b v a, calls n args b v a → Aiur.EvalFn q.program n args b v a :=
    fun _ _ _ _ _ h => h.1
  have reflect : ∀ n args b v a, calls n args b v a → b.Good q.program.enums →
      (∀ arg ∈ args, arg.Good q.program.enums) → SourceSemantics.EvalFn s.world n args b v a :=
    fun _ _ _ _ _ h => h.2
  have lifted : Engine.EvalFn (.ofProgram q.program) name args before result after := Engine.core_iff.mpr evaluated
  have conclusion : calls name args before result after := lifted.openCalls q.coreAgreement.symm.closed
    (fun n hn args ls e b v a prepared body ev =>
      ⟨.intro prepared body.toCore, fun hg ag => q.prepare_sound closed reflect hn prepared ev hg ag⟩) reachable
  exact conclusion.2 heapGood argsGood

theorem Specialized.native_entry_sound [Field F] [DecidableEq F] {s : Source F}
    (q : Specialized s entries) (selected : name ∈ entries)
    (evaluated : Aiur.EvalFn q.program name args [] result heap) :
    SourceSemantics.EvalFn s.world name args [] result heap := by
  have root := q.valid.2.2.2.2.2.2.2 name selected
  exact q.native_sound root.1 evaluated (by simp [Heap.Good]) (fun arg member =>
    ⟨(evaluated.publicArguments root.2.2 arg member).2,
      Value.pointerNames_of_free (evaluated.public_pointerFree root.2.2 arg member)⟩)

/-- Selected entrypoint claims have identical finite source and compiled
evaluations, with the exact same result and allocation heap. -/
theorem Specialized.native_entry_iff [Field F] [DecidableEq F] {s : Source F}
    (q : Specialized s entries) (selected : name ∈ entries) :
    SourceSemantics.EvalFn s.world name args [] result heap ↔
      Aiur.EvalFn q.program name args [] result heap :=
  ⟨q.native_core_complete (q.valid.2.2.2.2.2.2.2 name selected).1, q.native_entry_sound selected⟩

/-- The public claim predicates agree before and after compiler preparation.
The selected interface is external to the original source program. -/
theorem Specialized.native_evalCall_iff [Field F] [DecidableEq F] {s : Source F}
    (q : Specialized s entries) (selected : name ∈ entries) :
    s.EvalCall name args result ↔ Aiur.EvalCall q.program name args result := by
  have entry := q.valid.2.2.2.2.2.2.2 name selected
  constructor
  · rintro ⟨_, heap, evaluated⟩
    exact ⟨entry.2.2, heap, (q.native_entry_iff selected).mp evaluated⟩
  · rintro ⟨_, heap, evaluated⟩
    exact ⟨entry.2.1, heap, (q.native_entry_iff selected).mpr evaluated⟩

end Aiur.Generic
