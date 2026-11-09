import IxCC.Cfg.Rc.Proof.Native.SimpleOutcomes
import IxCC.Cfg.Rc.Proof.Physical.AllocationResult
import IxCC.Cfg.Rc.Proof.Physical.CaseResult
import IxCC.Cfg.Rc.Proof.Physical.JumpResult
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarOutcomes
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ProjectionOutcomes
import IxCC.Cfg.Rc.Proof.Physical.CallResult
import IxCC.Fir.Proof.Mono

/-! Complete simulation of the actual source evaluator by the physical RC
lowering. The only recursive hypotheses are discharged by the source clock
and then the source code/join measure. No execution, heap-capacity, or
readback premise is added to the checked admission contract. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec

theorem eval_physical {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)}
    {functions : List Lir.Func}
    (admission : CodeAdmission F bodies P config pairs functions) (main clock : Nat)
    (smaller : ∀ next, next < clock → PhysicalAtClock F P config pairs main next)
    (sourceJoins : List Fir.JEntry) (code : Fir.Code) :
    PhysicalCode F P config pairs main clock sourceJoins code := by
  match code with
  | .bind x rhs cont =>
    cases rhs with
    | arg arg =>
      exact IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar.argument_result admission arg
        (eval_physical admission main clock smaller sourceJoins cont)
    | ctor ctor args =>
      by_cases zero : ctor.arity = 0
      · exact IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar.fieldless_result admission ctor args zero
          (eval_physical admission main clock smaller sourceJoins cont)
      · exact allocation_result admission.scopedProgram (by omega)
          (eval_physical admission main clock smaller sourceJoins cont)
    | proj y key i =>
      exact IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar.projection_result admission y key i
        (eval_physical admission main clock smaller sourceJoins cont)
    | prim op args =>
      exact IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar.primitive_result admission op args
        (eval_physical admission main clock smaller sourceJoins cont)
    | call f args =>
      intro H addresses external live sourceEnv ownedEnv roots joins ownedJoins sourceFunction
        function source target memory context base bump limit regionBytes slots lists callers imm
        sourceLookup before heap
      exact call_result admission main clock smaller before sourceLookup heap callers
        (eval_physical admission main clock smaller sourceJoins cont)
  | .jp j params rec body cont =>
    apply physical_declare
    intro sourceEnv
    exact eval_physical admission main clock smaller
      ({id := j, charged := false, env := sourceEnv, params, body, isRec := rec} :: sourceJoins) cont
  | .jmp j args =>
    apply jump_result admission.scopedProgram admission.consuming smaller
    intro entry rest found free
    have jumpSmaller := Fir.jump_measure found free
    exact eval_physical admission main clock smaller (entry.after rest) entry.body
  | .case x alts default =>
    apply case_result admission.scopedProgram admission.consuming admission.switches
    intro body smallerBody
    exact eval_physical admission main clock smaller sourceJoins body
  | .ret arg => exact physical_return admission arg
  | .tcall f args =>
    intro H addresses external live sourceEnv ownedEnv roots joins ownedJoins sourceFunction
      function source target memory context base bump limit regionBytes slots lists callers imm
      sourceLookup before heap
    exact tail_result admission main clock smaller before sourceLookup heap callers
  | .trap => exact physical_trap admission
termination_by code.size + Fir.jweight sourceJoins
decreasing_by
  all_goals simp_wf
  all_goals simp only [Fir.Code.size, Fir.jweight, Fir.JEntry.weight,
    Bool.false_eq_true, ↓reduceIte] at *
  all_goals omega

theorem checked_physical {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)}
    {functions : List Lir.Func}
    (admission : CodeAdmission F bodies P config pairs functions) (main : Nat) :
    ∀ clock, PhysicalAtClock F P config pairs main clock := by
  intro clock
  induction clock using Nat.strongRecOn with
  | ind clock smaller =>
    exact PhysicalAtClock.of_code (eval_physical admission main clock smaller)

/-- Successful public admission supplies the complete static contract. The
physical statement is derived here, rather than carried in that contract. -/
theorem public_physical {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {config : Rt.Config} {lowered : Public.Lowered}
    (checked : checkScopedProgram F bodies P = true)
    (accepted : Public.lower config F bodies P = .ok lowered) :
    ∃ main pairs functions,
      CodeAdmission F bodies P config pairs functions ∧
      P.base.exports.head? = some main ∧
      ∀ clock, PhysicalAtClock F P config pairs main clock := by
  obtain ⟨main, pairs, functions, admission, entry⟩ := CodeAdmission.of_public checked accepted
  exact ⟨main, pairs, functions, admission, entry, checked_physical admission main⟩




end IxCC.Cfg.Rc.Native.Spec
