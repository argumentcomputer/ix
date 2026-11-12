import IxCC.Cfg.Rc.Proof.Native.SimpleOutcomes
import IxCC.Cfg.Rc.Proof.Owned.Actions
import IxCC.Cfg.Rc.Proof.Physical.AllocationResult
import IxCC.Cfg.Rc.Proof.Physical.CaseResult
import IxCC.Cfg.Rc.Proof.Physical.JumpResult
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarOutcomes
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ProjectionOutcomes
import IxCC.Cfg.Rc.Proof.Physical.CallResult
import IxCC.Cfg.Rc.Proof.Physical.TailResult
import IxCC.Fir.Proof.Mono

/-! Complete simulation of the actual source evaluator by the physical RC lowering, by induction
on the **Own** code the certificate carries (heap stage 2): any placement of `inc`/`dec` the
ownership checker accepted. The source side runs the code's erasure, so an `inc` or `dec` is a
source stutter, decided by the Own code's size; every other construct decreases the source
measure (the code's size plus the join stack's weight); a call or a charged jump uses the claim at
a smaller source clock. No execution, heap-capacity, or readback premise is added to the checked
admission contract. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar

section
variable {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
  {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
  {main clock : Nat} {sourceJoins : List Fir.JEntry}

/-- A binding, by its right-hand side. -/
theorem bind_result (admission : CodeAdmission F bodies P config pairs functions)
    (smaller : ∀ k, k < clock → PhysicalAtClock F P config pairs main k)
    {x : Fir.Var} {rhs : Fir.Rhs} {k : Own.Plain.Code}
    (next : PhysicalCode F P config pairs main clock sourceJoins k) :
    PhysicalCode F P config pairs main clock sourceJoins (.bind x rhs k) := by
  cases rhs with
  | arg arg => exact argument_result admission arg next
  | ctor ctor args =>
    by_cases zero : ctor.arity = 0
    · exact fieldless_result admission ctor args zero next
    · exact allocation_result admission (by omega) next
  | proj y key i => exact projection_result admission y key i next
  | prim op args => exact primitive_result admission op args next
  | call f args => exact call_result admission smaller next

end

/-- **The physical simulation's induction over the typing context.** -/
theorem eval_physical {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)}
    {functions : List Lir.Func}
    (admission : CodeAdmission F bodies P config pairs functions) (main clock : Nat)
    (smaller : ∀ next, next < clock → PhysicalAtClock F P config pairs main next)
    (sourceJoins : List Fir.JEntry) (code : Own.Plain.Code) :
    PhysicalCode F P config pairs main clock sourceJoins code := by
  match code with
  | .act (.inc x n) k =>
    exact physical_inc admission (eval_physical admission main clock smaller sourceJoins k)
  | .act (.dec x) k =>
    exact physical_dec admission (eval_physical admission main clock smaller sourceJoins k)
  | .bind x rhs k =>
    exact bind_result admission smaller
      (eval_physical admission main clock smaller sourceJoins k)
  | .jp j params captured rec body cont =>
    apply physical_declare
    intro sourceEnv
    exact eval_physical admission main clock smaller
      ({id := j, charged := false, env := sourceEnv, params, body := Own.Plain.eraseCode body,
        isRec := rec} :: sourceJoins) cont
  | .jmp j args =>
    apply jump_result admission smaller
    intro entry rest found free body erased
    have := Fir.jump_measure found free
    exact eval_physical admission main clock smaller (entry.after rest) body
  | .case x alts dflt =>
    apply case_result admission
    intro body smallerBody
    exact eval_physical admission main clock smaller sourceJoins body
  | .ret arg => exact physical_return admission arg
  | .tcall f args => exact tail_result admission smaller
  | .trap => exact physical_trap admission
termination_by ((Own.Plain.eraseCode code).size + Fir.jweight sourceJoins, sizeOf code)
decreasing_by
  all_goals simp_wf
  all_goals rw [Prod.lex_def]
  all_goals first
    | (right; refine ⟨rfl, ?_⟩; simp; omega)
    | (left; rw [erased]; simp only [Own.Plain.eraseCode, Fir.Code.size] at *; omega)
    | (left; simp only [Own.Plain.eraseCode, Fir.Code.size, Fir.jweight, Fir.JEntry.weight,
        Bool.false_eq_true, ↓reduceIte] at *; omega)

/-- **The physical simulation over the typing context**, at every clock. -/
theorem checked_physical {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)}
    {functions : List Lir.Func}
    (admission : CodeAdmission F bodies P config pairs functions) (main : Nat) :
    ∀ clock, PhysicalAtClock F P config pairs main clock := by
  intro clock
  induction clock using Nat.strongRecOn with
  | ind clock smaller =>
    exact eval_physical admission main clock smaller


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
