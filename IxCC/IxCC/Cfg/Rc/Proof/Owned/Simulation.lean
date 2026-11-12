import IxCC.Cfg.Rc.Proof.Owned.Actions
import IxCC.Cfg.Rc.Proof.Owned.Terminals
import IxCC.Cfg.Rc.Proof.Owned.Declare
import IxCC.Cfg.Rc.Proof.Owned.Jump
import IxCC.Cfg.Rc.Proof.Owned.Case
import IxCC.Cfg.Rc.Proof.Owned.Argument
import IxCC.Cfg.Rc.Proof.Owned.Scalars
import IxCC.Cfg.Rc.Proof.Owned.Projection
import IxCC.Cfg.Rc.Proof.Owned.Allocation
import IxCC.Cfg.Rc.Proof.Owned.Call
import IxCC.Cfg.Rc.Proof.Owned.Tail
import IxCC.Fir.Proof.Mono

/-! # The physical simulation over the typing context (heap stage 2)

The induction on the **Own** code: the source side runs its erasure, so an `inc` or `dec` is a
source stutter, decided by the Own code's size; every other construct decreases the source
measure (the code's size plus the join stack's weight), and a call or a charged jump uses the
claim at a smaller source clock. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec

section
variable {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
  {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
  {main clock : Nat} {sourceJoins : List Fir.JEntry}

/-- A binding, by its right-hand side. -/
theorem bind_result_owned (admission : CodeAdmission F bodies P config pairs functions)
    (smaller : ∀ k, k < clock → PhysicalAtClockOwned F P config pairs main k)
    {x : Fir.Var} {rhs : Fir.Rhs} {k : Own.Plain.Code}
    (next : PhysicalCodeOwned F P config pairs main clock sourceJoins k) :
    PhysicalCodeOwned F P config pairs main clock sourceJoins (.bind x rhs k) := by
  cases rhs with
  | arg arg => exact argument_result_owned admission arg next
  | ctor ctor args =>
    by_cases zero : ctor.arity = 0
    · exact fieldless_result_owned admission ctor args zero next
    · exact allocation_result_owned admission (by omega) next
  | proj y key i => exact projection_result_owned admission y key i next
  | prim op args => exact primitive_result_owned admission op args next
  | call f args => exact call_result_owned admission smaller next

end

/-- **The physical simulation's induction over the typing context.** -/
theorem eval_physical_owned {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)}
    {functions : List Lir.Func}
    (admission : CodeAdmission F bodies P config pairs functions) (main clock : Nat)
    (smaller : ∀ next, next < clock → PhysicalAtClockOwned F P config pairs main next)
    (sourceJoins : List Fir.JEntry) (code : Own.Plain.Code) :
    PhysicalCodeOwned F P config pairs main clock sourceJoins code := by
  match code with
  | .act (.inc x n) k =>
    exact physical_inc admission (eval_physical_owned admission main clock smaller sourceJoins k)
  | .act (.dec x) k =>
    exact physical_dec admission (eval_physical_owned admission main clock smaller sourceJoins k)
  | .bind x rhs k =>
    exact bind_result_owned admission smaller
      (eval_physical_owned admission main clock smaller sourceJoins k)
  | .jp j params captured rec body cont =>
    apply physical_declare_owned
    intro sourceEnv
    exact eval_physical_owned admission main clock smaller
      ({id := j, charged := false, env := sourceEnv, params, body := Own.Plain.eraseCode body,
        isRec := rec} :: sourceJoins) cont
  | .jmp j args =>
    apply jump_result_owned admission smaller
    intro entry rest found free body erased
    have := Fir.jump_measure found free
    exact eval_physical_owned admission main clock smaller (entry.after rest) body
  | .case x alts dflt =>
    apply case_result_owned admission
    intro body smallerBody
    exact eval_physical_owned admission main clock smaller sourceJoins body
  | .ret arg => exact physical_return_owned admission arg
  | .tcall f args => exact tail_result_owned admission smaller
  | .trap => exact physical_trap_owned admission
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
theorem checked_physical_owned {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)}
    {functions : List Lir.Func}
    (admission : CodeAdmission F bodies P config pairs functions) (main : Nat) :
    ∀ clock, PhysicalAtClockOwned F P config pairs main clock := by
  intro clock
  induction clock using Nat.strongRecOn with
  | ind clock smaller =>
    exact eval_physical_owned admission main clock smaller

end IxCC.Cfg.Rc.Native.Spec
