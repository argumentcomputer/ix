import Compilatrix.Cfg.Rc.Proof.Native.CodeRecursion

/-! The terminal and zero-step declaration cases of the physical source
induction. All source environments and concrete native states remain
universally quantified by PhysicalCode. -/
set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec
open Compilatrix.Rt.Rc.Procs

variable {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
  {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
  {main clock : Nat} {sourceJoins : List Fir.JEntry}

theorem physical_return (admission : CodeAdmission F bodies P config pairs functions)
    (arg : Fir.Arg) :
    PhysicalCode F P config pairs main clock sourceJoins (.ret arg) := by
  intro H addresses external live sourceEnv ownedEnv roots joins ownedJoins sourceFunction
    function source target memory context base bump limit regionBytes slots lists callers
    sourceLookup before heap
  exact before.return_result admission.scopedProgram admission.consuming
    (Public.Spec.rawSource config P pairs) main sourceLookup heap clock callers

theorem physical_trap (admission : CodeAdmission F bodies P config pairs functions) :
    PhysicalCode F P config pairs main clock sourceJoins .trap := by
  intro H addresses external live sourceEnv ownedEnv roots joins ownedJoins sourceFunction
    function source target memory context base bump limit regionBytes slots lists callers
    sourceLookup before heap
  exact before.trap_result admission.scopedProgram admission.consuming
    (Public.Spec.rawSource config P pairs) main sourceLookup heap clock callers

theorem physical_declare {j : Fir.JoinId} {params : List Fir.Var} {rec : Bool}
    {body cont : Fir.Code}
    (next : ∀ sourceEnv : Fir.Env,
      PhysicalCode F P config pairs main clock
        ({id := j, charged := false, env := sourceEnv, params, body, isRec := rec} :: sourceJoins)
        cont) :
    PhysicalCode F P config pairs main clock sourceJoins (.jp j params rec body cont) := by
  intro H addresses external live sourceEnv ownedEnv roots joins ownedJoins sourceFunction
    function source target memory context base bump limit regionBytes slots lists callers
    sourceLookup before heap
  rw [Fir.eval_jp]
  exact next sourceEnv H addresses external live sourceEnv ownedEnv roots ((j, live) :: joins)
    _ sourceFunction function source target memory context base bump limit regionBytes slots lists
    callers sourceLookup before.declare heap




end Compilatrix.Cfg.Rc.Native.Spec
