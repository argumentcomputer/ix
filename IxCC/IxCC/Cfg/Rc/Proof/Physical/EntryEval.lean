import IxCC.Cfg.Rc.Proof.Physical.ResultEval
import IxCC.Cfg.Rc.Proof.Physical.PublicEval
import IxCC.Cfg.Rc.Proof.Physical.EntryResult
import IxCC.Cfg.Rc.Proof.Native.PhysicalSimulation

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs

variable {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
  {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
  {main : Nat} {sourceFunction : Fir.Fun}
  {H : Own.Heap} {addresses : AddressMap} {external : Nat → Nat}
  {values : List Own.RVal} {logical : List Fir.Val} {words : List Lir.Word}
  {memory : X86.Memory} {context base bump limit : Lir.Word} {regionBytes : Nat}
  {slots : List Slot} {lists : Nat → List Lir.Word}

/-- All source clocks are discharged by the checked whole-code induction.
Only concrete initial values, physical heap, and accepted entry remain. -/
theorem entry_eval_sim
    (admission : CodeAdmission F bodies P config pairs functions)
    (sourceLookup : F.fun? main = some sourceFunction)
    (den : Sem.Forall2 (Own.Proof.Den H) values logical) (balance : Own.Rc.Balance H external values)
    (represented : Rt.Proof.ListRel (fun value word => valueWord addresses value = some word) values words)
    (compatible : ∀ value ∈ values, ValueCtorOk (tablesOf P pairs) value)
    (arity : values.length = sourceFunction.params.length)
    (heap : HeapState P pairs H addresses memory external values context base bump limit regionBytes slots lists) :
    let lp := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main
    Sem.Sim (ReturnedOutput P pairs lp H addresses external context base limit regionBytes)
      Nat.succ (fun clock => Fir.run F clock main logical)
      (fun clock => Lir.eval lp clock words memory context) := by
  dsimp only
  apply resultAt_eval_sim_succ
  · have sourceArity : logical.length = sourceFunction.params.length := den.length.symm.trans arity
    rw [Fir.run_eq, Fir.evalCall_of F 0 sourceLookup, Fir.callFun, if_pos sourceArity]
    rfl
  · intro clock
    obtain ⟨callee, initialized, execution⟩ := main_entry_result admission
      (checked_physical admission main clock) sourceLookup den balance represented compatible arity heap
    exact ⟨_, initialized, execution⟩

/-- Behavioral refinement includes divergence, traps, and resource failure;
successful output retains the complete physical return witness. -/
theorem entry_eval_refines
    (admission : CodeAdmission F bodies P config pairs functions)
    (sourceLookup : F.fun? main = some sourceFunction)
    (den : Sem.Forall2 (Own.Proof.Den H) values logical) (balance : Own.Rc.Balance H external values)
    (represented : Rt.Proof.ListRel (fun value word => valueWord addresses value = some word) values words)
    (compatible : ∀ value ∈ values, ValueCtorOk (tablesOf P pairs) value)
    (arity : values.length = sourceFunction.params.length)
    (heap : HeapState P pairs H addresses memory external values context base bump limit regionBytes slots lists) :
    let lp := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main
    Sem.Behaviour.Refines (ReturnedOutput P pairs lp H addresses external context base limit regionBytes)
      (Sem.behaviour (fun clock => Fir.run F clock main logical))
      (Sem.behaviour (fun clock => Lir.eval lp clock words memory context)) :=
  Sem.Sim.refines (Fir.run_mono F main logical) (Lir.eval_mono _ words memory context)
    (entry_eval_sim admission sourceLookup den balance represented compatible arity heap)



end IxCC.Cfg.Rc.Native.Spec
