import Compilatrix.Cfg.Rc.Proof.Physical.EntryEval
import Compilatrix.Cfg.Rc.Proof.Physical.PublicRoot

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec
open Compilatrix.Cfg.Rc.Proof.Physical.Bridge Compilatrix.Rt.Rc.Procs

variable {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
  {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
  {lowered : Public.Lowered} {root : Nat} {sourceFunction : Fir.Fun}
  {H : Own.Heap} {addresses : AddressMap} {external : Nat → Nat}
  {values : List Own.RVal} {logical : List Fir.Val} {words : List Lir.Word}
  {memory : X86.Memory} {context base bump limit : Lir.Word} {regionBytes : Nat}
  {slots : List Slot} {lists : Nat → List Lir.Word}

/-- Concrete initialized entry through the accepted public program, at any
selected root. Both the whole-code proof and every layout transport are
discharged; successful evaluation keeps its physical return witness. -/
theorem public_entry_eval_sim
    (admission : CodeAdmission F bodies P config pairs functions)
    (accepted : Public.lower config F bodies P = .ok lowered)
    (sourceLookup : F.fun? root = some sourceFunction)
    (den : Sem.Forall2 (Own.Proof.Den H) values logical) (balance : Own.Rc.Balance H external values)
    (represented : Rt.Proof.ListRel (fun value word => valueWord addresses value = some word) values words)
    (compatible : ∀ value ∈ values, ValueCtorOk (tablesOf P pairs) value)
    (arity : values.length = sourceFunction.params.length)
    (heap : HeapState P pairs H addresses memory external values context base bump limit regionBytes slots lists) :
    let raw := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) root
    Sem.Sim (ReturnedOutput P pairs raw H addresses external context base limit regionBytes)
      Nat.succ (fun clock => Fir.run F clock root logical)
      (fun clock => Lir.eval {lowered.runtime.program with main := root} clock words memory context) :=
  eval_transfer_sim (fun clock => admitted_root_eval_stages admission accepted root clock words memory context)
    (entry_eval_sim admission sourceLookup den balance represented compatible arity heap)

theorem public_entry_eval_refines
    (admission : CodeAdmission F bodies P config pairs functions)
    (accepted : Public.lower config F bodies P = .ok lowered)
    (sourceLookup : F.fun? root = some sourceFunction)
    (den : Sem.Forall2 (Own.Proof.Den H) values logical) (balance : Own.Rc.Balance H external values)
    (represented : Rt.Proof.ListRel (fun value word => valueWord addresses value = some word) values words)
    (compatible : ∀ value ∈ values, ValueCtorOk (tablesOf P pairs) value)
    (arity : values.length = sourceFunction.params.length)
    (heap : HeapState P pairs H addresses memory external values context base bump limit regionBytes slots lists) :
    let raw := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) root
    Sem.Behaviour.Refines (ReturnedOutput P pairs raw H addresses external context base limit regionBytes)
      (Sem.behaviour (fun clock => Fir.run F clock root logical))
      (Sem.behaviour (fun clock => Lir.eval {lowered.runtime.program with main := root} clock words memory context)) :=
  Sem.Sim.refines (Fir.run_mono F root logical) (Lir.eval_mono _ words memory context)
    (public_entry_eval_sim admission accepted sourceLookup den balance represented compatible arity heap)



end Compilatrix.Cfg.Rc.Native.Spec
