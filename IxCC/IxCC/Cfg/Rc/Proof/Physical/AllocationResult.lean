import IxCC.Cfg.Rc.Proof.Physical.AllocationActivation
import IxCC.Cfg.Rc.Proof.Native.CodeRecursion

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs IxCC.Own.Rc

theorem allocation_result {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true)
    {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {main clock : Nat}
    {sourceJoins : List Fir.JEntry} {x : Fir.Var} {ctor : Fir.CtorInfo}
    {args : List Fir.Arg} {cont : Fir.Code} (positive : 0 < ctor.arity)
    (next : PhysicalCode F P config pairs main clock sourceJoins cont) :
    PhysicalCode F P config pairs main clock sourceJoins (.bind x (.ctor ctor args) cont) := by
  intro H addresses external live sourceEnv ownedEnv roots joins ownedJoins sourceFunction
    function source target memory context base bump limit regionBytes slots lists callers imm
    sourceLookup before heap
  have empty : holdRoots external [] = external := by funext location; simp [holdRoots, refsIn]
  have framed : Activation F P pairs (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
      H addresses (holdRoots external []) live sourceEnv ownedEnv roots joins sourceJoins ownedJoins
      (.bind x (.ctor ctor args) cont) sourceFunction.vars function source target imm := by
    simpa only [empty] using before
  have initial : HeapState P pairs H addresses memory external (roots ++ [])
      context base bump limit regionBytes slots lists := by simpa only [List.append_nil] using heap
  rcases allocation_activation checked (Public.Spec.rawSource config P pairs) main framed sourceLookup
      positive initial callers with success | failure
  · obtain ⟨fields, logical, copied, address, bump', memory', slots', lists', after, final,
      ownedArgs, sourceArgs, copies, effect, activation, heapAfter, trace, size, sameFn, preserved⟩ := success
    simp only [empty, List.append_nil] at activation heapAfter
    have arityArgs : args.length = ctor.arity := by
      have facts := before.scope
      simp only [Own.Plain.scopeOk, Own.Plain.rhsIn, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at facts
      exact facts.2.1
    have arity : logical.length = ctor.arity := (Fir.evalArgs_length sourceEnv sourceArgs).trans arityArgs
    rw [Fir.eval_bind_ctor, Fir.evalRhs_ctor, sourceArgs]
    simp only [Sem.Result.ofOption, Sem.Result.bind_ok, if_pos arity]
    have history : HeapHistory H.size addresses (copied.alloc .rc {ctor, fields}).2.size
        (placeFresh addresses copied.size address) := by
      simpa only [size] using HeapHistory.allocate copied {ctor, fields} addresses address
    exact ResultAt.prefix trace (fun value logical _ den => preserved value logical den) history
      (by omega) (next _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ callers
        (by simpa only [sameFn] using sourceLookup) activation heapAfter)
  · exact ResultAt.of_fails failure


end IxCC.Cfg.Rc.Native.Spec
