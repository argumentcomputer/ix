import IxCC.Cfg.Rc.Proof.Native.Outcome
import IxCC.Fir.Proof.Unfold

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs

variable {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
  (checked : checkScopedProgram F bodies P = true)
  {pairs : List (Nat × Cfg.Fun)} (consuming : consumeAll P = .ok pairs)
  (functions : Nat → Lir.Func) (main : Nat)
  {H : Own.Heap} {addresses : AddressMap} {external : Nat → Nat} {roots : List Own.RVal}
  {live imm : List Fir.Var} {sourceEnv : Fir.Env} {ownedEnv : Own.Env}
  {joins : Own.Plain.Joins} {sourceJoins : List Fir.JEntry} {ownedJoins : List Own.Plain.JEntry}
  {sourceFunction : Fir.Fun} {function : Cfg.Fun} {source : Cfg.Frame} {target : Lir.Frame}
  {memory : X86.Memory} {context base bump limit : Lir.Word} {regionBytes : Nat}
  {slots : List Slot} {lists : Nat → List Lir.Word}

include checked consuming

theorem Activation.return_result {arg : Fir.Arg}
    (before : Activation F P pairs (Public.Spec.sourceStage P functions main) H addresses external
      live sourceEnv ownedEnv roots joins sourceJoins ownedJoins (.ret arg)
      sourceFunction.vars function source target imm)
    (sourceLookup : F.fun? source.fn = some sourceFunction)
    (heap : HeapState P pairs H addresses memory external roots
      context base bump limit regionBytes slots lists)
    (clock : Nat) (callers : List Lir.Frame) :
    ResultAt P pairs (Public.Spec.sourceStage P functions main) H addresses external context base limit
      regionBytes clock {mem := memory, ctx := context, stack := target :: callers} callers
      (Fir.eval F clock sourceEnv sourceJoins (.ret arg)) := by
  rcases before.return_value checked consuming functions main sourceLookup heap callers with success | failure
  · obtain ⟨value, logical, afterMemory, afterHeap, afterSlots, afterLists, final, cost, word,
      ownValue, sourceValue, den, balance, afterState, trace, ret, represented, bounded,
      compatible, preserved, history⟩ := success
    simp only [Fir.eval_ret, sourceValue, Sem.Result.ofOption]
    let returned : Returned P pairs (Public.Spec.sourceStage P functions main) H addresses external
        context base limit regionBytes logical := {
      heap := afterHeap
      addresses := addresses
      memory := afterMemory
      bump := bump
      slots := afterSlots
      lists := afterLists
      frame := final
      value := value
      word := word
      den := den
      balance := balance
      state := afterState
      terminator := ret
      represented := represented
      bounded := bounded
      compatible := compatible
      preserved := preserved
      history := history }
    exact .inl ⟨returned, cost, trace⟩
  · exact ResultAt.of_fails failure

theorem Activation.trap_result
    (before : Activation F P pairs (Public.Spec.sourceStage P functions main) H addresses external
      live sourceEnv ownedEnv roots joins sourceJoins ownedJoins .trap
      sourceFunction.vars function source target imm)
    (sourceLookup : F.fun? source.fn = some sourceFunction)
    (heap : HeapState P pairs H addresses memory external roots
      context base bump limit regionBytes slots lists)
    (clock : Nat) (callers : List Lir.Frame) :
    ResultAt P pairs (Public.Spec.sourceStage P functions main) H addresses external context base limit
      regionBytes clock {mem := memory, ctx := context, stack := target :: callers} callers
      (Fir.eval F clock sourceEnv sourceJoins .trap) := by
  rw [Fir.eval_trap]
  rcases before.trap checked consuming functions main sourceLookup heap callers with success | failure
  · obtain ⟨afterMemory, final, cost, trace, trapped⟩ := success
    exact .inl ⟨cost, _, trace, trapped⟩
  · exact .inr failure



end IxCC.Cfg.Rc.Native.Spec
