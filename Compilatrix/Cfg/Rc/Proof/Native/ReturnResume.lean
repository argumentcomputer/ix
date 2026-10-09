import Compilatrix.Cfg.Rc.Proof.Native.ReturnCursor

/-! Actual return-to-caller and final-return execution. These interfaces use
the RetAt receipt constructed from the consumed cursor, preserving memory
and binding precisely the selected destination in the suspended activation. -/
set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec
open Compilatrix.Cfg.Rc.Proof.Physical.Bridge Compilatrix.Rt.Rc.Procs Compilatrix.Rt.Proof

theorem return_resume {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    {source : Cfg.Frame} {caller returning : Lir.Frame} {x : Nat}
    (cursor : ConsumedCursor P pairs lp source caller) (destination : caller.dsts = [x])
    {addresses : AddressMap} {D : Nat → Prop} {bound : Nat} {sourceEnv : Own.Env}
    (registers : FusedWords addresses D bound sourceEnv caller.env) (real : x < bound)
    {value : Own.RVal} {word : Lir.Word} (represented : valueWord addresses value = some word)
    (returned : RetAt lp returning word)
    (mem : X86.Memory) (context : Lir.Word) (callers : List Lir.Frame) :
    let resumed := {caller with env := caller.env.insert x word, dsts := []}
    Lir.step lp {mem, ctx := context, stack := returning :: caller :: callers} =
      .next {mem, ctx := context, stack := resumed :: callers} false ∧
    ConsumedCursor P pairs lp {source with env := source.env.insert x value} resumed ∧
    FusedWords addresses D bound (sourceEnv.insert x value) resumed.env := by
  obtain ⟨_, function, block, operand, functionLookup, blockLookup, position, terminal, evaluated⟩ := returned
  refine ⟨?_, cursor.withEnvs (source.env.insert x value) (caller.env.insert x word) [],
    registers.bind real represented⟩
  exact Lir.step_ret_caller (vals := [word]) functionLookup blockLookup position terminal
    (by simp [Lir.evalArgs_cons, Lir.evalArgs_nil, evaluated])
    (by rw [destination]; rfl)

theorem return_final {lp : Lir.Program} {returning : Lir.Frame} {word : Lir.Word}
    (returned : RetAt lp returning word) (mem : X86.Memory) (context : Lir.Word) :
    Lir.step lp {mem, ctx := context, stack := [returning]} = .done [word] mem := by
  obtain ⟨_, function, block, operand, functionLookup, blockLookup, position, terminal, evaluated⟩ := returned
  exact Lir.step_ret_done functionLookup blockLookup position terminal
    (by simp [Lir.evalArgs_cons, Lir.evalArgs_nil, evaluated])



end Compilatrix.Cfg.Rc.Native.Spec
