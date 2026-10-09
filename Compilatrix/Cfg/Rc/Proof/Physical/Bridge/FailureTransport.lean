import Compilatrix.Rt.Rc.Proof.TraceTransport

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix Compilatrix.Lir Compilatrix.Rt.Rc.Procs

/-- Resource failure is terminal even above suspended callers. It is not
reinterpreted as a successful return or as permission to assume count room. -/
theorem local_fail_transport (f : Func) (free : CallFree f) (P : Program) (fn : Nat)
    (function : P.funcs[fn]? = some f) (mem : X86.Memory) (context : Word)
    (frame : Frame) (zero : frame.fn = 0) (callers : List Frame) (resource : Sem.Resource)
    (failure : step (localProgram f) (localState mem context frame) = .fail resource) :
    step P (ambientState mem context fn frame callers) = .fail resource := by
  have localLookup : (localProgram f).funcs[frame.fn]? = some f := by simp [localProgram, zero]
  simp only [step, localState, ambientState, localLookup, function] at failure ⊢
  cases lookup : f.blocks[frame.label]? with
  | none => simp [lookup] at failure
  | some block =>
    simp only [lookup] at failure ⊢
    have member : block ∈ f.blocks := Array.mem_of_getElem? lookup
    by_cases position : frame.pos < block.body.size
    · simp only [dif_pos position] at failure ⊢
      have instructionMember : block.body[frame.pos] ∈ block.body := Array.getElem_mem position
      cases instruction : block.body[frame.pos] with
      | call dsts callee args =>
        exact False.elim (free.1 block member _ instructionMember dsts callee args instruction)
      | assign x rhs =>
        simp only [instruction] at failure
        cases result : (Stmt.assign x rhs).exec frame.env mem context <;> simp [result] at failure
      | store width address value =>
        simp only [instruction] at failure
        cases result : (Stmt.store width address value).exec frame.env mem context <;> simp [result] at failure
    · simp only [dif_neg position] at failure ⊢
      have edgeCannotFail (env : Env) (edge : Edge) :
          takeEdge f (localState mem context frame) frame [] env edge ≠ .fail resource := by
        unfold takeEdge
        cases evalArgs env edge.args <;> cases f.blocks[edge.target]? <;> simp
        split <;> simp
      cases terminal : block.term with
      | jump edge => exact False.elim (edgeCannotFail _ _ (by simpa only [terminal, localState] using failure))
      | br cond width a b yes no =>
        simp only [terminal] at failure
        cases ha : a.eval frame.env <;> cases hb : b.eval frame.env <;> simp only [ha, hb] at failure
        all_goals first | cases failure | exact False.elim (edgeCannotFail _ _ failure)
      | brOvf op x a b yes no =>
        simp only [terminal] at failure
        cases ha : a.eval frame.env <;> cases hb : b.eval frame.env <;> simp only [ha, hb] at failure
        all_goals first | cases failure | exact False.elim (edgeCannotFail _ _ failure)
      | ret args =>
        simp only [terminal] at failure
        cases values : evalArgs frame.env args <;> simp [values] at failure
      | tail callee args =>
        exact False.elim (free.2 block member callee args terminal)
      | fail reason => simpa only [terminal] using failure
      | trap => simp [terminal] at failure

theorem local_resource_transport (f : Func) (free : CallFree f) (P : Program) (fn : Nat)
    (function : P.funcs[fn]? = some f) (mem : X86.Memory) (context : Word)
    (frame : Frame) (zero : frame.fn = 0) (callers : List Frame)
    {clock : Nat} {resource : Sem.Resource}
    (reaches : Sem.Reaches (semStep (localProgram f)) (localState mem context frame)
      clock (.resource resource)) :
    Sem.Reaches (semStep P) (ambientState mem context fn frame callers) clock (.resource resource) := by
  obtain ⟨charges, finish, path, bounded, final⟩ :=
    (Sem.Reaches.iff_final (by simp : (Sem.Result.resource resource : Sem.Result (List Word × X86.Memory)) ≠ .timeout)).mp reaches
  obtain ⟨mem', next, finishEq, nextZero, ambientPath⟩ :=
    local_star_transport f free P fn function context callers path mem frame zero rfl
  have failed : semStep (localProgram f) finish = .fail resource := by
    generalize equation : semStep (localProgram f) finish = outcome at final
    cases final
    rfl
  rw [finishEq] at failed
  have terminal := local_fail_transport f free P fn function mem' context next nextZero callers
    resource (semStep_fail.mp failed)
  apply (Sem.Reaches.iff_final (by simp : (Sem.Result.resource resource : Sem.Result (List Word × X86.Memory)) ≠ .timeout)).mpr
  exact ⟨charges, _, ambientPath, bounded, semStep_fail.mpr terminal ▸ .fail⟩



end Compilatrix.Cfg.Rc.Proof.Physical.Bridge
