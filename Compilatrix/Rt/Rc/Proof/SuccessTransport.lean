import Compilatrix.Rt.Rc.Proof.TraceTransport

namespace Compilatrix.Rt.Rc.Procs
open Lir

/-- Transport a proved standalone successful procedure run into any ambient
program and suspended caller. Its actual changed memory crosses the return;
no caller-supplied operation simulation is needed. -/
theorem local_success_transport (f : Func) (hfree : CallFree f) (P : Program) (fn : Nat)
    (hfn : P.funcs[fn]? = some f) (mem : X86.Memory) (context : Word) (frame : Frame)
    (hzero : frame.fn = 0) (caller : Frame) (callers : List Frame)
    {values : List Word} {finalMem : X86.Memory} {env : Env} {clock : Nat}
    (hr : Sem.Reaches (semStep (localProgram f)) (localState mem context frame) clock (.ok (values, finalMem)))
    (hbind : bindParams caller.env caller.dsts values = some env) :
    ∃ charges, charges ≤ clock ∧
      Sem.Star (semStep P) (ambientState mem context fn frame (caller :: callers)) charges
        { mem := finalMem, ctx := context, stack := {caller with env, dsts := []} :: callers } := by
  obtain ⟨charges, finish, hpath, hle, hfinal⟩ :=
    (Sem.Reaches.iff_final (by simp : Sem.Result.ok (values, finalMem) ≠ .timeout)).mp hr
  obtain ⟨mem', fr', hf, hz, hpath'⟩ :=
    local_star_transport f hfree P fn hfn context (caller :: callers) hpath mem frame hzero rfl
  have hdone : semStep (localProgram f) finish = .done (values, finalMem) := by
    generalize he : semStep (localProgram f) finish = outcome at hfinal
    cases hfinal
    rfl
  rw [hf] at hdone
  have hreturn := local_return_transport f P fn hfn mem' context fr' hz caller callers
    (semStep_done.mp hdone) hbind
  refine ⟨charges, hle, ?_⟩
  have hlast : Sem.Star (semStep P) (ambientState mem' context fn fr' (caller :: callers)) 0
      { mem := finalMem, ctx := context, stack := {caller with env, dsts := []} :: callers } :=
    .free (semStep_next.mpr hreturn) (.refl _)
  simpa using hpath'.trans hlast


end Compilatrix.Rt.Rc.Procs
