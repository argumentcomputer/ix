import IxCC.Rt.Rc.Gen.Proof.AllocFree
import IxCC.Rt.Rc.Gen.Proof.Scanned
import IxCC.Rt.Rc.Proof.SuccessTransport

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Lir
open IxCC.Rt IxCC.Rt.Rc IxCC.Rt.Rc.Procs

theorem allocator_call_free (fields tag : Nat) : CallFree (Gen.alloc (CellLayout.ofFields fields tag)) := by
  unfold Gen.alloc
  split
  · simp [CallFree, Gen.declined]
  · split <;> simp [CallFree, Gen.allocFunc, Gen.declined]

/-- Transport the proved concrete allocator run to the publishing wrapper's
one-result continuation. Free/bump corollaries discharge the execution premise
from actual loads, bounds and byte write permissions. -/
theorem allocator_caller {fields tag : Nat} (positive : 0 < fields) (small : fields ≤ maxFields)
    (tagBound : tag ≤ maxTag) {mem after : X86.Memory} {context address : Word}
    (execution : Lir.eval (Gen.allocProgram (CellLayout.ofFields fields tag)) 0 [] mem context = .ok ([address], after))
    {P : Lir.Program} {procedure destination : Nat}
    (function : P.funcs[procedure]? = some (Gen.alloc (CellLayout.ofFields fields tag)))
    (caller : Lir.Frame) (callers : List Lir.Frame) (dest : caller.dsts = [destination]) :
    Sem.Star (Lir.semStep P)
      {mem, ctx := context, stack := {fn := procedure, label := 0, pos := 0, env := {}} :: caller :: callers} 0
      {mem := after, ctx := context,
        stack := {caller with env := caller.env.insert destination address, dsts := []} :: callers} := by
  have reaches := (Lir.runs_eval (Gen.alloc_free_initial mem context _ _
    (Gen.ofFields_layout positive small tagBound).1 (Gen.ofFields_layout (tag := tag) positive small tagBound).2)) 0
  dsimp only at reaches
  rw [execution] at reaches
  let frame : Lir.Frame := {fn := 0, label := 0, pos := 0, env := {}}
  have localRun : Sem.Reaches (Lir.semStep (localProgram (Gen.alloc (CellLayout.ofFields fields tag))))
      (localState mem context frame) 0 (.ok ([address], after)) := by
    simpa only [localProgram, Gen.allocProgram, localState, allocState, frame] using reaches
  obtain ⟨charges, bound, trace⟩ := local_success_transport (Gen.alloc (CellLayout.ofFields fields tag))
    (allocator_call_free fields tag) P procedure function mem context frame rfl caller callers
    (env := caller.env.insert destination address) localRun (by simp [dest, Lir.bindParams])
  have zero : charges = 0 := by omega
  subst charges
  simpa only [ambientState, frame] using trace


end IxCC.Cfg.Rc.Native
