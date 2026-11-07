import IxCC.Recheck.Rc.Proof.Exports
import IxCC.Recheck.Rc.Linked
import IxCC.Backend.Proof.Exports
import IxCC.Backend.Proof.Driver

set_option autoImplicit false
namespace IxCC.Recheck.RcReplay
open IxCC.Xv.Stacking.Proof

/-- The actual emitted drop export takes the owned machine word unchanged.
Its only caller premise is the existing backend entry contract; unlike a
numeric root, it has no Nat-range premise on that word. -/
theorem drop_sim_linked {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact}
    (accepted : run cfg P c = .ok a) {driver : X86.Driver}
    (driverOk : driver.Ok a.backend.encoded.text.size)
    {word : Lir.Word} {bytes : Lir.Word → UInt8} {memory : X86.Memory}
    (entry : EntryBase (driver.core [word] bytes) driver.ret memory driver.ctx) :
    Sem.Sim (X86.ObjectEval.Lifted Backend.StackFinal)
      (fun clock => (a.backend.stacked.program.blocks.size + 1) * (clock + 1))
      (fun clock => Lir.eval {a.front.lowered.program with main := a.front.drop}
        clock [word] memory driver.ctx)
      (X86.ObjectEval.call a.backend.object "cx_drop" driver.base
        (driver.core [word] bytes) driver.flags) := by
  obtain ⟨_, xv, xl, selected, validated, emitted, apart⟩ := run_parts accepted
  obtain ⟨function, lookup, convention, _, reps⟩ := run_drop accepted selected validated
  let config := emittedConfig cfg a.front c.base
  have validated' : Xv.Validate.run config.env xv c.base.alloc = .ok xl := validated
  have representation : mainReps {xl with main := a.front.drop} config.reps = [.word] := by
    simp only [mainReps, lookup, Xv.Stacking.exportReps,
      show config.reps a.front.drop = some [.word] from reps, Option.getD_some]
  have inv : EntryInv {xl with main := a.front.drop} config.reps
      (driver.core [word] bytes) driver.ret [word] memory driver.ctx :=
    { toEntryBase := entry
      args := by rw [representation]; rfl
      fit := by
        rw [representation]
        simp [ArgsFit, Xv.Stacking.sysvArgs] }
  exact Backend.call_sim_export selected validated' emitted apart lookup convention
    [word] memory driver.ctx (driver.core [word] bytes) driver.base driver.ret
    driver.flags inv driverOk.retOut


end IxCC.Recheck.RcReplay
