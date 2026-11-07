import IxCC.Rt.Rc.Proof.AllocatorMetadata
import IxCC.Rt.Rc.Proof.ProtectedOps
import IxCC.Rt.Rc.Proof.IncrementEntry
import IxCC.Rt.Rc.Proof.FrameReleaseCaller

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Own IxCC.Own.Rc

theorem AllocatorReady.increment_ready
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady heap addresses mem external context base bump limit slots lists)
    {location refs body address} (hc : heap.cell? location = some (.live refs .dyn body))
    (ha : addresses location = some address) (hroom : refs < maxCount) :
    Own.Rc.inc heap (.loc location) 1 = some (setCell heap location (.live (refs+1) .dyn body)) ∧
    AllocatorReady (setCell heap location (.live (refs+1) .dyn body)) addresses
      (storeCount mem address (UInt64.ofNat refs))
      (fun k => external k + refsIn k [.loc location]) context base bump limit slots lists ∧
    eval incProgram 0 [address] mem context = .ok ([], storeCount mem address (UInt64.ofNat refs)) := by
  obtain ⟨source, idle, result⟩ := increment_entry_complete h.idle hc ha hroom
  exact ⟨source, h.after_protected (h.idle.count_protected hc ha _) idle, result⟩

theorem AllocatorReady.release_caller_ready
    {heap addresses mem external value context base bump limit slots lists}
    (h : AllocatorReady heap addresses mem
      (fun location => external location + refsIn location [value])
      context base bump limit slots lists)
    (word : Word) (hw : valueWord addresses value = some word)
    (P : Program) (fn : Nat) (hfn : P.funcs[fn]? = some dec)
    (caller : Frame) (callers : List Frame) (hdsts : caller.dsts = []) :
    ∃ heap' mem' slots' lists' charges,
      dropAll heap [value] = some heap' ∧
      AllocatorReady heap' addresses mem' external context base bump limit slots' lists' ∧
      Sem.Star (semStep P)
        { mem, ctx := context, stack := { fn, label := 0, pos := 0, env := decEnv word } :: caller :: callers }
        charges { mem := mem', ctx := context, stack := caller :: callers } := by
  obtain ⟨heap', mem', slots', lists', charges, source, idle, trace, frame⟩ :=
    release_caller_complete_frame h.idle word hw P fn hfn caller callers hdsts
  exact ⟨heap', mem', slots', lists', charges, source, h.after_protected frame idle, trace⟩



end IxCC.Rt.Rc.Procs
