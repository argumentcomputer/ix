import Compilatrix.Cfg.Rc.Proof.Native.Outcome
import Compilatrix.Own.Plain.Proof.Frames

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec
open Compilatrix.Cfg.Rc.Proof.Physical.Bridge Compilatrix.Own Compilatrix.Own.Rc
open Compilatrix.Rt.Rc.Procs

/-- Rejoin an actual returned callee with the suspended caller produced by
the call boundary. Source roots, saved joins, stale registers, and the native
return instruction are restored from concrete receipts after arbitrary
callee heap growth; no execution of the caller continuation is assumed. -/
theorem resume_activation {F : Fir.Program} {P : Program} {pairs : List (Nat × Cfg.Fun)}
    {lp : Lir.Program} {H copied : Heap} {addresses : AddressMap}
    {external : Nat → Nat} {held roots : List RVal} {live : List Fir.Var}
    {ρf : Fir.Env} {ρo : Own.Env} {joins : Own.Plain.Joins}
    {Jf : List Fir.JEntry} {Jo : List Own.Plain.JEntry}
    (before : Own.Plain.State (Own.Plain.signatures F) H (holdRoots external held)
      live ρf ρo roots joins Jf Jo)
    (copiedSize : copied.size = H.size)
    (copies : ∀ value, H.value? value = copied.value? value)
    {bound : Nat} {function : Cfg.Fun} {source : Cfg.Frame} {saved : Lir.Frame}
    (frame : FrameState P pairs lp addresses copied.size bound function source saved)
    {x : Nat} {cont : Fir.Code} (destination : saved.dsts = [x]) (real : x < bound)
    (layout : ∀ value, At F P {source with env := source.env.insert x value}
      (ρo.insert x value) Jo (Own.Plain.lowerCode (live ++ [x]) joins cont))
    (fused : ∀ value block, function.blocks[source.blk]? = some block →
      Rt.Proof.FusedDone (tablesOf P pairs) function block {source with env := source.env.insert x value})
    (fresh : x ∉ live)
    (scope : Own.Plain.scopeOk (Own.Plain.signatures F) (live ++ [x])
      (Own.Plain.stackArities Jf) cont = true)
    {context base limit : Lir.Word} {regionBytes : Nat} {logical : Fir.Val}
    (returned : Returned P pairs lp copied addresses (holdRoots external (roots ++ held))
      context base limit regionBytes logical)
    (callers : List Lir.Frame) :
    let resumed := {saved with env := saved.env.insert x returned.word, dsts := []}
    Lir.step lp {mem := returned.memory, ctx := context, stack := returned.frame :: saved :: callers} =
      .next {mem := returned.memory, ctx := context, stack := resumed :: callers} false ∧
    Activation F P pairs lp returned.heap returned.addresses (holdRoots external held)
      (live ++ [x]) (ρf.insert x logical) (ρo.insert x returned.value)
      (roots ++ [returned.value]) joins Jf Jo cont bound function
      {source with env := source.env.insert x returned.value} resumed ∧
    HeapState P pairs returned.heap returned.addresses returned.memory (holdRoots external held)
      (roots ++ [returned.value]) context base returned.bump limit regionBytes returned.slots returned.lists ∧
    HeapState P pairs returned.heap returned.addresses returned.memory external
      ((roots ++ [returned.value]) ++ held)
      context base returned.bump limit regionBytes returned.slots returned.lists ∧
    Own.Plain.ExternalPreserved H returned.heap (holdRoots external held) ∧
    HeapHistory H.size addresses returned.heap.size returned.addresses := by
  dsimp only
  have externalEq : holdRoots external (roots ++ held) = holdRoots (holdRoots external held) roots := by
    funext location
    simp only [holdRoots, refsIn_append]
    omega
  have counted : Balance returned.heap (holdRoots (holdRoots external held) roots) [returned.value] :=
    Eq.mp (congrArg (fun external' => Balance returned.heap external' [returned.value]) externalEq)
      returned.balance
  have preserved : Own.Plain.ExternalPreserved copied returned.heap
      (holdRoots (holdRoots external held) roots) :=
    Eq.mp (congrArg (fun external' => Own.Plain.ExternalPreserved copied returned.heap external') externalEq)
      returned.preserved
  obtain ⟨canonical, preserved⟩ := before.resume x fresh copies returned.den counted preserved
  obtain ⟨step, resumedFrame⟩ := returned.history.resume frame destination real
    returned.represented returned.bounded returned.compatible returned.terminator
    returned.memory context callers
  have rootEq : holdRoots (holdRoots external (roots ++ held)) [returned.value] =
      holdRoots (holdRoots external held) (roots ++ [returned.value]) := by
    funext location
    simp only [holdRoots, refsIn_append]
    omega
  have heap : HeapState P pairs returned.heap returned.addresses returned.memory (holdRoots external held)
      (roots ++ [returned.value]) context base returned.bump limit regionBytes returned.slots returned.lists :=
    ⟨by rw [← rootEq]; exact returned.state.ready,
      returned.state.ordered, returned.state.compatible, returned.state.extent⟩
  have rootEq' : holdRoots (holdRoots external held) (roots ++ [returned.value]) =
      holdRoots external ((roots ++ [returned.value]) ++ held) := by
    funext location
    simp only [holdRoots, refsIn_append]
    omega
  have initialHistory : HeapHistory H.size addresses copied.size addresses :=
    ⟨by omega, fun _ _ => rfl⟩
  exact ⟨step, ⟨canonical, layout returned.value, resumedFrame, scope, rfl, fused returned.value⟩,
    heap, ⟨by rw [← rootEq']; exact heap.ready, heap.ordered, heap.compatible, heap.extent⟩,
    preserved, initialHistory.trans returned.history⟩


end Compilatrix.Cfg.Rc.Native.Spec
