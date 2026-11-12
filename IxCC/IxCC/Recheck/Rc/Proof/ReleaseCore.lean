import IxCC.Cfg.Rc.Proof.Native.Activation
import IxCC.Cfg.Rc.Proof.Physical.NativeMarkers
import IxCC.Rt.Rc.Gen.Proof.FrameReleaseCaller
import IxCC.Rt.Rc.Gen.Proof.AllocatorMetadata
import IxCC.Own.Rc.Proof.LeakFreedom
import IxCC.Lir.Proof.Run

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Rt.Rc
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Own IxCC.Own.Rc IxCC.Rt.Rc.Procs

/-- The returned value contributes exactly one owned root occurrence. The
public wrapper executes the real release loop before returning erased1. -/
theorem drop_top {P : Program} {pairs : List (Nat × Cfg.Fun)}
    {H : Heap} {addresses : AddressMap} {memory : X86.Memory} {external : Nat → Nat}
    {value : RVal} {word context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses memory external [value]
      context base bump limit regionBytes slots lists)
    (represented : valueWord addresses value = some word)
    {program : Lir.Program} {drop procedure : Nat}
    (wrapper : program.funcs[drop]? = some (Public.dropWrapper procedure))
    (runtime : program.funcs[procedure]? = some Gen.dec) (main : program.main = drop) :
    ∃ H' memory' slots' lists' clock,
      dropAll H [value] = some H' ∧
      HeapState P pairs H' addresses memory' external []
        context base bump limit regionBytes slots' lists' ∧
      Gen.ProtectedFrame memory memory' context base bump ∧
      Lir.eval program clock [word] memory context = .ok ([1], memory') := by
  let env : Lir.Env := ({} : Lir.Env).insert 0 word
  let continuation : Lir.Frame := {fn := drop, label := 0, pos := 1, env}
  have entered : Lir.State.initial program [word] memory context =
      some {mem := memory, ctx := context, stack := [{fn := drop, label := 0, pos := 0, env}]} := by
    simp [Lir.State.initial, Lir.enter, main, wrapper, Public.dropWrapper,
      decrementWrapper, Lir.bindParams, env]
  have enterDec : Lir.enter program procedure [word] =
      some {fn := procedure, label := 0, pos := 0, env := Gen.decEnv word} := by
    simp [Lir.enter, runtime, Gen.dec, Lir.bindParams, Gen.decEnv]
  have callStep := marker_call (g := drop) (env := env) (rest := [])
    (mem := memory) (ctx := context) wrapper rfl (Lir.env_insert_self ..) enterDec
  have idle : Gen.ReleaseInvariant maxClass H addresses memory
      (fun location => external location + refsIn location [value]) none []
      context base bump limit slots lists := heap.ready.idle
  obtain ⟨H', memory', slots', lists', charges, released, restored, trace, frame⟩ :=
    Gen.release_caller_complete_frame idle word represented program procedure runtime continuation [] rfl
  have ready := heap.ready.after_protected frame restored
  have balance : Balance H external [value] := by
    intro location
    have counted := heap.ready.idle.balance location
    simp only [Balance, holdRoots, Option.toList_none, cursorTokens, List.map_nil,
      flattenPending, List.nil_append, refsIn] at counted ⊢
    omega
  obtain ⟨logicalHeap, logicalDrop, _, ordered⟩ := dropAll_heapOk H [value] balance heap.ordered
  have same : logicalHeap = H' := Option.some.inj (logicalDrop.symm.trans released)
  subst logicalHeap
  have final : Lir.step program {mem := memory', ctx := context, stack := [continuation]} =
      .done [1] memory' := by
    apply Lir.step_ret_done wrapper (by rfl) (by rfl) (by rfl)
    simp [Lir.evalArgs, Lir.Arg.eval]
  have readyEmpty : Gen.AllocatorReady maxClass H' addresses memory' (holdRoots external [])
      context base bump limit slots' lists' := by
    have roots : holdRoots external [] = external := by
      funext location
      simp [holdRoots, refsIn]
    rw [roots]
    exact ready
  have complete := (Sem.Star.single (Lir.semStep_next.mpr callStep)).trans trace
  refine ⟨H', memory', slots', lists', 1+charges, released,
    ⟨readyEmpty, ordered,
      HeapCtorOk.dropAll H [value] heap.compatible released, heap.extent⟩,
    frame, ?_⟩
  apply (Lir.runs_eval entered).eq
  exact Sem.Reaches.of_final complete (Lir.semStep_done.mpr final ▸ .done) (by simp)

/-- With no external roots, the actual completed release leaves no logical
live cells. Free-list and arena facts remain in the returned HeapState. -/
theorem HeapState.reclaimed {P : Program} {pairs : List (Nat × Cfg.Fun)}
    {H : Heap} {addresses : AddressMap} {memory : X86.Memory}
    {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses memory (fun _ => 0) []
      context base bump limit regionBytes slots lists) :
    ∀ location, location < H.size → H.cell? location = some .dead := by
  apply heapOk_zero_all_dead heap.ordered
  intro location
  have counted := heap.ready.idle.balance location
  simpa [holdRoots, refsIn, cursorTokens, flattenPending] using counted



end IxCC.Cfg.Rc.Native.Spec
