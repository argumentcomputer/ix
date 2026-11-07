import IxCC.Recheck.Rc.Proof.PublicRelease
import IxCC.Cfg.Rc.Proof.Physical.NumericInputs
import IxCC.Cfg.Rc.Proof.Physical.PublicEntry

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Own IxCC.Own.Rc IxCC.Rt.Rc.Procs

/-- Numeric arguments own no heap edges, even in an arena with a nonempty
allocation history and recycled slots. No initializer is invoked here. -/
theorem HeapState.numeric_reentry {P : Program} {pairs : List (Nat × Cfg.Fun)}
    {H : Heap} {addresses : AddressMap} {memory : X86.Memory} {external : Nat → Nat}
    {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses memory external []
      context base bump limit regionBytes slots lists) (numbers : List Nat) :
    HeapState P pairs H addresses memory external (Own.litArgs numbers)
      context base bump limit regionBytes slots lists ∧
      Balance H external (Own.litArgs numbers) := by
  have roots : holdRoots external (Own.litArgs numbers) = holdRoots external [] := by
    funext location
    simp [holdRoots, numeric_refs, refsIn]
  refine ⟨⟨?_, heap.ordered, heap.compatible, heap.extent⟩, ?_⟩
  · rw [roots]
    exact heap.ready
  · intro location
    have counted := heap.ready.idle.balance location
    simpa [Balance, holdRoots, refsIn, numeric_refs, cursorTokens, flattenPending] using counted

/-- Start another actual public root from the heap left by release, retaining
bump/free-list history. Its physical simulation is the existing checked
whole-code theorem instantiated at this reached idle boundary. -/
theorem recycled_entry {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
    {lowered : Public.Lowered} (admission : CodeAdmission F bodies P config pairs functions)
    (accepted : Public.lower config F bodies P = .ok lowered)
    {H : Heap} {addresses : AddressMap} {memory : X86.Memory} {external : Nat → Nat}
    {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses memory external []
      context base bump limit regionBytes slots lists)
    {root : Nat} {source : Fir.Fun} (sourceLookup : F.fun? root = some source)
    {numbers : List Nat} {words : List Lir.Word} (encoded : Rt.natWords numbers = some words)
    (arity : numbers.length = source.params.length) :
    let raw := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) root
    Sem.Sim (ReturnedOutput P pairs raw H addresses external context base limit regionBytes)
      Nat.succ (fun clock => Fir.run F clock root (Fir.litArgs numbers))
      (fun clock => Lir.eval {lowered.runtime.program with main := root} clock words memory context) := by
  obtain ⟨ready, balance⟩ := heap.numeric_reentry numbers
  exact public_entry_eval_sim admission accepted sourceLookup (Own.dens_lits H numbers) balance
    (numeric_words encoded) (numeric_compatible _ numbers)
    (by simpa only [Own.litArgs, List.length_map] using arity) ready



end IxCC.Cfg.Rc.Native.Spec
