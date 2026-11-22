import IxCC.Cfg.Rc.Proof.Native.Activation
import IxCC.Rt.Rc.Proof.Readback.Initial

/-! Construct the shared physical heap invariant by executing the real
initializer. Empty roots and logical heap are consequences of that execution;
the arena extent is retained for later complete result observation. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs

theorem HeapState.initialize {P : Program} {pairs : List (Nat × Cfg.Fun)}
    {program : Lir.Program} {initializer : Lir.FunId}
    (lookup : program.funcs[initializer]? = some Rt.Procs.cxInit)
    (main : program.main = initializer)
    {size budget context : Lir.Word} {memory : X86.Memory}
    (region : Rt.Proof.RegionOk context size) (readable : Rt.Proof.LirRegion memory context size) :
    ∃ left initialized base limit,
      (∀ clock, Lir.eval program clock [size, budget] memory context =
        .ok ([left], initialized)) ∧
      Rt.Proof.InitPost context budget memory initialized ∧
      HeapState P pairs {} (fun _ => none) initialized (fun _ => 0) []
        context base base limit size.toNat [] (fun _ => []) := by
  obtain ⟨left, initialized, base, limit, execution, post, ready, extent⟩ :=
    Init.cxInit_ready_extent lookup main region readable
  refine ⟨left, initialized, base, limit, execution, post, ?_⟩
  refine ⟨?_, Own.Rc.heapOk_empty, heapCtorOk_empty _, extent⟩
  exact ready


end IxCC.Cfg.Rc.Native.Spec
