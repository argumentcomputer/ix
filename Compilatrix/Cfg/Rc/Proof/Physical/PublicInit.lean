import Compilatrix.Cfg.Rc.Proof.Native.HeapInit
import Compilatrix.Cfg.Rc.Proof.Native.Split

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Public.Spec
open Native.Spec Compilatrix.Rt.Rc.Procs

theorem cxInit_split : Rt.Procs.cxInit.splitCriticalEdges = Rt.Procs.cxInit := by rfl

/-- The actual accepted public initializer survives native edge splitting
and the appended release entry at its declared index. -/
theorem accepted_init {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program} {lowered : Lowered}
    (accepted : Public.lower config F bodies P = .ok lowered) :
    lowered.runtime.program.funcs[lowered.runtime.init]? = some Rt.Procs.cxInit := by
  obtain ⟨original, native, rfl, _⟩ := lower_parts accepted
  obtain ⟨main, pairs, funcs, _, _, _, _, _, _, length, program, init, _⟩ := Native.Spec.lower_parts native
  have lookup : original.program.funcs[original.init]? = some Rt.Procs.cxInit := by
    rw [program, init]
    simp only [Lir.Program.splitCriticalEdges, Array.getElem?_map,
      raw_init (l := layoutOf P) (funcs := funcs) length main, Option.map_some, cxInit_split]
  exact (assemble_existing original (layoutOf P) (Array.getElem?_eq_some_iff.mp lookup).1).trans lookup

theorem initialize_heap {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program} {lowered : Lowered}
    (accepted : Public.lower config F bodies P = .ok lowered)
    (pairs : List (Nat × Cfg.Fun))
    {size budget context : Lir.Word} {memory : X86.Memory}
    (region : Rt.Proof.RegionOk context size) (readable : Rt.Proof.LirRegion memory context size) :
    ∃ left initialized base limit,
      (∀ clock, Lir.eval {lowered.runtime.program with main := lowered.runtime.init}
        clock [size, budget] memory context = .ok ([left], initialized)) ∧
      Rt.Proof.InitPost context budget memory initialized ∧
      HeapState P pairs {} (fun _ => none) initialized (fun _ => 0) []
        context base base limit size.toNat [] (fun _ => []) :=
  HeapState.initialize (program := {lowered.runtime.program with main := lowered.runtime.init})
    (accepted_init accepted) rfl region readable




end Compilatrix.Cfg.Rc.Public.Spec
