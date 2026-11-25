import IxCC.Cfg.Rc.Proof.Native.HeapInit
import IxCC.Cfg.Rc.Proof.Native.Split

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Public.Spec
open Native.Spec IxCC.Rt.Rc.Procs

theorem cxInit_split : Rt.Procs.cxInit.splitCriticalEdges = Rt.Procs.cxInit := by rfl

/-- The actual accepted public initializer survives native edge splitting
and the appended release entry at its declared index. -/
theorem accepted_init {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program} {lowered : Lowered}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (accepted : Public.lower config F bodies P borrows uniqs = .ok lowered) :
    lowered.runtime.program.funcs[lowered.runtime.init]? = some Rt.Procs.cxInit := by
  obtain ⟨original, native, rfl, _⟩ := lower_parts accepted
  obtain ⟨main, pairs, funcs, _, _, _, _, _, _, length, program, init, _⟩ := Native.Spec.lower_parts native
  have lookup : original.program.funcs[original.init]? = some Rt.Procs.cxInit := by
    rw [program, init]
    have hge : (layoutOf P).sourceCount ≤ (layoutOf P).init := by
      simp [layoutOf, Native.Layout.init, Native.Layout.incProc]; omega
    have hinl : (inlinedProgram (layoutOf P) funcs main).funcs[(layoutOf P).init]? = some Rt.Procs.cxInit := by
      have hle : (layoutOf P).init ≤ (layoutOf P).isUniqueProc := by
        simp [Native.Layout.isUniqueProc]
      have hneDec : (layoutOf P).init ≠ (layoutOf P).decProc := by
        simp [Native.Layout.init, Native.Layout.decProc]; omega
      have hnpInit : Prune.isPrunableDeadRuntime (layoutOf P) (layoutOf P).init = false :=
        Prune.isPrunableDeadRuntime_init (layoutOf P)
      rw [inlinedProgram, Prune.pruneDeadRuntime_get_not_prunable hnpInit,
        FastDec.install_get_ne _ _ hneDec, InlineWrappers.inlineProgram_get_le hle,
        Prune.pruneUnusedReuse_get_le hle, Inline.inlineProgram_get_ge _ _ hge]
      exact raw_init (l := layoutOf P) (funcs := funcs) length main
    simp only [Lir.Program.splitCriticalEdges_eq, Array.getElem?_map, hinl, Option.map_some, cxInit_split]
  exact (assemble_existing original (layoutOf P) (Array.getElem?_eq_some_iff.mp lookup).1).trans lookup

theorem initialize_heap {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program} {lowered : Lowered}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (accepted : Public.lower config F bodies P borrows uniqs = .ok lowered)
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




end IxCC.Cfg.Rc.Public.Spec
