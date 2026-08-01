import Ix.Tc.Verify.Check.MemberEvidence

/-!
# Per-constant reset framing

The public checker enters the recursive method table before executing
`TcM.reset`.  This file proves that the exact reset establishes the empty
local-context invariant while retaining the stable kernel/cache state needed
by the fixed method table.
-/

namespace Ix.Tc

namespace TcM

/-- The production reset preserves the stable kernel invariant and
establishes the exact empty-context, full-inference entry conditions. -/
theorem reset_whnf_entry
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} (before : TcState .anon)
    (hlayer : layer.StateOK before) :
    TcM.WF
      (KernelStateWF semantics trProj world support) before
      (TcM.reset (m := .anon))
      (fun _ after =>
        after.inferOnly = false ∧
          CtxRecon world.venv uvars world.nameOf trProj after [] ∧
          layer.StateOK after ∧
          after.recFuel = before.fuelBudget) := by
  intro hkernel
  change KernelStateWF semantics trProj world support
      { before with
        ctx := #[]
        letVals := #[]
        numLetBindings := 0
        ctxId := emptyCtxAddr
        ctxIdStack := #[]
        equivManager := {}
        inferOnly := false
        inNativeReduce := false
        cheapRecursionDepth := 0
        eagerReduce := false
        defEqDepth := 0
        defEqPeak := 0
        dispatchDepth := 0
        recFuel := before.fuelBudget
        ctxAddrCache := {}
        lctx := {} } ∧
    (false = false ∧
      CtxRecon world.venv uvars world.nameOf trProj
        { before with
          ctx := #[]
          letVals := #[]
          numLetBindings := 0
          ctxId := emptyCtxAddr
          ctxIdStack := #[]
          equivManager := {}
          inferOnly := false
          inNativeReduce := false
          cheapRecursionDepth := 0
          eagerReduce := false
          defEqDepth := 0
          defEqPeak := 0
          dispatchDepth := 0
          recFuel := before.fuelBudget
          ctxAddrCache := {}
          lctx := {} } [] ∧
      layer.StateOK
        { before with
          ctx := #[]
          letVals := #[]
          numLetBindings := 0
          ctxId := emptyCtxAddr
          ctxIdStack := #[]
          equivManager := {}
          inferOnly := false
          inNativeReduce := false
          cheapRecursionDepth := 0
          eagerReduce := false
          defEqDepth := 0
          defEqPeak := 0
          dispatchDepth := 0
          recFuel := before.fuelBudget
          ctxAddrCache := {}
          lctx := {} } ∧
      before.fuelBudget = before.fuelBudget)
  refine ⟨?_, rfl, ?_, ?_, rfl⟩
  · exact
      { core := hkernel.core.of_env_eq rfl
        internSupport := hkernel.internSupport
        caches := hkernel.caches
        equivalences := EquivManager.WF.empty }
  · exact CtxRecon.empty rfl rfl rfl rfl
  · cases layer with
    | structuralNoAccel => exact hlayer
    | noAccel => exact hlayer
    | accelerated => exact hlayer

end TcM

end Ix.Tc
