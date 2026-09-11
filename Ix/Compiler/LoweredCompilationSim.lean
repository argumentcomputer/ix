import Ix.Compiler.LoweredCompilation
import Ix.Compiler.PipelineSound
import Ix.Compiler.IxIR1.ReaddressOwnership

/-! Ownership, progress, and addressed execution derived from the common
checked lowering record. Ixon provenance is composed by the calling frontend.
-/

namespace Ix.Compiler.Pipeline.LoweredCompilation

open Ix.Compiler.Ixon (Address Owned)
open Ix.Compiler.IxIR1
open Ix.Compiler.IxIR1.Lower
open Ix.Compiler.IxIR1.LowerSim

variable {mainWorld : Owned} {fuel : Nat}

def sourceCtx (compilation : LoweredCompilation mainWorld fuel) : IxIR0.Ctx :=
  { env := IxIR0.Env.ofList compilation.declarations }

def exactTargetCtx (compilation : LoweredCompilation mainWorld fuel)
    (oracle : Address → List RVal → Option RVal) : Ctx :=
  compilation.lowering.result.rebuildSourceCtx compilation.lowering.raw oracle

def functionRel (compilation : LoweredCompilation mainWorld fuel) : IxIR1.Sim.FunctionRel :=
  CompilerFunctionRel compilation.sourceCtx (IxIR0.Env.ofList compilation.declarations)
    compilation.lowering.finalState

theorem lowerRun (compilation : LoweredCompilation mainWorld fuel) :
    (lowerAllAction compilation.declarations compilation.main mainWorld fuel).run {} =
      .ok (compilation.lowering.raw, compilation.lowering.mainCode) compilation.lowering.finalState := by
  simpa only [lowerAllIndexedAction_eq_lowerAllAction] using compilation.lowering.lowerRun

theorem rebuildAudit (compilation : LoweredCompilation mainWorld fuel) :
    compilation.lowering.result.rebuildSemanticAudit
      compilation.lowering.raw compilation.lowering.mainCode = true :=
  ReaddressAll.rebuildSemanticAudit_of_run_eq_ok
    (readdressAll_run_of_lowerAllIndexedFullyAddressed_eq_ok
      compilation.lowering.lowerRun compilation.lowering.addressedRun)

theorem exactTargetCtx_decls_of_mem (compilation : LoweredCompilation mainWorld fuel)
    (oracle : Address → List RVal → Option RVal) {address : Address} {declaration : Decl}
    (member : (address, declaration) ∈ compilation.lowering.raw) :
    (compilation.exactTargetCtx oracle).decls address = some declaration :=
  ReaddressAll.Result.raw_lookup_of_mem_of_rebuildSemanticAudit compilation.rebuildAudit member

theorem exactExtraRepresented (compilation : LoweredCompilation mainWorld fuel)
    (oracle : Address → List RVal → Option RVal) :
    ExtraRepresented (compilation.exactTargetCtx oracle) compilation.lowering.finalState := by
  apply lowerAllAction_extraRepresented compilation.lowerRun
  intro address declaration member
  exact compilation.exactTargetCtx_decls_of_mem oracle
    (lowerAllAction_extra_mem_result compilation.lowerRun member)

theorem exactCompilerContracts (compilation : LoweredCompilation mainWorld fuel)
    (oracle : Address → List RVal → Option RVal) :
    CompilerContracts (IxIR0.Env.ofList compilation.declarations)
        (compilation.exactTargetCtx oracle) ∧
      ExtraFnContracts (compilation.exactTargetCtx oracle) compilation.lowering.finalState := by
  apply lowerAllAction_compilerContracts compilation.lowerRun
    (fun member => compilation.exactTargetCtx_decls_of_mem oracle member)
  · intro address source worlds result member _
    exact compilation.declarationSelected member
  · rfl

theorem externValueContract (compilation : LoweredCompilation mainWorld fuel)
    (oracle : Address → List RVal → Option RVal) :
    ExternValueContract compilation.functionRel compilation.sourceCtx
      (compilation.exactTargetCtx oracle) := by
  constructor
  intro store address arity sourceFunction sourceResult sourceArgs args result lookup
  exact False.elim (compilation.sourceEnv_ne_extern lookup)

theorem externTraceProgressContract (compilation : LoweredCompilation mainWorld fuel)
    (oracle : Address → List RVal → Option RVal) :
    ExternTraceProgressContract compilation.functionRel compilation.sourceCtx
      (compilation.exactTargetCtx oracle) := by
  constructor
  intro sourceLimit store address arity sourceFunction sourceResult sourceArgs args lookup
  exact False.elim (compilation.sourceEnv_ne_extern lookup)

/-- Every call-aware source trace produces an owned execution of the exact
fully addressed output. Ownership and intermediate progress are reconstructed
from the compiler trace and checked row/extern certificate. -/
theorem addressedOwnedMain (compilation : LoweredCompilation .shared fuel)
    {sourceFuel : Nat} {sourceValue : IxIR0.Value}
    (trace : IxIR0.ProjectionSafe.Eval compilation.sourceCtx sourceFuel []
      compilation.main sourceValue) :
    ∃ targetFuel rawStore store value,
      IxIR1.runOwnedMain (compilation.lowering.result.addressedCtx (fun _ _ => none))
        .shared compilation.lowering.result.main targetFuel = .ok (store, value) ∧
      store = Readdress.Store.mapAddresses
        (compilation.lowering.result.rebuildRename compilation.lowering.raw) rawStore ∧
      IxIR1.Sim.ValueGraph compilation.functionRel rawStore sourceValue value := by
  have progress := lowerAllAction_main_progress_of_trace_sealed rfl compilation.lowerRun
    (fun member => compilation.exactTargetCtx_decls_of_mem (fun _ _ => none) member)
    (compilation.exactExtraRepresented (fun _ _ => none))
    (compilation.exactCompilerContracts (fun _ _ => none)).1
    (compilation.externValueContract (fun _ _ => none))
    (compilation.externTraceProgressContract (fun _ _ => none)) trace
  have simulation : SemanticForwardSimulation compilation.sourceCtx
      (compilation.exactTargetCtx (fun _ _ => none)) compilation.main
      compilation.lowering.mainCode compilation.functionRel := by
    apply lowerAllAction_semanticForwardSimulation_of_targetProgress_sealed rfl compilation.lowerRun
      (fun member => compilation.exactTargetCtx_decls_of_mem (fun _ _ => none) member)
      (compilation.exactExtraRepresented (fun _ _ => none))
      (compilation.exactCompilerContracts (fun _ _ => none)).1
      (compilation.externValueContract (fun _ _ => none))
    intro _ _ _
    exact progress
  obtain ⟨targetFuel, rawStore, value, rawRun, graph⟩ := simulation trace.run
  let rename := compilation.lowering.result.rebuildRename compilation.lowering.raw
  let store := Readdress.Store.mapAddresses rename rawStore
  have ownership := lowerAllAction_main_owned compilation.lowerRun
    (compilation.exactExtraRepresented (fun _ _ => none))
    (compilation.exactCompilerContracts (fun _ _ => none)).1 rawRun
  have rawWorld : IxIR1.Sim.HasWorld rawStore .shared value :=
    ownership.roots_world ⟨.shared, value⟩ (by simp)
  have finalWorld : IxIR1.Sim.HasWorld store .shared value :=
    (IxIR1.Sim.hasWorld_mapAddresses_iff rename rawStore .shared value).mpr rawWorld
  have addressedRun : IxIR1.runMain (compilation.lowering.result.addressedCtx (fun _ _ => none))
      compilation.lowering.result.main targetFuel = .ok (store, value) := by
    simp only [exactTargetCtx] at rawRun
    rw [compilation.lowering.result.main_eq_rebuildMapAddresses compilation.rebuildAudit]
    rw [Readdress.runMain_mapAddresses
      (compilation.lowering.result.renames_rebuildSourceCtx compilation.rebuildAudit (fun _ _ => none))
      compilation.lowering.mainCode targetFuel, rawRun]
    rfl
  refine ⟨targetFuel, rawStore, store, value, ?_, rfl, graph⟩
  unfold IxIR1.runOwnedMain
  change (IxIR1.runMain (compilation.lowering.result.addressedCtx (fun _ _ => none))
    compilation.lowering.result.main targetFuel >>= IxIR1.checkResultWorld .shared) = _
  rw [addressedRun]
  simp [IxIR1.checkResultWorld, IxIR1.Sim.rval_hasWorld_eq_true_iff.mpr finalWorld]

/-- Every successful fully addressed main can reclaim its returned root.
The common lowering trace supplies both ownership and append-order facts. -/
theorem reclamation (compilation : LoweredCompilation mainWorld fuel)
    (oracle : Address → List RVal → Option RVal) :
    Reclamation (compilation.lowering.result.addressedCtx oracle)
      compilation.lowering.result.main mainWorld := by
  have raw : Reclamation (compilation.exactTargetCtx oracle)
      compilation.lowering.mainCode mainWorld :=
    NoReuse.lowerAllAction_reclamation compilation.lowerRun rfl
      (compilation.exactExtraRepresented oracle)
      (compilation.exactCompilerContracts oracle).1
  intro runFuel store value run
  exact NoReuse.lowerAllIndexedFullyAddressed_reclamation_of_exact_raw
    compilation.lowering.lowerRun compilation.lowering.addressedRun oracle raw run

/-- Ownership at any successful addressed execution follows from the exact
lowering trace; the address action preserves locations and owner counts. -/
theorem owned (compilation : LoweredCompilation mainWorld fuel)
    (oracle : Address → List RVal → Option RVal)
    {runFuel : Nat} {store : Store} {value : RVal}
    (run : IxIR1.runMain (compilation.lowering.result.addressedCtx oracle)
      compilation.lowering.result.main runFuel = .ok (store, value)) :
    IxIR1.Sim.RootOwnership store [⟨mainWorld, value⟩] := by
  rw [compilation.lowering.result.main_eq_rebuildMapAddresses compilation.rebuildAudit] at run
  have transport := Readdress.runMain_mapAddresses
    (compilation.lowering.result.renames_rebuildSourceCtx compilation.rebuildAudit oracle)
    compilation.lowering.mainCode runFuel
  rw [run] at transport
  cases rawRun : IxIR1.runMain (compilation.exactTargetCtx oracle)
      compilation.lowering.mainCode runFuel with
  | error error =>
      simp only [exactTargetCtx] at rawRun
      rw [rawRun] at transport
      contradiction
  | ok output =>
      rcases output with ⟨rawStore, rawValue⟩
      simp only [exactTargetCtx] at rawRun
      rw [rawRun] at transport
      have result : store = Readdress.Store.mapAddresses
          (compilation.lowering.result.rebuildRename compilation.lowering.raw) rawStore ∧
          value = rawValue := by
        simpa only [Readdress.mapRunResult_ok, Except.ok.injEq, Prod.mk.injEq] using transport
      rcases result with ⟨rfl, rfl⟩
      exact (IxIR1.Sim.rootOwnership_mapAddresses_iff _ _ _).mpr
        (lowerAllAction_main_owned compilation.lowerRun
          (compilation.exactExtraRepresented oracle)
          (compilation.exactCompilerContracts oracle).1 rawRun)

end Ix.Compiler.Pipeline.LoweredCompilation
