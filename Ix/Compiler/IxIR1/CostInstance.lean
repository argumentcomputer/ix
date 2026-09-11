import Ix.Compiler.IxIR1.NoReuse

/-!
# Exact cost instance for a real IxIR₀ → IxIR₁ lowering

This module pins one nondegenerate whole-pass cost observation.  A closed
reference to a nullary constructor lowers to one shared allocation, and the
resulting target run has exactly one allocation and no reuse, free, or
reference-count operation.  `RunCostInvariant.of_witness` promotes the exact
kernel-checked run to every successful fuel and then to `CostRefinement`.
-/

namespace Ix.Compiler.IxIR1.CostInstance

open Ix.Compiler.Ixon (Address)
open Ix.Compiler.IxIR1.Lower
open Ix.Compiler.IxIR1.LowerSim

/-- Stable source identity for the exact cost fixture. -/
def constructor : Address := Address.replicate 0xc7

/-- A single nullary constructor declaration. -/
def sourceDeclarations : List (Address × IxIR0.Decl) :=
  [(constructor, .ctor 0 0)]

/-- The closed source program constructs that nullary value. -/
def sourceMain : IxIR0.Expr := .ref constructor

/-- The declaration environment used to execute the source fixture. -/
def sourceCtx : IxIR0.Ctx :=
  { env := IxIR0.Env.ofList sourceDeclarations }

/-- The pure value produced by the source fixture. -/
def sourceValue : IxIR0.Value := .ctor constructor 0 []

/-- The exact target code emitted by the whole-pass lowerer. -/
def targetCode : Code :=
  .letOp (.alloc .shared (ctorIdOf constructor 0) #[])
    (.ret (.var 0))

/-- Constructors do not need target declarations: their identity is carried
by `Op.alloc`. -/
def targetCtx : Ctx := { decls := Env.empty }

/-- The target store after the fixture's sole allocation. -/
def targetStore : Store :=
  (({} : Store).allocNode .shared
    (.ctorN (ctorIdOf constructor 0) #[])).1

/-- The exact four-counter observation for the fixture. -/
def exactCost : CostObservation :=
  { allocs := 1, reuses := 0, frees := 0, rcops := 0 }

@[simp] private theorem estateMapGet_run {error state result : Type}
    (f : state → result) (initial : state) :
    EStateM.run (f <$> (get : EStateM error state state)) initial =
      .ok (f initial) initial := by
  rfl

/-- The executable whole-program lowerer emits exactly the fixture code and
no declarations or generated state. -/
theorem lowerAllAction_run :
    (lowerAllAction sourceDeclarations sourceMain .shared 10).run {} =
      .ok ([], targetCode) {} := by
  simp [sourceDeclarations, sourceMain, targetCode, lowerAllAction,
    lowerDecl, lowerFnBody, releaseSlots, lowerE, ctorIdOf,
    AVal.toAtom, VEnv.rel, VEnv.bump, emitOp, IxIR0.Env.ofList,
    constructor, List.filterMapM,
    List.filterMapM.loop]

/-- The source reference evaluates to the declared nullary constructor. -/
theorem sourceEval_exact :
    IxIR0.eval sourceCtx 3 [] sourceMain = .ok sourceValue := by
  simp [sourceCtx, sourceDeclarations, sourceMain, sourceValue,
    IxIR0.eval, IxIR0.saturate, IxIR0.fire, IxIR0.Env.ofList,
    IxIR0.Head.arity, constructor]

/-- Two evaluator ticks execute the allocation and final return. -/
theorem runMain_exact :
    runMain targetCtx targetCode 2 = .ok (targetStore, .loc 0) := by
  unfold runMain targetCode
  rw [runCode.eq_def]
  dsimp only
  rw [Sim.runOp_alloc (by rfl)]
  simp only [bind, Except.bind]
  rw [runCode.eq_def]
  dsimp only
  rfl

/-- The exact run changes only the allocation counter. -/
theorem targetStore_cost : costObservation targetStore = exactCost := by
  rfl

/-- The allocated target node realizes the exact source constructor value. -/
theorem valueGraph_exact (funRel : Sim.FunctionRel) :
    Sim.ValueGraph funRel targetStore sourceValue (.loc 0) := by
  refine .ctor (by rfl) (by rfl) (by rfl) ?_
  exact .nil

/-- Every successful execution of the emitted target code has the same exact
four-counter observation. -/
theorem exactRunCost :
    RunCostInvariant targetCtx targetCode (fun observation =>
      observation = exactCost) := by
  refine RunCostInvariant.of_witness
    (spec := fun observation => observation = exactCost)
    (witnessFuel := 2) (witnessStore := targetStore)
    (witnessValue := .loc 0) runMain_exact ?_
  exact targetStore_cost

/-- The exact target observation is a semantic cost refinement for the source
fixture, independently of the chosen function relation. -/
theorem exactCostRefinement (funRel : Sim.FunctionRel) :
    CostRefinement
      sourceCtx
      targetCtx sourceMain targetCode funRel
      (fun _ observation => observation = exactCost) :=
  exactRunCost.costRefinement

/-- One theorem joins the real lowering result, successful source and target
runs, their semantic value graph, and the exact counter refinement.  This is
the nonvacuous executable witness for the generic cost interface. -/
theorem loweringCostWitness (funRel : Sim.FunctionRel) :
    (lowerAllAction sourceDeclarations sourceMain .shared 10).run {} =
        .ok ([], targetCode) {} ∧
      IxIR0.eval sourceCtx 3 [] sourceMain = .ok sourceValue ∧
      runMain targetCtx targetCode 2 = .ok (targetStore, .loc 0) ∧
      Sim.ValueGraph funRel targetStore sourceValue (.loc 0) ∧
      costObservation targetStore = exactCost := by
  refine ⟨lowerAllAction_run, sourceEval_exact, runMain_exact,
    valueGraph_exact funRel, ?_⟩
  exact (exactCostRefinement funRel) sourceEval_exact runMain_exact
    (valueGraph_exact funRel)

end Ix.Compiler.IxIR1.CostInstance
