import Ix.Compiler.IxIR1.CostInstance

/-!
# A source-sensitive constructor cost model

IxIR₀ evaluator fuel remains only a totality witness.  This module instead
attaches cost to the IxIR₁ operations emitted for a parametric family of
closed source programs.  The source numeral `n` is a unary constructor tree;
its actual whole-pass lowering performs exactly `n + 1` allocations and no
reuse, free, or reference-count operation.

This is deliberately a first proved fragment, not a global syntax bound:
calls and recursion require a dynamic source trace or a compositional
lowering certificate before the same statement can cover arbitrary programs.
-/

namespace Ix.Compiler.IxIR1.CostModel

open Ix.Compiler.Ixon (Address)
open Ix.Compiler.IxIR1.Lower
open Ix.Compiler.IxIR1.LowerSim

/-- Stable constructor identities for the unary source family. -/
def zeroConstructor : Address := Address.replicate 0xc8

def succConstructor : Address := Address.replicate 0xc9

@[simp] theorem zeroConstructor_ne_succConstructor :
    zeroConstructor ≠ succConstructor := by
  intro heq
  have hbyte := congrArg (fun address =>
    address.get (⟨0, by omega⟩ : Fin 32)) heq
  simp [zeroConstructor, succConstructor] at hbyte

/-- The complete source declaration set for unary constructor values. -/
def sourceDeclarations : List (Address × IxIR0.Decl) :=
  [(zeroConstructor, .ctor 0 0), (succConstructor, .ctor 1 1)]

def sourceCtx : IxIR0.Ctx :=
  { env := IxIR0.Env.ofList sourceDeclarations }

@[simp] theorem sourceCtx_zero :
    sourceCtx.env zeroConstructor = some (.ctor 0 0) := by
  simp [sourceCtx, sourceDeclarations, IxIR0.Env.ofList]

@[simp] theorem sourceCtx_succ :
    sourceCtx.env succConstructor = some (.ctor 1 1) := by
  simp [sourceCtx, sourceDeclarations, IxIR0.Env.ofList,
    zeroConstructor_ne_succConstructor]

/-- A closed unary numeral.  Its parameter is source structure, not fuel. -/
def sourceNat : Nat → IxIR0.Expr
  | 0 => .ref zeroConstructor
  | n + 1 => .app (.ref succConstructor) (sourceNat n)

/-- The pure unary value denoted by `sourceNat`. -/
def sourceValue : Nat → IxIR0.Value
  | 0 => .ctor zeroConstructor 0 []
  | n + 1 => .ctor succConstructor 1 [sourceValue n]

/-- Constructor occurrences in a pure source value.  This is the
source-result component of the fragment's cost specification. -/
def constructorNodes : IxIR0.Value → Nat
  | .ctor _ _ fields => 1 + (fields.map constructorNodes).sum
  | .clos .. | .pap .. | .lit .. | .erased => 0

@[simp] theorem constructorNodes_sourceValue (n : Nat) :
    constructorNodes (sourceValue n) = n + 1 := by
  induction n with
  | zero => simp [sourceValue, constructorNodes]
  | succ n ih =>
      simp [sourceValue, constructorNodes, ih]
      omega

/-- The target prefix emitted for a unary numeral. -/
def targetEmit : Nat → Emit
  | 0 => emitOp (.alloc .shared (ctorIdOf zeroConstructor 0) #[])
  | n + 1 =>
      targetEmit n ∘
        emitOp (.alloc .shared (ctorIdOf succConstructor 1) #[.var 0])

def targetCode (n : Nat) : Code :=
  targetEmit n (.ret (.var 0))

def targetCtx : Ctx := { decls := Env.empty }

/-- The exact instruction-counter model for source numeral `n`. -/
def exactCost (n : Nat) : CostObservation :=
  { allocs := n + 1, reuses := 0, frees := 0, rcops := 0 }

/-- The semantic cost relation: allocations equal the constructor size of
the source result, and the remaining memory counters are zero. -/
def SourceSensitiveCostSpec
    (value : IxIR0.Value) (observation : CostObservation) : Prop :=
  observation.allocs = constructorNodes value ∧
    observation.reuses = 0 ∧ observation.frees = 0 ∧
      observation.rcops = 0

theorem sourceEval_exact (n : Nat) :
    IxIR0.eval sourceCtx (n + 3) [] (sourceNat n) =
      .ok (sourceValue n) := by
  induction n with
  | zero =>
      simp [sourceNat, sourceValue, IxIR0.eval, IxIR0.saturate,
        IxIR0.fire, IxIR0.Head.arity]
  | succ n ih =>
      simp [sourceNat, sourceValue, IxIR0.eval, IxIR0.saturate,
        IxIR0.Head.arity, ih, Nat.add_assoc]
      simp only [bind, Except.bind]
      rw [IxIR0.apply.eq_def]
      dsimp only
      rw [IxIR0.saturate.eq_def]
      dsimp only
      simp [IxIR0.Head.arity, IxIR0.fire]

/-! ## Exact target execution -/

/-- The concrete heap built by the target allocation chain. -/
def targetStore : Nat → Store
  | 0 =>
      (({} : Store).allocNode .shared
        (.ctorN (ctorIdOf zeroConstructor 0) #[])).1
  | n + 1 =>
      ((targetStore n).allocNode .shared
        (.ctorN (ctorIdOf succConstructor 1) #[.loc n])).1

/-- Runtime binders after the chain, newest unary node first. -/
def targetEnv : Nat → List RVal
  | 0 => [.loc 0]
  | n + 1 => .loc (n + 1) :: targetEnv n

@[simp] theorem targetEnv_head (n : Nat) :
    (targetEnv n)[0]? = some (.loc n) := by
  cases n <;> rfl

@[simp] theorem targetStore_nodes_size (n : Nat) :
    (targetStore n).nodes.size = n + 1 := by
  induction n with
  | zero => simp [targetStore, Store.allocNode]
  | succ n ih => simp [targetStore, Store.allocNode, ih, Nat.add_assoc]

theorem targetStore_counters (n : Nat) :
    (targetStore n).allocs = n + 1 ∧
      (targetStore n).reuses = 0 ∧ (targetStore n).frees = 0 ∧
        (targetStore n).rcops = 0 := by
  induction n with
  | zero => simp [targetStore, Store.allocNode]
  | succ n ih =>
      rcases ih with ⟨hallocs, hreuses, hfrees, hrcops⟩
      simp [targetStore, Store.allocNode, hallocs, hreuses, hfrees,
        hrcops]

@[simp] theorem targetStore_cost (n : Nat) :
    costObservation (targetStore n) = exactCost n := by
  rcases targetStore_counters n with ⟨hallocs, hreuses, hfrees, hrcops⟩
  simp only [costObservation, exactCost]
  rw [hallocs, hreuses, hfrees, hrcops]

/-- Executing the allocation prefix leaves exactly `targetStore n` and its
newest-to-oldest runtime environment for an arbitrary continuation. -/
theorem runCode_targetEmit (cur : FnDef) (n k : Nat) (rest : Code) :
    runCode targetCtx (k + n + 2) cur {} [] (targetEmit n rest) =
      runCode targetCtx (k + 1) cur (targetStore n) (targetEnv n) rest := by
  induction n generalizing k rest with
  | zero =>
      rw [runCode.eq_def]
      dsimp only [targetEmit, emitOp]
      rw [Sim.runOp_alloc (by rfl)]
      rfl
  | succ n ih =>
      rw [targetEmit]
      simp only [Function.comp_apply, emitOp]
      rw [show k + (n + 1) + 2 = (k + 1) + n + 2 by omega]
      rw [ih (k + 1)]
      rw [runCode.eq_def]
      dsimp only
      rw [Sim.runOp_alloc (values := [.loc n]) (by
        unfold resolveAtoms
        rw [← Array.foldlM_toList]
        simp [resolveAtom]
        rfl)]
      simp only [bind, Except.bind]
      simp [targetStore, targetEnv, Store.allocNode,
        targetStore_nodes_size]

/-- The exact successful target trace for every unary source size. -/
theorem runMain_exact (n : Nat) :
    runMain targetCtx (targetCode n) (n + 2) =
      .ok (targetStore n, .loc n) := by
  unfold runMain targetCode
  have hprefix := runCode_targetEmit
    { arity := 0, result := .shared, papSafe := false,
      body := targetEmit n (.ret (.var 0)) }
    n 0 (.ret (.var 0))
  simp only [Nat.zero_add] at hprefix
  rw [hprefix]
  rw [runCode.eq_def]
  simp [resolveAtom, bind, Except.bind]

/-! ## Exact whole-pass lowering -/

/-- The recursive lowering core emits precisely the unary allocation prefix.
The compiler-fuel expression is only a sufficient termination witness. -/
theorem lowerE_exact (n : Nat) (state : LowSt) :
    (lowerE sourceCtx.env (4 * n + 1) ⟨[], 0⟩ .shared
      (sourceNat n)).run state =
        .ok (⟨[], n + 1⟩, targetEmit n, .slotA n) state := by
  induction n generalizing state with
  | zero =>
      simp [sourceNat, lowerE, VEnv.bump, targetEmit]
  | succ n ih =>
      simp [sourceNat, lowerE, lowerSpine, knownCall, lowerArgs,
        padWorlds, sourceCtx_succ, VEnv.bump, VEnv.rel, AVal.toAtom,
        targetEmit, emitOp, Function.comp_def, Nat.mul_succ]
      have hih := ih state
      simp only [EStateM.run] at hih
      simp only [Functor.map, EStateM.map, EStateM.run]
      rw [hih]
      simp

theorem lowerFnBody_exact (n : Nat) (state : LowSt) :
    (lowerFnBody sourceCtx.env (4 * n + 2) ⟨[], 0⟩ [] .shared
      (sourceNat n)).run state = .ok (targetCode n) state := by
  simp [lowerFnBody, releaseSlots]
  have hlower := lowerE_exact n state
  simp only [EStateM.run] at hlower
  simp only [Functor.map, EStateM.map, EStateM.run]
  rw [hlower]
  simp [targetCode, VEnv.rel, AVal.toAtom]

/-- The executable whole-pass lowering, including declaration traversal and
generated-state observation, emits no declarations and exactly `targetCode`.
-/
theorem lowerAllAction_run (n : Nat) :
    (lowerAllAction sourceDeclarations (sourceNat n) .shared
      (4 * n + 2)).run {} = .ok ([], targetCode n) {} := by
  simp [lowerAllAction, sourceDeclarations, lowerDecl, List.filterMapM,
    List.filterMapM.loop]
  have hmain := lowerFnBody_exact n ({} : LowSt)
  simp only [sourceCtx, sourceDeclarations] at hmain
  simp only [EStateM.run] at hmain
  simp only [EStateM.run]
  rw [hmain]

/-! ## Source-sensitive cost refinement -/

/-- The target heap realizes the complete unary source result at its newest
allocation. -/
theorem valueGraph_exact (funRel : Sim.FunctionRel) (n : Nat) :
    Sim.ValueGraph funRel (targetStore n) (sourceValue n) (.loc n) := by
  induction n with
  | zero =>
      refine .ctor (by rfl) (by rfl) (by rfl) ?_
      exact .nil
  | succ n ih =>
      let node : Node :=
        .ctorN (ctorIdOf succConstructor 1) #[.loc n]
      have hextends : Sim.StoreGraphExtends (targetStore n)
          ((targetStore n).allocNode .shared node).1 :=
        Sim.StoreGraphExtends.allocNode (targetStore n) .shared node
      have hfield : Sim.ValueGraph funRel
          ((targetStore n).allocNode .shared node).1
          (sourceValue n) (.loc n) :=
        ih.monoStore hextends
      have hget : (targetStore (n + 1)).get? (n + 1) =
          some ⟨.shared, 1,
            .ctorN (ctorIdOf succConstructor 1) #[.loc n]⟩ := by
        have hnew :
            ((targetStore n).allocNode .shared node).1.get? (n + 1) =
              some ⟨.shared, 1, node⟩ := by
          rw [← targetStore_nodes_size n]
          exact Sim.HeapIso.get?_allocNode_new
            (targetStore n) .shared node
        simpa only [targetStore, node] using hnew
      refine .ctor hget (by rfl) (by rfl) (.cons ?_ .nil)
      simpa [targetStore, node] using hfield

/-- Every successful execution of the emitted numeral code has the exact
counter vector predicted by the source parameter. -/
theorem exactRunCost (n : Nat) :
    RunCostInvariant targetCtx (targetCode n)
      (fun observation => observation = exactCost n) := by
  refine RunCostInvariant.of_witness
    (spec := fun observation => observation = exactCost n)
    (witnessFuel := n + 2) (witnessStore := targetStore n)
    (witnessValue := .loc n) (runMain_exact n) ?_
  exact targetStore_cost n

/-- Exact source-sensitive cost refinement for the unary constructor
fragment.  In particular, allocation is bounded (indeed equal) by source
result size, and RC traffic is bounded by zero. -/
theorem sourceSensitiveCostRefinement (funRel : Sim.FunctionRel) (n : Nat) :
    CostRefinement sourceCtx targetCtx (sourceNat n) (targetCode n) funRel
      SourceSensitiveCostSpec := by
  intro sourceFuel result targetFuel store runtimeValue hsource htarget
    _hgraph
  have hresult : result = sourceValue n :=
    sourceEval_ok_unique hsource (sourceEval_exact n)
  subst result
  have hcost : costObservation store = exactCost n :=
    exactRunCost n htarget
  rw [hcost]
  simp [SourceSensitiveCostSpec, exactCost]

def SourceSensitiveBoundsSpec
    (value : IxIR0.Value) (observation : CostObservation) : Prop :=
  observation.allocs ≤ constructorNodes value ∧ observation.rcops ≤ 0

/-- The exact model exposed in conventional upper-bound form. -/
theorem sourceSensitiveBoundsCostRefinement
    (funRel : Sim.FunctionRel) (n : Nat) :
    CostRefinement sourceCtx targetCtx (sourceNat n) (targetCode n) funRel
      SourceSensitiveBoundsSpec := by
  intro sourceFuel result targetFuel store runtimeValue hsource htarget hgraph
  have hexact := sourceSensitiveCostRefinement funRel n
    hsource htarget hgraph
  exact ⟨Nat.le_of_eq hexact.1, Nat.le_of_eq hexact.2.2.2⟩

/-- One parametric theorem joins actual whole-pass output, both semantics,
their value graph, and the source-sensitive instruction-cost relation. -/
theorem loweringCostWitness (funRel : Sim.FunctionRel) (n : Nat) :
    (lowerAllAction sourceDeclarations (sourceNat n) .shared
        (4 * n + 2)).run {} = .ok ([], targetCode n) {} ∧
      IxIR0.eval sourceCtx (n + 3) [] (sourceNat n) =
        .ok (sourceValue n) ∧
      runMain targetCtx (targetCode n) (n + 2) =
        .ok (targetStore n, .loc n) ∧
      Sim.ValueGraph funRel (targetStore n) (sourceValue n) (.loc n) ∧
      SourceSensitiveCostSpec (sourceValue n)
        (costObservation (targetStore n)) := by
  refine ⟨lowerAllAction_run n, sourceEval_exact n, runMain_exact n,
    valueGraph_exact funRel n, ?_⟩
  exact (sourceSensitiveCostRefinement funRel n)
    (sourceEval_exact n) (runMain_exact n) (valueGraph_exact funRel n)

end Ix.Compiler.IxIR1.CostModel
