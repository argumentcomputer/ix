import Aiur.Optimized.Depth
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.FinCases

/-! The depth pass closes the memo-cycle gap on the canonical counterexample,
`fn loop(x: Field) -> Field { loop(x) }`, over the physical (wire) circuit model.
Compare `AiurTests/Memo.lean`, where the scalar model accepts a cyclic graph
for every claimed result and no acyclic one exists. -/

open Aiur Aiur.Circuit Aiur.Optimized

namespace AiurDepthTests

/-- The physical chip for `loop`: column 0 is `x`, column 1 is the self-call's
result and the output. -/
def loopChip : Chip Rat := {
  name := "loop"
  inputs := [⟨.field, [0]⟩]
  output := ⟨.field, [.var 1]⟩
  numVars := 2
  constraints := []
  sends := [⟨"loop", [⟨.field, [.var 0]⟩], ⟨.field, [1]⟩, .const 1⟩]
  memory := [] }

def loopSystem : System Rat := ⟨[loopChip], [], [], []⟩

def loopClaim (x result : Rat) : Message Rat := ⟨"loop", [⟨.field, [x]⟩], ⟨.field, [result]⟩⟩

/-- The forged row `loop(0) = 42`, provided twice: once for its own self-call
and once for the public claim. -/
def forged : WeightedRow Rat := ⟨⟨"loop", [0, 42]⟩, 2⟩

/-- Without the depth pass the Lean memo checker accepts the forgery, exactly
like today's STARK verifier (`crates/aiur/src/trace/stark/tests/memo_cycle.rs`). -/
example : loopSystem.checkMemo ⟨[]⟩ (loopClaim 0 42) [forged] = .ok () := by decide +kernel

/-- One self-referencing node accepts every result. -/
def cyclicGraph (result : Rat) : MemoDerivation loopSystem ⟨[]⟩ (loopClaim 0 result) := {
  size := 1
  node := fun _ => .node loopChip ⟨"loop", [0, result]⟩ rfl (by
    simp [Chip.ValidRow, loopChip, Chip.wellFormed, Send.inBounds, MemoryLookup.inBounds,
      Scalar.Circuit.ArithExpr.inBounds, ArithExpr.inBounds, Satisfies, Scalar.Circuit.Satisfies])
  root := 0
  root_claim := by
    simp [RuleInstance.conclusion, Chip.receive, loopChip, loopClaim, WireValue.map,
      Row.assignment, Scalar.Circuit.Row.assignment, Scalar.Circuit.ArithExpr.denote]
  target := fun _ _ => 0
  target_claim := by
    intro i j
    fin_cases j
    simp [RuleInstance.conclusion, RuleInstance.premises, Chip.receive, Chip.premises, loopChip,
      Send.message, WireValue.map, Row.assignment, Scalar.Circuit.Row.assignment,
      Scalar.Circuit.ArithExpr.denote] }

example (result : Rat) : MemoDerives loopSystem ⟨[]⟩ (loopClaim 0 result) := ⟨cyclicGraph result⟩

/-- No finite derivation of any `loop` claim exists. -/
theorem loop_underivable (rom : WireROM Rat) (message : Message Rat) :
    ¬ Derives loopSystem rom message := by
  apply not_derives_of_no_leaves (by rfl)
  intro chip row lookup _
  simp only [System.findChip?, loopSystem, List.find?_cons, List.find?_nil] at lookup
  split at lookup
  · cases lookup
    simp [Chip.premises, loopChip, Scalar.Circuit.ArithExpr.denote]
  · cases lookup

/-- `loop` is recursive; its self-call is an exact slot (callee depth `d - 1`). -/
def depthConfig : Depth.Config :=
  { plans := [("loop", { recursive := true, slots := [.exact] })], ranks := [("loop", 0)] }

theorem certified : Depth.Certified depthConfig loopSystem := by decide +kernel

/-- The depth chip provides `loop(x, d)` and demands `loop(x, d - 1)`. -/
example : (Depth.system depthConfig loopSystem).chips =
    [{ loopChip with
      inputs := [⟨.field, [0]⟩, ⟨.field, [2]⟩]
      numVars := 3
      sends := [⟨"loop", [⟨.field, [.var 0]⟩, ⟨.field, [.sub (.var 2) (.const 1)]⟩],
        ⟨.field, [1]⟩, .const 1⟩] }] := rfl

theorem loop_named (root : Message Rat) (channel : root.channel = "loop") :
    root.channel ∉ depthConfig.names := by
  rw [channel]
  decide +kernel

/-- Under the depth pass no memo graph for `loop` exists at all, cyclic or not,
for any depth word in the root. Every graph is acyclic (characteristic zero
admits any row bound), so it unfolds to a finite derivation, which erases to a
finite derivation of `loop`, which does not exist. -/
theorem no_memo_graph (rom : WireROM Rat) (root : Message Rat) (channel : root.channel = "loop")
    (graph : MemoDerivation (Depth.system depthConfig loopSystem) rom root) : False := by
  have acyclic := Depth.acyclic certified.facts graph le_rfl
    (fun n positive _ => Nat.cast_ne_zero.mpr positive.ne')
  exact loop_underivable rom _ (Depth.derives_erase certified.facts
    (graph.derives_of_acyclic acyclic) (loop_named root channel))

/-- Hence the memo checker rejects every trace for `loop` under the depth pass,
the forgery above included, whatever depth word the root claims. -/
theorem checkMemo_rejects (rom : WireROM Rat) (root : Message Rat) (channel : root.channel = "loop")
    (rows : List (WeightedRow Rat)) :
    (Depth.system depthConfig loopSystem).checkMemo rom root rows ≠ .ok () := by
  intro checked
  exact loop_underivable rom _ (Depth.checkMemo_sound certified le_rfl
    (fun n positive _ => Nat.cast_ne_zero.mpr positive.ne') checked (loop_named root channel))

/-! ### The deployed shape: activated plan rows -/

/-- `loop` as the prover commits to it today: one ungrouped, activated chip. -/
def plainPlan : Grouping.Plan loopSystem (fun _ => .ok 0) :=
  ⟨loopSystem.chips, [], fun chip member => by
      simp only [loopSystem, List.mem_singleton] at member
      subst member
      rfl,
    by simp, fun chip member => Or.inl member⟩

/-- The plan checker models the deployed circuit: it accepts the forged
activated row (`x`, the self-call result, selector `1`) provided twice. -/
example : plainPlan.checkMemo ⟨[]⟩ (loopClaim 0 42) [⟨⟨"loop", [0, 42, 1]⟩, 2⟩] = .ok () := by
  decide +kernel

/-- The same plan over the depth pass. -/
def depthPlan : Grouping.Plan (Depth.system depthConfig loopSystem) (fun _ => .ok 0) :=
  ⟨(Depth.system depthConfig loopSystem).chips, [], fun chip member => by
      simp only [Depth.system, loopSystem, List.map_cons, List.map_nil, List.mem_singleton] at member
      subst member
      rfl,
    by simp, fun chip member => Or.inl member⟩

theorem depthActivated : depthPlan.WellFormedActivation := by decide +kernel

/-- Under the depth pass the grouped, activated memo checker rejects every trace
for `loop`, whatever depth word the root claims. -/
theorem plan_checkMemo_rejects (rom : WireROM Rat) (root : Message Rat)
    (channel : root.channel = "loop") (rows : List (WeightedRow Rat)) :
    depthPlan.checkMemo rom root rows ≠ .ok () := by
  intro checked
  exact loop_underivable rom _ (Depth.plan_checkMemo_sound certified depthPlan depthActivated le_rfl
    (fun n positive _ => Nat.cast_ne_zero.mpr positive.ne') checked (loop_named root channel))

/-- info: 'AiurDepthTests.plan_checkMemo_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms plan_checkMemo_rejects

/-- info: 'AiurDepthTests.checkMemo_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkMemo_rejects

/-- info: 'Aiur.Optimized.Depth.checkMemo_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Depth.checkMemo_sound

/-- info: 'Aiur.Optimized.Depth.acyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Depth.acyclic

/-- info: 'Aiur.Optimized.Physical.Prepared.depth_native_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Physical.Prepared.depth_native_heap_sound

/-! ### Terminating recursion and the grouped `Plan.checkMemo` path -/

/-- `count(0) = 7`, `count(x) = count(x - 1)` otherwise. Columns: `x`, `r`, `s` (`s = 1` when recursing). -/
def countChip : Chip Rat := {
  name := "count"
  inputs := [⟨.field, [0]⟩]
  output := ⟨.field, [.var 1]⟩
  numVars := 3
  constraints := [
    .mul (.var 2) (.sub (.var 2) (.const 1)),
    .mul (.sub (.const 1) (.var 2)) (.var 0),
    .mul (.sub (.const 1) (.var 2)) (.sub (.var 1) (.const 7))]
  sends := [⟨"count", [⟨.field, [.sub (.var 0) (.const 1)]⟩], ⟨.field, [1]⟩, .var 2⟩]
  memory := [] }

def countSys : System Rat := ⟨[countChip], [], [], []⟩

def countCfgE : Depth.Config :=
  { limbs := [], plans := [("count", { recursive := true, slots := [.exact] })], ranks := [("count", 0)] }

def countCfgG : Depth.Config :=
  { limbs := [2], plans := [("count", { recursive := true, slots := [.gap] })], ranks := [("count", 0)] }

theorem countCertE : Depth.Certified countCfgE countSys := by decide +kernel
theorem countCertG : Depth.Certified countCfgG countSys := by decide +kernel

def countPlanOf (cfg : Depth.Config) : Grouping.Plan (Depth.system cfg countSys) (fun _ => .ok 0) :=
  ⟨(Depth.system cfg countSys).chips, [], fun chip member => by
      simp only [Depth.system, countSys, List.map_cons, List.map_nil, List.mem_singleton] at member
      subst member
      rfl,
    by simp, fun chip member => Or.inl member⟩

def countRootE : Message Rat := ⟨"count", [⟨.field, [1]⟩, ⟨.field, [1]⟩], ⟨.field, [7]⟩⟩

def countRowsE : List (WeightedRow Rat) :=
  [ ⟨⟨"count", [1, 7, 1, 1, 1]⟩, 1⟩, ⟨⟨"count", [0, 7, 0, 0, 1]⟩, 1⟩ ]

example : (countPlanOf countCfgE).checkMemo ⟨[]⟩ countRootE countRowsE = .ok () := by decide +kernel

def countRootG : Message Rat := ⟨"count", [⟨.field, [1]⟩, ⟨.field, [3]⟩], ⟨.field, [7]⟩⟩

def countRowsG (lo : Rat) : List (WeightedRow Rat) :=
  [ ⟨⟨"count", [1, 7, 1, 3, lo, 1]⟩, 1⟩, ⟨⟨"count", [0, 7, 0, 0, 0, 1]⟩, 1⟩ ]

example : (countPlanOf countCfgG).checkMemo ⟨[]⟩ countRootG (countRowsG 2) = .ok () := by decide +kernel
example : (countPlanOf countCfgG).checkMemo ⟨[]⟩ countRootG (countRowsG 5) ≠ .ok () := by decide +kernel
example : (countPlanOf countCfgE).checkMemo ⟨[]⟩ ⟨"count", [⟨.field, [1]⟩, ⟨.field, [1]⟩], ⟨.field, [9]⟩⟩ countRowsE ≠ .ok () := by
  decide +kernel

def countPadRow : Row Rat := ⟨"count", [0, 0, 0, 0, 0]⟩

example : (countPlanOf countCfgE).checkMemo ⟨[]⟩ countRootE (countRowsE ++ [⟨countPadRow, 0⟩]) = .ok () := by decide +kernel
example : (countPlanOf countCfgE).checkMemo ⟨[]⟩ countRootE (countRowsE ++ [⟨countPadRow, 3⟩]) ≠ .ok () := by decide +kernel

def otherChip : Chip Rat := {
  name := "other"
  inputs := [⟨.field, [0]⟩]
  output := ⟨.field, [.var 0]⟩
  numVars := 1
  constraints := []
  sends := []
  memory := [] }

def groupedSys : System Rat := ⟨[countChip, otherChip], [], [], []⟩

def groupedCfg : Depth.Config :=
  { limbs := []
    plans := [("count", { recursive := true, slots := [.exact] }), ("other", {})]
    ranks := [("count", 0), ("other", 0)] }

def groupedId (name : String) : Except String Nat :=
  if name == "count" then .ok 0 else if name == "other" then .ok 1 else .error s!"unknown {name}"

def checkGroupedCases : Bool :=
  match (do
    unless Depth.certify groupedCfg groupedSys do throw "not certified"
    let system := Depth.system groupedCfg groupedSys
    let checked ← Grouping.compile "g" groupedId system.chips
    let plan ← Grouping.preparePlan system groupedId [⟨system.chips, checked⟩]
    let g := checked.layout
    let some m := g.members.find? (·.name == "count") | throw "no member"
    let row (a : List Rat) : Row Rat :=
      ⟨g.name, (List.range g.width).map fun v => (m.embedding v).denote (fun i => a.getD i 0)⟩
    let honest : List (WeightedRow Rat) := [⟨row [1, 7, 1, 1], 1⟩, ⟨row [0, 7, 0, 0], 1⟩]
    let pad : Row Rat := ⟨g.name, List.replicate g.width 0⟩
    let wrong : Message Rat := ⟨"count", [⟨.field, [1]⟩, ⟨.field, [1]⟩], ⟨.field, [9]⟩⟩
    let skewed : List (WeightedRow Rat) := [⟨row [1, 7, 1, 5], 1⟩, ⟨row [0, 7, 0, 0], 1⟩]
    let skewedRoot : Message Rat := ⟨"count", [⟨.field, [1]⟩, ⟨.field, [5]⟩], ⟨.field, [7]⟩⟩
    return (plan.checkMemo ⟨[]⟩ countRootE honest).isOk &&
      (plan.checkMemo ⟨[]⟩ countRootE (honest ++ [⟨pad, 0⟩])).isOk &&
      !(plan.checkMemo ⟨[]⟩ countRootE (honest ++ [⟨pad, 3⟩])).isOk &&
      !(plan.checkMemo ⟨[]⟩ wrong honest).isOk &&
      !(plan.checkMemo ⟨[]⟩ skewedRoot skewed).isOk : Except String Bool) with
  | .ok b => b
  | .error _ => false

#guard checkGroupedCases

end AiurDepthTests
