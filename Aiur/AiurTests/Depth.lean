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

end AiurDepthTests
