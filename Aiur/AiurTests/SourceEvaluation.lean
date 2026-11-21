import Aiur.Generic
import Mathlib.Algebra.Field.Rat

namespace AiurSourceEvaluationTests
open Aiur
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

-- Checking records type information without inlining source const references.
def program : Generic.Program Nat := aiur% "
type Four = [Field; 4];
const zeros = [0; 4];
fn repeated() -> Four { [0; 4] }
fn referenced() -> Four { zeros }
fn pattern(a: Four) -> Field { match a { [0; 4] => 1, _ => 2 } }
fn slice() -> [Field; 2] { [1, 2, 3, 4][1..3] }
fn stored() -> [&Field; 0] { [&7; 0] }
fn read() -> Field { let &x = &9; x }
fn key() -> Field { hint::<Field>(*(&3)) }
"

#guard program.aliases.length == 1 && program.consts.length == 1
#guard (program.findFunction? "referenced").map (·.body) ==
  some (.global "zeros" (some (.array .field 4)))
#guard (program.findFunction? "repeated").any fun f => match f.body with
  | .repeat (.literal 0) 4 => true
  | _ => false
#guard (program.findFunction? "pattern").any fun f => match f.body with
  | .matchValue _ ((.repeat (.literal 0) 4, _) :: _) => true
  | _ => false
#guard (program.findFunction? "slice").any fun f => match f.body with
  | .slice (.array _) 1 (some 3) => true
  | _ => false
#guard (program.findFunction? "read").any fun f => match f.body with
  | .letValue (.load (.bind "x")) (.store _) (.var "x") => true
  | _ => false

-- These fuel bounds distinguish native source execution from desugared code.
#guard (do
  let s ← Generic.prepare (program.toField Rat)
  s.run "repeated" [] 2) == .ok (.tuple [0, 0, 0, 0], [])
#guard (do
  let s ← Generic.prepare (program.toField Rat)
  s.coreRun "repeated" [] 2) == .error (reprStr EvalError.outOfFuel)
#guard (do
  let s ← Generic.prepare (program.toField Rat)
  s.run "slice" [] 3) == .ok (.tuple [2, 3], [])
#guard (do
  let s ← Generic.prepare (program.toField Rat)
  s.run "stored" [] 3) == .ok (.tuple [], [7])
#guard (do
  let s ← Generic.prepare (program.toField Rat)
  s.run "read" [] 3) == .ok (9, [9])
#guard (do
  let s ← Generic.prepare (program.toField Rat)
  let q ← Generic.specialize s ["repeated", "slice", "stored", "read"]
  q.run "repeated" [] 2) == .ok (.tuple [0, 0, 0, 0], [])
#guard (do
  let s ← Generic.prepare (program.toField Rat)
  let q ← Generic.specialize s ["repeated"]
  return q.instances.any fun (name, f) => name == "repeated" && f.any fun (f : Generic.SourceFunction Rat) => match f.body with
    | .repeat (.literal 0) 4 => true
    | _ => false) == .ok true

-- A hint's key is executed ordinarily; only the supplied witness is nondeterministic.
#guard (do
  let s ← Generic.prepare (program.toField Rat)
  let q ← Generic.specialize s ["key"]
  let provider := s.checkedHints fun _ key => match key with
    | .field 3 => .ok (.field 12)
    | _ => .error .unavailable
  q.run "key" [] (hints := provider)) == .ok (12, [3])

-- The predicate exposes the native operation, including the zero-repeat heap.
example (world : Generic.SourceSemantics.World Rat) :
    Generic.SourceSemantics.EvalExpr world [] []
      (.repeat (.store (.literal 7)) 0) [] (.tuple []) [7] :=
  .repeat (.store .literal)

-- Every successful generic run transfers to the finite specialization.
example [Field F] [DecidableEq F] {s : Generic.Source F}
    (q : Generic.Specialized s entries) (selected : name ∈ entries)
    {hints : s.HintProvider}
    (executed : s.run name args fuel hints = .ok (value, heap)) :
    q.EvalCall name args value := by
  obtain ⟨entry, evaluated⟩ := Generic.Source.run_spec executed
  exact (q.evalCall_iff selected).mp ⟨entry, heap, evaluated⟩

-- A successful specialized source run reflects back to the generic predicate.
example [Field F] [DecidableEq F] {s : Generic.Source F}
    (q : Generic.Specialized s entries) (selected : name ∈ entries)
    {hints : s.HintProvider}
    (executed : q.run name args fuel hints = .ok (value, heap)) :
    s.EvalCall name args value :=
  (q.evalCall_iff selected).mpr (Generic.Specialized.evalCall_of_run executed)

/-- info: 'Aiur.Generic.SourceSemantics.evalExpr_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.SourceSemantics.evalExpr_spec
/-- info: 'Aiur.Generic.SourceSemantics.let_load_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.SourceSemantics.let_load_iff
/-- info: 'Aiur.Generic.Specialized.sourceAgreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.Specialized.sourceAgreement

/-- info: 'Aiur.Generic.SourceSemantics.expression_preparation_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.SourceSemantics.expression_preparation_iff
/-- info: 'Aiur.Generic.Preparation.pattern_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.Preparation.pattern_match
/-- info: 'Aiur.Generic.PatternLowering.PlanTree.attempt_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.PatternLowering.PlanTree.attempt_sound
/-- info: 'Aiur.Generic.PatternLowering.PlanTree.attempt_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.PatternLowering.PlanTree.attempt_complete
/-- info: 'Aiur.Generic.PatternLowering.PlanTree.match_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.PatternLowering.PlanTree.match_iff
/-- info: 'Aiur.Generic.PatternLowering.lowerLet_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.PatternLowering.lowerLet_iff
/-- info: 'Aiur.Generic.PatternLowering.lowerMatch_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.PatternLowering.lowerMatch_iff
/-- info: 'Aiur.Generic.Specialized.native_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.Specialized.native_complete
/-- info: 'Aiur.Generic.Specialized.checker_heap_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.Specialized.checker_heap_complete
/-- info: 'Aiur.Generic.Specialized.checkerMemo_heap_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.Specialized.checkerMemo_heap_complete
/-- info: 'Aiur.Generic.Specialized.native_entry_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.Specialized.native_entry_iff
/-- info: 'Aiur.Generic.Specialized.native_evalCall_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.Specialized.native_evalCall_iff
/-- info: 'Aiur.Generic.Specialized.checker_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.Specialized.checker_heap_sound
/-- info: 'Aiur.Generic.Specialized.checkerMemo_acyclic_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.Specialized.checkerMemo_acyclic_heap_sound
/-- info: 'Aiur.Generic.Compiled.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.Compiled.check_sound
/-- info: 'Aiur.Generic.Compiled.checkMemo_acyclic_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.Compiled.checkMemo_acyclic_sound

-- Lowered empty projections alone would accept a scalar. The compiler's
-- source-scope certificate still requires an array operand and valid bounds.
#guard (Generic.Expr.slice (.literal (0 : Rat)) 0 (some 0)).checkLowerTypes { functions := [] } [] [] == none
#guard (Generic.Expr.slice (.array ([] : List (Generic.Expr Rat))) 0 (some 0)).checkLowerTypes { functions := [] } [] [] == some (.tuple [])
#guard (Generic.Expr.slice (.array ([] : List (Generic.Expr Rat))) 1 (some 1)).checkLowerTypes { functions := [] } [] [] == none

-- Const expansion is a compiler operation with a proof on the independent
-- native predicate, including the exact resulting heap.
example [Field F] [DecidableEq F] (s : Generic.Source F)
    (expanded : Generic.Preparation.expression s.program depth types expr = .ok prepared) :
    Generic.SourceSemantics.EvalExpr s.world types locals expr before value after ↔
      Generic.SourceSemantics.EvalExpr s.world [] locals prepared before value after :=
  Generic.SourceSemantics.expression_preparation_iff s.program s.world
    (fun _ _ => rfl) rfl depth types expr expanded locals before value after

end AiurSourceEvaluationTests
