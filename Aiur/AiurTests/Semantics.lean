import Aiur.Scalar
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert

open Aiur.Scalar Aiur.Scalar.Circuit

namespace AiurSemanticsTests

-- Both directions of compiler correctness must remain free of admitted proofs.
/-- info: 'Aiur.Scalar.compiler_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Scalar.compiler_sound

/-- info: 'Aiur.Scalar.evaluation_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Scalar.evaluation_complete

/-- info: 'Aiur.Scalar.compiler_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Scalar.compiler_correct

-- The source relation needs field laws, but no decidable equality or fuel.
example [Field F] (x : F) :
    EvalExpr ⟨[]⟩ [("x", x)] (.neg (.binary .add (.var "x") (.literal 1))) (-(x + 1)) :=
  .neg (.add (.var rfl) .literal)

def source : Program Nat := scalar_aiur% "
fn square(x) { x * x }
fn main(x, y) { square(x / y) }
"

theorem square_evaluates : EvalCall (source.toField Rat) "square" [3] 9 := by
  refine EvalCall.intro
    (defn := ⟨"square", ["x"], .binary .mul (.var "x") (.var "x")⟩) ?_ rfl ?_
  · simp [Program.findFunction?, source, Program.toField, Program.map, Function.map, Expr.map]
  rw [show (9 : Rat) = 3 * 3 by norm_num]
  exact .mul (.var rfl) (.var rfl)

theorem main_evaluates : EvalCall (source.toField Rat) "main" [6, 2] 9 := by
  refine EvalCall.intro
    (defn := ⟨"main", ["x", "y"], .call "square" [.binary .div (.var "x") (.var "y")]⟩) ?_ rfl ?_
  · simp [Program.findFunction?, source, Program.toField, Program.map, Function.map, Expr.map]
  apply EvalExpr.call (values := [3]) _ square_evaluates
  apply EvalArgs.cons _ .nil
  rw [show (3 : Rat) = 6 / 2 by norm_num]
  exact .div (.var rfl) (.var rfl) (by decide)

example : ¬ EvalCall (source.toField Rat) "main" [6, 2] 10 := by
  intro wrong
  have := main_evaluates.deterministic wrong
  contradiction

example : ¬ EvalCall (source.toField Rat) "square" [] result := by
  intro evaluated
  obtain ⟨defn, lookup, arity⟩ := evaluated.function_exists
  cases lookup
  cases arity

-- Division by zero and an uncovered match have no successful derivations.
example (program : Program Rat) (result : Rat) :
    ¬ EvalExpr program [] (.binary .div (.literal 1) (.literal 0)) result := by
  intro evaluated
  cases evaluated with
  | div left right nonzero =>
      cases left
      cases right
      exact nonzero rfl

example (program : Program Rat) (result : Rat) :
    ¬ EvalExpr program [] (.matchValue (.literal 0) [(.literal 1, .literal 7)]) result := by
  intro evaluated
  cases evaluated with
  | matchValue scrutinee selected _ =>
      cases scrutinee
      cases selected with
      | skip _ rest => cases rest

-- Wildcards stop matching, even if a later branch would divide by zero.
example (program : Program Rat) :
    EvalExpr program []
      (.matchValue (.literal 0)
        [(.wildcard, .literal 11), (.literal 0, .binary .div (.literal 1) (.literal 0))]) 11 :=
  .matchValue .literal .wildcard .literal

def recursive : Program Nat := scalar_aiur% "
fn even(n) { match n { 0 => 1, _ => odd(n - 1) } }
fn odd(n) { match n { 0 => 0, _ => even(n - 1) } }
"

private theorem even_zero : EvalCall (recursive.toField Rat) "even" [0] 1 := by
  apply EvalCall.intro (defn := (recursive.toField Rat).functions[0]) rfl rfl
  conv => arg 3; simp [recursive, Program.toField, Program.map, Function.map, Expr.map, Pattern.map]
  exact .matchValue (.var rfl) .literal .literal

private theorem odd_one : EvalCall (recursive.toField Rat) "odd" [1] 1 := by
  apply EvalCall.intro (defn := (recursive.toField Rat).functions[1]) rfl rfl
  conv => arg 3; simp [recursive, Program.toField, Program.map, Function.map, Expr.map, Pattern.map]
  refine EvalExpr.matchValue (.var rfl) (.skip (by decide) .wildcard) ?_
  refine EvalExpr.call (values := [0]) (.cons ?_ .nil) even_zero
  rw [show (0 : Rat) = 1 - 1 by norm_num]
  exact .sub (.var rfl) .literal

theorem even_two : EvalCall (recursive.toField Rat) "even" [2] 1 := by
  apply EvalCall.intro (defn := (recursive.toField Rat).functions[0]) rfl rfl
  conv => arg 3; simp [recursive, Program.toField, Program.map, Function.map, Expr.map, Pattern.map]
  refine EvalExpr.matchValue (.var rfl) (.skip (by decide) .wildcard) ?_
  refine EvalExpr.call (values := [1]) (.cons ?_ .nil) odd_one
  conv => arg 4; equals (2 : Rat) - 1 => norm_num
  exact .sub (.var rfl) .literal

-- Completeness builds the recursive tree, including active wildcard inverses.
example : ∃ system, compile (recursive.toField Rat) = .ok system ∧
    CircuitEvaluates system "even" [2] 1 := by
  have succeeds : (compile (recursive.toField Rat)).isOk = true := by decide +kernel
  cases compiled : compile (recursive.toField Rat) with
  | error error => simp [compiled, Except.isOk, Except.toBool] at succeeds
  | ok system => exact ⟨system, rfl, evaluation_complete compiled even_two⟩

def inactiveBranches : Program Nat := scalar_aiur% "
fn choose(x) {
  match x {
    0 => match x { 0 => 1 / 0, _ => looping(x) },
    1 => 7,
    2 => 1 / 0,
    _ => 9,
  }
}
fn looping(x) { looping(x) }
"

private theorem choose_literal : EvalCall (inactiveBranches.toField Rat) "choose" [1] 7 := by
  apply EvalCall.intro (defn := (inactiveBranches.toField Rat).functions[0]) rfl rfl
  conv => arg 3; simp [inactiveBranches, Program.toField, Program.map, Function.map, Expr.map, Pattern.map]
  exact .matchValue (.var rfl) (.skip (by decide) .literal) .literal

private theorem choose_default : EvalCall (inactiveBranches.toField Rat) "choose" [3] 9 := by
  apply EvalCall.intro (defn := (inactiveBranches.toField Rat).functions[0]) rfl rfl
  conv => arg 3; simp [inactiveBranches, Program.toField, Program.map, Function.map, Expr.map, Pattern.map]
  exact .matchValue (.var rfl)
    (.skip (by decide) (.skip (by decide) (.skip (by decide) .wildcard))) .literal

-- Inactive arms before and after the selected arm need no evaluation proofs,
-- even when they contain nested matches, division by zero, and nontermination.
example : ∃ system, compile (inactiveBranches.toField Rat) = .ok system ∧
    CircuitEvaluates system "choose" [1] 7 ∧ CircuitEvaluates system "choose" [3] 9 := by
  have succeeds : (compile (inactiveBranches.toField Rat)).isOk = true := by decide +kernel
  cases compiled : compile (inactiveBranches.toField Rat) with
  | error error => simp [compiled, Except.isOk, Except.toBool] at succeeds
  | ok system =>
      exact ⟨system, rfl, evaluation_complete compiled choose_literal,
        evaluation_complete compiled choose_default⟩

def loopProgram : Program Rat := ⟨[⟨"loop", [], .call "loop" []⟩]⟩

theorem loop_never_evaluates (name : String) (args : List Rat) (result : Rat) :
    ¬ EvalCall loopProgram name args result := by
  intro evaluated
  induction evaluated using EvalCall.rec
    (motive_1 := fun _ expr _ _ => expr ≠ .call "loop" [])
    (motive_2 := fun _ _ _ _ => True) with
  | literal | var | neg | add | sub | mul | div | matchValue => intro equality; cases equality
  | call _ _ _ calleeIH => exact calleeIH.elim
  | nil | cons => trivial
  | intro lookup _ _ bodyIH =>
      simp only [Program.findFunction?, loopProgram, List.find?] at lookup
      split at lookup
      · cases lookup
        exact bodyIH rfl
      · cases lookup

def squareChip : Chip Rat := {
  name := "square", arity := 1, numVars := 2, output := 1
  constraints := [.sub (.var 1) (.mul (.var 0) (.var 0))]
  sends := []
}

def mainChip : Chip Rat := {
  name := "main", arity := 2, numVars := 5, output := 2
  constraints := [
    .mul (.const 1) (.sub (.mul (.var 1) (.var 3)) (.const 1)),
    .mul (.const 1) (.sub (.const 1) (.const 1)),
    .sub (.var 2) (.var 4)]
  sends := [⟨"square", [.mul (.var 0) (.var 3)], 4, .const 1⟩]
}

def system : System Rat := ⟨[squareChip, mainChip]⟩

-- The trees below use the actual output of the compiler.
theorem source_compiles : compile (source.toField Rat) = .ok system := by
  have checked : typecheck (source.toField Rat) = .ok () := by decide +kernel
  simp only [compile, checked]
  simp [source, Program.toField, Program.map, Function.map, Expr.map,
    Compiler.lowerFunction, Compiler.lowerExpr, Compiler.lowerArgs, Compiler.boolean,
    StateT.run, StateT.bind, StateT.pure, bind, pure, Except.bind, Except.pure,
    system, squareChip, mainChip]
  rfl

def squareTree : Derivation system ⟨"square", [3], 9⟩ :=
  .node squareChip ⟨"square", [3, 9]⟩ rfl
    (by norm_num [Chip.ValidRow, squareChip, Chip.wellFormed, ArithExpr.inBounds,
      Satisfies, ArithExpr.denote, Row.assignment]) .nil

example : ¬ squareChip.ValidRow ⟨"square", [3, 10]⟩ := by
  norm_num [Chip.ValidRow, squareChip, Satisfies, ArithExpr.denote, Row.assignment]

def mainTree : Derivation system ⟨"main", [6, 2], 9⟩ :=
  .node mainChip ⟨"main", [6, 2, 9, 1 / 2, 9]⟩ rfl
    (by norm_num [Chip.ValidRow, mainChip, Chip.wellFormed, ArithExpr.inBounds,
      Send.inBounds, Satisfies, ArithExpr.denote, Row.assignment])
    (by
      convert Derivations.cons squareTree Derivations.nil using 1
      norm_num [Chip.premises, mainChip, Send.message, ArithExpr.denote, Row.assignment,
        List.filterMap_cons, List.filterMap_nil, List.getElem_cons_zero, List.getElem_cons_succ]
      decide +kernel)

example : CircuitEvaluates system "main" [6, 2] 9 := ⟨mainTree⟩

-- Soundness rules out a wrong result for every closed tree.
example (result : Rat) (derives : CircuitEvaluates system "main" [6, 2] result) : result = 9 :=
  (compiler_sound source_compiles "main" [6, 2] result derives).deterministic main_evaluates

-- A disabled send requires no child proof, including a call to this same chip.
def disabledChip : Chip Rat := {
  name := "disabled", arity := 0, numVars := 1, output := 0
  constraints := [.sub (.var 0) (.const 7)]
  sends := [⟨"disabled", [], 0, .const 0⟩]
}

example : Derives ⟨[disabledChip]⟩ ⟨"disabled", [], 7⟩ :=
  ⟨.node disabledChip ⟨"disabled", [7]⟩ rfl
    (by simp [Chip.ValidRow, disabledChip, Chip.wellFormed, ArithExpr.inBounds,
      Send.inBounds, Satisfies, ArithExpr.denote, Row.assignment]) .nil⟩

-- Two identical calls require two child occurrences and flatten to two callee rows.
def twiceChip : Chip Rat := {
  name := "twice", arity := 1, numVars := 4, output := 1
  constraints := [
    .mul (.const 1) (.sub (.const 1) (.const 1)),
    .mul (.const 1) (.sub (.const 1) (.const 1)),
    .sub (.var 1) (.add (.var 2) (.var 3))]
  sends := [⟨"square", [.var 0], 2, .const 1⟩, ⟨"square", [.var 0], 3, .const 1⟩]
}

def twiceSystem : System Rat := ⟨[squareChip, twiceChip]⟩

def twiceTree : Derivation twiceSystem ⟨"twice", [3], 18⟩ := by
  have child : Derivation twiceSystem ⟨"square", [3], 9⟩ :=
    .node squareChip ⟨"square", [3, 9]⟩ rfl
      (by norm_num [Chip.ValidRow, squareChip, Chip.wellFormed, ArithExpr.inBounds,
        Satisfies, ArithExpr.denote, Row.assignment]) .nil
  exact .node twiceChip ⟨"twice", [3, 18, 9, 9]⟩ rfl
    (by norm_num [Chip.ValidRow, twiceChip, Chip.wellFormed, ArithExpr.inBounds,
      Send.inBounds, Satisfies, ArithExpr.denote, Row.assignment])
    (.cons child (.cons child .nil))

example : twiceTree.rows =
    [⟨"twice", [3, 18, 9, 9]⟩, ⟨"square", [3, 9]⟩, ⟨"square", [3, 9]⟩] := rfl

-- An always-enabled recursive call cannot provide its own justification.
def loopChip : Chip Rat := {
  name := "loop", arity := 0, numVars := 1, output := 0
  constraints := []
  sends := [⟨"loop", [], 0, .const 1⟩]
}

example (result : Rat) : ¬ CircuitEvaluates ⟨[loopChip]⟩ "loop" [] result := by
  apply not_derives_of_no_leaves
  intro chip row lookup _
  simp only [System.findChip?, List.find?] at lookup
  split at lookup
  · cases lookup
    simp [Chip.premises, loopChip, ArithExpr.denote]
  · cases lookup

end AiurSemanticsTests
