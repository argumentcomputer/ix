import Aiur.Scalar

open Aiur.Scalar Aiur.Scalar.Circuit

namespace SemanticsExample

def source : Program Nat := scalar_aiur% "fn identity(x) { x }"

-- A source evaluation proof needs neither fuel nor decidable equality on the field.
theorem identity_evaluates [Field F] (x : F) :
    EvalCall (source.toField F) "identity" [x] x := by
  refine EvalCall.intro (defn := ⟨"identity", ["x"], .var "x"⟩) ?_ rfl ?_
  · simp [Program.findFunction?, source, Program.toField, Program.map, Function.map, Expr.map]
  · exact .var rfl

def identityChip (F : Type) : Chip F := {
  name := "identity", arity := 1, numVars := 2, output := 1
  constraints := [.sub (.var 1) (.var 0)]
  sends := []
}

def system (F : Type) : System F := ⟨[identityChip F]⟩

theorem source_compiles [Field F] [DecidableEq F] :
    compile (source.toField F) = .ok (system F) := by
  have checked : typecheck (source.toField F) = .ok () := by
    simp [typecheck, source, Program.toField, Program.map, Function.map, Expr.map, inferType]
    rfl
  simp only [compile, checked]
  simp [source, Program.toField, Program.map, Function.map, Expr.map,
    Compiler.lowerFunction, Compiler.lowerExpr, StateT.run, StateT.pure,
    bind, pure, Except.bind, Except.pure, system, identityChip]

-- This is a closed leaf: the equation holds and there are no call premises.
def identity_derivation [Field F] [DecidableEq F] (x : F) :
    Derivation (system F) ⟨"identity", [x], x⟩ :=
  .node (identityChip F) ⟨"identity", [x, x]⟩ rfl
    (by simp [Chip.ValidRow, identityChip, Chip.wellFormed, ArithExpr.inBounds,
      Satisfies, ArithExpr.denote, Row.assignment]) .nil

theorem identity_circuit_evaluates [Field F] [DecidableEq F] (x : F) :
    CircuitEvaluates (system F) "identity" [x] x :=
  ⟨identity_derivation x⟩

-- The proved compiler theorem applies to any closed tree for the compiled system.
theorem identity_result_unique [Field F] [DecidableEq F] (x y : F)
    (derives : CircuitEvaluates (system F) "identity" [x] y) : y = x :=
  (compiler_sound source_compiles "identity" [x] y derives).deterministic (identity_evaluates x)

-- Flattening retains the assignment used by the proof.
example [Field F] [DecidableEq F] (x : F) :
    (identity_derivation x).rows = [⟨"identity", [x, x]⟩] := rfl

end SemanticsExample
