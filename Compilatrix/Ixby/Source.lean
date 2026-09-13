import Compilatrix.Ixby.Certificate
import Compilatrix.Pipeline

/-! Ixon enters through the existing checked erasure boundary. Raw erasure
keys are deliberately retained: the immutable target does not need the native
backend's second address image or any ownership lowering. -/

namespace Compilatrix.Ixby

open Ixon (Address Constant)

/-- Apply the selected closed Ixon definition to runtime arguments in their
external order. The source evaluator uses the reverse de Bruijn environment. -/
def entryExpression (main : Address) (parameters : Nat) : IxIR0.Expr :=
  ((List.range parameters).reverse.map IxIR0.Expr.var).foldl IxIR0.Expr.app (.ref main)

structure IxonCompilation (constants : List (Address × Constant)) (main : Address)
    (sourceConfig : Pipeline.Config) (eraseFuel : Nat) (config : Config) (parameters : Nat) where
  erasure : Pipeline.ValidatedErasure constants main sourceConfig eraseFuel
  target : Compiled
    { declarations := erasure.erasure.result.raw, main := entryExpression main parameters, parameters }
    config

def compileIxon (constants : List (Address × Constant)) (main : Address)
    (sourceConfig : Pipeline.Config := {}) (config : Config := {}) (parameters : Nat := 0)
    (checkFuel : Nat := Ixon.UsageCheck.defaultFuel) (eraseFuel : Nat := Erase.defaultFuel)
    (validateFuel : Nat := Erase.defaultFuel) :
    Except String (IxonCompilation constants main sourceConfig eraseFuel config parameters) := do
  let erasure ← (Pipeline.eraseValidatedWithTrace constants main sourceConfig
    checkFuel eraseFuel validateFuel).mapError reprStr
  let target ← compile {
    declarations := erasure.erasure.result.raw,
    main := entryExpression main parameters, parameters } config
  return { erasure, target }

end Compilatrix.Ixby
