module

public import IxC.Kernel.CheckerBase
public import IxC.Kernel.Cached.ExprOpsC

@[expose] public section

/-! # Check the equations of bound definitions

The pin generator and tests use these checks after the ordinary declaration
checker has accepted the definitions and certificate theorems. The checks use
that environment's ordinary reduction rules. They install no new native rule.
-/

namespace Ix.Kernel

/-- Close a telescope whose free variables are numbered outermost first.
Each domain may mention only the preceding variables. -/
def closeRoleTelescope (lambda : Bool) (domains : List (Expr md))
    (body : Expr md) : Expr md :=
  (domains.zipIdx.reverse).foldl (fun body (domain, index) =>
    let domain := domain.abstractRange 0 index
    if lambda then .lam domain body default else .forallE domain body default)
    (body.abstractRange 0 domains.length)

/-- An unconditional equation's side, closed over its variables. -/
def Equation.closedSide (equation : Equation md) (side : Expr md) : Expr md :=
  closeRoleTelescope true equation.vars side

/-- The complete universally quantified equality, including its hypotheses. -/
def Equation.statement (equation : Equation md) : Expr md :=
  let equality := Expr.app (.app (.app (.const eqName [equation.level])
    equation.carrier) equation.lhs) equation.rhs
  closeRoleTelescope false (equation.vars ++ equation.hyps) equality

variable {m : Type → Type} [Monad m] [MonadExcept (CheckError md) m]

/-- Guard a closed term before passing it to the ordinary type checker. -/
def checkRoleTerm (env : Env md) (parameters : List LevelParam) (term : Expr md) : m Unit := do
  unless term.looseBVarsBounded 0 && !term.hasFvar &&
      term.allLevelParamsDefined parameters && term.constsResolve env do
    throw (.invalid "a role equation contains an open, unresolved, or undeclared term")

/-- Check one equation against its actual evidence. Conditional equations need
a theorem; a definitional equation checks both sides' types before equality. -/
def checkRoleEquation (ops : CheckerOps md m) (env : Env md) (levels : Nat)
    (equation : Equation md) (evidence : Evidence (Key md × Expr md)) : m Unit := do
  let parameters := List.range levels
  let statement := equation.statement
  checkRoleTerm env parameters statement
  let statement ← ops.annotate env 0 statement
  let statementType ← ops.inferType env 0 statement
  let _ ← ops.ensureSort env 0 statementType
  match evidence with
  | .defeq =>
    unless equation.hyps.isEmpty do
      throw (.invalid "a conditional role equation requires proof evidence")
    let left := equation.closedSide equation.lhs
    let right := equation.closedSide equation.rhs
    checkRoleTerm env parameters left
    checkRoleTerm env parameters right
    let left ← ops.annotate env 0 left
    let right ← ops.annotate env 0 right
    let leftType ← ops.inferType env 0 left
    let rightType ← ops.inferType env 0 right
    unless ← ops.isDefEq env 0 leftType rightType do
      throw (.invalid "a role equation's sides have different types")
    unless ← ops.isDefEq env 0 left right do
      throw (.invalid "a role equation does not hold by definitional equality")
  | .proof (key, value) =>
    let some (.thmInfo cv _) := env.find? key
      | throw (.invalid "a role equation's evidence does not name a checked theorem")
    unless cv.levelParams.length == levels && cv.levelParams.eraseDups == cv.levelParams do
      throw (.invalid "a role equation's theorem has different universe parameters")
    checkRoleTerm env cv.levelParams cv.type
    checkRoleTerm env cv.levelParams value
    let universes := parameters.map Level.param
    let theoremType := Expr.instLevelParams cv.levelParams universes cv.type
    let theoremType ← ops.annotate env 0 theoremType
    unless ← ops.isDefEq env 0 theoremType statement do
      throw (.invalid "a role equation's theorem has a different statement")
    let value := Expr.instLevelParams cv.levelParams universes value
    let value ← ops.annotate env 0 value
    let valueType ← ops.inferType env 0 value
    unless ← ops.isDefEq env 0 valueType statement do
      throw (.invalid "a role equation's proof has a different type")

/-- Validate one definition's specification without enabling an acceleration.
The environment must already be checked by the ordinary declaration fold. -/
def eqnsCheck (ops : CheckerOps md m) (env : Env md) (role : Role)
    (evidence : Evidences md) : m Unit := do
  let .eqns levels type equations := role.spec (md := md)
    | throw (.invalid "the role has no definition equations")
  let some (.defnInfo cv _ _) := env.find? (roleKey role)
    | throw (.invalid "a role equation's operation is not a checked definition")
  unless cv.levelParams.length == levels && cv.levelParams.eraseDups == cv.levelParams do
    throw (.invalid "a bound definition has different universe parameters")
  checkRoleTerm env cv.levelParams cv.type
  checkRoleTerm env (List.range levels) type
  let actualType := Expr.instLevelParams cv.levelParams ((List.range levels).map Level.param) cv.type
  let actualType ← ops.annotate env 0 actualType
  let expectedType ← ops.annotate env 0 type
  unless ← ops.isDefEq env 0 actualType expectedType do
    throw (.invalid "a bound definition has a different type")
  let entries := evidence.of role
  unless entries.length == equations.length do
    throw (.invalid "a definition's evidence does not match its equation count")
  for (equation, entry) in equations.zip entries do
    checkRoleEquation ops env levels equation entry

end Ix.Kernel
