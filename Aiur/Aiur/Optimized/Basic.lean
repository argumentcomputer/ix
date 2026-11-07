import Aiur.Circuit.Compile
import Aiur.Circuit.Stats

deriving instance DecidableEq for Aiur.Scalar.Circuit.ArithExpr

namespace Aiur.Optimized

abbrev Polynomial := Circuit.ArithExpr
abbrev ScopeId := Nat
abbrev Witness := Nat

structure Config where
  maxDegree : Nat := 3
  shareAuxiliaries : Bool := true
  eliminateSelectors : Bool := true
  propagateScopes : Bool := true
  simplifyConstraints : Bool := true
  propagateValues : Bool := true
  mergeLookups : Bool := true
  deduplicate : Bool := true
  deriving Repr, BEq

/-- A path records selected arms of independent choices, not execution times. -/
abbrev Path := List (Nat × Nat)

def Path.exclusive (left right : Path) : Bool :=
  left.any fun (choice, arm) => right.any fun (other, branch) =>
    choice == other && arm != branch

inductive Role where
  | input
  | output
  | selector
  | auxiliary (scope : ScopeId)
  deriving Repr, BEq, DecidableEq

structure Scope (F : Type) where
  activation : Polynomial F
  path : Path
  deriving Repr, BEq, DecidableEq

structure Equation (F : Type) where
  scope : ScopeId
  polynomial : Polynomial F
  deriving Repr, BEq, DecidableEq

structure Call (F : Type) where
  scope : ScopeId
  channel : String
  args : List (WireValue (Polynomial F))
  result : WireValue Witness
  deriving Repr, BEq, DecidableEq

structure Cell (F : Type) where
  scope : ScopeId
  address : Polynomial F
  value : WireValue (Polynomial F)
  deriving Repr, BEq, DecidableEq

/-- The coverage and exclusion equations for a choice are checked separately;
this record describes their intended parent/child relationship. -/
structure Choice where
  parent : ScopeId
  children : List ScopeId
  deriving Repr, BEq, DecidableEq

/-- Logical witnesses have roles and scopes; selector aliases need no column. -/
structure ScopedChip (F : Type) where
  name : String
  inputs : List (WireValue Witness)
  output : WireValue Witness
  roles : Array Role
  aliases : Array (Option (Polynomial F))
  scopes : Array (Scope F)
  equations : Array (Equation F)
  calls : Array (Call F)
  cells : Array (Cell F)
  choices : Array Choice := #[]
  deriving Repr, BEq

structure ColumnLayout where
  /-- `none` identifies a witness eliminated by an affine definition. -/
  columnOf : Array (Option Circuit.Var)
  /-- All logical witnesses that share each physical column. -/
  occupants : Array (List Witness)
  deriving Repr, BEq

structure LaidOutChip (F : Type) where
  logical : ScopedChip F
  /-- Allocation before final copy/constant propagation and column compaction. -/
  layout : ColumnLayout
  /-- Final physical chip, after value propagation when enabled. -/
  chip : Circuit.Chip F
  deriving Repr, BEq

namespace Polynomial

export Aiur.Scalar.Circuit.ArithExpr (const var add sub mul)

abbrev degree (expr : Polynomial F) : Nat := Circuit.ArithExpr.degree expr

def subst (replacement : Witness → Polynomial F) : Polynomial F → Polynomial F
  | .const value => .const value
  | .var id => replacement id
  | .add a b => .add (subst replacement a) (subst replacement b)
  | .sub a b => .sub (subst replacement a) (subst replacement b)
  | .mul a b => .mul (subst replacement a) (subst replacement b)

def vars : Polynomial F → List Witness
  | .const _ => []
  | .var id => [id]
  | .add a b | .sub a b | .mul a b => vars a ++ vars b

/-- These simplifications concern total polynomials, never source operations. -/
def simplify [Field F] [DecidableEq F] : Polynomial F → Polynomial F
  | .const value => .const value
  | .var id => .var id
  | .add a b =>
      match simplify a, simplify b with
      | .const a, .const b => .const (a + b)
      | .const a, b => if a = 0 then b else .add (.const a) b
      | a, .const b => if b = 0 then a else .add a (.const b)
      | a, b => .add a b
  | .sub a b =>
      let a := simplify a
      let b := simplify b
      if a == b then .const 0 else
      match a, b with
      | .const a, .const b => .const (a - b)
      | a, .const b => if b = 0 then a else .sub a (.const b)
      | a, b => .sub a b
  | .mul a b =>
      match simplify a, simplify b with
      | .const a, .const b => .const (a * b)
      | .const a, b => if a = 0 then .const 0 else if a = 1 then b else .mul (.const a) b
      | a, .const b => if b = 0 then .const 0 else if b = 1 then a else .mul a (.const b)
      | a, b => .mul a b

end Polynomial

end Aiur.Optimized
