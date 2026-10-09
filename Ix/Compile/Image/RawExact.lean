module
public import Ix.Environment
public import Init.Data.Array.Lemmas
public section

namespace Ix.Compile.Image.RawExact

/-! Exact raw equality for retained development-cache keys. Unlike the global
`BEq` instances, this includes cached addresses and every metadata field.
These decisions are local implementation details, not global equality changes. -/

deriving instance DecidableEq for Ix.Name
attribute [-instance] instDecidableEqName
attribute [local instance] instDecidableEqName
deriving instance DecidableEq for Ix.Level
attribute [-instance] instDecidableEqLevel
attribute [local instance] instDecidableEqLevel
deriving instance DecidableEq for Ix.Int
attribute [-instance] instDecidableEqInt
attribute [local instance] instDecidableEqInt
deriving instance DecidableEq for Ix.Substring
attribute [-instance] instDecidableEqSubstring
attribute [local instance] instDecidableEqSubstring
deriving instance DecidableEq for Ix.SourceInfo
attribute [-instance] instDecidableEqSourceInfo
attribute [local instance] instDecidableEqSourceInfo
deriving instance DecidableEq for Ix.SyntaxPreresolved
attribute [-instance] instDecidableEqSyntaxPreresolved
attribute [local instance] instDecidableEqSyntaxPreresolved

/-- The member witness exposes strict descent through a nested array. -/
def listDecEqOn {α : Type} (xs ys : List α)
    (cmp : ∀ x, x ∈ xs → ∀ y, Decidable (x = y)) : Decidable (xs = ys) :=
  match xs, ys with
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (by intro h; cases h)
  | _ :: _, [] => .isFalse (by intro h; cases h)
  | x :: xs, y :: ys =>
    match cmp x (by simp) y with
    | .isFalse different => .isFalse (fun h => different (List.cons.inj h).1)
    | .isTrue same =>
      match listDecEqOn xs ys (fun z hz => cmp z (by simp only [List.mem_cons]; exact Or.inr hz)) with
      | .isFalse different => .isFalse (fun h => different (List.cons.inj h).2)
      | .isTrue rest => .isTrue (by cases same; cases rest; rfl)

def arrayDecEqOn {α : Type} (xs ys : Array α)
    (cmp : ∀ x, x ∈ xs → ∀ y, Decidable (x = y)) : Decidable (xs = ys) :=
  match listDecEqOn xs.toList ys.toList (fun x hx => cmp x (Array.mem_toList_iff.mp hx)) with
  | .isTrue same => .isTrue (Array.toList_inj.mp same)
  | .isFalse different => .isFalse (fun h => different (congrArg Array.toList h))

/-- `Syntax` is nested through an array, so its decision is made explicitly.
The recursive call receives the actual array-member descent proof. -/
def syntaxDecEq (a b : Ix.Syntax) : Decidable (a = b) := by
  cases a <;> cases b
  case missing.missing => exact .isTrue rfl
  case node.node info kind args info' kind' args' =>
    letI : Decidable (args = args') :=
      arrayDecEqOn args args' (fun x hx y => syntaxDecEq x y)
    exact decidable_of_iff (info = info' ∧ kind = kind' ∧ args = args')
      (by simp only [Ix.Syntax.node.injEq])
  case atom.atom info value info' value' =>
    exact decidable_of_iff (info = info' ∧ value = value')
      (by simp only [Ix.Syntax.atom.injEq])
  case ident.ident info raw value pres info' raw' value' pres' =>
    exact decidable_of_iff (info = info' ∧ raw = raw' ∧ value = value' ∧ pres = pres')
      (by simp only [Ix.Syntax.ident.injEq])
  all_goals exact .isFalse (by intro same; cases same)
termination_by sizeOf a
decreasing_by
  exact Nat.lt_trans (Array.sizeOf_lt_of_mem hx) (by simp +arith)

local instance : DecidableEq Ix.Syntax := syntaxDecEq

def binderDecEq (a b : Lean.BinderInfo) : Decidable (a = b) := by
  cases a <;> cases b <;> first
    | exact .isTrue rfl
    | exact .isFalse (by intro same; cases same)

def literalDecEq : (a b : Lean.Literal) → Decidable (a = b)
  | .natVal a, .natVal b => decidable_of_iff (a = b) (by simp only [Lean.Literal.natVal.injEq])
  | .strVal a, .strVal b => decidable_of_iff (a = b) (by simp only [Lean.Literal.strVal.injEq])
  | .natVal _, .strVal _ => .isFalse (by intro same; cases same)
  | .strVal _, .natVal _ => .isFalse (by intro same; cases same)

local instance : DecidableEq Lean.BinderInfo := binderDecEq
local instance : DecidableEq Lean.Literal := literalDecEq
deriving instance DecidableEq for Ix.DataValue
attribute [-instance] instDecidableEqDataValue
attribute [local instance] instDecidableEqDataValue
deriving instance DecidableEq for Ix.Expr
attribute [-instance] instDecidableEqExpr

/-- Existing Lean's verified pointer fast path, with full structural fallback.
The original expression remains alive in the cache entry. -/
def exprDecEq (a b : Ix.Expr) : Decidable (a = b) :=
  withPtrEqDecEq a b (fun _ => instDecidableEqExpr a b)

end Ix.Compile.Image.RawExact
