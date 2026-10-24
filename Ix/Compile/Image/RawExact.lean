/-
  Ix.Compile.Image.RawExact: exact raw equality for the image generator's
  retained table keys and its expression comparisons (`alphaEq`,
  `motiveEq`).

  Unlike the hash-based `BEq` instances of `Ix.Name`, `Ix.Level` and
  `Ix.Expr`, these decide equality of the complete values, cached addresses
  and every metadata field included: a stored digest never decides an
  equality. The decisions are the compiler's exact-key decisions
  (`Ix.Compile.ExactKey`, derived structurally, with the pointer fast path for
  expressions); this module only names them for the generator.
-/
module
public import Ix.Environment
public import Ix.Compile.ExactKey
public section

namespace Ix.Compile.Image.RawExact

/-- Full retained name equality, including cached addresses at every node. -/
def nameEq (a b : Ix.Name) : Bool := decide (a = b)

/-- Full retained level equality, including recursive name and level caches. -/
def levelEq (a b : Ix.Level) : Bool := decide (a = b)

/-- The exact universe arguments of a constant. -/
def levelsEq (a b : Array Ix.Level) : Bool := decide (a = b)

@[simp] theorem nameEq_eq_true (a b : Ix.Name) : nameEq a b = true ↔ a = b := by
  simp only [nameEq, decide_eq_true_eq]

@[simp] theorem levelEq_eq_true (a b : Ix.Level) : levelEq a b = true ↔ a = b := by
  simp only [levelEq, decide_eq_true_eq]

@[simp] theorem levelsEq_eq_true (a b : Array Ix.Level) : levelsEq a b = true ↔ a = b := by
  simp only [levelsEq, decide_eq_true_eq]

/-- Exact expression equality: pointer equality first, then the full
structural decision. The compared expressions stay alive in the caller's
table entry. -/
def exprDecEq (a b : Ix.Expr) : Decidable (a = b) := Ix.Compile.ExactKey.ptrDec a b

/-- `exprDecEq` as a Boolean. -/
def exprEq (a b : Ix.Expr) : Bool := @decide (a = b) (exprDecEq a b)

@[simp] theorem exprEq_eq_true (a b : Ix.Expr) : exprEq a b = true ↔ a = b :=
  @decide_eq_true_iff _ (exprDecEq a b)

/-- Exact expression equality decided at the root: the root's own fields
compared in full, its expression children with `exprEq` (pointer equality
first). When equal children are the same objects, as in a table of shared
nodes, the decision does not descend; otherwise it is the full comparison. -/
def nodeEq (a b : Ix.Expr) : Bool :=
  match a, b with
  | .app f x h, .app f' x' h' =>
    decide (h = h') && exprEq f f' && exprEq x x'
  | .lam n t x bi h, .lam n' t' x' bi' h' =>
    decide (h = h') && exprEq t t' && exprEq x x' && nameEq n n' && decide (bi = bi')
  | .forallE n t x bi h, .forallE n' t' x' bi' h' =>
    decide (h = h') && exprEq t t' && exprEq x x' && nameEq n n' && decide (bi = bi')
  | .letE n t v x nd h, .letE n' t' v' x' nd' h' =>
    decide (h = h') && exprEq t t' && exprEq v v' && exprEq x x' && nameEq n n' &&
      decide (nd = nd')
  | .proj s i x h, .proj s' i' x' h' =>
    decide (h = h') && exprEq x x' && nameEq s s' && decide (i = i')
  | .mdata md x h, .mdata md' x' h' =>
    decide (h = h') && exprEq x x' && decide (md = md')
  | a, b => exprEq a b

theorem nodeEq_eq {a b : Ix.Expr} (hq : nodeEq a b = true) : a = b := by
  unfold nodeEq at hq
  split at hq <;> simp_all

end Ix.Compile.Image.RawExact

end
