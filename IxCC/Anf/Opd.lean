import IxCC.Anf.Syntax

/-! # Level-based operands

The passes build target terms while walking source terms under an
environment, so no term is ever shifted: an operand names a target variable
by its **level** (its position counted from the outside), which stays valid
under every binder the pass adds later, and becomes a de Bruijn index only
where an atom is emitted (`Opd.atom d` at target depth `d`). -/

namespace IxCC.Anf

/-- A target operand: a variable by level, a literal or □. -/
inductive Opd where
  | lvl (l : Nat)
  | lit (l : Lam.Lit)
  | box
  deriving DecidableEq, Repr, Inhabited

/-- The atom of an operand at target depth `d`. -/
def Opd.atom (d : Nat) : Opd → Atom
  | .lvl l => .var (d - 1 - l)
  | .lit l => .lit l
  | .box => .box

/-- The operand of an atom at depth `d` (its variable's level). -/
def Atom.opd (d : Nat) : Atom → Opd
  | .var i => .lvl (d - 1 - i)
  | .lit l => .lit l
  | .box => .box

/-- The operands of `n` parameters at levels `d … d + n - 1`, as an
environment (innermost first: parameter `i` at index `n - 1 - i`). -/
def paramOpds (d n : Nat) : List Opd :=
  ((List.range n).map fun i => Opd.lvl (d + i)).reverse

end IxCC.Anf
