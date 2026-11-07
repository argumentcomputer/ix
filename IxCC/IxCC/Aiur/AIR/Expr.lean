import IxCC.Vendor.Ix.Aiur.Goldilocks

/-! The base-field expression fragment used by the pinned memory and rank AIR.
Missing columns fail evaluation. This is not a parser or the complete
multi-stark expression language. -/

namespace IxCC.Aiur.AIR

open _root_.IxCC.Vendor.Aiur (G)

inductive Expr where
  | constant (value : G)
  | main (column : Nat)
  | next (column : Nat)
  | preprocessed (column : Nat)
  | transition
  | add (left right : Expr)
  | sub (left right : Expr)
  | mul (left right : Expr)
  | neg (value : Expr)
  deriving DecidableEq, Repr

structure Window where
  current : List G
  next : List G
  transition : Bool
  preprocessed : List G := []
  deriving DecidableEq, Repr

def Expr.eval (window : Window) : Expr → Option G
  | .constant value => some value
  | .main column => window.current[column]?
  | .next column => window.next[column]?
  | .preprocessed column => window.preprocessed[column]?
  | .transition => some (if window.transition then 1 else 0)
  | .add left right => return (← left.eval window) + (← right.eval window)
  | .sub left right => return (← left.eval window) - (← right.eval window)
  | .mul left right => return (← left.eval window) * (← right.eval window)
  | .neg value => return 0 - (← value.eval window)

structure Lookup where
  multiplicity : Expr
  arguments : List Expr
  deriving DecidableEq, Repr

structure Circuit where
  width : Nat
  zeros : List Expr
  lookups : List Lookup
  deriving DecidableEq, Repr

def Circuit.Satisfied (circuit : Circuit) (window : Window) : Prop :=
  ∀ expression ∈ circuit.zeros, expression.eval window = some 0

def Circuit.check (circuit : Circuit) (window : Window) : Bool :=
  circuit.zeros.all fun expression => expression.eval window == some 0

theorem Circuit.check_sound (circuit : Circuit) (window : Window)
    (checked : circuit.check window = true) : circuit.Satisfied window := by
  intro expression member
  exact beq_iff_eq.mp (List.all_eq_true.mp checked expression member)

end IxCC.Aiur.AIR
