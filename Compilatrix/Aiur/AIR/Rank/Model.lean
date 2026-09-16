import Compilatrix.Aiur.AIR.Expr

/-! Three scalar-u16 limbs encode the pinned 48-bit ranks and gaps.
The physical range channel is 15; it is distinct from the two-byte channel. -/

namespace Compilatrix.Aiur.AIR.Rank

open _root_.Aiur (G)

abbrev limbBound : Nat := 65536
abbrev rankBound : Nat := 281474976710656

structure Limbs where
  low : G
  middle : G
  high : G
  deriving DecidableEq, Repr

def Limbs.values (limbs : Limbs) : List G := [limbs.low, limbs.middle, limbs.high]

def Limbs.Bounded (limbs : Limbs) : Prop :=
  limbs.low.n < limbBound ∧ limbs.middle.n < limbBound ∧ limbs.high.n < limbBound

instance (limbs : Limbs) : Decidable limbs.Bounded := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def Limbs.value (limbs : Limbs) : Nat :=
  limbs.low.n + limbs.middle.n * 65536 + limbs.high.n * 4294967296

def Limbs.packed (limbs : Limbs) : G :=
  limbs.low + limbs.middle * 65536 + limbs.high * 4294967296

def pack (low middle high : Expr) : Expr :=
  .add (.add low (.mul middle (.constant 65536))) (.mul high (.constant 4294967296))

def ordered (parent gap : Limbs) : G := parent.packed + 1 + gap.packed

def orderedExpr (parent gap : Expr) : Expr := .add (.add parent (.constant 1)) gap

/-- The first two preprocessed columns of the actual 256-by-256 table. -/
def rangeColumns (index : Nat) : List G := [G.ofNat (index / 256), G.ofNat (index % 256)]

def rangeValue (index : Nat) : G := G.ofNat (index / 256) * 256 + G.ofNat (index % 256)

def rangePull : Lookup :=
  { multiplicity := .neg (.main 7)
    arguments := [.constant 15,
      .add (.mul (.preprocessed 0) (.constant 256)) (.preprocessed 1)] }

/-- Match the complete scalar-range message at an actual fixed-table row. -/
def RangeProvided (value : G) : Prop :=
  ∃ index, index < limbBound ∧ [15, value] = [15, rangeValue index]

def Limbs.RangeProvided (limbs : Limbs) : Prop :=
  Rank.RangeProvided limbs.low ∧ Rank.RangeProvided limbs.middle ∧ Rank.RangeProvided limbs.high

/-- These are the three modes emitted by the pinned component-aware builder. -/
inductive CallMode where
  | zero | bound | ordered
  deriving DecidableEq, Repr

def callValue (mode : CallMode) (parent gap : Limbs) (boundary : G) : G :=
  match mode with
  | .zero => 0
  | .bound => boundary
  | .ordered => ordered parent gap

/-- The rank is the final physical function-message field, outside the
source-level inputs and outputs. It must survive provider matching. -/
def functionMessage (function : G) (inputs outputs : List G) (rank : G) : List G :=
  ([0, function] ++ inputs ++ outputs) ++ [rank]

end Compilatrix.Aiur.AIR.Rank
