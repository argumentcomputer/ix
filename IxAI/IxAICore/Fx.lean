/-!
# Fixed-point numbers for the certified core

Everything in `IxAICore` imports only `Init` and is written so that a kernel can evaluate it:
structural recursion over `Nat` and `List`, integer arithmetic, no opaque or native functions.
Ix's IxVM evaluates these definitions inside its proofs, so a training run or an evaluation can
be stated as an Ix `Eval` claim and proved.

`Fx` is a fixed-point number `raw / 256`. Sums are exact. A product rounds once, toward negative
infinity, and a dot product accumulates its terms exactly and rounds once, so its value does not
depend on the order of accumulation.
-/

namespace IxAICore

structure Fx where
  raw : Int
  deriving DecidableEq, Repr, Inhabited

namespace Fx

def scale : Nat := 256

def zero : Fx := ⟨0⟩
def one : Fx := ⟨256⟩
def ofInt (n : Int) : Fx := ⟨n * 256⟩
/-- The value `n / 256`. -/
def ofRaw (n : Int) : Fx := ⟨n⟩

def add (a b : Fx) : Fx := ⟨a.raw + b.raw⟩
def sub (a b : Fx) : Fx := ⟨a.raw - b.raw⟩
def mul (a b : Fx) : Fx := ⟨(a.raw * b.raw) >>> 8⟩
def pos (a : Fx) : Bool := decide (a.raw > 0)
def relu (a : Fx) : Fx := if a.raw > 0 then a else zero
/-- Clamp to `[0, 1]`. -/
def clamp01 (a : Fx) : Fx := if a.raw < 0 then zero else if a.raw > 256 then one else a

/-- Exact sum of exact products. Extra elements of the longer list are ignored. -/
def dotRaw : List Fx → List Fx → Int
  | a :: as, b :: bs => a.raw * b.raw + dotRaw as bs
  | _, _ => 0

/-- `Σ aᵢ·bᵢ`, accumulated exactly and rounded once. -/
def dot (as bs : List Fx) : Fx := ⟨dotRaw as bs >>> 8⟩

def sumRaw : List Fx → Int
  | [] => 0
  | a :: as => a.raw + sumRaw as

def sum (as : List Fx) : Fx := ⟨sumRaw as⟩

end Fx

/-- Element `i` of a list, or `d`. -/
def getD {α : Type} : List α → Nat → α → α
  | [], _, d => d
  | a :: _, 0, _ => a
  | _ :: as, i + 1, d => getD as i d

/-- The `i`-th column of a list of rows. -/
def column {α : Type} (rows : List (List α)) (i : Nat) (d : α) : List α :=
  rows.map fun r => getD r i d

/-- Pair each element with its index. -/
def withIndex {α : Type} : List α → Nat → List (α × Nat)
  | [], _ => []
  | a :: as, i => (a, i) :: withIndex as (i + 1)

/-- Index of the first maximal element; `0` for an empty list. -/
def argmax (xs : List Fx) : Nat :=
  (withIndex xs 0).foldl (fun (best : Fx × Nat) (x, i) => if x.raw > best.1.raw then (x, i) else best)
    (getD xs 0 Fx.zero, 0) |>.2

theorem Fx.dotRaw_comm (as bs : List Fx) : Fx.dotRaw as bs = Fx.dotRaw bs as := by
  induction as generalizing bs with
  | nil => cases bs <;> rfl
  | cons a as ih =>
    cases bs with
    | nil => rfl
    | cons b bs => simp only [Fx.dotRaw, ih, Int.mul_comm]

end IxAICore
