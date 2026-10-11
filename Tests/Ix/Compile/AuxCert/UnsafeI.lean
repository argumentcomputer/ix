/-! H4: unsafe inductives (positivity unchecked), including a nested occurrence
in a negative position. -/
namespace UnsafeI
unsafe inductive U
  | leaf
  | mk : (U → U) → U

unsafe inductive UN
  | mk : List UN → UN

unsafe inductive UNeg
  | mk : (UNeg → Nat) → UNeg

unsafe inductive UNestNeg
  | mk : (List UNestNeg → Nat) → UNestNeg

unsafe def U.depth : U → Nat
  | .leaf => 0
  | .mk _ => 1
end UnsafeI
