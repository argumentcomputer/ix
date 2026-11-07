/-! MT.2 `even-odd` benchmark: MLton's `even-odd.sml` mutual recursion,
verbatim from `fixtures/corpus/phase1-scalar/src/Scalar.lean` (IxCC);
`entry` and `main` are the benchmark wrapper. -/

namespace Scalar

mutual
/-- MLton `even-odd.sml`: mutual structural recursion, sibling tail calls. -/
def isEven : Nat → Bool
  | 0 => true
  | n + 1 => isOdd n

def isOdd : Nat → Bool
  | 0 => false
  | n + 1 => isEven n
end

end Scalar

/-- The pure benchmark entry: `1` when `n` is even, else `0`. -/
def entry (n : Nat) : Nat := if Scalar.isEven n then 1 else 0

def main : List String → IO UInt32
  | [n] => do IO.println (toString (entry n.toNat!)); pure 0
  | _ => do IO.eprintln "usage: even-odd N"; pure 1
