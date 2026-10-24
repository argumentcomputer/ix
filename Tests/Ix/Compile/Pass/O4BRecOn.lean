/- A4 per-pass fixture (`pass3` suite), elaborated at run time and in no Lake library.
O4, `below`/`brecOn` over a permuted block: the structural recursion `Src.Even.toNat`,
`Src.Odd.toNat` goes through `brecOn` and `below` of the permuted pair, and must compile to the
bytes of `Can` (the pair in canonical order): O4 fires on every `brecOn`/`below` occurrence
(handlers and motives permuted). `Src.SB.depth` recurses structurally over the lower component of
a split block, which has no cross field: O4 fires too (`Can` declares the component alone).
`Src.SA.size` recurses over the upper component, whose constructor `a` has a field into the
lower one: O4 declines (the Ix `below` of a component has no slot for the cross field, O9's
re-pathing, A6) and the baseline stays. Value pins by `rfl`. -/
set_option Elab.async false

namespace PassO4
namespace Src
mutual
inductive Even
  | zero : Even
  | s : Odd → Even
inductive Odd
  | s : Even → Odd
end

mutual
def Odd.toNat : Odd → Nat
  | .s e => e.toNat + 1
def Even.toNat : Even → Nat
  | .zero => 0
  | .s o => o.toNat + 1
end

theorem three : Odd.toNat (.s (.s (.s .zero))) = 3 := rfl

mutual
inductive SA
  | a : SB → SA
  | n : SA → SA
  | stop : SA
inductive SB
  | b : SB → SB
  | leaf : SB
end

def SB.depth : SB → Nat
  | .b x => x.depth + 1
  | .leaf => 0

theorem depth_two : SB.depth (.b (.b .leaf)) = 2 := rfl

def SA.size : SA → Nat
  | .a b => b.depth
  | .n x => x.size + 1
  | .stop => 0

theorem size_two : SA.size (.n (.a (.b .leaf))) = 2 := rfl
end Src

namespace Can
mutual
inductive Odd
  | s : Even → Odd
inductive Even
  | zero : Even
  | s : Odd → Even
end

mutual
def Odd.toNat : Odd → Nat
  | .s e => e.toNat + 1
def Even.toNat : Even → Nat
  | .zero => 0
  | .s o => o.toNat + 1
end

theorem three : Odd.toNat (.s (.s (.s .zero))) = 3 := rfl

inductive SB
  | b : SB → SB
  | leaf : SB

def SB.depth : SB → Nat
  | .b x => x.depth + 1
  | .leaf => 0

theorem depth_two : SB.depth (.b (.b .leaf)) = 2 := rfl
end Can
end PassO4
