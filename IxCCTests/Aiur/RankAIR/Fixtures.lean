import IxCC.Aiur.AIR.Rank

namespace IxCCTests.Aiur.RankAIR

open _root_.IxCC.Vendor.Aiur (G)
open IxCC.Aiur.AIR
open IxCC.Aiur.AIR.Rank

/-- Keep the high limb untruncated so out-of-range ranks are rejected. -/
def limbs (value : Nat) : Limbs :=
  ⟨G.ofNat (value % 65536), G.ofNat (value / 65536 % 65536), G.ofNat (value / 4294967296)⟩

def edge (parent gap child : Nat) : Edge := ⟨limbs parent, limbs gap, limbs child⟩

def firstStep : Edge := edge 0 0 1
def limbCarry : Edge := edge 65535 0 65536
def highCarry : Edge := edge 4294967295 0 4294967296
def lastStep : Edge := edge (rankBound - 2) 0 (rankBound - 1)
def longGap : Edge := edge 0 (rankBound - 2) (rankBound - 1)
def wrongBinding : Edge := edge 7 1 7
def overflow : Edge := edge (rankBound - 1) 0 0

private def baseZeros : List Expr :=
  [.mul (.main 1) (.sub (.constant 1) (.main 1)),
   .mul (.main 1) (.sub (.main 1) (.constant 1)),
   .mul (.main 2) (.sub (.constant 1) (.main 1))]

private def ranges (branchless : Bool) (base : Nat) : List Lookup :=
  [base, base + 1, base + 2].map fun column => rangePush branchless (.main 1) (.main column)

/-- Complete tiny call-and-return circuits, compared with actual Rust
builder output. This is a fixture family, not a general function compiler. -/
def parentCircuit (ranked : Bool) (mode : CallMode) (gated : Bool) : Circuit :=
  let branchless := !gated
  let rank := if ranked then packColumns 3 else .constant 0
  let output := if ranked then 6 else 3
  let extra := match mode with | .zero => 0 | .bound => 1 | .ordered => 3
  let callRank := callExpr mode rank (packColumns (output + 1)) (.main (output + 1))
  { width := output + 1 + extra
    zeros := if gated then
      [.mul (.main 1) (.sub (.constant 1) (.main 1)), .mul (.main 1) (.main 0)] ++ baseZeros
      else baseZeros
    lookups := [functionPull branchless (.main 1) (.main 2) 0 [.main 0] [.main output] rank] ++
      (if ranked then ranges branchless 3 else []) ++
      [functionPush branchless (.main 1) 1 [.main 0] [.main output] callRank] ++
      (if mode = .ordered then ranges branchless (output + 1) else []) }

def childCircuit (ranked : Bool) : Circuit :=
  { width := if ranked then 6 else 3
    zeros := baseZeros
    lookups := [functionPull true (.main 1) (.main 2) 1 [.main 0] [.main 0]
      (if ranked then packColumns 3 else .constant 0)] ++
      (if ranked then ranges true 3 else []) }

def graphFixtures : List (String × List Circuit) :=
  [("legacy-ordered", [parentCircuit true .ordered false, childCircuit true]),
   ("ordered", [parentCircuit true .ordered false, childCircuit true]),
   ("bound", [parentCircuit true .bound false, childCircuit true]),
   ("bound-unranked-parent", [parentCircuit false .bound false, childCircuit true]),
   ("zero", [parentCircuit true .zero false, childCircuit false]),
   ("gated-ordered", [parentCircuit true .ordered true, childCircuit true])]

end IxCCTests.Aiur.RankAIR
