import IxCCTests.Aiur.RankAIR.Fixtures

namespace IxCCTests.Aiur.RankAIR

open _root_.IxCC.Vendor.Aiur (G)
open IxCC.Aiur.AIR
open IxCC.Aiur.AIR.Rank

private def need (count : IO.Ref Nat) (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"Aiur rank AIR regression failed: {label}")
  count.modify (· + 1)

private def accepts (entry : Edge) : Bool := match validate entry with | .ok _ => true | .error _ => false
private def rejects (entry : Edge) (expected : Error) : Bool :=
  match validate entry with | .error actual => decide (actual = expected) | .ok _ => false

def run : IO Unit := do
  let count ← IO.mkRef 0
  for (label, entry) in [("first step", firstStep), ("low carry", limbCarry),
      ("high carry", highCarry), ("last step", lastStep), ("large gap", longGap),
      ("nonzero origin", edge 123 17 141)] do
    need count label (accepts entry)
  need count "binding mismatch" (rejects wrongBinding .binding)
  need count "rank cannot wrap to zero" (rejects overflow .binding)
  need count "decreasing rank" (rejects (edge 9 0 8) .binding)
  need count "self rank" (rejects (edge 7 0 7) .binding)
  need count "too-large packed child" (rejects (edge (rankBound - 1) 0 rankBound) .childRange)
  for (name, malformed) in [("low", (⟨65536, 0, 0⟩ : Limbs)),
      ("middle", ⟨0, 65536, 0⟩), ("high", ⟨0, 0, 65536⟩), ("negative", ⟨0 - 1, 0, 0⟩)] do
    need count s!"parent {name}" (rejects { firstStep with parent := malformed } .parentRange)
    need count s!"gap {name}" (rejects { firstStep with gap := malformed } .gapRange)
    need count s!"child {name}" (rejects { firstStep with child := malformed } .childRange)
  need count "noncanonical equal packing rejected"
    (rejects ⟨⟨65536, 0, 0⟩, limbs 0, limbs 65537⟩ .parentRange)
  for value in [0, 1, 255, 256, 65535, 65536, 4294967295, 4294967296, rankBound - 1] do
    need count s!"packing {value}" ((limbs value).packed == G.ofNat value)
  for index in [0, 1, 255, 256, 257, 65534, 65535] do
    let window : Window := ⟨[9, 8, 7, 6, 5, 4, 3, 0 - 2], [], false, rangeColumns index⟩
    need count s!"range payload {index}"
      (rangePull.arguments.mapM (Expr.eval window) == some [15, G.ofNat index])
    need count s!"range signed weight {index}" (rangePull.multiplicity.eval window == some 2)
  let parent := limbs 65535
  let gap := limbs 9
  let child := limbs 65545
  for branchless in [false, true] do
    let window : Window := ⟨[1] ++ parent.values ++ gap.values ++ [child.packed], [], false, []⟩
    let selector := Expr.main 0
    let packedParent := packColumns 1
    let packedGap := packColumns 4
    let rank := orderedExpr packedParent packedGap
    let push := functionPush branchless selector 7 [.constant 99] [.constant 42] rank
    need count s!"complete selected call {branchless}"
      (push.arguments.mapM (Expr.eval window) == some (functionMessage 7 [99] [42] child.packed))
    need count s!"selected call weight {branchless}" (push.multiplicity.eval window == some 1)
    let range := rangePush branchless selector (.main 1)
    need count s!"selected range {branchless}"
      (range.arguments.mapM (Expr.eval window) == some [15, parent.low])
  let inactive : Window := ⟨[0, 7], [], false, []⟩
  for branchless in [false, true] do
    let push := rangePush branchless (.main 0) (.main 1)
    need count s!"inactive range weight {branchless}" (push.multiplicity.eval inactive == some 0)
    need count s!"inactive range arguments {branchless}"
      (push.arguments.mapM (Expr.eval inactive) == some (if branchless then [15, 7] else [0, 0]))
  need count "boundary rank does not add gap"
    (callValue .bound parent gap 3 == 3)
  need count "unranked callee has zero rank"
    (callValue .zero parent gap 123 == 0)
  need count "rank retained after outputs"
    (functionMessage 1 [7] [8] 0 != functionMessage 1 [7] [8] 1)
  need count "main does not substitute for fixed columns"
    (rangePull.arguments.mapM (Expr.eval ⟨[0, 7], [], false, []⟩) == none)
  need count "missing fixed high byte"
    (rangePull.arguments.mapM (Expr.eval ⟨[], [], false, [7]⟩) == none)
  need count "missing weight column"
    (rangePull.multiplicity.eval ⟨[], [], false, rangeColumns 7⟩ == none)
  need count "missing rank limb" ((packColumns 0).eval ⟨[1, 2], [], false, []⟩ == none)
  need count "zero gate still reads nonconstant operand"
    ((gate false (.main 0) (.main 9)).eval inactive == none)
  for (name, circuits) in graphFixtures do
    let [parent, child] := circuits | throw (IO.userError s!"malformed graph fixture: {name}")
    let inactiveProvider := fun circuit : Circuit =>
      circuit.check ⟨(List.replicate circuit.width (0 : G)).set 2 1, [], false, []⟩
    need count s!"inactive nonzero provider {name}" (!inactiveProvider parent && !inactiveProvider child)
  IO.println s!"aiur-rank-air-tests-ok: {← count.get} assertions, rank bounds, carries, exact messages, modes and missing columns"

end IxCCTests.Aiur.RankAIR
