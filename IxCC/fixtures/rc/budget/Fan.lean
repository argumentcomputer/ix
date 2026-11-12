/-! RC budget fixture (heap stage 2, milestone 2). Each root binds `C` values `xᵢ := n + i`, then
branches on `s` through a balanced tree of `s < m` tests with `K` leaves, then returns the leaf and
the sum of every `xᵢ`. In the compiled program the code after the branch is a join that captures
the `C` values and that every leaf jumps to, so an ownership certificate makes the checker take
`C` captured tokens at each of the `K` jumps and `C` at the join's declaration:
`Own.Plain.Certificate.capturedWork`, which admission bounds by `Anf.maxCapturedWork` (2²⁰).
`fanUnder` is within the limit, `fanOver` past it. `main` is an independent reference oracle. -/

namespace IxCCTests.Own.Budget

/-- `fanTree% s lo hi`: the leaves `lo … hi - 1` under a balanced tree of `s < m` tests. -/
syntax "fanTree% " ident num num : term
macro_rules
  | `(fanTree% $s:ident $lo:num $hi:num) => do
    let lo := lo.getNat
    let hi := hi.getNat
    if hi ≤ lo + 1 then
      return Lean.Syntax.mkNumLit (toString lo)
    let mid := (lo + hi) / 2
    let lo' := Lean.Syntax.mkNumLit (toString lo)
    let mid' := Lean.Syntax.mkNumLit (toString mid)
    let hi' := Lean.Syntax.mkNumLit (toString hi)
    `(if $s < $mid' then fanTree% $s $lo' $mid' else fanTree% $s $mid' $hi')

/-- `fanBody% n s C K`: the `C` bindings, the tree of `K` leaves on `s`, and the pair. -/
syntax "fanBody% " ident ident num num : term
macro_rules
  | `(fanBody% $n:ident $s:ident $c:num $k:num) => do
    let xs := (List.range c.getNat).map fun i => (Lean.mkIdent (Lean.Name.mkSimple s!"x{i}"), i)
    let sum ← xs.foldlM (fun acc (x, _) => `($acc + $x)) (← `(0))
    let tail ← `(let r := fanTree% $s 0 $k; (r, $sum))
    let body ← xs.foldrM (s := Lean.TSyntax `term) (fun (x, i) b =>
      `(let $x:ident := $n + $(Lean.Syntax.mkNumLit (toString i)); $b)) tail
    return body

set_option maxRecDepth 20000

/-- Within the captured-work limit. -/
def fanUnder (n s : Nat) : Nat × Nat := fanBody% n s 512 2047

/-- Past the captured-work limit. -/
def fanOver (n s : Nat) : Nat × Nat := fanBody% n s 513 2047

/-- The reference: the leaf is `min s (K - 1)`, the sum `C·n + C(C - 1)/2`. -/
def reference (c k n s : Nat) : Nat × Nat := (min s (k - 1), c * n + c * (c - 1) / 2)

end IxCCTests.Own.Budget

open IxCCTests.Own.Budget in
def main : IO Unit := do
  for (n, s) in [(0, 0), (1, 5), (7, 1000), (100, 2046), (3, 5000)] do
    unless fanUnder n s == reference 512 2047 n s && fanOver n s == reference 513 2047 n s do
      throw (IO.userError s!"fan {n} {s}: {fanUnder n s} {fanOver n s}")
  IO.println "ok"
