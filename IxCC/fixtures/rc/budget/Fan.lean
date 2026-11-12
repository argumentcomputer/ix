/-! RC budget fixture (heap stage 2, milestone 2). A fan function binds `C` values `xᵢ := n + i`,
then branches on `s` through a balanced tree of `s < m` tests with `K` leaves (leaf `lo` returns
`lo + o`), then returns the leaf plus the sum of every `xᵢ`. In the compiled program the code after
the branch is a join that captures the `C` values and that every leaf jumps to, so an ownership
certificate makes the checker take `C` captured tokens at each of the `K` jumps and `C` at the
join's declaration: `Own.Plain.Certificate.capturedWork`, which admission bounds by
`Anf.maxCapturedWork` (2²⁰). A root sums five fan functions (distinct by their offsets `o`, so that
content addressing keeps them apart) and returns a pair, so that the program allocates and the
automatic policy selects plain RC: `fanUnder` is within the limit, `fanOver` past it. Each fan
function stays within the consumer's expression depth (256) and the middle end's node budgets.
`main` checks both roots against an independent formula in Lean's interpreter. -/

namespace IxCCTests.Own.Budget

/-- `fanTree% s o lo hi`: the leaves `lo + o … hi - 1 + o` under a balanced tree of `s < m` tests. -/
syntax "fanTree% " ident num num num : term
macro_rules
  | `(fanTree% $s:ident $o:num $lo:num $hi:num) => do
    let lo := lo.getNat
    let hi := hi.getNat
    if hi ≤ lo + 1 then
      return Lean.Syntax.mkNumLit (toString (lo + o.getNat))
    let mid := (lo + hi) / 2
    let lo' := Lean.Syntax.mkNumLit (toString lo)
    let mid' := Lean.Syntax.mkNumLit (toString mid)
    let hi' := Lean.Syntax.mkNumLit (toString hi)
    `(if $s < $mid' then fanTree% $s $o $lo' $mid' else fanTree% $s $o $mid' $hi')

/-- `fanSum% lo hi`: the balanced sum of the identifiers `x{lo} … x{hi - 1}`. -/
syntax "fanSum% " num num : term
macro_rules
  | `(fanSum% $lo:num $hi:num) => do
    let lo := lo.getNat
    let hi := hi.getNat
    if hi ≤ lo then return Lean.Syntax.mkNumLit "0"
    if hi == lo + 1 then return Lean.mkIdent (Lean.Name.mkSimple s!"x{lo}")
    let mid := (lo + hi) / 2
    `(fanSum% $(Lean.Syntax.mkNumLit (toString lo)) $(Lean.Syntax.mkNumLit (toString mid)) +
      fanSum% $(Lean.Syntax.mkNumLit (toString mid)) $(Lean.Syntax.mkNumLit (toString hi)))

/-- `fanBody% n s C K o`: the `C` bindings, the tree of `K` leaves on `s`, the leaf plus the sum. -/
syntax "fanBody% " ident ident num num num : term
macro_rules
  | `(fanBody% $n:ident $s:ident $c:num $k:num $o:num) => do
    let xs := (List.range c.getNat).map fun i => (Lean.mkIdent (Lean.Name.mkSimple s!"x{i}"), i)
    let tail ← `(let r := fanTree% $s $o 0 $k; r + fanSum% 0 $c)
    let body ← xs.foldrM (s := Lean.TSyntax `term) (fun (x, i) b =>
      `(let $x:ident := $n + $(Lean.Syntax.mkNumLit (toString i)); $b)) tail
    return body

/-- Within the captured-work limit: 200 bindings, 1,047 leaves. -/
def fanA1 (n s : Nat) : Nat := fanBody% n s 200 1047 10000
def fanA2 (n s : Nat) : Nat := fanBody% n s 200 1047 20000
def fanA3 (n s : Nat) : Nat := fanBody% n s 200 1047 30000
def fanA4 (n s : Nat) : Nat := fanBody% n s 200 1047 40000
def fanA5 (n s : Nat) : Nat := fanBody% n s 200 1047 50000

/-- Past the captured-work limit: 200 bindings, 1,048 leaves. -/
def fanB1 (n s : Nat) : Nat := fanBody% n s 200 1048 10000
def fanB2 (n s : Nat) : Nat := fanBody% n s 200 1048 20000
def fanB3 (n s : Nat) : Nat := fanBody% n s 200 1048 30000
def fanB4 (n s : Nat) : Nat := fanBody% n s 200 1048 40000
def fanB5 (n s : Nat) : Nat := fanBody% n s 200 1048 50000

def fanUnder (n s : Nat) : Nat × Nat :=
  (fanA1 n s + fanA2 n s + fanA3 n s + fanA4 n s + fanA5 n s, s)

def fanOver (n s : Nat) : Nat × Nat :=
  (fanB1 n s + fanB2 n s + fanB3 n s + fanB4 n s + fanB5 n s, s)

/-- The reference: five leaves `min s (K - 1) + o` and five sums `C·n + C(C - 1)/2`. -/
def reference (c k n s : Nat) : Nat × Nat :=
  (5 * (min s (k - 1) + c * n + c * (c - 1) / 2) + 150000, s)

end IxCCTests.Own.Budget

open IxCCTests.Own.Budget in
def main : IO Unit := do
  for (n, s) in [(0, 0), (1, 5), (7, 1000), (100, 1046), (3, 5000)] do
    unless fanUnder n s == reference 200 1047 n s && fanOver n s == reference 200 1048 n s do
      throw (IO.userError s!"fan {n} {s}: {fanUnder n s} {fanOver n s}")
  IO.println "ok"
