/-! RC budget fixture (heap stage 2, milestone 2). A fan function binds `C` values `xᵢ := n + i`,
then branches on `s` through a balanced tree of `s < m` tests with `K` leaves (leaf `lo` returns
`lo + o`), then returns the leaf plus the sum of every `xᵢ`. In the compiled program the code after
the branch is a join that captures the `C` values and that every leaf jumps to, so an ownership
certificate makes the checker take `C` captured tokens at each of the `K` jumps and `C` at the
join's declaration: `Own.Plain.Certificate.capturedWork`, which admission bounds by
`Anf.maxCapturedWork` (2²⁰). A root sums twenty-three fan functions (distinct by their offsets
`o`, so that content addressing keeps them apart) and returns a pair, so that the program allocates
and the automatic policy selects plain RC: `fanUnder` is within the limit, `fanOver` past it. Each
fan function stays within the consumer's expression depth (256) and the middle end's node budgets
(16,384 Lam nodes per global).
`main` checks both roots against an independent formula in Lean's interpreter. -/

namespace IxCCTests.Own.Budget

/-- `fanTree% s o lo hi`: the leaves `lo + o … hi - 1 + o` under a balanced tree of `s < m`
tests. -/
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

/-- Within the captured-work limit: 150 bindings, 302 leaves. -/
def fanA1 (n s : Nat) : Nat := fanBody% n s 150 302 10000
def fanA2 (n s : Nat) : Nat := fanBody% n s 150 302 20000
def fanA3 (n s : Nat) : Nat := fanBody% n s 150 302 30000
def fanA4 (n s : Nat) : Nat := fanBody% n s 150 302 40000
def fanA5 (n s : Nat) : Nat := fanBody% n s 150 302 50000
def fanA6 (n s : Nat) : Nat := fanBody% n s 150 302 60000
def fanA7 (n s : Nat) : Nat := fanBody% n s 150 302 70000
def fanA8 (n s : Nat) : Nat := fanBody% n s 150 302 80000
def fanA9 (n s : Nat) : Nat := fanBody% n s 150 302 90000
def fanA10 (n s : Nat) : Nat := fanBody% n s 150 302 100000
def fanA11 (n s : Nat) : Nat := fanBody% n s 150 302 110000
def fanA12 (n s : Nat) : Nat := fanBody% n s 150 302 120000
def fanA13 (n s : Nat) : Nat := fanBody% n s 150 302 130000
def fanA14 (n s : Nat) : Nat := fanBody% n s 150 302 140000
def fanA15 (n s : Nat) : Nat := fanBody% n s 150 302 150000
def fanA16 (n s : Nat) : Nat := fanBody% n s 150 302 160000
def fanA17 (n s : Nat) : Nat := fanBody% n s 150 302 170000
def fanA18 (n s : Nat) : Nat := fanBody% n s 150 302 180000
def fanA19 (n s : Nat) : Nat := fanBody% n s 150 302 190000
def fanA20 (n s : Nat) : Nat := fanBody% n s 150 302 200000
def fanA21 (n s : Nat) : Nat := fanBody% n s 150 302 210000
def fanA22 (n s : Nat) : Nat := fanBody% n s 150 302 220000
def fanA23 (n s : Nat) : Nat := fanBody% n s 150 302 230000

/-- Past the captured-work limit: 150 bindings, 303 leaves. -/
def fanB1 (n s : Nat) : Nat := fanBody% n s 150 303 10000
def fanB2 (n s : Nat) : Nat := fanBody% n s 150 303 20000
def fanB3 (n s : Nat) : Nat := fanBody% n s 150 303 30000
def fanB4 (n s : Nat) : Nat := fanBody% n s 150 303 40000
def fanB5 (n s : Nat) : Nat := fanBody% n s 150 303 50000
def fanB6 (n s : Nat) : Nat := fanBody% n s 150 303 60000
def fanB7 (n s : Nat) : Nat := fanBody% n s 150 303 70000
def fanB8 (n s : Nat) : Nat := fanBody% n s 150 303 80000
def fanB9 (n s : Nat) : Nat := fanBody% n s 150 303 90000
def fanB10 (n s : Nat) : Nat := fanBody% n s 150 303 100000
def fanB11 (n s : Nat) : Nat := fanBody% n s 150 303 110000
def fanB12 (n s : Nat) : Nat := fanBody% n s 150 303 120000
def fanB13 (n s : Nat) : Nat := fanBody% n s 150 303 130000
def fanB14 (n s : Nat) : Nat := fanBody% n s 150 303 140000
def fanB15 (n s : Nat) : Nat := fanBody% n s 150 303 150000
def fanB16 (n s : Nat) : Nat := fanBody% n s 150 303 160000
def fanB17 (n s : Nat) : Nat := fanBody% n s 150 303 170000
def fanB18 (n s : Nat) : Nat := fanBody% n s 150 303 180000
def fanB19 (n s : Nat) : Nat := fanBody% n s 150 303 190000
def fanB20 (n s : Nat) : Nat := fanBody% n s 150 303 200000
def fanB21 (n s : Nat) : Nat := fanBody% n s 150 303 210000
def fanB22 (n s : Nat) : Nat := fanBody% n s 150 303 220000
def fanB23 (n s : Nat) : Nat := fanBody% n s 150 303 230000

def fanUnder (n s : Nat) : Nat × Nat :=
  (fanA1 n s + fanA2 n s + fanA3 n s + fanA4 n s + fanA5 n s + fanA6 n s +
    fanA7 n s + fanA8 n s + fanA9 n s + fanA10 n s + fanA11 n s + fanA12 n s +
    fanA13 n s + fanA14 n s + fanA15 n s + fanA16 n s + fanA17 n s + fanA18 n s +
    fanA19 n s + fanA20 n s + fanA21 n s + fanA22 n s + fanA23 n s, s)

def fanOver (n s : Nat) : Nat × Nat :=
  (fanB1 n s + fanB2 n s + fanB3 n s + fanB4 n s + fanB5 n s + fanB6 n s +
    fanB7 n s + fanB8 n s + fanB9 n s + fanB10 n s + fanB11 n s + fanB12 n s +
    fanB13 n s + fanB14 n s + fanB15 n s + fanB16 n s + fanB17 n s + fanB18 n s +
    fanB19 n s + fanB20 n s + fanB21 n s + fanB22 n s + fanB23 n s, s)

/-- The reference: twenty-three leaves `min s (K - 1) + o` and twenty-three sums
`C·n + C(C - 1)/2`. -/
def reference (c k n s : Nat) : Nat × Nat :=
  (23 * (min s (k - 1) + c * n + c * (c - 1) / 2) + 2760000, s)

end IxCCTests.Own.Budget

open IxCCTests.Own.Budget in
def main : IO Unit := do
  for (n, s) in [(0, 0), (1, 5), (7, 200), (100, 301), (3, 5000)] do
    unless fanUnder n s == reference 150 302 n s && fanOver n s == reference 150 303 n s do
      throw (IO.userError s!"fan {n} {s}: {fanUnder n s} {fanOver n s}")
  IO.println "ok"
