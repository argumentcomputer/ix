/-! RC budget fixture (heap stage 2, milestone 2). A fan function takes `s` and `C` parameters
`x₀ … x_{C-1}`, branches on `s` through a balanced tree of `Bool.casesOn (Nat.blt s m)` with `K`
leaves (leaf `lo` returns `lo + o`), then returns the leaf plus the sum of every `xᵢ`. In the
compiled program the code after the branch is a join that captures the `C` parameters and that
every leaf jumps to, so an ownership certificate makes the checker take `C` captured tokens at each
of the `K` jumps and `C` at the join's declaration: `Own.Plain.Certificate.capturedWork`, which
admission bounds by `Anf.maxCapturedWork` (2²⁰). A root calls forty-one fan functions (distinct by
their offsets `o`, so that content addressing keeps them apart), in twenty-one parts of at most
two calls, with every `xᵢ` its own `n`, sums them and returns a pair, so that the program allocates
and the automatic policy selects plain RC: `fanUnder` (C = 197) is within the limit, `fanOver`
(C = 198) past it. A part is a global of its own because the canonical placement gives `n` one
`inc` per extra copy passed, each nesting the ownership code one level: two calls nest a part's
code about 400 deep, within the certificate text's 512 (`Src.Hints.maxJsonDepth`), where the
four parts of ten or eleven calls this input had first nested 2,208 deep, past it.
The captured values are parameters, which cost the middle end no node, and the terms are written
without type-class instances or `if` (primitives, raw literals, `Bool.casesOn`), so that each fan
function stays within the consumer's expression depth (256: the parameters nest) and the middle
end's node and back-end work budgets. The canonical placement captures two more variables in
scope besides the parameters. `main` checks both roots against an independent formula in Lean's
interpreter. -/

namespace IxCCTests.Own.Budget

/-- `fanTree% s o lo hi`: the leaves `lo + o … hi - 1 + o` under a balanced tree of
`Bool.casesOn (Nat.blt s m)` tests. -/
syntax "fanTree% " ident num num num : term
macro_rules
  | `(fanTree% $s:ident $o:num $lo:num $hi:num) => do
    let lo := lo.getNat
    let hi := hi.getNat
    if hi ≤ lo + 1 then
      let leaf := Lean.Syntax.mkNumLit (toString (lo + o.getNat))
      return ← `(nat_lit $leaf)
    let mid := (lo + hi) / 2
    let lo' := Lean.Syntax.mkNumLit (toString lo)
    let mid' := Lean.Syntax.mkNumLit (toString mid)
    let hi' := Lean.Syntax.mkNumLit (toString hi)
    `(Bool.casesOn (motive := fun _ => Nat) (Nat.blt $s (nat_lit $mid'))
        (fanTree% $s $o $mid' $hi') (fanTree% $s $o $lo' $mid'))

/-- `fanSum% lo hi`: the balanced sum of the identifiers `x{lo} … x{hi - 1}`. -/
syntax "fanSum% " num num : term
macro_rules
  | `(fanSum% $lo:num $hi:num) => do
    let lo := lo.getNat
    let hi := hi.getNat
    if hi ≤ lo then return ← `(nat_lit 0)
    if hi == lo + 1 then return Lean.mkIdent (Lean.Name.mkSimple s!"x{lo}")
    let mid := (lo + hi) / 2
    let lo' := Lean.Syntax.mkNumLit (toString lo)
    let mid' := Lean.Syntax.mkNumLit (toString mid)
    let hi' := Lean.Syntax.mkNumLit (toString hi)
    `(Nat.add (fanSum% $lo' $mid') (fanSum% $mid' $hi'))

/-- `fanType% C`: `Nat → … → Nat` with `C + 1` arguments. -/
syntax "fanType% " num : term
macro_rules
  | `(fanType% $c:num) => do
    let mut t ← `(Nat)
    for _ in [0:c.getNat + 1] do
      t ← `(Nat → $t)
    return t

/-- `fanFun% C K o`: `fun s x₀ … x_{C-1} =>` the tree of `K` leaves on `s`, then the leaf plus
the sum of the parameters. -/
syntax "fanFun% " num num num : term
macro_rules
  | `(fanFun% $c:num $k:num $o:num) => do
    let s := Lean.mkIdent `s
    let body ← `(let r := fanTree% $s $o 0 $k; Nat.add r (fanSum% 0 $c))
    let xs := (List.range c.getNat).map fun i => Lean.mkIdent (Lean.Name.mkSimple s!"x{i}")
    let inner ← xs.foldrM (s := Lean.TSyntax `term) (fun x b => `(fun ($x:ident : Nat) => $b)) body
    `(fun ($s:ident : Nat) => $inner)

/-- `fanCalls% p n s C lo hi`: the balanced sum of `p{j} s n … n` (`C` copies of `n`) for `j` in
`lo … hi - 1`. -/
syntax "fanCalls% " ident ident ident num num num : term
macro_rules
  | `(fanCalls% $p:ident $n:ident $s:ident $c:num $lo:num $hi:num) => do
    let lo := lo.getNat
    let hi := hi.getNat
    if hi ≤ lo then return ← `(nat_lit 0)
    if hi == lo + 1 then
      let f := Lean.mkIdent (Lean.Name.mkSimple s!"{p.getId}{lo}")
      let args := (List.replicate c.getNat n).toArray
      return ← `($f $s $args*)
    let mid := (lo + hi) / 2
    let lo' := Lean.Syntax.mkNumLit (toString lo)
    let mid' := Lean.Syntax.mkNumLit (toString mid)
    let hi' := Lean.Syntax.mkNumLit (toString hi)
    `(Nat.add (fanCalls% $p $n $s $c $lo' $mid') (fanCalls% $p $n $s $c $mid' $hi'))

/-- Within the captured-work limit: 197 parameters, 127 leaves. -/
def fanA1 : fanType% 197 := fanFun% 197 127 10000
def fanA2 : fanType% 197 := fanFun% 197 127 20000
def fanA3 : fanType% 197 := fanFun% 197 127 30000
def fanA4 : fanType% 197 := fanFun% 197 127 40000
def fanA5 : fanType% 197 := fanFun% 197 127 50000
def fanA6 : fanType% 197 := fanFun% 197 127 60000
def fanA7 : fanType% 197 := fanFun% 197 127 70000
def fanA8 : fanType% 197 := fanFun% 197 127 80000
def fanA9 : fanType% 197 := fanFun% 197 127 90000
def fanA10 : fanType% 197 := fanFun% 197 127 100000
def fanA11 : fanType% 197 := fanFun% 197 127 110000
def fanA12 : fanType% 197 := fanFun% 197 127 120000
def fanA13 : fanType% 197 := fanFun% 197 127 130000
def fanA14 : fanType% 197 := fanFun% 197 127 140000
def fanA15 : fanType% 197 := fanFun% 197 127 150000
def fanA16 : fanType% 197 := fanFun% 197 127 160000
def fanA17 : fanType% 197 := fanFun% 197 127 170000
def fanA18 : fanType% 197 := fanFun% 197 127 180000
def fanA19 : fanType% 197 := fanFun% 197 127 190000
def fanA20 : fanType% 197 := fanFun% 197 127 200000
def fanA21 : fanType% 197 := fanFun% 197 127 210000
def fanA22 : fanType% 197 := fanFun% 197 127 220000
def fanA23 : fanType% 197 := fanFun% 197 127 230000
def fanA24 : fanType% 197 := fanFun% 197 127 240000
def fanA25 : fanType% 197 := fanFun% 197 127 250000
def fanA26 : fanType% 197 := fanFun% 197 127 260000
def fanA27 : fanType% 197 := fanFun% 197 127 270000
def fanA28 : fanType% 197 := fanFun% 197 127 280000
def fanA29 : fanType% 197 := fanFun% 197 127 290000
def fanA30 : fanType% 197 := fanFun% 197 127 300000
def fanA31 : fanType% 197 := fanFun% 197 127 310000
def fanA32 : fanType% 197 := fanFun% 197 127 320000
def fanA33 : fanType% 197 := fanFun% 197 127 330000
def fanA34 : fanType% 197 := fanFun% 197 127 340000
def fanA35 : fanType% 197 := fanFun% 197 127 350000
def fanA36 : fanType% 197 := fanFun% 197 127 360000
def fanA37 : fanType% 197 := fanFun% 197 127 370000
def fanA38 : fanType% 197 := fanFun% 197 127 380000
def fanA39 : fanType% 197 := fanFun% 197 127 390000
def fanA40 : fanType% 197 := fanFun% 197 127 400000
def fanA41 : fanType% 197 := fanFun% 197 127 410000

/-- Past the captured-work limit: 198 parameters, 127 leaves. -/
def fanB1 : fanType% 198 := fanFun% 198 127 10000
def fanB2 : fanType% 198 := fanFun% 198 127 20000
def fanB3 : fanType% 198 := fanFun% 198 127 30000
def fanB4 : fanType% 198 := fanFun% 198 127 40000
def fanB5 : fanType% 198 := fanFun% 198 127 50000
def fanB6 : fanType% 198 := fanFun% 198 127 60000
def fanB7 : fanType% 198 := fanFun% 198 127 70000
def fanB8 : fanType% 198 := fanFun% 198 127 80000
def fanB9 : fanType% 198 := fanFun% 198 127 90000
def fanB10 : fanType% 198 := fanFun% 198 127 100000
def fanB11 : fanType% 198 := fanFun% 198 127 110000
def fanB12 : fanType% 198 := fanFun% 198 127 120000
def fanB13 : fanType% 198 := fanFun% 198 127 130000
def fanB14 : fanType% 198 := fanFun% 198 127 140000
def fanB15 : fanType% 198 := fanFun% 198 127 150000
def fanB16 : fanType% 198 := fanFun% 198 127 160000
def fanB17 : fanType% 198 := fanFun% 198 127 170000
def fanB18 : fanType% 198 := fanFun% 198 127 180000
def fanB19 : fanType% 198 := fanFun% 198 127 190000
def fanB20 : fanType% 198 := fanFun% 198 127 200000
def fanB21 : fanType% 198 := fanFun% 198 127 210000
def fanB22 : fanType% 198 := fanFun% 198 127 220000
def fanB23 : fanType% 198 := fanFun% 198 127 230000
def fanB24 : fanType% 198 := fanFun% 198 127 240000
def fanB25 : fanType% 198 := fanFun% 198 127 250000
def fanB26 : fanType% 198 := fanFun% 198 127 260000
def fanB27 : fanType% 198 := fanFun% 198 127 270000
def fanB28 : fanType% 198 := fanFun% 198 127 280000
def fanB29 : fanType% 198 := fanFun% 198 127 290000
def fanB30 : fanType% 198 := fanFun% 198 127 300000
def fanB31 : fanType% 198 := fanFun% 198 127 310000
def fanB32 : fanType% 198 := fanFun% 198 127 320000
def fanB33 : fanType% 198 := fanFun% 198 127 330000
def fanB34 : fanType% 198 := fanFun% 198 127 340000
def fanB35 : fanType% 198 := fanFun% 198 127 350000
def fanB36 : fanType% 198 := fanFun% 198 127 360000
def fanB37 : fanType% 198 := fanFun% 198 127 370000
def fanB38 : fanType% 198 := fanFun% 198 127 380000
def fanB39 : fanType% 198 := fanFun% 198 127 390000
def fanB40 : fanType% 198 := fanFun% 198 127 400000
def fanB41 : fanType% 198 := fanFun% 198 127 410000

/-- The calls are split in parts of 2 (each a global of its own), so that each part's ownership
code nests within the certificate text's depth limit and each global within the node budget. -/
def fanUnder1 (n s : Nat) : Nat := fanCalls% fanA n s 197 1 3
def fanUnder2 (n s : Nat) : Nat := fanCalls% fanA n s 197 3 5
def fanUnder3 (n s : Nat) : Nat := fanCalls% fanA n s 197 5 7
def fanUnder4 (n s : Nat) : Nat := fanCalls% fanA n s 197 7 9
def fanUnder5 (n s : Nat) : Nat := fanCalls% fanA n s 197 9 11
def fanUnder6 (n s : Nat) : Nat := fanCalls% fanA n s 197 11 13
def fanUnder7 (n s : Nat) : Nat := fanCalls% fanA n s 197 13 15
def fanUnder8 (n s : Nat) : Nat := fanCalls% fanA n s 197 15 17
def fanUnder9 (n s : Nat) : Nat := fanCalls% fanA n s 197 17 19
def fanUnder10 (n s : Nat) : Nat := fanCalls% fanA n s 197 19 21
def fanUnder11 (n s : Nat) : Nat := fanCalls% fanA n s 197 21 23
def fanUnder12 (n s : Nat) : Nat := fanCalls% fanA n s 197 23 25
def fanUnder13 (n s : Nat) : Nat := fanCalls% fanA n s 197 25 27
def fanUnder14 (n s : Nat) : Nat := fanCalls% fanA n s 197 27 29
def fanUnder15 (n s : Nat) : Nat := fanCalls% fanA n s 197 29 31
def fanUnder16 (n s : Nat) : Nat := fanCalls% fanA n s 197 31 33
def fanUnder17 (n s : Nat) : Nat := fanCalls% fanA n s 197 33 35
def fanUnder18 (n s : Nat) : Nat := fanCalls% fanA n s 197 35 37
def fanUnder19 (n s : Nat) : Nat := fanCalls% fanA n s 197 37 39
def fanUnder20 (n s : Nat) : Nat := fanCalls% fanA n s 197 39 41
def fanUnder21 (n s : Nat) : Nat := fanCalls% fanA n s 197 41 42

def fanUnder (n s : Nat) : Nat × Nat :=
  ((Nat.add (Nat.add (Nat.add (Nat.add (fanUnder1 n s) (fanUnder2 n s)) (Nat.add (fanUnder3 n s) (Nat.add (fanUnder4 n s) (fanUnder5 n s)))) (Nat.add (Nat.add (fanUnder6 n s) (fanUnder7 n s)) (Nat.add (fanUnder8 n s) (Nat.add (fanUnder9 n s) (fanUnder10 n s))))) (Nat.add (Nat.add (Nat.add (fanUnder11 n s) (fanUnder12 n s)) (Nat.add (fanUnder13 n s) (Nat.add (fanUnder14 n s) (fanUnder15 n s)))) (Nat.add (Nat.add (fanUnder16 n s) (Nat.add (fanUnder17 n s) (fanUnder18 n s))) (Nat.add (fanUnder19 n s) (Nat.add (fanUnder20 n s) (fanUnder21 n s)))))), s)

def fanOver1 (n s : Nat) : Nat := fanCalls% fanB n s 198 1 3
def fanOver2 (n s : Nat) : Nat := fanCalls% fanB n s 198 3 5
def fanOver3 (n s : Nat) : Nat := fanCalls% fanB n s 198 5 7
def fanOver4 (n s : Nat) : Nat := fanCalls% fanB n s 198 7 9
def fanOver5 (n s : Nat) : Nat := fanCalls% fanB n s 198 9 11
def fanOver6 (n s : Nat) : Nat := fanCalls% fanB n s 198 11 13
def fanOver7 (n s : Nat) : Nat := fanCalls% fanB n s 198 13 15
def fanOver8 (n s : Nat) : Nat := fanCalls% fanB n s 198 15 17
def fanOver9 (n s : Nat) : Nat := fanCalls% fanB n s 198 17 19
def fanOver10 (n s : Nat) : Nat := fanCalls% fanB n s 198 19 21
def fanOver11 (n s : Nat) : Nat := fanCalls% fanB n s 198 21 23
def fanOver12 (n s : Nat) : Nat := fanCalls% fanB n s 198 23 25
def fanOver13 (n s : Nat) : Nat := fanCalls% fanB n s 198 25 27
def fanOver14 (n s : Nat) : Nat := fanCalls% fanB n s 198 27 29
def fanOver15 (n s : Nat) : Nat := fanCalls% fanB n s 198 29 31
def fanOver16 (n s : Nat) : Nat := fanCalls% fanB n s 198 31 33
def fanOver17 (n s : Nat) : Nat := fanCalls% fanB n s 198 33 35
def fanOver18 (n s : Nat) : Nat := fanCalls% fanB n s 198 35 37
def fanOver19 (n s : Nat) : Nat := fanCalls% fanB n s 198 37 39
def fanOver20 (n s : Nat) : Nat := fanCalls% fanB n s 198 39 41
def fanOver21 (n s : Nat) : Nat := fanCalls% fanB n s 198 41 42

def fanOver (n s : Nat) : Nat × Nat :=
  ((Nat.add (Nat.add (Nat.add (Nat.add (fanOver1 n s) (fanOver2 n s)) (Nat.add (fanOver3 n s) (Nat.add (fanOver4 n s) (fanOver5 n s)))) (Nat.add (Nat.add (fanOver6 n s) (fanOver7 n s)) (Nat.add (fanOver8 n s) (Nat.add (fanOver9 n s) (fanOver10 n s))))) (Nat.add (Nat.add (Nat.add (fanOver11 n s) (fanOver12 n s)) (Nat.add (fanOver13 n s) (Nat.add (fanOver14 n s) (fanOver15 n s)))) (Nat.add (Nat.add (fanOver16 n s) (Nat.add (fanOver17 n s) (fanOver18 n s))) (Nat.add (fanOver19 n s) (Nat.add (fanOver20 n s) (fanOver21 n s)))))), s)

/-- The reference: forty-one leaves `min s (K - 1) + o` and forty-one sums `C·n`. -/
def reference (c k n s : Nat) : Nat × Nat :=
  (41 * (min s (k - 1) + c * n) + 8610000, s)

end IxCCTests.Own.Budget

open IxCCTests.Own.Budget in
def main : IO Unit := do
  for (n, s) in [(0, 0), (1, 5), (7, 100), (100, 126), (3, 5000)] do
    unless fanUnder n s == reference 197 127 n s && fanOver n s == reference 198 127 n s do
      throw (IO.userError s!"fan {n} {s}: {fanUnder n s} {fanOver n s}")
  IO.println "ok"
