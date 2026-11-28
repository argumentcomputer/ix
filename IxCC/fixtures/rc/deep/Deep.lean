/-! Certificate-depth input (the producer's read-back, 2026-11-12). `deep n s x` tests `s` against
`n` thresholds in a chain of `Bool.casesOn (Nat.blt k s)`, and every leaf drops `s` and `x`, so the
canonical plain-RC ownership code nests one binding and one `case` (two levels) and one level of
the chain per test: a plain-RC certificate nests 3n + 6 deep. `deep240` (240 tests) nests 726,
past the certificate text's 512 (`Src.Hints.maxJsonDepth`), and `deep168` (168 tests) nests 510,
within it; the source stays within the consumer's expression depth (256). The roots return the
pair of the chain's result and their argument, so that the program allocates and the automatic
policy selects plain RC. The zero-RC certificate nests 8 deep whatever the chain. `main` checks
both roots against an independent formula in Lean's interpreter. -/
set_option maxRecDepth 100000

namespace IxCCTests.Cert.Deep

/-- `chain% s x k n`: `n` nested tests `Bool.casesOn (Nat.blt k s) k …`, thresholds from `k`. -/
syntax "chain% " ident ident num num : term
macro_rules
  | `(chain% $s:ident $x:ident $k:num $n:num) => do
    let kv := k.getNat
    let nv := n.getNat
    if nv == 0 then return ← `(nat_lit 0)
    let k0 := Lean.Syntax.mkNumLit (toString kv)
    let k1 := Lean.Syntax.mkNumLit (toString (kv + 1))
    let n1 := Lean.Syntax.mkNumLit (toString (nv - 1))
    `(Bool.casesOn (motive := fun _ => Nat) (Nat.blt (nat_lit $k0) $s) (nat_lit $k0) (chain% $s $x $k1 $n1))

def deep240chain (s x : Nat) : Nat := chain% s x 0 240
def deep168chain (s x : Nat) : Nat := chain% s x 0 168

/-- Past the depth limit under plain RC: 240 tests. -/
def deep240 (n : Nat) : Nat × Nat := (deep240chain n n, n)

/-- Within the depth limit under plain RC: 168 tests. -/
def deep168 (n : Nat) : Nat × Nat := (deep168chain n n, n)

/-- The reference: the first threshold `k < m` with `¬ (k < s)`, that is `min s m`, else `0` when
`s ≥ m`; so `if s < m then s else 0`. -/
def reference (m n : Nat) : Nat × Nat := (if n < m then n else 0, n)

end IxCCTests.Cert.Deep

open IxCCTests.Cert.Deep in
def main : IO Unit := do
  for n in [0, 1, 7, 167, 168, 169, 239, 240, 241, 5000] do
    unless deep240 n == reference 240 n && deep168 n == reference 168 n do
      throw (IO.userError s!"deep {n}: {deep240 n} {deep168 n}")
  IO.println "ok"
