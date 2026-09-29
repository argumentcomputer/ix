import Compilatrix.Xv.Select.Basic
import Compilatrix.Lir.Semantics

/-!
# Addressing modes (rule 8) and load sinking (rules 3 and 9)

An address is a sum of scaled registers (the context register counts as
one) and a displacement, modulo 2^64 (`Lin`). Selection folds the
single-use address arithmetic of the current block into it: `addr m`,
`a + b`, `a ± k`, `a << s` for `s ≤ 3`, `a * {1,2,4,8}`, constants and
copies, all at width 64. A fold is kept only if the sum still encodes as
`[base + index·scale + disp32]` (`Lin.encode`); the folded statements are
consumed, since their only use is now inside the address. Addresses wrap
modulo 2^64 at Lir (`Lir.Addr.eval`) and on the machine
(`X86.MemAddr.eval`), so the fold is exact whenever the displacement, taken
modulo 2^64, fits a signed 32-bit field.

`sinkLoad?` moves a single-use load of the block into its consumer's
memory operand, provided no store or call lies between them (05 §4, 06
S18) and the consumer reads at most the loaded bytes.
-/

namespace Compilatrix.Xv.Select

open Compilatrix.Lir (VReg Word)

/-- `Σ multiplier · register + disp`, modulo 2^64. -/
structure Lin where
  terms : List (Base VReg × Nat) := []
  disp : Int := 0
  deriving Inhabited

def Lin.add (a b : Lin) : Lin := { terms := a.terms ++ b.terms, disp := a.disp + b.disp }

def Lin.scale (c : Nat) (a : Lin) : Lin :=
  { terms := a.terms.map fun (t, m) => (t, c * m), disp := c * a.disp }

def Lin.ofArg : Lir.Arg → Lin
  | .v x => { terms := [(.r x, 1)] }
  | .imm k => { disp := k.toNat }

def Lin.ofAddr (m : Lir.Addr) : Lin :=
  { terms := (match m.base with
        | some (.v x) => [(.r x, 1)]
        | some .ctx => [(.ctx, 1)]
        | none => []) ++
      (match m.index with
        | some (x, s) => [(.r x, s.word.toNat)]
        | none => [])
    disp := m.disp }

/-- `d` modulo 2^64, as a signed 64-bit integer. -/
def signed64 (d : Int) : Int :=
  let r := d % (2 ^ 64 : Int)
  if r < 2 ^ 63 then r else r - 2 ^ 64

def scaleOf : Nat → Option X86.Scale
  | 1 => some .one
  | 2 => some .two
  | 4 => some .four
  | 8 => some .eight
  | _ => none

/-- Encode terms as they stand: a base with multiplier 1 (the context
register only as a base) and an index with multiplier 1, 2, 4 or 8. -/
def encodeTerms (terms : List (Base VReg × Nat)) (disp : Int) : Option (Amode VReg) := do
  let d := signed64 disp
  guard (-2147483648 ≤ d ∧ d < 2147483648)
  let disp := Int32.ofInt d
  let terms := terms.filter fun (_, m) => m % 2 ^ 64 != 0
  let regIndex : Base VReg × Nat → Option (VReg × X86.Scale)
    | (.r x, m) => (x, ·) <$> scaleOf (m % 2 ^ 64)
    | (.ctx, _) => none
  match terms with
  | [] => some { disp }
  | [(b, 1)] => some { base := some b, disp }
  | [t] => some { index := some (← regIndex t), disp }
  | [(b, 1), t] => some { base := some b, index := some (← regIndex t), disp }
  | [t, (b, 1)] => some { base := some b, index := some (← regIndex t), disp }
  | _ => none

/-- Merge the multipliers of equal registers. -/
def mergeTerms (terms : List (Base VReg × Nat)) : List (Base VReg × Nat) :=
  terms.foldl (init := []) fun acc (t, m) =>
    match acc.find? (·.1 == t) with
    | some _ => acc.map fun (u, n) => if u == t then (u, n + m) else (u, n)
    | none => acc ++ [(t, m)]

/-- An addressing mode for the sum, as written or with equal registers
merged. -/
def Lin.encode (l : Lin) : Option (Amode VReg) :=
  encodeTerms l.terms l.disp <|> encodeTerms (mergeTerms l.terms) l.disp

/-- The address arithmetic a right-hand side contributes, if foldable. -/
def rhsLin : Lir.Rhs → Option Lin
  | .addr m => some (Lin.ofAddr m)
  | .arg a => some (Lin.ofArg a)
  | .bin .add .w64 a b => some ((Lin.ofArg a).add (Lin.ofArg b))
  | .bin .sub .w64 a (.imm k) => some ((Lin.ofArg a).add { disp := -(k.toNat : Int) })
  | .bin .shl .w64 a (.imm s) =>
      let s := (s &&& Lir.shiftMask .w64).toNat
      if s ≤ 3 then some ((Lin.ofArg a).scale (2 ^ s)) else none
  | .bin .mul .w64 a (.imm k) | .bin .mul .w64 (.imm k) a =>
      if [1, 2, 4, 8].contains k.toNat then some ((Lin.ofArg a).scale k.toNat) else none
  | _ => none

/-- Fold the block's single-use address arithmetic into `l` (without
committing): the result and the statements it consumes. -/
def foldLin (l : Lin) : SelM (Lin × List Nat) := do
  let mut l := l
  let mut used : List Nat := []
  for _ in [:4] do
    let mut changed := false
    for (t, m) in l.terms do
      let .r x := t | continue
      unless ← singleUse x do continue
      let some (j, rhs) ← defStmt? x | continue
      if used.contains j then continue
      let some sub := rhsLin rhs | continue
      let rest : Lin := { l with terms := l.terms.filter (·.1 != t) }
      let cand := rest.add (sub.scale m)
      if cand.encode.isSome then
        l := cand
        used := j :: used
        changed := true
        break
    unless changed do break
  return (l, used)

/-- Commit the consumed statements of a fold. -/
def commitFold (used : List Nat) : SelM Unit := do
  for j in used do
    consume j
    fire "amode.fold"

/-- The addressing mode of a Lir address, with rule 8's folding. -/
def buildAmode (m : Lir.Addr) : SelM (Amode VReg) := do
  let (l, used) ← foldLin (Lin.ofAddr m)
  match l.encode with
  | some a =>
      commitFold used
      return a
  | none =>
      match (Lin.ofAddr m).encode with
      | some a => return a
      | none => unsupported "address" s!"displacement {m.disp} does not fit a signed 32-bit field"

/-- Rules 3 and 9: the memory operand of a single-use load of at least
`bytes` bytes that defines `y` earlier in this block, with no store or call
between it and the current site `i`; the load is consumed. -/
def sinkLoad? (y : VReg) (i bytes : Nat) : SelM (Option (Amode VReg)) := do
  unless ← singleUse y do return none
  let some (j, .load w _ m) ← defStmt? y | return none
  unless w.bytes ≥ bytes && (← pureBetween j i) do return none
  let a ← buildAmode m
  consume j
  fire "load.sink"
  return some a

end Compilatrix.Xv.Select
