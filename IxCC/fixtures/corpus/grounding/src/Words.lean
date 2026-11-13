/-! The `grounding` family's word subject (`docs/corpus.md`): fixed-width word arithmetic only, the
operations of `UInt8` to `UInt64` that stage W1 runs as primitives (DR2), with no decision, no
string and no `let`. Between them the roots reach every primitive operation kind at some width:
`add`, `sub`, `mul`, `div`, `mod`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight`, `complement`,
`neg`, `ofNat` (through `Nat.toUIntN` and literals), `toNat`, and conversions that narrow and widen.
Every root takes and returns `Nat`s; a `UInt64` result at or above `2^63` has no tagged word. -/

namespace Grounding.Words

/-- `UInt64` addition, wrapping at `2^64`. -/
def add64 (a b : Nat) : Nat := (a.toUInt64 + b.toUInt64).toNat

/-- `UInt32` multiply-add, wrapping at `2^32`. -/
def mulAdd32 (a b c : Nat) : Nat := (a.toUInt32 * b.toUInt32 + c.toUInt32).toNat

/-- `UInt8` exclusive or, shifts by literals, disjunction. -/
def mix8 (a b : Nat) : Nat := ((a.toUInt8 ^^^ b.toUInt8) <<< 3 ||| (a.toUInt8 >>> 5)).toNat

/-- `UInt16` negation, complement, conjunction, subtraction of a literal. -/
def neg16 (a b : Nat) : Nat := ((-(a.toUInt16) &&& ~~~b.toUInt16) - 1).toNat

/-- `UInt32` division and remainder (by zero: `0` and the dividend). -/
def divMod32 (a b : Nat) : Nat := (a.toUInt32 / b.toUInt32 + a.toUInt32 % b.toUInt32).toNat

/-- Conversions: narrowing reduces, widening keeps. -/
def convert (a : Nat) : Nat :=
  (a.toUInt64.toUInt8.toUInt32 + a.toUInt16.toUInt64.toUInt32 + a.toUInt32.toUInt16.toUInt32).toNat

/-- `UInt64` shifts by a variable amount (the amount wraps at the width), and a subtraction that
wraps. -/
def shift64 (a b : Nat) : Nat := ((a.toUInt64 <<< b.toUInt64) - (a.toUInt64 >>> b.toUInt64)).toNat

end Grounding.Words

/-- The oracle driver: each stdin line `ROOT ARG…` prints one value. -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  for line in input.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | [] => pure ()
    | root :: args =>
      let a := args.map String.toNat!
      IO.println <| match root, a with
        | "Grounding.Words.add64", [x, y] => toString (Grounding.Words.add64 x y)
        | "Grounding.Words.mulAdd32", [x, y, z] => toString (Grounding.Words.mulAdd32 x y z)
        | "Grounding.Words.mix8", [x, y] => toString (Grounding.Words.mix8 x y)
        | "Grounding.Words.neg16", [x, y] => toString (Grounding.Words.neg16 x y)
        | "Grounding.Words.divMod32", [x, y] => toString (Grounding.Words.divMod32 x y)
        | "Grounding.Words.convert", [x] => toString (Grounding.Words.convert x)
        | "Grounding.Words.shift64", [x, y] => toString (Grounding.Words.shift64 x y)
        | _, _ => "unknown root"
