/-!
The Phase 1 ABI and readback matrix (phase 1 plan, MT.4; research §9.4.5):
roots of arity 0–6 returning `Nat`, `Bool` and an enumeration, each called
natively in a test executable IxCC writes (arguments in the SysV registers
after the region, the callee-saved registers and `rsp` checked) and read back
by `Rt.readback` and by the tests' independent decoder.

A root of arity `k` mixes its arguments position by position
(`a₀ ^^^ (a₁ >>> 1) ^^^ … ^^^ (aₖ₋₁ >>> (k − 1))`), so an argument passed in
the wrong register, or truncated, changes the result; the mix of words
below `2⁶³` stays below `2⁶³`. The `Bool` and `Tri` roots branch on the mix.
Arity 6 is beyond the entry wrapper's five arguments: declined with
`rt: rt.params`.
-/

namespace Abi

/-- An enumeration: its values are the immediates `1`, `3`, `5`. -/
inductive Tri where
  | lo
  | mid
  | hi

def Tri.ofNat (n : Nat) : Tri :=
  match n % 3 with
  | 0 => .lo
  | 1 => .mid
  | _ => .hi

def nat0 : Nat := 42
def bool0 : Bool := true
def tri0 : Tri := .hi

def nat1 (a : Nat) : Nat := a
def bool1 (a : Nat) : Bool := a % 3 == 1
def tri1 (a : Nat) : Tri := Tri.ofNat a

def nat2 (a b : Nat) : Nat := a ^^^ (b >>> 1)
def bool2 (a b : Nat) : Bool := (a ^^^ (b >>> 1)) % 3 == 1
def tri2 (a b : Nat) : Tri := Tri.ofNat (a ^^^ (b >>> 1))

def nat3 (a b c : Nat) : Nat := a ^^^ (b >>> 1) ^^^ (c >>> 2)
def bool3 (a b c : Nat) : Bool := (a ^^^ (b >>> 1) ^^^ (c >>> 2)) % 3 == 1
def tri3 (a b c : Nat) : Tri := Tri.ofNat (a ^^^ (b >>> 1) ^^^ (c >>> 2))

def nat4 (a b c d : Nat) : Nat := a ^^^ (b >>> 1) ^^^ (c >>> 2) ^^^ (d >>> 3)
def bool4 (a b c d : Nat) : Bool := (a ^^^ (b >>> 1) ^^^ (c >>> 2) ^^^ (d >>> 3)) % 3 == 1
def tri4 (a b c d : Nat) : Tri := Tri.ofNat (a ^^^ (b >>> 1) ^^^ (c >>> 2) ^^^ (d >>> 3))

def nat5 (a b c d e : Nat) : Nat := a ^^^ (b >>> 1) ^^^ (c >>> 2) ^^^ (d >>> 3) ^^^ (e >>> 4)
def bool5 (a b c d e : Nat) : Bool := (a ^^^ (b >>> 1) ^^^ (c >>> 2) ^^^ (d >>> 3) ^^^ (e >>> 4)) % 3 == 1
def tri5 (a b c d e : Nat) : Tri := Tri.ofNat (a ^^^ (b >>> 1) ^^^ (c >>> 2) ^^^ (d >>> 3) ^^^ (e >>> 4))

def nat6 (a b c d e f : Nat) : Nat := a ^^^ (b >>> 1) ^^^ (c >>> 2) ^^^ (d >>> 3) ^^^ (e >>> 4) ^^^ (f >>> 5)
def bool6 (a b c d e f : Nat) : Bool := (a ^^^ (b >>> 1) ^^^ (c >>> 2) ^^^ (d >>> 3) ^^^ (e >>> 4) ^^^ (f >>> 5)) % 3 == 1
def tri6 (a b c d e f : Nat) : Tri := Tri.ofNat (a ^^^ (b >>> 1) ^^^ (c >>> 2) ^^^ (d >>> 3) ^^^ (e >>> 4) ^^^ (f >>> 5))

end Abi

/-- The constructor index of a `Tri`. -/
def Abi.Tri.idx : Abi.Tri → Nat
  | .lo => 0
  | .mid => 1
  | .hi => 2

/-- The oracle driver: each stdin line `ROOT ARG…` prints one value (a `Tri`
as its constructor index). -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  for line in input.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | [] => pure ()
    | root :: args =>
      let x := args.map String.toNat!
      IO.println <| match root, x with
        | "Abi.nat0", [] => toString Abi.nat0
        | "Abi.bool0", [] => toString Abi.bool0
        | "Abi.tri0", [] => toString Abi.tri0.idx
        | "Abi.nat1", [x0] => toString (Abi.nat1 x0)
        | "Abi.bool1", [x0] => toString (Abi.bool1 x0)
        | "Abi.tri1", [x0] => toString (Abi.tri1 x0).idx
        | "Abi.nat2", [x0, x1] => toString (Abi.nat2 x0 x1)
        | "Abi.bool2", [x0, x1] => toString (Abi.bool2 x0 x1)
        | "Abi.tri2", [x0, x1] => toString (Abi.tri2 x0 x1).idx
        | "Abi.nat3", [x0, x1, x2] => toString (Abi.nat3 x0 x1 x2)
        | "Abi.bool3", [x0, x1, x2] => toString (Abi.bool3 x0 x1 x2)
        | "Abi.tri3", [x0, x1, x2] => toString (Abi.tri3 x0 x1 x2).idx
        | "Abi.nat4", [x0, x1, x2, x3] => toString (Abi.nat4 x0 x1 x2 x3)
        | "Abi.bool4", [x0, x1, x2, x3] => toString (Abi.bool4 x0 x1 x2 x3)
        | "Abi.tri4", [x0, x1, x2, x3] => toString (Abi.tri4 x0 x1 x2 x3).idx
        | "Abi.nat5", [x0, x1, x2, x3, x4] => toString (Abi.nat5 x0 x1 x2 x3 x4)
        | "Abi.bool5", [x0, x1, x2, x3, x4] => toString (Abi.bool5 x0 x1 x2 x3 x4)
        | "Abi.tri5", [x0, x1, x2, x3, x4] => toString (Abi.tri5 x0 x1 x2 x3 x4).idx
        | _, _ => s!"unknown root {root} {args}"
