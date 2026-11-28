/-!
VS0 of the one-pipeline plan (`plans/ONE-PIPELINE.md`, sections 2, 3 and 7): full-range
`UInt64` on the certified reference-counted route. `Vs0.loop` carries a `UInt64` whose top
bit is set on most iterations (a multiply by the 64-bit golden-ratio constant, an `xor` with a
shift of itself, an add); on the reference-counted route it is a raw 64-bit register
(`Cfg.Rc.Raw`): `imul`, `xor` and `shr` with no tag operation and no `natOverflow` test. A
tagged word exists only below `2⁶³`, so before raw registers every iteration whose value has
its top bit set failed with `natOverflow`. The result `a >>> 1` is below `2⁶³`.
-/

namespace Vs0

def loop : Nat → UInt64 → Nat
  | 0, a => (a >>> 1).toNat
  | n+1, a => loop n (((a * (0x9E3779B97F4A7C15 : UInt64)) ^^^ (a >>> (29 : UInt64))) + n.toUInt64)

def vs0 (n : Nat) : Nat := loop n n.toUInt64

end Vs0

/-- The corpus oracle driver: each stdin line `ROOT ARG…` prints one value. -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  for line in input.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | [] => pure ()
    | root :: args =>
      let a := args.map String.toNat!
      IO.println <| match root, a with
        | "Vs0.vs0", [x] => toString (Vs0.vs0 x)
        | _, _ => s!"unknown root {root} {args}"
