/-!
OS-02 `subtype-decidable` of the ownership suite (`fixtures/ownership/README.md`,
MT.7): a plain program whose `Subtype` and `Decidable` erasure costs nothing.
Written for Compilatr.ix (Apache-2.0 OR MIT). `main` is the oracle driver for
`lean --run`: each stdin line `ROOT ARG…` prints that root's value on those
arguments.
-/

def mkPos (n : Nat) : {k : Nat // k > 0} := ⟨n+1, Nat.succ_pos n⟩

def clampSmall (n : Nat) : Nat := if n < 5 then n else 5

def entry (n : Nat) : Nat := (mkPos (clampSmall n)).val

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  for line in input.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | [] => pure ()
    | root :: args =>
      let a := args.map String.toNat!
      IO.println <| match root, a with
        | "entry", [x] => toString (entry x)
        | _, _ => "no such root"
