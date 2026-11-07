/-!
OS-03b `erased-data-dead-work` of the ownership suite (`fixtures/ownership/README.md`, MT.7).
Written for IxCC (Apache-2.0 OR MIT). The annotated source uses ix's
contract syntax; its plain twin is this text with the contract atoms and the
elaborator import deleted (`tests-own` checks this). `main` is the oracle
driver for `lean --run`: each stdin line `ROOT ARG…` prints that root's
value on those arguments.
-/

def ignoreFirst (_n : Nat) (m : Nat) : Nat := m + 1

def cube (n : Nat) : Nat := n * n * n

def entry (n : Nat) : Nat := ignoreFirst (cube n) n

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
