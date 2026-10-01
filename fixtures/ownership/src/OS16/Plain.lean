/-!
OS-16 `k0-reverse-plain` of the ownership suite (`fixtures/ownership/README.md`,
MT.7): the plain K0 reversal, whose annotated twin (OS-15) the pinned ix rejects.
Written for Compilatr.ix (Apache-2.0 OR MIT). `main` is the oracle driver for
`lean --run`: each stdin line `ROOT ARG…` prints that root's value on those
arguments.
-/

def build : Nat → List Nat → List Nat
  | 0, acc => acc
  | n+1, acc => build n (n :: acc)

def revAcc : List Nat → List Nat → List Nat
  | [], acc => acc
  | x :: xs, acc => revAcc xs (x :: acc)

def sumL : List Nat → Nat → Nat
  | [], s => s
  | x :: xs, s => sumL xs (s + x)

def entry (n : Nat) : Nat := sumL (revAcc (build n []) []) 0

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
