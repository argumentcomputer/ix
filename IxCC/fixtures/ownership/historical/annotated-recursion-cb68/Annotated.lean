import Ix.Compile.SourceContract.Elab

/-!
OS04 `erased-type-recursive` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P31LenErasedType`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def len {0 α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: rest => len rest + 1

def entry (n : Nat) : Nat := len [n, n, n]

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
