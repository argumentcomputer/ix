import Ix.Aiur.Bytecode
import Ix.Aiur.Simple
import Ix.Aiur.Meta

def toplevel := ⟦
  enum Nat {
    Succ(&Nat),
    Zero
  }

  fn even(m: Nat) -> u1 {
    match m {
      Nat.Zero => 1u1,
      Nat.Succ m => odd(load(m)),
    }
  }

  fn odd(m: Nat) -> u1 {
    match m {
      Nat.Zero => 0u1,
      Nat.Succ m => even(load(m)),
    }
  }
⟧

def main : IO Unit := do
  match Aiur.checkAndSimplifyToplevel toplevel with
  | .ok decls => do
    let bytecode := decls.compile
    println! (repr bytecode).pretty
  | .error error => println! (repr error).pretty

#eval main
