import Ix.Aiur.Meta
import Ix.Aiur.Simple
import Ix.Aiur.Compile
import Ix.Aiur.Protocol

def toplevel := ⟦
  enum Nat {
    Zero,
    Succ(&Nat)
  }

  fn g_to_nat(g: G) -> Nat {
    match g {
      0 => Nat.Zero,
      _ => Nat.Succ(store(g_to_nat(sub(g, 1)))),
    }
  }

  fn nat_to_g(n: Nat) -> G {
    match n {
      Nat.Zero => 0,
      Nat.Succ(ptr) => add(nat_to_g(load(ptr)), 1),
    }
  }

  fn nat_add(a: Nat, b: Nat) -> Nat {
    match b {
      Nat.Zero => a,
      Nat.Succ(b'ptr) => nat_add(Nat.Succ(store(a)), load(b'ptr)),
    }
  }

  fn nat_fib(n: Nat) -> Nat {
    match n {
      Nat.Zero => Nat.Succ(store(Nat.Zero)),
      Nat.Succ(n'ptr) =>
        let n' = load(n'ptr);
        match n' {
          Nat.Zero => Nat.Succ(store(Nat.Zero)),
          Nat.Succ(n''ptr) =>
            let n'' = load(n''ptr);
            nat_add(nat_fib(n'), nat_fib(n'')),
        },
    }
  }

  fn main(g: G) -> G {
    nat_to_g(nat_fib(g_to_nat(g)))
  }
⟧

def friParameters : Aiur.FriParameters := {
  logBlowup := 1
  logFinalPolyLen := 0
  numQueries := 100
  proofOfWorkBits := 20
}

def main (_args : List String) : IO UInt32 := do
  match toplevel.checkAndSimplify with
  | .error e => IO.eprintln e; return 1
  | .ok decls =>
    let bytecode := decls.compile
    let system := Aiur.AiurSystem.build bytecode
    let funIdx := toplevel.getFuncIdx `main |>.get!
    let (claim, proof) := system.prove friParameters funIdx #[26]
    match system.verify friParameters claim proof with
    | .ok _ => return 0
    | .error e => IO.eprintln e; return 1
