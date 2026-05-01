import Ix.Aiur.Meta
import Ix.Aiur.Compiler
import Ix.Aiur.Protocol
import Ix.Benchmark.Bench

open BgroupM

def toplevel := ⟦
  enum Nat {
    Zero,
    Succ(&Nat)
  }

  fn g_to_nat(g: G) -> Nat {
    match g {
      0 => Nat.Zero,
      _ => Nat.Succ(store(g_to_nat(g - 1))),
    }
  }

  fn nat_to_g(n: Nat) -> G {
    match n {
      Nat.Zero => 0,
      Nat.Succ(ptr) => nat_to_g(load(ptr)) + 1,
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

  pub fn main(g: G) -> G {
    nat_to_g(nat_fib(g_to_nat(g)))
  }
⟧

def commitmentParameters : Aiur.CommitmentParameters := {
  logBlowup := 1
  capHeight := 0
}

def friParameters : Aiur.FriParameters := {
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 100
  commitProofOfWorkBits := 20
  queryProofOfWorkBits := 0
}

-- Stages the e2e proving pipeline through `benchStep`: each call times a stage
-- and threads its output into the next. `prove fib 10` is one-shot because a
-- single iteration already runs in the hundreds of milliseconds.
--
-- `simplify toplevel` and `compile decls` are side-benches that measure
-- sub-steps of `Toplevel.compile`. They sit inside a `skipE2E` block so they
-- show up in the report without double-counting against `compile`.
def main : IO Unit := do
  let decls ← match toplevel.checkAndSimplify with
    | .error e => throw (IO.userError s!"{repr e}")
    | .ok decls => pure decls
  let concDecls ← match decls.concretize with
    | .error e => throw (IO.userError s!"{repr e}")
    | .ok cd => pure cd
  let _ ← bgroup "nat_fib" { e2e := true } do
    skipE2E
    bench "simplify toplevel" Aiur.Source.Toplevel.checkAndSimplify toplevel
    bench "concretize decls" Aiur.Typed.Decls.concretize decls
    bench "compile decls" Aiur.Concrete.Decls.toBytecode concDecls
    countInE2E
    let compiled ← benchStepE "compile" Aiur.Source.Toplevel.compile toplevel
    let system ← benchStep "build AiurSystem"
        (Aiur.AiurSystem.build compiled.bytecode) commitmentParameters
    let funIdx := compiled.getFuncIdx `main |>.get!
    let (claim, proof, _) ← benchStep "prove fib 10"
        (Aiur.AiurSystem.prove system friParameters funIdx #[10]) default (oneShot := true)
    IO.println s!"proof size: {proof.toBytes.size} bytes"
    let _ ← benchStepE "verify fib 10"
        (Aiur.AiurSystem.verify system friParameters claim) proof
