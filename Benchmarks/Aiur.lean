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

def proveE2E (name: Lean.Name) : IO UInt32 := do
  let compiled ← match toplevel.compile with
    | .error e => IO.eprintln e; return 1
    | .ok compiled => pure compiled
  let system := Aiur.AiurSystem.build compiled.bytecode commitmentParameters
  let funIdx := compiled.getFuncIdx name |>.get!
  let (claim, proof, _) := system.prove friParameters funIdx #[10] default
  match system.verify friParameters claim proof with
  | .ok _ => return 0
  | .error e => IO.eprintln e; return 1

/-- Compile `toplevel` once so the per-stage benchmarks can reuse the result. -/
def compileToplevel : IO Aiur.CompiledToplevel := do
  match toplevel.compile with
  | .error e => throw (IO.userError e)
  | .ok compiled => pure compiled

-- End-to-end proof generation and verification benchmark. `samplingMode`
-- defaults to `.auto`, which will fall back to flat for this slow bench.
def proveE2EBench : IO $ Array BenchReport :=
  bgroup "prove E2E" {} do
    benchIO "fib 10" proveE2E `main

-- Individual benchmarks of each step from `proveE2E`. Each stage has different
-- `α`/`β` types, so they live in their own `bgroup` even though they share
-- the `nat_fib` group name on disk.

def toplevelBench : IO $ Array BenchReport :=
  bgroup "nat_fib" {} do
    bench "simplify toplevel" Aiur.Toplevel.checkAndSimplify toplevel

def compileBench : IO $ Array BenchReport := do
  match toplevel.checkAndSimplify with
  | .error e => throw (IO.userError s!"{repr e}")
  | .ok decls =>
    bgroup "nat_fib" {} do
      bench "compile decls" Aiur.TypedDecls.toBytecode decls

def buildAiurSystemBench : IO $ Array BenchReport := do
  let compiled ← compileToplevel
  bgroup "nat_fib" {} do
    bench "build AiurSystem" (Aiur.AiurSystem.build compiled.bytecode) commitmentParameters

def proveBench : IO $ Array BenchReport := do
  let compiled ← compileToplevel
  let system := Aiur.AiurSystem.build compiled.bytecode commitmentParameters
  let funIdx := compiled.getFuncIdx `main |>.get!
  bgroup "nat_fib" {} do
    bench "prove fib 10" (Aiur.AiurSystem.prove system friParameters funIdx #[10]) default

def verifyBench : IO $ Array BenchReport := do
  let compiled ← compileToplevel
  let system := Aiur.AiurSystem.build compiled.bytecode commitmentParameters
  let funIdx := compiled.getFuncIdx `main |>.get!
  let (claim, proof, _) := system.prove friParameters funIdx #[10] default
  bgroup "nat_fib" {} do
    bench "verify fib 10" (Aiur.AiurSystem.verify system friParameters claim) proof

def main (args : List String) : IO Unit := do
  setBenchArgs args
  let _ ← toplevelBench
  let _ ← compileBench
  let _ ← buildAiurSystemBench
  let _ ← proveBench
  let _ ← verifyBench
