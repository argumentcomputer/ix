import Ix.Aiur.Meta
import Ix.Aiur.Simple
import Ix.Aiur.Compile
import Ix.Aiur.Protocol
import Ix.Benchmark.Bench

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

  fn main(g: G) -> G {
    nat_to_g(nat_fib(g_to_nat(g)))
  }
⟧

def commitmentParameters : Aiur.CommitmentParameters := {
  logBlowup := 1
}

def friParameters : Aiur.FriParameters := {
  logFinalPolyLen := 0
  numQueries := 100
  proofOfWorkBits := 20
}

def proveE2E (name: Lean.Name) : IO UInt32 := do
  match toplevel.checkAndSimplify with
  | .error e => IO.eprintln e; return 1
  | .ok decls =>
    let bytecode := decls.compile
    let system := Aiur.AiurSystem.build bytecode commitmentParameters
    let funIdx := toplevel.getFuncIdx name |>.get!
    let (claim, proof, _) := system.prove friParameters funIdx #[10] default
    match system.verify friParameters claim proof with
    | .ok _ => return 0
    | .error e => IO.eprintln e; return 1


-- End-to-end proof generation and verification benchmark
def proveE2EBench := bgroup "prove E2E" [
  benchIO "fib 10" proveE2E `main
] { samplingMode := .flat }

-- Individual benchmarks of each step from `proveE2E`

def toplevelBench := bgroup "nat_fib" [
  bench "simplify toplevel" Aiur.Toplevel.checkAndSimplify toplevel
]

def compileBench : IO $ Array BenchReport := do
  match toplevel.checkAndSimplify with
  | .error e => throw (IO.userError s!"{repr e}")
  | .ok decls =>
    bgroup "nat_fib" [
      bench "compile decls" Aiur.TypedDecls.compile decls
    ]

def buildAiurSystemBench : IO $ Array BenchReport := do
  match toplevel.checkAndSimplify with
  | .error e => throw (IO.userError s!"{repr e}")
  | .ok decls =>
    let bytecode := decls.compile
    bgroup "nat_fib" [
      bench "build AiurSystem" (Aiur.AiurSystem.build bytecode) commitmentParameters
    ]

def proveBench : IO $ Array BenchReport := do
  match toplevel.checkAndSimplify with
  | .error e => throw (IO.userError s!"{repr e}")
  | .ok decls =>
    let bytecode := decls.compile
    let system := Aiur.AiurSystem.build bytecode commitmentParameters
    let funIdx := toplevel.getFuncIdx `main |>.get!
    bgroup "nat_fib" [
      bench "prove fib 10" (Aiur.AiurSystem.prove system friParameters funIdx #[10]) default,
    ]

def verifyBench : IO $ Array BenchReport := do
  match toplevel.checkAndSimplify with
  | .error e => throw (IO.userError s!"{repr e}")
  | .ok decls =>
    let bytecode := decls.compile
    let system := Aiur.AiurSystem.build bytecode commitmentParameters
    let funIdx := toplevel.getFuncIdx `main |>.get!
    let (claim, proof, _) := system.prove friParameters funIdx #[10] default
    bgroup "nat_fib" [
      bench "verify fib 10" (Aiur.AiurSystem.verify system friParameters claim) proof
    ]

def main (_args : List String) : IO Unit := do
  let _result ← proveBench
