import IxCC.Recheck
import IxCC.Cli
import IxCCTests.Rt.Machine
import IxCCTests.Rt.Native
import IxCCTests.Rt.Levels
import IxCCTests.Src.Bench

/-! Shared support for the end-to-end suite (`tests-pipeline`): the fixtures, the compiler on them
(`Recheck.ingress`, `produce`, `run`), an artifact as the backend harness's `Compiled`, and native
linking with the runtime driver compiled once per entry symbol. -/

namespace IxCCTests.Pipeline

open IxCC IxCC.Recheck IxCCTests.Src
open System

def benchIxe (name : String) : FilePath := fixtures / "bench-k1" / s!"{name}.ixe"
def benchEqs (name : String) : FilePath := fixtures / "bench-k1" / s!"{name}.equations.json"
def k1Ixe : FilePath := fixtures / "k1/k1.ixe"
def k1Eqs : FilePath := fixtures / "k1/equations.json"

/-- The `k1.ixe` roots and the benchmark each one is. -/
def k1Roots : List (String × String) :=
  [("K1.fib", "fib"), ("K1.sumLoop", "sum-loop"), ("K1.ack", "ackermann"), ("K1.tak", "tak"),
   ("K1.gcd", "gcd")]

/-- Ingress on fixture files (erased typing off unless asked: `tests-ixon-v3`
gates it for every K1 closure). -/
def ingressFile (ixe eqs : FilePath) (roots : List String := []) (typecheck : Bool := false) :
    IO Input := do
  let bytes ← IO.FS.readBinFile ixe
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  match ingress bytes json roots typecheck with
  | .ok i => pure i
  | .error e => throw (IO.userError s!"{ixe}: {e.render}")

def benchInput (name : String) (typecheck : Bool := false) : IO Input :=
  ingressFile (benchIxe name) (benchEqs name) [] typecheck

/-- An `Except Err` as `IO`, evaluated when the action runs. -/
def ofErr {α : Type} (label : String) (x : Unit → Except Err α) : IO α := do
  match ← IO.lazyPure x with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{label}: {e.render}")

/-- `produce` and `run` on an input, with the input's names unless `cfg`
gives some. -/
def compileIn (label : String) (inp : Input) (cfg : Config := {}) : IO (Cert × Artifact) :=
  ofErr label fun _ => compileInput cfg inp

/-- An artifact as the backend harness's compiled program. -/
def compiledOf (a : Artifact) : Rt.Machine.Compiled :=
  { lir := a.lowered, xv := a.xv, xl := a.xl, artifact := a.backend }

/-- The root's result read back from a Lir-level word and memory (Phase 1:
`Nat` and `Bool` results). -/
def readWord (r : Root) (m : X86.Memory) (w : Lir.Word) : Option Sem.Obs := do
  let (sig, ty) ← r.ty
  Rt.readback sig ((Rt.limitOf Rt.defaultSize - Rt.base).toNat / 8) m ty w

/-! ## Native runs -/

/-- Link `object` with the runtime driver built for `entry` (compiled once
into the work directory), with the same flags as `IxCCTests.Rt.Native.link`. -/
def link (t : Rt.Native.Tools) (name : String) (object : ByteArray) (entry : String) : IO FilePath := do
  let driver := t.work / s!"driver_{entry}.o"
  unless ← driver.pathExists do
    let out ← IO.Process.output {
      cmd := t.cc
      args := #["-std=c11", "-O1", "-Wall", "-Wextra", "-Werror", "-c", s!"-DENTRY={entry}",
        t.driver.toString, "-o", driver.toString] }
    unless out.exitCode == 0 do throw (IO.userError s!"compiling the driver for {entry}:\n{out.stderr}")
  let obj := t.work / s!"{name}.o"
  IO.FS.writeBinFile obj object
  let exe := t.work / name
  let out ← IO.Process.output {
    cmd := t.cc
    args := #["-no-pie", "-Wl,--fatal-warnings", driver.toString, obj.toString, "-o", exe.toString] }
  unless out.exitCode == 0 do throw (IO.userError s!"linking {name} failed:\n{out.stdout}{out.stderr}")
  pure exe

/-- The status and value a driver line reports, as an exit. -/
def exitOf (l : Rt.Native.Line) : IxCCTests.Backend.Exit := ⟨l.status, l.value⟩

end IxCCTests.Pipeline
