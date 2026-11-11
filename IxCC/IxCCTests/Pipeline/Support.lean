import IxCC.Recheck
import IxCC.Cli
import IxCCTests.Rt.Machine
import IxCCTests.Rt.Native
import IxCCTests.Rt.Levels
import IxCCTests.Src.Bench

/-! Shared support for the end-to-end suite (`tests-pipeline`): the fixtures, the compiler on them
(`Recheck.ingress`, `produce`, `run`), an artifact as the backend harness's `Compiled`, and native
runs as test executables IxCC writes (`IxCCTests.Rt.Native`). -/

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

/-- Ingress on fixture files (the kernel's acceptance included). -/
def ingressFile (ixe eqs : FilePath) (roots : List String := []) :
    IO Input := do
  let bytes ← IO.FS.readBinFile ixe
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  match ingress bytes json roots with
  | .ok i => pure i
  | .error e => throw (IO.userError s!"{ixe}: {e.render}")

def benchInput (name : String) : IO Input :=
  ingressFile (benchIxe name) (benchEqs name) []

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

/-- Write `object` and its test executable calling `entry` (`IxCCTests.Rt.Native.link`). -/
def link (t : Rt.Native.Tools) (name : String) (object : ByteArray) (entry : String) : IO FilePath :=
  Rt.Native.link t name object entry

/-- The status and value a native line reports, as an exit. -/
def exitOf (l : Rt.Native.Line) : IxCCTests.Backend.Exit := ⟨l.status, l.value⟩

end IxCCTests.Pipeline
