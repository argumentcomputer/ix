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

/-- `Recheck.ingress`'s steps with `extra` proposals beside the sidecar's, there
before the walk (`Src.Ingress.reach`), so that their theorems are proof seeds
as a sidecar's proposals' are: a table entry may name only a theorem read with
its proof. (A proposal added to an `Input` after ingress names a theorem read
by its statement, or not read, and its entry is refused.) Used for proposals the
`ixcc/k1-equations/1` sidecar cannot carry (`csimp`) or that a test adds. -/
def ingressWith (bytes : ByteArray) (equations : Lean.Json) (extra : Array Src.Proposal)
    (roots : List String := []) : Except Err Input := do
  let env ← (IxCC.Ixon.V3.decodeAnonymousEnv bytes).mapError fun m =>
    { stage := .ingress, code := "decode", message := m }
  let sidecar ← (Src.Hints.ofK1Json equations).mapError fun m =>
    { stage := .ingress, code := "hints", message := m }
  let sidecar := { sidecar with proposals := sidecar.proposals ++ extra }
  let chosen ← selectRoots sidecar.roots roots
  let hints := { sidecar with roots := chosen }
  let acc ← (Src.KernelFront.accept env).mapError fun r =>
    { stage := .ingress, code := "kernel", message := r.report }
  let records ← (Src.Ingress.reach env (Src.Ingress.Seeds.of sidecar
      (Src.KernelFront.pinsOfTable acc.table))).mapError fun m =>
    { stage := .ingress, code := "decode", message := m }
  let p ← (Src.Ingress.readConsts env records (chosen.map (·.1))).mapError fun m =>
    { stage := .ingress, code := "ingress", message := m }
  let p := { p with known := { pins := Src.KernelFront.pinsOfTable acc.table } }
  let p := { p with known := Src.Pinned.known p, resource := hints.resource }
  (Src.Resource.validate p).mapError fun m => { stage := .ingress, code := "resource-binding", message := m }
  let rd ← (Src.KernelFront.Reading.build acc p).mapError fun m =>
    { stage := .ingress, code := "faithful", message := m }
  let names := chosen.toList.zipIdx.map fun ((_, n), i) => n.getD s!"root{i}"
  pure { env, hints, program := p, names, kernel := { acc, rd, fe := Ix.Kernel.mkFEnv acc.env } }

/-- `ingressWith` on fixture files. -/
def ingressFileWith (ixe eqs : FilePath) (extra : Array Src.Proposal) (roots : List String := []) :
    IO Input := do
  let bytes ← IO.FS.readBinFile ixe
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  match ingressWith bytes json extra roots with
  | .ok i => pure i
  | .error e => throw (IO.userError s!"{ixe}: {e.render}")

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
