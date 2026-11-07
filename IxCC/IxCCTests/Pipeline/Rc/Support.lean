import IxCC.Recheck.Rc.Produce
import IxCCTests.Recheck.Rc.Fixtures
import IxCCTests.Rt.Machine
import IxCCTests.Rt.Native
import IxCC.Cfg.Rc.Run

set_option autoImplicit false
namespace IxCCTests.Pipeline.Rc
open IxCC

def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError label)

def clock : Nat := 10000
def regionSize : Nat := 16384
def cases : List (Nat × Nat) := [(0, 7), (1, 42), (3, 5)]

/-- Independent complete structural oracle; no evaluated IR supplies it. -/
def listObs (xs : List Nat) : Sem.Obs :=
  xs.foldr (fun n tail => .ctor 1 [.nat n, tail]) (.ctor 0 [])

def expected (name : String) (n seed : Nat) : Sem.Obs :=
  if name == "sharedReverse" then
    .ctor 0 [listObs ((List.range n).map fun i => seed + (n - 1 - i)),
      listObs ((List.range n).map (seed + ·))]
  else if name == "reverseRepeated" then listObs (List.replicate n seed)
  else listObs ((List.range n).map (seed + ·))

structure Compiled where
  name : String
  cert : Recheck.RcReplay.Cert
  artifact : Recheck.RcReplay.Artifact
  machine : IxCCTests.Rt.Machine.Compiled
  anf : List (String × Anf.Program)

def compile (name : String) : IO Compiled := do
  let input ← IxCCTests.Recheck.Rc.Fixtures.source name
  let cfg : Recheck.Config := { names := [name] }
  let (written, produced) ← IO.ofExcept ((Recheck.RcReplay.produce cfg input).mapError (·.message))
  let cert ← IO.ofExcept (Recheck.RcReplay.Cert.ofText written.toText)
  let artifact ← IO.ofExcept ((Recheck.RcReplay.run cfg input.program cert).mapError (·.message))
  check (name ++ ": serialized replay ELF differs") (produced.backend.object == artifact.backend.object)
  let f := artifact.front
  let p1 ← IO.ofExcept (Anf.convert f.lam)
  let (last, anf) ← IO.ofExcept (cert.base.mid.steps.foldlM
    (init := (p1, [("P1", p1)])) fun (P, stages) step => do
      let next ← step.run cert.base.mid.shrink P
      pure (next, stages ++ [(step.name, next)]))
  check (name ++ ": certificate Anf replay endpoint differs") (last.beq f.anf)
  let root := (f.src.roots.head?.map (·.1)).getD default
  let cfg := { cfg with provenance := some (cfg.provenance.getD (.ixir1Policy root 3 1)) }
  let (xv, xl, _, program, exports) ← IO.ofExcept
    ((Recheck.RcReplay.backTyped cfg f root cert.base).mapError (·.message))
  check (name ++ ": backend replay exports differ") (exports == artifact.backend.exports)
  -- The same backTyped receipt determines both models; no allocation rerun.
  let _ := program
  return {
    name, cert, artifact, anf
    machine := { lir := f.lowered, xv, xl, artifact := artifact.backend } }

def save (logs : System.FilePath) (c : Compiled) : IO Unit := do
  IO.FS.createDirAll logs
  IO.FS.writeFile (logs / s!"{c.name}.rc.json") (c.cert.toText ++ "\n")
  IO.FS.writeBinFile (logs / s!"{c.name}.o") c.artifact.backend.object

def observation {α : Type} (label : String) (read : α → Option Sem.Obs)
    (result : Sem.Result α) : IO Sem.Obs := do
  match result with
  | .ok value =>
    let some obs := read value | throw (IO.userError (label ++ ": complete readback failed"))
    return obs
  | .timeout => throw (IO.userError (label ++ ": timeout"))
  | .stuck => throw (IO.userError (label ++ ": stuck"))
  | .trap => throw (IO.userError (label ++ ": trap"))
  | .resource r => throw (IO.userError s!"{label}: resource {repr r}")

/-- Same independent native parser/decoder as the existing test support,
with an explicit child-process cap and retained inputs/output/exit evidence. -/
def runNative (logs : System.FilePath) (label : String) (exe : System.FilePath)
    (options : IxCCTests.Rt.Native.Options) (inputs : List (List Nat)) :
    IO (List IxCCTests.Rt.Native.Line) := do
  IO.FS.createDirAll logs
  let args := #["--kill-after=5", "30", exe.toString,
      "--region", toString options.region, "--stack", toString options.stack] ++
    (match options.ty with
      | some (sig, ty) => #["--type", ty.encode, "--sig", sig.encode]
      | none => #[]) ++
    (if options.dump then #["--dump"] else #[]) ++
    (if options.time then #["--time"] else #[])
  let start ← IO.monoMsNow
  let child ← IO.Process.spawn {
    cmd := "timeout"
    args
    stdin := .piped
    stdout := .piped
    stderr := .piped }
  let inputText := String.join (inputs.map fun xs => String.intercalate " " (xs.map toString) ++ "\n")
  let (stdin, child) ← child.takeStdin
  stdin.putStr inputText
  stdin.flush
  let stdout ← child.stdout.readToEnd
  let stderr ← child.stderr.readToEnd
  let code ← child.wait
  IO.FS.writeFile (logs / (label ++ ".stdin")) inputText
  IO.FS.writeFile (logs / (label ++ ".stdout")) stdout
  IO.FS.writeFile (logs / (label ++ ".stderr")) stderr
  IO.FS.writeFile (logs / (label ++ ".json")) ((Lean.Json.mkObj [
    ("command", Lean.toJson ("timeout" : String)), ("args", Lean.toJson args),
    ("timeout_seconds", Lean.toJson (30 : Nat)), ("exit", Lean.toJson code.toNat),
    ("elapsed_ms", Lean.toJson ((← IO.monoMsNow) - start))]).pretty ++ "\n")
  check (label ++ ": native timeout/signal/nonzero exit") (code == 0)
  let some rows := IxCCTests.Rt.Native.parse stdout options.ty.isSome options.time
    | throw (IO.userError (label ++ ": malformed native output"))
  check (label ++ ": native output row count") (rows.length == inputs.length)
  return rows

end IxCCTests.Pipeline.Rc
