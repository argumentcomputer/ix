import CompilatrixTests.Pipeline.Support
import CompilatrixTests.Fir.Support
import Compilatrix.Xv.Semantics
import Compilatrix.Xv.XlSemantics

/-! Every level agrees (M1.I2): each K1 program, as the compiler compiled it
(`Recheck.compileInput`: one artifact holds every level `run` made), on its
test input, at

* **SrcEval** on the checked program, **Lam**, **Anf after every pass**
  (P1, then each step of the certificate's middle end replayed: the
  programs `Anf.Pipeline.run` goes through), **Fir**, **Own** (immortal) and
  **Cfg**, read back by each level's own readback;
* **Lir**, **Xv** and **Xl** from the memory `cx_init` left, and the typed
  x86 machine (`X86.step` from the root's exported wrapper) and **ByteEval**
  on the object's own `.text`, each from `cx_init` on its machine, read
  back by `Rt.readback` at the root's type;
* natively (with `--cc`), the object linked with the runtime driver, read
  back by the driver's C decoder.

Every level must give `ok` and the observation `expected.txt` names. The
big-step evaluators (SrcEval, Lam, Anf, Fir, Own) nest native frames per
iteration of `sum-loop`'s loop, so its runs there go to a child process with
a large Lean stack. The typed x86 machine and ByteEval step one instruction
at a time (about 40 µs per typed step: `fib 25` would take over ten
minutes), so by default they run at reduced sizes (`Run.reduced`: fib 13,
sum-loop 5000, ackermann 3 3, tak 12 12 8 4; gcd at its test size), where
their readback must equal Cfg's on the same input; `--full` runs them at the
test size too. -/

namespace CompilatrixTests.Pipeline.Levels

open Compilatrix Compilatrix.Recheck CompilatrixTests.Src
open Compilatrix.Sem (Obs Result)
open System

/-- A K1 program as the compiler made it. -/
structure Compiled where
  name : String
  cert : Cert
  art : Artifact
  /-- P1 and the program after each certificate step. -/
  anf : List (String × Anf.Program)

/-- The middle end replayed step by step from the certificate (what
`Anf.Pipeline.run` computes, with every intermediate program). -/
def anfStages (c : Cert) (lam : Lam.Program) : Except String (List (String × Anf.Program)) := do
  let p1 ← Anf.convert lam
  let (_, stages) ← c.mid.steps.foldlM (init := (p1, [("P1", p1)])) fun (P, acc) s => do
    let P ← s.run c.mid.shrink P
    pure (P, acc ++ [(s.name, P)])
  pure stages

def compileBench (name : String) : IO Compiled := do
  let inp ← benchInput name
  let (cert, art) ← compileIn name inp
  let anf ← IO.ofExcept (anfStages cert art.lam)
  -- the replay ends where `run` ended
  let some (_, last) := anf.getLast? | throw (IO.userError s!"{name}: no Anf stage")
  unless last.beq art.anf do throw (IO.userError s!"{name}: the replayed middle end differs from run's")
  pure { name, cert, art, anf }

/-- The levels, in pipeline order. -/
def levelNames (c : Compiled) : List String :=
  ["src", "lam"] ++ (c.anf.zipIdx.map fun ((s, _), i) => s!"anf{i}.{s}") ++
    ["fir", "own", "cfg", "lir", "xv", "xl", "x86", "bytes"]

/-- Levels whose evaluator nests native frames per recursive call. -/
def bigStep (level : String) : Bool :=
  ["src", "lam", "fir", "own"].contains level || level.startsWith "anf"

def shape {α : Type} : Result α → String
  | .ok _ => "ok"
  | .timeout => "timeout"
  | .stuck => "stuck"
  | .trap => "trap"
  | .resource r => s!"resource {repr r}"

def lirShape : Lir.Outcome → String
  | .ok _ => "ok"
  | .timeout => "timeout"
  | .stuck => "stuck"
  | .trap => "trap"
  | .resource r => s!"resource {repr r}"

def clock : Nat := 1 <<< 40

/-- One level on the root (position 0) and `args`: its outcome and readback. -/
def runLevel (c : Compiled) (level : String) (args : List Nat) : IO (String × Option Obs) := do
  let a := c.art
  let some root := a.roots.head? | throw (IO.userError s!"{c.name}: no root")
  match level with
  | "src" =>
    let r ← CompilatrixTests.Lam.runSrc a.src clock root.const args
    pure (shape r, match r with
      | .ok v => Src.readback a.src a.checked.keeps v
      | _ => none)
  | "lam" =>
    let some g := a.lam.roots.head? | throw (IO.userError "no Lam root")
    let r ← CompilatrixTests.Lam.runLam a.lam clock g args
    pure (shape r, match r with
      | .ok v => Lam.readback a.lam v
      | _ => none)
  | "fir" =>
    let some f := a.fir.exports.head? | throw (IO.userError "no Fir root")
    let r ← CompilatrixTests.Fir.runFir a.fir clock f args
    pure (shape r, match r with
      | .ok v => Fir.readback v
      | _ => none)
  | "own" =>
    let some f := a.own.exports.head? | throw (IO.userError "no Own root")
    let r ← CompilatrixTests.Fir.runOwn .immortal a.own clock f args
    pure (shape r, match r with
      | .ok (v, H) => H.readback v
      | _ => none)
  | "cfg" =>
    let some f := a.cfg.exports.head? | throw (IO.userError "no Cfg root")
    let r ← CompilatrixTests.Fir.runCfg .immortal a.cfg clock f args
    pure (shape r, match r with
      | .ok (v, H) => H.readback v
      | _ => none)
  | "lir" | "xv" | "xl" =>
    let mem ← IO.ofExcept (CompilatrixTests.Rt.initRegion a.lowered)
    let words := args.map CompilatrixTests.Rt.tag
    let r ← IO.lazyPure fun _ => match level with
      | "lir" => Lir.eval { a.lowered.program with main := root.fn } clock words mem CompilatrixTests.Rt.ctx
      | "xv" => Xv.eval { a.xv with main := root.fn } clock words mem CompilatrixTests.Rt.ctx
      | _ => Xv.Xl.eval { a.xl with main := root.fn } {} clock words mem CompilatrixTests.Rt.ctx
    pure (lirShape r, match r with
      | .ok ([w], m) => readWord root m w
      | _ => none)
  | "x86" | "bytes" =>
    let cc := compiledOf a
    let ms ← IO.ofExcept (CompilatrixTests.Rt.Machine.initMachines cc)
    let words := args.map UInt64.ofNat
    let (e, s, _) ← IO.ofExcept <| ← IO.lazyPure fun _ =>
      if level == "x86" then CompilatrixTests.Rt.Machine.runExportTyped cc root.symbol words ms.typed (1 <<< 34)
      else CompilatrixTests.Rt.Machine.runExportBytes cc root.symbol words ms.bytes (1 <<< 34)
    pure (if e.status == 0 then "ok" else s!"status {e.status}",
      if e.status == 0 then readWord root s.memory e.value else none)
  | _ =>
    match level.splitOn "." with
    | anfI :: _ =>
      let some i := (anfI.drop 3).toNat? | throw (IO.userError s!"unknown level {level}")
      let some (_, A) := c.anf[i]? | throw (IO.userError s!"no Anf stage {i}")
      let some g := A.roots.head? | throw (IO.userError "no Anf root")
      let r ← CompilatrixTests.Anf.runAnf A clock g args
      pure (shape r, match r with
        | .ok v => Anf.readback A v
        | _ => none)
    | [] => throw (IO.userError s!"unknown level {level}")

/-- The child process's stack for big-step levels (as `tests-src`). -/
def deepStackKb : Nat := CompilatrixTests.Src.Bench.deepStackKb

/-- Child-process mode: one level of one bench entry on the given
arguments; prints the outcome and the rendered observation. -/
def childMain (name level : String) (args : List Nat) : IO Unit := do
  let c ← compileBench name
  let (o, obs) ← runLevel c level args
  IO.println s!"{o}\t{(obs.map Rt.renderObs).getD "-"}"

/-- One level, in a child process with a large stack when `deep`. -/
def levelRun (self : FilePath) (c : Compiled) (level : String) (args : List Nat) (deep : Bool) :
    IO (String × String) := do
  if deep then
    let env := #[("LEAN_STACK_SIZE_KB", some (toString deepStackKb))]
    let o ← IO.Process.output
      { cmd := self.toString, args := #["--level", c.name, level] ++ (args.map toString).toArray, env := env }
    unless o.exitCode == 0 do
      throw (IO.userError s!"{c.name} {level} child exited {o.exitCode}: {o.stderr}")
    match (o.stdout.trimAscii.toString.splitOn "\t") with
    | [out, obs] => pure (out, obs)
    | _ => throw (IO.userError s!"{c.name} {level} child printed {o.stdout}")
  else
    let (o, obs) ← runLevel c level args
    pure (o, (obs.map Rt.renderObs).getD "-")

/-- Every level of every K1 program on its test input. `reduced`: the
arguments to use instead of the test size at a level (the CI budget). -/
def run (a : Assert) (self : FilePath) (native : Option Rt.Native.Tools)
    (reduced : String → String → Option (List Nat)) (names : List String := benchNames) (progress : Bool := false) :
    IO (Array String) := do
  let mut out := #[]
  for name in names do
    let c ← compileBench name
    let (testArgs, want) ← CompilatrixTests.Src.Bench.testCase name
    let mut times : Array String := #[]
    for level in levelNames c do
      let args := (reduced name level).getD testArgs
      let expectObs := if args == testArgs then toString want else "?"
      let deep := name == "sum-loop" && bigStep level && args == testArgs
      let ((o, obs), ms) ← timed (levelRun self c level args deep)
      expect a (o == "ok") s!"{name} {args} at {level}: {o}"
      if args == testArgs then
        expect a (obs == expectObs) s!"{name} {args} at {level}: reads back {obs}, expected {want}"
      else
        -- a reduced size: the level must agree with Cfg (small-step, fast) on it
        let (_, ref) ← levelRun self c "cfg" args false
        expect a (obs == ref) s!"{name} {args} at {level}: reads back {obs}, Cfg {ref}"
      times := times.push s!"{level} {ms}{if args == testArgs then "" else s!" (at {args})"}"
      if progress then IO.eprintln s!"      [{name}] {level} {args}: {ms} ms"
    if let some nt := native then
      let some root := c.art.roots.head? | throw (IO.userError s!"{name}: no root")
      let exe ← link nt s!"levels_{name}" c.art.object root.symbol
      let ((lines, _), ms) ← timed do
        pure (← Rt.Native.run exe { stack := 1 <<< 28, ty := root.ty } [testArgs], ())
      for l in lines do
        expect a (l.status == 0 && l.ok) s!"{name} {testArgs} natively: status {l.status}"
        expect a (l.obs == some (toString want)) s!"{name} {testArgs} natively: {l.obs}"
      times := times.push s!"native {ms}"
    out := out.push s!"{name} {testArgs} = {want}, {(levelNames c).length + (if native.isSome then 1 else 0)} levels agree (ms):"
    out := out.push s!"  {", ".intercalate times.toList}"
  return out

end CompilatrixTests.Pipeline.Levels
