import CompilatrixTests.Pipeline.Rc.Support
import CompilatrixTests.Rt.Native

set_option autoImplicit false
namespace CompilatrixTests.Pipeline.Rc.Levels
open Compilatrix

def one (c : Compiled) (n seed : Nat) : IO (List (String × Sem.Obs)) := do
  let f := c.artifact.front
  let some root := c.artifact.roots.head? | throw (IO.userError "no RC root")
  let some lamRoot := f.lam.roots.head? | throw (IO.userError "no Lam root")
  let some firRoot := f.fir.exports.head? | throw (IO.userError "no Fir root")
  let some cfgRoot := f.cfg.base.exports.head? | throw (IO.userError "no Cfg root")
  let some (sig, ty) := root.ty | throw (IO.userError "no complete result signature")
  let args := [n, seed]
  let fargs := args.map fun x => Fir.Val.lit (.nat x)
  let rargs := args.map fun x => Own.RVal.lit (.nat x)
  let wordRead := fun (m : X86.Memory) w => Rt.readback sig (regionSize / 8) m ty w
  let want := expected c.name n seed
  let mut rows : List (String × Sem.Obs) := []
  let src ← observation "Src" (Src.readback f.src f.checked.keeps)
    (← IO.lazyPure fun _ => Src.run f.src clock root.const (args.map .lit))
  rows := rows ++ [("src", src)]
  let lam ← observation "Lam" (Lam.readback f.lam)
    (← IO.lazyPure fun _ => Lam.run f.lam clock lamRoot (args.map fun x => .lit (.nat x)))
  rows := rows ++ [("lam", lam)]
  for ((label, P), i) in c.anf.zipIdx do
    let some entry := P.roots.head? | throw (IO.userError "no Anf root")
    let value ← observation "Anf" (Anf.readback P)
      (← IO.lazyPure fun _ => Anf.run P clock entry (args.map fun x => .lit (.nat x)))
    rows := rows ++ [(s!"anf{i}.{label}", value)]
  let fir ← observation "Fir" Fir.readback
    (← IO.lazyPure fun _ => Fir.run f.fir clock firRoot fargs)
  rows := rows ++ [("fir", fir)]
  let own ← observation "Own.Plain" (fun (v, H) => H.readback v)
    (← IO.lazyPure fun _ => Own.Plain.run f.own clock firRoot rargs)
  rows := rows ++ [("own.plain", own)]
  let cfg ← observation "Cfg.Rc" (fun (v, H) => H.readback v)
    (← IO.lazyPure fun _ => Cfg.Rc.run f.cfg clock cfgRoot rargs)
  rows := rows ++ [("cfg.rc", cfg)]
  let memory ← IO.ofExcept (CompilatrixTests.Rt.initRegion f.lowered regionSize)
  let words := args.map CompilatrixTests.Rt.tag
  for (label, evaluate) in [
      ("lir", fun (_ : Unit) => Lir.eval { f.lowered.program with main := root.fn } clock words memory CompilatrixTests.Rt.ctx),
      ("xv", fun (_ : Unit) => Xv.eval { c.machine.xv with main := root.fn } clock words memory CompilatrixTests.Rt.ctx),
      ("xl", fun (_ : Unit) => Xv.Xl.eval { c.machine.xl with main := root.fn } {} clock words memory CompilatrixTests.Rt.ctx)] do
    let result ← IO.lazyPure evaluate
    let value ← match result with
      | .ok ([word], mem) =>
        let some obs := wordRead mem word | throw (IO.userError (label ++ ": readback failed"))
        pure obs
      | _ => throw (IO.userError (label ++ ": " ++ CompilatrixTests.Rt.lirOutcome result))
    rows := rows ++ [(label, value)]
  let machines ← IO.ofExcept (CompilatrixTests.Rt.Machine.initMachines c.machine regionSize)
  let (typed, typedState, _) ← IO.ofExcept (← IO.lazyPure fun _ =>
    CompilatrixTests.Rt.Machine.runExportTyped c.machine root.symbol
      (args.map UInt64.ofNat) machines.typed 5000000)
  let (bytes, bytesState, _) ← IO.ofExcept (← IO.lazyPure fun _ =>
    CompilatrixTests.Rt.Machine.runExportBytes c.machine root.symbol
      (args.map UInt64.ofNat) machines.bytes 5000000)
  for (label, exit, state) in [("x86", typed, typedState), ("bytes", bytes, bytesState)] do
    check (label ++ ": nonzero status") (exit.status == 0)
    let some value := wordRead state.memory exit.value | throw (IO.userError (label ++ ": readback failed"))
    rows := rows ++ [(label, value)]
  for (label, value) in rows do
    check s!"{c.name} {n} {seed} {label}: {Rt.renderObs value}, expected {Rt.renderObs want}"
      (value == want)
  return rows

def run (logs : System.FilePath) : IO Unit := do
  CompilatrixTests.Recheck.Rc.Fixtures.verify
  let mut report : List String := []
  for name in CompilatrixTests.Recheck.Rc.Fixtures.roots do
    let c ← compile name
    save logs c
    for (n, seed) in cases do
      let rows ← one c n seed
      for (label, value) in rows do
        report := report ++ [s!"{name}\t{n}\t{seed}\t{label}\t{Rt.renderObs value}"]
      IO.println s!"PASS {name} {n} {seed}: {rows.length} actual RC pipeline levels, complete value"
  IO.FS.writeFile (logs / "levels.tsv") (String.intercalate "\n" report ++ "\n")

def native (logs : System.FilePath) : IO Unit := do
  CompilatrixTests.Recheck.Rc.Fixtures.verify
  IO.FS.createDirAll logs
  let mut report : List String := []
  for name in CompilatrixTests.Recheck.Rc.Fixtures.roots do
    let c ← compile name
    save logs c
    let some root := c.artifact.roots.head? | throw (IO.userError "no root")
    let some (sig, ty) := root.ty | throw (IO.userError "no root type")
    let exe ← CompilatrixTests.Rt.Native.link { work := logs } s!"levels-{name}" c.artifact.backend.object root.symbol
    let rows ← runNative logs ("native-" ++ name) exe
      { region := regionSize, stack := 1048576, ty := root.ty, dump := true }
      (cases.map fun (n, seed) => [n, seed])
    check "native row count" (rows.length == cases.length)
    for ((n, seed), row) in cases.zip rows do
      let want := expected name n seed
      check s!"{name} {n} {seed}: independent C/Lean full native observation"
        (row.status == 0 && row.ok && !row.init && row.obs == some (Rt.renderObs want) &&
          row.readback regionSize sig ty == some want)
      report := report ++ [s!"{name}\t{n}\t{seed}\tnative\t{Rt.renderObs want}"]
      IO.println s!"PASS native {name} {n} {seed}: complete C+Lean value"
  IO.FS.writeFile (logs / "native-levels.tsv") (String.intercalate "\n" report ++ "\n")

end CompilatrixTests.Pipeline.Rc.Levels
