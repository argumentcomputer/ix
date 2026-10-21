/- A copied sizeOf value is still an O11a occurrence. Its producer dependencies
must not depend on the source name, worker count, or ready-key order. -/
import Tests.Ix.Compile.Harness.Units
import Tests.Ix.Compile.ScheduleReference

open Lean

namespace Tests.Ix.Compile.O11aCopies

def copyNames : List Name :=
  (List.range 16).map fun i => `O11aCopies ++ Name.mkSimple s!"copy{i}"

def unit : IO Tests.Ix.Compile.Harness.CUnit := do
  let env ← getFileEnv "Tests/Ix/Compile/Pass/O2Split.lean"
  let some (.defnInfo value) := env.find? `PassO2.SA._sizeOf_1
    | throw <| IO.userError "missing source sizeOf value"
  let action : CoreM Unit := do
    for name in copyNames do
      addDecl (.defnDecl { value with name, all := [name] })
  let (_, state) ← action.toIO
    { fileName := "O11aCopies", fileMap := default, maxHeartbeats := 0 } { env }
  let env := state.env
  return { name := "o11a-copies", env, seeds := copyNames.toArray,
           closure := Ix.EnvScope.collectSelectedDeps env copyNames }

def causes (cenv : Ix.CompileM.CompileEnv) : Array (String × String) :=
  (cenv.p3NonCanonical.toArray.map fun (n, reason) => (n.pretty, reason)).qsort (·.1 < ·.1)

def result (label : String) (names : Array Name) (env : Ixon.Env)
    (cenv : Ix.CompileM.CompileEnv) : IO Bool := do
  let present := names.filter fun n => env.named.contains (_root_.Ix.Name.fromLeanName n)
  IO.println s!"[o11a-copies] {label}: {present.size}/{names.size} roots present, \
{cenv.ungrounded.size} failures, {cenv.p3NonCanonical.size} declines"
  for (n, why) in cenv.ungrounded.toList.take 4 do
    IO.println s!"[o11a-copies] {label}: {n.pretty}: {why}"
  (← IO.getStdout).flush
  return present.size == names.size && cenv.ungrounded.isEmpty

/-- Identical bytes/reports and every requested root under all four schedules. -/
def compareSchedules (u : Tests.Ix.Compile.Harness.CUnit) :
    IO (Ix.CompileM.LeanPipelineOut × Bool) := do
  let one ← Tests.Ix.Compile.Harness.compileUnit u (workers := 1)
  let mut ok ← result s!"{u.name} workers=1" u.seeds one.env one.cenv
  let eight ← Tests.Ix.Compile.Harness.compileUnit u (workers := 8)
  ok := (← result s!"{u.name} workers=8" u.seeds eight.env eight.cenv) && ok
  if one.bytes != eight.bytes || causes one.cenv != causes eight.cenv then
    IO.println "[o11a-copies] worker counts changed bytes or decline reports"
    ok := false
  for least in [true, false] do
    let label := s!"{u.name} {if least then "least" else "greatest"} ready key"
    let folded ← IO.lazyPure fun _ =>
      Tests.Ix.Compile.ScheduleReference.sequential one.cenv.env one.blocks
        (unmaterialized := u.closure.length) (least := least)
    match folded with
    | .error why => IO.println s!"[o11a-copies] {label}: {why}"; ok := false
    | .ok (env, _, cenv) =>
      ok := (← result label u.seeds env cenv) && ok
      let bytes ← IO.ofExcept (Ixon.serEnv env)
      if bytes != one.bytes || causes cenv != causes one.cenv then
        IO.println s!"[o11a-copies] {label}: bytes/reports differ from workers=1"
        ok := false
  return (one, ok)

def run : IO UInt32 := do
  let (_, ok) ← compareSchedules (← unit)
  IO.println s!"[o11a-copies] {if ok then "PASS" else "FAIL"}"
  return if ok then 0 else 1

end Tests.Ix.Compile.O11aCopies
