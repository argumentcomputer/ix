/- Observational companion to the L2aSyn runner.
   This performs a separate compile with the same unit constructor and compiler;
   it does not intercept, substitute, or weaken the original test invocation.
   Exit zero means the accounting stream completed, not that its rows passed.
   Acceptance requires separately checking all reported row outcomes. -/
import Tests.Ix.Compile.L2aSyn
import Lean.Data.Json

open Lean

namespace L2sLandingAccounting

def nameParts : _root_.Ix.Name → Array Json
  | .anonymous _ => #[]
  | .str p s _ => (nameParts p).push (Json.mkObj [("str", toJson s)])
  | .num p n _ => (nameParts p).push (Json.mkObj [("num", toJson n)])

def nameData (n : _root_.Ix.Name) : Json :=
  Json.mkObj [("parts", Json.arr (nameParts n)), ("pretty", toJson n.pretty)]

def rowData (r : Tests.Ix.Compile.L2aSyn.Row) : Json :=
  Json.mkObj [("name", nameData r.rec_), ("dom", toJson r.dom),
    ("closed", toJson r.closed), ("exec", toJson r.exec),
    ("core", toJson r.core), ("same", toJson r.same)]

def inventory (cenv : _root_.Ix.CompileM.CompileEnv) : Array Json := Id.run do
  let inp := _root_.Ix.Compile.Pass.viewInput cenv
  let mut blocks : Array Json := #[]
  for (key, all) in cenv.p3Blocks do
    let targets := (_root_.Ix.Compile.Pass.imageKinds inp.const? all).filter
      (fun r => match inp.const? r with | some (.recInfo _) => true | _ => false)
    let (viewOK, viewError) := match _root_.Ix.Compile.Pass.buildView inp all with
      | .ok _ => (true, "")
      | .error e => (false, toString e)
    let selected := targets.map fun n =>
      let reason := cenv.ungrounded[n]?
      Json.mkObj [("name", nameData n), ("ungrounded", toJson reason.isSome),
        ("cause", match reason with | some s => toJson s | none => Json.null),
        ("retained", toJson (viewOK && reason.isNone))]
    blocks := blocks.push (Json.mkObj [("key", nameData key),
      ("members", Json.arr (all.map nameData)), ("view_ok", toJson viewOK),
      ("view_error", toJson viewError), ("targets", Json.arr selected)])
  return blocks

def emit (j : Json) : IO Unit := do
  IO.println ("[l2a-accounting] " ++ j.compress)
  (← IO.getStdout).flush

def run : IO UInt32 := do
  if (← IO.getEnv "L2A_SYN_ONLY").isSome then
    IO.eprintln "L2A_SYN_ONLY must be absent, including the empty-string case"
    return 2
  let files := Tests.Ix.Compile.Pass3.auxCertFiles ++ Tests.Ix.Compile.Pass3.protoFiles ++
    Tests.Ix.Compile.Pass3.passFiles ++ Tests.Ix.Compile.Pass3.pjPassFiles
  let selected := files.filter fun p =>
    !Tests.Ix.Compile.Pass3.leanRejects.contains ((System.FilePath.mk p).fileStem.getD p)
  if selected.length != 61 then
    IO.eprintln s!"selected-unit count changed: {selected.length}"
    return 2
  emit <| Json.mkObj [("kind", toJson ("begin" : String)),
    ("paths", toJson selected), ("filter_absent", toJson true),
    ("skip_stems", toJson Tests.Ix.Compile.Pass3.leanRejects)]
  let mut completed := 0
  for p in selected do
    let stem := (System.FilePath.mk p).fileStem.getD p
    let mut phase := "unitOfFile"
    let result ← try
      let u ← Tests.Ix.Compile.Pass3.unitOfFile p
      phase := "compileUnit"
      let on ← Tests.Ix.Compile.Pass3.compileUnit u
      phase := "runCompiled and accounting"
      let r := Tests.Ix.Compile.L2aSyn.runCompiled on.cenv
      let ungrounded := on.cenv.ungrounded.toArray.map fun (n, cause) =>
        Json.mkObj [("name", nameData n), ("cause", toJson cause)]
      pure <| Json.mkObj [("kind", toJson ("unit" : String)), ("path", toJson p),
        ("stem", toJson stem), ("status", toJson ("compiled" : String)),
        ("seeds", Json.arr (u.seeds.map (nameData ∘ _root_.Ix.Name.fromLeanName))),
        ("closure_names", Json.arr (u.closure.toArray.map
          (fun pair => nameData (_root_.Ix.Name.fromLeanName pair.1)))),
        ("artifact_bytes", toJson on.bytes.size), ("ungrounded", Json.arr ungrounded),
        ("blocks", Json.arr (inventory on.cenv)),
        ("rows", Json.arr (r.rows.map rowData)), ("problems", toJson r.problems)]
    catch e =>
      pure <| Json.mkObj [("kind", toJson ("unit" : String)), ("path", toJson p),
        ("stem", toJson stem), ("status", toJson ("refused" : String)),
        ("phase", toJson phase), ("message", toJson (toString e))]
    emit result
    completed := completed + 1
  emit <| Json.mkObj [("kind", toJson ("end" : String)),
    ("selected", toJson selected.length), ("accounted", toJson completed),
    ("scope", toJson ("separate same-source compile; original test remains unchanged" : String))]
  return 0

end L2sLandingAccounting

def main : IO UInt32 := L2sLandingAccounting.run
