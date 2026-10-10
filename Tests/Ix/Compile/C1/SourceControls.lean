/- Native source and serialized-output controls for C1.
   Every process compiles the same full ordinary-source closure with both
   default compilers. Failures are retained and never converted to a subset. -/
import Tests.Ix.Compile.L2aSyn
import Lean.Data.Json

open Lean

namespace EarlyC1SourceControls

abbrev IXName := _root_.Ix.Name
abbrev Out := _root_.Ix.CompileM.LeanPipelineOut
open Tests.Ix.Compile.Pass3 (CUnit unitOfFile ixN toLeanName)

private def emit (j : Json) : IO Unit := do
  IO.println ("[c1-source] " ++ j.compress)
  (← IO.getStdout).flush

private def need (p : Bool) (why : String) : IO Unit :=
  unless p do throw (IO.userError why)

private def parts : IXName → Array Json
  | .anonymous _ => #[]
  | .str p s _ => (parts p).push (Json.mkObj [("str", toJson s)])
  | .num p n _ => (parts p).push (Json.mkObj [("num", toJson n)])

private def nameData (n : IXName) : Json :=
  Json.mkObj [("parts", Json.arr (parts n)), ("pretty", toJson n.pretty)]

private def writeNew (path : System.FilePath) (data : ByteArray) : IO Unit := do
  need (!(← path.pathExists)) s!"would overwrite {path}"
  IO.FS.writeBinFile path data

private def sourceRec (u : CUnit) (s : String) : IO Lean.RecursorVal := do
  let n := Tests.Ix.Compile.Pass3.parseName s
  let some (.recInfo rv) := u.env.find? n
    | throw (IO.userError s!"source recursor absent: {s}")
  return rv

private def wireRec (env : Ixon.Env) (s : String) : IO Ixon.Recursor := do
  let n := ixN (Tests.Ix.Compile.Pass3.parseName s)
  let some address := env.getAddr? n | throw (IO.userError s!"serialized recursor absent: {s}")
  let some c := env.getConst? address | throw (IO.userError s!"serialized body absent: {s}")
  match c.info with
  | .recr r => return r
  | .rPrj p =>
    let some b := env.getConst? p.block | throw (IO.userError s!"recursor owner absent: {s}")
    let .muts members := b.info | throw (IO.userError s!"recursor owner is not mutual: {s}")
    let some (.recr r) := members[p.idx.toNat]?
      | throw (IO.userError s!"recursor slot absent/wrong kind: {s}")
    return r
  | _ => throw (IO.userError s!"expected serialized recursor: {s}")

private def flags (u : CUnit) (on : Out) : IO Unit := do
  for (name, levels, wantK) in [
      ("KernelSpecC1.P._ix.rec", 0, false),
      ("KernelSpecC1.W._ix.rec", 0, false),
      ("KernelSpecC1.EmptyP.rec", 1, false),
      ("KernelSpecC1.K.rec", 1, true),
      ("KernelSpecC1.Drec.rec", 1, false),
      ("KernelSpecC1.T._ix.rec", 1, false)] do
    let r ← wireRec on.env name
    emit <| Json.mkObj [("kind", toJson ("wire-flags" : String)),
      ("name", toJson name), ("levels", toJson r.lvls.toNat),
      ("k", toJson r.k), ("recursor", toJson (reprStr r))]
    need (r.lvls.toNat == levels && r.k == wantK) s!"serialized recursor flags differ: {name}"
  -- C1 removes the canonical eliminator's extra universe even though the
  -- source may expose a different recursor. Do not use source flags as an
  -- oracle for canonical flags. Check the actual generated recursor table.
  for s in ["KernelSpecC1.P", "KernelSpecC1.W"] do
    let member := Tests.Ix.Compile.Pass3.parseName s
    let recs := on.cenv.p3CanonRecs.toArray.filter fun (_, rv) =>
      rv.all.any fun n => toLeanName n == member
    need (!recs.isEmpty) s!"no canonical recursor for repaired member {s}"
    for (n, rv) in recs do
      emit <| Json.mkObj [("kind", toJson ("canonical-flags" : String)),
        ("member", toJson s), ("name", nameData n),
        ("level_params", Json.arr (rv.cnst.levelParams.map nameData)),
        ("k", toJson rv.k), ("recursor", toJson (reprStr rv))]
      need (rv.cnst.levelParams.isEmpty && !rv.k)
        s!"C1 canonical recursor must be small/non-K: {n.pretty}"
  for (s, wantK) in [("EmptyP", false), ("K", true), ("Drec", false)] do
    let rv ← sourceRec u s!"KernelSpecC1.{s}.rec"
    need (rv.levelParams.length == 1 && rv.k == wantK)
      s!"nonnested source neighbour has unexpected recursor flags: {s}"
  let t := on.cenv.p3CanonRecs.toArray.filter fun (_, rv) =>
    rv.all.any fun n => toLeanName n == `KernelSpecC1.T
  need (!t.isEmpty) "nested Type neighbour has no canonical recursors"
  for (n, rv) in t do
    need (rv.cnst.levelParams.map toLeanName == #[`u] && !rv.k)
      s!"nested Type neighbour must retain large elimination: {n.pretty}"
    emit <| Json.mkObj [("kind", toJson ("canonical-flags" : String)),
      ("member", toJson ("KernelSpecC1.T" : String)), ("name", nameData n),
      ("level_params", Json.arr (rv.cnst.levelParams.map nameData)),
      ("k", toJson rv.k), ("recursor", toJson (reprStr rv))]

private def checkReaders (dir path : System.FilePath) (names : Array String)
    (anon : Bool := false) : IO Unit := do
  need (!names.isEmpty) "empty reader request"
  need (names.toList.eraseDups.length == names.size) "duplicate pretty reader selector"
  IO.FS.createDirAll dir
  let run ← Tests.Ix.Compile.Pass3.kernelRun dir path names (anon := anon)
  -- kernelRun's permitted documented declines are insufficient here. Require
  -- an actual accepting owning-record verdict for every requested C1 record.
  let report ← IO.ofExcept <| Tests.Ix.Compile.KernelReport.parse
    (← IO.FS.readFile (dir / "cert.jsonl"))
  let decoded ← IO.ofExcept <| Ixon.deEnvVerifiedLazy (← IO.FS.readBinFile path)
  let ownerMap : Std.HashMap String String := decoded.namedRows.foldl (init := {})
    fun m row => m.insert row.name.pretty
      (toString (Tests.Ix.Compile.AuxCert.recordOf decoded.env row.addr))
  let rawMap : Std.HashMap String String := decoded.namedRows.foldl (init := {})
    fun m row => m.insert row.name.pretty (toString row.addr)
  let mut requested : Array Json := #[]
  let mut rawAddresses : Array String := #[]
  for n in names do
    let some owner := ownerMap[n]? | throw (IO.userError s!"owner missing for {n}")
    let some raw := rawMap[n]? | throw (IO.userError s!"raw address missing for {n}")
    let some v := report[owner]? | throw (IO.userError s!"certified row missing for {n}")
    requested := requested.push <| Json.mkObj [("name", toJson n),
      ("owner", toJson owner), ("raw", toJson raw),
      ("outcome", toJson v.outcome), ("reason", toJson v.reason)]
    rawAddresses := rawAddresses.push raw
  emit <| Json.mkObj [("kind", toJson ("readers" : String)),
    ("directory", toJson dir.toString), ("anon", toJson anon),
    ("requested", Json.arr requested), ("failed", toJson (reprStr run.failed)),
    ("checked", toJson run.checked)]
  need run.failed.isEmpty s!"reader failures: {reprStr run.failed}"
  for item in requested do
    need ((← IO.ofExcept (item.getObjValAs? String "outcome")) == "accept")
      s!"a repaired fixture/rule record was not accepted: {item.compress}"
  let counts : Std.HashMap String Nat := run.checked.foldl (fun m p => m.insert p.1 p.2) {}
  need (counts["cert"]? == some names.size) "certified requested-name count differs"
  -- Meta selectors count names; anonymous selectors can share one address.
  let expectedLean := if anon then rawAddresses.toList.eraseDups.length else names.size
  need (counts["lean"]? == some expectedLean) "Lean checked-target coverage differs"
  need (counts["rs"]? == some expectedLean) "Rust checked-target coverage differs"

def run (args : List String) : IO UInt32 := do
  let [workersS, order, output] := args
    | throw (IO.userError "usage: source-controls <1|32> <forward|reverse> out/<tag>/<case>")
  let some workers := workersS.toNat? | throw (IO.userError "bad worker count")
  need (workers == 1 || workers == 32) "only reviewed worker controls permitted"
  need (order == "forward" || order == "reverse") "bad source insertion order"
  need ((← IO.getEnv "IX_COMPILE_WORKERS") == some workersS &&
        (← IO.getEnv "RAYON_NUM_THREADS") == some workersS) "explicit Rust workers differ"
  need ((← IO.getEnv "IX_PASS3").isNone) "requires default compiler mode"
  let dir := System.FilePath.mk output
  need (!(← dir.pathExists)) "fresh output directory required"
  IO.FS.createDirAll dir
  let u ← unitOfFile "Tests/Ix/Compile/C1/KernelSpecC1.lean"
  let closure := if order == "reverse" then u.closure.reverse else u.closure
  let input ← IO.ofExcept <| (Ix.Compile.compileInputFromEnv u.env closure).mapError toString
  emit <| Json.mkObj [("kind", toJson ("begin" : String)),
    ("workers", toJson workers), ("order", toJson order),
    ("seeds", Json.arr (u.seeds.map (nameData ∘ ixN))),
    ("closure", Json.arr (closure.toArray.map (nameData ∘ ixN ∘ Prod.fst)))]
  let on ← match ← Ix.CompileM.compileLeanInput input (numWorkers := workers) with
    | .ok o => pure o
    | .error e => throw (IO.userError s!"Lean compile failed: {e}")
  writeNew (dir / "lean.ixe") on.bytes
  let prepared ← IO.ofExcept input.prepare
  let rs ← Ix.CompileM.rsCompileEnvBytesFFI prepared (dir / "rust.ixe").toString false
  emit <| Json.mkObj [("kind", toJson ("compiler-results" : String)),
    ("lean_ungrounded", Json.arr (on.cenv.ungrounded.toArray.map fun (n, e) =>
      Json.mkObj [("name", nameData n), ("reason", toJson e)])),
    ("rust_status", toJson (reprStr rs)), ("rust_ungrounded", toJson rs.ungrounded),
    ("named", Json.arr (on.env.named.toArray.map fun (n, nd) =>
      Json.mkObj [("name", nameData n), ("address", toJson (toString nd.addr))]))]
  need (on.cenv.ungrounded.isEmpty && rs.ungrounded.isEmpty) "partial fixture compile"
  let namesCheck := Tests.Ix.Compile.Pass3.namesCheck u on
  need namesCheck.problems.isEmpty s!"name accounting: {reprStr namesCheck.problems}"
  for (n, _) in closure do
    need (on.env.named.contains (ixN n)) s!"closure name missing: {n}"
  let rb ← IO.FS.readBinFile (dir / "rust.ixe")
  need (rb == on.bytes) "complete Lean/Rust fixture bytes differ"
  flags u on
  let seedNames := u.seeds.map toString
  let names := on.env.named.toArray.filterMap fun (n, _) =>
    if seedNames.contains n.pretty || Ix.Compile.Pass.hasReserved n then some n.pretty else none
  checkReaders (dir / "lean-readers") (dir / "lean.ixe") names
  checkReaders (dir / "rust-readers") (dir / "rust.ixe") names
  let (renv, images, rules) ← IO.ofExcept <| Tests.Ix.Compile.Pass3.ruleEnv on
  need (!images.isEmpty && !rules.isEmpty) "no changed recursor/rule witnesses"
  writeNew (dir / "rules.ixe") (← IO.ofExcept <| Ixon.serEnv renv)
  checkReaders (dir / "rule-readers") (dir / "rules.ixe") (images ++ rules) true
  emit <| Json.mkObj [("kind", toJson ("end" : String)),
    ("workers", toJson workers), ("order", toJson order),
    ("all_requested_complete", toJson true), ("byte_identical", toJson true)]
  return 0

end EarlyC1SourceControls

def main (args : List String) : IO UInt32 := EarlyC1SourceControls.run args
