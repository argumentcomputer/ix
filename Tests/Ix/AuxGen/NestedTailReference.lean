import Tests.Ix.AuxGen.NineReference
import Tests.Ix.AuxGen.Reference.NestedTails

namespace Tests.Ix.AuxGen.NestedTailReference
open _root_.Ix _root_.Ix.AuxGen
open Lean (Json)

run_cmd do
  let env ← Lean.getEnv
  for (stem, suffix, aliasName) in #[
      ("Tests.Ix.AuxGen.NineReference", "tail", `completeTail),
      ("Tests.Ix.AuxGen.NineReference", "encodingControls", `encodingControls),
      ("Tests.Ix.AuxGen.PatchReference", "name", `name),
      ("Tests.Ix.AuxGen.PatchReference", "names", `names)] do
    let found := env.constants.fold (init := (#[] : Array Lean.Name)) fun acc n _ =>
      if n.toString.startsWith ("_private." ++ stem ++ ".") && n.toString.endsWith ("." ++ stem ++ "." ++ suffix) then acc.push n else acc
    unless found.size == 1 do throwError "nested reference alias {stem}.{suffix}: {found}"
    Lean.Elab.Command.elabCommand (← `(abbrev $(Lean.mkIdent aliasName) := @$(Lean.mkIdent found[0]!)))

private def nat (n : Nat) : Json := .str (toString n)
private def optional (f : α → Json) : Option α → Json
  | none => .arr #[.str "none"] | some x => .arr #[.str "some", f x]
private def require (ok : Bool) (why : String) : Except String Unit :=
  unless ok do throw s!"nested reference: {why}"
private abbrev Tail := ((Option Ixon.AuxLayout × AuxTailRecs) × AuxKernelCtx) × CompileM.BlockState
private def encode (t : Tail) : Except String Json := completeTail t.1.1.1 t.1.1.2 t.2
private def verdict : AuxVerdict → Json
  | .identical => .arr #[.str "identical"] | .accepted => .arr #[.str "accepted"]
  | .refused e => .arr #[.str "refused", .str e] | .exempt e => .arr #[.str "exempt", .str e]
private def canonical : CanonicalVerdict → Json
  | .installed => .arr #[.str "installed"] | .refused e => .arr #[.str "refused", .str e]
  | .leanSame n => .arr #[.str "leanSame", nat n] | .leanDiffer n => .arr #[.str "leanDiffer", .str n]
private def kind : GeneratedKind → Json
  | .recursor => .str "recursor" | .casesOnDef => .str "casesOnDef" | .recOnDef => .str "recOnDef"
  | .belowDef => .str "belowDef" | .belowFamily => .str "belowFamily" | .belowRecursor => .str "belowRecursor"
  | .brecOnDef => .str "brecOnDef" | .brecOnGo => .str "brecOnGo" | .brecOnEq => .str "brecOnEq" | .other => .str "other"
-- All seven report fields, with full structured names; the inherited census
-- rejects field additions. No global BEq instance moves across import cycles.
private def report (r : BlockReport) : Json := Json.mkObj [
  ("canonical", optional canonical r.canonical),
  ("generated", .arr (r.generated.map fun (n, k) => .arr #[name n, kind k])),
  ("admitted", .arr (r.admitted.map fun (n, v) => .arr #[name n, verdict v])),
  ("exempt", optional Json.str r.exempt), ("display", .arr (r.display.map fun (n, d) => .arr #[name n, name d])),
  ("refusal", optional (fun e => .arr #[.str e.scope, .str e.question, .str e.reason]) r.refusal),
  ("retried", optional Json.str r.retried)]

private def read : Except String (Array Json) := do
  Reference.JsonTable.controls
  encodingControls
  let table ← Json.parse Reference.NestedTails.json
  require (Reference.NestedTails.json.utf8ByteSize == 28531 && (← table.getObjVal? "count") == nat 782 &&
    (← table.getObjVal? "root") == nat 781 && (← table.getObjVal? "expandedBytes") == nat 187636 &&
    (← table.getObjVal? "depth") == nat 27) "table identity/coverage differs"
  let document ← Reference.JsonTable.decode 187636 table
  let rows ← (← document.getObjVal? "rows").getArr?
  let header := Json.mkObj [("schema", .str "m7-nested-tail-expectations-v1"),
    ("parent", .str "328dcebd681efbcbed3ff877f40031829ca689ef"),
    ("normalization", .str "tail encoder normalizes auxReport only; raw reports archived separately; live checked rollback clears only retried"),
    ("emptyGuards", .str "reviewed NineReference field census and complete tail guards unchanged"),
    ("count", nat 2), ("rows", .arr rows)]
  require (document == header) "schema/provenance/normalization differs"
  return rows

private def checkRow (rows : Array Json) (i : Nat) (actual : Json) : Except String Unit := do
  require (rows.size == 2 && i < 2) "case coverage differs"
  require (rows[i]! == actual) s!"complete case differs at {i}"
private def rejected (result : Except String Unit) (wanted : String) : Except String Unit := do
  match result with
  | .error e => require (e == wanted) s!"wrong perturbation failure: {e}"
  | .ok _ => throw "nested reference: perturbation escaped the ordinary checker"

/-- Bind each actual input context even though their complete tails agree.
The original evaluator guards and legacy arms remain upstream. -/
def check (i : Nat) (modules seeds : Array Lean.Name) (planted : Option Name)
    (env : Environment) (blocks : CondensedBlocks) (key : Name) (members : Array Name)
    (why : String) (retry direct : Tail) : Except String Unit := do
  require (i < 2 && !members.isEmpty) "case coverage differs"
  for t in #[retry, direct] do
    let c := t.1.2
    require (c.generated.size == 2 && c.admitted.size == 2 &&
      c.admitted.all (fun (_, v) => v == .exempt s!"{AuxTable.notAcceptedPrefix}{why}") &&
      t.1.1.2.recs.size == 2 && t.1.1.2.belowRecs.isEmpty) "exemption/recursor coverage differs"
    require (c.ixcStats.recRefused == 0 && c.scopeEpoch == 0 && c.tcState.env.consts.isEmpty &&
      c.ingressCache.isEmpty && c.auxIngressSeen.isEmpty && c.sourceNames.isEmpty) "checked tail refused or touched legacy state"
  require (retry.2.auxReport.retried == some why && direct.2.auxReport.retried.isNone) "retry reason differs"
  let payload ← encode retry
  require (payload == (← encode direct)) "whole checked state rollback differs"
  require (report { retry.2.auxReport with retried := none } == report direct.2.auxReport)
    "whole checked report rollback differs (only retried may differ)"
  let allNames := env.consts.toArray.map (·.1) |>.qsort (fun a b => Name.cmpRaw a b == .lt)
  let actual := Json.mkObj [("case", .str (#["controls-planted-alias", "retry-tier-tree"] : Array String)[i]!),
    ("modules", .arr (modules.map (Json.str ∘ toString))), ("seeds", names (seeds.map Name.fromLeanName)),
    ("planted", optional name planted), ("inputNames", names allNames),
    ("inputCount", nat env.consts.size), ("blockCount", nat blocks.blocks.size),
    ("key", name key), ("members", names members), ("reason", .str why), ("exempt", nat 2), ("expected", payload)]
  let rows ← read
  checkRow rows i actual
  rejected (checkRow rows.pop i actual) "nested reference: case coverage differs"
  let mismatch := s!"nested reference: complete case differs at {i}"
  rejected (checkRow #[rows[1]!, rows[0]!] i actual) mismatch
  let .arr #[layout, recs, prop, state] := payload | throw "nested reference: tail shape differs"
  let changed ← if i == 0 then do
    let .bool flag ← state.getObjVal? "univsFinal" | throw "nested reference: state flag shape differs"
    pure (.arr #[layout, recs, prop, state.setObjVal! "univsFinal" (.bool !flag)])
  else do
    let .arr #[.str "some", .arr #[perm, ctors, .arr evap]] := layout | throw "nested reference: layout shape differs"
    require (evap == #[nat 0]) "raw evaporation fixture differs"
    pure (.arr #[.arr #[.str "some", .arr #[perm, ctors, .arr #[]]], recs, prop, state])
  rejected (checkRow rows i (actual.setObjVal! "expected" changed)) mismatch

end Tests.Ix.AuxGen.NestedTailReference
