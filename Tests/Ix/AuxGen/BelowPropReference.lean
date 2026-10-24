import Tests.Ix.AuxGen.NestedTailReference
import Tests.Ix.AuxGen.Reference.BelowProp

namespace Tests.Ix.AuxGen.BelowPropReference
open _root_.Ix _root_.Ix.AuxGen
open Lean (Json toJson)

run_cmd do
  let env ← Lean.getEnv
  for (stem, suffix, aliasName) in #[
      ("Tests.Ix.AuxGen.NineReference", "tail", `completeTail),
      ("Tests.Ix.AuxGen.NineReference", "encodingControls", `encodingControls),
      ("Tests.Ix.AuxGen.NestedTailReference", "report", `rawReport),
      ("Tests.Ix.AuxGen.PatchReference", "name", `name),
      ("Tests.Ix.AuxGen.PatchReference", "names", `names)] do
    let found := env.constants.fold (init := (#[] : Array Lean.Name)) fun acc n _ =>
      if n.toString.startsWith ("_private." ++ stem ++ ".") && n.toString.endsWith ("." ++ stem ++ "." ++ suffix) then acc.push n else acc
    unless found.size == 1 do throwError "Below Prop alias {stem}.{suffix}: {found}"
    Lean.Elab.Command.elabCommand (← `(abbrev $(Lean.mkIdent aliasName) := @$(Lean.mkIdent found[0]!)))
  let some info := Lean.getStructureInfo? env ``AuxKernelCtx | throwError "kernel context missing"
  unless info.fieldNames == #[`tcState, `ingressCache, `sourceNames, `auxIngressSeen, `scopeEpoch,
      `ixcStats, `canonical, `canonicalOracle, `generated, `admitted] && info.parentInfo.isEmpty do
    throwError "unmeasured kernel-context field: {info.fieldNames}"

-- Derivation retains every stats field, including future additions.
deriving instance Lean.ToJson for IxcStats
private def nat (n : Nat) : Json := .str (toString n)
private def require (ok : Bool) (why : String) : Except String Unit :=
  unless ok do throw s!"below reference: {why}"
private def rejected (r : Except String α) (why : String) : Except String Unit := match r with
  | .error e => require (e == why) s!"wrong control failure: {e}"
  | .ok _ => throw "below reference: negative control passed"
private def marker := "m7-json-natural-number-v1"
private def numbers : Bool → Nat → Json → Except String Json
  | _, 0, _ => throw "below reference: numeric depth exhausted"
  | inverse, fuel + 1, j => match j with
    | .num _ => do
      require (!inverse) "unwrapped numeric value"
      let text := j.compress
      let some v := text.toNat? | throw "below reference: non-natural numeric value"
      require (toString v == text) "noncanonical numeric value"
      return .arr #[.str marker, .str text]
    | .arr xs => do
      if xs.size == 2 && xs[0]? == some (.str marker) then
        require inverse "numeric marker collision"
        let text ← xs[1]!.getStr?
        let some v := text.toNat? | throw "below reference: non-natural numeric value"
        require (toString v == text) "noncanonical numeric value"
        Json.parse text
      else Json.arr <$> xs.mapM (numbers inverse fuel)
    | .obj fields => Json.mkObj <$> fields.toList.mapM (fun (k, v) => do return (k, ← numbers inverse fuel v))
    | _ => pure j
private def retired : Array String := #["tcFast", "equal", "differ", "decisionsEqual", "decisionsDiffer",
  "recEqual", "recDiffer", "recDiffName", "recDiffInfo", "recDiffLevel", "recDiffOther",
  "recDecisionDiffer", "recSkipDiffer", "elimEqual", "elimDiffer"]
-- The live view retires only the shadow call/status and enumerated Tc fields.
-- Every checked report/context field remains; no whitelist or default zeros.
private def project (row : Json) : Except String Json := do
  let .obj fields := row | throw "below reference: case object absent"
  let row := Json.mkObj (fields.toList.filter fun (k, _) => k != "shadow" && k != "shadowStatus")
  let result ← row.getObjVal? "checked"
  if let .ok context := result.getObjVal? "context" then
    let .obj stats ← context.getObjVal? "stats" | throw "below reference: stats object absent"
    let kept := Json.mkObj (stats.toList.filter fun (k, _) => !retired.contains k)
    return row.setObjVal! "checked" (result.setObjVal! "context" (context.setObjVal! "stats" kept))
  return row
private def checkRow (rows : Array Json) (i : Nat) (actual : Json) : Except String Unit := do
  require (rows.size == 219 && i < rows.size) "case coverage differs"
  require (rows[i]! == (← project actual)) s!"complete case differs at {i}"
private def changeSide (row : Json) (f : Json → Except String Json) : Except String Json := do
  return row.setObjVal! "checked" (← f (← row.getObjVal? "checked"))
private def controls (rows : Array Json) : Except String Unit := do
  let sample := Json.mkObj [("n", toJson (37 : Nat)), ("s", .str "37")]
  require ((← numbers true 1024 (← numbers false 1024 sample)) == sample) "numeric inverse differs"
  rejected (numbers false 1024 (.arr #[.str marker, .str "1"])) "below reference: numeric marker collision"
  rejected (numbers true 1024 (.arr #[.str marker, .str "01"])) "below reference: noncanonical numeric value"
  rejected (numbers true 1024 (.arr #[.str marker, .str "-1"])) "below reference: non-natural numeric value"
  rejected (checkRow rows.pop 0 rows[0]!) "below reference: case coverage differs"
  rejected (checkRow (rows.set! 1 rows[0]!) 1 rows[1]!) "below reference: complete case differs at 1"
  rejected (checkRow (rows.set! 0 rows[1]!) 0 rows[0]!) "below reference: complete case differs at 0"
  for (row, i) in rows.zipIdx do
    checkRow rows i row
    let bad := s!"below reference: complete case differs at {i}"
    rejected (checkRow rows i (row.setObjVal! "originalStatus" (.str "changed"))) bad
    let promoted ← (← row.getObjVal? "promoted").getBool?
    rejected (checkRow rows i (row.setObjVal! "promoted" (.bool !promoted))) bad
    let c ← row.getObjVal? "checked"
    if (← c.getObjVal? "outcome") == .str "failure" then
      let e ← (← c.getObjVal? "error").getStr?
      let changedError ← changeSide row fun c => pure (c.setObjVal! "error" (.str (e ++ " changed")))
      rejected (checkRow rows i changedError) bad
      let changedOutcome ← changeSide row fun c => pure (c.setObjVal! "outcome" (.str "success-no-Prop"))
      rejected (checkRow rows i changedOutcome) bad
    else
      let context ← c.getObjVal? "context"
      let stats ← context.getObjVal? "stats"
      for changed in #[context.setObjVal! "canonicalOracle" (.str "changed"),
          context.setObjVal! "stats" (stats.setObjVal! "futureField" (nat 7))] do
        let changedRow ← changeSide row fun c => pure (c.setObjVal! "context" changed)
        rejected (checkRow rows i changedRow) bad
  for i in #[36, 102] do
    let changed ← changeSide rows[i]! fun c => do
      let .arr #[layout, recs, prop, state] ← c.getObjVal? "tail" | throw "below reference: control tail shape differs"
      let tail ← if i == 36 then do
        require ((← state.getObjVal? "univsFinal") == .bool true) "state control fixture differs"
        pure (.arr #[layout, recs, prop, state.setObjVal! "univsFinal" (.bool false)])
      else do
        let .arr #[.str "some", .arr #[perm, ctors, .arr flags]] := layout | throw "below reference: control layout shape differs"
        require (flags == #[nat 0]) "raw evaporation control differs"
        pure (.arr #[.arr #[.str "some", .arr #[perm, ctors, .arr #[]]], recs, prop, state])
      return c.setObjVal! "tail" tail
    rejected (checkRow rows i changed) s!"below reference: complete case differs at {i}"

/-- Decode once; both raw capture sides stay archived. The checked call keeps
its own report/context and takes its complete output expectation from shadow. -/
def load (encoded : String) : Except String (Json × Array Json) := do
  Reference.JsonTable.controls; encodingControls
  let table ← Json.parse encoded
  require (encoded.utf8ByteSize == 3559164 && (← table.getObjVal? "count") == nat 62088 &&
    (← table.getObjVal? "root") == nat 62087 && (← table.getObjVal? "expandedBytes") == nat 53218644 &&
    (← table.getObjVal? "depth") == nat 66) "table identity/coverage differs"
  let doc ← Reference.JsonTable.decode 53218644 table
  require ((← doc.getObjVal? "schema") == .str "m7-below-prop-full-json-archive-v1") "schema differs"
  let manifest ← doc.getObjVal? "manifest"
  require ((← manifest.getObjVal? "parent") == .str "2752a2817244a5ea8b90df745feb37d50a2ff83e" &&
    (← manifest.getObjVal? "selected") == nat 219 && (← manifest.getObjVal? "Prop") == nat 14 &&
    (← manifest.getObjVal? "pairedFailures") == nat 85 && (← manifest.getObjVal? "successNoProp") == nat 120 &&
    (← manifest.getObjVal? "noTail") == nat 0) "capture provenance/coverage differs"
  let raw ← (← doc.getObjVal? "cases").getArr?
  require (raw.size == 219) "case coverage differs"
  let rows ← raw.mapM fun row => do
    let s ← row.getObjVal? "shadow"; let c ← row.getObjVal? "checked"
    let outcome ← s.getObjVal? "outcome"
    require (#[Json.str "failure", .str "Prop", .str "success-no-Prop"].contains outcome &&
      outcome == (← c.getObjVal? "outcome")) "unmeasured captured outcome"
    if (← s.getObjVal? "outcome") == .str "Prop" then
      require ((← s.getObjVal? "tail") == (← c.getObjVal? "tail")) "captured complete tails differ"
      -- The checked output expectation explicitly comes from old shadow.
      project (row.setObjVal! "checked" (c.setObjVal! "tail" (← s.getObjVal? "tail")))
    else project row
  controls rows
  return (← doc.getObjVal? "input", rows)

def read (env : Environment) (blocks : CondensedBlocks) (selected : Array (Name × Array Name)) : Except String (Array Json) := do
  let (input, rows) ← load Reference.BelowProp.json
  let ns := env.consts.toArray.map (·.1) |>.qsort (fun a b => Name.cmpRaw a b == .lt)
  let actual := selected.map fun (lo, ms) => Json.arr #[name lo, name (CompileM.blockKey lo ((blocks.blocks.get? lo).getD {})), names ms]
  require (env.consts.size == 6529 && blocks.blocks.size == 5676 && (← input.getObjVal? "inputNames") == names ns &&
    (← input.getObjVal? "rawCount") == nat 6529 && (← input.getObjVal? "canonicalCount") == nat 6529 &&
    (← input.getObjVal? "blockCount") == nat 5676 && (← input.getObjVal? "selected") == .arr actual) "actual input/member binding differs"
  return rows

abbrev Tail := (Option Ixon.AuxLayout × AuxTailRecs) × AuxKernelCtx
abbrev Output := Option Tail × CompileM.BlockState
private def context (c : AuxKernelCtx) : Except String Json := do return Json.mkObj [
  ("admissionRows", rawReport { canonical := c.canonical, generated := c.generated, admitted := c.admitted }),
  ("stats", ← numbers false 1024 (toJson c.ixcStats)), ("scopeEpoch", nat c.scopeEpoch),
  ("canonicalOracle", match c.canonicalOracle with
    | none => .null | some o => Json.mkObj [("mode", .str (reprStr o.mode)), ("trace", .bool o.trace),
      ("recursors", .bool o.recursors), ("asked", .bool o.asked), ("status", toJson (o.blockStatus ())), ("retry", .bool o.retry.isSome)]),
  ("legacyConsts", nat c.tcState.env.consts.size), ("ingressCache", nat c.ingressCache.size),
  ("auxIngressSeen", nat c.auxIngressSeen.size), ("sourceNames", nat c.sourceNames.size)]
private def observed (stateKey : CompileM.BlockState → String) : Except String Output → Except String Json
  | .error e => pure (Json.mkObj [("outcome", .str "failure"), ("error", .str e)])
  | .ok (none, _) => throw "below reference: unmeasured no-tail outcome"
  | .ok (some t, s) => do
    let prop := t.2.ixcStats.familyInstalled + t.2.ixcStats.familyRefused > 0
    let tail ← if prop then completeTail t.1.1 t.1.2 s else pure .null
    return Json.mkObj [("outcome", .str (if prop then "Prop" else "success-no-Prop")),
      ("tail", tail), ("encoderError", .null),
      ("report", rawReport s.auxReport), ("context", ← context t.2), ("stateKey", .str (stateKey s))]

-- Actual anonymous payloads and §5 Named bytes, using the writer's indexes.
private def wire (base : Ixon.Env) (s : CompileM.BlockState) : Except String (Array ByteArray × ByteArray) := do
  let ns := s.blockNames.fold (fun m a n => m.insert a n) base.names
  let nameIdx : Ixon.NameIndex := (Ixon.Env.topologicalSortNames ns).zipIdx.foldl (fun m ((a, _), i) => m.insert a i.toUInt64) {}
  let addresses := s.auxConsts.foldl (fun m (a, _) => m.insert a ()) (base.consts.fold (fun m a _ => m.insert a ()) ({} : Std.HashMap Address Unit))
  let constIdx := (addresses.toArray.map (·.1) |>.qsort Ixon.addrLt).zipIdx.foldl (fun m (a, i) => m.insert a i.toUInt64) ({} : Std.HashMap Address UInt64)
  let (result, bytes) := (Ixon.Env.putNamedEntries s.auxNamed 0 s.auxNamed.size nameIdx constIdx).run.run ByteArray.empty
  result
  return (s.auxConsts.map (fun (_, c) => Ixon.serConstant c), bytes)

/-- Consume the real checked call; no captured value is used as an answer. -/
def checkChecked (rows : Array Json) (i : Nat) (rep key : Name) (members : Array Name) (promoted : Bool)
    (checkedOracle : AuxOracle) (checked : Except String Output)
    (stateKey : CompileM.BlockState → String) (base : Ixon.Env) : Except String Unit := do
  require (checkedOracle.mode == .failClosed && checkedOracle.recursors && checkedOracle.retry.isNone) "wrong checked capability"
  let actual := Json.mkObj [("index", nat i), ("representative", name rep), ("key", name key), ("members", names members),
    ("promoted", .bool promoted), ("originalStatus", toJson (checkedOracle.blockStatus ())),
    ("checked", ← observed stateKey checked)]
  checkRow rows i actual
  if i == 36 || i == 102 then
    let .ok (some t, s) := checked | throw "below reference: live byte-control outcome differs"
    require (!s.auxConsts.isEmpty && !s.auxNamed.isEmpty) "live byte control is empty"
    let (changedTail, changedState) ← if i == 36 then do
      require s.univsFinal "live state-control fixture differs"
      pure (t, { s with univsFinal := false })
    else do
      let some l := t.1.1 | throw "below reference: live layout absent"
      require (l.evaporated == #[0] && l.perm.size == 1) "live evaporation fixture differs"
      let changed := { l with evaporated := #[] }
      let mut hits := 0
      let named := s.auxNamed.map fun (n, v) => match v.constMeta.info with
        | .muts all (some layout) => if layout == l then (n, { v with constMeta := { v.constMeta with info := .muts all (some changed) } }) else (n, v)
        | _ => (n, v)
      for (_, v) in s.auxNamed do if let .muts _ (some layout) := v.constMeta.info then if layout == l then hits := hits + 1
      require (hits > 0) "live emitted Muts layout missing"
      pure (((some changed, t.1.2), t.2), { s with auxNamed := named })
    require ((← wire base s) == (← wire base changedState)) "negative control changed serializer bytes"
    let changed ← observed stateKey (.ok (some changedTail, changedState))
    rejected (checkRow rows i (actual.setObjVal! "checked" changed)) s!"below reference: complete case differs at {i}"

end Tests.Ix.AuxGen.BelowPropReference
