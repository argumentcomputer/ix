import Tests.Ix.AuxGen.BelowIxc
import Tests.Ix.AuxGen.MLListElimination
import Tests.Ix.AuxGen.Reference.MLList
import Tests.Ix.AuxGen.NineReference
import Lean.Elab.Command

namespace Tests.Ix.AuxGen.MLListReference
open _root_.Ix _root_.Ix.AuxGen
open Lean (Json)

run_cmd do
  let env ← Lean.getEnv
  for (stem, suffix, aliasName) in #[
      ("Tests.Ix.AuxGen.NineReference", "tail", `completeTail),
      ("Tests.Ix.AuxGen.NineReference", "encodingControls", `encodingControls),
      ("Tests.Ix.AuxGen.PatchReference", "name", `name),
      ("Tests.Ix.AuxGen.PatchReference", "names", `names),
      ("Tests.Ix.AuxGen.PatchReference", "level", `level),
      ("Tests.Ix.AuxGen.PatchReference", "expr", `expr),
      ("Tests.Ix.AuxGen.PatchReference", "definition", `definition),
      ("Tests.Ix.AuxGen.PatchReference", "familyInput", `familyInput),
      ("Tests.Ix.AuxGen.PatchReference", "recursors", `recursors)] do
    let found := env.constants.fold (init := (#[] : Array Lean.Name)) fun acc n _ =>
      if n.toString.startsWith ("_private." ++ stem ++ ".") && n.toString.endsWith ("." ++ stem ++ "." ++ suffix) then acc.push n else acc
    unless found.size == 1 do throwError "MLList encoder alias {stem}.{suffix}: {found}"
    Lean.Elab.Command.elabCommand (← `(abbrev $(Lean.mkIdent aliasName) := @$(Lean.mkIdent found[0]!)))

private def nat (n : Nat) : Json := .str (toString n)
private def option (f : α → Json) : Option α → Json
  | none => .arr #[.str "none"] | some x => .arr #[.str "some", f x]
private def ensure (ok : Bool) (why : String) : Except String Unit := unless ok do throw s!"MLList reference: {why}"
private def need (ok : Bool) (why : String) : IO Unit := IO.ofExcept (ensure ok why)
private def locals (xs : Array (Name × Expr)) : Except String Json :=
  Json.arr <$> xs.mapM (fun (n, e) => do return .arr #[name n, ← expr e])
private def how : WhnfHow → Json
  | .stuck => .str "stuck" | .same => .str "same" | .replayed => .str "replayed" | .beta => .str "beta"
private def capability (o : AuxOracle) : Json := .arr #[.str (reprStr o.mode), .bool o.trace,
  .bool o.recursors, .bool o.asked, option Json.str (o.blockStatus ()), .bool o.retry.isSome]
private def declaration : GeneratedDecl → Except String Json
  | .defn n us t v thm => do return .arr #[.str "defn", name n, names us, ← expr t, ← expr v, .bool thm]
  | .family ts rs => do return .arr #[.str "family", ← familyInput ts, ← recursors rs]
private abbrev Catalogue := Std.HashMap Json Json
private def marker := "M7_MLLIST_COMPUTED_ANSWER:"
private def observe (known : Catalogue) (key answer : Json) : Except String Unit := do
  match known.get? key with
  | some expected => ensure (expected == answer) "recorded answer mismatch"
  | none => throw (marker ++ (Json.mkObj [("schema", .str "m7-mlist-query-v1"), ("key", key), ("answer", answer)]).compress)
private def badScope (error : String) : OracleScope :=
  .mk (fun _ => .error error) (fun _ => .error error) (fun _ => .error error)
    (fun _ => .error error) (fun _ => .error error) (fun _ _ => .error error) (fun _ => .error error)
private def headLookup (overlay input : Name → Option ConstantInfo) (e : Expr) : Except String Json := do
  match Ixc.stripMData (decomposeApps (Ixc.stripMData e)).1 with
  | .const n _ _ =>
    let record ← match Ixc.overlaid overlay input n with
      | some (.inductInfo v) => pure (.arr #[.str "inductInfo", name v.cnst.name, names v.cnst.levelParams, ← expr v.cnst.type,
          nat v.numParams, nat v.numIndices, names v.all, names v.ctors, nat v.numNested, .bool v.isRec, .bool v.isUnsafe, .bool v.isReflexive])
      | some (.ctorInfo c) => pure (.arr #[.str "ctorInfo", name c.cnst.name, names c.cnst.levelParams, ← expr c.cnst.type,
          name c.induct, nat c.cidx, nat c.numParams, nat c.numFields, .bool c.isUnsafe])
      | _ => throw "MLList reference: unmeasured lazy head-lookup variant"
    return .arr #[name n, .str (if (overlay n).isSome then "overlay" else "input"), record]
  | _ => return .str "no-lookup"

-- Scope state is explicit; genuine operations run first and their real
-- successors are wrapped. Queries never return a stored reference answer.
private def wrapScope : Nat → Catalogue → Json → String → (Expr → Except String Json) → Array Name → Array (Name × Expr) → Array Json → OracleScope → OracleScope
  | 0, _, _, _, _, _, _, _, _ => badScope "MLList reference: scope wrapper fuel exhausted"
  | fuel + 1, known, installed, route, lookup, us, ls, history, s => Id.run do
    let key (op : String) (input : Array Json) (head : Option Expr := none) : Except String Json := do
      let observed ← if route == "lazy" then match head with
        | some e => lookup e | none => throw "MLList reference: unmeasured lazy query operation"
        else pure (.str "not-lazy")
      return Json.mkObj [("source", nat 0), ("installed", installed), ("scope", .str route),
        ("universes", names us), ("locals", ← locals ls), ("history", .arr history),
        ("operation", .str op), ("input", .arr input), ("headLookup", observed)]
    let next := wrapScope fuel known installed route lookup us ls history
    return .mk
      (fun e => do
        let (answer, fast, after) ← s.getLevel e
        observe known (← key "getLevel" #[← expr e]) (.arr #[level answer, .bool fast])
        return (answer, fast, next after))
      (fun ds => do
        let after ← s.push ds
        return wrapScope fuel known installed route lookup us (ls ++ ds) (history.push (.arr #[.str "push", ← locals ds])) after)
      (fun n => do
        let after ← s.pop n
        ensure (n ≤ ls.size) "pop context tracking mismatch"
        return wrapScope fuel known installed route lookup us (ls.extract 0 (ls.size - n)) (history.push (.arr #[.str "pop", nat n])) after)
      (fun e => do
        let (answer, after) ← s.infer e
        observe known (← key "infer" #[← expr e]) (← expr answer)
        return (answer, next after))
      (fun e => do
        let (answer, after) ← s.whnf e
        observe known (← key "whnf" #[← expr e]) (← expr answer)
        return (answer, next after))
      (fun a b => do
        let (answer, after) ← s.isDefEq a b
        observe known (← key "isDefEq" #[← expr a, ← expr b]) (.bool answer)
        return (answer, next after))
      (fun e => do
        let (answer, method, after) ← s.whnfNamed e
        ensure (route != "lazy" || method == .stuck) "unmeasured lazy named reduction"
        observe known (← key "whnfNamed" #[← expr e] (some e)) (.arr #[← expr answer, how method])
        return (answer, method, next after))

-- A successor's key includes every actual installer argument and result,
-- retaining the complete successful lineage. Overlay callbacks pass through.
private def wrapOracle (input : Name → Option ConstantInfo) : Nat → Nat → Catalogue → Json → AuxOracle → Except String AuxOracle
  | 0, _, _, _, _ => .error "MLList reference: oracle wrapper fuel exhausted"
  | fuel + 1, scopeFuel, known, installed, o => do
    ensure (o.mode == .failClosed && o.recursors && o.retry.isNone) "capture capability must be failClosed/recursors/no-retry"
    let next (op : String) (args result : Json) (after : AuxOracle) :=
      wrapOracle input fuel scopeFuel known (.arr #[installed, .str op, args, result, capability after]) after
    return .mk o.mode o.trace
      (fun us ls => do return wrapScope scopeFuel known installed "eager" (fun _ => .ok (.str "not-lazy")) us ls #[] (← o.newScope us ls))
      (fun classes originals rs => do
        let result ← o.withFlat classes originals rs
        match result with
        | none => return none
        | some after => some <$> next "withFlat" (.arr #[.arr (classes.map names), names originals, ← recursors rs]) (.str "some") after)
      (fun ds => do
        let (after, ok, bad) ← o.admitBelow ds
        let args ← ds.mapM fun d => definition "belowDef" d.name d.levelParams d.typ d.value d.isUnsafe
        return (← next "admitBelow" (.arr args) (.arr #[nat ok, nat bad]) after, ok, bad))
      o.recursors o.asked
      (fun overlay us ls => wrapScope scopeFuel known installed "lazy" (headLookup overlay input) us ls #[] (o.newLazyScope overlay us ls))
      (fun ds => do
        let (after, rows) ← o.admit ds
        let result := .arr (rows.map fun (n, why) => .arr #[name n, option Json.str why])
        return (← next "admit" (.arr (← ds.mapM declaration)) result after, rows))
      o.blockStatus none
      (fun ts => do let after ← o.withFamily ts; next "withFamily" (← familyInput ts) (.str "installed") after)

abbrev Output := (Option Ixon.AuxLayout × AuxTailRecs) × AuxKernelCtx
abbrev Tail := Output × CompileM.BlockState
private def run (cenv : CompileM.CompileEnv) (lo : Name) (members : Array Name) (o : AuxOracle) :
    Except CompileM.CompileError Output × CompileM.BlockState := Id.run do
  let action : CompileM.CompileM Output := do
    let some (cs, sorted, addr, maps) ← Tests.Ix.AuxGen.BelowIxc.tailArgs lo members
      | throw (.unsupportedExpr "MLList reference: actual tail missing")
    (compileMutualAuxTail cs sorted addr maps (.ixc maps o)).run AuxKernelCtx.new
  -- The public CompileM.run discards the state on error. Retain this same
  -- stack's error/state pair to read refuseIxc's structured reason directly.
  return StateT.run (ExceptT.run (ReaderT.run action (cenv,
    { all := {}, current := lo, mutCtx := default, univCtx := [] }))) {}
private def success : Except CompileM.CompileError Output × CompileM.BlockState → Except String Tail
  | (.ok out, state) => pure (out, state) | (.error e, _) => .error (toString e)
private def transport (error : CompileM.CompileError) (r : IxcRefusal) (key : Json) : Except String String := do
  let raw := (AuxKernelError.kernel (.ixc s!"{r.question} in {r.scope}") r.reason).toCompileError
  if error == raw then return "direct"
  let ls ← (← key.getObjVal? "locals").getArr?
  if (← key.getObjVal? "operation") == .str "getLevel" && (← key.getObjVal? "scope") == .str "eager" &&
      r.scope == s!".brecOn's scope at depth {ls.size}" then
    -- Exact landed BRecOn.lean:1266–1274 envelope; the actual two recursors
    -- bound its original/aux class indices (call sites1818/1901).
    for ci in [:2] do
      let wrapped := CompileM.CompileError.unsupportedExpr s!"brecOn ilvl inference failed for motive at class {ci}: TcScope::get_level on major domain returned {raw}. This typically means `canon_kenv` is missing a required inductive — check that Phase 2 (populate_canon_kenv_with_below) ran before brecOn generation"
      if error == wrapped then return s!"brecOn-ilvl/class{ci}"
  throw s!"MLList reference: genuine failure: {error}"
private def packet (r : Except CompileM.CompileError Output × CompileM.BlockState) : Except String Json := do
  let (.error error, state) := r | throw "MLList reference: expected capture stop, got a tail"
  let some refusal := state.auxReport.refusal | throw s!"MLList reference: genuine failure without structured refusal: {error}"
  ensure (refusal.reason.startsWith marker) s!"genuine failure: {error}"
  let p ← Json.parse ((refusal.reason.drop marker.length).toString)
  let k ← p.getObjVal? "key"; let answer ← p.getObjVal? "answer"
  ensure (p == Json.mkObj [("schema", .str "m7-mlist-query-v1"), ("key", k), ("answer", answer)]) "capture packet shape differs"
  discard <| transport error refusal k
  return Json.mkObj [("key", k), ("answer", answer), ("scopeSite", .str refusal.scope), ("questionSite", .str refusal.question)]
private def encode (t : Tail) : Except String Json := completeTail t.1.1.1 t.1.1.2 t.2
private def coverage (t : Tail) : IO Unit := do
  let s := t.1.2.ixcStats
  need (s.queries == 62 && s.recWhnf == 20 && s.elim == 1 && s.belowAdmitted == 2) "coverage changed from62/20/1/2; stop for explanation"
  need (s.answered == s.queries && [s.refused, s.scopesRefused, s.flatRefused,
    s.leanRecDiffer, s.belowRefused, s.recRefused, s.elimRefused, s.familyRefused].all (· == 0)) "genuine query/refusal/difference"
private def genuine (why : String) (r : Except CompileM.CompileError Output × CompileM.BlockState) : IO Unit := do
  let (.error error, state) := r | throw (IO.userError "genuine-error control unexpectedly succeeded")
  let some refusal := state.auxReport.refusal | throw (IO.userError "genuine-error control lost structured refusal")
  need (refusal.reason == why && error ==
    (AuxKernelError.kernel (.ixc s!"{refusal.question} in {refusal.scope}") why).toCompileError) "wrong genuine-error category/site/cause"
  match packet r with
  | .error e => need (e == s!"MLList reference: genuine failure: {error}") "genuine error misclassified"
  | .ok _ => throw (IO.userError "genuine error became a capture packet")

private def read : Except String (Json × Array Json × Array Json × Json) := do
  Reference.JsonTable.controls; encodingControls
  let t ← Json.parse Reference.MLList.json
  ensure (Reference.MLList.json.utf8ByteSize == 169788 && (← t.getObjVal? "count") == nat 3981 &&
    (← t.getObjVal? "root") == nat 3980 && (← t.getObjVal? "depth") == nat 42 && (← t.getObjVal? "expandedBytes") == nat 8883319) "table identity differs"
  let d ← Reference.JsonTable.decode 8883319 t
  let input ← d.getObjVal? "input"; let expected ← d.getObjVal? "expected"
  let rows ← (← d.getObjVal? "queries").getArr?; let routes ← (← d.getObjVal? "transports").getArr?
  ensure (rows.size == 67 && routes.size == 67 && d == Json.mkObj [
    ("schema", .str "m7-mlist-scoped-expectations-proposal-v1"), ("witness-sha256", .str "7d7ef2febb14074265bea7a8c69fb0cb00deb85e4778bbade2e387087e494a53"),
    ("input", input), ("queries", .arr rows), ("transports", .arr routes), ("count", nat 67), ("expected", expected),
    ("elimination", .str "decision is not an oracle callback; full-tail/existing elimination assertions only, no captured decision answer"),
    ("coverage", .arr (#["62", "20", "1", "2", "20-stuck", "0-forced", "54-level-rows", "13-named-rows"].map Json.str))]) "complete document/coverage differs"
  return (input, rows, routes, expected)
private def actualInput (env : Environment) (svc : Source.Service) (n : Lean.Name) (lo : Name) (members : Array Name) : Except String Json := do
  let owner := Name.fromLeanName n
  ensure (svc.statusOf? owner == some (.tier "unsafe") && (svc.firstUnaccepted? #[owner]).isSome &&
    (svc.env.fold.fe.find? (Ix.LeanIngress.ingressKey owner)).isNone && (svc.env.answers.find? (svc.env.key owner)).isSome) "unsafe/not-accepted/logical-absence policy changed"
  let some (.inductive ts cs rs) := svc.input.blockGroupOf? owner | throw "MLList reference: actual group missing"
  let b ← (Ix.LeanIngress.convertTierInductive ts cs rs).mapError Source.renderRead
  ensure (b.types.all (fun (cv, _) => cv.levelParams == [0]) && b.recs.length == 2 &&
    b.recs.all (fun (cv, _, _) => cv.levelParams == [1, 0])) "fresh-eliminator-first headers changed"
  let ns := env.consts.toArray.map (·.1) |>.qsort (fun a b => Name.cmpRaw a b == .lt)
  return Json.mkObj [("parent", .str "c8506f477cefa8fab2d92676117b168aa8df300b"), ("module", .str "Batteries.Data.MLList.Basic"),
    ("seeds", names ((#[n, n ++ `below, n ++ `brecOn]).map Name.fromLeanName)), ("inputNames", names ns),
    ("key", name lo), ("members", names members), ("tier", .str "unsafe/not-accepted"), ("family", ← familyInput (ts.zip cs)),
    ("providedRecursors", ← recursors (rs.map fun r => (r.cnst.name, r))), ("blockLevels", .arr (b.types.toArray.map fun (cv, _) => .arr (cv.levelParams.toArray.map nat))),
    ("recursorLevels", .arr (b.recs.toArray.map fun (cv, _, _) => .arr (cv.levelParams.toArray.map nat)))]
private def inputCheck (expected actual : Json) : Except String Unit := ensure (expected == actual) "input/header binding differs"

/-- Consume the original fixture and actual checked baseline; all operations
compute real answers against the captured complete expectation. The data is never returned as an oracle answer. -/
def check (env : Environment) (cenv : CompileM.CompileEnv) (svc : Source.Service) (n : Lean.Name)
    (lo : Name) (members : Array Name) (real : AuxOracle) (baseline : Tail) : IO Unit := do
  MLListElimination.check env cenv lo (Name.fromLeanName n) members real
  let (input, rows, routes, expected) ← IO.ofExcept read
  let actual ← IO.ofExcept (actualInput env svc n lo members)
  IO.ofExcept (inputCheck input actual)
  match inputCheck input (actual.setObjVal! "recursorLevels" (.arr #[.arr #[nat 0, nat 1], .arr #[nat 1, nat 0]])) with
  | .error e => need (e == "MLList reference: input/header binding differs") "wrong header-order refusal"
  | .ok _ => throw (IO.userError "wrong header order escaped ordinary input checker")
  let mut known : Catalogue := {}
  for p in rows do
    let k ← IO.ofExcept (p.getObjVal? "key"); need (!(known.contains k)) "duplicate scoped reference"
    known := known.insert k (← IO.ofExcept (p.getObjVal? "answer"))
  let initial := Json.arr #[.str "initial", nat 0, capability real]
  let invoke (catalogue : Catalogue) (scopeFuel : Nat := 256) := do
    let o ← IO.ofExcept (wrapOracle env.get? 32 scopeFuel catalogue initial real)
    IO.lazyPure fun _ => run cenv lo members o
  let checked ← IO.ofExcept (success (← invoke known))
  let direct ← IO.ofExcept (success (← IO.lazyPure fun _ => run cenv lo members real))
  for t in #[baseline, checked, direct] do
    coverage t; need (t.1.1.2.recs.size == 2 && t.1.2.ixcStats.recStuck == 20 && t.1.2.ixcStats.recForced == 0) "actual class/lazy boundary changed"
    need ((← IO.ofExcept (encode t)) == expected) "complete captured/baseline/wrapped/unwrapped tail differs"
  for t in #[baseline, checked, direct] do need t.2.auxReport.refusal.isNone "final refusal"
  let reachable (catalogue : Catalogue) (p route : Json) : IO Bool := do
    let k ← IO.ofExcept (p.getObjVal? "key"); let r ← invoke (catalogue.erase k)
    match r.1 with
    | .ok _ => return false
    | .error error =>
      let observed ← IO.ofExcept (packet r)
      let some refusal := r.2.auxReport.refusal | throw (IO.userError "missing structured refusal")
      return observed == p && .str (← IO.ofExcept (transport error refusal k)) == route
  for (p, route) in rows.zip routes do need (← reachable known p route) "unreachable/misbound request or transport"
  let first := rows[0]!
  let k ← IO.ofExcept (first.getObjVal? "key"); let answer ← IO.ofExcept (first.getObjVal? "answer")
  let .arr #[.arr fields, method] := answer | throw (IO.userError "first named answer shape differs")
  let .arr #[.str hash, size] := fields.back! | throw (IO.userError "stored expression hash missing")
  need (hash.length == 64) "hash-control shape changed"
  let altered := (if hash.startsWith "0" then "1" else "0") ++ (hash.drop 1).toString
  genuine "MLList reference: recorded answer mismatch" (← invoke (known.insert k (.arr #[.arr (fields.set! (fields.size - 1) (.arr #[.str altered, size])), method])))
  let some observed := rows.find? (fun p => match (p.getObjVal? "key" >>= (·.getObjVal? "headLookup")) with | .ok (.arr _) => true | _ => false)
    | throw (IO.userError "actual composed lookup missing")
  let lk ← IO.ofExcept (observed.getObjVal? "key"); let la ← IO.ofExcept (observed.getObjVal? "answer")
  let .arr #[head, origin, .arr record] ← IO.ofExcept (lk.getObjVal? "headLookup") | throw (IO.userError "lookup record changed")
  let .bool flag := record.back! | throw (IO.userError "lookup Boolean missing")
  let changed := lk.setObjVal! "headLookup" (.arr #[head, origin, .arr (record.set! (record.size - 1) (.bool !flag))])
  match observe known changed la with
  | .error e => need (e == marker ++ (Json.mkObj [("schema", .str "m7-mlist-query-v1"), ("key", changed), ("answer", la)]).compress) "wrong composed-lookup refusal"
  | .ok _ => throw (IO.userError "lookup mutation escaped ordinary key check")
  let fake := k.setObjVal! "input" (.arr #[← IO.ofExcept (expr (Expr.mkConst (Name.mkStr .mkAnon "M7_unreachable_query") #[]))])
  need (!(known.contains fake) && !(← reachable (known.insert fake answer) (first.setObjVal! "key" fake) routes[0]!)) "unused reference escaped coverage"
  genuine "MLList reference: scope wrapper fuel exhausted" (← invoke known 0)
  match wrapOracle env.get? 0 256 known initial real with
  | .error e => need (e == "MLList reference: oracle wrapper fuel exhausted") "wrong oracle exhaustion"
  | .ok _ => throw (IO.userError "oracle wrapper fuel ignored")
  IO.println "MLList reference: full input/headers/tail, all67 scoped answers and reachability/corruption/lookup/exhaustion controls passed"

end Tests.Ix.AuxGen.MLListReference
