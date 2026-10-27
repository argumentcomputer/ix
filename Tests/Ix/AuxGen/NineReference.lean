import Ix.CompileDriver
import Tests.Ix.AuxGen.PatchReference
import Tests.Ix.AuxGen.Reference.JsonTable
import Tests.Ix.AuxGen.Reference.Nine
import Lean.Elab.Command

namespace Tests.Ix.AuxGen.NineReference
open _root_.Ix _root_.Ix.AuxGen
open Lean (Json)

run_cmd do
  let env ← Lean.getEnv
  let stem := "Tests.Ix.AuxGen.PatchReference"
  for (suffix, aliasName) in #[("arr", `arr), ("nat", `nat), ("address", `address), ("name", `name),
      ("names", `names), ("level", `rawLevel), ("expr", `rawExpr), ("binder", `binder),
      ("recursors", `recursors), ("optional", `optional)] do
    let found := env.constants.fold (init := (#[] : Array Lean.Name)) fun acc n _ =>
      if n.toString.startsWith ("_private." ++ stem ++ ".") && n.toString.endsWith ("." ++ stem ++ "." ++ suffix) then acc.push n else acc
    unless found.size == 1 do throwError "nine reference alias {suffix}: {found}"
    Lean.Elab.Command.elabCommand (← `(abbrev $(Lean.mkIdent aliasName) := @$(Lean.mkIdent found[0]!)))
  let records : Array (Lean.Name × Array Lean.Name) := #[
    (``Ixon.ValueContract, #[`owned, `locality]), (``Ixon.BinderContract, #[`uses, `value]),
    (``Ixon.LetContract, #[`nonDep, `kind, `binder]), (``Ixon.ExprMetaArena, #[`nodes]),
    (``Ixon.AuxLayout, #[`perm, `sourceCtorCounts, `evaporated]), (``Ixon.UnivPatch, #[`arenaIdx, `univIdxs]),
    (``Ixon.ConstantMeta, #[`info, `metaSharing, `metaRefs, `metaUnivs, `univPatches]),
    (``Ixon.Named, #[`addr, `constMeta, `original, `hints]), (``Ixon.Constant, #[`info, `sharing, `refs, `univs]),
    (``Ix.Compile.ExactKey.UnivKey, #[`level, `params]), (``Ix.AuxGen.AuxTailRecs, #[`recs, `belowRecs]),
    (``Ix.AuxGen.BlockReport, #[`canonical, `generated, `admitted, `exempt, `display, `refusal, `retried]),
    (``Ix.CompileM.BlockResult, #[`block, `blockBytes, `blockAddr, `blockMeta, `projections, `classNames]),
    (``Ix.CompileM.BlockState, #[`exprCache, `univCache, `refs, `refsIndex, `univs, `univsIndex, `univsFinal,
      `canonUnivCache, `metaUnivs, `metaUnivsIndex, `univPatches, `blockBlobs, `blockNames, `defHints, `arena,
      `blockNameToAddr, `auxNameToAddr, `auxConsts, `auxNamed, `auxGenExtraNames, `auxReport, `surgerySharing])]
  unless records.size == 14 do throwError "nine witness field census coverage differs"
  for (decl, expected) in records do
    let some info := Lean.getStructureInfo? env decl | throwError "encoded structure missing: {decl}"
    unless info.fieldNames == expected && info.parentInfo.isEmpty do
      throwError "nine witness structure changed: {decl}; fields={info.fieldNames}"

private def ensure (ok : Bool) (why : String) : Except String Unit := unless ok do throw s!"nine witness: {why}"
private def u64 (n : UInt64) : Json := nat n.toNat
private def us (ns : Array UInt64) : Json := .arr (ns.map u64)
private def addrs (xs : Array Address) : Json := .arr (xs.map address)
private def bytes (b : ByteArray) : Json := arr [.str "bytes", .str (toString (Address.mk b)), nat b.size]
private def mapEntries (xs : Array (Json × Json)) : Json :=
  .arr ((xs.qsort (fun a b => a.1.compress < b.1.compress)).map fun (k, v) => arr [k, v])
private def univ : Ixon.Univ → Json
  | .zero => arr [.str "zero"] | .succ u => arr [.str "succ", univ u]
  | .max u v => arr [.str "max", univ u, univ v] | .imax u v => arr [.str "imax", univ u, univ v]
  | .var i => arr [.str "var", u64 i]
private def valueContract (v : Ixon.ValueContract) : Json := arr [
  .str (match v.owned with | .shared => "shared" | .unique => "unique"),
  .str (match v.locality with | .unrestricted => "unrestricted" | .local => "local")]
private def binderContract (b : Ixon.BinderContract) : Json := arr [
  .str (match b.uses with | .erased => "erased" | .linear => "linear" | .affine => "affine" | .many => "many"), valueContract b.value]
private def letContract (l : Ixon.LetContract) : Json := arr [.bool l.nonDep,
  .str (match l.kind with | .value => "value" | .borrowShared => "borrowShared"), binderContract l.binder]
private def ixonExpr : Ixon.Expr → Json
  | .sort i => arr [.str "sort", u64 i] | .var i => arr [.str "var", u64 i]
  | .ref i ls => arr [.str "ref", u64 i, us ls] | .recur i ls => arr [.str "recur", u64 i, us ls]
  | .prj i j e => arr [.str "prj", u64 i, u64 j, ixonExpr e]
  | .str i => arr [.str "str", u64 i] | .nat i => arr [.str "nat", u64 i]
  | .app f a => arr [.str "app", ixonExpr f, ixonExpr a]
  | .lam c t b => arr [.str "lam", binderContract c, ixonExpr t, ixonExpr b]
  | .all c r t b => arr [.str "all", binderContract c, valueContract r, ixonExpr t, ixonExpr b]
  | .letE c t v b => arr [.str "let", letContract c, ixonExpr t, ixonExpr v, ixonExpr b]
  | .share i => arr [.str "share", u64 i]
private def dataValue : Ixon.DataValue → Json
  | .ofString a => arr [.str "string", address a] | .ofBool b => arr [.str "bool", .bool b]
  | .ofName a => arr [.str "name", address a] | .ofNat a => arr [.str "nat", address a]
  | .ofInt a => arr [.str "int", address a] | .ofSyntax a => arr [.str "syntax", address a]
private def metaNode : Ixon.ExprMetaData → Json
  | .leaf => arr [.str "leaf"] | .app f a => arr [.str "app", u64 f, u64 a]
  | .binder n bi t b => arr [.str "binder", address n, binder bi, u64 t, u64 b]
  | .letBinder n t v b => arr [.str "letBinder", address n, u64 t, u64 v, u64 b]
  | .ref n => arr [.str "ref", address n] | .prj n c => arr [.str "prj", address n, u64 c]
  | .mdata ds c => arr [.str "mdata", .arr (ds.map fun kv => .arr (kv.map fun (k, v) => arr [address k, dataValue v])), u64 c]
private def arena (a : Ixon.ExprMetaArena) : Json := .arr (a.nodes.map metaNode)
private def layout (l : Ixon.AuxLayout) : Json := arr [us l.perm, us l.sourceCtorCounts, us l.evaporated]
private def metaInfo : Ixon.ConstantMetaInfo → Json
  | .empty => arr [.str "empty"]
  | .defn n ls all ctx a t v => arr [.str "defn", address n, addrs ls, addrs all, addrs ctx, arena a, u64 t, u64 v]
  | .axio n ls a t => arr [.str "axio", address n, addrs ls, arena a, u64 t]
  | .quot n ls a t => arr [.str "quot", address n, addrs ls, arena a, u64 t]
  | .indc n ls cs all ctx a t => arr [.str "indc", address n, addrs ls, addrs cs, addrs all, addrs ctx, arena a, u64 t]
  | .ctor n ls ind a t => arr [.str "ctor", address n, addrs ls, address ind, arena a, u64 t]
  | .recr n ls rs all ctx a t roots => arr [.str "recr", address n, addrs ls, addrs rs, addrs all, addrs ctx, arena a, u64 t, us roots]
  | .muts all l => arr [.str "muts", .arr (all.map addrs), optional layout l]
private def univPatch (p : Ixon.UnivPatch) : Json := arr [u64 p.arenaIdx, us p.univIdxs]
private def metadata (m : Ixon.ConstantMeta) : Json := arr [metaInfo m.info, .arr (m.metaSharing.map ixonExpr),
  addrs m.metaRefs, .arr (m.metaUnivs.map univ), .arr (m.univPatches.map univPatch)]
private def hints : Lean.ReducibilityHints → Json
  | .opaque => arr [.str "opaque"] | .abbrev => arr [.str "abbrev"] | .regular h => arr [.str "regular", nat h.toNat]
private def named (n : Ixon.Named) : Json := arr [address n.addr, metadata n.constMeta,
  optional (fun (a, m) => arr [address a, metadata m]) n.original, optional hints n.hints]
private def constant (c : Ixon.Constant) : Except String Json := do
  let raw := Ixon.serConstant c
  let decoded ← Ixon.deConstantExact raw
  ensure (decoded == c) "anonymous codec changed a raw constant field"
  return bytes raw
private def anon (cs : Array (Address × Ixon.Constant)) : Except String Json :=
  Json.arr <$> cs.mapM (fun (a, c) => do return arr [address a, ← constant c])
private def namedEntries (ns : Array (Name × Ixon.Named)) : Json := .arr (ns.map fun (n, v) => arr [name n, named v])
private def result (r : CompileM.BlockResult) : Except String Json := do
  let projections ← r.projections.mapM fun (n, c, m) => do return arr [name n, ← constant c, metadata m]
  return Json.mkObj [("block", ← constant r.block), ("blockBytes", bytes r.blockBytes), ("blockAddr", address r.blockAddr),
    ("blockMeta", metadata r.blockMeta), ("projections", .arr projections), ("classNames", .arr (r.classNames.map names))]
private def state (s : CompileM.BlockState) : Except String Json := do
  -- These exact fields are empty in the measured corpus; never erase a value.
  ensure s.exprCache.isEmpty "nonempty unmeasured BlockState field"
  ensure (s.auxReport.canonical.isNone && s.auxReport.generated.isEmpty && s.auxReport.admitted.isEmpty && s.auxReport.exempt.isNone && s.auxReport.display.isEmpty && s.auxReport.refusal.isNone && s.auxReport.retried.isNone) "caller did not perform the original auxReport normalization"
  let levels := s.univCache.toArray.map fun (k, v) => (arr [rawLevel k.level, names k.params.toArray], univ v)
  return Json.mkObj [("exprCache", .arr #[]), ("univCache", mapEntries levels), ("refs", addrs s.refs),
    ("refsIndex", mapEntries (s.refsIndex.toArray.map fun (k, v) => (address k, u64 v))),
    ("univs", .arr (s.univs.map univ)), ("univsIndex", mapEntries (s.univsIndex.toArray.map fun (k, v) => (univ k, u64 v))),
    ("univsFinal", .bool s.univsFinal), ("canonUnivCache", mapEntries (s.canonUnivCache.toArray.map fun (k, v) => (univ k, univ v))),
    ("metaUnivs", .arr (s.metaUnivs.map univ)), ("metaUnivsIndex", mapEntries (s.metaUnivsIndex.toArray.map fun (k, v) => (univ k, u64 v))),
    ("univPatches", .arr (s.univPatches.map univPatch)), ("blockBlobs", mapEntries (s.blockBlobs.toArray.map fun (k, v) => (address k, bytes v))),
    ("blockNames", mapEntries (s.blockNames.toArray.map fun (k, v) => (address k, name v))),
    ("defHints", mapEntries (s.defHints.toArray.map fun (k, v) => (name k, hints v))), ("arena", arena s.arena),
    ("blockNameToAddr", mapEntries (s.blockNameToAddr.toArray.map fun (k, v) => (name k, address v))),
    ("auxNameToAddr", mapEntries (s.auxNameToAddr.toArray.map fun (k, v) => (name k, address v))),
    ("auxConsts", ← anon s.auxConsts), ("auxNamed", namedEntries s.auxNamed),
    ("auxGenExtraNames", .arr ((s.auxGenExtraNames.toArray.qsort (fun a b => Name.cmpRaw a b == .lt)).map name)),
    ("auxReport", .str "normalized-default"), ("surgerySharing", .arr (s.surgerySharing.map ixonExpr))]
private def tail (l : Option Ixon.AuxLayout) (r : AuxTailRecs) (s : CompileM.BlockState) : Except String Json := do
  return arr [optional layout l, ← recursors r.recs, ← recursors r.belowRecs, ← state { s with auxReport := {} }]
private def full (r : CompileM.BlockResult) (s : CompileM.BlockState)
    (l : Option Ixon.AuxLayout) : Except String Json := do
  return arr [← result r, ← state { s with auxReport := {} }, optional layout l]

private def require (ok : Bool) (why : String) : Except String Unit :=
  unless ok do throw s!"nine reference: {why}"
private def encodingControls : Except String Unit := do
  let a : Ixon.AuxLayout := { perm := #[0], sourceCtorCounts := #[1], evaporated := #[] }
  require (layout a != layout { a with evaporated := #[0] } &&
    layout { a with evaporated := #[1] } != layout { a with evaporated := #[2] }) "raw evaporation distinctions lost"
  let cached : Std.HashMap _root_.Ix.Compile.ExactKey.ExprKey (Ixon.Expr × UInt64) :=
    ({} : Std.HashMap _ _).insert (_root_.Ix.Expr.mkBVar 0) (.var 0, 0)
  match state { exprCache := cached } with
  | .error e => require (e == "nine witness: nonempty unmeasured BlockState field") "wrong state refusal"
  | .ok _ => throw "nine reference: nonempty state escaped its guard"

def read (targets : Array String) : Except String (Array Json) := do
  Reference.JsonTable.controls
  encodingControls
  let table ← Json.parse Reference.Nine.json
  require ((← table.getObjVal? "count") == nat 25495 && (← table.getObjVal? "root") == nat 25494 &&
    (← table.getObjVal? "expandedBytes") == nat 17665691 && (← table.getObjVal? "depth") == nat 66) "table identity/coverage differs"
  let document ← Reference.JsonTable.decode 17665691 table
  let rows ← (← document.getObjVal? "rows").getArr?
  require (rows.size == 9 && targets.size == 9 && targets.toList.eraseDups.length == 9) "nine-target coverage differs"
  let header := Json.mkObj [("schema", .str "m7-nine-output-expectations-v1"), ("parent", .str "4beddffd09ac6a65de65e19230707b193292a0fd"),
    ("witness-sha256", .str "815b6d452045961f7869cb4242ae10f0a3a63b6753143734c51de0beb879830b"),
    ("normalization", .str "auxReport := {} only; live checked retry rollback retains every other report field"),
    ("emptyGuards", .str "BlockState: exprCache,p3Records,p3MetaRefs,p3MetaCache,p3CliquePlans,p3CliqueRows; Published: views,imageExps,declines,originals; raw Expr.mdata refuses"),
    ("namingBoundary", .str "Published views are required empty; existing Naming BEq is not extensional function equality"),
    ("count", nat 9), ("rows", .arr rows)]
  require (document == header) "schema/provenance/normalization differs"
  for (row, i) in rows.zipIdx do
    require ((← row.getObjVal? "target") == .str targets[i]!) s!"target/order differs at {i}"
  return rows

private def checkRow (i : Nat) (expected actual : Json) : Except String Unit :=
  require (expected == actual) s!"complete row differs at {i}"
private def perturb (i : Nat) (row : Json) : Except String Json := do
  let .arr #[t, f] ← row.getObjVal? "expected" | throw "nine reference: pair shape differs"
  let pair ← if i == 1 then do
    let .arr #[.arr #[.str "some", .arr #[perm, ctors, .arr evap]], recs, prop, s] := t
      | throw "nine reference: raw layout perturbation fixture differs"
    require (evap == #[nat 0]) "raw evaporation fixture differs"
    pure (arr [arr [arr [.str "some", arr [perm, ctors, .arr #[]]], recs, prop, s], f])
  else do
    let .arr #[b, s, l, p] := f | throw "nine reference: full-state perturbation fixture differs"
    require ((← s.getObjVal? "univsFinal") == .bool true) "univsFinal fixture differs"
    pure (arr [t, arr [b, s.setObjVal! "univsFinal" (.bool false), l, p]])
  return row.setObjVal! "expected" pair

/-- Consume the existing nine-loop results; no extra compilation/generation.
Every original legacy comparison and live checked rollback remains upstream. -/
def check (rows : Array Json) (i : Nat) (target : String) (key : Name) (members : Array Name)
    (reason : String) (exempt : Nat) (observed : (Option Ixon.AuxLayout × AuxTailRecs) × CompileM.BlockState)
    (compiled : CompileM.BlockResult × (CompileM.BlockState × Option Ixon.AuxLayout))
    : Except String Unit := do
  require (rows.size == 9 && i < 9 && !members.isEmpty) "case index/input coverage differs"
  require (exempt == (#[0,15,18,18,18,18,18,17,27] : Array Nat)[i]! &&
    observed.1.2.recs.size == (#[0,2,2,2,2,2,2,2,5] : Array Nat)[i]! &&
    observed.1.2.belowRecs.size == (#[0,2,2,2,2,2,2,2,0] : Array Nat)[i]!) s!"exemption/recursor coverage differs at {i}"
  let actual := Json.mkObj [("target", .str target), ("key", name key), ("members", names members), ("reason", .str reason),
    ("exempt", nat exempt), ("expected", arr [← tail observed.1.1 observed.1.2 observed.2,
      ← full compiled.1 compiled.2.1 compiled.2.2])]
  checkRow i rows[i]! actual
  if i == 0 || i == 1 then
    match checkRow i (← perturb i rows[i]!) actual with
    | .error e => require (e == s!"nine reference: complete row differs at {i}") "wrong perturbation failure"
    | .ok _ => throw "nine reference: raw layout/state perturbation escaped the same checker"

end Tests.Ix.AuxGen.NineReference
