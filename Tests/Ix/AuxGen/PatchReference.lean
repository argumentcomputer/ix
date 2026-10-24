import Ix.AuxGen.Types
import Tests.Ix.AuxGen.Reference.Patches
import Tests.Ix.AuxGen.PatchReferenceFields
import Lean

/-! Complete structural finite references for ExplicitKernel's four existing
outputs. The reviewed capture encoding is preserved; raw mdata refuses. -/

namespace Tests.Ix.AuxGen.PatchReference
open _root_.Ix _root_.Ix.AuxGen
open Lean (Json)

private def arr (xs : List Json) : Json := .arr xs.toArray
private def nat (n : Nat) : Json := .str (toString n)
private def address (a : Address) : Json := arr [.str (toString a), nat a.hash.size]
private def name : Name → Json
  | .anonymous h => arr [.str "anonymous", address h]
  | .str p s h => arr [.str "str", name p, .str s, address h]
  | .num p n h => arr [.str "num", name p, nat n, address h]
private def names (ns : Array Name) : Json := .arr (ns.map name)
private def level : Level → Json
  | .zero h => arr [.str "zero", address h]
  | .succ u h => arr [.str "succ", level u, address h]
  | .max u v h => arr [.str "max", level u, level v, address h]
  | .imax u v h => arr [.str "imax", level u, level v, address h]
  | .param n h => arr [.str "param", name n, address h]
  | .mvar n h => arr [.str "mvar", name n, address h]
private def binder : Lean.BinderInfo → Json
  | .default => .str "default" | .implicit => .str "implicit"
  | .strictImplicit => .str "strictImplicit" | .instImplicit => .str "instImplicit"
private def expr : Expr → Except String Json
  | .bvar i h => pure (arr [.str "bvar", nat i, address h])
  | .fvar n h => pure (arr [.str "fvar", name n, address h])
  | .mvar n h => pure (arr [.str "mvar", name n, address h])
  | .sort u h => pure (arr [.str "sort", level u, address h])
  | .const n us h => pure (arr [.str "const", name n, .arr (us.map level), address h])
  | .app f a h => do return arr [.str "app", ← expr f, ← expr a, address h]
  | .lam n t b bi h => do return arr [.str "lam", name n, ← expr t, ← expr b, binder bi, address h]
  | .forallE n t b bi h => do return arr [.str "forallE", name n, ← expr t, ← expr b, binder bi, address h]
  | .letE n t v b nd h => do return arr [.str "letE", name n, ← expr t, ← expr v, ← expr b, .bool nd, address h]
  | .lit (.natVal n) h => pure (arr [.str "lit.nat", nat n, address h])
  | .lit (.strVal s) h => pure (arr [.str "lit.string", .str s, address h])
  | .proj n i e h => do return arr [.str "proj", name n, nat i, ← expr e, address h]
  | .mdata .. => .error "four witness: raw Expr.mdata is outside this measured corpus"
private def constant (c : ConstantVal) : Except String Json := do
  return arr [.str "ConstantVal", name c.name, names c.levelParams, ← expr c.type]
private def recursor (r : RecursorVal) : Except String Json := do
  let rules ← r.rules.mapM fun rule => do return arr [name rule.ctor, nat rule.nfields, ← expr rule.rhs]
  return arr [.str "RecursorVal", ← constant r.cnst, names r.all, nat r.numParams, nat r.numIndices,
    nat r.numMotives, nat r.numMinors, .arr rules, .bool r.k, .bool r.isUnsafe]
private def recursors (rs : Array (Name × RecursorVal)) : Except String Json :=
  Json.arr <$> rs.mapM (fun (n, r) => do return arr [name n, ← recursor r])
private def definition (tag : String) (n : Name) (lps : Array Name) (ty value : Expr)
    (unsafeFlag : Bool) : Except String Json := do
  return arr [.str tag, name n, names lps, ← expr ty, ← expr value, .bool unsafeFlag]
private def patch : PatchedConstant → Except String Json
  | .recr r => do return arr [.str "recr", ← recursor r]
  | .recOnDef d => definition "recOnDef" d.name d.levelParams d.typ d.value d.isUnsafe
  | .casesOnDef d => definition "casesOnDef" d.name d.levelParams d.typ d.value d.isUnsafe
  | .belowDef d => definition "belowDef" d.name d.levelParams d.typ d.value d.isUnsafe
  | .belowIndc d => do
    let ctors ← d.ctors.mapM fun c => do return arr [name c.name, ← expr c.typ, nat c.nParams, nat c.nFields]
    return arr [.str "belowIndc", name d.name, names d.levelParams, nat d.nParams, nat d.nIndices,
      .bool d.isReflexive, .bool d.isUnsafe, ← expr d.typ, .arr ctors]
  | .brecOnDef d => do
    return arr [.str "brecOnDef", ← definition "definition" d.name d.levelParams d.typ d.value d.isUnsafe, .bool d.isProp]
private def optional (f : α → Json) : Option α → Json
  | none => arr [.str "none"] | some a => arr [.str "some", f a]
private def sorted (entries : Array (Name × α)) : Array (Name × α) :=
  entries.qsort (fun a b => Name.cmpRaw a.1 b.1 == .lt)
private def patches (p : AuxPatchesOutput) : Except String Json := do
  let entries ← (sorted p.patches.toArray).mapM fun (n, p) => do return arr [name n, ← patch p]
  return Json.mkObj [("patches", .arr entries), ("aliases", .arr ((sorted p.aliases.toArray).map fun (n, v) => arr [name n, name v])),
    ("perm", optional (fun xs => .arr (xs.map nat)) p.perm), ("evaporated", optional (fun xs => .arr (xs.map Json.bool)) p.evaporated),
    ("nCanonicalAux", nat p.nCanonicalAux), ("canonicalRecs", ← recursors p.canonicalRecs)]
private def familyInput (family : Array (InductiveVal × Array ConstructorVal)) : Except String Json := do
  let rows ← family.mapM fun (v, cs) => do
    let former := arr [.str "InductiveVal", ← constant v.cnst, nat v.numParams, nat v.numIndices, names v.all, names v.ctors,
      nat v.numNested, .bool v.isRec, .bool v.isUnsafe, .bool v.isReflexive]
    let ctors ← cs.mapM fun c => do
      return arr [.str "ConstructorVal", ← constant c.cnst, name c.induct, nat c.cidx, nat c.numParams, nat c.numFields, .bool c.isUnsafe]
    return arr [former, .arr ctors]
  return .arr rows
private def need (ok : Bool) (why : String) : Except String Unit :=
  unless ok do throw s!"patch reference: {why}"

-- These are encoding controls only; fabricated records never enter Source.
private def encodingControls : Except String Unit := do
  let a := Name.mkStr .mkAnon "same"
  let b := Name.str .mkAnon "same" Name.mkAnon.getHash
  let c := Name.str .mkAnon "other" a.getHash
  let order := sorted #[(b, ()), (a, ()), (c, ())]
  need (name a != name b && name a != name c &&
    Name.cmpRaw order[0]!.1 order[1]!.1 == .lt && Name.cmpRaw order[1]!.1 order[2]!.1 == .lt) "key/hash distinctions lost"
  let d : AuxDef := ⟨a, #[], Expr.mkSort Level.mkZero, Expr.mkSort Level.mkZero, false⟩
  need ((← patch (.recOnDef d)) != (← patch (.casesOnDef d))) "patch tags merged"
  match expr (.mdata #[] d.value d.value.getHash) with
  | .error e => need (e == "four witness: raw Expr.mdata is outside this measured corpus") "wrong mdata refusal"
  | .ok _ => throw "patch reference: mdata silently encoded or erased"

private def owners : Array Name := (#[`Tests.Ix.AuxGen.ExplicitKernel.Tree,
  `Tests.Ix.AuxGen.ExplicitKernel.Predicate, `Tests.Ix.Compile.Mutual.AlphaCollapse.A,
  `NestedSortUK.T] : Array Lean.Name).map Name.fromLeanName

def read : Except String (Array Json) := do
  encodingControls
  let document ← Json.parse Reference.Patches.json
  let rows ← (← document.getObjVal? "rows").getArr?
  need (rows.size == 4) "four-row coverage differs"
  let header := Json.mkObj [("schema", .str "m7-four-patch-expectations-v1"),
    ("parent", .str "a0fd7dc17a987f583346a15f2d0480483f861fd1"),
    ("witness-sha256", .str "b97c732c6240a791a37cf6bbf68e50b1a5d3135306ba8d05ef1dcb884436c9ef"),
    ("pairColumns", .arr #[.str "AuxPatchesOutput", .str "PropRecursors"]), ("count", nat 4), ("rows", .arr rows)]
  need (document == header) "schema/identity/count differs"
  for (row, i) in rows.zipIdx do
    need ((← row.getObjVal? "owner") == name owners[i]!) s!"owner/order differs at {i}"
  return rows

private def checkRow (i : Nat) (expected actual : Json) : Except String Unit :=
  need (expected == actual) s!"complete row differs at {i}"

/-- Alter an alias component without changing its stored hash, or a rule's
field count. The normal complete-row checker must see either change. -/
private def perturb (i : Nat) (expected : Json) : Except String Json := do
  let Json.arr #[out, prop] ← expected.getObjVal? "expected" | throw "patch reference: pair shape differs"
  let out ← if i == 2 then do
    let aliases ← (← out.getObjVal? "aliases").getArr?
    let some (Json.arr #[key, Json.arr #[Json.str "str", parent, Json.str component, hash]]) := aliases[0]?
      | throw "patch reference: alias perturbation fixture differs"
    let target := arr [.str "str", parent, .str (component ++ "_perturbed"), hash]
    pure (out.setObjVal! "aliases" (.arr (aliases.set! 0 (arr [key, target]))))
  else do
    let recs ← (← out.getObjVal? "canonicalRecs").getArr?
    let some (Json.arr #[key, Json.arr #[Json.str "RecursorVal", cnst, allNames, np, ni, nm, nmin, Json.arr rules, k, u]]) := recs[0]?
      | throw "patch reference: recursor perturbation fixture differs"
    let some (Json.arr #[ctor, Json.str fields, rhs]) := rules[0]?
      | throw "patch reference: rule perturbation fixture differs"
    let some count := fields.toNat? | throw "patch reference: rule count is not a natural"
    let changed := arr [.str "RecursorVal", cnst, allNames, np, ni, nm, nmin,
      .arr (rules.set! 0 (arr [ctor, nat (count + 1), rhs])), k, u]
    pure (out.setObjVal! "canonicalRecs" (.arr (recs.set! 0 (arr [key, changed]))))
  return expected.setObjVal! "expected" (arr [out, prop])

/-- Use already generated records: no extra compilation or generation pass.
The original live Tc comparisons remain in ExplicitKernel.evaluate. -/
def check (rows : Array Json) (i : Nat) (owner : Name) (classes : Array (Array Name))
    (originalAll : Array Name) (out : AuxPatchesOutput)
    (family : Array (InductiveVal × Array ConstructorVal))
    (propRecs : Array (Name × RecursorVal)) : Except String Unit := do
  need (rows.size == 4 && i < 4) "case index/coverage differs"
  need (Name.beqRaw owner owners[i]! && !classes.isEmpty && !originalAll.isEmpty) s!"owner/input differs at {i}"
  need (out.patches.size == (#[4, 3, 4, 2] : Array Nat)[i]! && out.aliases.size == (#[0, 0, 2, 0] : Array Nat)[i]! &&
    out.canonicalRecs.size == (#[1, 1, 1, 2] : Array Nat)[i]! && out.nCanonicalAux == (#[0, 0, 0, 1] : Array Nat)[i]! &&
    family.size == (#[0, 1, 0, 0] : Array Nat)[i]! && propRecs.size == (#[0, 1, 0, 0] : Array Nat)[i]!) s!"output counts differ at {i}"
  let actual := Json.mkObj [("owner", name owner), ("classes", .arr (classes.map names)), ("originalAll", names originalAll),
    ("sharedPropInput", ← familyInput family), ("expected", arr [← patches out, ← recursors propRecs])]
  checkRow i rows[i]! actual
  if i == 0 || i == 2 then
    match checkRow i (← perturb i rows[i]!) actual with
    | .error e => need (e == s!"patch reference: complete row differs at {i}") "wrong perturbation failure"
    | .ok _ => throw "patch reference: changed stored field escaped the same checker"

end Tests.Ix.AuxGen.PatchReference
