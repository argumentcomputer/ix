import IxCCTests.Src.Support
import IxCC.Tools.Check

/-! Pinned tables: `Src.Pinned` equals the
rows of `primitives.tsv` it transcribes and all of `src-tables.tsv`, and
every pinned address that `k1.ixe` contains is a declaration of the right
shape (each prim row passes its type check, each lazy row its λ count, and
the opaque-by-value row is a safe opaque). -/

namespace IxCCTests.Src.Pins

open IxCC IxCC.Src IxCCTests.Src

def rows (path : System.FilePath) : IO (Array (List String)) := do
  let text ← IO.FS.readFile path
  return (text.splitOn "\n").toArray.filterMap fun line =>
    if line.isEmpty || line.startsWith "#" then none else some (line.splitOn "\t")

def run (a : Assert) : IO Unit := do
  let prims ← rows (fixtures / "primitives.tsv")
  let lookup := fun (name : String) => (prims.find? (·.head? == some name)).bind (·[1]?)
  for (_, name, hex) in Pinned.primRows do
    expectEq a (lookup name) (some hex) s!"primitives.tsv row {name}"
  for (name, hex) in Pinned.constRows do
    expectEq a (lookup name) (some hex) s!"primitives.tsv row {name}"
  let tables ← rows (fixtures / "src-tables.tsv")
  let lazyRows := tables.filter (·.head? == some "lazy")
  expectEq a lazyRows.size Pinned.lazyRows.length "src-tables.tsv lazy row count"
  expectEq a lazyRows.size 30 "30 lazy rows (28 macro_inline, Bool.or, Bool.and)"
  for (row, (name, hex, arity)) in lazyRows.toList.zip Pinned.lazyRows do
    expect a (row == ["lazy", name, hex, toString arity]) s!"src-tables.tsv lazy row {name}: {row}"
  let obvRows := tables.filter (·.head? == some "opaque-by-value")
  expectEq a obvRows.size Pinned.opaqueByValueRows.length "src-tables.tsv opaque-by-value rows"
  for (row, (name, hex)) in obvRows.toList.zip Pinned.opaqueByValueRows do
    expect a (row == ["opaque-by-value", name, hex, "-"]) s!"src-tables.tsv row {name}: {row}"
  expectEq a tables.size (lazyRows.size + obvRows.size) "src-tables.tsv has no other rows"
  -- The provenance records the TSV's hash.
  let prov ← IxCC.Tools.Check.readJson (fixtures / "src-tables.provenance.json")
  let recorded ← IxCC.Tools.Check.strField prov "tsv_sha256"
  expectEq a recorded (← IxCC.Tools.Check.sha256 (fixtures / "src-tables.tsv"))
    "src-tables.provenance.json pins the TSV"
  -- Shapes on k1.ixe.
  let l ← loadK1
  let p := l.program
  for (op, name, hex) in Pinned.primRows do
    if let some c := p.lookup (Pinned.addr hex) then
      expect a ((Table.checkPrim p c op PrimOp.all) matches .ok ()) s!"k1.ixe: {name} has its primitive type"
  let mut lazyPresent := 0
  for (name, hex, arity) in Pinned.lazyRows do
    if let some c := p.lookup (Pinned.addr hex) then
      lazyPresent := lazyPresent + 1
      expect a ((Table.checkLazy p c arity) matches .ok ()) s!"k1.ixe: lazy {name} is a safe definition of arity {arity}"
  expect a (lazyPresent > 0) "k1.ixe contains lazy constants"
  -- The `Decidable ↦ Bool` alias: both pairs resolve, with
  -- matching constructor indices and one proof field on the Decidable side.
  let ctorIdx := fun (c : Option CId) => match c.bind p.decl? with
    | some (.ctor _ _ ind cidx np nf _) => some (ind, cidx, np, nf)
    | _ => none
  let k := p.known
  match ctorIdx k.decIsFalse, ctorIdx k.decIsTrue, ctorIdx k.boolFalse, ctorIdx k.boolTrue with
  | some (d, 0, 1, 1), some (d', 1, 1, 1), some (b, 0, 0, 0), some (b', 1, 0, 0) =>
    expect a (d == d' && b == b' && d != b) "k1.ixe: Decidable and Bool constructors pair up"
  | _, _, _, _ => expect a false "k1.ixe: Decidable.isFalse/isTrue and Bool.false/true resolve"
  for (name, hex) in Pinned.opaqueByValueRows do
    if let some c := p.lookup (Pinned.addr hex) then
      expect a (match p.decl? c with | some (.defn .opaq .safe ..) => true | _ => false)
        s!"k1.ixe: {name} is a safe opaque"
      expect a (p.table.isOpaqueByValue c) s!"k1.ixe: {name} is allowlisted"

end IxCCTests.Src.Pins
