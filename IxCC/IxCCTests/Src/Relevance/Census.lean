import IxCCTests.Src.Support
import IxCC.Tools.Check

/-! The relevance census on `k1.ixe`: annotate (the kernel annotator,
`KernelFront.Kernel.annotateChecked`, through the loader) and check the runtime
closure of the five K1 roots, report each reached constant, and assert the
expected classifications. The constructor classes the `unbox?` assertions read
are the kernel annotator's (`KernelFront.ctorRel` over the accepted
environment). Constant names come from the untrusted, test-only
`src-names.tsv` (the same ix run as `src-tables.tsv`). -/

namespace IxCCTests.Src.Relevance.Census

open IxCC IxCC.Src IxCC.Src.Relevance IxCCTests.Src
open Lean (Json toJson)

def names : IO (List (String × IxCC.Ixon.Address)) := do
  let text ← IO.FS.readFile (fixtures / "src-names.tsv")
  let rows := (text.splitOn "\n").filter fun l => !l.isEmpty && !l.startsWith "#"
  rows.mapM fun row => do
    match row.splitOn "\t" with
    | [name, hex] =>
      match IxCC.Ixon.Address.fromString hex with
      | some a => pure (name, a)
      | none => throw (IO.userError s!"src-names.tsv: bad address for {name}")
    | _ => throw (IO.userError s!"src-names.tsv: bad row {row}")

/-- The kernel annotator's field classes of the constructors `cs`
(`KernelFront.ctorRel`, the function the annotator applies to every
constructor it reaches), over the loaded closure's accepted environment. -/
def kernelCtorRels (k : KernelFront.Kernel) (cs : Array CId) :
    Except String (Array (CId × CtorRel)) :=
  let core := KernelFront.coreOf k.fe
  let go : KernelFront.AM (Array (CId × CtorRel)) := cs.mapM fun c => do
    let some (.ctor cv np nf) := k.rd.info? c
      | throw s!"census: constant {c} is not a constructor in the kernel's reading"
    return (c, ← KernelFront.ctorRel { core, back := KernelFront.backOf cv.levelParams } np nf cv.type)
  (go.run {}).map (·.1)

def relName : Rel → String
  | .rel => "rel"
  | .proof .never => "rel"
  | .proof (.allZero []) => "proof"
  | .proof (.allZero ps) => s!"proof when {ps} are zero"
  | .type => "type"

/-- A deterministic JSON line per reached constant. -/
def report (l : Loaded) : Json :=
  let p := l.program
  Json.arr (l.checked.reached.toArray.map fun c =>
    let rel := l.checked.constRel? c
    Json.mkObj [("address", toJson (toString (p.addr c))),
      ("kind", toJson (((p.decl? c).map Decl.kindName).getD "?")),
      ("result", toJson ((rel.map (relName ·.result)).getD "-")),
      ("params", toJson ((rel.map fun r => r.params.map relName).getD [])),
      ("verdict", toJson "accepted")])

def run (a : Assert) (reportPath : Option System.FilePath) : IO (Array String) := do
  let l ← loadK1
  let p := l.program
  let named ← names
  let idOf := fun (n : String) => (named.find? (·.1 == n)).bind fun (_, addr) => p.lookup addr
  let need := fun (n : String) => do
    match idOf n with
    | some c => pure c
    | none => throw (IO.userError s!"census: {n} is not in k1.ixe")
  let mut out := #[]
  out := out.push s!"k1.ixe closure: {l.checked.reached.length} constants, {l.checked.keys.length} runtime terms"
  if let some path := reportPath then
    IO.FS.writeFile path ((report l).pretty ++ "\n")
    out := out.push s!"census report written to {path}"
  -- Recursor kinds.
  for n in ["Eq.rec", "HEq.rec", "And.rec", "Acc.rec", "True.rec"] do
    if let some c := idOf n then
      expect a (match p.table.recKindOf c with | some (.subsingleton ..) => true | _ => false)
        s!"census: {n} is subsingleton"
  for n in ["False.rec", "Empty.rec"] do
    if let some c := idOf n then
      expect a (p.table.recKindOf c == some .empty) s!"census: {n} is empty"
  -- Acc.intro's x is read from the index; Exists eliminates only into proofs.
  let accRec ← need "Acc.rec"
  expect a (p.table.recKindOf accRec == some (.subsingleton .always [.index 0, .proof]))
    s!"census: Acc.rec reads x from its index ({repr (p.table.recKindOf accRec)})"
  if let some c := idOf "Exists.rec" then
    expect a (p.table.recKindOf c == some (.subsingleton .always [.proof, .proof]))
      s!"census: Exists.rec has only proof fields ({repr (p.table.recKindOf c)})"
  -- unbox? on the one-field structures, from their constructors' classes.
  let structs := ["Fin", "Subtype", "BitVec", "UInt64", "Char", "OfNat", "HAdd"]
  let ctorOf := fun (t : CId) => match p.decl? t with
    | some (.induct _ _ _ _ _ ctors) => ctors[0]?
    | _ => none
  let present := structs.filterMap fun n => (idOf n).map (n, ·)
  expect a (["Fin", "OfNat", "HAdd"].all fun n => present.any (·.1 == n))
    s!"census: structures present {present.map (·.1)}"
  out := out.push s!"unbox? checked on {present.map (·.1)}; absent from k1.ixe: {structs.filter fun n => !present.any (·.1 == n)}"
  let ctors := present.toArray.filterMap fun (_, t) => ctorOf t
  let rels ← IO.ofExcept (kernelCtorRels l.kernel ctors)
  let relOf := fun (k : CId) => (rels.find? (·.1 == k)).map (·.2)
  for (n, t) in present do
    let atType := (List.range (((p.decl? t).map Decl.lvls).getD 0)).map fun _ => false
    expect a ((unboxOf p relOf t atType).isSome) s!"census: {n} unboxes"
  -- Decidable has two constructors with no kept field.
  let dec ← need "Decidable"
  match p.decl? dec with
  | some (.induct _ _ _ _ _ dctors) =>
    expectEq a dctors.length 2 "census: Decidable has two constructors"
    let drels ← IO.ofExcept (kernelCtorRels l.kernel dctors.toArray)
    for (_, rel) in drels do
      expect a (!rel.fields.contains .keep) "census: Decidable constructors keep no field"
  | _ => expect a false "census: Decidable is not an inductive"
  return out

end IxCCTests.Src.Relevance.Census
