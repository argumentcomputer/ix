import Ix.IxVM.RecordSections

/-!
# The two binder-data annotators agree byte for byte

Two routes write a record's binder-data section: the compiler's inline
annotator, the Ix kernel's annotation pass over each declaration installed from
its source, for every compiled record; and IxC's annotation pass over the Ixon record (`IxVM.RecordSections`),
for the records no Lean source annotates (model records, closed evidence
theorems, ad hoc definitions, hand-built test records). A difference between
them gives one constant two addresses depending on the tool, so they must write
the same section bytes for the same record.

`binder-data-annotators` (manual) checks a compiled artifact (`IX_BD_IXE`): every
record's section recomputed by IxC's pass, the record re-encoded with it, must be
byte-identical to the stored record. A record that differs is counted as a data
difference (the data of its binders, read in pre-order through its shares, differ)
or an encoding difference (the data agree, the section's spelling does not: variant
numbering, block order), and the first few are named. The pass's statistics are
printed (among them the constants of records the kernel did not install that are left
out, a root of theirs undecided). With `IX_BD_DUMP`, the address each record with
expressions has under the recomputed section is written there, one line per record
in address order, so that two runs' sections can be compared.
-/

namespace Tests.Ix.IxVM.BinderAnnotators

open IxVM.PwHints

abbrev Key := Bool × UInt64 × UInt64

/-- The next node of a block. -/
def next : StateT (List Ixon.BinderNode) (Except String) Ixon.BinderNode := do
  match ← get with
  | x :: xs => set xs; return x
  | [] => throw "a block ends early"

/-- The data of `e`'s binders in pre-order, each binderful share replaced by its
entry's data at the variant its node names; `next` takes the next node of the
expression's block. -/
partial def expand (c : Ixon.Constant) (full : Array Bool) (blocks : Std.HashMap Key (Array Ixon.BinderNode)) :
    Ixon.Expr → StateT (List Ixon.BinderNode) (Except String) (Array Ixon.BinderNode)
  | .lam t b => do
    let n ← next
    if let .share _ := n then throw "a share node at a binder"
    return #[n] ++ (← expand c full blocks t) ++ (← expand c full blocks b)
  | .all t b => do
    let n ← next
    if let .share _ := n then throw "a share node at a binder"
    return #[n] ++ (← expand c full blocks t) ++ (← expand c full blocks b)
  | .app f a => return (← expand c full blocks f) ++ (← expand c full blocks a)
  | .letE _ _ t v b =>
    return (← expand c full blocks t) ++ (← expand c full blocks v) ++ (← expand c full blocks b)
  | .prj _ _ v => expand c full blocks v
  | .share n => do
    unless full[n.toNat]?.getD false do return #[]
    match ← next with
    | .share v =>
      let some nodes := blocks[(true, n, v)]? | throw s!"no block for entry {n} variant {v}"
      let some entry := c.sharing[n.toNat]? | throw s!"no sharing entry {n}"
      let (out, rest) ← (expand c full blocks entry).run nodes.toList
      unless rest.isEmpty do throw s!"entry {n} variant {v}: nodes left over"
      return out
    | _ => throw "a binder node at a share"
  | _ => return #[]

/-- Every root's data, expanded through the shares. -/
def dataOf (c : Ixon.Constant) (binders : Array Ixon.BinderBlock) :
    Except String (Array (Array Ixon.BinderNode)) := do
  let full := binderful c.sharing
  let blocks : Std.HashMap Key (Array Ixon.BinderNode) :=
    binders.foldl (fun m b => m.insert (b.shared, b.index, b.variant) b.nodes) {}
  let mut out := #[]
  for (e, r) in (roots c).zipIdx do
    let nodes := (blocks[(false, r.toUInt64, (0 : UInt64))]?).getD #[]
    let (data, rest) ← (expand c full blocks e).run nodes.toList
    unless rest.isEmpty do throw s!"root {r}: nodes left over"
    out := out.push data
  return out

def run : IO UInt32 := do
  let some ixe ← IO.getEnv "IX_BD_IXE" | do IO.eprintln "IX_BD_IXE is not set"; return 1
  let env ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile ixe))
  let records ← IO.ofExcept (Ix.Compile.BinderData.recordsOf env)
  let t0 ← IO.monoMsNow
  let chosen ← IO.ofExcept (IxVM.RecordSections.chosenOf env)
  let (sections, stats) ← IO.ofExcept
    (IxVM.RecordSections.sectionsOfWithStats records #[] env.blobs env.anonHints chosen)
  IO.println s!"BDANN {records.size} records; IxC's pass in {(← IO.monoMsNow) - t0} ms"
  IO.println s!"BDANN pass: {stats.render}"
  if let some dump ← IO.getEnv "IX_BD_DUMP" then
    let lines := (records.filter fun (_, c) => !(roots c).isEmpty).qsort
        (fun x y => x.1.cmpBytes y.1 == .lt)
      |>.map fun (a, c) =>
        s!"{a} {Address.blake3 (Ixon.serConstant { c with binders := sections.getD a #[] })}\n"
    IO.FS.writeFile dump (String.join lines.toList)
  let mut compared := 0
  let mut dataDiffer : Array Address := #[]
  let mut bytesDiffer : Array Address := #[]
  for (a, c) in records do
    if (roots c).isEmpty then continue
    compared := compared + 1
    let recomputed := sections.getD a #[]
    let stored := (env.consts[a]?.map (·.rawBytes)).getD (Ixon.serConstant c)
    if Ixon.serConstant { c with binders := recomputed } == stored then continue
    match dataOf c c.binders, dataOf c recomputed with
    | .ok x, .ok y => if x == y then bytesDiffer := bytesDiffer.push a else dataDiffer := dataDiffer.push a
    | _, _ => dataDiffer := dataDiffer.push a
  IO.println s!"BDANN {compared} records with expressions compared: {dataDiffer.size} differ in data, \
    {bytesDiffer.size} agree in data but differ in bytes"
  let wanted : Std.HashSet Address := (dataDiffer.extract 0 10 ++ bytesDiffer.extract 0 10).foldl (·.insert ·) {}
  let names := Ix.Compile.BinderData.namesOf env wanted
  for (what, xs) in [("data", dataDiffer), ("bytes", bytesDiffer)] do
    for a in xs.extract 0 10 do
      let some c := (records.find? (·.1 == a)).map (·.2) | continue
      IO.println s!"BDANN differs in {what}: {names.getD a "?"} ({a})"
      IO.println s!"  stored     {repr c.binders}"
      IO.println s!"  recomputed {repr (sections.getD a #[])}"
  return (if dataDiffer.isEmpty && bytesDiffer.isEmpty then 0 else 1)

end Tests.Ix.IxVM.BinderAnnotators
