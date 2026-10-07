/-
  The Rust whole-unit pack against the Lean one (M6R slice 5; design document
  §6.3, the logical unit; `Ix.Cli.PackCmd`).

  `ix pack` completes logical units in Lean (`packWholeUnits`: the unit view
  `ixonUnitView`, read from the compiled environment's names and metadata,
  and one Rust value-closure pack per missing member, merged to a fixpoint).
  The Rust side has its own port of the unit view (`ixon::unit::IxonUnitView`)
  and completes the units inside one prune (`Ixon.rsPackEnvUnits`, `ix pack
  --rust-units`). Lean's output is the reference. On a compiled environment
  (a `.ixe` path):

  1. **unit view**: the Rust view's tables (every name's auxiliary owner, the
     roots of every owner's unit in order, every unit key's auxiliaries) equal
     the Lean view's (`Ixon.rsIxonUnitView` against `ixonUnitView`), so every
     name has the same unit (`members`) on both sides; a table that compared
     nothing fails;
  2. **Rust pack, every root**: the Rust whole-unit bundle of every root is
     written (closed: `validate_closed`) and is whole under the *Lean* view:
     no member of the unit of a carried name is missing
     (`Ix.Cli.PackCmd.missingUnitMembers`, the check `packWholeUnits` loops on);
  3. **Rust pack against Lean**: for the roots compared with `packWholeUnits`,
     the Rust bundle's file is byte-identical to the Lean bundle's, and the
     completion took the same number of rounds.

  The roots: one per unit that holds a name with a Pass 3 reserved component
  (`Lean.unitReservedComponent`: the clique hook's `x._ix.*`, `c._ix`,
  `p._ix_retyped.s`, `f._ix.fg`, `T.noConfusion{,Type}._ix`, the `_ix` display
  names of a changed block's auxiliaries), that name itself as the bundle's
  root (its unit brings its Lean declaration and the declaration's other
  auxiliaries), and the roots the caller adds. Check 3 compares all of them
  when there are at most `maxLean` (default 10), and otherwise the caller's
  roots and a cover of the reserved-name shapes (`shapeOf`: `_ix._mutual`,
  `_ix.rec_`, `_ix_retyped._f`, `noConfusionType._ix`, `_ix`, …): per shape
  not yet covered, the root with the smallest Rust bundle, then the smallest
  remaining, up to `maxLean`. The bound exists because the Lean completion
  runs one Rust pack of the whole source per member (M1-h's cost): one root
  of the twins unit takes 152 s there (410 member packs of a 22 MB source)
  and 1 s in Rust. Checks 1 and 2 are exhaustive.
-/
import Ix.Cli.PackCmd

namespace Tests.Ix.Compile.PackParity

open Ix.Cli.PackCmd (ixToLeanName ixonUnitView packWholeUnits readIxe)

def say (s : String) : IO Unit := do
  IO.println s!"[pack-parity] {s}"
  (← IO.getStdout).flush

/-- Does `n` have a Pass 3 reserved component? -/
def hasReserved (n : Lean.Name) : Bool :=
  n.components.any fun c => match c with
    | .str .anonymous s => Lean.unitReservedComponent s
    | _ => false

def sortNames (a : Array Lean.Name) : Array Lean.Name := a.qsort Lean.Name.lt

/-- The tables a unit view is compared by. -/
structure Tables where
  owners : Std.HashMap Lean.Name Lean.Name := {}
  roots : Std.HashMap Lean.Name (List Lean.Name) := {}
  index : Std.HashMap Lean.Name (Array Lean.Name) := {}

/-- The tables of the Lean view. -/
def leanTables (view : Lean.UnitView) (idx : Lean.UnitIndex) : Tables := Id.run do
  let mut t : Tables := {}
  for n in view.names () do
    let o? := view.auxOwner? n
    if let some o := o? then t := { t with owners := t.owners.insert n o }
    let o := o?.getD n
    unless t.roots.contains o do t := { t with roots := t.roots.insert o (view.roots o) }
  for (k, ms) in idx do t := { t with index := t.index.insert k (sortNames ms) }
  return t

/-- The tables of the Rust view of the env at `path`. -/
def rustTables (path : String) : IO Tables := do
  let (owners, roots, index) ← Ixon.rsIxonUnitView path
  let mut t : Tables := {}
  for (n, o) in owners do
    t := { t with owners := t.owners.insert (ixToLeanName n) (ixToLeanName o) }
  for (o, r) in roots do
    t := { t with roots := t.roots.insert (ixToLeanName o) (r.toList.map ixToLeanName) }
  for (k, ms) in index do
    t := { t with index := t.index.insert (ixToLeanName k) (sortNames (ms.map ixToLeanName)) }
  return t

/-- The differences of two maps, both directions, as messages. -/
def diffMap {α : Type} [BEq α] (what : String) (lean rust : Std.HashMap Lean.Name α)
    (fmt : α → String) : Array String := Id.run do
  let mut out : Array String := #[]
  for (k, a) in lean do
    match rust.get? k with
    | some b => unless a == b do out := out.push s!"{what} {k}: Lean {fmt a} / Rust {fmt b}"
    | none => out := out.push s!"{what} {k}: Lean {fmt a} / Rust none"
  for (k, b) in rust do
    unless lean.contains k do out := out.push s!"{what} {k}: Lean none / Rust {fmt b}"
  return out

def diffTables (lean rust : Tables) : Array String :=
  diffMap "owner" lean.owners rust.owners toString ++
  diffMap "roots" lean.roots rust.roots toString ++
  diffMap "index" lean.index rust.index toString

/-- One root per unit that holds a name with a reserved component: the least
such name of the unit (by its string). -/
def ixRoots (view : Lean.UnitView) : Array Lean.Name := Id.run do
  let mut byKey : Std.HashMap Lean.Name Lean.Name := {}
  for n in view.names () do
    unless hasReserved n do continue
    let k := view.key ((view.auxOwner? n).getD n)
    match byKey.get? k with
    | some m => if n.toString < m.toString then byKey := byKey.insert k n
    | none => byKey := byKey.insert k n
  return (byKey.toArray.map (·.2)).qsort (·.toString < ·.toString)

/-- `s` without its trailing digits (`rec_2` ↦ `rec_`). -/
def stripDigits (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile Char.isDigit).reverse

/-- The shape of a reserved name: its first reserved component with the
component after it, digits dropped (`x._ix.rec_2` ↦ `_ix.rec_`,
`g._ix._mutual` ↦ `_ix._mutual`, `p._ix_retyped._f` ↦ `_ix_retyped._f`), or,
when the reserved component is last, with the auxiliary component before it
(`T.noConfusionType._ix` ↦ `noConfusionType._ix`; a proof-justified pass's
`c._ix` ↦ `_ix`). -/
def shapeOf (n : Lean.Name) : String := Id.run do
  let cs : Array String := n.components.toArray.map fun c => match c with
    | .str .anonymous s => s
    | .num .anonymous i => toString i
    | _ => ""
  let some i := cs.findIdx? Lean.unitReservedComponent | return ""
  let r := cs[i]!
  if let some nxt := cs[i + 1]? then return s!"{r}.{stripDigits nxt}"
  if i > 0 then
    let prev := cs[i - 1]!
    if [Lean.UnitOwnerKind.induct, .ctor, .defn].any (Lean.unitAuxComponent · prev) then
      return s!"{stripDigits prev}.{r}"
  return r

/-- The shapes of the reserved names of every unit, by unit key. -/
def unitShapes (view : Lean.UnitView) : Std.HashMap Lean.Name (Array String) := Id.run do
  let mut m : Std.HashMap Lean.Name (Array String) := {}
  for n in view.names () do
    unless hasReserved n do continue
    let k := view.key ((view.auxOwner? n).getD n)
    let sh := shapeOf n
    let cur := m.getD k #[]
    unless cur.contains sh do m := m.insert k (cur.push sh)
  return m

/-- How many elements of `a` are not in `b`. -/
def countOnly {α : Type} [BEq α] [Hashable α] (a b : Array α) : Nat :=
  let s : Std.HashSet α := b.foldl (·.insert ·) {}
  (a.filter (!s.contains ·)).size

/-- What two bundle files differ by (constants, names, blobs). -/
def describe (lean rust : Ixon.Env) : String :=
  let lc := lean.consts.toList.map (·.1) |>.toArray
  let rc := rust.consts.toList.map (·.1) |>.toArray
  let ln := lean.named.toList.map (·.1) |>.toArray
  let rn := rust.named.toList.map (·.1) |>.toArray
  let lnames := lean.names.toList.map (·.1) |>.toArray
  let rnames := rust.names.toList.map (·.1) |>.toArray
  let lb := lean.blobs.toList.map (·.1) |>.toArray
  let rb := rust.blobs.toList.map (·.1) |>.toArray
  s!"constants Lean-only {countOnly lc rc} / Rust-only {countOnly rc lc}; Named Lean-only {countOnly ln rn} / \
    Rust-only {countOnly rn ln}; names Lean-only {countOnly lnames rnames} / Rust-only {countOnly rnames lnames}; \
    blobs Lean-only {countOnly lb rb} / Rust-only {countOnly rb lb}; main {lean.main == rust.main}; \
    assumptions {lean.assumptions.size} / {rust.assumptions.size}"

/-- The roots of check 3: all candidates when there are at most `maxLean`,
else the caller's roots, a cover of the shapes (per uncovered shape, sorted,
the candidate with the smallest Rust bundle) and the smallest remaining, up
to `maxLean`. Candidates are `(root, Rust bundle size, shapes)`. -/
def leanRoots (cands : Array (Lean.Name × Nat × Array String)) (extra : Array Lean.Name)
    (maxLean : Nat) : Array Lean.Name × Nat × Nat := Id.run do
  let allShapes : Array String :=
    (cands.foldl (fun (s : Std.HashSet String) (_, _, sh) => sh.foldl (·.insert ·) s) {}).toArray.qsort (· < ·)
  if cands.size ≤ maxLean then return (cands.map (·.1), allShapes.size, allShapes.size)
  let bySize := cands.qsort fun a b => a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.1.toString < b.1.toString)
  let mut chosen : Array Lean.Name := extra.filter fun r => cands.any (·.1 == r)
  let mut covered : Std.HashSet String := {}
  for (r, _, sh) in cands do
    if chosen.contains r then covered := sh.foldl (·.insert ·) covered
  for shape in allShapes do
    if chosen.size ≥ maxLean then break
    if covered.contains shape then continue
    if let some (r, _, sh) := bySize.find? fun (_, _, sh) => sh.contains shape then
      chosen := chosen.push r
      covered := sh.foldl (·.insert ·) covered
  for (r, _, _) in bySize do
    if chosen.size ≥ maxLean then break
    unless chosen.contains r do chosen := chosen.push r
  return (chosen, (allShapes.filter covered.contains).size, allShapes.size)

/-- The unit view and pack legs on the compiled environment at `srcPath`
(roots: `ixRoots` and `extra`; `anon` packs the first compared root
anonymously too; `maxLean` bounds the roots compared with the Lean
completion). Returns the defects. -/
def run (label : String) (srcPath : String) (extra : Array Lean.Name := #[])
    (anon : Bool := false) (maxLean : Nat := 10) : IO (Array String) := do
  let src ← readIxe srcPath
  let view := ixonUnitView src
  let idx := view.index
  let mut errors : Array String := #[]
  -- 1. unit view
  let lt := leanTables view idx
  let rt ← rustTables srcPath
  let diffs := diffTables lt rt
  let reserved := (view.names ()).filter hasReserved
  say s!"{label}: unit view: {src.named.size} names, {lt.owners.size} with an owner \
    ({reserved.length} with a reserved component), {lt.roots.size} owners, {lt.index.size} unit keys; \
    Rust {rt.owners.size} / {rt.roots.size} / {rt.index.size}; {diffs.size} difference(s)"
  if lt.roots.isEmpty then errors := errors.push s!"{label}: the unit view compared nothing"
  for d in diffs.toList.take 10 do errors := errors.push s!"{label}: unit view: {d}"
  -- 2. the Rust pack of every root, whole under the Lean view
  let ixr := ixRoots view
  let all := ixr ++ extra.filter (!ixr.contains ·)
  let shapes := unitShapes view
  let dir ← IO.FS.createTempDir
  let mut cands : Array (Lean.Name × Nat × Array String) := #[]
  let mut rustOf : Std.HashMap Lean.Name (Nat × Nat × Nat) := {}
  let mut rustMs := 0
  for (r, i) in all.zipIdx do
    let rs := r.toString (escape := false)
    let out := dir / s!"rust{i}.ixe"
    let t0 ← IO.monoMsNow
    match ← (Ixon.rsPackEnvUnits srcPath rs #[] out.toString false false).toBaseIO with
    | .error e => errors := errors.push s!"{label}: Rust pack of {rs}: {e}"
    | .ok (rounds, members) =>
      rustMs := rustMs + ((← IO.monoMsNow) - t0)
      let b ← readIxe out.toString
      let gaps := Ix.Cli.PackCmd.missingUnitMembers src view idx b
      unless gaps.isEmpty do
        errors := errors.push s!"{label}: Rust pack of {rs}: {gaps.size} unit member(s) missing, \
          first {gaps.toList.take 3 |>.map (·.1)}"
      let size := (← IO.FS.readBinFile out).size
      rustOf := rustOf.insert r (size, rounds, members)
      cands := cands.push (r, size, shapes.getD (view.key ((view.auxOwner? r).getD r)) #[])
    IO.FS.removeFile out
  say s!"{label}: Rust packs: {rustOf.size}/{all.size} root(s) whole under the Lean view ({ixr.size} \
    unit(s) with Pass 3 names; {rustMs} ms)"
  -- 3. the Rust pack against the Lean completion
  let (roots, covered, nShapes) := leanRoots cands extra maxLean
  let mut same := 0
  let mut cases : Array (Lean.Name × Bool) := roots.map (·, false)
  if anon then if let some r := roots[0]? then cases := cases.push (r, true)
  for ((r, an), i) in cases.zipIdx do
    let rs := r.toString (escape := false)
    let leanOut := dir / s!"root{i}-lean.ixe"
    let rustOut := dir / s!"root{i}-rust.ixe"
    let t0 ← IO.monoMsNow
    let (lr, lp) ← packWholeUnits srcPath rs #[] leanOut.toString an false
    let t1 ← IO.monoMsNow
    let (rr, rp) ← Ixon.rsPackEnvUnits srcPath rs #[] rustOut.toString an false
    let t2 ← IO.monoMsNow
    let lb ← IO.FS.readBinFile leanOut
    let rb ← IO.FS.readBinFile rustOut
    let tag := if an then " (anon)" else ""
    if lb == rb && lr == rr then
      same := same + 1
      say s!"{label}: {rs}{tag}: BYTE-IDENTICAL, {lb.size} B; rounds {lr}; Lean {lp} member \
        bundle(s) merged ({t1 - t0} ms), Rust {rp} member(s) added ({t2 - t1} ms)"
    else
      let why := describe (← readIxe leanOut.toString) (← readIxe rustOut.toString)
      say s!"{label}: {rs}{tag}: DIFFERENT, Lean {lb.size} B / Rust {rb.size} B; rounds Lean {lr} / \
        Rust {rr}; {why}"
      errors := errors.push s!"{label}: pack of {rs}{tag}: Lean {lb.size} B, Rust {rb.size} B, \
        rounds {lr}/{rr}: {why}"
  IO.FS.removeDirAll dir
  say s!"{label}: packs against the Lean completion: {roots.size} root(s) of {all.size} ({covered}/{nShapes} \
    reserved-name shape(s) covered){if cases.size > roots.size then ", the first also anonymously" else ""}: \
    {same}/{cases.size} bundle(s) byte-identical"
  return errors

end Tests.Ix.Compile.PackParity
