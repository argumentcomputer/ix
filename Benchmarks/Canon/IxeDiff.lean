/-
  ixe-diff: which Lean names changed address between two compiled
  environments, grouped by the block they belong to, with a one-word
  cause where it can be inferred.

  ```
  ixe-diff <old.ixe> <new.ixe> [--names] [--tsv <rows.tsv>]
  ixe-diff --originals <file.ixe> [--names] [--tsv <rows.tsv>]
  ```

  Two-environment mode. The join and the per-field classification are
  `Ixon.rsDiffEnvFiles` (both files memory-mapped, anonymous structure
  only; the ripple verdict marks a row whose change is explained by
  re-addressed dependencies). Each changed name is then placed in a group
  and given a cause:

  * the group is the Muts block its old address projects into, else the
    block its new address projects into, else the name alone;
  * `cascade`: the constant itself is unchanged; only addresses it refers
    to moved (Rust's ripple verdict, which includes a block whose sibling
    moved);
  * `packaging`: the name moved between a projection and a standalone
    constant, or between blocks of different sizes;
  * `nested-order`: a projection into a block of the same size at another
    index (a permutation of the block);
  * `content`: anything else (the constant's own terms changed).

  Printed: totals per cause, one line per group (first member, size,
  counts per cause), added and removed names, and with `--names` every
  changed name. `--tsv` writes `name, group, cause, old kind, new kind`.

  `--originals` mode reads one environment and lists the names whose
  `Named.original` (the compile of Lean's own form of a regenerated
  auxiliary) has another address than `Named.addr`, grouped the same way
  (by the block of `addr`), with the cause `packaging` when the two are
  a projection and a standalone constant (or blocks of different sizes),
  `content` otherwise.

  Untrusted measurement tooling; it never writes an environment.
-/
import Ix.Ixon

namespace Benchmarks.Canon.IxeDiff

open Ixon

/-- The shape of a constant: standalone (with its kind) or a projection
    into a block of `size` members at `idx`. -/
inductive Shape where
  | standalone (kind : String)
  | proj (kind : String) (block : Address) (idx : UInt64) (size : Nat)
  | missing
  deriving Inhabited, BEq

def Shape.kind : Shape → String
  | .standalone k => k
  | .proj k .. => k
  | .missing => "missing"

def Shape.block? : Shape → Option Address
  | .proj _ b .. => some b
  | _ => none

/-- Constant windows of one file. -/
structure Slices where
  buf : ByteArray
  idx : Std.HashMap Address (Nat × Nat)

def Slices.load (path : String) : IO Slices := do
  let buf ← IO.FS.readBinFile path
  let raw ← IO.ofExcept (Ixon.rsDeEnvLazyFFI buf)
  let idx := raw.consts.foldl (init := {}) fun m s =>
    m.insert s.addr (s.offset.toNat, s.len.toNat)
  return { buf, idx }

def Slices.get? (s : Slices) (a : Address) : Option Constant :=
  match s.idx.get? a with
  | some (off, len) => (LazyConstant.ofSlice s.buf off len).get?
  | none => none

/-- The shape of the constant at `a`; block sizes are cached. -/
def shapeOf (s : Slices) (cache : IO.Ref (Std.HashMap Address Nat)) (a : Address) :
    IO Shape := do
  let some c := s.get? a | return .missing
  let blockSize (b : Address) : IO Nat := do
    if let some n := (← cache.get).get? b then return n
    let n := match s.get? b with
      | some { info := .muts ms, .. } => ms.size
      | _ => 0
    cache.modify (·.insert b n)
    return n
  match c.info with
  | .defn _ => return .standalone "defn"
  | .recr _ => return .standalone "recr"
  | .axio _ => return .standalone "axio"
  | .quot _ => return .standalone "quot"
  | .muts _ => return .standalone "muts"
  | .dPrj p => return .proj "dprj" p.block p.idx (← blockSize p.block)
  | .rPrj p => return .proj "rprj" p.block p.idx (← blockSize p.block)
  | .iPrj p => return .proj "iprj" p.block p.idx (← blockSize p.block)
  | .cPrj p => return .proj "cprj" p.block p.idx (← blockSize p.block)

/-- Packaging: a projection on one side and a standalone constant on the
    other, or projections into blocks of different sizes. -/
def isPackaging : Shape → Shape → Bool
  | .proj .., .standalone _ => true
  | .standalone _, .proj .. => true
  | .proj _ _ _ n, .proj _ _ _ m => n != m
  | _, _ => false

def isReorder : Shape → Shape → Bool
  | .proj _ _ i n, .proj _ _ j m => n == m && i != j
  | _, _ => false

structure Row where
  name : String
  group : String
  cause : String
  oldKind : String
  newKind : String
  deriving Inhabited

def groupKey (name : String) (a b : Shape) : String :=
  match a.block?, b.block? with
  | some x, _ => s!"old:{x}"
  | none, some y => s!"new:{y}"
  | none, none => s!"name:{name}"

def causes : List String := ["packaging", "nested-order", "cascade", "content"]

/-- Print the grouped report of `rows`. -/
def report (rows : Array Row) (names : Bool) : IO Unit := do
  let mut perCause : Std.HashMap String Nat := {}
  let mut groups : Std.HashMap String (Array Row) := {}
  for r in rows do
    perCause := perCause.insert r.cause (perCause.getD r.cause 0 + 1)
    groups := groups.insert r.group ((groups.getD r.group #[]).push r)
  IO.println <| s!"changed names: {rows.size}; " ++ ", ".intercalate
    (causes.map fun c => s!"{c} {perCause.getD c 0}")
  -- groups, labelled by their least member name, sorted by label
  let labelled := groups.toArray.map fun (_, rs) =>
    let sorted := rs.qsort (·.name < ·.name)
    (sorted[0]!.name, sorted)
  let labelled := labelled.qsort (·.1 < ·.1)
  let mut groupsPerCause : Std.HashMap String Nat := {}
  for (_, rs) in labelled do
    let main := causes.find? (fun c => rs.any (·.cause == c)) |>.getD "content"
    groupsPerCause := groupsPerCause.insert main (groupsPerCause.getD main 0 + 1)
  IO.println <| s!"groups: {labelled.size}; by leading cause: " ++ ", ".intercalate
    (causes.map fun c => s!"{c} {groupsPerCause.getD c 0}")
  for (label, rs) in labelled do
    let counts := causes.filterMap fun c =>
      let n := rs.foldl (fun k r => if r.cause == c then k + 1 else k) 0
      if n == 0 then none else some s!"{c} {n}"
    IO.println s!"  {label} ({rs.size}): {", ".intercalate counts}"
    if names then
      for r in rs do
        let kind := if r.oldKind == r.newKind then r.oldKind else s!"{r.oldKind}→{r.newKind}"
        IO.println s!"      {r.name}  {kind}  {r.cause}"

def writeTsv (path : String) (rows : Array Row) : IO Unit := do
  let lines := rows.map fun r => s!"{r.name}\t{r.group}\t{r.cause}\t{r.oldKind}\t{r.newKind}"
  IO.FS.writeFile path ("name\tgroup\tcause\told_kind\tnew_kind\n" ++ "\n".intercalate lines.toList ++ "\n")

def diffMode (oldPath newPath : String) (names : Bool) (tsv? : Option String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  if ← Ixon.rsIxeFilesEqual oldPath newPath then
    IO.println "identical"
    return 0
  let d ← Ixon.rsDiffEnvFiles oldPath newPath false
  IO.eprintln s!"[ixe-diff] diff: {d.namedChanged.size} changed, {d.namedAdded.size} added, \
    {d.namedRemoved.size} removed ({(← IO.monoMsNow) - t0} ms)"
  let sa ← Slices.load oldPath
  let sb ← Slices.load newPath
  let ca ← IO.mkRef ({} : Std.HashMap Address Nat)
  let cb ← IO.mkRef ({} : Std.HashMap Address Nat)
  let mut rows : Array Row := #[]
  for c in d.namedChanged do
    -- synthetic Muts names (`Ix.<block hash>.…`) never join as changed rows
    let a ← shapeOf sa ca c.oldAddr
    let b ← shapeOf sb cb c.newAddr
    let cause :=
      if c.rippled then "cascade"
      else if isPackaging a b then "packaging"
      else if isReorder a b then "nested-order"
      else "content"
    rows := rows.push { name := c.name, group := groupKey c.name a b, cause,
                        oldKind := a.kind, newKind := b.kind }
  IO.println s!"# ixe-diff {oldPath} → {newPath}"
  report rows names
  let isSyn (s : String) : Bool := s.startsWith "Ix." && ((s.drop 3).takeWhile (· != '.')).positions.length == 64
  let added := d.namedAdded.filter (!isSyn ·.1)
  let removed := d.namedRemoved.filter (!isSyn ·.1)
  IO.println s!"added names: {added.size}; removed names: {removed.size} \
    (synthetic block names: {d.namedAdded.size - added.size} added, \
    {d.namedRemoved.size - removed.size} removed)"
  if names then
    for (n, _) in added do IO.println s!"  + {n}"
    for (n, _) in removed do IO.println s!"  - {n}"
  if let some p := tsv? then writeTsv p rows
  IO.eprintln s!"[ixe-diff] done ({(← IO.monoMsNow) - t0} ms)"
  return if rows.isEmpty && added.isEmpty && removed.isEmpty then 0 else 1

def originalsMode (path : String) (names : Bool) (tsv? : Option String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let bytes ← IO.FS.readBinFile path
  let parts ← IO.ofExcept (Ixon.deEnvVerifiedLazy bytes)
  IO.eprintln s!"[ixe-diff] {path}: {parts.namedRows.size} named ({(← IO.monoMsNow) - t0} ms)"
  let consts := parts.env.consts
  let get? (a : Address) : Option Constant := (consts.get? a).bind (·.get?)
  let cache ← IO.mkRef ({} : Std.HashMap Address Nat)
  let shape (a : Address) : IO Shape := do
    let some c := get? a | return .missing
    let blockSize (b : Address) : IO Nat := do
      if let some n := (← cache.get).get? b then return n
      let n := match get? b with
        | some { info := .muts ms, .. } => ms.size
        | _ => 0
      cache.modify (·.insert b n)
      return n
    match c.info with
    | .dPrj p => return .proj "dprj" p.block p.idx (← blockSize p.block)
    | .rPrj p => return .proj "rprj" p.block p.idx (← blockSize p.block)
    | .iPrj p => return .proj "iprj" p.block p.idx (← blockSize p.block)
    | .cPrj p => return .proj "cprj" p.block p.idx (← blockSize p.block)
    | .defn _ => return .standalone "defn"
    | .recr _ => return .standalone "recr"
    | _ => return .standalone "other"
  let mut total := 0
  let mut rows : Array Row := #[]
  for row in parts.namedRows do
    let named ← IO.ofExcept (row.materialize parts.backing parts.nameRev)
    let some (orig, _) := named.original | continue
    total := total + 1
    if orig == named.addr then continue
    let a ← shape named.addr
    -- the original's bytes are never stored: its shape is unknown unless an
    -- identical constant happens to be stored
    let o ← shape orig
    let cause := if o == .missing then
        (match a with | .proj .. => "packaging" | _ => "content")
      else if isPackaging o a then "packaging" else "content"
    rows := rows.push { name := toString row.name, group := groupKey (toString row.name) .missing a,
                        cause, oldKind := o.kind, newKind := a.kind }
  IO.println s!"# ixe-diff --originals {path}"
  IO.println s!"names with Named.original: {total}; equal to Named.addr: {total - rows.size}; differ: {rows.size}"
  report rows names
  if let some p := tsv? then writeTsv p rows
  IO.eprintln s!"[ixe-diff] done ({(← IO.monoMsNow) - t0} ms)"
  return 0

def usage : String :=
  "usage: ixe-diff <old.ixe> <new.ixe> [--names] [--tsv <rows.tsv>]\n       ixe-diff --originals <file.ixe> [--names] [--tsv <rows.tsv>]"

def main (args : List String) : IO UInt32 := do
  let rec flags (acc : Bool × Option String) : List String → Option (Bool × Option String)
    | [] => some acc
    | "--names" :: rest => flags (true, acc.2) rest
    | "--tsv" :: p :: rest => flags (acc.1, some p) rest
    | _ => none
  match args with
  | "--originals" :: path :: rest =>
    let some (names, tsv?) := flags (false, none) rest | IO.eprintln usage; return 2
    originalsMode path names tsv?
  | a :: b :: rest =>
    let some (names, tsv?) := flags (false, none) rest | IO.eprintln usage; return 2
    diffMode a b names tsv?
  | _ => IO.eprintln usage; return 2

end Benchmarks.Canon.IxeDiff

def main (args : List String) : IO UInt32 := Benchmarks.Canon.IxeDiff.main args
