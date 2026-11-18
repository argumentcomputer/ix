import Aiur.Tiling
import Aiur.Library.Field.BN254.Prime
import Aiur.Tiling.Ixa

/-!
# Narrow v2 layout export

Runs the verified v2 tiling pass and writes the layout
`narrow_heap_sound_compact` (or `_stacked`) is about (format
`ix-tiling-v2-layout-1`). The input is either

* `ix-tiling-v2-input-2`: the configuration only (width, shards, the chips to
  lay out with their capacities, ROM capacities, entry) and the path of the
  compiled artifact. The circuits are `Ixa.IChip.lower` of the artifact's
  chips (`Bridge.lower`, by `IChip.lower_ofChip`), the map claims are the
  artifact's, the request is the entry's, `checkEnables` runs on every
  laid-out chip, and `Package.checkIds` on the artifact's channels (`ids` and
  `idBound` of `Shaped`, by `Ixa.ids_ofChip`); or
* `ix-tiling-v2-input-1` (legacy): graphs, map claims and request supplied by
  the Rust v2 backend (`template/v2/lean.rs`).

The layout lists, per laid-out circuit, its wide lookup circuit as a graph
(`circuits`), the narrow shard circuits (`narrow_circuits`, `S.circuit k`) and
the compact table circuits (`compact_circuits`, `Compact.circuit`), so that a
consumer interprets these instead of building the expressions itself.

* the chip layout: every graph lowered by `lowerCircuit` (with the checked
  `compressUnroll` on the graph marked `"unroll"`), repeated over `shards`
  shards, accepted by `Sharded.check`;
* the stacked tables: one map table per called map, in input order, keyed by
  global ids after the chip shards' instances (map by map), and one ROM table
  per memory width with `capacity` rows keyed by the addresses `0..capacity`,
  each accepted by `Stacked.check` and `checkMap` or `checkRom`, on distinct
  channels;
* the entry request, accepted by `Part.checkRequest` and `checkRequest2`
  (the input's request has the entry's shape; those checks read only it);
* the fixed matrix of the chip layout, rows `0..places`: the bytes of
  `Sharded.emit`, which `Sharded.emit_eq` proves equal to `Sharded.fixedAt`.
  The instance-independent segments of a row are serialized once; the writer
  is compared with `emit` on instance 0 of every template row.

The export fails unless every check passes. It reports the closed-form size
bounds of the theorem (`bound` is the largest of them plus one).

`Sharded.check` and the table checks run as tasks beside the fixed-matrix
writer, whose blocks of instances are serialized in parallel and written in
order; the exit status is nonzero, and the layout file is not written, unless
every check accepts. The fixed path may be `/dev/stdout`, so that a consumer
reads the matrix from a pipe instead of a file.

Usage: `tiling_export2 input.json output.json (fixed.bin | /dev/stdout | -) [tables.bin]`.
The fixed file is in the `IXTLFX01` format of `TilingExport.lean`.

With `tables.bin`, the tables are the compact tables of
`narrow_heap_sound_compact` instead of the stacked ones: one map table
(`Compact.ofMaps`, keys `shards · Σ caps + row`) and one ROM table for every
word count (`Compact.ofRoms`), accepted by `checkTables`. Their fixed matrices
(`Compact.fixedRows`, equal to `Compact.fixedAt` by `fixedAt_offset`) are
written to `tables.bin`, map table first, each as an `IXTLFX01` block; the
layout lists them under `"compact"`.

Input 2 may add `"wide": [{"chip" | "chip_index", "cap"}…]`: chips laid out
as wide units beside the shards (`Periodic.mixed_heap_sound`, compact mode
only). Unit `t` is `IWideUnit ⟨chip, keyBase, cap⟩` with `keyBase` = the
narrow instance count plus the caps of units `< t`. A chip may not be both a
narrow circuit and a wide unit (a capacity-0 carrier included), nor two wide
units. A channel of a unit that
no laid-out template carries gets a carrier (`chooseCarriers`): a chip lowered
with capacity 0 and appended to `circuits`. The map claims, ROM widths and
`checkEnables` then cover the carriers and the units, `checkMixedI` must
accept, and the size bounds include `mixedLookups` and `mixedPartCount`. The
layout gains `wide_units` (per unit: `chip`, `chip_index`, `key_base`, `cap`,
`circuit` = `IWideUnit.circuit` as a graph whose fixed column 0 is the row id
`key_base + r`) and `mixed` (`rows`, `lookups`, `parts`, and `carriers`: the
carriers' positions in `circuits`). Without wide units neither field is
written.
-/

namespace Aiur.Tiling.TilingExport2

open Lean (Json)
open Aiur.Library.Field.BN254 (modulus modulus_prime)
open Aiur.Tiling.Periodic

instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

abbrev F := ZMod modulus

instance : Hashable F := ⟨fun x => hash x.val⟩

def toNat (x : F) : Nat := x.val

def parseTuple (j : Json) : Except String (List F) := do
  return (← (← j.getArr?).mapM (Export.parseField (F := F))).toList

def pushNat (out : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut len := 0
  let mut m := n
  while m != 0 do
    len := len + 1
    m := m / 256
  let mut out := out.push len.toUInt8
  let mut k := n
  while k != 0 do
    out := out.push (k % 256).toUInt8
    k := k / 256
  return out

def pushField (out : ByteArray) (x : F) : ByteArray := pushNat out (toNat x)

def bytesOf (xs : List F) : ByteArray := xs.foldl pushField ByteArray.empty

def pushU64 (out : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut out := out
  let mut n := n
  for _ in [0:8] do
    out := out.push (n % 256).toUInt8
    n := n / 256
  return out

def progress (msg : String) : IO Unit := do
  IO.eprintln s!"tiling_export2: {msg}"
  (← IO.getStderr).flush

/-- Chunks of `W − 2` of `n` columns. -/
def chunksOf (W n : Nat) (col : Nat → Nat) : List (List Nat) :=
  let per := W - 2
  (List.range ((n + per - 1) / per)).map fun c => (List.range' (c * per) (min per (n - c * per))).map col

/-- Slices of `n` payload columns `col 0, …, col (n-1)`: one slice if the
payload fits a row (with `head` before it), else chunks of `W − 2`. -/
def slicesOf (W n : Nat) (col : Nat → Nat) (head : List Nat) : List (List Nat) :=
  if head.length + n + 1 ≤ W then [head ++ (List.range n).map col] else chunksOf W n col

def mapTable (W : Nat) (tag sub : F) (rows : List (List F)) (keyBase : Nat) : Stacked F :=
  let n := (rows.headD []).length
  let T : Stacked F := {
    tag := tag
    sub := sub
    rows := rows.length
    keyBase := keyBase
    mainWidth := 1
    slices := []
    data := rows }
  { T with slices := slicesOf W n T.dataCol [] }

def romTable (W width cap : Nat) : Stacked F :=
  let T : Stacked F := {
    tag := 2
    sub := (width : F)
    rows := cap
    keyBase := 0
    mainWidth := 1 + width
    slices := [] }
  { T with slices := if width + 2 ≤ W then [T.keyCol :: (List.range width).map (1 + ·)]
      else chunksOf W width (1 + ·) }

def tableJson (T : Stacked F) : Json :=
  Json.mkObj [("tag", Export.field toNat T.tag), ("sub", Export.field toNat T.sub), ("rows", Json.num T.rows),
    ("key_base", Json.num T.keyBase), ("main_width", Json.num T.mainWidth),
    ("slices", Json.arr (T.slices.map fun sl => Json.arr (sl.map (Json.num ·)).toArray).toArray)]

/-- The per-row segments of one template row in the fixed file: the static
columns, the row-message columns, the key flag, the cells' slots and the
multiplicities. -/
abbrev RowParts := ByteArray × List F × Bool × Array (Option Nat) × ByteArray

/-- The fixed rows of instances `i0 … i1 − 1` of a template whose instance 0
has label base `kb` and id `idb`: the bytes of `Sharded.emit`. -/
def emitBlock (parts : Array RowParts) (slots kb idb i0 i1 size : Nat) : ByteArray := Id.run do
  let mut buf := ByteArray.emptyWithCapacity size
  for i in [i0:i1] do
    let lb := kb + i * slots
    let id : F := ((idb + i : Nat) : F)
    for (pre, rm, kf, cells, mults) in parts do
      buf := buf ++ pre
      for k in [0:5] do
        buf := pushField buf (if k = 3 then (if kf then id else 0) else rm.getD k 0)
      for c in cells do
        buf := match c with
          | some s => pushNat buf (lb + s + 1)
          | none => pushNat buf 0
      buf := buf ++ mults
  return buf

def templateJson (T : Template2 F) : Json :=
  (Export2.template toNat T).setObjVal! "slots" (Json.arr (T.slots.map (Export.slot toNat)).toArray)
    |>.setObjVal! "virtual" (Json.arr (T.virtual.map (Json.num ·)).toArray)

/-- A graph as JSON in the format of `Export.parseGraph`, with `fixed_width`:
variables `width … width + fixed_width − 1` are preprocessed columns. -/
def graphJson (fixedWidth : Nat) (g : Graph F) : Json :=
  let node : Node F → Json
    | .const v => Json.arr #["const", Export.field toNat v]
    | .var c => Json.arr #["var", Json.num c]
    | .add x y => Json.arr #["add", Json.num x, Json.num y]
    | .sub x y => Json.arr #["sub", Json.num x, Json.num y]
    | .neg x => Json.arr #["neg", Json.num x]
    | .mul x y => Json.arr #["mul", Json.num x, Json.num y]
  Json.mkObj [("width", Json.num g.width), ("fixed_width", Json.num fixedWidth),
    ("nodes", Json.arr (g.nodes.map node)),
    ("zeros", Json.arr (g.zeros.map (Json.num ·)).toArray),
    ("lookups", Json.arr (g.lookups.map fun (m, args) =>
      Json.arr #[Json.num m, Json.arr (args.map (Json.num ·)).toArray]).toArray)]

def circuitJson (C : Circuit F) : Json := graphJson C.fixedWidth (Graph.ofCircuit C)

/-- What the layout is built from, after reading either input format. -/
structure Source where
  W : Nat
  shards : Nat
  /-- Per laid-out circuit: the wide lookup circuit, its unrolling, the graph
  the lowering reads, and (for an artifact input) the chip's name and index. -/
  units : Array (Circuit F × Option (Unroll F) × Graph F × Option (String × Nat))
  caps : Array Nat
  tuples : Array (List F)
  roms : Array (Nat × Nat)
  request : List F
  /-- For an artifact input: the laid-out chips and the callable names. -/
  chips : Array (Ixa.IChip F) := #[]
  callables : Array String := #[]
  /-- For an artifact input: the decoded package and the chips laid out as
  wide units, with their row counts. -/
  pkg : Option (Ixa.Package F) := none
  wide : Array (Nat × Nat) := #[]
  /-- For an artifact input: the entry chip's name. -/
  entry : String := ""

def natField (j : Json) (k : String) : Except String Nat := do (← j.getObjVal? k).getNat?

/-- `ix-tiling-v2-input-1`: graphs and map claims supplied by the caller. -/
def readInput1 (j : Json) : IO Source := do
  let W ← IO.ofExcept (natField j "width")
  let shards ← IO.ofExcept (natField j "shards")
  let graphsJ ← IO.ofExcept do (← j.getObjVal? "graphs").getArr?
  let caps ← IO.ofExcept do (← (← j.getObjVal? "caps").getArr?).mapM (·.getNat?)
  let tuples ← IO.ofExcept do (← (← j.getObjVal? "tables").getArr?).mapM parseTuple
  let roms ← IO.ofExcept do (← (← j.getObjVal? "rom").getArr?).mapM fun e => do
    let a ← e.getArr?
    return (← a[0]!.getNat?, ← a[1]!.getNat?)
  let request ← IO.ofExcept (parseTuple (← IO.ofExcept (j.getObjVal? "request")))
  if caps.size != graphsJ.size then throw (IO.userError "one capacity per graph")
  let units ← graphsJ.mapM fun gj => do
    let g ← IO.ofExcept (Export.parseGraph (F := F) gj)
    let C := g.circuit
    let U ← match gj.getObjVal? "unroll" with
      | .ok fj => do pure (some (← IO.ofExcept (compressUnroll C (← IO.ofExcept fj.getNat?))))
      | .error _ => pure none
    return (C, U, g, none)
  return { W, shards, units, caps, tuples, roms, request }

/-- `ix-tiling-v2-input-2`: the configuration only. The circuits are
`Bridge.lower` of the chips of the compiled artifact (`Ixa.IChip.lower`,
equal to `Bridge.lower` by `IChip.lower_ofChip`), the map claims are the
artifact's maps called by those chips, and the request is the entry's. -/
def readInput2 (j : Json) (base : System.FilePath) : IO Source := do
  let W ← IO.ofExcept (natField j "width")
  let shards ← IO.ofExcept (natField j "shards")
  let path : System.FilePath := ← IO.ofExcept do (← j.getObjVal? "artifact").getStr?
  let path := if path.isAbsolute then path else base / path
  let pkg ← IO.ofExcept (Ixa.decodeChecked (F := F) modulus ZMod.val (← IO.FS.readBinFile path))
  progress s!"decoded {path}: {pkg.chips.size} chips, {pkg.callables.size} callables"
  let index : Std.HashMap String Nat := pkg.chips.zipIdx.foldl (fun m (x, i) => m.insert x.name i) {}
  let circuitsJ ← IO.ofExcept do (← j.getObjVal? "circuits").getArr?
  let resolve (cj : Json) : IO Nat :=
    match cj.getObjValAs? String "chip", cj.getObjValAs? Nat "chip_index" with
      | .ok name, _ => match index[name]? with
          | some i => pure i
          | none => throw (IO.userError s!"no chip {name} in the artifact")
      | .error _, .ok i =>
          if i < pkg.chips.size then pure i else throw (IO.userError s!"no chip {i} in the artifact")
      | .error _, .error _ => throw (IO.userError "a circuit names no chip")
  let mut units := #[]
  let mut caps := #[]
  for cj in circuitsJ do
    let i ← resolve cj
    let name := pkg.chips[i]!.name
    let cap ← IO.ofExcept (natField cj "cap")
    let unroll := (cj.getObjValAs? Bool "unroll").toOption.getD false
    let C := pkg.chips[i]!.lower pkg.idOf
    let U ← if unroll then pure (some (← IO.ofExcept (compressUnroll C (pkg.idOf name)))) else pure none
    units := units.push (C, U, Graph.ofCircuit C, some (name, i))
    caps := caps.push cap
  let laid := units.filterMap (·.2.2.2)
  let called : Std.HashSet String := laid.foldl (fun s (_, i) =>
    pkg.chips[i]!.sends.foldl (fun s x => s.insert x.channel) s) {}
  let tuples := (pkg.claims called.contains).toArray
  let roms ← IO.ofExcept do (← (← j.getObjVal? "rom").getArr?).mapM fun e => do
    let a ← e.getArr?
    return (← a[0]!.getNat?, ← a[1]!.getNat?)
  let widths : List Nat := (laid.toList.flatMap fun (_, i) => pkg.chips[i]!.memory.map (·.values.length)).dedup
  for w in widths do
    unless roms.any (·.1 == w) do throw (IO.userError s!"no ROM capacity for width {w}")
  let entry ← match j.getObjValAs? String "entry" with
    | .ok name => pure name
    | .error _ => match laid[0]? with
      | some (name, _) => pure name
      | none => throw (IO.userError "no circuits")
  let some e := index[entry]? | throw (IO.userError s!"no entry chip {entry}")
  let x := pkg.chips[e]!
  let request : List F := (Bridge.CALL : F) :: (pkg.idOf entry : F) ::
    List.replicate (x.inputs.length + x.output.length) 0
  let chips := laid.map fun (_, i) => pkg.chips[i]!
  let callables := pkg.callables
  let wideJ ← match j.getObjVal? "wide" with
    | .ok wj => IO.ofExcept wj.getArr?
    | .error _ => pure #[]
  let wide ← wideJ.mapM fun wj => do return (← resolve wj, ← IO.ofExcept (natField wj "cap"))
  return { W, shards, units, caps, tuples, roms, request, chips, callables, pkg := some pkg, wide, entry }

/-- The row keys `(tag, sub_row)` of the logical messages of `T`: those the
system's `arities` lists for it. -/
def messageKeys (T : Template2 F) : List (F × F) :=
  T.logical.messages.map fun (_, tag, sub, _) => (tag, sub)

/-- The channels `(tag, sub)` of a circuit's lookups, in order. -/
def lookupChannels (C : Circuit F) : List (F × F) :=
  C.lookups.filterMap fun L => match L.args with
    | .const t :: .const s :: _ => some (t, s)
    | _ => none

/-- The channels of the units' lookups with a row key outside `present`. -/
def missingChannels (idOf : String → Nat) (W : Nat) (present : Std.HashSet (F × F))
    (units : List (IWideUnit F)) : List (F × F) :=
  (units.flatMap fun u => (u.looks idOf).filterMap fun l =>
    if (l.rowKeysS W).all (present.contains ·.1) then none else some (l.tag, l.sub)).dedup

/-- Lookups (sends and memory) of the units' rows: `mixedLookups`. -/
def mixedLookupsI (units : List (IWideUnit F)) : Nat :=
  (units.map fun u => u.rows * (u.chip.sends.length + u.chip.memory.length)).sum

/-- Parts of the units' rows: `mixedPartCount`. -/
def mixedPartCountI (units : List (IWideUnit F)) : Nat :=
  (units.map fun u => u.rows * (1 + u.chip.sends.length + u.chip.memory.length)).sum

/-- Carriers for the channels the wide units use but no laid-out template
carries. `WLook.check` needs every row key of a wide lookup to have the
system's arity (and chunk role), which only a template's messages give, and
`mixed_heap_sound` needs every template to be `unitCircuit` of a chip of the
plan. So a carrier is a chip of the artifact, lowered like the laid-out ones
with capacity 0, that has a lookup on the channel. A chip laid out wide is
never a carrier, so every chip has one layout; its receive (lookup 0) must not
be a chunked receive of a wide unit, which would then have an in-system
receiver. Returns per carrier its chip index, wide circuit, lowered template
and merged circuit. -/
def chooseCarriers (W : Nat) (pkg : Ixa.Package F) (wideUnits : List (IWideUnit F))
    (wideIdx laidIdx : Std.HashSet Nat) (templates : List (Template2 F)) :
    Except String (Array (Nat × Circuit F × Template2 F × Circuit F)) := do
  let idOf := pkg.idOf
  let mut present : Std.HashSet (F × F) := templates.foldl (fun s T => (messageKeys T).foldl (·.insert ·) s) {}
  let chunkedRecv : Std.HashSet Nat := wideUnits.zip (List.range wideUnits.length) |>.foldl (init := {})
    fun s (u, _) => if ((u.receive idOf).chunkExprs W).isEmpty then s
      else match pkg.chips.findIdx? (·.name == u.chip.name) with
        | some i => s.insert i
        | none => s
  let n := pkg.chips.size
  let order := (List.range n).filter (!wideIdx.contains ·)
  let mut out := #[]
  for _ in [0:n + 1] do
    match missingChannels idOf W present wideUnits with
    | [] => return out
    | ch :: _ =>
      let mut found := none
      for i in order do
        if laidIdx.contains i || chunkedRecv.contains i || out.any (·.1 == i) then continue
        let C := pkg.chips[i]!.lower idOf
        let chs := lookupChannels C
        unless chs.contains ch do continue
        if let .ok (T, C', _) := lowerCircuit W C none then
          found := some (i, C, T, C')
          break
      let some (i, C, T, C') := found
        | throw s!"no chip can carry channel ({toNat ch.1}, {toNat ch.2}) of a wide unit"
      present := (messageKeys T).foldl (·.insert ·) present
      if (missingChannels idOf W present wideUnits).contains ch then
        throw s!"carrier {pkg.chips[i]!.name} does not carry the row keys of channel ({toNat ch.1}, {toNat ch.2})"
      out := out.push (i, C, T, C')
  throw "carrier selection did not terminate"

def main (args : List String) : IO UInt32 := do
  let (input, output, fixedPath, tablesPath) ← match args with
    | [a, b, c] => pure (a, b, c, none)
    | [a, b, c, d] => pure (a, b, c, some d)
    | _ => do IO.eprintln "usage: tiling_export2 input.json output.json (fixed.bin | -) [tables.bin]"; return 2
  let t0 ← IO.monoMsNow
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile input))
  let fmt ← IO.ofExcept ((← IO.ofExcept (j.getObjVal? "format")).getStr?)
  let src ← match fmt with
    | "ix-tiling-v2-input-1" => readInput1 j
    | "ix-tiling-v2-input-2" => readInput2 j ((System.FilePath.mk input).parent.getD ".")
    | _ => do IO.eprintln s!"unexpected input format {fmt}"; return 1
  let { W, shards, units, caps, tuples, roms, request, chips, callables, pkg, wide, entry } := src
  let mut units := units
  let mut caps := caps
  let mut tuples := tuples
  let mut chips := chips
  let t1 ← IO.monoMsNow
  progress s!"read {units.size} circuits and {tuples.size} map rows in {t1 - t0} ms"
  let mut circuits : Array (Circuit F) := #[]
  let mut templates : Array (Template2 F) := #[]
  for ((C, U, g, _), k) in units.toList.zipIdx do
    match lowerCircuit W C U g with
    | .ok (T, C', _) =>
        templates := templates.push T
        circuits := circuits.push C'
    | .error e => IO.eprintln s!"circuit {k}: {e}"; return 1
  -- Wide units: ids after the narrow ones, carriers for their channels.
  let mut wideUnits : List (IWideUnit F) := []
  let mut carrierAt : Array Nat := #[]
  if !wide.isEmpty then
    let some pkg := pkg | IO.eprintln "\"wide\" needs an artifact input"; return 1
    if tablesPath.isNone then IO.eprintln "\"wide\" needs the compact tables (tables.bin)"; return 1
    let narrowIds := shards * caps.toList.sum
    let mut kb := narrowIds
    for (i, cap) in wide do
      wideUnits := wideUnits ++ [⟨pkg.chips[i]!, kb, cap⟩]
      kb := kb + cap
    let wideIdx : Std.HashSet Nat := wide.foldl (fun s (i, _) => s.insert i) {}
    let laidIdx : Std.HashSet Nat := units.foldl (fun s u => match u.2.2.2 with
      | some (_, i) => s.insert i
      | none => s) {}
    -- A chip is laid out once: narrow (in `circuits`) or wide, not both, and
    -- not twice as a wide unit.
    if let some (i, _) := wide.find? (laidIdx.contains ·.1) then
      IO.eprintln s!"chip {pkg.chips[i]!.name} is laid out both narrow and wide"; return 1
    unless wideIdx.size == wide.size do IO.eprintln "a chip is laid out twice as a wide unit"; return 1
    match chooseCarriers W pkg wideUnits wideIdx laidIdx templates.toList with
    | .error e => IO.eprintln e; return 1
    | .ok cs =>
      for (i, C, T, C') in cs do
        carrierAt := carrierAt.push units.size
        units := units.push (C, none, Graph.ofCircuit C, some (pkg.chips[i]!.name, i))
        caps := caps.push 0
        templates := templates.push T
        circuits := circuits.push C'
        chips := chips.push pkg.chips[i]!
      progress s!"{wideUnits.length} wide units ({(wideUnits.map (·.rows)).sum} rows), carriers {cs.toList.map fun c => pkg.chips[c.1]!.name}"
    -- Map claims and ROM widths of every laid-out chip and wide unit.
    let used := chips.toList ++ wideUnits.map (·.chip)
    let called : Std.HashSet String := used.foldl (fun s x => x.sends.foldl (fun s y => s.insert y.channel) s) {}
    tuples := (pkg.claims called.contains).toArray
    for w in (used.flatMap fun x => x.memory.map (·.values.length)).dedup do
      unless roms.any (·.1 == w) do IO.eprintln s!"no ROM capacity for width {w}"; return 1
    chips := chips ++ (wideUnits.map (·.chip)).toArray
  let t2 ← IO.monoMsNow
  progress s!"lowered in {t2 - t1} ms"
  let L : Periodic.Layout F := ⟨circuits.toList, templates.toList, caps.toList⟩
  let S : Sharded F := {
    width := W
    shards := List.replicate shards L
    buses := busesOf toNat templates.toList }
  let checked := Task.spawn (prio := .dedicated) fun _ => S.check
  let t3 ← IO.monoMsNow
  let part := Part.request W request
  unless part.checkRequest S.system request && S.checkRequest2 part do
    IO.eprintln "the entry request is rejected"; return 1
  -- Map tables: consecutive rows of one channel.
  let mut tables : Array (Stacked F) := #[]
  let mut group : Array (List F) := #[]
  let mut key : Option (F × F) := none
  let mut mapBase := shards * caps.toList.sum
  for t in tuples.toList ++ [[]] do
    let k := match t with
      | tag :: sub :: _ => some (tag, sub)
      | _ => none
    if k != key || t.isEmpty then
      if let some (tag, sub) := key then
        tables := tables.push (mapTable W tag sub group.toList mapBase)
        mapBase := mapBase + group.size
      group := #[]
      key := k
    unless t.isEmpty do group := group.push (t.drop 2)
  for (width, cap) in roms do
    tables := tables.push (romTable W width cap)
  -- The compact tables and their check exist only in compact mode: a spawned
  -- task keeps the process alive until it finishes, even if nothing reads it.
  let compact : List (Compact F) := if tablesPath.isNone then [] else
    [Compact.ofMaps W tuples.toList (shards * caps.toList.sum), Compact.ofRoms W roms.toList]
  let compactChecked : Task Bool := if tablesPath.isNone then .pure true else
    Task.spawn (prio := .dedicated) fun _ => Periodic.checkTables S toNat compact
  if tablesPath.isSome then tables := #[]
  -- `wideOk` of `mixed_heap_sound` (`checkMixedI_ofUnit`).
  let wideFinal := wideUnits
  let mixedChecked : Task Bool := if wideUnits.isEmpty then .pure true else
    Task.spawn (prio := .dedicated) fun _ =>
      checkMixedI S ((pkg.map (·.idOf)).getD fun _ => 0) toNat compact wideFinal
  let tablesFinal := tables
  let tablesChecked := Task.spawn (prio := .dedicated) fun _ =>
    ((tablesFinal.toList.filter fun T => !(T.check S && (T.checkMap || T.checkRom))).map
      (fun T => (toNat T.tag, toNat T.sub)),
    decide (tablesFinal.toList.map fun T => (T.tag, T.sub)).Nodup)
  let t4 ← IO.monoMsNow
  -- Closed-form sizes of one chip layout.
  let ts := templates.toList
  let keysPer := ((ts.zip caps.toList).map fun (T, c) => c * T.slots.length).sum
  let places := ((ts.zip caps.toList).map fun (T, c) => c * T.rows.length).sum
  let idsPer := caps.toList.sum
  let lookupParts := shards * ((circuits.toList.zip caps.toList).map fun (C, c) => c * C.lookups.length).sum
  let tableRows := if tablesPath.isSome then (compact.map (·.parts.length)).sum
    else (tables.toList.map (·.rows)).sum
  let fw := (fixedRow W (fun _ _ => (0 : F)) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ => 0)).length
  let bounds : List (String × Nat) := [
    ("codes", (S.buses.map (·.2.1)).foldl max 0 + 1),
    ("labels", copyKey (shards * (keysPer + 1)) + 1),
    ("shadow", keysPer + 1 + places * W),
    ("instances", shards * idsPer),
    ("keys", (tables.toList.map fun T => T.keyBase + T.rows).foldl max 0),
    ("parts", lookupParts + 1 + tableRows + 1 + mixedPartCountI wideUnits),
    ("lookups", lookupParts + 16 * shards * idsPer + 1 + mixedLookupsI wideUnits)]
  let bound := (bounds.map (·.2)).foldl max 0 + 1
  let capacityRows := ((units.toList.zip caps.toList).map fun ((_, U, _), c) =>
    c * (U.map (·.bodies.length)).getD 1).sum + (wideUnits.map (·.rows)).sum
  unless capacityRows ≤ 2 ^ 39 do IO.eprintln s!"{capacityRows} chip rows exceed 2^39"; return 1
  -- From an artifact: `enablesOk` (`IChip.checkEnables_ofChip`) for every
  -- laid-out chip, and distinct callable names, so `idOf` is injective.
  if let some x := chips.find? (!·.checkEnables bound) then
    IO.eprintln s!"checkEnables rejects {x.name}"; return 1
  unless decide callables.toList.Nodup do IO.eprintln "two callables share a name"; return 1
  -- `ids`/`idBound` of `Shaped` (`Ixa.ids_ofChip`): every channel of every
  -- chip of the artifact, its maps and the entry is a callable, and there are
  -- at most `bound` callables.
  if let some pkg := pkg then
    unless pkg.checkIds bound entry do
      IO.eprintln "a channel is not a callable, or there are more callables than the bound"; return 1
    -- `claimsIn` (`Compiled.claimsIn_of_maps`): the range maps of the depth
    -- limbs are package maps; `entryPlain` (`Ixa.recursive_of_column`).
    unless pkg.checkRanges do IO.eprintln "a depth range map is not a package map"; return 1
    unless pkg.checkEntryPlain entry do IO.eprintln s!"the entry {entry} is recursive or has no chip"; return 1
  -- The fixed matrix.
  let mut written := 0
  if fixedPath != "-" then
    let h ← IO.FS.Handle.mk fixedPath .write
    h.write (pushU64 (pushU64 "IXTLFX01".toUTF8 places) fw)
    let mut buf : ByteArray := ByteArray.empty
    let mut kb := 0
    let mut idb := 0
    let mut pending : Array (Task ByteArray) := #[]
    for (T, cap) in ts.zip caps.toList do
      let table := Sharded.multTable T
      -- Per row: the bytes of the instance-independent segments of `emit`.
      let mut parts : Array RowParts := #[]
      for (row, r) in T.rows.zipIdx do
        let cells := T.rowCells row
        unless cells.all (fun c => c.all (· < T.slots.length)) do
          IO.eprintln "a physical cell is outside the slots"; return 1
        let pre := S.staticCols T row
        let rm := (List.range 5).map (row.rowMsg T S.buses 0)
        let mults := (List.range W).map (Sharded.multOf T table r)
        let full := bytesOf (S.emit pre rm (row.keyFlag T) cells mults kb ((idb : Nat) : F))
        let cellsA := ((List.range W).map fun j => cells.getD j none).toArray
        let fast := Id.run do
          let mut out := bytesOf pre
          for k in [0:5] do
            out := pushField out (if k = 3 then (if row.keyFlag T then ((idb : Nat) : F) else 0) else rm.getD k 0)
          for c in cellsA do
            out := match c with
              | some s => pushNat out (kb + s + 1)
              | none => pushNat out 0
          return out ++ bytesOf mults
        unless fast.data == full.data do
          IO.eprintln "the byte writer differs from Sharded.emit"; return 1
        parts := parts.push (bytesOf pre, rm, row.keyFlag T, cellsA, bytesOf mults)
      -- Blocks of about 2^16 rows; at most 64 blocks are in flight.
      let rows := max 1 T.rows.length
      let per := max 1 ((1 <<< 16) / rows)
      let rowBytes := (parts.toList.map fun (pre, _, _, _, mults) => pre.size + mults.size + 6 * 5 + 6 * W).sum
      let mut i := 0
      while i < cap do
        let j := min cap (i + per)
        let (ps, sl, k0, d0, a, b) := (parts, T.slots.length, kb, idb, i, j)
        pending := pending.push (Task.spawn fun _ => emitBlock ps sl k0 d0 a b ((b - a) * rowBytes))
        written := written + (j - i) * T.rows.length
        if pending.size ≥ 64 then
          h.write pending[0]!.get
          pending := pending.extract 1 pending.size
        i := j
      kb := kb + cap * T.slots.length
      idb := idb + cap
    for t in pending do
      h.write t.get
    h.write buf
    h.flush
    if written != places then IO.eprintln s!"wrote {written} rows for {places} places"; return 1
  let t5 ← IO.monoMsNow
  progress s!"fixed matrix of {written} rows × {fw} columns in {t5 - t4} ms"
  unless checked.get do IO.eprintln "Sharded.check rejected the layout"; return 1
  let t6 ← IO.monoMsNow
  progress s!"Sharded.check accepted {t6 - t3} ms after it started"
  if let some path := tablesPath then
    let h ← IO.FS.Handle.mk path .write
    for T in compact do
      let fw := 3 + T.nFixed
      h.write (pushU64 (pushU64 "IXTLFX01".toUTF8 T.rows) fw)
      for q in T.parts do
        for c in List.range q.nrows do
          h.write (bytesOf ((List.range fw).map (Compact.rowFixed S.buses q c)))
    h.flush
    unless compactChecked.get do IO.eprintln "checkTables rejected the compact tables"; return 1
    progress s!"compact tables accepted: {compact.map (·.rows)} rows"
  let (rejected, distinct) := tablesChecked.get
  if let some (tag, sub) := rejected.head? then
    IO.eprintln s!"stacked table ({tag}, {sub}) rejected"; return 1
  unless distinct do IO.eprintln "two stacked tables share a channel"; return 1
  unless mixedChecked.get do IO.eprintln "checkMixedI rejected the wide units"; return 1
  unless wideUnits.isEmpty do progress s!"checkMixedI accepted {wideUnits.length} wide units"
  let t7 ← IO.monoMsNow
  progress s!"request and {tables.size} stacked tables accepted {t7 - t3} ms after the checks started"
  let requestRows : List (List F) :=
    if part.chunks.isEmpty then [S.encode2 part.tuple]
    else (List.range part.chunks.length).map fun c => S.encode2 (part.chunkTuple c)
  let out := Json.mkObj ([
    ("format", Json.str "ix-tiling-v2-layout-1"),
    ("width", Json.num W), ("shards", Json.num shards), ("caps", Lean.toJson caps),
    ("fixed_width", Json.num fw), ("places", Json.num places),
    ("labels_per_shard", Json.num (keysPer + 1 : Nat)), ("ids_per_shard", Json.num idsPer),
    ("templates", Json.arr (templates.map templateJson)),
    ("buses", Json.arr (S.buses.map fun ((tag, sub), code, lane) =>
      Json.arr #[Export.field toNat tag, Export.field toNat sub, Json.str (toString code), Json.bool lane]).toArray),
    ("request", Json.arr (requestRows.map fun t => Json.arr (t.map (Export.field toNat)).toArray).toArray),
    ("tables", Json.arr (tables.map tableJson)),
    ("compact", if tablesPath.isNone then Json.arr #[] else Json.arr (compact.toArray.map fun T =>
      Json.mkObj [("n_fixed", Json.num T.nFixed), ("main_width", Json.num (T.mainWidth W)),
        ("fixed_width", Json.num (T.nFixed + 3 : Nat)), ("rows", Json.num T.rows),
        ("parts", Json.num T.parts.length)])),
    ("circuits", Json.arr (units.map fun (C, U, _, info) => Json.mkObj ([
        ("wide", circuitJson C), ("unroll", Json.bool U.isSome)] ++
        match info with
        | some (name, i) => [("chip", Json.str name), ("chip_index", Json.num i)]
        | none => []))),
    ("narrow_circuits", Json.arr ((List.range shards).map fun k => circuitJson (S.circuit k)).toArray),
    ("compact_circuits", Json.arr (compact.toArray.map fun T => circuitJson (T.circuit W))),
    ("map_claims", Json.num tuples.size),
    ("bound", Json.num bound),
    ("bounds", Json.mkObj (bounds.map fun (k, v) => (k, Json.num v))),
    ("ms", Json.mkObj [("parse", Json.num (t1 - t0)), ("lower", Json.num (t2 - t1)),
      ("check", Json.num (t6 - t3)), ("tables", Json.num (t7 - t3)), ("fixed", Json.num (t5 - t4)),
      ("total", Json.num (t7 - t0))])] ++
    if wideUnits.isEmpty then [] else
      let idOf := (pkg.map (·.idOf)).getD fun _ => 0
      [("wide_units", Json.arr (wideUnits.toArray.zip wide |>.map fun (u, (i, _)) => Json.mkObj [
          ("chip", Json.str u.chip.name), ("chip_index", Json.num i), ("key_base", Json.num u.keyBase),
          ("cap", Json.num u.rows), ("circuit", circuitJson (u.circuit idOf S.buses W))])),
        ("mixed", Json.mkObj [("rows", Json.num ((wideUnits.map (·.rows)).sum : Nat)),
          ("lookups", Json.num (mixedLookupsI wideUnits)), ("parts", Json.num (mixedPartCountI wideUnits)),
          ("carriers", Json.arr (carrierAt.map fun (c : Nat) => Json.num c))])])
  IO.FS.writeFile output out.compress
  progress s!"total {t7 - t0} ms"
  return 0

end Aiur.Tiling.TilingExport2
