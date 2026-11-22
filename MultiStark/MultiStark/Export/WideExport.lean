import Aiur.Tiling
import Aiur.Tiling.Ixa
import Aiur.Tiling.WideStage
import Aiur.Tiling.WideIxa
import Aiur.Tiling.IxaTrace
import Aiur.Tiling.GroupedIxa
import Aiur.Library.Field.BN254.Prime
import Aiur.Library.U32.Goldilocks

/-!
# Wide stage export

Writes the circuits of a wide (untiled) stage that `WideStage.wide_heap_sound`
is about, from the compiled artifact alone:

* one unit table per laid-out chip: `Ixa.IChip.lower` of the artifact's chip
  (`Bridge.lower`, by `IChip.lower_ofChip`; `unitAir` with no unrolling), with
  exactly `cap` rows;
* the map tables `mapAirs` of the artifact's map claims called by those chips,
  one per claim length, each with `rows` = the next power of two of its claim
  count (`sel = 0` on the padding rows);
* the ROM tables `romAirs` of the input's `(words, capacity)` pairs, `rows` =
  capacity, fixed `addr` = the row index.

The artifact is read with `Ixa.decodeChecked`: its trace section must
re-encode to the file's bytes (`Ixa.checkTrace`). The export fails unless
`checkEnables` accepts every laid-out chip
(`IChip.checkEnables_ofChip`), the callable names are distinct, every memory
width of the chips has one ROM table, the ROM widths are distinct and each
capacity is at most `bound`.

Usage: `wide_export input.json layout.json fixed.bin`. Input
(`ix-wide-input-1`): `field` (`"bn254"` or `"goldilocks"`), `artifact`
(path, relative to the input's directory unless absolute), `circuits`
(`[{"chip": name | "chip_index": i, "cap": rows}]`), `rom` (`[[words, cap]]`)
and `entry` (a chip name; default the first circuit's); optional `all_maps` (keep the claims of every map), `pow2` (require power-of-two row counts) and `map_padding`: `"repeat"` writes the selector-free map tables `mapAirsD` of `wide_heap_sound_dup` (main `mult`, fixed cells only, lookup `push(−mult, cells)`, padding rows repeating the last claim), otherwise `mapAirs`. The tables are `WideIxa.stageOf`'s. Output
(`ix-wide-layout-1`): `tables`, in the order of `stageLedger`'s sum (units,
then map tables, then ROM tables), each with `kind`, `rows` and `circuit` (the
graph format of `TilingExport2.graphJson`, variables `width …` fixed); the
request tuple; `bound`. `fixed.bin` holds one `IXTLFX01` block per map and ROM
table, in table order (`mapFixed`, and the row index for ROM tables).
-/

namespace Aiur.Tiling.WideExport

open Lean (Json)
open Aiur.Tiling.WideStage

section

variable (p : Nat) [Fact (Nat.Prime p)]

local notation "Fp" => ZMod p

instance : Hashable (ZMod p) := ⟨fun x => hash x.val⟩

def field (x : ZMod p) : Json := Json.str (toString x.val)

def graphJson (fixedWidth : Nat) (g : Graph (ZMod p)) : Json :=
  let node : Node (ZMod p) → Json
    | .const v => Json.arr #["const", field p v]
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

def circuitJson (C : Circuit (ZMod p)) : Json := graphJson p C.fixedWidth (Graph.ofCircuit C)

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

def pushU64 (out : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut out := out
  let mut n := n
  for _ in [0:8] do
    out := out.push (n % 256).toUInt8
    n := n / 256
  return out

/-- An `IXTLFX01` block of `rows × width` values `f row column`. -/
def block (rows width : Nat) (f : Nat → Nat → ZMod p) : ByteArray := Id.run do
  let mut out := pushU64 (pushU64 "IXTLFX01".toUTF8 rows) width
  for i in [0:rows] do
    for k in [0:width] do
      out := pushNat out (f i k).val
  return out

def run (j : Json) (base output fixedPath : System.FilePath) : IO UInt32 := do
  let get (k : String) : IO Json := IO.ofExcept (j.getObjVal? k)
  let path : System.FilePath := ← IO.ofExcept (← get "artifact").getStr?
  let path := if path.isAbsolute then path else base / path
  let pkg ← IO.ofExcept (Ixa.decodeChecked (F := Fp) p ZMod.val (← IO.FS.readBinFile path))
  IO.eprintln s!"wide_export: decoded {path}: {pkg.chips.size} chips"
  let mut circuits : List (String × Nat) := []
  for cj in ← IO.ofExcept (← get "circuits").getArr? do
    let name ← match cj.getObjValAs? String "chip", cj.getObjValAs? Nat "chip_index" with
      | .ok name, _ => pure name
      | .error _, .ok i => match pkg.chips[i]? with
          | some x => pure x.name
          | none => throw (IO.userError s!"no chip {i} in the artifact")
      | .error _, .error _ => throw (IO.userError "a circuit names no chip")
    circuits := circuits ++ [(name, ← IO.ofExcept (cj.getObjValAs? Nat "cap"))]
  let rom ← IO.ofExcept do (← (← j.getObjVal? "rom").getArr?).toList.mapM fun e => do
    let a ← e.getArr?
    return ((← a[0]!.getNat?, ← a[1]!.getNat?) : Nat × Nat)
  let entry := (j.getObjValAs? String "entry").toOption
  let allMaps := (j.getObjValAs? Bool "all_maps").toOption.getD false
  let pow2 := (j.getObjValAs? Bool "pow2").toOption.getD false
  let mut groups : List (String × Nat) := []
  for gj in (j.getObjValAs? (Array Json) "groups").toOption.getD #[] do
    let name ← match gj.getObjValAs? String "group", gj.getObjValAs? Nat "group_index" with
      | .ok name, _ => pure name
      | .error _, .ok i => match pkg.trace.groups[i]? with
          | some g => pure g.name
          | none => throw (IO.userError s!"no group {i} in the artifact")
      | .error _, .error _ => throw (IO.userError "a group entry names no group")
    groups := groups ++ [(name, ← IO.ofExcept (gj.getObjValAs? Nat "cap"))]
  let cfg : WideIxa.Config := { circuits, rom, entry, allMaps, pow2, groups }
  let st ← match WideIxa.stageOf pkg cfg with
    | .ok st => pure st
    | .error e => do IO.eprintln s!"wide_export: {e}"; return 1
  -- `ids`/`idBound` of `Shaped` (`Ixa.ids_ofChip`) for `Package.idOf`.
  let entryName := entry.getD ((circuits.head?.map (·.1)).getD "")
  unless pkg.checkIds st.bound entryName do
    IO.eprintln "wide_export: a channel is not a callable, or there are more callables than the bound"; return 1
  unless pkg.checkRanges do IO.eprintln "wide_export: a depth range map is not a package map"; return 1
  unless pkg.checkEntryPlain entryName do
    IO.eprintln s!"wide_export: the entry {entryName} is recursive or has no chip"; return 1
  let h ← IO.FS.Handle.mk fixedPath .write
  -- `mapFixed` reads claims by list index; the writer reads an array and is
  -- compared with `Air.fixed` on the first rows of every table.
  -- With `"map_padding": "repeat"` the map tables are `mapAirsD`
  -- (`wide_heap_sound_dup`): no selector, padding rows repeat the last claim.
  let sharedLayout := (j.getObjValAs? String "map_layout").toOption == some "shared"
  if sharedLayout && !allMaps then
    IO.eprintln "wide_export: \"map_layout\": \"shared\" needs \"all_maps\""; return 1
  let shared := if sharedLayout then Grouped.sharedTablesOf pkg else []
  for (T, _) in shared do
    unless T.checkFast st.claims do
      IO.eprintln "wide_export: a shared map table row is not a map claim"; return 1
  let repeatPad := (j.getObjValAs? String "map_padding").toOption == some "repeat"
  let maps := if repeatPad then mapAirsD st.claims (WideIxa.mapRows st.claims) else st.maps
  for (T, _) in shared do
    h.write (block p T.rows T.fixedWidth T.fixed)
  for (L, a) in (if sharedLayout then [] else (mapLengths st.claims).zip maps) do
    let cs := (claimsOf st.claims L).toArray
    let f : Nat → Nat → ZMod p := if repeatPad then
        fun i k => (cs.getD (min i (cs.size - 1)) []).getD k 0
      else fun i k => match k with
        | 0 => if i < cs.size then 1 else 0
        | k + 1 => (cs.getD i []).getD k 0
    for i in List.range (min 4 a.rows) ++ ((List.range 2).map (cs.size + ·)).filter (· < a.rows) do
      for k in [0:a.circuit.fixedWidth] do
        unless f i k == a.fixed i k do IO.eprintln "the map writer differs from the map table's fixed matrix"; return 1
    h.write (block p a.rows a.circuit.fixedWidth f)
  for a in st.roms do
    h.write (block p a.rows a.circuit.fixedWidth a.fixed)
  h.flush
  let index : Std.HashMap String Nat := pkg.chips.zipIdx.foldl (fun m (x, i) => m.insert x.name i) {}
  let units := st.chips.map fun (x, rows) => Json.mkObj [("kind", Json.str "unit"),
    ("chip", Json.str x.name), ("chip_index", Json.num (index[x.name]?.getD 0)), ("rows", Json.num rows),
    ("circuit", circuitJson p (x.lower pkg.idOf))]
  let gindex : Std.HashMap String Nat :=
    pkg.trace.groups.zipIdx.foldl (fun m (g, i) => m.insert g.name i) {}
  let groupsJ := st.groups.map fun (g, _, rows) => Json.mkObj [("kind", Json.str "group"),
    ("group", Json.str g.name), ("group_index", Json.num (gindex[g.name]?.getD 0)),
    ("members", Json.arr (g.members.map (Json.str ·.name)).toArray), ("rows", Json.num rows),
    ("circuit", circuitJson p g.lower)]
  let claims := st.claims
  let romsA := st.roms
  let roms := rom
  let request := st.request
  let bound := st.bound
  let bounds : List (String × Nat) := [("bound", bound)]
  let laid := st.chips
  let sharedJ := shared.map fun (T, real) => Json.mkObj [("kind", Json.str "map_shared"),
    ("maps", Json.arr (T.maps.map fun (c, cols) => Json.mkObj [("callable", Json.num c),
      ("cells", Json.arr (cols.map (Json.num ·)).toArray)]).toArray),
    ("rows", Json.num T.rows), ("real_rows", Json.num real), ("padding", Json.str "repeat-row-0"),
    ("circuit", circuitJson p (Grouped.sharedMapCircuit (F := ZMod p) T.fixedWidth T.maps))]
  let mapsJ := if sharedLayout then sharedJ else ((mapLengths claims).zip maps).map fun (L, a) => Json.mkObj [("kind", Json.str "map"),
    ("length", Json.num L), ("claims", Json.num (claimsOf claims L).length), ("rows", Json.num a.rows),
    ("padding", Json.str (if repeatPad then "repeat" else "selector")),
    ("circuit", circuitJson p a.circuit)]
  let romsJ := (roms.zip romsA).map fun ((w, cap), a) => Json.mkObj [("kind", Json.str "rom"),
    ("words", Json.num w), ("rows", Json.num cap), ("circuit", circuitJson p a.circuit)]
  let out := Json.mkObj [("format", Json.str "ix-wide-layout-1"), ("modulus", Json.str (toString p)),
    ("artifact", Json.str path.toString),
    ("tables", Json.arr (units ++ groupsJ ++ mapsJ ++ romsJ).toArray),
    ("request", Json.arr (request.map (field p)).toArray),
    ("bound", Json.num bound), ("bounds", Json.mkObj (bounds.map fun (k, v) => (k, Json.num v)))]
  IO.FS.writeFile output out.compress
  IO.eprintln s!"wide_export: {laid.length} unit, {st.groups.length} group, {maps.length} map and {romsA.length} ROM tables"
  return 0

end

def main (args : List String) : IO UInt32 := do
  let [input, output, fixed] := args
    | do IO.eprintln "usage: wide_export input.json layout.json fixed.bin"; return 2
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile input))
  unless (j.getObjValAs? String "format").toOption == some "ix-wide-input-1" do
    IO.eprintln "unexpected input format"; return 1
  let base := (System.FilePath.mk input).parent.getD "."
  match (j.getObjValAs? String "field").toOption with
  | some "bn254" =>
      have : Fact (Nat.Prime Aiur.Library.Field.BN254.modulus) := ⟨Aiur.Library.Field.BN254.modulus_prime⟩
      run Aiur.Library.Field.BN254.modulus j base output fixed
  | some "goldilocks" =>
      have : Fact (Nat.Prime Aiur.Library.U32.Goldilocks.modulus) := ⟨Aiur.Library.U32.Goldilocks.modulus_prime⟩
      run Aiur.Library.U32.Goldilocks.modulus j base output fixed
  | _ => do IO.eprintln "field must be bn254 or goldilocks"; return 1

end Aiur.Tiling.WideExport
