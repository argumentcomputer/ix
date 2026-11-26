import Aiur.Tiling
import Aiur.Tiling.Ixa
import Aiur.Tiling.WideStage
import Aiur.Tiling.WideIxa
import Aiur.Tiling.IxaTrace
import Aiur.Tiling.GroupedIxa
import Aiur.Tiling.SingleCircuit
import Aiur.Tiling.BLS12381
import Aiur.Tiling.VectorRom
import Aiur.Library.Field.BN254.Prime
import Aiur.Library.Field.BLS12381.Prime
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

Usage: `wide_export [--goldilocks | --bls12-381 | --bn254 | --field <name>] [--vector-rom K] [--single-circuit [--pow2-rows] [--min-rows N] [--packed-rows N]] input.json layout.json fixed.bin`. Input
(`ix-wide-input-1`): `field` (`"bn254"`, `"goldilocks"`, or `"bls12-381"`, alias
`"bls12381"`, normalized to `"bls12-381"` in output JSON; may also be supplied on
the CLI and fails closed on mismatch), `artifact`
(path, relative to the input's directory unless absolute), `circuits`
(`[{"chip": name | "chip_index": i, "cap": rows}]`), `rom` (`[[words, cap]]`),
optional `rom_vector` (`K ≥ 1`, default `1`; may also be supplied via `--vector-rom K`
and fails closed on `0` or CLI/JSON mismatch),
and `entry` (a chip name; default the first circuit's); optional `all_maps` (keep the claims of every map), `pow2` (require power-of-two row counts) and `map_padding`: `"repeat"` writes the selector-free map tables `mapAirsD` of `wide_heap_sound_dup` (main `mult`, fixed cells only, lookup `push(−mult, cells)`, padding rows repeating the last claim), otherwise `mapAirs`. The tables are `WideIxa.stageOf`'s. When `K ≥ 2`, ROM tables use `VectorRom.vectorRomAir w K cap` (`rows = (cap + K - 1) / K`, `fixed_width = 1`, `addr_base = K * r`, enforcing `K * rows ≤ bound`), recording `"rom_vector": K` in `layout.json` across both normal and `--single-circuit` modes. Output
(`ix-wide-layout-1`): `field`, `modulus`, `tables`, in the order of `stageLedger`'s sum (units,
then map tables, then ROM tables), each with `kind`, `rows` and `circuit` (the
graph format of `TilingExport2.graphJson`, variables `width …` fixed); the
request tuple; `bound`. `fixed.bin` holds one `IXTLFX01` block per map and ROM
table, in table order (`mapFixed`, and the row index for ROM tables).

In both normal and `--single-circuit` modes, the exporter enforces the field's
soundness preconditions: `2 < bound`, stage rows `≤ 2^39`, `bound ≤ 2^63` and
`pkg.limbs.sum ≤ 24` for Goldilocks (`Aiur.Tiling.Goldilocks`), `bound ≤ 2^254`
and `pkg.limbs.sum ≤ 214` for BLS12-381 (`Aiur.Tiling.BLS12381`), and
`bound ≤ BN254.modulus` for BN254.

With `--single-circuit` (standard unit + `mapAirs` + `romAirs` layout, no groups /
shared / repeat map layout), all tables (`st.units ++ st.maps ++ st.roms`, the
`Ixa` realization of `SingleCircuit.wideAirs` by `WideIxa.units_ofChip` and
`WideIxa.stageOf_spec`) are horizontally packed via `Aiur.Tiling.SingleCircuit.pack`
into one single circuit (`num_circuits == 1`, backed by
`SingleCircuit.wide_single_circuit_sound_goldilocks` over Goldilocks and
`Aiur.Tiling.BLS12381.wide_single_circuit_sound_bls12381` over BLS12-381).
`layout.json` gains a `"single_circuit"` object with geometry, per-constituent
offsets / optional `active_col`, and serialized `packCircuit` graph, and
`fixed.bin` receives ONE `IXTLFX01` block for the packed fixed matrix
(`packedRows × fixed_width`).
-/

namespace Aiur.Tiling.WideExport

open Lean (Json)
open Aiur.Tiling.WideStage

/-- The prime field the exporter runs over. -/
inductive FieldChoice where
  | bn254
  | goldilocks
  | bls12381
  deriving BEq, DecidableEq

def FieldChoice.name : FieldChoice → String
  | .bn254 => "bn254"
  | .goldilocks => "goldilocks"
  | .bls12381 => "bls12-381"

def FieldChoice.parse (s : String) : Except String FieldChoice :=
  match s with
  | "bn254" => pure .bn254
  | "goldilocks" => pure .goldilocks
  | "bls12-381" | "bls12381" => pure .bls12381
  | _ => throw s!"unknown field {s} (expected bn254, goldilocks, or bls12-381)"

/-- Maximum `bound` allowed by the field's wide soundness theorem. -/
def FieldChoice.maxBound : FieldChoice → Nat
  | .bn254 => Aiur.Library.Field.BN254.modulus
  | .goldilocks => 2 ^ 63
  | .bls12381 => 2 ^ 254

/-- Maximum depth-limb bit width (`cfg.bits`) allowed by the field's wide
soundness theorem (`24` for Goldilocks, `214` for BLS12-381). -/
def FieldChoice.maxDepthBits : FieldChoice → Option Nat
  | .bn254 => none
  | .goldilocks => some 24
  | .bls12381 => some 214

/-- Parsed CLI options for `wide_export`. -/
structure CliOptions where
  field : Option FieldChoice := none
  singleCircuit : Bool := false
  pow2Rows : Bool := false
  minRows : Option Nat := none
  packedRows : Option Nat := none
  vectorRom : Option Nat := none

def parseNatOpt (flag s : String) : Except String Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw s!"{flag} expects a natural number, got {s}"

def setFieldOpt (opts : CliOptions) (fc : FieldChoice) : Except String CliOptions := do
  if opts.field.isSome && opts.field != some fc then throw "conflicting field flags"
  pure { opts with field := some fc }

def parseArgsAux (opts : CliOptions) (pos : Array String) : List String →
    Except String (CliOptions × Array String)
  | [] => pure (opts, pos)
  | "--goldilocks" :: rest => do
      parseArgsAux (← setFieldOpt opts .goldilocks) pos rest
  | "--bn254" :: rest => do
      parseArgsAux (← setFieldOpt opts .bn254) pos rest
  | "--bls12-381" :: rest | "--bls12381" :: rest => do
      parseArgsAux (← setFieldOpt opts .bls12381) pos rest
  | "--field" :: f :: rest => do
      let fc ← FieldChoice.parse f
      parseArgsAux (← setFieldOpt opts fc) pos rest
  | ["--field"] => throw "--field expects bn254, goldilocks, or bls12-381"
  | "--vector-rom" :: n :: rest => do
      if opts.vectorRom.isSome then throw "duplicate --vector-rom"
      let v ← parseNatOpt "--vector-rom" n
      if v == 0 then throw "--vector-rom must be at least 1"
      parseArgsAux { opts with vectorRom := some v } pos rest
  | ["--vector-rom"] => throw "--vector-rom expects a positive natural number"
  | "--single-circuit" :: rest =>
      parseArgsAux { opts with singleCircuit := true } pos rest
  | "--pow2-rows" :: rest =>
      parseArgsAux { opts with pow2Rows := true } pos rest
  | "--min-rows" :: n :: rest => do
      if opts.minRows.isSome then throw "duplicate --min-rows"
      let v ← parseNatOpt "--min-rows" n
      parseArgsAux { opts with minRows := some v } pos rest
  | ["--min-rows"] => throw "--min-rows expects a natural number"
  | "--packed-rows" :: n :: rest => do
      if opts.packedRows.isSome then throw "duplicate --packed-rows"
      let v ← parseNatOpt "--packed-rows" n
      parseArgsAux { opts with packedRows := some v } pos rest
  | ["--packed-rows"] => throw "--packed-rows expects a natural number"
  | a :: rest => do
      if a.startsWith "--" then throw s!"unknown option {a}"
      parseArgsAux opts (pos.push a) rest

def parseArgs (args : List String) :
    Except String (CliOptions × String × String × String) := do
  let (opts, pos) ← parseArgsAux {} #[] args
  if !opts.singleCircuit && (opts.pow2Rows || opts.minRows.isSome || opts.packedRows.isSome) then
    throw "--pow2-rows, --min-rows, and --packed-rows require --single-circuit"
  match pos.toList with
  | [a, b, c] => pure (opts, a, b, c)
  | _ => throw "usage: wide_export [--goldilocks | --bls12-381 | --bn254 | --field <name>] [--vector-rom K] [--single-circuit [--pow2-rows] [--min-rows N] [--packed-rows N]] input.json layout.json fixed.bin"

/-- Resolve and validate the ROM vectorization factor `K ≥ 1` from CLI `--vector-rom`
and JSON `"rom_vector"`, failing closed on `0`, invalid types, or CLI/JSON conflict. -/
def resolveVectorRom (opts : CliOptions) (j : Json) : Except String Nat := do
  if let some c := opts.vectorRom then
    if c == 0 then throw "--vector-rom must be at least 1"
  let jsonK : Option Nat ← match j.getObjVal? "rom_vector" with
    | .error _ => pure none
    | .ok vj => match vj.getNat? with
        | .ok k =>
            if k == 0 then throw "\"rom_vector\" must be at least 1"
            pure (some k)
        | .error _ => throw "\"rom_vector\" must be a positive natural number"
  match opts.vectorRom, jsonK with
  | some c, some f =>
      if c == f then pure c
      else throw s!"CLI --vector-rom {c} conflicts with input \"rom_vector\" {f}"
  | some c, none => pure c
  | none, some f => pure f
  | none, none => pure 1

/-- Row indices validated directly against `SingleCircuit.packFixed`. -/
def boundaryRows {F : Type} (airs : List (Air F)) (packedRows : Nat) : List Nat :=
  let raw : List Nat :=
    [0] ++
    (airs.flatMap fun a =>
      (if a.rows > 0 then [a.rows - 1] else []) ++
      (if a.rows < packedRows then [a.rows] else [])) ++
    (if packedRows > 0 then [packedRows - 1] else [])
  (raw.filter (· < packedRows)).dedup

/-- Resolve and validate uniform packed height `packedRows` fail-closed. -/
def resolvePackedRows {F : Type} (opts : CliOptions) (airs : List (Air F)) :
    Except String Nat := do
  let maxH := (airs.map (·.rows)).foldl max 0
  let packedRows ← match opts.packedRows with
    | some r =>
        if r == 0 then throw "single-circuit packedRows must be positive"
        if let some m := opts.minRows then
          if r < m then throw s!"--packed-rows {r} is smaller than --min-rows {m}"
        if opts.pow2Rows && r.nextPowerOfTwo != r then
          throw s!"--packed-rows {r} is not a power of two (required by --pow2-rows)"
        pure r
    | none =>
        let base := max maxH (opts.minRows.getD 0)
        if base == 0 && !opts.pow2Rows then
          throw "single-circuit packedRows must be positive"
        pure (if opts.pow2Rows then (max 1 base).nextPowerOfTwo else base)
  if packedRows == 0 then
    throw "single-circuit packedRows must be positive"
  if packedRows > 2 ^ 39 then
    throw s!"single-circuit packedRows {packedRows} exceeds bound 2^39"
  for (a, idx) in airs.zipIdx do
    if a.rows > packedRows then
      throw s!"single-circuit constituent {idx} height {a.rows} exceeds packedRows {packedRows}"
  pure packedRows

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

def run (fieldChoice : FieldChoice) (opts : CliOptions) (j : Json) (base output fixedPath : System.FilePath) : IO UInt32 := do
  let vectorRom ← match resolveVectorRom opts j with
    | .ok k => pure k
    | .error e => do IO.eprintln s!"wide_export: {e}"; return 1
  let get (k : String) : IO Json := IO.ofExcept (j.getObjVal? k)
  let path : System.FilePath := ← IO.ofExcept (← get "artifact").getStr?
  let path := if path.isAbsolute then path else base / path
  let pkg ← IO.ofExcept (Ixa.decodeChecked (F := Fp) p ZMod.val (← IO.FS.readBinFile path))
  IO.eprintln s!"wide_export: decoded {path}: {pkg.chips.size} chips ({fieldChoice.name})"
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
  let stageRom : List (Nat × Nat) :=
    if vectorRom > 1 then VectorRom.expandedRoms vectorRom rom else rom
  let cfg : WideIxa.Config := {
    circuits, rom := stageRom, entry, allMaps,
    pow2 := if vectorRom > 1 then false else pow2,
    groups
  }
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
  unless 2 < st.bound do
    IO.eprintln s!"wide_export: bound {st.bound} does not exceed 2"; return 1
  unless st.bound ≤ fieldChoice.maxBound do
    IO.eprintln s!"wide_export: bound {st.bound} exceeds {fieldChoice.name} limit {fieldChoice.maxBound}"; return 1
  if let some maxBits := fieldChoice.maxDepthBits then
    unless pkg.limbs.sum ≤ maxBits do
      IO.eprintln s!"wide_export: depth limbs sum to {pkg.limbs.sum} bits, exceeding {fieldChoice.name} limit {maxBits}"; return 1
  let romsA : List (Air Fp) :=
    if vectorRom > 1 then VectorRom.vectorRomAirs vectorRom rom else st.roms
  if vectorRom > 1 then
    if pow2 then
      unless (st.chips.map (·.2) ++ st.groups.map (·.2.2) ++ romsA.map (·.rows)).all
          (fun n => 0 < n && n.nextPowerOfTwo == n) do
        IO.eprintln "wide_export: a row count is not a power of two"; return 1
    for ((w, cap), a) in rom.zip romsA do
      unless cap ≤ vectorRom * a.rows && vectorRom * a.rows ≤ st.bound do
        IO.eprintln s!"wide_export: vectorized ROM (w={w}, cap={cap}, K={vectorRom}) effective capacity {vectorRom * a.rows} violates bound {st.bound}"; return 1
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
  let mut singleCircuitFields : List (String × Json) := []
  if opts.singleCircuit then
    if sharedLayout then
      IO.eprintln "wide_export: --single-circuit does not support \"map_layout\": \"shared\""; return 1
    if repeatPad then
      IO.eprintln "wide_export: --single-circuit does not support \"map_padding\": \"repeat\""; return 1
    unless st.groups.isEmpty do
      IO.eprintln "wide_export: --single-circuit does not support \"groups\""; return 1
    -- `st.units ++ st.maps ++ romsA` is the `Ixa` realization of
    -- `SingleCircuit.wideAirs` (for `K = 1`) or `VectorRom.wideVectorAirs` (for `K ≥ 2`).
    let airs : List (Air Fp) := st.units ++ st.maps ++ romsA
    let packedRows ← match resolvePackedRows opts airs with
      | .ok r => pure r
      | .error e => IO.eprintln s!"wide_export: {e}"; return 1
    unless SingleCircuit.allInBounds airs do
      IO.eprintln "wide_export: SingleCircuit.allInBounds rejected a constituent circuit"; return 1
    let packed : Air Fp := SingleCircuit.pack airs packedRows
    unless SingleCircuit.Circuit.inBounds packed.circuit do
      IO.eprintln "wide_export: packed single circuit failed Circuit.inBounds"; return 1
    let mapData : Array (Nat × Array (List Fp) × Nat) :=
      (((mapLengths st.claims).zip st.maps).map fun (L, a) =>
        (L, (claimsOf st.claims L).toArray, a.rows)).toArray
    let oneBytes := pushNat ByteArray.empty (1 : Fp).val
    let zeroBytes := pushNat ByteArray.empty 0
    let fastRowBytes (i : Nat) : ByteArray := Id.run do
      let mut row := ByteArray.empty
      for u in st.units do
        if u.rows < packedRows then
          row := row ++ (if i < u.rows then oneBytes else zeroBytes)
      for (L, cs, mRows) in mapData do
        row := row ++ (if i < cs.size then oneBytes else zeroBytes)
        let claim := cs.getD i []
        for k in [0:L] do
          row := pushNat row (claim.getD k 0).val
        if mRows < packedRows then
          row := row ++ (if i < mRows then oneBytes else zeroBytes)
      let addrBytes := pushNat ByteArray.empty ((vectorRom * i : Nat) : Fp).val
      for r in romsA do
        row := row ++ addrBytes
        if r.rows < packedRows then
          row := row ++ (if i < r.rows then oneBytes else zeroBytes)
      return row
    -- Validate `packed.fixed` against `SingleCircuit.packFixed` and the fast
    -- writer on row 0, every constituent's boundary rows, and the final row.
    let packedFw := packed.circuit.fixedWidth
    for i in boundaryRows airs packedRows do
      let mut specBytes := ByteArray.empty
      for c in [0:packedFw] do
        let v1 := packed.fixed i c
        let v2 := SingleCircuit.packFixed packedRows airs i c
        unless v1 == v2 do
          IO.eprintln s!"wide_export: packed.fixed differs from SingleCircuit.packFixed at ({i}, {c})"; return 1
        specBytes := pushNat specBytes v1.val
      let fastBytes := fastRowBytes i
      unless fastBytes.data == specBytes.data do
        IO.eprintln s!"wide_export: single-circuit fixed writer differs from SingleCircuit.packFixed at row {i}"; return 1
    let h ← IO.FS.Handle.mk fixedPath .write
    h.write (pushU64 (pushU64 "IXTLFX01".toUTF8 packedRows) packedFw)
    let mut chunk := ByteArray.empty
    for i in [0:packedRows] do
      chunk := chunk ++ fastRowBytes i
      if chunk.size ≥ 1 <<< 20 then
        h.write chunk
        chunk := ByteArray.empty
    if chunk.size > 0 then
      h.write chunk
    h.flush
    let constituentJson (kind : String) (index idx : Nat) (a : Air Fp)
        (extra : List (String × Json) := []) : Json :=
      let mOff := SingleCircuit.mainOffset airs idx
      let fOff := SingleCircuit.fixedOffset airs packedRows idx
      let baseFields : List (String × Json) := [
        ("kind", Json.str kind),
        ("index", Json.num index),
        ("rows", Json.num a.rows),
        ("main_offset", Json.num mOff),
        ("main_width", Json.num a.circuit.width),
        ("fixed_offset", Json.num fOff),
        ("fixed_width", Json.num a.circuit.fixedWidth)]
      let actFields : List (String × Json) :=
        if SingleCircuit.needsAct packedRows a then
          [("active_col", Json.num (fOff + a.circuit.fixedWidth))]
        else []
      Json.mkObj (baseFields ++ actFields ++ extra)
    let nUnits := st.units.length
    let nMaps := st.maps.length
    let unitConstituents : Array Json := (((st.chips.zip st.units).zipIdx).map fun (((x, _), a), j) =>
      constituentJson "unit" j j a [("chip", Json.str x.name)]).toArray
    let mapConstituents : Array Json := ((((mapLengths st.claims).zip st.maps).zipIdx).map fun ((L, a), j) =>
      constituentJson "map" j (nUnits + j) a [("length", Json.num L)]).toArray
    let romConstituents : Array Json := (((rom.zip romsA).zipIdx).map fun (((w, _), a), j) =>
      let extra := [("words", Json.num w)] ++
        if vectorRom > 1 then
          [("rom_vector", Json.num vectorRom), ("capacity", Json.num (vectorRom * a.rows))]
        else []
      constituentJson "rom" j (nUnits + nMaps + j) a extra).toArray
    let packedCircuit := SingleCircuit.packCircuit airs packedRows
    singleCircuitFields := [("single_circuit", Json.mkObj [
      ("num_circuits", Json.num 1),
      ("rows", Json.num packedRows),
      ("main_width", Json.num packedCircuit.width),
      ("fixed_width", Json.num packedCircuit.fixedWidth),
      ("num_constraints", Json.num packedCircuit.constraints.length),
      ("num_lookups", Json.num packedCircuit.lookups.length),
      ("constituents", Json.arr (unitConstituents ++ mapConstituents ++ romConstituents)),
      ("circuit", circuitJson p packedCircuit)])]
    IO.eprintln s!"wide_export: single-circuit packed {airs.length} tables -> 1 circuit ({packedRows} rows × {packedCircuit.width} main, {packedCircuit.fixedWidth} fixed, {packedCircuit.constraints.length} constraints, {packedCircuit.lookups.length} lookups)"
  else
    let h ← IO.FS.Handle.mk fixedPath .write
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
    for a in romsA do
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
  let romsJ := (roms.zip romsA).map fun ((w, _), a) =>
    let base := [("kind", Json.str "rom"), ("words", Json.num w), ("rows", Json.num a.rows)]
    let extra := if vectorRom > 1 then
      [("rom_vector", Json.num vectorRom), ("capacity", Json.num (vectorRom * a.rows))]
    else []
    Json.mkObj (base ++ extra ++ [("circuit", circuitJson p a.circuit)])
  let romVectorFields : List (String × Json) :=
    if vectorRom > 1 then [("rom_vector", Json.num vectorRom)] else []
  let out := Json.mkObj ([("format", Json.str "ix-wide-layout-1"),
    ("field", Json.str fieldChoice.name), ("modulus", Json.str (toString p)),
    ("artifact", Json.str path.toString),
    ("tables", Json.arr (units ++ groupsJ ++ mapsJ ++ romsJ).toArray),
    ("request", Json.arr (request.map (field p)).toArray),
    ("bound", Json.num bound), ("bounds", Json.mkObj (bounds.map fun (k, v) => (k, Json.num v)))] ++
    romVectorFields ++ singleCircuitFields)
  IO.FS.writeFile output out.compress
  if vectorRom > 1 then
    IO.eprintln s!"wide_export: {laid.length} unit, {st.groups.length} group, {maps.length} map and {romsA.length} vectorized ROM tables (K={vectorRom})"
  else
    IO.eprintln s!"wide_export: {laid.length} unit, {st.groups.length} group, {maps.length} map and {romsA.length} ROM tables"
  return 0

end

def main (args : List String) : IO UInt32 := do
  let (opts, input, output, fixed) ← match parseArgs args with
    | .ok parsed => pure parsed
    | .error e => do IO.eprintln e; return 2
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile input))
  unless (j.getObjValAs? String "format").toOption == some "ix-wide-input-1" do
    IO.eprintln "unexpected input format"; return 1
  let jsonField : Option FieldChoice ← match j.getObjVal? "field" with
    | .error _ => pure none
    | .ok fj => match fj.getStr? with
        | .ok s => match FieldChoice.parse s with
            | .ok fc => pure (some fc)
            | .error _ => do IO.eprintln "field must be bn254, goldilocks, or bls12-381"; return 1
        | .error _ => do IO.eprintln "field must be bn254, goldilocks, or bls12-381"; return 1
  let fieldChoice : FieldChoice ← match opts.field, jsonField with
    | some c, some f =>
        if c == f then pure c
        else do IO.eprintln s!"CLI field {c.name} conflicts with input field {f.name}"; return 1
    | some c, none => pure c
    | none, some f => pure f
    | none, none => do IO.eprintln "field must be bn254, goldilocks, or bls12-381"; return 1
  let base := (System.FilePath.mk input).parent.getD "."
  match fieldChoice with
  | .bn254 =>
      have : Fact (Nat.Prime Aiur.Library.Field.BN254.modulus) := ⟨Aiur.Library.Field.BN254.modulus_prime⟩
      run Aiur.Library.Field.BN254.modulus .bn254 opts j base output fixed
  | .goldilocks =>
      have : Fact (Nat.Prime Aiur.Library.U32.Goldilocks.modulus) := ⟨Aiur.Library.U32.Goldilocks.modulus_prime⟩
      run Aiur.Library.U32.Goldilocks.modulus .goldilocks opts j base output fixed
  | .bls12381 =>
      run Aiur.Library.Field.BLS12381.modulus .bls12381 opts j base output fixed

end Aiur.Tiling.WideExport
