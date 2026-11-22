import Aiur.Tiling.Tables
import Aiur.Tiling.Export
import Aiur.Library.Field.BN254.Prime

/-!
# Narrow v1 layout export

Runs the verified tiling pass on a layout input written by the Rust
template backend (`aiur_backend::template::lean`) and writes what the prover
and the verifying key consume:

* the templates, in the JSON format of `Aiur.Tiling.Export`;
* the entry request `Part.request W t`, zero-padded to `W + 1` entries per
  tuple, which are the verifier's external claims;
* the fixed matrix of the narrow circuit, one row per entry of
  `System.places`, in a binary file.

The system is `graphs.map Graph.circuit ++ tables.map Bridge.tableCircuit`
with capacities `caps ++ [1, …]`: every map-claim row and every ROM entry is
one single-instance table circuit, so the layout has the shape that
`narrow_heap_sound_tables` takes. Export fails unless `System.checkKeyed` and
`Part.checkRequest` accept it.

The fixed rows are generated in `places` order with `Row.fixed`, which is the
row function of `System.fixedAt`. Labels, multiplicities and invocation ids
use closed forms of `System.label`, `System.multAt` and `System.instId`, since
the list-indexed definitions are quadratic in the trace height. Sampled rows,
or every row of a small system, are compared with `System.fixedAt` itself.

Input JSON: `{"width", "graphs", "caps", "tables", "request"}`, with field
elements as decimal strings. Usage: `tiling_export input.json output.json fixed.bin`;
with `-` for the fixed matrix, the layout is checked and no matrix is written.

Binary fixed format: the magic `IXTLFX01`, `u64` rows and columns (little
endian), then every entry row by row as one length byte `n ≤ 32` followed by
the `n` little-endian bytes of its canonical value.
-/

namespace Aiur.Tiling.TilingExport

open Lean (Json)
open Aiur.Library.Field.BN254 (modulus modulus_prime)

instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

abbrev F := ZMod modulus

def toNat (x : F) : Nat := x.val

def parseTuple (j : Json) : Except String (List F) := do
  return (← (← j.getArr?).mapM (Export.parseField (F := F))).toList

/-- Multiplicity of every cell `(r, j)` of a template, as `System.multAt`
assigns it: `o − 1` at a slot's first cell in row-major order, `−1` at its
other cells, `0` at empty cells. -/
def cellMults (T : Template F) : Array (Array F) := Id.run do
  let rows := T.rows.toArray
  let mut occ : Array Nat := Array.replicate T.slots.length 0
  for row in rows do
    for j in [0:T.width] do
      if let some s := (row.cells[j]?).getD none then
        occ := occ.modify s (· + 1)
  let mut seen : Array Bool := Array.replicate T.slots.length false
  let mut out : Array (Array F) := #[]
  for row in rows do
    let mut m : Array F := #[]
    for j in [0:T.width] do
      match (row.cells[j]?).getD none with
      | some s =>
          if seen[s]! then m := m.push (-1)
          else
            seen := seen.set! s true
            m := m.push ((occ[s]! : F) - 1)
      | none => m := m.push 0
    out := out.push m
  return out

def pushField (out : ByteArray) (x : F) : ByteArray := Id.run do
  let mut n := toNat x
  let mut bytes : ByteArray := ByteArray.empty
  while n != 0 do
    bytes := bytes.push (n % 256).toUInt8
    n := n / 256
  return (out.push bytes.size.toUInt8) ++ bytes

def pushU64 (out : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut out := out
  let mut n := n
  for _ in [0:8] do
    out := out.push (n % 256).toUInt8
    n := n / 256
  return out

/-- Fixed row of instance `i` of circuit `f`, template row `r`. -/
def fastRow (sys : System F) (T : Template F) (mults : Array (Array F)) (labelBase idBase i r : Nat) :
    List F :=
  match T.rows[r]? with
  | none => (List.range (fixedWidth sys.width)).map fun _ => 0
  | some row =>
      let label (j : Nat) : F :=
        match (row.cells[j]?).getD none with
        | some s => ((labelBase + i * T.slots.length + s + 1 : Nat) : F)
        | none => 0
      let mult (j : Nat) : F := (mults[r]!)[j]?.getD 0
      (List.range (fixedWidth sys.width)).map (row.fixed sys.width label mult ((idBase + i : Nat) : F))

/-- Writes the fixed matrix and returns the places of up to `samples` rows,
spread over the trace, with their generated rows. -/
def writeFixed (sys : System F) (path : System.FilePath) (total samples : Nat) :
    IO (Nat × List (Nat × List F)) := do
  let fw := fixedWidth sys.width
  let stride := max 1 (total / max 1 samples)
  let h ← IO.FS.Handle.mk path .write
  h.write (pushU64 (pushU64 "IXTLFX01".toUTF8 total) fw)
  let mut buf : ByteArray := ByteArray.empty
  let mut p := 0
  let mut labelBase := 0
  let mut idBase := 0
  let mut picked : List (Nat × List F) := []
  for (T, cap) in sys.templates.zip sys.caps do
    let mults := cellMults T
    for i in [0:cap] do
      for r in [0:T.rows.length] do
        let row := fastRow sys T mults labelBase idBase i r
        for x in row do buf := pushField buf x
        if p % stride == 0 || (i == 0 && r == 0) then picked := (p, row) :: picked
        p := p + 1
        if buf.size ≥ (1 <<< 24) then
          h.write buf
          buf := ByteArray.empty
    labelBase := labelBase + cap * T.slots.length
    idBase := idBase + cap
  h.write buf
  h.flush
  if p != total then throw (IO.userError s!"generated {p} fixed rows for {total} places")
  return (total, picked)

/-- `System.fixedAt` at up to `limit` of the sampled rows, evenly spread,
against the generated rows. -/
def checkSamples (sys : System F) (picked : List (Nat × List F)) (limit : Nat) : IO Nat := do
  if limit == 0 then return 0
  let fw := fixedWidth sys.width
  let step := max 1 ((picked.length + limit - 1) / max 1 limit)
  let mut n := 0
  for ((p, row), k) in picked.zipIdx do
    if k % step != 0 then continue
    let spec := (List.range fw).map (sys.fixedAt p)
    if spec != row then throw (IO.userError s!"fixed row {p} differs from System.fixedAt")
    n := n + 1
  return n

def padded (W : Nat) (p : Part F) : List (List F) :=
  if p.chunks.isEmpty then [Part.pad W p.tuple]
  else (List.range p.chunks.length).map fun c => Part.pad W (p.chunkTuple c)

def progress (msg : String) : IO Unit := do
  IO.eprintln s!"tiling_export: {msg}"
  (← IO.getStderr).flush

def main (args : List String) : IO UInt32 := do
  let [input, output, fixedPath] := args
    | IO.eprintln "usage: tiling_export input.json output.json (fixed.bin | -)"; return 2
  let t0 ← IO.monoMsNow
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile input))
  let W ← IO.ofExcept ((← IO.ofExcept (j.getObjVal? "width")).getNat?)
  let graphs ← IO.ofExcept do
    (← (← j.getObjVal? "graphs").getArr?).mapM (Export.parseGraph (F := F))
  let caps ← IO.ofExcept do (← (← j.getObjVal? "caps").getArr?).mapM (·.getNat?)
  let tables ← IO.ofExcept do (← (← j.getObjVal? "tables").getArr?).mapM parseTuple
  let request ← IO.ofExcept (parseTuple (← IO.ofExcept (j.getObjVal? "request")))
  if caps.size != graphs.size then
    IO.eprintln "one capacity per graph"; return 1
  let t1 ← IO.monoMsNow
  let mut templates : Array (Template F) := #[]
  for (g, k) in graphs.toList.zipIdx do
    match lower g W with
    | .ok T => templates := templates.push T
    | .error e => IO.eprintln s!"graph {k}: {e}"; return 1
  let tableCircuits := tables.toList.map Bridge.tableCircuit
  for (C, k) in tableCircuits.zipIdx do
    match lower (Graph.ofCircuit C) W with
    | .ok T => templates := templates.push T
    | .error e => IO.eprintln s!"table row {k}: {e}"; return 1
  let sys : System F :=
    { width := W
      circuits := graphs.toList.map Graph.circuit ++ tableCircuits
      templates := templates.toList
      caps := caps.toList ++ tables.toList.map fun _ => 1 }
  let t2 ← IO.monoMsNow
  progress s!"{graphs.size} graphs and {tables.size} table rows lowered in {t2 - t1} ms"
  unless sys.checkKeyed do
    IO.eprintln "System.checkKeyed rejected the layout"; return 1
  let t3 ← IO.monoMsNow
  let part := Part.request W request
  unless part.checkRequest sys request do
    IO.eprintln "Part.checkRequest rejected the entry request"; return 1
  progress s!"System.checkKeyed and Part.checkRequest accepted in {t3 - t2} ms"
  let count (n : Template F → Circuit F → Nat) :=
    (((sys.templates.zip sys.circuits).zip sys.caps).map fun ((T, C), cap) => cap * n T C).sum
  let places := count fun T _ => T.rows.length
  let keys := count fun T _ => T.slots.length
  let lookupParts := count fun _ C => C.lookups.length
  let small := places ≤ 3000
  if small then
    unless places == sys.places.length && keys == sys.keys.length &&
        lookupParts == (sys.enumerate sys.lookupCount).length do
      IO.eprintln "closed-form sizes differ from the enumerations"; return 1
  let (written, picked) ← if fixedPath == "-" then pure (places, [])
    else writeFixed sys fixedPath places (if small then places else 64)
  let t4 ← IO.monoMsNow
  progress (if fixedPath == "-" then s!"{written} places, no fixed matrix written"
    else s!"fixed matrix of {written} rows generated in {t4 - t3} ms")
  -- `System.fixedAt` enumerates the places on every call, which is
  -- quadratic in the number of circuits.
  let samples := if small then picked.length else if sys.templates.length ≤ 4000 then 2 else 0
  let checkedRows ← checkSamples sys picked.reverse samples
  let t5 ← IO.monoMsNow
  progress s!"System.fixedAt agrees on {checkedRows} rows ({t5 - t4} ms)"
  let out := Json.mkObj [
    ("width", Json.num W),
    ("templates", Json.arr (templates.map (Export.template toNat))),
    ("caps", Lean.toJson sys.caps),
    ("places", Json.num places),
    ("fixed_width", Json.num (fixedWidth W)),
    ("request", Json.arr ((padded W part).toArray.map fun t =>
      Json.arr (t.toArray.map (Export.field toNat)))),
    ("bound", Json.num (keys + 1 + places * W)),
    ("instances", Json.num sys.caps.sum),
    ("lookup_parts", Json.num lookupParts),
    ("rom_receivers", Json.num sys.romReceivers.length),
    ("fixed_rows_checked", Json.num checkedRows),
    ("fixed_rows_checked_all", Json.bool (small && checkedRows == places)),
    ("ms", Json.mkObj [("parse", Json.num (t1 - t0)), ("lower", Json.num (t2 - t1)),
      ("check_keyed", Json.num (t3 - t2)), ("fixed", Json.num (t4 - t3)),
      ("fixed_at_samples", Json.num (t5 - t4))])]
  IO.FS.writeFile output out.compress
  return 0

end Aiur.Tiling.TilingExport

def main (args : List String) : IO UInt32 := Aiur.Tiling.TilingExport.main args
