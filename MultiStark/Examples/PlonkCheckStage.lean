import Aiur.Tiling.IxaTrace
import Aiur.Tiling.WideIxa
import Aiur.Tiling.GroupedIxa
import Aiur.Plonk.WideSound
import Aiur.Plonk.Layout
import Aiur.Plonk.Schema
import Aiur.Plonk.Stage

/-!
# PLONK checker over a wide stage

`plonk_check_stage terminal.ixa schema.json [only] [maxRows] [selector-maps]`
builds the stage with `WideIxa.stageOf` (every map kept, power-of-two rows)
at the schema's capacities and decides `Plonk.stageOk airs P poolIdx`, the
hypothesis of `stage_sound`, table by table. The map tables are the
compiler's shared tables (`Grouped.sharedTablesOf`, each accepted by
`SharedTable.checkFast`; `plonk_shared_heap_sound`), or with `selector-maps`
the selector tables (array-backed, `mapAirsArr_eq`; `plonk_wide_heap_sound`):

1. lower every row (row 0 of a uniform table), threading the pool; `P` is the
   final pool;
2. `poolClosed P`, then `AirIn.rowCheck a r P poolIdx` on row 0 of each
   `uniformB` table and on every row of the others: constraints on their
   cones, every lookup's certificate and the running-sum chain, all against
   the row's gates lowered from `P` and `P`'s gates.

The schema supplies only the configuration (capacities, ROM widths) and the
entry: the root table calls the callable it names, which `Schema.entryOf`
requires to be an exported entry and a listed circuit whose argument and
output word counts are the schema's `public_inputs` and `private_outputs`.
-/

namespace Aiur.Plonk.CheckStage

open Aiur.Plonk Aiur.Tiling Aiur.Tiling.WideStage

/-- For `SharedTable.checkFast`, which equals `check` under any instance. -/
instance : Hashable Aiur.Plonk.Lower.Fr := ⟨fun x => hash x.val⟩
def say (s : String) : IO Unit := do IO.println s; (← IO.getStdout).flush

def run (args : List String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let pkg ← IO.ofExcept (Ixa.decodeChecked (F := Lower.Fr) Aiur.Library.Field.BN254.modulus ZMod.val
    (← IO.FS.readBinFile args[0]!))
  let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile args[1]!))
  let src ← IO.ofExcept (Schema.source j)
  let only := args[2]?.getD ""
  let maxRows := (args[3]?.getD "0").toNat!
  let sharedMaps := args[4]? != some "selector-maps"
  let circuits := src.tables.filterMap fun t =>
    if pkg.chips.any (·.name == t.name) then some (t.name, t.rows) else none
  let rom := src.tables.filterMap fun t =>
    if t.name.startsWith "<ROM:" then
      some (((t.name.drop 5).takeWhile Char.isDigit).toString.toNat!, t.rows) else none
  say s!"decoded: {circuits.length} chips, ROM {rom}, {(← IO.monoMsNow) - t0} ms"
  let entry ← IO.ofExcept (Schema.entryOf pkg circuits j)
  let st ← IO.ofExcept (WideIxa.stageOf pkg { circuits, rom, entry := some entry, allMaps := true, pow2 := true })
  unless st.request.length ≥ 2 && st.request[0]! == (Bridge.CALL : Lower.Fr) &&
      st.request[1]! == (pkg.idOf entry : Lower.Fr) do
    say s!"the root message is not a call of {entry}"; return 1
  let claims := st.claims
  let digest := claims.foldl (fun h c => c.foldl (fun h x => mixHash h (hash x.val)) (mixHash h 7)) (0 : UInt64)
  say s!"stageOf: entry {entry}, {claims.length} claims, digest {digest}, bound {st.bound}, {(← IO.monoMsNow) - t0} ms"
  let chips := st.chips
  let units := st.units
  -- Selector tables: `stageOf_spec` gives `st.maps = mapAirs st.claims (mapRows st.claims)`, which
  -- `mapAirsArr_eq` equates with the array-backed tables.
  let shared := if sharedMaps then (Grouped.sharedTablesOf pkg).map (·.1) else []
  for T in shared do
    unless T.checkFast claims do
      say "a shared map table row is not a map claim"; return 1
  let maps := if sharedMaps then shared.map Grouped.SharedTable.air
    else mapAirsArr claims (WideIxa.mapRows claims)
  let roms := st.roms
  let nRoot := st.request.length - 2
  let airs := units ++ maps ++ roms ++ [rootAir st.request[1]! nRoot]
  let mapLabels := if sharedMaps then (List.range maps.length).map (s!"map_shared/{·}")
    else maps.map (fun a => s!"map/{a.circuit.fixedWidth - 1}")
  let labels := chips.map (·.1.name) ++ mapLabels ++
    roms.map (fun a => s!"rom/{a.circuit.width - 1}") ++ ["root"]
  say s!"stage: {units.length} units, {maps.length} maps {maps.map (·.rows)}, {roms.length} ROMs"
  let only' (name : String) := only != "" && name != only
  -- pass 1: the final pool
  let mut pool : Lower.Pool := {}
  let mut census : Lower.Census := {}
  for (a, name) in airs.zip labels do
    if only' name then continue
    let uniform := AirIn.uniformB a
    let rows := if uniform then 1 else if maxRows == 0 then a.rows else min a.rows maxRows
    for r in [0:rows] do
      let s := AirIn.lowerRowState a r pool
      pool := s.pool
      census := census.add s.gates (if uniform then a.rows else 1)
  let P := pool
  let poolIdx : Std.HashMap Lower.Ref Nat := P.gates.zipIdx.foldl (fun m (g, i) => m.insert g.c i) {}
  say s!"pass 1: pool {P.gates.size}, poolClosed {poolClosed P}, {(← IO.monoMsNow) - t0} ms"
  -- pass 2: `stageOk`, table by table
  let mut ok := 0
  let mut bad := if poolClosed P then 0 else 1
  for (a, name) in airs.zip labels do
    if only' name then continue
    let t1 ← IO.monoMsNow
    let uniform := AirIn.uniformB a
    if !uniform && a.circuit.fixedWidth == 0 then say s!"{name}: not uniform"
    let rows := if uniform then 1 else if maxRows == 0 then a.rows else min a.rows maxRows
    let mut err : Option Nat := none
    for r in [0:rows] do
      unless AirIn.rowCheck a r P (poolIdx[·]?) do
        err := some r
        break
    match err with
    | none => ok := ok + 1
    | some r => bad := bad + 1; say s!"{name}: rowCheck rejects row {r}"
    let grown := (AirIn.lowerRowState a 0 P).pool.gates.size != P.gates.size
    say s!"{name}: {a.rows} rows, {a.circuit.constraints.length} constraints, {a.circuit.lookups.length} lookups, uniform {uniform}{if grown then ", pool grows" else ""}, {(← IO.monoMsNow) - t1} ms"
  census := { census with pool := pool.gates.size }
  let poolDigest := pool.gates.foldl (fun h g =>
    [g.a, g.b, g.c, g.L.val, g.R.val, g.O.val, g.M.val, g.C.val].foldl (fun h x => mixHash h (hash x)) h) (0 : UInt64)
  say s!"pool digest {poolDigest}"
  say s!"census: {repr census}, total {census.total}"
  say s!"stageOk: {ok} tables accepted, {bad} rejected{if maxRows == 0 && only == "" then "" else " (partial run)"}, {(← IO.monoMsNow) - t0} ms"
  -- the layout and its running-sum link (full runs only)
  if maxRows == 0 && only == "" then
    let airsA := airs.toArray
    let mut frs : Array (Array Nat) := #[]
    let mut nlocs : Array Nat := #[]
    for a in airs do
      if AirIn.uniformB a then
        let s := AirIn.lowerRowState a 0 P
        frs := frs.push #[s.sum]; nlocs := nlocs.push s.nloc
      else
        let mut fs : Array Nat := #[]
        let mut nl := 0
        for r in [0:a.rows] do
          let s := AirIn.lowerRowState a r P
          fs := fs.push s.sum; nl := max nl s.nloc
        frs := frs.push fs; nlocs := nlocs.push nl
    let tR := airsA.size - 1
    let mut cellBases : Array Nat := #[]
    let mut cur := nRoot
    for h : t in [0:airsA.size] do
      let a := airsA[t]
      if t == tR then cellBases := cellBases.push 0
      else cellBases := cellBases.push cur; cur := cur + a.rows * a.circuit.width
    let poolBase := cur
    cur := poolBase + P.next
    let mut locStarts : Array Nat := #[]
    for h : t in [0:airsA.size] do
      locStarts := locStarts.push cur
      cur := cur + airsA[t].rows * nlocs[t]!
    let init := cur
    let spare := cur + 1
    let locBase (i : Nat × Nat) : Nat := locStarts[i.1]! + i.2 * nlocs[i.1]!
    let fr (i : Nat × Nat) : Nat := let fs := frs[i.1]!; if fs.size == 1 then fs[0]! else fs.getD i.2 Lower.sumIn
    -- `sumIn` per row: the previous row's final-sum wire
    let mut sums : Array (Array Nat) := #[]
    let mut s := init
    let mut linkErr := false
    for h : t in [0:airsA.size] do
      let a := airsA[t]
      let uniform := frs[t]!.size == 1
      if uniform then
        let f := frs[t]!.getD 0 Lower.sumIn
        sums := sums.push #[s]
        if a.rows > 0 && f != Lower.sumIn then
          if f % 4 != 1 then linkErr := true
          s := locBase (t, a.rows - 1) + f / 4
      else
        let mut ss : Array Nat := #[]
        for r in [0:a.rows] do
          ss := ss.push s
          let f := fr (t, r)
          if f != Lower.sumIn then
            if f % 4 != 1 then linkErr := true
            s := locBase (t, r) + f / 4
        sums := sums.push ss
    let last := s
    let sumIn (i : Nat × Nat) : Nat :=
      let ss := sums[i.1]!
      if frs[i.1]!.size == 1 then
        let f := frs[i.1]!.getD 0 Lower.sumIn
        if i.2 == 0 || f == Lower.sumIn then ss.getD 0 0 else locBase (i.1, i.2 - 1) + f / 4
      else ss.getD i.2 0
    let L : Layout := ⟨(fun t => cellBases[t]!), (fun t => (airsA.getD t defaultAir).circuit.width), poolBase, locBase, sumIn, spare⟩
    let fOk := Layout.finalOk airs P fr
    let lOk := L.linkOkF airs fr init last
    say s!"layout: {spare + 1} wires ({nRoot} root cells, pool at {poolBase}, locals at {locStarts[0]!}), linkErr {linkErr}, finalOk {fOk}, linkOkF {lOk}, {(← IO.monoMsNow) - t0} ms"
    if !(fOk && lOk) then bad := bad + 1
  return if bad == 0 then 0 else 1

end Aiur.Plonk.CheckStage

def main (args : List String) : IO UInt32 := Aiur.Plonk.CheckStage.run args
