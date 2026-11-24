import Aiur.Tiling.Grouped
import Aiur.Tiling.WideIxa
import Aiur.Tiling.IxaTrace

/-!
# Grouped circuits from a compiled artifact

`Ixa.IGroup.lower` (used by `WideIxa.stageOf` for its group tables) lowers the
group record of the trace section. For the record `Trace.putGroup` writes
(`IGroup.ofLayout`, `putGroup_eq`) it is `Grouped.lowerGroup` of the layout.
-/

namespace Aiur.Tiling.Grouped

open Aiur.Tiling.Ixa

variable {F : Type} [Field F] [DecidableEq F]

theorem IGroup.lower_ofLayout (g : Optimized.Grouping.Layout F) :
    (IGroup.ofLayout g).lower = lowerGroup g := by
  simp [IGroup.lower, IGroup.ofLayout, lowerGroup, List.map_map, Function.comp_def]

theorem groupAirI_ofLayout {id : String → Except String Nat} (x : Optimized.Grouping.Packed F id × Nat) :
    WideIxa.groupAirI (IGroup.ofLayout x.1.checked.layout, x.2) = groupAir x := by
  simp [WideIxa.groupAirI, groupAir, IGroup.lower_ofLayout]

/-- The compiler's map tables (`circuits.rs` `fixed_tables`) of a decoded
package: maps grouped by input-table height (first-occurrence order), height
the next power of two (`0` stays `0`), fixed column `0` the constant `1`, then
one block of columns per distinct input or output table in first-use order;
padding rows repeat row `0`. Returns the tables with their real heights. -/
def sharedTablesOf (pkg : Package F) : List (SharedTable F × Nat) :=
  let bc := pkg.program.bytecode
  let tables := bc.tables.toArray
  let groups : List (Nat × List (Nat × Execution.Map)) :=
    bc.maps.zipIdx.foldl (fun gs (m, k) =>
      let h := (tables.getD m.input ⟨"", .field, []⟩).rows.length
      if gs.any (·.1 == h) then gs.map fun g => if g.1 == h then (g.1, g.2 ++ [(k, m)]) else g
      else gs ++ [(h, [(k, m)])]) []
  groups.map fun (real, maps) =>
    let height := if real = 0 then 0 else real.nextPowerOfTwo
    let rowsOf := fun t => (tables.getD t ⟨"", .field, []⟩).rows
    let widthOf := fun t => ((rowsOf t).headD []).length
    let place := fun (cols : List (Nat × Nat × Nat)) (next : Nat) (t : Nat) =>
      match cols.find? (·.1 == t) with
      | some (_, start, _) => (cols, next, start)
      | none => (cols ++ [(t, next, widthOf t)], next + widthOf t, next)
    let (cols, width, specs) := maps.foldl (fun (cols, next, specs) (k, m) =>
      let (cols, next, i) := place cols next m.input
      let (cols, next, o) := place cols next m.output
      (cols, next, specs ++ [(bc.functions.length + k,
        (List.range (widthOf m.input)).map (i + ·) ++ (List.range (widthOf m.output)).map (o + ·))]))
      ([], 1, [])
    let matrix : Array (Array F) := (Array.range real).map fun r =>
      #[(1 : F)] ++ (cols.foldl (fun acc (t, _, _) => acc ++ ((rowsOf t)[r]?.getD []).toArray) #[])
    ({ fixedWidth := width, maps := specs, rows := height,
       fixed := fun i c => (matrix.getD (if i < real then i else 0) #[]).getD c 0 }, real)

end Aiur.Tiling.Grouped
