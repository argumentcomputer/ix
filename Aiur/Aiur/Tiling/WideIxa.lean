import Aiur.Tiling.Ixa
import Aiur.Tiling.WideStage
import Aiur.Tiling.EnablesFast

/-!
# The circuits of a wide stage, from a compiled artifact

`stageOf pkg cfg` builds, from a decoded package (`Ixa.decodePackage`), the
table list `WideStage.wide_heap_sound` is about, in `stageLedger` order:

* `units`: one `Air` per laid-out chip, `⟨IChip.lower idOf x, rows, 0⟩`; for
  the chips `putChip` wrote this is `WideStage.unitAirs idOf` of the source
  chips (`units_ofChip`);
* `maps`: `mapAirs claims mapRows`, one table per claim length, over the
  claims of the called maps, or of every map (`allMaps`);
* `roms`: `romAirs cfg.rom`.

It also returns the entry request and the size `bound` the theorem's
`lookups` and `romCaps` need, and fails unless `checkEnables bound` accepts
every laid-out chip, the callables are distinct, the ROM widths are distinct
and cover the chips' memory widths, and (with `pow2`) every row count is a
power of two.
-/

namespace Aiur.Tiling.WideIxa

open Aiur.Tiling.WideStage Aiur.Tiling.Ixa

variable {F : Type} [Field F] [DecidableEq F]

structure Config where
  /-- Laid-out chips (trace section names) with their row counts. -/
  circuits : List (String × Nat)
  /-- `(words, capacity)` per memory width. -/
  rom : List (Nat × Nat)
  /-- The entry chip; the first circuit's when absent. -/
  entry : Option String := none
  /-- Keep the claims of every map, not only of the maps the chips call. -/
  allMaps : Bool := false
  /-- Require power-of-two row counts everywhere. -/
  pow2 : Bool := false
  /-- Laid-out groups (trace section group names) with their row counts. -/
  groups : List (String × Nat) := []

structure Stage (F : Type) [Field F] where
  chips : List (IChip F × Nat)
  claims : List (List F)
  units : List (Air F)
  maps : List (Air F)
  roms : List (Air F)
  request : List F
  bound : Nat
  /-- Laid-out groups with their members' chips and row counts. -/
  groups : List (IGroup F × List (IChip F) × Nat) := []
  /-- One table per laid-out group, `groupAirI`. -/
  gunits : List (Air F) := []

def Stage.airs (s : Stage F) : List (Air F) := s.units ++ s.gunits ++ s.maps ++ s.roms

/-- The lookup circuit of a written group (`Grouped.lowerGroup` of the layout
`putGroup` wrote, by `Grouped.IGroup.lower_ofLayout`). -/
def _root_.Aiur.Tiling.Ixa.IGroup.lower (g : IGroup F) : Tiling.Circuit F where
  width := g.width + 1
  constraints := g.constraints ++ [.mul (.sub (.const 1) g.activation) (.var g.width)]
  lookups := ⟨.sub (.const 0) (.var g.width), g.receive⟩ :: g.sends.map fun s => ⟨s.1, s.2⟩

/-- The table of a written group with `rows` rows. -/
def groupAirI (x : IGroup F × Nat) : Air F := ⟨x.1.lower, x.2, fun _ _ => 0⟩

/-- The unit table of a written chip with `rows` rows. -/
def unitAirI (idOf : String → Nat) (x : IChip F × Nat) : Air F :=
  ⟨x.1.lower idOf, x.2, fun _ _ => 0⟩

theorem units_ofChip (idOf : String → Nat) (cs : List (Circuit.Chip F × Nat)) :
    (cs.map fun c => (IChip.ofChip c.1, c.2)).map (unitAirI idOf) =
      unitAirs idOf (cs.map fun c => ((c.1, none), c.2)) := by
  simp [unitAirs, unitAirI, unitAir, Bridge.unitCircuit, IChip.lower_ofChip]

/-- Map table rows: the next power of two of the claim count of each length. -/
def mapRows (claims : List (List F)) (L : Nat) : Nat := (claimsOf claims L).length.nextPowerOfTwo

def stageOf (pkg : Package F) (cfg : Config) : Except String (Stage F) := do
  let index : Std.HashMap String Nat := pkg.chips.zipIdx.foldl (fun m (x, i) => m.insert x.name i) {}
  let chips ← cfg.circuits.mapM fun (name, rows) => do
    let some i := index[name]? | throw s!"no chip {name} in the artifact"
    return (pkg.chips[i]!, rows)
  let groups ← cfg.groups.mapM fun (name, rows) => do
    let some g := pkg.trace.groups.find? (·.name == name) | throw s!"no group {name} in the artifact"
    let members ← g.members.mapM fun m => do
      let some i := index[m.name]? | throw s!"no chip {m.name} for a member of {name}"
      return pkg.chips[i]!
    return (g, members, rows)
  let proved := chips.map (·.1) ++ groups.flatMap (·.2.1)
  let called : Std.HashSet String :=
    proved.foldl (fun s x => x.sends.foldl (fun s y => s.insert y.channel) s) {}
  let claims := pkg.claims (fun n => cfg.allMaps || called.contains n)
  let widths := (proved.flatMap fun x => x.memory.map (·.values.length)).dedup
  for w in widths do
    unless cfg.rom.any (·.1 == w) do throw s!"no ROM table for width {w}"
  unless decide (cfg.rom.map Prod.fst).Nodup do throw "two ROM tables share a width"
  unless decide pkg.callables.toList.Nodup do throw "two callables share a name"
  unless decide (pkg.chips.toList.map (·.name) ++ pkg.trace.groups.map (·.name)).Nodup do
    throw "a group shares its name with a chip or another group"
  let entry ← match cfg.entry, cfg.circuits.head? with
    | some e, _ => pure e
    | none, some (e, _) => pure e
    | none, none => throw "no circuits"
  let some e := index[entry]? | throw s!"no entry chip {entry}"
  let ex := pkg.chips[e]!
  let request : List F := (Bridge.CALL : F) :: (pkg.idOf entry : F) ::
    List.replicate (ex.inputs.length + ex.output.length) 0
  let groupCost := fun (ms : List (IChip F)) => (ms.map fun x => x.sends.length + x.memory.length).sum
  let lookups := (chips.map fun (x, rows) => rows * (x.sends.length + x.memory.length)).sum +
    (groups.map fun (_, ms, rows) => rows * groupCost ms).sum + 1
  let bound := max 3 (max (lookups + 1) (max ((cfg.rom.map (·.2)).foldl max 0) ((widths ++ cfg.rom.map (·.1)).foldl max 0 + 1)))
  unless (chips.map (·.2)).sum + (groups.map (·.2.2)).sum ≤ 2 ^ 39 do throw "the stage exceeds 2^39 rows"
  if let some x := proved.find? fun x => !x.checkEnables bound then
    throw s!"checkEnables rejects {x.name}"
  let maps := mapAirs claims (mapRows claims)
  let roms := romAirs (F := F) cfg.rom
  if cfg.pow2 then
    unless (chips.map (·.2) ++ groups.map (·.2.2) ++ cfg.rom.map (·.2)).all (fun n => 0 < n && n.nextPowerOfTwo == n) do
      throw "a row count is not a power of two"
  let gunits := groups.map fun x => groupAirI (x.1, x.2.2)
  return { chips, claims, units := chips.map (unitAirI pkg.idOf), maps, roms, request, bound, groups, gunits }

/-- A successful `stageOf` returns the unit tables of its chips, the map tables
of its claims and the ROM tables of `cfg.rom`: the table lists of
`WideStage.wide_heap_sound`'s `balanced`. -/
theorem stageOf_spec {pkg : Package F} {cfg : Config} {st : Stage F} (h : stageOf pkg cfg = .ok st) :
    st.units = st.chips.map (unitAirI pkg.idOf) ∧ st.maps = mapAirs st.claims (mapRows st.claims) ∧
      st.roms = romAirs cfg.rom := by
  unfold stageOf at h
  simp only [bind, Except.bind, pure, Except.pure, decide_eq_true_eq, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' (split at h)
  all_goals first
    | (cases h; exact ⟨rfl, rfl, rfl⟩)
    | cases h

end Aiur.Tiling.WideIxa
