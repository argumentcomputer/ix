import Aiur.Tiling.Tile2
import Aiur.Tiling.Export

/-!
JSON for v2 templates in the format of the prototype's v2 comparison harness:
the prototype's slots (the invocation and virtual slots that follow them are
left out), and physical rows with their lane coefficients, spans, packed
`ts = tag + 4·sub` and multiplicity columns `mk, mc`.
-/

namespace Aiur.Tiling.Periodic.Export2

open Lean (Json)
open Aiur.Tiling.Export (field slot)

variable {F : Type} [Field F] [DecidableEq F] [Hashable F]

def ts (T : Template2 F) (m : Nat) : F :=
  match T.messages[m]? with
  | some (_, tag, sub, _) => tag + 4 * sub
  | none => 0

def msgCell (T : Template2 F) (m j : Nat) : Option Nat :=
  if j = 0 then (T.physMult m).2.2 else ((T.msgCells m)[j]?).getD none

def laneUse (toNat : F → Nat) (T : Template2 F) : LaneUse F → Json
  | .empty => Json.str "empty"
  | .gate l => Json.mkObj [("gate", Json.mkObj [("qm", field toNat l.qm),
      ("q", Json.arr #[field toNat l.q0, field toNat l.q1, field toNat l.q2, field toNat l.q3]),
      ("qc", field toNat l.qc), ("cells", Json.arr #[Export.cell l.c0, Export.cell l.c1, Export.cell l.c2, Export.cell l.c3])])]
  | .message m => Json.mkObj [("msg", Json.mkObj [("ts", field toNat (ts T m)),
      ("mk", field toNat (T.physMult m).1), ("mc", field toNat (T.physMult m).2.1),
      ("cells", Json.arr ((List.range 4).map fun j => Export.cell (msgCell T m j)).toArray)])]

def row (toNat : F → Nat) (T : Template2 F) : Row2 F → Json
  | .gate ls spans => Json.mkObj [("gate", Json.mkObj [
      ("lanes", Json.arr (ls.map (laneUse toNat T)).toArray),
      ("spans", Json.arr (spans.map fun sp => Json.arr #[Json.num sp.start, Json.num sp.len]).toArray)])]
  | .message m key => Json.mkObj [("message", Json.mkObj [("ts", field toNat (ts T m)),
      ("mk", field toNat (T.physMult m).1), ("mc", field toNat (T.physMult m).2.1), ("key", Json.bool key),
      ("cells", Json.arr ((List.range T.width).map fun j =>
        Export.cell (if key ∧ j = 1 then none else msgCell T m j)).toArray)])]

/-- The number of prototype slots: invocation and virtual slots come last. -/
def protoSlots (T : Template2 F) : Nat :=
  T.slots.length - T.virtual.length - (if T.slots.contains .invocation then 1 else 0)

def template (toNat : F → Nat) (T : Template2 F) : Json :=
  Json.mkObj [("slots", Json.arr ((T.slots.take (protoSlots T)).map (slot toNat)).toArray),
    ("rows", Json.arr (T.rows.map (row toNat T)).toArray)]

/-- The checker's verdict on a one-template system: two shards of `cap`
instances. -/
def verdict (toNat : F → Nat) (W : Nat) (T : Template2 F) (C : Circuit F) : Json :=
  let L : Layout F := ⟨[C], [T], [2]⟩
  let S : Sharded F := { width := W, shards := [L, L], buses := busesOf toNat [T] }
  Json.mkObj [("checked", Json.bool S.check), ("logical", Json.bool S.system.checkKeyed),
    ("physical", Json.bool (T.checkPhysical S.buses))]

/-- Lower every fixture graph (one body) and record the checker's verdict. -/
def run (toNat : F → Nat) (fixtures : Json) (W : Nat) : Except String Json := do
  let graphs ← (← fixtures.getArr?).mapM (Export.parseGraph (F := F))
  return Json.arr <| graphs.map fun g =>
    match lowerCircuit W g.circuit none g with
    | .ok (T, C, _) => (template toNat T).mergeObj (verdict toNat W T C)
    | .error e => Json.mkObj [("error", Json.str e)]

end Aiur.Tiling.Periodic.Export2
